import FHE.Pin.BFV.Checks
import FHE.Pin.ChecksProg
import Challenge.BFVDecryptLib

/-!
# FHE.Pin.BFV.ChecksProg — the extracted BFV program against the recorded run
(UNTRUSTED glue around the trusted definitions)

The program of `prog.fhecheck.json` is replayed one instruction at a time with `FHE.Pin.stepA`
(= `Spec.Source.step`, `stepA_spec`). Every variable that has an OpenFHE object is compared with it:

* `c.input`: the input hypothesis `Spec.TraceBFV.InputsOK`, input by input, at
  `Spec.TraceBFV.inputBound` (decided by `FHE.Pin.BFV.inputOKb`, sound);
* `b.msg`, `b.raw`, `b.output`: the message `Source.step` computes against
  `Spec.Scheme.bfvDecrypt` of OpenFHE's ciphertext and against OpenFHE's own `Decrypt`;
* `e.step`: `Spec.TraceBFV.StepOK` at the budget `Challenge.CertifyBFV.budgetBFV x k` of instruction `k` of the decoded
  input `x` (decided by `FHE.Pin.BFV.stepOKb`, sound), with the witness quantities of the
  multiplication contract;
* `f.bound`: the measured BFV noise against the bound of `Challenge.BFV.refBoundBFV`, replayed as
  `Challenge.BFV.refRunBFVAt` does (`f.refAnalyze`: the replay's result is `refAnalyzeBFVAt`'s);
* `f.verdict`: `Challenge.CertifyBFV.certifyBFV?` on the input `fhe_check` builds;
  `f.certified-consistent`: a CERTIFIED program has no violated step contract, no noise above its
  bound and no input outside its bound.
-/

namespace FHE.Pin.BFV
open Lean Spec Spec.NPoly Spec.Scheme Spec.Source FHE.Pin
open Spec.TraceBFV (Bnd)
open Spec.CertifyBFV (InputBFV)
open Challenge.BFV (decOK domainOK bndOK refAnalyzeBFVAt)
open Challenge.CertifyBFV (budgetBFV certifyBFV?)

/-! ### The `mul` verdict, computed once

`stepOKb` on a `mul` is `mulOKb`, whose rounding witness `D` (`mulWitD`) costs one product of
size `N²`. The checker computes `D` once, prints its norm and takes the verdict `mulVerdict` from
it; the two theorems say this is `stepOKb`'s verdict (so `stepOKb_sound` applies). -/

/-- The three tests of `mulOKb`, given the witness `D`. -/
def mulVerdict (N : ℕ) (h : Hooks) (E : TraceBFV.Budget) (Q : ℕ) (ka kb D : Array ℤ) : Bool :=
  decide (normA N ka ≤ E.mulLift) && decide (normA N kb ≤ E.mulLift) &&
    h.roundOK (normA N D) Q E.mulRound

theorem stepOKb_mul (P : FullParams) (E : TraceBFV.Budget) (K : ℕ) (h : Hooks) (d a c : Var)
    (lvl : ℕ) (dph : Ph) (get : Var → Option (Ph × ℕ)) (ka kb : Array ℤ) (x y : Ph × ℕ)
    (hx : get a = some x) (hy : get c = some y) :
    stepOKb P E K h (.mul d a c) lvl dph get ka kb =
      some (mulVerdict P.src.N h E (P.src.modulus lvl) ka kb
        (mulWitD P.src.N K h (P.src.modulus lvl) P.src.t dph.Z x.1.Z y.1.Z ka kb)) := by
  simp [stepOKb, hx, hy, mulOKb, mulVerdict]

theorem stepOKb_square (P : FullParams) (E : TraceBFV.Budget) (K : ℕ) (h : Hooks) (d a : Var)
    (lvl : ℕ) (dph : Ph) (get : Var → Option (Ph × ℕ)) (ka kb : Array ℤ) (x : Ph × ℕ)
    (hx : get a = some x) :
    stepOKb P E K h (.square d a) lvl dph get ka kb =
      some (mulVerdict P.src.N h E (P.src.modulus lvl) ka ka
        (mulWitD P.src.N K h (P.src.modulus lvl) P.src.t dph.Z x.1.Z x.1.Z ka ka)) := by
  simp [stepOKb, hx, mulOKb, mulVerdict]

/-- What the checker knows about a program variable. -/
structure VRec where
  ph : Option Ph := none
  parts : Nat := 0
  level : Nat := 0
  key : Nat := 1
  isPt : Bool := false
  synthetic : Bool := false
  /-- A `modSwitch` chain through variables without an OpenFHE object: the last variable with
  data and the limbs dropped since (first dropped first). -/
  pend : Option (Var × List Nat) := none
  depth : Nat := 0
  /-- `Challenge.BFV.refRunBFV` rejects at this variable or at an ancestor (domain, bound rule or
  `decOK` of the bound): bounds from here on are not claims of the analyzer. -/
  tainted : Bool := false
  /-- An input this value depends on fails its input contract (`c.input`). -/
  premiseBad : Bool := false
  /-- The step that produced this value, or one that produced an ancestor, violates its contract
  (its `e.step` line fails): what the library computed is not the program's value. -/
  stepBad : Bool := false
  cost : Nat := 1
  deriving Inhabited

/-- The lift witness of the `mul` contract for an operand: `k := (Ψ − Φ) / Q`, with
`Ψ = Σ [cᵢ]_Q · σ_key(s)ⁱ` over `ℤ` the integer phase of the centred components and `Φ` the
centred phase. Returns `k` and whether the division is exact. -/
def liftWitnessOf (b : BX) (ph : Ph) (lvl : Nat) (lift : Array Int → Array Int) :
    IO (Array Int × Bool) := do
  let N := b.N
  let Q := b.P.src.modulus lvl
  let sk ← b.x.sKey ph.key
  let cc := ph.comps.map fun c => lift (centredA N b.K .none Q c)
  let Ψ := phaseZ N b.K b.x.mt sk cc
  let Φ := centredA N b.K .none Q ph.Z
  let diff := toArr b.K (ofArr (N := N) Ψ - ofArr Φ)
  pure (diff.map (· / (Q : Int)), diff.all (· % (Q : Int) == 0))

def liftWitness (b : BX) (ph : Ph) (lvl : Nat) : IO (Array Int × Bool) := liftWitnessOf b ph lvl id

/-- A model of the lift of OpenFHE's exact base extension of the HPS family
(`DCRTPolyImpl::SwitchCRTBasis`, `dcrtpoly-impl.h:1058-1109`, called by `ExpandCRTBasis`): for the
canonical residues `xᵢ` of `x` modulo `q₁ … q_k`, `yᵢ = [xᵢ·q̂ᵢ⁻¹]_{qᵢ}`, the binary64 sum
`ν = 0.5 + Σᵢ yᵢ·(1/qᵢ)` (in this order, `1/qᵢ` rounded to binary64), `α = ⌊ν⌋`, lift
`Σᵢ yᵢ·q̂ᵢ − α·Q`. It equals the centred representative except where `ν` is within the rounding
error of an integer (coefficients near `±Q/2`). UNTRUSTED: it only supplies a witness. -/
def hpsLift (qs : List Nat) (x : Int) : Int := Id.run do
  let Q := qs.foldl (· * ·) 1
  let mut v : Int := 0
  let mut nu : Float := 0.5
  for q in qs do
    let hat := Q / q
    let inv := invMod (hat % q) q
    let y : Nat := ((x % (q : Int)).toNat * inv) % q
    v := v + (y : Int) * (hat : Int)
    nu := nu + Float.ofNat y * (1.0 / Float.ofNat q)
  return v - (nu.floor.toUInt64.toNat : Int) * (Q : Int)

/-- A model of the lift of OpenFHE's BEHZ base extension (`FastBaseConvqToBskMontgomery`,
Bajard et al. 2016, §4.3): for a residue vector `c` modulo `q₁ … q_k` (canonical residues),
`v = Σᵢ [cᵢ·m̃·q̂ᵢ⁻¹]_{qᵢ}·q̂ᵢ`, `r = [−v·Q⁻¹]_{m̃}` in `[−m̃/2, m̃/2)`, lift `(v + Q·r)/m̃` (an integer
`≡ c (mod Q)`, equal to the centred representative except near `±Q/2`). UNTRUSTED: it only
supplies a witness to `stepOKb`, which is sound for every witness. -/
def behzLift (qs : List Nat) (mt : Nat) (x : Int) : Int := Id.run do
  let Q := qs.foldl (· * ·) 1
  if mt = 0 then return x
  let mut v : Int := 0
  for q in qs do
    let hat := Q / q
    let inv := invMod (hat % q) q
    let ci : Int := x % (q : Int)
    v := v + ((ci * (mt : Int) * (inv : Int)) % (q : Int)) * (hat : Int)
  let Qinv : Int := invMod (Q % mt) mt
  let mut r : Int := (-v * Qinv) % (mt : Int)
  if 2 * r ≥ (mt : Int) then r := r - mt
  return (v + (Q : Int) * r) / (mt : Int)

/-- The budgets a step line compares with: the one charged, the textbook one, the idealised one
(`floatTol := false`). -/
structure Budgets where
  E : TraceBFV.Budget
  textbook : TraceBFV.Budget
  ideal : TraceBFV.Budget
  lay : Budget.KSLayout

/-- The verdict and the diagnostic fields of `e.step` for the destination `d` (at level `vLevel`)
of instruction `i`. **The verdict is `FHE.Pin.BFV.stepOKb`** (proved sound for
`Spec.TraceBFV.StepOK`: `stepOKb_sound`; for `mul`/`square` through `stepOKb_mul`,
`stepOKb_square`); the fields are recomputed for the report. `none`: an operand has no data. -/
def stepReport (b : BX) (B : Budgets) (i : Instr) (vLevel : Nat) (d : Ph)
    (get : Var → Option (Ph × Nat)) : IO (Option (Bool × List (String × Json))) := do
  let P := b.P
  let N := b.N
  let t := b.t
  let E := B.E
  let h := b.mu.hooks
  let Q := P.src.modulus vLevel
  let mulFields := fun (ka kb D : Array Int) (exact : Bool) =>
    let nD := normA N D
    let r := cdiv (2 * nD) Q
    let la := normA N ka
    let lb := normA N kb
    measuredBound r E.mulRound ++
      [("roundMeasured", natJ r), ("roundBound", natJ E.mulRound),
       ("roundTextbook", natJ B.textbook.mulRound), ("roundIdealised", natJ B.ideal.mulRound),
       ("roundSlackBits", slackJ r E.mulRound), ("roundSlackBitsTextbook", slackJ r B.textbook.mulRound),
       ("roundSlackBitsIdealised", slackJ r B.ideal.mulRound),
       ("normDBits", bitsJ nD),
       ("liftA", natJ la), ("liftB", natJ lb), ("liftMeasured", natJ (max la lb)), ("liftBound", natJ E.mulLift),
       ("liftTextbook", natJ B.textbook.mulLift), ("liftIdealised", natJ B.ideal.mulLift),
       ("liftSlackBits", slackJ (max la lb) E.mulLift),
       ("liftSlackBitsTextbook", slackJ (max la lb) B.textbook.mulLift),
       ("witnessExact", boolJ exact)]
  -- the witnesses tried, in order: the centred lift; under BEHZ, the model of its Montgomery lift
  -- (`behzLift`). The verdict is `stepOKb`'s with the first witness that passes (sound for every
  -- witness: `stepOKb_sound`); the line says which, and what the centred witness gave.
  let mt := (jNat? b.bfvJ "behzMtilde").getD 0
  let behz := b.mult == "BEHZ" && mt > 0
  let qsL := P.src.qs.take vLevel
  let lifts : List (String × (Array Int → Array Int)) :=
    [("centred", fun (a : Array Int) => a)] ++
    (if behz then [("behz-montgomery", fun (a : Array Int) => a.map (behzLift qsL mt))]
     else [("hps-switchcrt", fun (a : Array Int) => a.map (hpsLift qsL))])
  -- pairs (first operand's lift, second operand's lift); the centred pair first
  let pairs : List ((String × (Array Int → Array Int)) × (String × (Array Int → Array Int))) :=
    lifts.flatMap fun la => lifts.map fun lb => (la, lb)
  let pick : Option (Ph × Ph × Bool) := match i with
    | .mul _ a c => match get a, get c with
      | some x, some y => some (x.1, y.1, false)
      | _, _ => none
    | .square _ a => (get a).map fun x => (x.1, x.1, true)
    | _ => none
  match i with
  | .mul .. | .square .. =>
    let some (x, y, sq) := pick | return none
    let mut res : Option (Bool × List (String × Json)) := none
    let mut first : List (String × Json) := []
    for ((wa, lfa), (wb, lfb)) in pairs do
      if sq && wa != wb then continue
      let wn := if wa == wb then wa else s!"{wa}/{wb}"
      let (ka, ea) ← liftWitnessOf b x vLevel lfa
      let (kb, eb) ← if sq then pure (ka, ea) else liftWitnessOf b y vLevel lfb
      let D := mulWitD N b.K h Q t d.Z x.Z y.Z ka kb
      let ok := mulVerdict N h E Q ka kb D
      let f := mulFields ka kb D (ea && eb)
      if first.isEmpty then first := f
      res := some (ok, f ++ [("witness", Json.str wn)] ++
        (if wn == "centred" then [] else
          [("centredWitnessRoundMeasured", (first.lookup "roundMeasured").getD Json.null),
           ("why", Json.str "the centred lift witness fails; witnesses from models of the library's lift (BEHZ Montgomery / HPS SwitchCRTBasis) are tried (stepOKb is sound for every witness)")]))
      if ok then break
    return res
  | _ =>
    let some ok := stepOKb P E b.K h i vLevel d get #[] #[] | return none
    let fields : List (String × Json) := match i with
      | .relin _ a | .keySwitch _ a =>
        match get a with
        | some (x, _) =>
          let e := toArr b.K (centered (ofInt Q (ofArr (N := N) d.Z) - ofInt Q (ofArr x.Z)))
          let nrm := normA N e
          let at' := BudgetBFV.ksBoundAt P B.lay x.level
          measuredBound nrm E.keySwitch ++
            [("ksBoundAt", natJ at'), ("ksBoundAtBits", bitsJ at'), ("slackBitsAtLevel", slackJ nrm at'),
             ("withinKsBoundAt", boolJ (decide (nrm ≤ at'))),
             ("ksBudget", natJ (BudgetBFV.ksBudget P B.lay)), ("operandLevel", Json.num x.level)]
        | none => []
      | .addPlain _ a p | .subPlain _ a p =>
        match get a, get p with
        | some (x, _), some (y, _) =>
          let Δ : ZMod Q := ((h.delta Q t : ℕ) : ZMod Q)
          let rhs : Poly Q N := match i with
            | .subPlain .. => ofInt Q (ofArr x.Z) - Δ • ofInt Q (ofArr y.Z)
            | _ => ofInt Q (ofArr x.Z) + Δ • ofInt Q (ofArr y.Z)
          let δ := toArr b.K (centered (ofInt Q (ofArr (N := N) d.Z) - rhs))
          let nrm := normA N δ
          measuredBound nrm E.plainAdd ++
            [("QmodT", natJ (Q % t)), ("plainNorm", natJ (normA N y.Φ)),
             ("rounded", natJ (BudgetBFV.plainAddRounded P (Challenge.CertifyBFV.maxPlainBound P
               (match b.inp with | .ok inp => inp.base.prog | .error _ => ⟨[], [], [], []⟩))))]
        | _, _ => []
      | .modSwitch _ a =>
        match get a with
        | some (x, parts) =>
          match P.src.qs[x.level - 1]? with
          | some q =>
            let δ := toArr b.K ((q : Int) • ofArr (N := N) d.Φ - ofArr x.Φ)
            let nrm := normA N δ
            measuredBound (cdiv nrm q) E.modSwitch ++
              [("normDelta", natJ nrm), ("q", natJ q), ("operandParts", Json.num parts)]
          | none => []
        | none => []
      | .dropLimbs .. => [("why", Json.str "not a BFV operation (Spec.TraceBFV.StepOK is False)")]
      | _ => []
    return some (ok, fields)

/-- The lines of one variable that has ciphertext data: `b.msg`, `b.raw`, `f.bound`, `f.decok`. -/
def reportVar (b : BX) (name op : String) (r : VRec) (ph : Ph) (msg : Array (ZMod b.P.src.t))
    (β : Option Bnd) (arbitrary : Bool) (objId : Option String) (extra : List (String × Json)) :
    IO Unit := do
  let P := b.P
  let N := b.N
  let t := b.t
  let Q := P.src.modulus r.level
  let common : List (String × Json) :=
    [("level", Json.num r.level), ("parts", Json.num r.parts), ("key", Json.num r.key),
     ("depth", Json.num r.depth), ("synthetic", boolJ r.synthetic), ("tainted", boolJ r.tainted),
     ("premiseBad", boolJ r.premiseBad), ("stepBad", boolJ r.stepBad)] ++ extra
  if r.isPt then
    let nrm := normA N ph.Φ
    match β with
    | some (.pt bd) =>
      b.emit "f.bound" name "plaintext" (some (decide (nrm ≤ bd))) "forced" (measuredBound nrm bd ++ common)
    | _ => b.emit "f.bound" name "plaintext" none "forced" (common ++ [("why", Json.str "no plaintext bound")])
    return
  -- hand-built inputs (`inputsArbitrary`) are judged like any other: their `c.input` line decides
  -- `Spec.TraceBFV.InputsOK`, and only an input that fails it voids what depends on it
  let excused := r.tainted || (r.premiseBad && (op != "input" || arbitrary)) || r.stepBad
  let exWhy := if r.stepBad then "this value or an ancestor violates its step contract (see the failing e.step line): what the library computed is not the program's value"
    else if r.premiseBad && op == "input" then "inputsArbitrary: this hand-built input is outside its input contract"
    else if r.tainted then "Challenge.BFV.refRunBFV rejects the program at this variable or at an ancestor (the bound is not a claim of the analyzer)"
    else "an input this value depends on fails its input contract (see its c.input line)"
  let dec := b.mu.decryptOfPhase N b.K t Q ph.Φ
  let msgOK := dec == msg
  b.emit "b.msg" name op (if msgOK then some true else if excused then none else some false) "forced"
    (common ++ [("mismatches", Json.num (diffCount dec msg))] ++
      (if msgOK then [] else [("why", Json.str (if excused then exWhy else
        "the message Source.step computes differs from Spec.Scheme.bfvDecrypt of OpenFHE's ciphertext although the analyzer accepts the program up to here"))]))
  let decObj : Option Json := do
    let id ← objId
    let o ← b.c.object? id
    jObj? o "decrypt"
  if let some dj := decObj then
    if r.key == 1 then
      if let some rawName := jStr? dj "raw" then
        let (raw, rawT) ← b.rawDec rawName
        let pred := valsOf msg
        b.emit "b.raw" name op (if pred == raw then some true else if excused then none else some false) "forced"
          (common ++ [("mismatches", Json.num (diffCount pred raw)), ("rawEqualsT", Json.num rawT)] ++
            (if pred == raw then [] else [("why", Json.str (if excused then exWhy else
              "the message Source.step computes differs from OpenFHE's Decrypt"))]))
  let noise := b.mu.noise N b.K t Q ph.Z msg
  if let some id := objId then
    if r.key == 1 then b.objNoise.modify (·.insert id noise)
  let limit := FHE.Check.BFV.maxNoise t Q
  let limitJ : List (String × Json) :=
    [("limitBits", match limit with | some m => bitsJ m | none => Json.null)]
  match β with
  | some (.ct bd) =>
    let within := decide (noise ≤ bd)
    let ok : Option Bool := if within then some true else if excused then none else some false
    if ok == some false then b.boundFail.modify (· + 1)
    b.emit "f.bound" name op ok "forced"
      (measuredBound noise bd ++ common ++ limitJ ++ [("boundDecOK", boolJ (decOK t Q bd))] ++
        (if ok.isNone then [("why", Json.str exWhy)] else []))
  | _ =>
    b.emit "f.bound" name op none "forced"
      (common ++ [("measured", natJ noise), ("measuredBits", bitsJ noise),
        ("why", Json.str "Challenge.BFV.refBoundBFV gives no ciphertext bound (an operand has none)")])
  let dOK := decOK t Q noise
  b.emit "f.decok" name op (if dOK then some true else if excused then none else some false) "forced"
    ([("measured", natJ noise), ("measuredBits", bitsJ noise)] ++ common ++ limitJ ++
      (if dOK then [] else [("why", Json.str (if excused then exWhy else
        "the measured noise violates Challenge.BFV.decOK although the analyzer accepts the program up to here"))]))
  if b.literal r.parts then
    let lit := toArr b.K (centered (Trace.phaseAt P Q r.key (ofArr b.s) (ph.comps.map ofArr)))
    b.emit "e.phase.literal-vs-forced" name "phaseAt" (some (lit == ph.Φ)) "literal+forced" common

/-- The failing conjuncts of `Challenge.CertifyBFV.checksOK` (diagnostic; the verdict is
`certifyBFV?`'s). -/
def failingChecks (x : InputBFV) : List String :=
  let P := x.P
  let prog := x.prog
  let L := P.src.qs.length
  let cs : List (String × Bool) :=
    [("Spec.schemeParamsOK?", schemeParamsOK? P), ("kind = bfv", decide (P.src.kind = .bfv)),
     ("Spec.Budget.specialOK?", Budget.specialOK? P), ("Spec.Certify.layoutOK?", Spec.Certify.layoutOK? P x.lay),
     ("the program has an output", !prog.outputs.isEmpty),
     ("decOK of every input ciphertext's bound", prog.inputs.all (fun d => decide (d.parts = 1) || !d.ok P.src ||
        decOK P.src.t (P.src.modulus d.level) (TraceBFV.inputBound P prog d))),
     ("a multiplication technique is declared", x.mul.isSome || !prog.body.any Challenge.CertifyBFV.isMul),
     ("a plaintext-addition method is declared", x.plainAdd.isSome || !prog.body.any Challenge.CertifyBFV.isPlainAdd),
     ("modulus switching rounds", x.msRound || !prog.body.any Challenge.CertifyBFV.isMS),
     ("no square under P-over-Q", match x.mul with
        | some (.poverq _) | some (.leveled ..) => !prog.body.any Challenge.CertifyBFV.isSquare
        | _ => true),
     ("one declared internal drop per instruction", match x.mul with
        | some (.leveled _) => decide (x.drops.length = prog.body.length)
        | _ => true),
     ("mulLevels within 1..L", (Challenge.CertifyBFV.mulLevels P.src prog).all (fun ℓ => decide (1 ≤ ℓ) && decide (ℓ ≤ L))),
     ("the side conditions of every instruction (stepChecks)",
        Challenge.CertifyBFV.checksAux x prog.body (Challenge.CertifyBFV.dropsOf x) (initEnv P.src prog fun _ => .exact 0))]
  (cs.filter (!·.2)).map (·.1)

def budgetJ (E : TraceBFV.Budget) : List (String × Json) :=
  [("keySwitch", natJ E.keySwitch), ("modSwitch", natJ E.modSwitch), ("mulLift", natJ E.mulLift),
   ("mulRound", natJ E.mulRound), ("plainAdd", natJ E.plainAdd),
   ("keySwitchBits", bitsJ E.keySwitch), ("mulRoundBits", bitsJ E.mulRound)]

def budgetEq (E F : TraceBFV.Budget) : Bool :=
  E.keySwitch == F.keySwitch && E.modSwitch == F.modSwitch && E.mulLift == F.mulLift &&
    E.mulRound == F.mulRound && E.plainAdd == F.plainAdd

/-- c.input, b, e, f for the extracted program. -/
def checkProg (b : BX) (inp : FHE.Check.BFV.Input) (lay : Budget.KSLayout) : IO Unit := do
  let P := b.P
  let N := b.N
  let t := P.src.t
  let prog := inp.base.prog
  let x0 := FHE.Check.BFV.inputBFV inp lay
  -- one budget per instruction (`budgetBFV x k`), as `certifyBFV?` charges it
  let n := prog.body.length
  let Etrue := budgetBFV x0
  let Emu := budgetBFV (b.mu.input x0)
  let Eat : Nat → TraceBFV.Budget := fun k => b.mu.budget x0 (Emu k)
  let Earr : Array TraceBFV.Budget := (Array.range n).map Eat
  let E : Nat → TraceBFV.Budget := fun k => Earr.getD k (BudgetBFV.budgetOf 0 0 0 0 0)
  let Eideal := budgetBFV { x0 with floatTol := false }
  let Bs0 : Budgets :=
    { E := E 0, textbook := BudgetBFV.budgetOf (BudgetBFV.ksBudget P lay) (BudgetBFV.msBudget P)
        (BudgetBFV.mulLift P) (BudgetBFV.mulRound P) 0,
      ideal := Eideal 0, lay }
  let cert := certifyBFV? x0
  let arbitrary := jBool b.c.pin "inputsArbitrary"
  let progJ := (jObj? b.c.progJson "program").getD Json.null
  let inputsJ := jArr progJ "inputs"
  let originOf : Var → Option String := fun v =>
    inputsJ.findSome? fun d =>
      if jStr? d "name" == some v then (jObj? d "origin").bind (jStr? · "openfhe") else none
  -- the traced internal drop of HPSPOVERQLEVELED, per instruction (`provenance[].internalDrop`)
  let dropOf : Nat → Option Nat := fun k =>
    (jArr b.c.progJson "provenance").findSome? fun p =>
      if jNat? p "index" == some k then jNat? p "internalDrop" else none
  -- the OpenFHE object of a program variable: its own id, or, for `id#k` (a later definition
  -- with the same content-hash id), the object `id`. `id~k` and `id@g~k` have no object.
  let objOf : Var → Option String := fun v =>
    if (b.c.object? v).isSome then some v else
      match v.splitOn "#" with
      | [base, k] => if k.all Char.isDigit && !k.isEmpty && (b.c.object? base).isSome then some base else none
      | _ => none
  let encPt : Var → Option String := fun v =>
    (jArr b.c.pin "encryptions").findSome? fun e =>
      if jStr? e "ct" == some v then jStr? e "pt" else none
  let maxOf := fun (f : TraceBFV.Budget → Nat) => (List.range n).foldl (fun m k => max m (f (E k))) 0
  let Emax := BudgetBFV.budgetOf (maxOf (·.keySwitch)) (maxOf (·.modSwitch)) (maxOf (·.mulLift))
    (maxOf (·.mulRound)) (maxOf (·.plainAdd))
  b.emit "f.budget" "E" "budgetBFV"
    (if b.mu.isNone then cert.map (fun c => (List.range n).all fun k => budgetEq (c.budget k) (E k)) else none) "literal"
    (budgetJ Emax ++
      [("perInstruction", Json.arr ((List.range n).map fun k => Json.mkObj (budgetJ (E k))).toArray),
       ("budgetIsCertificate", match cert with
          | some c => boolJ ((List.range n).all fun k => budgetEq (c.budget k) (Etrue k)) | none => Json.null),
       ("textbook", Json.mkObj (budgetJ Bs0.textbook)),
       ("drops", Json.arr (x0.drops.map (Json.num ·)).toArray),
       ("floatTol", boolJ x0.floatTol), ("inputNoise", natJ P.inputNoise), ("keyNoise", natJ P.keyNoise),
       ("mulLevels", Json.arr ((Challenge.CertifyBFV.mulLevels P.src prog).map (Json.num ·)).toArray),
       ("what", Json.str "Challenge.CertifyBFV.budgetBFV x k for every instruction k (the five numbers printed are the maxima over the instructions); ok: equal to the certificate's c.budget k at every k (null: no certificate)")])
  b.emit "b.decls" "inputs" "Decl.ok" (some (prog.inputs.all fun d => d.ok P.src)) "literal"
  -- inputs
  let mut msgTab : Std.HashMap Var (Array (ZMod P.src.t)) := {}
  let mut recs : Std.HashMap Var VRec := {}
  let mut β : Std.HashMap Var Bnd := {}
  let mut inputsOK := true
  for d in prog.inputs do
    let isPt := d.parts == 1
    let B0 := TraceBFV.inputBound P prog d
    let Bd := if isPt then B0 else B0 / b.mu.freshDiv
    β := β.insert d.name (if isPt then .pt Bd else .ct Bd)
    try
      let origin := originOf d.name
      let objId := if (b.c.object? d.name).isSome then d.name else origin.getD d.name
      let (comps, towers) ← b.x.objComps objId
      let objKind := ((b.c.object? objId).bind (jStr? · "kind")).getD "?"
      let objParts := match b.c.object? objId with
        | some oj => if objKind == "pt" then 1 else (jNat? oj "parts").getD 0
        | none => 0
      b.emit "b.shape" d.name "input" (some (towers == d.level && objParts == d.parts && comps.length == d.parts)) "literal"
        [("level", Json.num d.level), ("towers", Json.num towers), ("parts", Json.num d.parts),
         ("objectParts", Json.num objParts), ("object", Json.str objId)]
      if towers != d.level then throw (IO.userError s!"declared at level {d.level}, object has {towers} towers")
      let ph ← b.x.mkPh comps d.level d.key
      let Q := P.src.modulus d.level
      -- the message: a plaintext's own polynomial mod t; a ciphertext's stored plaintext mod t
      let ptOf : Option String := if isPt then none else
        match origin.bind fun o => (b.c.object? o).bind fun oj => if jStr? oj "kind" == some "pt" then some o else none with
        | some p => some p
        | none => encPt d.name
      let (msg, msgSrc) ← match isPt, ptOf with
        | true, _ => pure (toArr b.K (ofInt P.src.t (ofArr (N := N) ph.Φ)), "the plaintext polynomial mod t")
        | false, some p => do
          let (_, m, _) ← storedPlain b p
          pure (m, s!"stored plaintext {p} mod t")
        | false, none => pure (b.mu.decryptOfPhase N b.K t Q ph.Φ, "bfvDecrypt of the input itself (no recorded plaintext)")
      msgTab := msgTab.insert d.name msg
      let ok := b.mu.inputOK P b.K Bd d.parts ph msg
      let measured := if isPt then normA N ph.Φ else b.mu.noise N b.K t Q ph.Z msg
      let okJ : Option Bool := if arbitrary && !ok then none else some ok
      if okJ == some false then
        inputsOK := false
        b.inputFail.modify (· + 1)
      b.emit "c.input" d.name (if isPt then "PlainOK" else "Encrypts") okJ "forced"
        (measuredBound measured Bd ++
          [("level", Json.num d.level), ("parts", Json.num d.parts), ("key", Json.num d.key),
           ("declared", boolJ true), ("declaredBound", boolJ (prog.boundOf d.name).isSome),
           ("message", Json.str msgSrc)] ++
          (if okJ.isNone then [("why", Json.str "inputsArbitrary: the inputs of this case are hand-built, not encryptions")] else []))
      if b.literal d.parts then
        let sk : IntPoly P.src.N := automorph d.key (ofArr b.s)
        let ctQ : List (Poly Q P.src.N) := comps.map fun c => ofInt Q (ofArr c)
        let lit := decide (comps.length = d.parts) &&
          (if isPt then decide (BGVEncrypts P.src.t Bd sk ctQ (ofArr msg))
           else decide (BFVEncrypts P.src.t Bd sk ctQ (ofArr msg)))
        b.emit "c.input" d.name (if isPt then "PlainOK" else "Encrypts")
          (if arbitrary && !lit then none else some lit) "literal" [("level", Json.num d.level)]
        b.emit "c.input.literal-vs-forced" d.name "input" (some (lit == ok)) "literal+forced"
      let r : VRec := { ph := some ph, parts := d.parts, level := d.level, key := d.key, isPt,
                        tainted := !isPt && !decOK t Q Bd, premiseBad := !ok }
      recs := recs.insert d.name r
      reportVar b d.name "input" r ph msg β[d.name]? arbitrary
        (if (b.c.object? d.name).isSome then some objId else none) []
    catch e =>
      inputsOK := false
      b.emit "b.error" d.name "input" (some false) "forced" [("why", Json.str s!"{e}")]
  b.emit "c.inputs" "inputs" "InputsOK" (if arbitrary && !inputsOK then none else some inputsOK) "forced"
    [("inputs", Json.num prog.inputs.length),
     ("what", Json.str "Spec.TraceBFV.InputsOK: every input passed its c.input line")]
  let tab := msgTab
  let msgs : Var → Msg P.src.t P.src.N := fun v =>
    match tab[v]? with
    | some a => .exact (ofArr a)
    | none => .exact 0
  let mut ρ : Env P.src := initEnv P.src prog msgs
  let mut fmsg : Std.HashMap Var (Array (ZMod P.src.t)) := msgTab
  let mut idx : Nat := 0
  -- the first instruction at which `refRunBFV` rejects (domain, step, bound rule, `bndOK`)
  let mut firstReject : Option (Nat × String) := none
  let mut stepFailed := false
  for i in prog.body do
    let d := Trace.dst i
    let op := opName i
    let dom := domainOK ρ i
    let some ρ' := stepA b.K b.x.mt P.src ρ i
      | do
        b.emit "b.step" d op (some false) "forced"
          [("index", Json.num idx),
           ("why", Json.str s!"Spec.Source.step rejects instruction {idx} ({op}) of the extracted program")]
        stepFailed := true
        if firstReject.isNone then firstReject := some (idx, "Source.step")
        break
    let some v := ρ' d | break
    let βm := β
    let Ei := E idx
    let bnd := b.mu.refBound P Ei v.level (fun y => βm[y]?) i
    let msgArr : Array (ZMod P.src.t) := match v.msg with
      | .exact m => toArr b.K m
    fmsg := fmsg.insert d msgArr
    let ors := (operands i).map fun a => (recs[a]?).getD {}
    let depth := ors.foldl (fun acc r => max acc r.depth) 0 +
      (match i with | .mul .. | .square .. => 1 | _ => 0)
    let cost := match i with
      | .mul .. | .mulPlain .. | .square .. => N * (ors.foldl (fun acc r => acc + r.cost) 0) * (match i with | .square .. => 2 | _ => 1)
      | .automorph .. => N * (ors.foldl (fun acc r => acc + r.cost) 0)
      | _ => ors.foldl (fun acc r => acc + r.cost) 0
    let reject : Option String :=
      if !dom then some "domainOK" else
      match bnd with
      | none => some "refBoundBFV"
      | some bd => if bndOK P v.level bd then none else some "decOK of the bound"
    if let some why := reject then
      if firstReject.isNone then firstReject := some (idx, why)
    let tainted := reject.isSome || ors.any (·.tainted)
    let premiseBad := ors.any (·.premiseBad)
    let mut r : VRec := { parts := v.parts, level := v.level, key := v.key, depth, tainted, premiseBad, cost,
                          stepBad := ors.any (·.stepBad) }
    let dropJ : List (String × Json) := match dropOf idx with
      | some k => [("levelsDropped", Json.num k)]
      | none => []
    let common : List (String × Json) :=
      [("index", Json.num idx), ("level", Json.num v.level), ("parts", Json.num v.parts)] ++ dropJ
    -- the representation OpenFHE holds each recorded operand in (`pin.json: objects[].format`,
    -- written only when it is not EVALUATION), printed where the operands' representations differ
    let fmtOf : Var → Option String := fun y =>
      ((objOf y).bind b.c.object?).map fun o => (jStr? o "format").getD "EVALUATION"
    let opFmts := (operands i).filterMap fun y => (fmtOf y).map fun f => (y, f)
    let fmtJ : List (String × Json) :=
      if (opFmts.map (·.2)).eraseDups.length ≤ 1 then []
      else [("operandFormats", Json.mkObj (opFmts.map fun (y, f) => (y, Json.str f))), ("mixedFormats", boolJ true)]
    try
      let oid := objOf d
      if let some od := oid then
        let (comps, towers) ← b.x.objComps od
        let decrypted := ((b.c.object? od).bind (jObj? · "decrypt")).isSome
        let shapeOK := towers == v.level && comps.length == v.parts && (!decrypted || v.key == 1)
        b.emit "b.shape" d op (some shapeOK) "literal"
          (common ++ [("towers", Json.num towers), ("objectParts", Json.num comps.length), ("key", Json.num v.key)])
        if towers == v.level then
          r := { r with ph := some (← b.x.mkPh comps v.level v.key) }
      else
        match i with
        | .automorph _ a g =>
          if let some pa := (recs[a]?).bind (·.ph) then
            -- no OpenFHE object (the library key-switches first and permutes after): the trusted
            -- automorphism applied to each component of the operand
            let comps := pa.comps.map (autoA N b.K b.x.mt g)
            r := { r with ph := some (← b.x.mkPh comps v.level v.key), synthetic := true }
        | .modSwitch _ a =>
          let ra := (recs[a]?).getD {}
          let q := P.src.qs[v.level]?.getD 0
          r := { r with pend := match ra.ph, ra.pend with
            | some _, _ => some (a, [q])
            | none, some (root, qsD) => some (root, qsD ++ [q])
            | none, none => none }
        | _ => pure ()
      match r.ph with
      | none =>
        if !(match i with | .modSwitch .. => r.pend.isSome | _ => false) then
          b.emit "e.step" d op none "forced"
            (common ++ [("why", Json.str "the destination has no OpenFHE object and cannot be synthesised")])
      | some ph =>
        let recsNow := recs
        let get : Var → Option (Ph × Nat) := fun a => do
          let ra ← recsNow[a]?
          let p ← ra.ph
          pure (p, ra.parts)
        -- composite modulus switch through object-less intermediates (Compress by several limbs)
        let composite : Option (Var × List Nat) := match i with
          | .modSwitch _ a =>
            match (recs[a]?).bind (·.ph), (recs[a]?).bind (·.pend) with
            | none, some (root, qsD) => some (root, qsD ++ [P.src.qs[v.level]?.getD 0])
            | _, _ => none
          | _ => none
        match composite with
        | some (root, qsD) =>
          match get root with
          | none => b.emit "e.step" d op none "forced" (common ++ [("why", Json.str "composite modSwitch: the root has no data")])
          | some (pr, parts) =>
            let qprod := qsD.foldl (· * ·) 1
            let δ := toArr b.K (((qprod : Nat) : Int) • ofArr (N := N) ph.Φ - ofArr pr.Φ)
            let nrm := normA N δ
            -- Σ_j (q_1 ⋯ q_j)·E.modSwitch: the composed contract of the single switches
            let bound := (List.range qsD.length).foldl
              (fun acc j => acc + (qsD.take (j + 1)).foldl (· * ·) 1 * Ei.modSwitch) 0
            let ok := decide (nrm ≤ bound)
            if !ok then
              b.stepFail.modify (· + 1)
              r := { r with stepBad := true }
            b.emit "e.step" d op (some ok) "forced"
              (measuredBound (cdiv nrm qprod) (cdiv bound qprod) ++ common ++
                [("composite", boolJ true), ("mirroredOnly", boolJ true), ("root", Json.str root),
                 ("normDelta", natJ nrm), ("q", natJ qprod), ("budget", natJ Ei.modSwitch),
                 ("operandParts", Json.num parts)])
        | none =>
          match ← stepReport b { Bs0 with E := Ei, ideal := Eideal idx } i v.level ph get with
          | none =>
            b.emit "e.step" d op none "forced" (common ++ [("why", Json.str "an operand has no ciphertext data")])
          | some (ok, fields) =>
            let partsOK := ph.comps.length == v.parts
            if !(ok && partsOK) then
              b.stepFail.modify (· + 1)
              r := { r with stepBad := true }
            b.emit "e.step" d op (some (ok && partsOK)) "forced"
              (fields ++ common ++ fmtJ ++ [("synthetic", boolJ r.synthetic), ("depth", Json.num depth), ("partsOK", boolJ partsOK),
                ("operandSynthetic", boolJ (ors.any (·.synthetic))),
                ("operandsParts", Json.arr (ors.map fun o => Json.num o.parts).toArray)])
        reportVar b d op r ph msgArr bnd arbitrary oid [("index", Json.num idx)]
    catch e =>
      b.emit "b.error" d op (some false) "forced" (common ++ [("why", Json.str s!"{e}")])
    β := match bnd with
      | some bd => β.insert d bd
      | none => β.erase d
    recs := recs.insert d r
    ρ := ρ'
    idx := idx + 1
  let outsDefined := prog.outputs.all fun o => (ρ o).isSome
  if !stepFailed then
    b.emit "b.outputs" "outputs" "eval" (some outsDefined) "forced"
  -- outputs: OpenFHE's own decryption is the plaintext computation
  for o in prog.outputs do
    match objOf o, fmsg[o]? with
    | some od, some m =>
      match ((b.c.object? od).bind (jObj? · "decrypt")).bind (jStr? · "raw") with
      | some rawName =>
        try
          let (raw, rawT) ← b.rawDec rawName
          let r := (recs[o]?).getD {}
          let agree := valsOf m == raw
          -- a wrong output after a violated step contract is NOT excused: it is what the user sees
          let excused := r.tainted || r.premiseBad
          b.emit "b.output" o "output" (if agree then some true else if excused then none else some false) "forced"
            ([("mismatches", Json.num (diffCount (valsOf m) raw)), ("rawEqualsT", Json.num rawT), ("level", Json.num r.level),
              ("tainted", boolJ r.tainted), ("stepBad", boolJ r.stepBad),
              ("what", Json.str "OpenFHE's Decrypt of the output = Source.eval on the recorded input messages")] ++
              (if agree || !excused then [] else [("why", Json.str "the analyzer rejects the program (or the inputs are outside their contract): no claim")]))
        catch e => b.emit "b.output" o "output" (some false) "forced" [("why", Json.str s!"{e}")]
      | none => b.emit "b.output" o "output" none "forced" [("why", Json.str "OpenFHE did not decrypt this output")]
    | _, _ => b.emit "b.output" o "output" none "forced" [("why", Json.str "the output has no OpenFHE object")]
  -- the literal Source.eval on the whole program
  if b.literal 2 then
    match Source.eval P.src prog msgs with
    | none =>
      b.emit "b.eval" "program" "eval" (some false) "literal"
        [("why", Json.str "Spec.Source.eval rejects the extracted program"), ("forcedAlsoRejects", boolJ stepFailed)]
    | some ρL =>
      b.emit "b.eval" "program" "eval" (some (!stepFailed)) "literal" [("forcedAlsoAccepts", boolJ (!stepFailed))]
      for (name, r) in recs.toList do
        if r.cost * N > b.x.o.litCost then
          b.emit "b.literal-vs-forced" name "eval" none "literal+forced"
            [("why", Json.str s!"literal (unmemoised) message would cost about {r.cost * N} coefficient accesses (limit {b.x.o.litCost})")]
        else
          match ρL name, fmsg[name]? with
          | some vL, some fm =>
            match vL.msg with
            | .exact m =>
              let lit := toArr b.K m
              b.emit "b.literal-vs-forced" name "eval"
                (some (lit == fm && vL.level == r.level && vL.parts == r.parts && vL.key == r.key)) "literal+forced"
          | _, _ => b.emit "b.literal-vs-forced" name "eval" (some false) "literal+forced" [("why", Json.str "variable missing")]
  -- the replay of the bounds is the locked reference analyzer's
  let βf := β
  let outBounds : List (Option Nat) := prog.outputs.map fun o =>
    match (βf[o]? : Option Bnd) with
    | some (Bnd.ct bd) => some bd
    | _ => none
  let mine : Option Nat :=
    if P.src.kind == .bfv && (prog.inputs.all fun d => d.ok P.src) && firstReject.isNone && !stepFailed &&
        outsDefined && outBounds.all (·.isSome) then
      some ((outBounds.filterMap id).foldl max 0)
    else none
  if b.mu.isNone then
    let ra := refAnalyzeBFVAt P E prog
    b.emit "f.refAnalyze" "program" "refAnalyzeBFVAt" (some (ra == mine)) "literal"
      [("accepts", boolJ ra.isSome), ("bound", match ra with | some v => natJ v | none => Json.null),
       ("replayBound", match mine with | some v => natJ v | none => Json.null),
       ("firstRejectIndex", match firstReject with | some (k, _) => Json.num k | none => Json.null),
       ("firstRejectWhy", match firstReject with | some (_, w) => Json.str w | none => Json.null),
       ("what", Json.str "the per-variable replay of refRunBFVAt/refBoundBFV used by f.bound returns what Challenge.BFV.refAnalyzeBFVAt returns at the per-instruction budget")]
    -- the verdict
    let tool := FHE.Check.BFV.runCheck inp
    let nStep ← b.stepFail.get
    let nBound ← b.boundFail.get
    let nInput ← b.inputFail.get
    let assumed := match cert with
      | some c => c.assumed.map FHE.Check.BFV.assumptionName
      | none => []
    let outsJ : List Json := match cert with
      | some c => c.outputs.map fun (o, bd) =>
        let lvl := ((ρ o).map (·.level)).getD 0
        let Q := P.src.modulus lvl
        let lim := FHE.Check.BFV.maxNoise t Q
        Json.mkObj [("output", Json.str o), ("level", Json.num lvl), ("bound", natJ bd), ("boundBits", bitsJ bd),
          ("limitBits", match lim with | some m => bitsJ m | none => Json.null),
          ("marginBits", match lim with | some m => slackJ bd m | none => Json.null)]
      | none => []
    let reasons : List String := match cert with
      | some _ => []
      | none =>
        let fc := failingChecks x0
        if !fc.isEmpty then fc.map (s!"checksOK: {·}")
        else match firstReject with
          | some (k, w) => [s!"refAnalyzeBFV rejects at body[{k}] ({w})"]
          | none => if !Encrypt.outputsUnderS? P.src prog then ["an output is not under the secret key itself (outputsUnderS?)"]
            else ["refAnalyzeBFV rejects (outputs)"]
    b.emit "f.verdict" "program" (if cert.isSome then "CERTIFIED" else "NOT CERTIFIED") none "literal"
      [("why", Json.str "information: the verdict of Challenge.CertifyBFV.certifyBFV? on the decoded input"),
       ("certified", boolJ cert.isSome), ("assumed", Json.arr (assumed.map Json.str).toArray),
       ("tool", Json.str tool.label), ("toolHeadline", Json.str tool.headline),
       -- fhe_check certifies only when, besides certifyBFV?, OpenFHE's own decryption of every
       -- output is proved (the locked Challenge.BFVDecryptLib.decryptLibExtOK?)
       ("toolAgrees", boolJ ((tool.verdict == .certified) ==
          (match cert with | some c => Challenge.BFVDecryptLib.decryptLibExtOK? x0 c | none => false))),
       ("bound", match cert with | some c => natJ c.bound | none => Json.null),
       ("boundBits", match cert with | some c => bitsJ c.bound | none => Json.null),
       ("outputs", Json.arr outsJ.toArray), ("reasons", Json.arr (reasons.map Json.str).toArray),
       ("instructions", Json.num prog.body.length),
       ("stepFailures", Json.num nStep), ("boundFailures", Json.num nBound), ("inputFailures", Json.num nInput)]
    let detail : List (String × Json) :=
      [("certified", boolJ cert.isSome), ("stepFailures", Json.num nStep), ("boundFailures", Json.num nBound),
       ("inputFailures", Json.num nInput), ("assumed", Json.arr (assumed.map Json.str).toArray)]
    match cert with
    | some _ =>
      b.emit "f.certified-consistent" "program" "CERTIFIED"
        (some (nStep == 0 && nBound == 0 && nInput == 0)) "glue"
        (detail ++ (if nStep == 0 && nBound == 0 && nInput == 0 then [] else
            [("why", Json.str "a CERTIFIED program has a violated step contract, a noise above its bound, or an input outside its bound")]))
    | none =>
      b.emit "f.certified-consistent" "program" "NOT CERTIFIED" none "glue"
        (detail ++ [("why", Json.str "not certified: no claim to be consistent with")])

end FHE.Pin.BFV
