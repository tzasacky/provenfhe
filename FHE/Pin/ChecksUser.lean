import FHE.Pin.ChecksProg
import Spec.Scaling

/-!
# FHE.Pin.ChecksUser — what the user reads after `Decode` (`b.user.*`)
(UNTRUSTED glue around the trusted definitions of `Spec.Scaling`; the forced forms are proved)

For every case with an extracted program, the scaling data `sd : Spec.Scaling.ScaleData` is built
exactly as `fhe_check` builds it (`FHE.Check.decode`, `$.scaling`): from the file's `scaling`
section when it has one; the committed fixtures were recorded before the extractor wrote that
section, so otherwise it is **rebuilt with the extractor's own formula**
(`harness/frontend/openfhe/extract.py`, `"scaling"`): `factors` = every program input's recorded
`scalingFactorInt` (`pin.json` `objects[…].sf` of the input ciphertext / plaintext) modulo `t`,
`marks[i]` = `body[i].op == "mulConst"` in the file's JSON body (the extractor's `negate`, decoded
as `mulConst −1`, is NOT an adjustment), `tracks` = technique ∈ {FLEXIBLEAUTO, FLEXIBLEAUTOEXT}.
Every line says which (`sdSource`), and when the file has the section it is compared with the rule
(`fileVsRule`).

Lines (all `impl` as stated, group `b`):

* `b.user.factors`: `Spec.Scaling.factors? P prog sd` is `some` (the scaling data are printed);
* `b.user.scaleOK`: `Spec.Scaling.scaleOK? P prog sd = true`;
* `b.user.decode` (per output OpenFHE decrypted): the factor `Spec.Scaling.decodeAt?` gives (the
  factor `Decrypt` hands to `Decode` according to `Spec.Scaling.facStep`) = the `scalingFactorInt`
  OpenFHE's `Decrypt` returned (`decrypt.sf`), and its level = the ciphertext's towers. **This link
  is not proved**: that OpenFHE follows `facStep` is the assumption `Challenge.Scaling` names; this
  line is the executed evidence for it;
* `b.user.decrypt` (per such output, when every input's stored plaintext polynomial is recorded):
  with `u x = sf_x⁻¹ • p_x` (in `Z_t`; `p_x` the stored plaintext polynomial of input `x`, for a
  ciphertext input the one `Encrypt` added, `encryptions[].pt`), `Spec.Scaling.userDecrypt P dF ℓ
  s ct` (`dF, ℓ` from `decodeAt?`, `ct` OpenFHE's output ciphertext) = `Spec.Scaling.plainEval prog
  sd.marks u` at the output, **and** OpenFHE's own reading `decrypt.sf⁻¹ • decrypt.raw` = the same.
  Forced (`userDecryptA_spec`, `plainRunA_eq` below) at every `N`; literally (the definitions
  applied to wrapped arrays) at small `N` (`b.user.literal-vs-forced`). `null` where the
  reference analysis does not exclude a phase wrap, an input exceeds its premise, or the inputs are
  hand-built (as `b.raw`), with the comparison still printed.
-/

namespace FHE.Pin
open Lean Spec Spec.NPoly Spec.Scheme Spec.Source Spec.Scaling

/-! ## Forced plain semantics and user-level decryption (kernel-checked equalities) -/

section Plain
variable {t N : ℕ}

/-- `Spec.Scaling.plainInstr` with the loop forms of `*` and `automorph`. -/
def plainInstrF (adj : Bool) (μ : Var → Poly t N) : Instr → (Var → Poly t N)
  | .add d a b | .addPlain d a b => upd μ d (μ a + μ b)
  | .sub d a b | .subPlain d a b => upd μ d (μ a - μ b)
  | .mul d a b | .mulPlain d a b => upd μ d (mulF (μ a) (μ b))
  | .square d a => upd μ d (mulF (μ a) (μ a))
  | .mulConst d a c => upd μ d (if adj then μ a else (c : ZMod t) • μ a)
  -- the trusted (lazy) automorphism: this closure is never forced on the forced path
  -- (`plainDstArr` computes the destination with `Kron.autoArr`); an eager `autoF` here would be
  -- recomputed on every lookup through this step
  | .automorph d a g => upd μ d (automorph g (μ a))
  | .copy d a | .toEval d a | .toCoeff d a | .relin d a | .keySwitch d a | .modSwitch d a
  | .dropLimbs d a _ => upd μ d (μ a)

theorem plainInstrF_eq (adj : Bool) (μ : Var → Poly t N) (i : Instr) :
    plainInstrF adj μ i = plainInstr adj μ i := by
  cases i <;> simp [plainInstrF, plainInstr]

/-- The destination's message of one step as an array: products and automorphisms computed as
arrays (the compiler would re-evaluate an `NPoly`-valued product per coefficient), every other
instruction forced from `plainInstrF`. -/
def plainDstArr (K : ℕ) (adj : Bool) (μ : Var → Poly t N) (i : Instr) : Array (ZMod t) :=
  match i with
  | .mul _ a b | .mulPlain _ a b => mulArrQ (μ a) (μ b)
  | .square _ a => mulArrQ (μ a) (μ a)
  | .automorph _ a g => Kron.autoArr g (μ a)
  | i => toArr K (plainInstrF adj μ i (Trace.dst i))

theorem ofArr_plainDstArr (K : ℕ) (adj : Bool) (μ : Var → Poly t N) (i : Instr) :
    ofArr (plainDstArr K adj μ i) = plainInstrF adj μ i (Trace.dst i) := by
  cases i <;> simp [plainDstArr, plainInstrF, upd, Trace.dst, ofArr_mulArrQ, ofArr_autoArr]

/-- A message table. A structure, so that the compiler does not eta-expand the forced steps
(a definition returning a function would be compiled with the variable as an extra argument, and
every lookup would recompute the whole run). -/
structure Tab (t N : ℕ) where
  f : Var → Poly t N

/-- Update with a tabulated message (`@[noinline]`: `arr` is computed before the closure). -/
@[noinline] def updTab (μ : Var → Poly t N) (d : Var) (arr : Array (ZMod t)) : Tab t N :=
  ⟨upd μ d (ofArr arr)⟩

/-- One forced step: the instruction, then the destination's message tabulated. -/
def plainStepA (K : ℕ) (adj : Bool) (μ : Tab t N) (i : Instr) : Tab t N :=
  let μ' := plainInstrF adj μ.f i
  let d := Trace.dst i
  let arr := plainDstArr K adj μ.f i
  updTab μ' d arr

theorem plainStepA_eq (K : ℕ) (adj : Bool) (μ : Tab t N) (i : Instr) :
    (plainStepA K adj μ i).f = plainInstr adj μ.f i := by
  funext y
  simp only [plainStepA, updTab, upd, ofArr_plainDstArr, plainInstrF_eq]
  split
  · rename_i h; subst h; rfl
  · rfl

/-- Forced `Spec.Scaling.plainRun`. -/
def plainRunA (K : ℕ) : List Instr → List Bool → Tab t N → Tab t N
  | [], _, μ => μ
  | i :: is, ms, μ => plainRunA K is ms.tail (plainStepA K (ms.headD false) μ i)

/-- **`Spec.Scaling.plainRun`** (hence `plainEval prog marks u = (plainRunA K prog.body marks ⟨u⟩).f`). -/
theorem plainRunA_eq (K : ℕ) (body : List Instr) (ms : List Bool) (μ : Tab t N) :
    (plainRunA K body ms μ).f = plainRun body ms μ.f := by
  induction body generalizing ms μ with
  | nil => rfl
  | cons i is ih => simp only [plainRunA, plainRun, ih, plainStepA_eq]

end Plain

/-- Forced `Spec.Scaling.userDecrypt`: the forced switched decryption times `dF⁻¹`. -/
def userDecryptA (K : ℕ) (m : Mut) (P : Params) (dF : ZMod P.t) (ℓ : ℕ) (s : Array ℤ)
    (ct : List (Array ℤ)) : Array (ZMod P.t) :=
  toArr K (dF⁻¹ • (ofArr (N := P.N) (decryptSwitchedA P.N K m P.t (P.qs.take ℓ) s ct)))

/-- **`Spec.Scaling.userDecrypt`.** -/
theorem userDecryptA_spec (K : ℕ) (P : Params) (dF : ZMod P.t) (ℓ : ℕ) (s : Array ℤ)
    (ct : List (Array ℤ)) :
    ofArr (N := P.N) (userDecryptA K .none P dF ℓ s ct) =
      userDecrypt P dF ℓ (ofArr s) (ct.map ofArr) := by
  simp only [userDecryptA, ofArr_toArr, decryptSwitchedA_spec, userDecrypt, List.map_map]
  rfl

/-! ## The check -/

/-- What `checkProg` knows about a variable that the user checks need (wrap / premise taint). -/
structure UserTaint where
  tainted : Bool
  premiseBad : Bool
  /-- Per-coefficient cost of the literal (unmemoised) message (`VarRec.cost`). -/
  cost : Nat

def jNatArr (l : List Nat) : Json := Json.arr (l.map fun n => Json.num n).toArray

/-- `b.user.*` for the extracted program `inp` (module docstring). `taint`: per variable, whether
the reference analysis excludes a wrap there (from `checkProg`). -/
def checkUser (x : Cx) (inp : FHE.Check.Input) (taint : Var → Option UserTaint) : IO Unit := do
  let P := x.P.src
  let N := x.N
  let t := P.t
  let prog := inp.prog
  let technique := x.c.scaling
  let tracksRule := technique == "FLEXIBLEAUTO" || technique == "FLEXIBLEAUTOEXT"
  let arbitrary := jBool x.c.pin "inputsArbitrary"
  let progJ := (jObj? x.c.progJson "program").getD Json.null
  let inputsJ := jArr progJ "inputs"
  let bodyJ := jArr progJ "body"
  let originOf : Var → Option String := fun v =>
    inputsJ.findSome? fun d =>
      if jStr? d "name" == some v then (jObj? d "origin").bind (jStr? · "openfhe") else none
  let objOf : Var → Option String := fun v =>
    if (x.c.object? v).isSome then some v else
      match v.splitOn "#" with
      | [base, k] => if k.all Char.isDigit && !k.isEmpty && (x.c.object? base).isSome then some base else none
      | _ => none
  -- the input objects: (program input, object id, stored-plaintext object id)
  let encs := jArr x.c.pin "encryptions"
  let inputObj : Var → Option (String × Option String) := fun v =>
    let ptId : Option String := (originOf v).bind fun o =>
      match x.c.object? o with
      | some oj => if jStr? oj "kind" == some "pt" then some o else none
      | none => none
    let objId := if (x.c.object? v).isSome then some v else ptId
    objId.map fun oid =>
      match x.c.object? oid with
      | some oj =>
        if jStr? oj "kind" == some "pt" then (oid, some oid)
        else (oid, encs.findSome? fun e => if jStr? e "ct" == some oid then jStr? e "pt" else none)
      | none => (oid, none)
  -- the scaling data, by the extractor's rule
  let ruleFactors : List (Var × Nat) := prog.inputs.filterMap fun d => do
    let (oid, _) ← inputObj d.name
    let sf ← (x.c.object? oid).bind (jNat? · "sf")
    pure (d.name, sf % t)
  let ruleAdj : List Nat := (List.range bodyJ.size).filter fun k =>
    (bodyJ[k]?.bind (jStr? · "op")) == some "mulConst"
  let ruleSD : ScaleData :=
    { factors := ruleFactors, marks := (List.range prog.body.length).map (ruleAdj.contains ·),
      tracks := tracksRule }
  let (sd, sdSource, fileVsRule) : ScaleData × String × Option Bool := match inp.scaling with
    | some f =>
      let same := f.tracks == ruleSD.tracks && f.marks == ruleSD.marks &&
        f.factors.length == ruleSD.factors.length &&
        (ruleSD.factors.all fun (v, n) => (f.factors.lookup v).map (· % t) == some n)
      (f, "file ($.scaling, as fhe_check reads it)", some same)
    | none => (ruleSD, "rebuilt (the fixture predates $.scaling; extract.py's formula: input sf mod t, mulConst indices of the JSON body, technique)", none)
  let adjOf (sd : ScaleData) : List Nat := (List.range sd.marks.length).filter fun k => sd.marks.getD k false
  let sdJ : List (String × Json) :=
    [("technique", Json.str technique), ("sdSource", Json.str sdSource),
     ("tracks", boolJ sd.tracks),
     ("inputFactors", Json.arr (sd.factors.map fun (v, n) => Json.mkObj [("name", Json.str v), ("factor", natJ n)]).toArray),
     ("adjustments", jNatArr (adjOf sd)), ("bodyLength", Json.num prog.body.length)] ++
    (match fileVsRule with
     | some b => [("fileVsRule", boolJ b), ("ruleAdjustments", jNatArr ruleAdj),
                  ("ruleFactors", Json.arr (ruleSD.factors.map fun (v, n) => Json.mkObj [("name", Json.str v), ("factor", natJ n)]).toArray)]
     | none => [])
  let F? := factors? P prog sd
  x.emit "b.user.factors" "program" "factors?" (some (F?.isSome && fileVsRule != some false)) "literal"
    (sdJ ++ (if F?.isSome then [] else [("why", Json.str "Spec.Scaling.factors? is none: an input without a declared factor, an addition/subtraction of operands with different true factors, a modSwitch without a limb to drop, or rescale")]) ++
     (if fileVsRule == some false then [("why", Json.str "the file's $.scaling differs from the extractor's rule")] else []))
  let sOK := scaleOK? P prog sd
  -- per output: the factors (for the report)
  let outFac : List (Var × Option (Fac t)) := prog.outputs.map fun o => (o, F?.bind (· o))
  x.emit "b.user.scaleOK" "program" "scaleOK?" (some sOK) "literal"
    ([("technique", Json.str technique), ("sdSource", Json.str sdSource),
      ("outputs", Json.arr (outFac.map fun (o, f) => Json.mkObj ([("name", Json.str o)] ++ match f with
        | some f => [("phi", natJ f.phi.val), ("lam", natJ f.lam.val), ("level", Json.num f.level),
                     ("decodeFactor", natJ (decodeFactor P sd.tracks f).val),
                     ("phiTimesDecScale", natJ (f.phi * Decrypt.decScale P f.level).val)]
        | none => [("factor", Json.null)])).toArray)])
  -- the user's input messages u x = sf_x⁻¹ • p_x
  let mut uTab : Std.HashMap Var (Array (ZMod t)) := {}
  let mut missing : List String := []
  for d in prog.inputs do
    match inputObj d.name with
    | none => missing := missing ++ [s!"{d.name}: no OpenFHE object"]
    | some (oid, none) => missing := missing ++ [s!"{d.name}: the stored plaintext of {oid} is not recorded"]
    | some (_, some pt) =>
      try
        let some pj := x.c.object? pt | throw (IO.userError s!"object {pt}")
        let some pn := jStr? pj "poly" | throw (IO.userError s!"object {pt}: poly")
        let (pm, v) ← liftExcept (x.c.rnsPolyAny pn)
        let vc := centredA N x.K .none (pm.foldl (· * ·) 1) v
        let p : Poly t N := ofInt t (ofArr (N := N) vc)
        let f := inputFactor P sd d.name
        if f * f⁻¹ != 1 then
          missing := missing ++ [s!"{d.name}: its factor {f.val} is not invertible modulo t"]
        else
          uTab := uTab.insert d.name (toArr x.K (f⁻¹ • p))
      catch e => missing := missing ++ [s!"{d.name}: {e}"]
  let uT := uTab
  let u : Var → Poly t N := fun v => match uT[v]? with
    | some a => ofArr a
    | none => 0
  let plainF : Tab t N := plainRunA x.K prog.body sd.marks ⟨u⟩
  for o in prog.outputs do
    let some oid := objOf o
      | x.emit "b.user.decode" o "decodeAt?" none "literal"
          [("technique", Json.str technique), ("why", Json.str "the output has no OpenFHE object")]
    let some oj := x.c.object? oid | continue
    let some dj := jObj? oj "decrypt"
      | x.emit "b.user.decode" o "decodeAt?" none "literal"
          [("technique", Json.str technique), ("object", Json.str oid),
           ("why", Json.str s!"OpenFHE did not decrypt this ciphertext ({(jStr? oj "decryptError").getD "decrypt is null"})")]
    let towers := (jNat? oj "towers").getD 0
    let decSf? := jNat? dj "sf"
    let common : List (String × Json) := [("technique", Json.str technique), ("object", Json.str oid),
      ("towers", Json.num towers), ("sdSource", Json.str sdSource)]
    match decodeAt? P prog sd o, decSf? with
    | none, _ =>
      x.emit "b.user.decode" o "decodeAt?" (some false) "literal"
        (common ++ [("why", Json.str "Spec.Scaling.decodeAt? is none")])
    | _, none =>
      x.emit "b.user.decode" o "decodeAt?" (some false) "literal"
        (common ++ [("why", Json.str "decrypt.sf missing")])
    | some (dF, ℓ), some decSf =>
      let okD := dF.val == decSf % t && ℓ == towers
      x.emit "b.user.decode" o "decodeAt?" (some okD) "literal"
        (common ++ [("decodeFactor", natJ dF.val), ("openfheDecryptSf", natJ (decSf % t)),
          ("level", Json.num ℓ),
          ("link", Json.str "NOT PROVED: that OpenFHE's Decrypt returns the factor Spec.Scaling.facStep/decodeFactor predict is the assumption Challenge.Scaling names; this line is executed evidence")] ++
          (if okD then [] else [("why", Json.str (if ℓ != towers then "decodeAt?'s level differs from the ciphertext's towers" else "decodeAt?'s factor differs from the scalingFactorInt OpenFHE's Decrypt returned"))]))
      -- user-level decryption against the plain semantics
      if !missing.isEmpty then
        x.emit "b.user.decrypt" o "userDecrypt" none "forced"
          (common ++ [("why", Json.str s!"not every input's stored plaintext is usable: {missing}")])
        continue
      try
        let (comps, _) ← x.objComps oid
        let some rawName := jStr? dj "raw" | throw (IO.userError "decrypt.raw missing")
        let raw ← x.rawPoly rawName t
        let key := ((x.c.object? oid).bind (jNat? · "key")).getD 1
        let _ := key
        let userF := userDecryptA x.K x.mt P dF ℓ x.s comps
        let plain := toArr x.K (plainF.f o)
        let decInv := ((decSf : ZMod t))⁻¹
        let ofhe := toArr x.K (decInv • (ofArr (N := N) (raw.map fun (z : Int) => ((z : ZMod t))) : Poly t N))
        let userOK := userF == plain
        let ofheOK := ofhe == plain
        let tn := taint o
        let excused := arbitrary || (tn.map (·.tainted)).getD false || (tn.map (·.premiseBad)).getD false
        let ok := userOK && ofheOK
        x.emit "b.user.decrypt" o "userDecrypt" (if ok then some true else if excused then none else some false) "forced"
          (common ++ [("userDecryptEqPlain", boolJ userOK), ("openfheReadEqPlain", boolJ ofheOK),
            ("mismatches", Json.num (diffCount userF plain)), ("openfheMismatches", Json.num (diffCount ofhe plain)),
            ("decodeFactor", natJ dF.val), ("openfheDecryptSf", natJ (decSf % t)),
            ("plainHead", Json.arr ((valsOf plain).extract 0 4 |>.map fun z => intJ z)),
            ("userHead", Json.arr ((valsOf userF).extract 0 4 |>.map fun z => intJ z))] ++
            (if ok then [] else [("why", Json.str (if excused then
              "the reference analysis does not exclude a phase wrap here, or an input exceeds its premise, or the inputs are hand-built (as b.raw)"
              else "the user-level decryption differs from the plain semantics of the program on the user's messages"))]))
        let litPlain := x.o.mu = .none && N ≤ x.o.litMaxN &&
          ((tn.map (·.cost)).getD (x.o.litCost + 1)) * N ≤ x.o.litCost
        if litPlain && x.literal comps.length then
          let qsℓ := P.qs.take ℓ
          let ctQ : List (IntPoly N) := comps.map ofArr
          let litUser := toArr x.K (dF⁻¹ • Decrypt.bgvDecryptSwitched t qsℓ (ofArr x.s) (ctQ.map (ofInt qsℓ.prod)))
          let litPlainO := toArr x.K (plainEval prog sd.marks u o)
          x.emit "b.user.literal-vs-forced" o "userDecrypt" (some (litUser == userF)) "literal+forced" common
          x.emit "b.user.literal-vs-forced" o "plainEval" (some (litPlainO == plain)) "literal+forced" common
      catch e =>
        x.emit "b.user.decrypt" o "userDecrypt" (some false) "forced" (common ++ [("why", Json.str s!"{e}")])

end FHE.Pin
