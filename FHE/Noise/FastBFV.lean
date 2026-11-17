import FHE.Noise.Fast
import Challenge.CertifyBFV.Defs
import Challenge.BFVEncrypt.Defs
import Challenge.BFVDecrypt
import Challenge.BFVDecryptLib

/-!
# FHE.Noise.FastBFV — the BFV analysis and certificate decision in near-linear time
(UNTRUSTED, audited as part of the holes)

The BFV counterpart of `FHE.Noise.Fast`: `Challenge.BFV.refAnalyzeBFVAt` (one budget per
instruction) and `Challenge.CertifyBFV.certifyBFV?` with the environments in search trees
(`Std.TreeMap`) and each replay of the body run once.

* `runBody` calls the locked `Source.step`, `Challenge.BFV.domainOK`, `refBoundBFV` (at the budget
  `E n` of instruction `n`) and `bndOK` themselves, on lookup functions backed by the trees;
  `analyze` is `refAnalyzeBFVAt`.
* `mulLevels`, `budgets`, `checks` are `Challenge.CertifyBFV.mulLevels`, `budgetsBFV` and
  `checksAux` (the replays of `Source.step` that collect the multiplication levels, the budget of
  every instruction and its side conditions), with a tree and an accumulator. They call the
  locked `stepChecks` and a copy of `stepBudget`.
* `certify` is `certifyBFV?`. The functions `…With` below are the locked `stepBudget`,
  `checksOK`, `assumptionsOf` and `maxPlainBound` **word for word**, except that what they
  recompute from the whole program at every use is a parameter: the largest plaintext bound `mpb`
  (for `maxPlainBound x.P x.prog`, recomputed by the locked `stepBudget` at every instruction),
  the input bound `ib` (for `TraceBFV.inputBound x.P x.prog`, a list search per input), the
  multiplication levels `ml` and the result `ca` of the per-instruction checks. Instantiated at
  the locked values they *are* the locked functions by definitional unfolding
  (`Validation.FastBFV`: `rfl`); `certify` passes the same values computed once, with trees. If a
  locked definition changes, the copy here must change with it: the proof fails until it does
  (it cannot silently disagree).

Nothing here is trusted: `Challenge.Fast` states, and `Validation.FastBFV` proves, that
`analyze` and `certify` are **equal** to the locked functions on every input.
-/

namespace FHE.Noise.FastBFV
open Spec Spec.Source Spec.BudgetBFV Spec.CertifyBFV Challenge.BFV Challenge.BFVMul
open Challenge.CertifyBFV
open Spec.TraceBFV (Bnd)
open FHE.Noise.Fast (VMap mapOf boundMap initEnvMap)

/-! ## The analyzer -/

/-- `TraceBFV.inputBound P prog d`, with the declared bounds in a tree. -/
def inputBound (P : FullParams) (bm : VMap ℕ) (d : Decl) : ℕ :=
  (bm[d.name]?).getD (if d.parts = 1 then P.src.t - 1 else P.inputNoise)

/-- The initial bounds of `refAnalyzeBFV`. -/
def initBndMap (P : FullParams) (prog : Program) : VMap Bnd :=
  let bm := boundMap prog
  mapOf (·.name) (fun d => if d.parts = 1 then Bnd.pt (inputBound P bm d)
    else Bnd.ct (inputBound P bm d)) prog.inputs

/-- `Challenge.BFV.refBoundBFV` with `Q` for `P.src.modulus ℓ` (which the reference recomputes,
as a product of the chain, several times per instruction). Word for word otherwise
(`Validation.FastBFV.Aux.refBoundBFVQ_eq`: `rfl` in every case). -/
def refBoundBFVQ (P : FullParams) (E : TraceBFV.Budget) (ℓ Q : ℕ) (β : Var → Option Bnd) :
    Instr → Option Bnd
  | .add _ a b | .sub _ a b =>
    match β a, β b with
    | some (.ct x), some (.ct y) => some (.ct (x + y + Q % P.src.t))
    | _, _ => none
  | .addPlain _ a p | .subPlain _ a p =>
    match β a, β p with
    | some (.ct x), some (.pt y) =>
      some (.ct (x + Q % P.src.t * ((y + P.src.t - 1) / P.src.t) + E.plainAdd))
    | _, _ => none
  | .mulPlain _ a p =>
    match β a, β p with
    | some (.ct x), some (.pt y) =>
      some (.ct (P.src.N * y * (x + Q % P.src.t)))
    | _, _ => none
  | .mul _ a b =>
    match β a, β b with
    | some (.ct x), some (.ct y) =>
      some (.ct (mulBound P.src.N P.src.t Q E.mulLift E.mulRound x y))
    | _, _ => none
  | .square _ a =>
    match β a with
    | some (.ct x) =>
      some (.ct (mulBound P.src.N P.src.t Q E.mulLift E.mulRound x x))
    | _ => none
  | .mulConst _ a c =>
    match β a with
    | some (.ct x) => some (.ct (c.natAbs * (x + Q % P.src.t)))
    | _ => none
  | .copy _ a | .toEval _ a | .toCoeff _ a => β a
  | .automorph _ a _ =>
    match β a with
    | some (.ct x) => some (.ct (x + Q % P.src.t))
    | _ => none
  | .relin _ a | .keySwitch _ a =>
    match β a with
    | some (.ct x) => some (.ct (x + E.keySwitch))
    | _ => none
  | .modSwitch _ a =>
    match β a, P.src.qs[ℓ]? with
    | some (.ct x), some q => some (.ct (x / q + E.modSwitch + Q % P.src.t))
    | _, _ => none
  | .dropLimbs _ _ _ => none

/-- `Challenge.BFV.bndOK` with `Q` for `P.src.modulus ℓ`. -/
def bndOKQ (P : FullParams) (Q : ℕ) : Bnd → Bool
  | .ct b => decOK P.src.t Q b
  | .pt _ => true

/-- `Challenge.BFV.refRunBFVAt` with the environments in trees; `Q ℓ` is the modulus at level `ℓ`
(`P.src.modulus ℓ`, from a table). -/
def runBody (P : FullParams) (E : ℕ → TraceBFV.Budget) (Q : ℕ → ℕ) :
    ℕ → List Instr → VMap (Val P.src) → VMap Bnd → Option (VMap (Val P.src) × VMap Bnd)
  | _, [], ρ, β => some (ρ, β)
  | n, i :: is, ρ, β => do
    guard (domainOK (Pr := P.src) (fun x => ρ[x]?) i)
    let ρ' ← step P.src (fun x => ρ[x]?) i
    let v ← ρ' (Trace.dst i)
    let b ← refBoundBFVQ P (E n) v.level (Q v.level) (fun x => β[x]?) i
    guard (bndOKQ P (Q v.level) b)
    runBody P E Q (n + 1) is (ρ.insert (Trace.dst i) v) (β.insert (Trace.dst i) b)

/-- The part of `refAnalyzeBFVAt` that does not depend on the outputs. -/
def run (P : FullParams) (E : ℕ → TraceBFV.Budget) (prog : Program) :
    Option (VMap (Val P.src) × VMap Bnd) := do
  guard (P.src.kind = .bfv)
  guard (prog.inputs.all fun d => d.ok P.src)
  runBody P E (FHE.Noise.Fast.modAt P (FHE.Noise.Fast.modsOf P)) 0 prog.body
    (initEnvMap P.src prog) (initBndMap P prog)

/-- The part of `refAnalyzeBFVAt` that reads the outputs from the final environments. -/
def outBound {Pr : Params} (r : VMap (Val Pr) × VMap Bnd) (outputs : List Var) : Option ℕ := do
  guard (outputs.all fun o => (r.1[o]?).isSome)
  let bs ← outputs.mapM (ctBound fun x => r.2[x]?)
  pure (bs.foldl max 0)

/-- **The fast BFV analyzer**: equal to `Challenge.BFV.refAnalyzeBFVAt`
(`Challenge.Fast.analyzeBFVFast_eq`). -/
def analyze : NoiseAnalyzerBFVAt := fun P E prog => do
  let r ← run P E prog
  outBound r prog.outputs

/-! ## The levels at which the program multiplies -/

/-- The level of the (first) operand of a `mul` or `square`, if it is defined. -/
def mulHere {Pr : Params} (ρ : VMap (Val Pr)) : Instr → List ℕ
  | .mul _ a _ | .square _ a => ((ρ[a]?).map (·.level)).toList
  | _ => []

/-- `Challenge.CertifyBFV.mulLevelsAux` with the environment in a tree and the levels found so
far in an accumulator (most recent first). -/
def mulLevelsGo (Pr : Params) : List Instr → VMap (Val Pr) → List ℕ → List ℕ
  | [], _, acc => acc.reverse
  | i :: is, ρ, acc =>
    match step Pr (fun x => ρ[x]?) i with
    | some ρ' =>
      match ρ' (Trace.dst i) with
      | some v => mulLevelsGo Pr is (ρ.insert (Trace.dst i) v) (mulHere ρ i ++ acc)
      | none => (mulHere ρ i ++ acc).reverse
    | none => (mulHere ρ i ++ acc).reverse

/-- `Challenge.CertifyBFV.mulLevels`. -/
def mulLevels (Pr : Params) (prog : Program) : List ℕ :=
  (mulLevelsGo Pr prog.body (initEnvMap Pr prog) []).eraseDups

/-- The level of the (first) operand of a `mul`, `square`, `relin` or `keySwitch`, if it is
defined (`Challenge.CertifyBFV.opLevelsAux` at one instruction). -/
def opHere {Pr : Params} (ρ : VMap (Val Pr)) : Instr → List ℕ
  | .mul _ a _ | .square _ a | .relin _ a | .keySwitch _ a => ((ρ[a]?).map (·.level)).toList
  | _ => []

/-- `Challenge.CertifyBFV.opLevelsAux` with the environment in a tree and the levels found so
far in an accumulator (most recent first). The locked one keeps the environment as closures, so
it is quadratic in the program length; `certify` calls this one
(`Validation.FastBFV.Aux2.opLevelsFast_eq`). -/
def opLevelsGo (Pr : Params) : List Instr → VMap (Val Pr) → List ℕ → List ℕ
  | [], _, acc => acc.reverse
  | i :: is, ρ, acc =>
    match step Pr (fun x => ρ[x]?) i with
    | some ρ' =>
      match ρ' (Trace.dst i) with
      | some v => opLevelsGo Pr is (ρ.insert (Trace.dst i) v) (opHere ρ i ++ acc)
      | none => (opHere ρ i ++ acc).reverse
    | none => (opHere ρ i ++ acc).reverse

/-- `Challenge.CertifyBFV.opLevels`. -/
def opLevelsFast (Pr : Params) (prog : Program) : List ℕ :=
  opLevelsGo Pr prog.body (initEnvMap Pr prog) []

/-! ## The checks, the budget and the assumptions, with the program's shape as parameters -/

/-- `Challenge.CertifyBFV.maxPlainBound` with the input bound `ib` as a parameter. -/
def maxPlainBoundWith (prog : Program) (ib : Decl → ℕ) : ℕ :=
  ((prog.inputs.filter (·.parts = 1)).map ib).foldl max 0

/-- `Challenge.CertifyBFV.plainAddAt` with `mpb` for `maxPlainBound x.P x.prog`. -/
def plainAddAtWith (x : InputBFV) (mpb ℓ : ℕ) : ℕ :=
  match x.plainAdd with
  | some .rounded => plainAddRoundedAt x.P ℓ mpb
  | some .scaled => plainAddScaledAt x.P ℓ mpb
  | _ => 0

/-- `Challenge.CertifyBFV.stepBudget` with `mpb` for `maxPlainBound x.P x.prog`. -/
def stepBudgetWith (x : InputBFV) (mpb : ℕ) (ρ : Env x.P.src) (dr : ℕ) (i : Instr) :
    TraceBFV.Budget :=
  let P := x.P
  let ℓ := levelOf ρ (operand i)
  let sl := slackOf x ℓ dr i
  budgetOf
    (match i with
      | .relin .. => ksAt x ℓ dr (P.src.N * P.secretBound * P.secretBound)
      | .keySwitch .. => ksAt x ℓ dr P.secretBound
      | _ => 0)
    (msBudget P) (max (mulLift P) (mulLiftNormAt P ℓ sl.e)) (mulRoundApprox P (max 1 sl.rho))
    (plainAddAtWith x mpb ℓ)

/-- `Challenge.CertifyBFV.budgetsAux` with the environment in a tree and the budgets found so far
in an accumulator (most recent first). -/
def budgetsGo (x : InputBFV) (mpb : ℕ) :
    List Instr → List ℕ → VMap (Val x.P.src) → List TraceBFV.Budget → List TraceBFV.Budget
  | [], _, _, acc => acc.reverse
  | i :: is, ds, ρ, acc =>
    let acc' := stepBudgetWith x mpb (fun y => ρ[y]?) (ds.headD 0) i :: acc
    match step x.P.src (fun y => ρ[y]?) i with
    | some ρ' =>
      match ρ' (Trace.dst i) with
      | some v => budgetsGo x mpb is ds.tail (ρ.insert (Trace.dst i) v) acc'
      | none => acc'.reverse
    | none => acc'.reverse

/-! ### Memoised per-instruction budgets and checks

`stepBudget` and `stepChecks` depend on the instruction only through its kind (`kindOf`) and on
the environment only through the level of the first operand; for a `mul` they evaluate the slack
of the technique and its side conditions (`slackAt`), which is costly. `budgetsGoM`, `checksGoM`
compute each distinct `(level, drop, kind)` once (`Validation.FastBFV`: equal to `budgetsGo`,
`checksGo`). -/

/-- The kind of an instruction, as `stepBudget` and `stepChecks` read it. -/
def kindOf : Instr → ℕ
  | .relin .. => 0
  | .keySwitch .. => 1
  | .mul .. | .square .. => 2
  | _ => 3

/-- A representative instruction of each kind. -/
def reprOf : ℕ → Instr
  | 0 => .relin "d" "a"
  | 1 => .keySwitch "d" "a"
  | 2 => .mul "d" "a" "a"
  | _ => .copy "d" "a"

/-- An environment in which `a` is at level `ℓ`. -/
def envAt (Pr : Params) (ℓ : ℕ) : Env Pr :=
  fun _ => some { msg := .exact 0, parts := 2, level := ℓ, key := 1, scale := 0 }

/-- The memoised value of `f k` (`m` holds earlier `(k, f k)`). -/
def memo {V : Type} (f : ℕ × ℕ × ℕ → V) (m : List ((ℕ × ℕ × ℕ) × V)) (k : ℕ × ℕ × ℕ) :
    V × List ((ℕ × ℕ × ℕ) × V) :=
  match m.find? (·.1 == k) with
  | some p => (p.2, m)
  | none => let v := f k; (v, (k, v) :: m)

/-- `budgetsGo` with the budgets of each `(level, drop, kind)` memoised. -/
def budgetsGoM (x : InputBFV) (mpb : ℕ) :
    List Instr → List ℕ → VMap (Val x.P.src) → List TraceBFV.Budget →
      List ((ℕ × ℕ × ℕ) × TraceBFV.Budget) → List TraceBFV.Budget
  | [], _, _, acc, _ => acc.reverse
  | i :: is, ds, ρ, acc, m =>
    let (b, m') := memo (fun k => stepBudgetWith x mpb (envAt x.P.src k.1) k.2.1 (reprOf k.2.2)) m
      (levelOf (fun y => ρ[y]?) (operand i), ds.headD 0, kindOf i)
    let acc' := b :: acc
    match step x.P.src (fun y => ρ[y]?) i with
    | some ρ' =>
      match ρ' (Trace.dst i) with
      | some v => budgetsGoM x mpb is ds.tail (ρ.insert (Trace.dst i) v) acc' m'
      | none => acc'.reverse
    | none => acc'.reverse

/-- `checksGo` with the checks of each `(level, drop, kind)` memoised. -/
def checksGoM (x : InputBFV) :
    List Instr → List ℕ → VMap (Val x.P.src) → List ((ℕ × ℕ × ℕ) × Bool) → Bool
  | [], _, _, _ => true
  | i :: is, ds, ρ, m =>
    let (c, m') := memo (fun k => stepChecks x (envAt x.P.src k.1) k.2.1 (reprOf k.2.2)) m
      (levelOf (fun y => ρ[y]?) (operand i), ds.headD 0, kindOf i)
    c &&
      match step x.P.src (fun y => ρ[y]?) i with
      | some ρ' =>
        match ρ' (Trace.dst i) with
        | some v => checksGoM x is ds.tail (ρ.insert (Trace.dst i) v) m'
        | none => true
      | none => true

/-- `Challenge.CertifyBFV.checksAux` with the environment in a tree. -/
def checksGo (x : InputBFV) : List Instr → List ℕ → VMap (Val x.P.src) → Bool
  | [], _, _ => true
  | i :: is, ds, ρ =>
    stepChecks x (fun y => ρ[y]?) (ds.headD 0) i &&
      match step x.P.src (fun y => ρ[y]?) i with
      | some ρ' =>
        match ρ' (Trace.dst i) with
        | some v => checksGo x is ds.tail (ρ.insert (Trace.dst i) v)
        | none => true
      | none => true

/-- `Challenge.CertifyBFV.ksDropped` in one pass over the body and the drops (the locked one
reads both by position, which is quadratic). -/
def ksDroppedGo : List Instr → List ℕ → Bool
  | [], _ => false
  | i :: is, ds => (isKS i && ds.headD 0 != 0) || ksDroppedGo is ds.tail

/-- `Challenge.CertifyBFV.assumptionsOf` with `ml` for `mulLevels x.P.src x.prog`, `kd` for
`ksDropped x` and `top` for `(opLevels x.P.src x.prog).contains x.P.src.qs.length`. -/
def assumptionsOfWith (x : InputBFV) (ml : List ℕ) (kd top : Bool) : List AssumptionBFV :=
  let mults := !ml.isEmpty
  let a : AssumptionBFV := if x.floatTol then .binary64 else .idealised
  (match x.mul with
  | some (.hps _) | some (.poverq _) => if mults then [a] else []
  | some (.leveled _) =>
    (if mults || kd then [a] else []) ++ (if top then [.declaredDrops] else [])
  | _ => []) ++
  (if Challenge.CertifyBFV.libTechnique x.mul then [.binary64Dec] else [])

/-- `Challenge.CertifyBFV.plainBoundsOK` with `ib` for `TraceBFV.inputBound x.P x.prog`. -/
def plainBoundsOKWith (P : FullParams) (prog : Program) (ib : Decl → ℕ) : Bool :=
  prog.inputs.all fun d => decide (d.parts ≠ 1) || decide (P.src.t / 2 ≤ ib d)

/-- `Challenge.CertifyBFV.checksOK` with `ib` for `TraceBFV.inputBound x.P x.prog` and `ca` for
the result of `checksAux` on the body. -/
def checksOKWith (x : InputBFV) (ib : Decl → ℕ) (ca : Bool) : Bool :=
  let P := x.P
  let prog := x.prog
  schemeParamsOK? P && decide (P.src.kind = .bfv) && Budget.specialOK? P &&
    Spec.Certify.layoutOK? P x.lay && !prog.outputs.isEmpty &&
    prog.inputs.all (fun d => decide (d.parts = 1) || !d.ok P.src ||
      decOK P.src.t (P.src.modulus d.level) (ib d)) &&
    plainBoundsOKWith P prog ib &&
    (x.mul.isSome || !prog.body.any isMul) &&
    (x.plainAdd.isSome || !prog.body.any isPlainAdd) &&
    (x.msRound || !prog.body.any isMS) &&
    (match x.mul with
      | some (.poverq _) | some (.leveled _) => !prog.body.any isSquare
      | _ => true) &&
    (match x.mul with
      | some (.leveled _) => decide (x.drops.length = prog.body.length)
      | _ => true) &&
    (decide (P.src.t - 1 ≤ P.src.qs.headD 0 / 2) && P.src.qs.all fun q => decide (P.src.t ≤ q)) &&
    Challenge.RealizeBFV.ksDeclOK? P x.lay &&
    ca

/-! ## The decision -/

/-- **The fast BFV certificate decision**: equal to `Challenge.CertifyBFV.certifyBFV?`
(`Challenge.Fast.certifyBFVFast_eq`). -/
def certify (x : InputBFV) : Option CertificateBFV :=
  let ib := inputBound x.P (boundMap x.prog)
  let ρ₀ := initEnvMap x.P.src x.prog
  let ml := mulLevels x.P.src x.prog
  do
    guard (checksOKWith x ib (checksGoM x x.prog.body (dropsOf x) ρ₀ []))
    let bs := (budgetsGoM x (maxPlainBoundWith x.prog ib) x.prog.body (dropsOf x) ρ₀ [] []).toArray
    let E := budgetFn bs
    let r ← run x.P E x.prog
    let B ← outBound r x.prog.outputs
    guard (x.prog.outputs.all fun o => (r.1[o]?).map (·.key) == some 1)
    let outs ← x.prog.outputs.mapM fun o => (outBound r [o]).map fun b => (o, b)
    pure ⟨E, B, outs, ml, assumptionsOfWith x ml (ksDroppedGo x.prog.body x.drops)
      ((opLevelsFast x.P.src x.prog).contains x.P.src.qs.length)⟩

/-! ## The fresh-encryption decision (`Challenge.BFVEncrypt.certifyBFVFresh?`) -/

open Spec.Encrypt Spec.EncryptBFV in
/-- `Spec.EncryptBFV.freshInputNoise` with the fresh names in a tree. -/
def freshInputNoise (P : FullParams) (prog : Program) (fresh : List Var) (ε : ℕ) : ℕ :=
  let fs : VMap Unit := mapOf (fun x => x) (fun _ => ()) fresh
  ε + ((prog.inputs.filter fun d => (fs[d.name]?).isSome).map fun d =>
    encodeDev P.src.t (P.src.modulus d.level)).foldl max 0

/-- `Spec.EncryptBFV.freshOKBFV?` with the name lookups in trees. -/
def freshOKBFV (prog : Program) (fresh : List Var) : Bool :=
  let names : VMap Unit := mapOf (·.name) (fun _ => ()) prog.inputs
  let fs : VMap Unit := mapOf (fun x => x) (fun _ => ()) fresh
  let bm := boundMap prog
  !fresh.isEmpty && (fresh.all fun x => (names[x]?).isSome) &&
  prog.inputs.all fun d =>
    if (fs[d.name]?).isSome then d.parts == 2 && d.key == 1 && (bm[d.name]?).isNone
    else d.parts == 1

/-- `Challenge.BFVEncrypt.certifyAt?` with the fast functions. -/
def certifyAt (x : InputBFV) (fresh : List Var) (ε : ℕ) (used : Spec.Certify.NoiseUsed)
    (drift : ℕ) : Option Spec.EncryptBFV.FreshCertBFV := do
  let P' : FullParams := { x.P with inputNoise := freshInputNoise x.P x.prog fresh ε }
  guard (freshOKBFV x.prog fresh)
  let c ← certify { x with P := P' }
  pure ⟨P', c, used, ε, drift⟩

open Spec.Encrypt Spec.EncryptBFV in
/-- **The fast fresh-encryption BFV decision**: equal to
`Challenge.BFVEncrypt.certifyBFVFresh?` (`Challenge.Fast.certifyBFVFreshFast_eq`). The same text
with `certifyAt` for `certifyAt?`. -/
def certifyFresh (x : InputBFV) : FreshModeBFV → Option FreshCertBFV
  | .worst fresh Bk Bu B1 B2 =>
    certifyAt x fresh (worstError x.P.src.N x.P.secretBound Bk Bu B1 B2) .freshWorst 0
  | .kappa fresh Bk Bu B1 B2 mn md κ => do
    guard (0 < varProxy x.P.src.N x.P.secretBound Bk Bu B1 B2)
    guard (0 < md)
    let (ε, used, drift) := Spec.Certify.freshEps x.P fresh.length Bk Bu B1 B2 mn md κ
    certifyAt x fresh ε used drift
  | .kappaL2 fresh E2 S2 Vu V1 V2 mn md κ => do
    guard (0 < varProxyL2 E2 S2 Vu V1 V2)
    guard (0 < md)
    let drift := meanDrift (E2 + 1 + S2) mn md
    let ε := epsFor (varProxyL2 E2 S2 Vu V1 V2) (fresh.length * (2 * x.P.src.N)) κ + drift
    certifyAt x fresh ε .freshKappaL2 drift

/-! ## The library-decryption check (`Challenge.BFVDecrypt.decryptLibOK?`) -/

/-- `List.foldlM (Source.step Pr)` with the environment in a tree. -/
def stepsGo (Pr : Params) : List Instr → VMap (Val Pr) → Option (VMap (Val Pr))
  | [], ρ => some ρ
  | i :: is, ρ =>
    match step Pr (fun y => ρ[y]?) i with
    | some ρ' =>
      match ρ' (Trace.dst i) with
      | some v => stepsGo Pr is (ρ.insert (Trace.dst i) v)
      | none => none
    | none => none

/-- `Source.eval Pr prog (fun _ => .exact 0)` with the environment in a tree. -/
def evalZ (Pr : Params) (prog : Program) : Option (VMap (Val Pr)) := do
  guard (prog.inputs.all fun dcl => dcl.ok Pr)
  guard (prog.inputs.all fun _ => (Msg.exact (0 : Poly Pr.t Pr.N)).fits Pr.kind)
  let m ← stepsGo Pr prog.body (initEnvMap Pr prog)
  guard (prog.outputs.all fun o => (m[o]?).isSome)
  pure m

/-- **`Challenge.BFVDecrypt.decryptLibOK?`**, with the levels of the outputs read from one
evaluation of the program in a tree (the locked one evaluates the program once per output, on
closures); equal to it (`Challenge.Fast.decryptLibFast_eq`). -/
def decryptLibOK (x : InputBFV) (c : CertificateBFV) : Bool :=
  let ev := evalZ x.P.src x.prog
  (match x.mul with
    | some (.hps _) => true
    | some (.poverq _) => true
    | some (.leveled ..) => true
    | _ => false) &&
  Spec.DecryptBFV.decParamsOK? x.P.src.t x.P.src.qs &&
  x.prog.outputs.all (fun o =>
    (ev.bind fun m => (m[o]?).map (·.level)) == some x.P.src.qs.length) &&
  c.outputs.all (fun ob => Spec.DecryptBFV.decLibOK? x.P.src.t x.P.src.qs ob.2)

/-- **`Challenge.BFVDecryptLib.decryptLibExtOK?`**, with the levels of the outputs read from one
evaluation of the program in a tree; equal to it (`Challenge.Fast.decryptLibExtFast_eq`). -/
def decryptLibExtOK (x : InputBFV) (c : CertificateBFV) : Bool :=
  let ev := evalZ x.P.src x.prog
  match Challenge.BFVDecryptLib.techLib? x.mul with
  | none => false
  | some behz => x.prog.outputs.all fun o =>
      match ev.bind (fun m => (m[o]?).map (·.level)), c.outputs.lookup o with
      | some ℓ, some B => Challenge.BFVDecryptLib.outputLibOK? behz x.P.src.t x.P.src.qs ℓ B
      | _, _ => false

/-- The budgets of the instructions of the program (`Challenge.CertifyBFV.budgetsBFV`;
`Validation.FastBFV.Aux2.budgets_eq`), for the report. -/
def budgets (x : InputBFV) : List TraceBFV.Budget :=
  budgetsGoM x (maxPlainBoundWith x.prog (inputBound x.P (boundMap x.prog))) x.prog.body
    (dropsOf x) (initEnvMap x.P.src x.prog) [] []

end FHE.Noise.FastBFV
