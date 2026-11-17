import Challenge.CertifyBFV.Library
import FHE.Pin.BFV.Load
import FHE.Pin.BFV.Stage
import FHE.Pin.BFV.Float64
import FHE.Check.BFVBudget

/-!
# FHE.Pin.BFV.AlgoLibrary — `Challenge.CertifyBFV.runLibrary` against the recorded objects
(UNTRUSTED glue; the equality of the forced execution is proved)

`algo.runLibrary`: on a recorded BFV program that `certifyBFV?` CERTIFIES, the locked
`Challenge.CertifyBFV.runLibrary x A rk gk cts` (the declared technique's algorithms, instruction
by instruction: `libStep`) is executed on the recorded input ciphertexts, the recorded
relinearization keys `rk` and rotation keys `gk g` (CRT lifts of the stored limbs), in the
binary64 arithmetic of the build (`A64`, or `A64fma` if `build.float.fmaContraction`); every
intermediate and output ciphertext that has a recorded object is compared with it, limb for limb.

Execution: `runLibF` is `runLibraryAux` with every instruction's result forced once
(`frcL`), the products of the multiplications by the forced pipelines of `FHE.Pin.BFV.Stage`, the
key switches by `ksBFVF` (every ModUp or CRT digit forced once, every product a Kronecker product,
`FHE.Pin.Kron.mulNeg_eq`), the plaintext products by `mulA` and the automorphisms by the
linear-time scatter (`FHE.Pin.Kron.autoL_eq`); `runLibF_eq` proves it equal to the locked
`runLibraryAux`. `runLibL` is the same execution with the ciphertext environment kept as a list
(`runLibL_eq`, `runLibrary_list`): that is what the checker runs. So the check runs at real ring
dimensions (cap: `max --library-max-n (forced cap)`, the forced cap of the multiplications,
`--forced-max-n`).
-/

namespace FHE.Pin.BFV
open Lean Spec Spec.NPoly Spec.Source Spec.CertifyBFV Challenge.CertifyBFV FHE.Pin
open Challenge.CertifyBFV (operand levelOf)


/-! ## `libStep` with forced intermediates (proved equal) -/

/-- `libMul` with the forced pipelines of `FHE.Pin.BFV.Stage`. -/
def libMulF (K : ℕ) (x : InputBFV) (A : Spec.Float.Arith) (n ℓ : ℕ) (ca cb : List (IntPoly x.P.src.N)) :
    List (IntPoly x.P.src.N) :=
  let t := x.P.src.t
  let qs := x.P.src.qs.take ℓ
  match x.mul with
  | some (.hps R) => hpsForced K (Challenge.BFVMul.Fl.floatSums A) t qs R ca cb
  | some (.poverq Ps) => poverqForced K (Challenge.BFVMul.Fl.floatSums A) t qs (Ps.take ℓ) ca cb
  | some (.leveled Ps) =>
    if ℓ = x.P.src.qs.length ∧ x.drops.getD n 0 ≠ 0 then
      leveledForced K (Challenge.BFVMul.Fl.floatSums A) t qs Ps (x.drops.getD n 0) ca cb
    else poverqForced K (Challenge.BFVMul.Fl.floatSums A) t qs (Ps.take ℓ) ca cb
  | some (.behz B msk mt) => behzForced K t qs B msk mt ca cb
  | _ => Challenge.BFV.bfvMul t (x.P.src.modulus ℓ) ca cb

theorem libMulF_eq (K : ℕ) (x : InputBFV) (A : Spec.Float.Arith) (n ℓ : ℕ) (ca cb : List (IntPoly x.P.src.N)) :
    libMulF K x A n ℓ ca cb = libMul x A n ℓ ca cb := by
  delta libMulF libMul
  rcases h : x.mul with _ | t
  · rfl
  · cases t <;> simp [hpsForced_eq, poverqForced_eq, leveledForced_eq, behzForced_eq]

/-- The component `Fl.leveledKS` switches: the third of three, the second of two. -/
def selComp {N : ℕ} : List (IntPoly N) → IntPoly N
  | [_, _, c2] => c2
  | [_, c1] => c1
  | _ => 0

/-- `Fl.leveledKS` applies its key switch once, to the scaled-down switched component: with that
pair computed (and forced) first, the result is the same. -/
theorem leveledKS_hoist {N : ℕ} (S : Challenge.BFVMul.Fl.Sums) (qs : List ℕ) (drop : ℕ)
    (core : IntPoly N → IntPoly N × IntPoly N) (ct : List (IntPoly N)) :
    Challenge.BFVMul.Fl.leveledKS S qs drop core ct =
      Challenge.BFVMul.Fl.leveledKS S qs drop
        (fun _ => core (Challenge.BFVMul.Fl.scaleDown S qs (qs.length - drop) (selComp ct))) ct := by
  rcases ct with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, rest⟩⟩⟩⟩ <;> rfl

/-! ## The key switch with its products by Kronecker substitution (proved equal)

`Challenge.RealizeBFV.ksBFV` executed as written evaluates, for every coefficient of its result,
the schoolbook products of `Challenge.Realize.innerKey` (or of `ksBV`), and inside them every
coefficient of a ModUp digit (a fast base conversion with its modular inverses) once per term:
`N²` big-integer products and `N²` base conversions per digit. `ksBFVF` is the same composition
with every ModUp digit (or CRT digit) forced once, every product `mulA` (Kronecker substitution,
`FHE.Pin.Kron.mulNeg_eq`), and every inner product and ModDown forced: `ksBFVF_eq`. -/

/-- Evaluate every coefficient once, as an array (`toArr` behind a call boundary of its own). -/
@[noinline] def forceA {N : ℕ} (K : ℕ) (p : IntPoly N) : Array ℤ := toArr K p

/-- The Kronecker product of two polynomials, each forced to an array once, as an ARRAY (the
pipelines below keep products as arrays in lists and wrap them with `ofArr` afterwards, as
`FHE.Pin.BFV.mulLimbsF` does: a polynomial-valued lambda can be re-evaluated per coefficient by
the compiled code). -/
def mulA {N : ℕ} (K : ℕ) (a b : IntPoly N) : Array ℤ := Kron.mulNeg N (forceA K a) (forceA 1 b)

@[simp] theorem ofArr_mulA {N : ℕ} (K : ℕ) (a b : IntPoly N) : (ofArr (mulA K a b) : IntPoly N) = a * b := by
  have h := Kron.mulNeg_eq N (toArr K a) (toArr 1 b)
  have e : ∀ arr : Array ℤ, (ofArr arr : IntPoly N) = Kron.ofArrZ N arr := fun _ => rfl
  show ofArr (Kron.mulNeg N (toArr K a) (toArr 1 b)) = a * b
  rw [e, h, ← e, ← e, ofArr_toArr, ofArr_toArr]

/-- `Challenge.Realize.innerKey` with every ModUp digit forced once and every product `mulA`,
the sum forced. -/
def innerKeyF (K : ℕ) (P : FullParams) (lay : Spec.Budget.KSLayout) (ℓ : ℕ) (d : IntPoly P.src.N)
    (k : ℕ → IntPoly P.src.N) : IntPoly P.src.N :=
  frc K ((List.ofFn fun j : Fin (lay.sizes ℓ).length =>
    mulA K (Challenge.Realize.modUpDigit P lay ℓ d j) (k j)).map ofArr).sum

theorem innerKeyF_eq (K : ℕ) (P : FullParams) (lay : Spec.Budget.KSLayout) (ℓ : ℕ)
    (d : IntPoly P.src.N) (k : ℕ → IntPoly P.src.N) :
    innerKeyF K P lay ℓ d k = Challenge.Realize.innerKey P lay ℓ d k := by
  simp only [innerKeyF, frc_eq, List.map_ofFn, Function.comp_def, ofArr_mulA]
  rfl

/-- `Challenge.Realize.ksOpenFHE` with `innerKeyF` and the ModDown forced. -/
def ksOpenFHEF (K : ℕ) (P : FullParams) (lay : Spec.Budget.KSLayout) (ℓ : ℕ) (d : IntPoly P.src.N)
    (keys : List (IntPoly P.src.N × IntPoly P.src.N)) : IntPoly P.src.N × IntPoly P.src.N :=
  (frc K (Challenge.Realize.modDownBGV P (innerKeyF K P lay ℓ d fun j => (keys.getD j (0, 0)).1)),
   frc K (Challenge.Realize.modDownBGV P (innerKeyF K P lay ℓ d fun j => (keys.getD j (0, 0)).2)))

theorem ksOpenFHEF_eq (K : ℕ) (P : FullParams) (lay : Spec.Budget.KSLayout) (ℓ : ℕ)
    (d : IntPoly P.src.N) (keys : List (IntPoly P.src.N × IntPoly P.src.N)) :
    ksOpenFHEF K P lay ℓ d keys = Challenge.Realize.ksOpenFHE P lay ℓ d keys := by
  simp only [ksOpenFHEF, frc_eq, innerKeyF_eq]
  rfl

/-- `Challenge.RealizeBFV.ksBV` with every CRT digit forced once, every product `mulA` and both
sums forced. -/
def ksBVF (K : ℕ) (P : FullParams) (ℓ : ℕ) (d : IntPoly P.src.N)
    (keys : List (IntPoly P.src.N × IntPoly P.src.N)) : IntPoly P.src.N × IntPoly P.src.N :=
  (frc K ((List.ofFn fun i : Fin ℓ =>
      mulA K (Challenge.RealizeBFV.crtDigit (P.src.qs.getD i 0) d) (keys.getD i (0, 0)).1).map ofArr).sum,
   frc K ((List.ofFn fun i : Fin ℓ =>
      mulA K (Challenge.RealizeBFV.crtDigit (P.src.qs.getD i 0) d) (keys.getD i (0, 0)).2).map ofArr).sum)

theorem ksBVF_eq (K : ℕ) (P : FullParams) (ℓ : ℕ) (d : IntPoly P.src.N)
    (keys : List (IntPoly P.src.N × IntPoly P.src.N)) :
    ksBVF K P ℓ d keys = Challenge.RealizeBFV.ksBV P ℓ d keys := by
  simp only [ksBVF, frc_eq, List.map_ofFn, Function.comp_def, ofArr_mulA]
  rfl

/-- `Challenge.RealizeBFV.ksBFV` by `ksBVF` / `ksOpenFHEF`. -/
def ksBFVF (K : ℕ) (P : FullParams) (lay : Spec.Budget.KSLayout) (ℓ : ℕ) (d : IntPoly P.src.N)
    (keys : List (IntPoly P.src.N × IntPoly P.src.N)) : IntPoly P.src.N × IntPoly P.src.N :=
  if P.store.special = [] then ksBVF K P ℓ d keys
  else ksOpenFHEF K (Spec.BudgetBFV.unitPlain P) lay ℓ d keys

/-- **The forced key switch is the locked `Challenge.RealizeBFV.ksBFV`.** -/
theorem ksBFVF_eq (K : ℕ) (P : FullParams) (lay : Spec.Budget.KSLayout) (ℓ : ℕ)
    (d : IntPoly P.src.N) (keys : List (IntPoly P.src.N × IntPoly P.src.N)) :
    ksBFVF K P lay ℓ d keys = Challenge.RealizeBFV.ksBFV P lay ℓ d keys := by
  have e1 := ksBVF_eq K P ℓ d keys
  have e2 := ksOpenFHEF_eq K (Spec.BudgetBFV.unitPlain P) lay ℓ d keys
  show (if P.store.special = [] then ksBVF K P ℓ d keys
      else ksOpenFHEF K (Spec.BudgetBFV.unitPlain P) lay ℓ d keys) =
    (if P.store.special = [] then Challenge.RealizeBFV.ksBV P ℓ d keys
      else Challenge.Realize.ksOpenFHE (Spec.BudgetBFV.unitPlain P) lay ℓ d keys)
  exact ite_congr rfl (fun _ => e1) (fun _ => e2)

/-- `Challenge.RealizeBFV.relinBFV` with `ksBFVF`, computed once. -/
def relinBFVF (K : ℕ) (P : FullParams) (lay : Spec.Budget.KSLayout) (ℓ : ℕ)
    (ca : List (IntPoly P.src.N)) (keys : List (IntPoly P.src.N × IntPoly P.src.N)) :
    List (IntPoly P.src.N) :=
  match ca with
  | [c0, c1, c2] =>
    let r := ksBFVF K P lay ℓ c2 keys
    [c0 + r.1, c1 + r.2]
  | _ => []

theorem relinBFVF_eq (K : ℕ) (P : FullParams) (lay : Spec.Budget.KSLayout) (ℓ : ℕ)
    (ca : List (IntPoly P.src.N)) (keys : List (IntPoly P.src.N × IntPoly P.src.N)) :
    relinBFVF K P lay ℓ ca keys = Challenge.RealizeBFV.relinBFV P lay ℓ ca keys := by
  rcases ca with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨e, rest⟩⟩⟩⟩
  · rfl
  · rfl
  · rfl
  · simp only [relinBFVF, ksBFVF_eq]
    rfl
  · rfl

/-- `Challenge.RealizeBFV.keySwitchBFV` with `ksBFVF`, computed once. -/
def keySwitchBFVF (K : ℕ) (P : FullParams) (lay : Spec.Budget.KSLayout) (ℓ : ℕ)
    (ca : List (IntPoly P.src.N)) (keys : List (IntPoly P.src.N × IntPoly P.src.N)) :
    List (IntPoly P.src.N) :=
  match ca with
  | [c0, c1] =>
    let r := ksBFVF K P lay ℓ c1 keys
    [c0 + r.1, r.2]
  | _ => []

theorem keySwitchBFVF_eq (K : ℕ) (P : FullParams) (lay : Spec.Budget.KSLayout) (ℓ : ℕ)
    (ca : List (IntPoly P.src.N)) (keys : List (IntPoly P.src.N × IntPoly P.src.N)) :
    keySwitchBFVF K P lay ℓ ca keys = Challenge.RealizeBFV.keySwitchBFV P lay ℓ ca keys := by
  rcases ca with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
  · rfl
  · rfl
  · simp only [keySwitchBFVF, ksBFVF_eq]
    rfl
  · rfl

/-- `libKS` with the forced key switch `ksBFVF` (and, for a leveled operand, the switched
component scaled down and forced first). -/
def libKSF (K : ℕ) (x : InputBFV) (A : Spec.Float.Arith) (n ℓ : ℕ) (ca : List (IntPoly x.P.src.N))
    (keys : List (IntPoly x.P.src.N × IntPoly x.P.src.N)) : List (IntPoly x.P.src.N) :=
  let dr := x.drops.getD n 0
  match x.mul with
  | some (.leveled _) =>
    if ℓ = x.P.src.qs.length then
      let qs := x.P.src.qs.take ℓ
      let S := Challenge.BFVMul.Fl.floatSums A
      let sel : IntPoly x.P.src.N := selComp ca
      let d := frc K (Challenge.BFVMul.Fl.scaleDown S qs (qs.length - dr) sel)
      let ab := ksBFVF K x.P x.lay (ℓ - dr) d keys
      Challenge.BFVMul.Fl.leveledKS S qs dr (fun _ => ab) ca
    else if ca.length = 3 then relinBFVF K x.P x.lay ℓ ca keys
      else keySwitchBFVF K x.P x.lay ℓ ca keys
  | _ => if ca.length = 3 then relinBFVF K x.P x.lay ℓ ca keys
      else keySwitchBFVF K x.P x.lay ℓ ca keys

theorem libKSF_eq (K : ℕ) (x : InputBFV) (A : Spec.Float.Arith) (n ℓ : ℕ) (ca : List (IntPoly x.P.src.N))
    (keys : List (IntPoly x.P.src.N × IntPoly x.P.src.N)) :
    libKSF K x A n ℓ ca keys = libKS x A n ℓ ca keys := by
  have hp : (if ca.length = 3 then relinBFVF K x.P x.lay ℓ ca keys
        else keySwitchBFVF K x.P x.lay ℓ ca keys) =
      (if ca.length = 3 then Challenge.RealizeBFV.relinBFV x.P x.lay ℓ ca keys
        else Challenge.RealizeBFV.keySwitchBFV x.P x.lay ℓ ca keys) := by
    rw [relinBFVF_eq, keySwitchBFVF_eq]
  delta libKSF libKS
  cases h : x.mul with
  | none => exact hp
  | some tech =>
    cases tech with
    | leveled Ps =>
      simp only
      by_cases hℓ : ℓ = x.P.src.qs.length
      · simp only [hℓ, ite_true]
        rw [leveledKS_hoist _ _ _ (fun c => Challenge.RealizeBFV.ksBFV x.P x.lay (x.P.src.qs.length - x.drops.getD n 0) c keys)]
        simp [frc_eq, ksBFVF_eq]
      · simp only [hℓ, ite_false]
        exact hp
    | _ => exact hp

/-- `libStep` with `libMulF` and `libKSF`. -/
def libStepF (K : ℕ) (x : InputBFV) (A : Spec.Float.Arith)
    (rk : List (IntPoly x.P.src.N × IntPoly x.P.src.N))
    (gk : ℕ → List (IntPoly x.P.src.N × IntPoly x.P.src.N)) (n : ℕ) (ρ : Env x.P.src)
    (σ : Trace.CtEnv x.P) (i : Instr) : List (IntPoly x.P.src.N) :=
  let get := fun v => (σ v).getD []
  let ℓ := levelOf ρ (operand i)
  match i with
  | .mul _ a b => libMulF K x A n ℓ (get a) (get b)
  | .square _ a => libMulF K x A n ℓ (get a) (get a)
  | .relin _ a => libKSF K x A n ℓ (get a) rk
  | .keySwitch _ a =>
    let g := ((ρ a).map (·.key)).getD 1
    (((libKSF K x A n ℓ (((get a).map (Kron.autoArr (rotInv x.P.src.N g))).map Kron.ofArrD) (gk g)).map
      (Kron.autoArr g)).map Kron.ofArrD)
  | .mulPlain _ a p =>
    let pp := (get p).headD 0
    ((get a).map fun c => mulA K pp c).map ofArr
  | .automorph _ a g => ((get a).map (Kron.autoArr g)).map Kron.ofArrD
  | _ => libStep x A rk gk n ρ σ i

theorem libStepF_eq (K : ℕ) (x : InputBFV) (A : Spec.Float.Arith)
    (rk : List (IntPoly x.P.src.N × IntPoly x.P.src.N))
    (gk : ℕ → List (IntPoly x.P.src.N × IntPoly x.P.src.N)) (n : ℕ) (ρ : Env x.P.src)
    (σ : Trace.CtEnv x.P) (i : Instr) :
    libStepF K x A rk gk n ρ σ i = libStep x A rk gk n ρ σ i := by
  cases i with
  | mul d a b' => exact libMulF_eq _ _ _ _ _ _ _
  | square d a => exact libMulF_eq _ _ _ _ _ _ _
  | relin d a => exact libKSF_eq _ _ _ _ _ _ _
  | keySwitch d a =>
    change List.map Kron.ofArrD (List.map (Kron.autoArr _)
        (libKSF K x A n _ (List.map Kron.ofArrD (List.map (Kron.autoArr _) _)) _)) =
      List.map (automorph _) (libKS x A n _ (List.map (automorph _) _) _)
    simp only [List.map_map]
    have e' : ∀ g, (Kron.ofArrD ∘ Kron.autoArr g : IntPoly x.P.src.N → IntPoly x.P.src.N) = automorph g :=
      fun g => funext (Kron.autoL_eq g)
    simp only [e']
    exact congrArg (List.map (automorph _)) (libKSF_eq _ _ _ _ _ _ _)
  | mulPlain d a p =>
    change List.map ofArr (List.map (fun c => mulA K (((σ p).getD []).headD 0) c)
        ((σ a).getD [])) = List.map (fun c => ((σ p).getD []).headD 0 * c) ((σ a).getD [])
    simp only [List.map_map, Function.comp_def, ofArr_mulA]
  | automorph d a g =>
    change List.map Kron.ofArrD (List.map (Kron.autoArr g) ((σ a).getD [])) =
      List.map (automorph g) ((σ a).getD [])
    rw [List.map_map, show (Kron.ofArrD ∘ Kron.autoArr g : IntPoly x.P.src.N → IntPoly x.P.src.N) =
      automorph g from funext (Kron.autoL_eq g)]
  | _ => rfl

/-- `runLibraryAux` with every result forced once. -/
def runLibF (x : InputBFV) (A : Spec.Float.Arith) (K : ℕ)
    (rk : List (IntPoly x.P.src.N × IntPoly x.P.src.N))
    (gk : ℕ → List (IntPoly x.P.src.N × IntPoly x.P.src.N)) :
    ℕ → List Instr → Env x.P.src → Trace.CtEnv x.P → Trace.CtEnv x.P
  | _, [], _, σ => σ
  | n, i :: is, ρ, σ =>
    match step x.P.src ρ i with
    | some ρ' => runLibF x A K rk gk (n + 1) is ρ' (σ.set (Trace.dst i) (frcL K (libStepF K x A rk gk n ρ σ i)))
    | none => σ

/-- **The forced execution is the locked `runLibraryAux`.** -/
theorem runLibF_eq (x : InputBFV) (A : Spec.Float.Arith) (K : ℕ)
    (rk : List (IntPoly x.P.src.N × IntPoly x.P.src.N))
    (gk : ℕ → List (IntPoly x.P.src.N × IntPoly x.P.src.N)) (n : ℕ) (is : List Instr)
    (ρ : Env x.P.src) (σ : Trace.CtEnv x.P) :
    runLibF x A K rk gk n is ρ σ = runLibraryAux x A rk gk n is ρ σ := by
  induction is generalizing n ρ σ with
  | nil => rfl
  | cons i is ih =>
    rw [show runLibraryAux x A rk gk n (i :: is) ρ σ =
        (match step x.P.src ρ i with
         | some ρ' => runLibraryAux x A rk gk (n + 1) is ρ' (σ.set (Trace.dst i) (libStep x A rk gk n ρ σ i))
         | none => σ) from rfl]
    simp only [runLibF, frcL_eq, libStepF_eq]
    cases step x.P.src ρ i with
    | none => rfl
    | some ρ' => exact ih _ _ _

/-- **`runLibrary` by the forced execution.** -/
theorem runLibrary_forced (x : InputBFV) (A : Spec.Float.Arith) (K : ℕ)
    (rk : List (IntPoly x.P.src.N × IntPoly x.P.src.N))
    (gk : ℕ → List (IntPoly x.P.src.N × IntPoly x.P.src.N)) (cts : Var → List (IntPoly x.P.src.N)) :
    runLibF x A K rk gk 0 x.prog.body (initEnv x.P.src x.prog fun _ => .exact 0) (Trace.initCt x.P x.prog cts)
      = runLibrary x A rk gk cts := runLibF_eq x A K rk gk 0 _ _ _

/-! ## The execution with its ciphertext environment as data (proved equal)

`runLibF` returns the environment as a function (`Trace.CtEnv`); compiled, reading it can execute
the whole program again for every variable read. `runLibL` is the same execution with the
assignments kept in a list (latest first): `runLibL_eq`. -/

/-- The environment of a list of assignments (latest first) in front of `base`. -/
def envOf {P : FullParams} (base : Trace.CtEnv P) :
    List (Var × List (IntPoly P.src.N)) → Trace.CtEnv P
  | [] => base
  | (d, c) :: tab => (envOf base tab).set d c

/-- `runLibF` with the assignments as a list. -/
def runLibL (x : InputBFV) (A : Spec.Float.Arith) (K : ℕ)
    (rk : List (IntPoly x.P.src.N × IntPoly x.P.src.N))
    (gk : ℕ → List (IntPoly x.P.src.N × IntPoly x.P.src.N)) (base : Trace.CtEnv x.P) :
    ℕ → List Instr → Env x.P.src → List (Var × List (IntPoly x.P.src.N)) →
      List (Var × List (IntPoly x.P.src.N))
  | _, [], _, tab => tab
  | n, i :: is, ρ, tab =>
    match step x.P.src ρ i with
    | some ρ' => runLibL x A K rk gk base (n + 1) is ρ'
        ((Trace.dst i, frcL K (libStepF K x A rk gk n ρ (envOf base tab) i)) :: tab)
    | none => tab

theorem runLibL_eq (x : InputBFV) (A : Spec.Float.Arith) (K : ℕ)
    (rk : List (IntPoly x.P.src.N × IntPoly x.P.src.N))
    (gk : ℕ → List (IntPoly x.P.src.N × IntPoly x.P.src.N)) (base : Trace.CtEnv x.P) (n : ℕ)
    (is : List Instr) (ρ : Env x.P.src) (tab : List (Var × List (IntPoly x.P.src.N))) :
    envOf base (runLibL x A K rk gk base n is ρ tab) = runLibF x A K rk gk n is ρ (envOf base tab) := by
  induction is generalizing n ρ tab with
  | nil => rfl
  | cons i is ih =>
    cases h : step x.P.src ρ i with
    | none => simp only [runLibL, runLibF, h]
    | some ρ' =>
      simp only [runLibL, runLibF, h]
      exact ih _ _ _

/-- **`runLibrary` by the execution with the environment as data.** -/
theorem runLibrary_list (x : InputBFV) (A : Spec.Float.Arith) (K : ℕ)
    (rk : List (IntPoly x.P.src.N × IntPoly x.P.src.N))
    (gk : ℕ → List (IntPoly x.P.src.N × IntPoly x.P.src.N)) (cts : Var → List (IntPoly x.P.src.N)) :
    envOf (Trace.initCt x.P x.prog cts)
        (runLibL x A K rk gk (Trace.initCt x.P x.prog cts) 0 x.prog.body
          (initEnv x.P.src x.prog fun _ => .exact 0) [])
      = runLibrary x A rk gk cts := by
  rw [runLibL_eq]
  exact runLibrary_forced x A K rk gk cts

/-- The key set of `pin.json` `evalKeys` with `kind` (and `index` for a rotation), CRT-lifted over
all its limbs. -/
def libKeys (c : Case) (N : ℕ) (kind : String) (idx : Option Nat) : List (IntPoly N × IntPoly N) :=
  match (jArr c.pin "evalKeys").find? fun k =>
      jStr? k "kind" == some kind && (idx.isNone || jNat? k "index" == idx) with
  | none => []
  | some key =>
    (jArr key "digits").toList.filterMap fun dj => do
      let bn ← jStr? dj "b"
      let an ← jStr? dj "a"
      let eb ← c.polys[bn]?
      let ea ← c.polys[an]?
      let zb ← (crt bn N eb.moduli eb.limbs).toOption
      let za ← (crt an N ea.moduli ea.limbs).toOption
      pure ((ofArr zb : IntPoly N), (ofArr za : IntPoly N))

end FHE.Pin.BFV
