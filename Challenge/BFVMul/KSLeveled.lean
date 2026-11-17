import Challenge.BFVMul.Float
import Challenge.BudgetRestrict
import Challenge.BFV

/-!
# Challenge.BFVMul.KSLeveled — key switching with an internal drop (OpenFHE `HPSPOVERQLEVELED`)   (LOCKED)

Under `HPSPOVERQLEVELED`, on a ciphertext with the full number of limbs (`sizeQ == sizeQM`),
OpenFHE v1.6.1 (upstream b59e1f29) does not key-switch at the ciphertext's modulus `Q`.
`LeveledSHEBFVRNS::RelinearizeCore` (`src/pke/lib/scheme/bfvrns/bfvrns-leveledshe.cpp:856-900`;
it serves relinearisation, `cv.size() == 3`, switched component `cv[2]`, and the key switch of a
rotation, `cv.size() == 2`, switched component `cv[1]`: `:860-862`):

1. computes a number of limbs to drop, `FindLevelsToDrop` (`:98-198`, called at `:874`), and
   `l = sizeQ − 1 − drop`, the index of the last limb kept (`k − drop` limbs remain: `Q_l`);
2. scales the switched component from `Q` to `Q_l` by rounding: `ScaleAndRound` (`:876-878`;
   `DCRTPolyImpl::ScaleAndRound`, `src/core/include/lattice/hal/default/dcrtpoly-impl.h:1536`,
   with the tables `QlQHatInvModqDivqModq`, `QlQHatInvModqDivqFrac`,
   `bfvrns-cryptoparameters.cpp:597-621`): the same call, with the same tables, as the scaling of
   operand 1 in the leveled multiplication (`:278`; `Fl.leveledMul`). The call is made also when
   `drop = 0` (it is then the identity: `Q_l = Q`, no input limb);
3. key-switches the scaled component at `Q_l`: `KeySwitchCore` (`:882`; the keys are the
   top-level keys, of which the library uses the limbs and digits of `Q_l`);
4. multiplies both components of the result by `D = Q/Q_l` back into `Q`:
   `ExpandCRTBasisQlHat` (`:884-889`; `dcrtpoly-impl.h:1196-1216`: limb `i < l` is multiplied by
   `[Q/Q_l]_{qᵢ}`, the other limbs are zero);
5. adds: `cv[0] += ab[0]`; `cv[1] += ab[1]` for a relinearisation, `cv[1] = ab[1]` for a key
   switch (`:891-899`).

`Fl.leveledKS S qs drop core ct` is this, with the truncated sum of step 2 taken from `S`
(`Fl.scaleRoundOut S`, as in `Challenge.BFVMul.Float`) and step 3 a parameter `core`: any
function of the scaled component returning two polynomials. What is asked of `core` is the phase
contract of a key switch at `Q_l` (`KSCoreOK`): `core(d)₀ + core(d)₁·s = d·tgt + e (mod Q_l)`,
`‖e‖∞ ≤ ksl`. `ksCore_realizable`: plain hybrid key switching with the digits of the layout at
that level, from the TOP-level keys cut down (`Challenge.Budget.gadgetKeys_restrict`), is such a
function with `ksl = Spec.BudgetBFV.ksBoundAt P lay (L − drop)`.

**The bound.** With `c' = ⌊c/D⌉` up to the tolerance of the binary64 sum (`r1/2⁵³`,
`r1 = doubleSr (dropped limbs)`), `D·c' = c + D·ε` with `‖ε‖∞ ≤ 1/2 + r1/2⁵³`, so the phase moves
by `D·(ε·tgt + e)`: at most `Spec.BudgetBFV.ksLeveled N D ksl btgt r1`, `btgt` a bound on
`‖tgt‖∞` (`N·B_s²` for `tgt = s²`, `B_s` for `tgt = σ_g(s)`, `g` odd). For `drop = 0` the scaling
is the identity and the error is that of `core`: `ksl`.

**What is not covered.** `FindLevelsToDrop` (binary64 `log2`, `sqrt`, `pow`) is not modelled:
`drop` is a parameter (the frontend reads the value the library computed). Machine words and the
NTT are exact modular arithmetic here. `EvalFastRotationPrecompute`/`EvalFastRotation`
(`:759-850`) perform the same steps around a hoisted key switch and are not stated separately.
A rotation (`EvalAutomorphism`, `:744-757`) key-switches first and applies the automorphism to
the result; a source program states it as `automorph` followed by `keySwitch`, and
`stepOK_keySwitch_leveled_tol` is about that `keySwitch` (operand under `σ_g(s)`), as
`Challenge.BFV.keySwitch_realizable` is for the key switch without a drop.
-/

namespace Challenge.BFVMul
open Spec NPoly Scheme Source Correct

variable {N : ℕ}

namespace Fl

/-- Step 2: `ScaleAndRound` of one component from the basis `qs` to its first `l` limbs
(`bfvrns-leveledshe.cpp:876-878`), as an integer polynomial with coefficients in `[0, Q_l)`:
`⌊c/D⌉ mod Q_l`, `D` the product of the dropped limbs, with the truncated sum of `S`. -/
def scaleDown (S : Sums) (qs : List ℕ) (l : ℕ) (c : IntPoly N) : IntPoly N :=
  let xl := HPS.toLimbs qs c
  HPS.reconstruct (qs.take l) (scaleRoundOut S 1 (qs.drop l) (qs.take l) (xl.drop l) (xl.take l))

/-- Step 4: `ExpandCRTBasisQlHat` of a polynomial given modulo the first `l` limbs of `qs`
(`bfvrns-leveledshe.cpp:884-889`), as an integer polynomial with coefficients in `[0, Q)`:
`(Q/Q_l)·y mod Q`. -/
def scaleUp (qs : List ℕ) (l : ℕ) (y : IntPoly N) : IntPoly N :=
  HPS.reconstruct qs (POverQ.expandQlHat qs (qs.take l) (HPS.toLimbs (qs.take l) y))

/-- **`RelinearizeCore` under `HPSPOVERQLEVELED` on a full-size ciphertext** (module docstring)
with `drop` limbs dropped internally and the key switch `core` at the reduced modulus: three
components (relinearisation; the switched component is the third) or two (key switch; the
second). Anything else is not a case of the library's function (`[]`). -/
def leveledKS (S : Sums) (qs : List ℕ) (drop : ℕ) (core : IntPoly N → IntPoly N × IntPoly N)
    (ct : List (IntPoly N)) : List (IntPoly N) :=
  let l := qs.length - drop
  match ct with
  | [c0, c1, c2] =>
    let ab := core (scaleDown S qs l c2)
    [c0 + scaleUp qs l ab.1, c1 + scaleUp qs l ab.2]
  | [c0, c1] =>
    let ab := core (scaleDown S qs l c1)
    [c0 + scaleUp qs l ab.1, scaleUp qs l ab.2]
  | _ => []

end Fl

/-- **The phase contract of a key switch of one component** at modulus `Q`, for the secret `s`,
the key target `tgt` (`s²` or `σ_g(s)`) and the error bound `B`: for every component `d` (any
integer representative) the two polynomials `core d` satisfy
`core(d)₀ + core(d)₁·s = d·tgt + e (mod Q)` with `‖e‖∞ ≤ B`. -/
def KSCoreOK (Q B : ℕ) (s tgt : IntPoly N) (core : IntPoly N → IntPoly N × IntPoly N) : Prop :=
  ∀ d : IntPoly N, ∃ e : IntPoly N, normInf e ≤ B ∧
    ofInt Q (core d).1 + ofInt Q (core d).2 * ofInt Q s = ofInt Q d * ofInt Q tgt + ofInt Q e

variable (P : FullParams)

/-- **A key switch at every level from the top-level keys.** For BFV parameters and a layout
that restricts from the top level to level `ℓ`, there is a function of one component and the
keys alone (plain hybrid key switching on the digits of level `ℓ`) which, for every secret within
the bound, every key target and every list of gadget keys valid at the TOP level, cut down to the
digits of level `ℓ`, meets `KSCoreOK` at `Q_ℓ` with error at most `BudgetBFV.ksBoundAt P lay ℓ`. -/
theorem ksCore_realizable (lay : Budget.KSLayout) (hP : SchemeParamsOK P)
    (hk : P.src.kind = .bfv) (hS : Budget.SpecialOK P) (ℓ : ℕ) (hℓ : ℓ ≤ P.src.qs.length)
    (hlay : Budget.restrictsTo lay P.src.qs.length ℓ = true) :
    ∃ core : IntPoly P.src.N → List (IntPoly P.src.N × IntPoly P.src.N) →
        IntPoly P.src.N × IntPoly P.src.N,
      ∀ (s : IntPoly P.src.N), SecretOK P.secretBound s →
      ∀ (tgt : KeyTarget) (keys : List (IntPoly P.src.N × IntPoly P.src.N)),
        Budget.GadgetKeysOK P lay P.src.qs.length tgt s keys →
        KSCoreOK (P.src.modulus ℓ) (BudgetBFV.ksBoundAt P lay ℓ) s (tgt.eval s)
          (fun c => core c (keys.take (lay.sizes ℓ).length)) := sorry

/-- **Relinearisation with an internal drop meets the `relin` contract** within
`Spec.BudgetBFV.ksLeveled N D ksl (N·B_s²) (doubleSr (dropped limbs))` (`D = Q/Q_l`; within `ksl`
itself when `drop = 0`), for every truncated sum within the tolerances (`Fl.SumsOK S`) and every
key switch `core` meeting `KSCoreOK` at the reduced modulus for the target `s²` with error at
most `ksl`. -/
theorem stepOK_relin_leveled_tol (S : Fl.Sums) (hS : Fl.SumsOK S)
    (hP : SchemeParamsOK P) (E : TraceBFV.Budget)
    (s : IntPoly P.src.N) (hs : SecretOK P.secretBound s) (ρ ρ' : Env P.src)
    (σ : Trace.CtEnv P) (d a : Var) (x : Val P.src) (ca : List (IntPoly P.src.N))
    (drop ksl : ℕ) (core : IntPoly P.src.N → IntPoly P.src.N × IntPoly P.src.N)
    (hcore : KSCoreOK (P.src.modulus (x.level - drop)) ksl s (s * s) core)
    (hE : (if drop = 0 then ksl else
            BudgetBFV.ksLeveled P.src.N (P.src.modulus x.level / P.src.modulus (x.level - drop))
              ksl (P.src.N * P.secretBound * P.secretBound)
              (BudgetBFV.doubleSr ((P.src.qs.take x.level).drop (x.level - drop)))) ≤
          E.keySwitch)
    (hstep : step P.src ρ (.relin d a) = some ρ') (hx : ρ a = some x) (ha : σ a = some ca)
    (hla : ca.length = 3) (hℓL : x.level ≤ P.src.qs.length) (hdrop : drop < x.level)
    (haux : floatAuxOK? (P.src.qs.take x.level) [] = true) :
    TraceBFV.StepOK P E s ρ ρ' σ
      (σ.set d (Fl.leveledKS S (P.src.qs.take x.level) drop core ca)) (.relin d a) := sorry

/-- **A key switch with an internal drop meets the `keySwitch` contract** within
`Spec.BudgetBFV.ksLeveled N D ksl B_s (doubleSr (dropped limbs))` (within `ksl` when `drop = 0`).
The operand is under `σ_g(s)`, `g = x.key` odd (`run_key_odd`); `core` meets `KSCoreOK` for the
target `σ_g(s)`. -/
theorem stepOK_keySwitch_leveled_tol (S : Fl.Sums) (hS : Fl.SumsOK S)
    (hP : SchemeParamsOK P) (E : TraceBFV.Budget)
    (s : IntPoly P.src.N) (hs : SecretOK P.secretBound s) (ρ ρ' : Env P.src)
    (σ : Trace.CtEnv P) (d a : Var) (x : Val P.src) (ca : List (IntPoly P.src.N))
    (drop ksl : ℕ) (core : IntPoly P.src.N → IntPoly P.src.N × IntPoly P.src.N)
    (hcore : KSCoreOK (P.src.modulus (x.level - drop)) ksl s (automorph x.key s) core)
    (hE : (if drop = 0 then ksl else
            BudgetBFV.ksLeveled P.src.N (P.src.modulus x.level / P.src.modulus (x.level - drop))
              ksl P.secretBound
              (BudgetBFV.doubleSr ((P.src.qs.take x.level).drop (x.level - drop)))) ≤
          E.keySwitch)
    (hstep : step P.src ρ (.keySwitch d a) = some ρ') (hx : ρ a = some x) (ha : σ a = some ca)
    (hla : ca.length = 2) (hodd : x.key % 2 = 1)
    (hℓL : x.level ≤ P.src.qs.length) (hdrop : drop < x.level)
    (haux : floatAuxOK? (P.src.qs.take x.level) [] = true) :
    TraceBFV.StepOK P E s ρ ρ' σ
      (σ.set d (Fl.leveledKS S (P.src.qs.take x.level) drop core ca)) (.keySwitch d a) := sorry

/-- **With no internal drop, the key switch does not depend on the floating-point arithmetic.**
At `drop = 0` the library still calls `ScaleAndRound` (`bfvrns-leveledshe.cpp:876-878`, with no
condition on the drop), but from `Q` to `Q` itself: there is no input limb, its floating-point
loop is empty and `nu = 0.5` exactly (`dcrtpoly-impl.h:1566-1571`), so nothing is rounded.
Here: `Fl.leveledKS` at drop `0` gives the same result for every two arithmetics (the truncated
sum over no limb is `⌊1/2⌋` whatever the arithmetic). With `Challenge.BFVMul.exact_conforms`
this makes the realizability of a drop-0 key switch independent of `Spec.Float.Conforms`. -/
theorem leveledKS_drop_zero (A B : Spec.Float.Arith) (qs : List ℕ)
    (core : IntPoly N → IntPoly N × IntPoly N) (ct : List (IntPoly N)) :
    Fl.leveledKS (Fl.floatSums A) qs 0 core ct = Fl.leveledKS (Fl.floatSums B) qs 0 core ct :=
  sorry

/-- **Every value of a run is under an odd key.** If every input declaration is well formed
(`Decl.ok`: in particular an odd key) and `Source.step` over a list of instructions from the
initial environment gives `ρ`, every value of `ρ` has an odd key (`automorph` takes odd `g`
only, and `(key·g) mod 2N` is odd; `keySwitch` returns to key `1`). So the hypothesis `hodd` of
`stepOK_keySwitch_leveled_tol` holds at every `keySwitch` a run reaches. -/
theorem run_key_odd (Pr : Params) (prog : Program) (msgs : Var → Msg Pr.t Pr.N)
    (hin : (prog.inputs.all fun d => d.ok Pr) = true) (pre : List Instr) (ρ : Env Pr)
    (hρ : pre.foldlM (step Pr) (initEnv Pr prog msgs) = some ρ)
    (a : Var) (xa : Val Pr) (hx : ρ a = some xa) : xa.key % 2 = 1 := sorry

/-! ## Checks at tiny parameters

`N = 2`, `qs = [7, 11, 13]` (`Q = 1001`), the exact sums (`Fl.exactSums`), the secret `s = 1 − X`
(`s² = −2X`, `σ₃(s) = 1 + X`) and the noiseless key switch `core d = (d·tgt, 0)`, which meets
`KSCoreOK` with `B = 0` at every modulus. The phase error is the largest centred distance modulo
`Q` between `r₀ + r₁·s` and the phase of the operand. With a limb dropped it is not zero (so a
budget of `ksl = 0` alone would not cover a drop) and it is within
`Spec.BudgetBFV.ksLeveled N D 0 btgt 0`; with `drop = 0` it is zero. A switched component that is
a multiple of `D` is scaled exactly. -/

-- Relinearisation: `btgt = N·B_s² = 2`; `D = 13` (bound 26) and `D = 143` (bound 286).
#guard
  let s : IntPoly 2 := ⟨![1, -1]⟩
  let err := fun (drop : ℕ) (c0 c1 c2 : IntPoly 2) =>
    match Fl.leveledKS Fl.exactSums [7, 11, 13] drop (fun d => (d * (s * s), 0)) [c0, c1, c2] with
    | [r0, r1] => POverQ.maxDist 1001 [r0 + r1 * s] [c0 + c1 * s + c2 * (s * s)]
    | _ => -1
  BudgetBFV.ksLeveled 2 13 0 2 0 == 26 && BudgetBFV.ksLeveled 2 143 0 2 0 == 286 &&
  err 1 ⟨![3, 990]⟩ ⟨![500, 501]⟩ ⟨![6, 7]⟩ == 12 &&
  err 1 ⟨![0, 0]⟩ ⟨![1, 2]⟩ ⟨![1000, 137]⟩ == 12 &&
  err 1 ⟨![17, 400]⟩ ⟨![999, 2]⟩ ⟨![13, 26]⟩ == 0 &&
  err 2 ⟨![3, 990]⟩ ⟨![500, 501]⟩ ⟨![6, 7]⟩ == 14 &&
  err 2 ⟨![17, 400]⟩ ⟨![999, 2]⟩ ⟨![500, 501]⟩ == 142 &&
  err 0 ⟨![3, 990]⟩ ⟨![500, 501]⟩ ⟨![6, 7]⟩ == 0 &&
  err 0 ⟨![0, 0]⟩ ⟨![1, 2]⟩ ⟨![1000, 137]⟩ == 0 &&
  err 0 ⟨![17, 400]⟩ ⟨![999, 2]⟩ ⟨![500, 501]⟩ == 0

-- Key switch under `σ₃(s)`: `btgt = B_s = 1`, `D = 13` (bound 13).
#guard
  let s : IntPoly 2 := ⟨![1, -1]⟩
  let err := fun (drop : ℕ) (c0 c1 : IntPoly 2) =>
    match Fl.leveledKS Fl.exactSums [7, 11, 13] drop (fun d => (d * automorph 3 s, 0)) [c0, c1] with
    | [r0, r1] => POverQ.maxDist 1001 [r0 + r1 * s] [c0 + c1 * automorph 3 s]
    | _ => -1
  BudgetBFV.ksLeveled 2 13 0 1 0 == 13 &&
  err 1 ⟨![500, 501]⟩ ⟨![6, 7]⟩ == 12 &&
  err 1 ⟨![1, 2]⟩ ⟨![1000, 137]⟩ == 7 &&
  err 0 ⟨![500, 501]⟩ ⟨![6, 7]⟩ == 0 &&
  err 0 ⟨![1, 2]⟩ ⟨![1000, 137]⟩ == 0

-- Neither two nor three components: not a case of the library's function.
#guard (Fl.leveledKS (N := 2) Fl.exactSums [7, 11, 13] 1 (fun d => (d, 0)) [0]).isEmpty

end Challenge.BFVMul
