import Respec.Noise
import Respec.Equiv.Decrypt
import FHE.RNS.Poly
import Validation.Switch
import Challenge.Headline.Defs
import Spec.Budget

/-!
# Respec.Equiv.ModSwitch — item 7: modulus switching

In this module `A` is the specification (`Spec`, `Challenge`) and `B` the independent
re-specification (`Respec`); "A's `x`" and "B's `x`" are the corresponding definitions of each.

## Verdicts

* **RNS algorithm: EQUAL, limb for limb (PROVED).**
  `modSwitchBGVRns_centred_eq` : B's `modSwitchBGVRns .centred t q` (OpenFHE `ModReduce`,
  dcrtpoly-impl.h:758-777) is A's `FHE.RNS.Basis.bgvModSwitchPoly t` on the same limbs.
  `modSwitchBGVRns_canonical_eq` : B's `.canonical` variant is A's `bgvModSwitchCanon`
  (the canonical-lift reading). Both for every basis, every `t`, every input.
* **Integer formula: EQUAL (PROVED).** `modSwitchElt_eq` : A's textbook
  `Challenge.Source.bgvModSwitchComp t q` applied to *any* integer representative and reduced
  modulo `Q'` is B's `modSwitchElt (.ghs .centred) t q Q'` of the reduction modulo `Q = Q'·q`.
  The same integer map is A's `Spec.Decrypt.switchPhase` and `Validation.Switch.sw`.
* **Message scaling: EQUAL UP TO CONVENTION (PROVED).** A's `Source.step` multiplies the message
  by `q_last⁻¹` (`step_modSwitch_msg`); B's `State.modSwitch` keeps the message and multiplies the
  scaling factor `sf` by `q_ℓ⁻¹`. Under the translation `msg_A = sf_B • msg_B`
  (`state_modSwitch_translate`) they agree. Both match OpenFHE
  `LeveledSHEBGVRNS::ModReduceInternalInPlace` (bgvrns-leveledshe.cpp, `scalingFactorInt`
  multiplied by `(q_ℓ mod t)⁻¹`).
* **Budget, any number of components: EQUAL UP TO ROUNDING (PROVED).** A's budget is
  parts-dependent (`Spec.Budget.msBudgetAt P k = ⌈t·Σ_{i<k} (N·B_s)ⁱ / 2⌉`, charged through
  `Trace.Budget.modSwitchAt`), as B's `modSwitchBound … D` is (`D + 1` components).
  `msBudgetAt_vs_B` : for an operand with `D + 1` components A's per-switch charge
  `⌊B/q⌋ + msBudgetAt P (D + 1)` is at least `⌊B's modSwitchBound (.ghs .centred) N t B_s q D B⌋`
  and exceeds it by at most 1 (`msCharge_vs_B`: the same without `FullParams`; `msBudget_vs_B`:
  the case of two components, `msBudget`).
* **Three components, the witness (PROVED, kernel-checked).** `threePart_needs_parts` : the
  textbook switch of `(1, 1, 1)` at `N = 1`, `s = 1`, `t = 2`, `q_last = 7` adds the correction
  `δ₀ + δ₁·s + δ₂·s² = 18` and has output centred phase `3`. The *two-component* budget
  `Spec.Budget.msBudget` would predict `⌊3/7⌋ + 2 = 2 < 3` (`18 > 7·msBudget = 14`): `msBudget`
  does not cover a three-component switch. A's three-component budget `msBudgetAt wit3P 3 = 3`
  predicts `⌊3/7⌋ + 3 = 3`, which covers it, and B's `modSwitchBound … (D := 2)` gives
  `24/7 ≥ 3`. `threePart_refAnalyze` : A's reference analyzer with the certified budget returns
  `some 3` on this program. (Historical: an earlier version of the analyzer charged `msBudget` for
  every number of components and returned `some 2` here; this witness showed it, and the
  parts-dependent budget fixes it, `Challenge.Budget.modSwitch_realizable_parts`.
  The witness is kept as the reason the budget depends on the number of components.)

* **Other corrections: the certified budget is met only by the centred one (PROVED witness).**
  `twoPart_nonCentred_exceeds` : with 2 components, `N = 1`, `s = 1`, `t = 2`, `q_last = 7`:
  A's *own* canonical switch `FHE.RNS.Basis.bgvModSwitchCanon` (the canonical-lift correction) and SEAL's correction (B's `MSVariant.seal`, `|δ| < t·q`) both produce output noise 4
  where A's analysis with `msBudget` predicts 2 (`δ(s) = 24 > q·msBudget = 14`). `msBudget`
  is specific to the centred correction `t·[−c·t⁻¹]_q` with `valMinAbs` (OpenFHE `ModReduce`);
  a backend using the canonical correction needs about twice the budget
  (`t·(q−1)·(1 + N·B_s)/q`). A's `Spec/Budget.lean` now says so itself ("for the centred
  correction only", citing this theorem) and defines no budget for the other convention; that
  statement of A's docstring is what this witness supports. B's `.bgv12` (`Scale`,
  `c' ≡ c mod t`) agrees with A's message bookkeeping only when `q_last ≡ 1 (mod t)` (B's own
  `#guard`s in `BGVTest.lean`), i.e. A correctly does not model it.
* **One component:** A's `⌊B/q⌋ + ⌈t/2⌉` (`msBudgetOne = msBudgetAt P 1`) vs B's `B/q + t/2`
  (`D = 0`): equal up to rounding, the case `D = 0` of `msBudgetAt_vs_B`.
-/

namespace Respec.Equiv

open Spec Spec.NPoly Spec.Scheme Spec.Source Respec Respec.BGV Respec.Noise Validation.Ring
  Validation.Scheme

variable {N : ℕ}

/-- A's RNS polynomial over `C` as B's. -/
def toBR {ℓ : ℕ} (C : FHE.RNS.Basis ℓ) (a : FHE.RNS.RNSPoly C N) : RnsPoly C.q N := ⟨a⟩

/-- **RNS modulus switch, centred: B's = A's, limb for limb.** -/
theorem modSwitchBGVRns_centred_eq {k : ℕ} (t : ℕ) (C : FHE.RNS.Basis (k + 1))
    (a : FHE.RNS.RNSPoly C N) (i : Fin k) :
    (modSwitchBGVRns .centred t C.q (toBR C a)).limb i = C.bgvModSwitchPoly t a i := by
  ext n
  simp only [modSwitchBGVRns, modSwitchBGVCore, rmk_eq, psmul_eq, padd_eq, switchMod, force_eq,
    toBR, FHE.RNS.Basis.bgvModSwitchPoly, FHE.RNS.Basis.mapCoeff, FHE.RNS.Basis.bgvModSwitch,
    FHE.RNS.Basis.rescaleWith, FHE.RNS.Basis.modDownWith, FHE.RNS.Basis.coeffVec, Lift.rep,
    coeff_smul', coeff_add']
  push_cast
  rw [mul_comm ((-((t : ℕ) : ZMod (C.q (Fin.last k)))⁻¹)), neg_mul_comm, mul_comm]
  rfl

/-- **RNS modulus switch, canonical: B's = A's `bgvModSwitchCanon`.** -/
theorem modSwitchBGVRns_canonical_eq {k : ℕ} (t : ℕ) (C : FHE.RNS.Basis (k + 1))
    (a : FHE.RNS.RNSPoly C N) (i : Fin k) :
    (modSwitchBGVRns .canonical t C.q (toBR C a)).limb i =
      C.mapCoeff (p := C.dropLast.q) (C.bgvModSwitchCanon t) a i := by
  ext n
  simp only [modSwitchBGVRns, modSwitchBGVCore, rmk_eq, psmul_eq, padd_eq, switchMod, force_eq,
    toBR, FHE.RNS.Basis.mapCoeff, FHE.RNS.Basis.bgvModSwitchCanon,
    FHE.RNS.Basis.rescaleWith, FHE.RNS.Basis.modDownWith, FHE.RNS.Basis.coeffVec, Lift.rep,
    coeff_smul', coeff_add']
  push_cast
  rw [mul_comm ((-((t : ℕ) : ZMod (C.q (Fin.last k)))⁻¹)), neg_mul_comm, mul_comm]
  rfl

/-- A's textbook switch of one component, unfolded (by `rfl`: no equation lemma of the
`Challenge` definition is generated here). -/
theorem bgvModSwitchComp_unfold (t q : ℕ) (c : IntPoly N) :
    Challenge.Source.bgvModSwitchComp t q c =
      ⟨fun i => (c.coeff i +
        (t : ℤ) * ((((-(c.coeff i) : ℤ) : ZMod q) * (t : ZMod q)⁻¹).valMinAbs)) / q⟩ := rfl

/-- **Integer formula: A's textbook switch = B's `modSwitchElt (.ghs .centred)`.** For any
integer representative `c` of a component modulo `Q = Q'·q`. -/
theorem modSwitchElt_eq (t q Q' : ℕ) (hq : 0 < q) (hQ' : 0 < Q') (hcop : Nat.Coprime t q) (c : IntPoly N) :
    ofInt Q' (Challenge.Source.bgvModSwitchComp t q c) =
      modSwitchElt (.ghs .centred) t q Q' (ofInt (Q' * q) c) := by
  ext n
  simp only [modSwitchElt, force_eq, msDeltaZ, Lift.rep, ofInt_unfold,
    bgvModSwitchComp_unfold]
  -- both sides are `Validation.Switch.sw t q` of representatives congruent modulo `q·Q'`
  have h := Validation.Switch.sw_congr hq hcop Q'
    (x := c.coeff n) (y := (((c.coeff n : ZMod (Q' * q))).val : ℤ)) (by
      haveI : NeZero (Q' * q) := ⟨(Nat.mul_pos hQ' hq).ne'⟩
      rw [mul_comm q Q', Int.cast_natCast, ZMod.natCast_zmod_val])
  have e1 : ∀ x : ℤ, Validation.Switch.sw t q x =
      (x + (t : ℤ) * (((-x : ℤ) : ZMod q) * (t : ZMod q)⁻¹).valMinAbs) / q := fun _ => rfl
  rw [e1, e1] at h
  rw [h]
  congr 3
  push_cast
  ring

/-! ### Message bookkeeping -/

/-- A's `Source.step` on `modSwitch` (BGV) multiplies the message by `q_last⁻¹`. -/
theorem step_modSwitch_msg (P : Source.Params) (hk : P.kind = .bgv) (ρ : Env P) (d a : Var)
    (x : Val P) (m : Poly P.t P.N) (hx : ρ a = some x) (hm : x.msg = .exact m)
    (h2 : 2 ≤ x.level) (q : ℕ) (hq : P.qs[x.level - 1]? = some q) :
    ∃ ρ', step P ρ (.modSwitch d a) = some ρ' ∧
      ρ' d = some { x with msg := .exact (((q : ZMod P.t)⁻¹) • m), level := x.level - 1 } := by
  refine ⟨ρ.set d { x with msg := .exact (((q : ZMod P.t)⁻¹) • m), level := x.level - 1 }, ?_,
    by simp [Env.set]⟩
  simp [step, hx, h2, hq, hk, hm, Msg.lift₁]

/-- **Translation**: B's `State.modSwitch` (scaling factor `sf ↦ sf·q⁻¹`, message kept) carries
`sf • msg` to `q⁻¹ • (sf • msg)`, which is A's message update. -/
theorem state_modSwitch_translate {t : ℕ} (ql : ℕ) (st : State t N) :
    (st.modSwitch ql).sf • (st.modSwitch ql).msg = ((ql : ZMod t)⁻¹) • (st.sf • st.msg) := by
  ext i
  simp only [State.modSwitch, coeff_smul']
  ring

/-! ### Budgets -/

/-- B's `lsum` of a list of naturals is `List.sum`. -/
theorem lsum_nat_eq_sum (l : List ℕ) : lsum l = l.sum := by
  unfold lsum; rw [List.sum_eq_foldl]

/-- **Any number of components: `⌊B/q⌋ + ⌈t·S/2⌉` is B's bound rounded up (by at most one)**,
`S = Σ_{i ≤ D} (N·Bs)ⁱ`, for the centred GHS/OpenFHE correction and any `q > 0`. -/
theorem msCharge_vs_B (N t Bs q D B : ℕ) (hq : 0 < q) :
    ⌊modSwitchBound (.ghs .centred) N t Bs q D B⌋ ≤
        ((B / q + (t * ((List.range (D + 1)).map fun i => (N * Bs) ^ i).sum + 1) / 2 : ℕ) : ℤ) ∧
      ((B / q + (t * ((List.range (D + 1)).map fun i => (N * Bs) ^ i).sum + 1) / 2 : ℕ) : ℤ) ≤
        ⌊modSwitchBound (.ghs .centred) N t Bs q D B⌋ + 1 := by
  set S : ℕ := ((List.range (D + 1)).map fun i => (N * Bs) ^ i).sum with hS
  have hb : modSwitchBound (.ghs .centred) N t Bs q D B =
      (B : ℚ) / q + (t * S : ℕ) / 2 := by
    unfold modSwitchBound
    rw [lsum_nat_eq_sum, ← hS]
    simp only [msDeltaBound2, Lift.bound2]
    have hq' : (q : ℚ) ≠ 0 := by exact_mod_cast hq.ne'
    field_simp
    push_cast
    ring
  rw [hb]
  set X := t * S
  have hBq : ((B / q : ℕ) : ℚ) ≤ (B : ℚ) / q ∧ (B : ℚ) / q < (B / q : ℕ) + 1 := by
    have hq' : (0 : ℚ) < q := by exact_mod_cast hq
    constructor
    · rw [le_div_iff₀ hq']; exact_mod_cast Nat.div_mul_le_self B q
    · rw [div_lt_iff₀ hq']
      have := Nat.lt_div_mul_add (a := B) hq
      push_cast at this ⊢
      have h2 : ((B : ℕ) : ℚ) < ((B / q : ℕ) : ℚ) * q + q := by exact_mod_cast this
      linarith
  have hX : (((X + 1) / 2 : ℕ) : ℚ) * 2 ≥ X ∧ (((X + 1) / 2 : ℕ) : ℚ) * 2 ≤ X + 1 := by
    constructor
    · have : X ≤ (X + 1) / 2 * 2 := by omega
      exact_mod_cast this
    · have : (X + 1) / 2 * 2 ≤ X + 1 := Nat.div_mul_le_self _ _
      exact_mod_cast this
  constructor
  · rw [Int.floor_le_iff]
    simp only [Int.cast_add, Int.cast_natCast, Nat.cast_add]
    linarith [hBq.2, hX.1]
  · have h1 : ((((B / q + (X + 1) / 2 : ℕ) : ℤ) - 1 : ℤ) : ℚ) ≤ (B : ℚ) / q + (X : ℕ) / 2 := by
      simp only [Int.cast_sub, Int.cast_add, Int.cast_natCast, Int.cast_one, Nat.cast_add]
      linarith [hBq.1, hX.2]
    have := Int.le_floor.mpr h1
    linarith

/-- **A's parts-dependent charge is B's bound rounded up (by at most one)**: for an operand with
`D + 1` components, `⌊B's bound⌋ ≤ ⌊B/q⌋ + msBudgetAt P (D + 1) ≤ ⌊B's bound⌋ + 1`. -/
theorem msBudgetAt_vs_B (P : FullParams) (q D B : ℕ) (hq : 0 < q) :
    ⌊modSwitchBound (.ghs .centred) P.src.N P.src.t P.secretBound q D B⌋ ≤
        ((B / q + Spec.Budget.msBudgetAt P (D + 1) : ℕ) : ℤ) ∧
      ((B / q + Spec.Budget.msBudgetAt P (D + 1) : ℕ) : ℤ) ≤
        ⌊modSwitchBound (.ghs .centred) P.src.N P.src.t P.secretBound q D B⌋ + 1 :=
  msCharge_vs_B P.src.N P.src.t P.secretBound q D B hq

/-- **Two components: A's charge is B's bound rounded up (by at most one).** For the centred
GHS/OpenFHE correction (any `q > 0`): `⌊B's bound⌋ ≤ ⌊B/q⌋ + msBudget ≤ ⌊B's bound⌋ + 1`, where
`msBudget = ⌈t·(1 + N·Bs)/2⌉`. -/
theorem msBudget_vs_B (N t Bs q B : ℕ) (hq : 0 < q) :
    ⌊modSwitchBound (.ghs .centred) N t Bs q 1 B⌋ ≤ ((B / q + (t * (1 + N * Bs) + 1) / 2 : ℕ) : ℤ) ∧
      ((B / q + (t * (1 + N * Bs) + 1) / 2 : ℕ) : ℤ) ≤ ⌊modSwitchBound (.ghs .centred) N t Bs q 1 B⌋ + 1 := by
  have h := msCharge_vs_B N t Bs q 1 B hq
  have hl : ((List.range (1 + 1)).map fun i => (N * Bs) ^ i).sum = 1 + N * Bs := by
    simp [List.range_succ]
  rwa [hl] at h

/-- Parameters of the three-component witness. -/
def wit3P : FullParams where
  src := { kind := .bgv, N := 1, qs := [11, 7], t := 2 }
  store := { W := 1, limbs := [], special := [] }
  secretBound := 1
  inputNoise := 3
  keyNoise := 0
  outputNoise := 0

/-- The three-component witness: the textbook switch of `[1, 1, 1]` by `q = 7` at `t = 2`. -/
def wit3 : List (IntPoly 1) := [⟨fun _ => 1⟩, ⟨fun _ => 1⟩, ⟨fun _ => 1⟩]

/-- **Three components: the two-component budget `msBudget` is not enough; `msBudgetAt P 3`
is.** `N = 1`, `s = 1` (`Bs = 1`), `t = 2`, chain `[11, 7]` (switch from `Q = 77` to `Q' = 11`).
* the input phase is `3` (noise 3 at level 2);
* each component's correction is `δᵢ = 6 = t·⌊q/2⌋` (the maximum), so `δ(s) = 18 > q·msBudget =
  7·2 = 14`;
* the output's centred phase is `3`; charging the two-component budget would predict
  `⌊3/7⌋ + msBudget = 2`;
* A's three-component budget is `msBudgetAt wit3P 3 = 3`, and `⌊3/7⌋ + 3 = 3` covers the output;
* B's `modSwitchBound` with `D = 2` is `24/7 ≥ 3`. -/
theorem threePart_needs_parts :
    let s : IntPoly 1 := ⟨fun _ => 1⟩
    let out := wit3.map (Challenge.Source.bgvModSwitchComp 2 7)
    -- input noise 3, output noise 3
    normInf (centeredPhase s (wit3.map (ofInt 77))) = 3 ∧
    normInf (centeredPhase s (out.map (ofInt 11))) = 3 ∧
    -- what the two-component budget would predict
    3 / 7 + Spec.Budget.msBudget wit3P = 2 ∧
    -- A's three-component budget and its prediction
    Spec.Budget.msBudgetAt wit3P 3 = 3 ∧ 3 / 7 + Spec.Budget.msBudgetAt wit3P 3 = 3 ∧
    -- the textbook corrections
    (wit3.map fun c => (Challenge.Source.bgvModSwitchComp 2 7 c).coeff 0 * 7 - c.coeff 0) = [6, 6, 6] ∧
    -- B's parts-dependent bound covers it
    (3 : ℚ) ≤ modSwitchBound (.ghs .centred) 1 2 1 7 2 3 := by
  intro s out
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold normInf centeredPhase; decide +kernel
  · unfold normInf centeredPhase; decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · simp only [modSwitchBound, msDeltaBound2, Lift.bound2, lsum]
    norm_num

/-- The program of the witness: one 3-component input at level 2, switched once. -/
def wit3Prog : Program :=
  { inputs := [⟨"a", 3, 2, 1, 1⟩], body := [.modSwitch "c" "a"], outputs := ["c"] }

/-- **A's reference analyzer with A's certified budget gives the witness the bound 3**, which is
the noise of the textbook switch of the witness input (noise 3, inside `inputNoise = 3`). -/
theorem threePart_refAnalyze :
    Challenge.Headline.refAnalyze wit3P (Spec.Budget.certified wit3P (Spec.Budget.uniformLayout 1))
      wit3Prog = some 3 := by
  decide +kernel

/-! ### Other corrections: SEAL's and the canonical-lift one -/

/-- Parameters of the two-component witnesses (`inputNoise = 4`). -/
def wit2P : FullParams where
  src := { kind := .bgv, N := 1, qs := [11, 7], t := 2 }
  store := { W := 1, limbs := [], special := [] }
  secretBound := 1
  inputNoise := 4
  keyNoise := 0
  outputNoise := 0

/-- One 2-component input at level 2, switched once. -/
def wit2Prog : Program :=
  { inputs := [⟨"a", 2, 2, 1, 1⟩], body := [.modSwitch "c" "a"], outputs := ["c"] }

/-- **The certified `msBudget` is met only by the centred correction, even for 2 components.**
`N = 1`, `s = 1`, `t = 2`, chain `[11, 7]`, `msBudget = 2`, so `q·msBudget = 14`:
* A's reference analysis with the certified budget gives `2` for `wit2Prog` (input noise 4);
* **A's own canonical switch** `FHE.RNS.Basis.bgvModSwitchCanon` (the canonical-lift reading):
  on the input `[2, 2]` (phase 4) each correction is `t·6 = 12` (`2 + 12 = 7·2`), `δ(s) = 24 > 14`,
  and each output component is `2`: output phase `4 > 2`;
* **SEAL's correction** (B's `MSVariant.seal`): on the input `[−2, −2]` (phase `−4`) each
  correction is `−12`, output components `−2`, output centred phase `−4`, noise `4 > 2`. -/
theorem twoPart_nonCentred_exceeds :
    Challenge.Headline.refAnalyze wit2P (Spec.Budget.certified wit2P (Spec.Budget.uniformLayout 1))
        wit2Prog = some 2 ∧
    ((FHE.RNS.Basis.ofList [11, 7] (by decide) (by decide)).bgvModSwitchCanon 2
        (fun _ => 2) ⟨0, by decide⟩).val = 2 ∧
    msDeltaZ .seal 2 7 ((-2 : ℤ) % 77) = -12 ∧
    normInf (centeredPhase (⟨fun _ => 1⟩ : IntPoly 1)
      (modSwitch .seal 2 7 11 [(⟨fun _ => -2⟩ : Poly 77 1), ⟨fun _ => -2⟩])) = 4 := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  unfold normInf centeredPhase; decide +kernel

end Respec.Equiv
