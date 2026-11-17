import Challenge.FreshNoiseL2
import Validation.FreshNoise.Basic

/-!
# Validation.FreshNoise.L2 — the tail of a fresh encryption from `ℓ₂` norms

Proofs of the pins of `Challenge.FreshNoiseL2`, on the machinery of `Validation.FreshNoise.Tail`
(`convWt`, `wt`, `coeff_freshError_coords`, `subG_mono`, `sqNN`).

Reusable lemmas:
* `flip`, `flip_flip`, `sum_convWt_sq`: the weights of coefficient `k` of a negacyclic product
  are the coefficients of the fixed factor, permuted and signed, so their squares sum to `normSq`;
* `sum_natAbs_convWt_le`, `sum_wt_natAbs_le_l2`: the `ℓ₁` mass of those weights is at most
  `normSq`, so the total weight of a coefficient of `freshError` is at most `E2 + 1 + S2`;
* `coeff_subG_l2`: each coefficient of `freshError` is, about its mean, sub-Gaussian with
  parameter `varProxyL2` (the union bound is `Validation.FreshNoise.normInf_tail_of_centered`).
-/

namespace Validation.FreshNoise
open Spec NPoly Scheme Source Correct Spec.Encrypt Challenge.Headline MeasureTheory ProbabilityTheory
open Challenge.FreshNoise Challenge.FreshNoiseL2
open Validation.Ring Validation.Scheme
open scoped NNReal

variable {N : ℕ}

/-! ### The weights of a negacyclic product are a signed permutation -/

/-- The index of the coefficient of `s` that multiplies `aᵢ` in coefficient `k` of `a * s`. -/
def flip (k i : Fin N) : Fin N :=
  if h : i.val ≤ k.val then ⟨k.val - i.val, by have := k.isLt; omega⟩
  else ⟨N + k.val - i.val, by have := k.isLt; have := i.isLt; omega⟩

theorem flip_flip (k i : Fin N) : flip k (flip k i) = i := by
  have hk := k.isLt
  have hi := i.isLt
  apply Fin.ext
  unfold flip
  by_cases h : i.val ≤ k.val
  · simp only [h, dite_true]
    have h' : k.val - i.val ≤ k.val := by omega
    simp only [h', dite_true]
    omega
  · simp only [h, dite_false]
    have h' : ¬ N + k.val - i.val ≤ k.val := by omega
    simp only [h', dite_false]
    omega

theorem natAbs_convWt (s : IntPoly N) (k i : Fin N) :
    (convWt s k i).natAbs = (s.coeff (flip k i)).natAbs := by
  unfold convWt flip
  split_ifs <;> simp

/-- The squares of the weights of coefficient `k` of `a * s` sum to `‖s‖₂²`. -/
theorem sum_convWt_sq (s : IntPoly N) (k : Fin N) :
    ∑ i, (convWt s k i).natAbs ^ 2 = normSq s := by
  simp only [natAbs_convWt]
  exact Equiv.sum_comp (Function.Involutive.toPerm (flip k) (flip_flip k))
    (fun i => (s.coeff i).natAbs ^ 2)

theorem sqNN_intCast (w : ℤ) : sqNN (w : ℝ) = ((w.natAbs ^ 2 : ℕ) : ℝ≥0) := by
  apply NNReal.eq
  rw [coe_sqNN]
  push_cast
  rw [Nat.cast_natAbs, Int.cast_abs, sq_abs]

theorem coordProxy_inl (Vu V1 V2 : ℕ) (i : Fin N) : coordProxy N Vu V1 V2 (.inl i) = Vu := rfl
theorem coordProxy_inrl (Vu V1 V2 : ℕ) (i : Fin N) :
    coordProxy N Vu V1 V2 (.inr (.inl i)) = V1 := rfl
theorem coordProxy_inrr (Vu V1 V2 : ℕ) (i : Fin N) :
    coordProxy N Vu V1 V2 (.inr (.inr i)) = V2 := rfl

/-- The sub-Gaussian parameters of the `3N` weighted coordinates sum to
`V_u·‖e‖₂² + V_1 + V_2·‖s‖₂²`. -/
theorem sum_parL2 (s e : IntPoly N) (Vu V1 V2 : ℕ) (k : Fin N) :
    ∑ j, sqNN (wt s e k j : ℝ) * ((coordProxy N Vu V1 V2 j : ℕ) : ℝ≥0) =
      ((varProxyL2 (normSq e) (normSq s) Vu V1 V2 : ℕ) : ℝ≥0) := by
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
  simp only [wt, Sum.elim_inl, Sum.elim_inr, coordProxy_inl, coordProxy_inrl, coordProxy_inrr,
    sqNN_intCast]
  rw [← Finset.sum_mul, ← Finset.sum_mul, ← Finset.sum_mul, ← Nat.cast_sum, ← Nat.cast_sum,
    ← Nat.cast_sum, sum_convWt_sq, sum_convWt_sq]
  have h1 : ∑ i : Fin N, (if i = k then (1 : ℤ) else 0).natAbs ^ 2 = 1 := by
    have : ∀ i : Fin N, (if i = k then (1 : ℤ) else 0).natAbs ^ 2 = if i = k then 1 else 0 := by
      intro i; split_ifs <;> simp
    simp only [this, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [h1]
  unfold varProxyL2
  push_cast
  ring

/-- The `ℓ₁` mass of the weights of a negacyclic product is at most `‖s‖₂²` (`|x| ≤ x²` for an
integer `x`). -/
theorem sum_natAbs_convWt_le (s : IntPoly N) (k : Fin N) :
    ∑ i, (convWt s k i).natAbs ≤ normSq s := by
  rw [← sum_convWt_sq s k]
  exact Finset.sum_le_sum fun i _ => Nat.le_self_pow (by norm_num) _

/-- The total weight from `ℓ₂` norms: `E2 + 1 + S2`. -/
theorem sum_wt_natAbs_le_l2 (s e : IntPoly N) (E2 S2 : ℕ) (hs : normSq s ≤ S2)
    (he : normSq e ≤ E2) (k : Fin N) : ∑ j, (wt s e k j).natAbs ≤ E2 + 1 + S2 := by
  rw [sum_wt_natAbs]
  have h1 := sum_natAbs_convWt_le e k
  have h2 := sum_natAbs_convWt_le s k
  omega

section TailL2
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- **Each coefficient of the error of a fresh encryption is, about its mean, sub-Gaussian** with
parameter `varProxyL2`. -/
theorem coeff_subG_l2 (hN : 0 < N) (s e : IntPoly N) (E2 S2 Vu V1 V2 mn md : ℕ)
    (hs : normSq s ≤ S2) (he : normSq e ≤ E2) (u e₁ e₂ : Ω → IntPoly N)
    (h : SubGaussSamplerOK μ Vu V1 V2 mn md u e₁ e₂) (k : Fin N) :
    HasSubgaussianMGF
      (fun ω => ((freshError s e (u ω) (e₁ ω) (e₂ ω)).coeff k : ℝ) - drift μ s e u e₁ e₂ k)
      ((varProxyL2 E2 S2 Vu V1 V2 : ℕ) : ℝ≥0) μ := by
  have key := centered_sum_subG hN s e u e₁ e₂ k h.indep _
    (fun j => subG_const_mul (h.subG j) (wt s e k j : ℝ))
  rw [sum_parL2] at key
  have hle : ((varProxyL2 (normSq e) (normSq s) Vu V1 V2 : ℕ) : ℝ≥0) ≤
      ((varProxyL2 E2 S2 Vu V1 V2 : ℕ) : ℝ≥0) := by
    refine Nat.cast_le.2 ?_
    unfold varProxyL2
    gcongr
  exact subG_mono key hle

end TailL2

end Validation.FreshNoise

/-! ### The locked statements -/

namespace Validation.FreshNoiseL2
open Spec NPoly Scheme Source Correct Spec.Encrypt Challenge.Headline MeasureTheory ProbabilityTheory
open Challenge.FreshNoise Challenge.FreshNoiseL2
open Validation.Ring Validation.Scheme Validation.FreshNoise
open scoped NNReal

variable {N : ℕ}

theorem normSq_le (a : IntPoly N) : normSq a ≤ N * normInf a ^ 2 := by
  unfold normSq
  calc ∑ i, (a.coeff i).natAbs ^ 2 ≤ ∑ _i : Fin N, normInf a ^ 2 :=
        Finset.sum_le_sum fun i _ => Nat.pow_le_pow_left
          (Finset.le_sup (f := fun i => (a.coeff i).natAbs) (Finset.mem_univ i)) 2
    _ = _ := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]

theorem varProxyL2_support (N Bs Bk Bu B1 B2 : ℕ) :
    varProxyL2 (N * Bk ^ 2) (N * Bs ^ 2) (Bu ^ 2) (B1 ^ 2) (B2 ^ 2) = varProxy N Bs Bk Bu B1 B2 := by
  unfold varProxyL2 varProxy; ring

theorem subGaussSamplerOK_of_samplerOK {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (Bu B1 B2 mn md : ℕ) (u e₁ e₂ : Ω → IntPoly N)
    (h : SamplerOK μ Bu B1 B2 mn md u e₁ e₂) :
    SubGaussSamplerOK μ (Bu ^ 2) (B1 ^ 2) (B2 ^ 2) mn md u e₁ e₂ := by
  refine ⟨h.indep, fun j => subG_mono (coord_subG h j) (le_of_eq ?_), h.mean⟩
  rcases j with i | i | i <;>
    simp [coordBound_inl, coordBound_inrl, coordBound_inrr, coordProxy_inl, coordProxy_inrl,
      coordProxy_inrr]

theorem subGaussSamplerOK_mono {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (Vu V1 V2 Vu' V1' V2' mn md : ℕ) (hu : Vu ≤ Vu') (h1 : V1 ≤ V1') (h2 : V2 ≤ V2')
    (u e₁ e₂ : Ω → IntPoly N) (h : SubGaussSamplerOK μ Vu V1 V2 mn md u e₁ e₂) :
    SubGaussSamplerOK μ Vu' V1' V2' mn md u e₁ e₂ := by
  refine ⟨h.indep, fun j => subG_mono (h.subG j) (Nat.cast_le.2 ?_), h.mean⟩
  rcases j with i | i | i
  · exact hu
  · exact h1
  · exact h2

theorem subGaussSamplerOK_rademacher (N Bu B1 B2 mn md : ℕ) :
    SubGaussSamplerOK (N := N)
      (Measure.pi fun _ : Fin N ⊕ Fin N ⊕ Fin N =>
        ((2⁻¹ : NNReal) • (Measure.dirac true + Measure.dirac false) : Measure Bool))
      (Bu ^ 2) (B1 ^ 2) (B2 ^ 2) mn md
      (fun ω => ⟨fun i => coin Bu (ω (.inl i))⟩)
      (fun ω => ⟨fun i => coin B1 (ω (.inr (.inl i)))⟩)
      (fun ω => ⟨fun i => coin B2 (ω (.inr (.inr i)))⟩) :=
  Validation.FreshNoiseL2.subGaussSamplerOK_of_samplerOK _ Bu B1 B2 mn md _ _ _
    (Validation.FreshNoise.samplerOK_rademacher N Bu B1 B2 mn md)

theorem freshError_tail_l2 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (hN : 0 < N) (s e : IntPoly N) (E2 S2 Vu V1 V2 mn md : ℕ)
    (hs : normSq s ≤ S2) (he : normSq e ≤ E2) (u e₁ e₂ : Ω → IntPoly N)
    (h : SubGaussSamplerOK μ Vu V1 V2 mn md u e₁ e₂) (ε : ℝ) (hε : 0 ≤ ε) :
    μ.real {ω | ε + (mn : ℝ) / md * (E2 + 1 + S2 : ℕ) ≤
        (normInf (freshError s e (u ω) (e₁ ω) (e₂ ω)) : ℝ)} ≤
      2 * N * Real.exp (-ε ^ 2 / (2 * (varProxyL2 E2 S2 Vu V1 V2 : ℝ))) :=
  normInf_tail_of_centered hN (fun ω => freshError s e (u ω) (e₁ ω) (e₂ ω)) _
    (drift μ s e u e₁ e₂) _
    (fun k => abs_drift_le (by positivity) h.mean k _ (sum_wt_natAbs_le_l2 s e E2 S2 hs he k))
    (coeff_subG_l2 hN s e E2 S2 Vu V1 V2 mn md hs he u e₁ e₂ h) ε hε

theorem fresh_certified_l2 (P : FullParams) (E : Trace.Budget) (prog : Program) (B Bp ε D : ℕ)
    (hP : SchemeParamsOK P) (hk : P.src.kind = .bgv)
    (hnoise : freshNoise P.src.t Bp (ε + D) ≤ P.inputNoise)
    (fresh : List Var) (hfresh : freshOK? P prog fresh = true)
    (h : refAnalyze P E prog = some B)
    (E2 S2 Vu V1 V2 mn md : ℕ) (hD : (mn : ℝ) / md * (E2 + 1 + S2 : ℕ) ≤ D)
    (s e b a : IntPoly P.src.N) (hs : normSq s ≤ S2) (he : normSq e ≤ E2)
    (hpk : PublicKeyOK P.src.t (P.src.modulus P.src.qs.length) s e b a)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (u e₁ e₂ : Var → Ω → IntPoly P.src.N)
    (hsamp : ∀ x ∈ fresh, SubGaussSamplerOK μ Vu V1 V2 mn md (u x) (e₁ x) (e₂ x)) :
    μ.real {ω | FreshFails P E prog B fresh Bp s b a u e₁ e₂ ω} ≤
      fresh.length * (2 * P.src.N *
        Real.exp (-(ε : ℝ) ^ 2 / (2 * (varProxyL2 E2 S2 Vu V1 V2 : ℝ)))) := by
  have hN : 0 < P.src.N := by
    obtain ⟨k, hk'⟩ := hP.N_pow2
    rw [hk']; exact Nat.pos_of_ne_zero (by positivity)
  have hsub : {ω | FreshFails P E prog B fresh Bp s b a u e₁ e₂ ω} ⊆
      ⋃ x ∈ fresh, {ω | (ε : ℝ) + (mn : ℝ) / md * (E2 + 1 + S2 : ℕ) ≤
        (normInf (freshError s e (u x ω) (e₁ x ω) (e₂ x ω)) : ℝ)} := by
    intro ω hω
    by_contra hne
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq, not_exists, not_le] at hne
    obtain ⟨p, m, cts, hin, hno⟩ := hω
    refine hno (Validation.FreshNoise.fresh_sound P E prog B Bp (ε + D) hP hk hnoise fresh hfresh h
      s e b a hpk (fun x => u x ω) (fun x => e₁ x ω) (fun x => e₂ x ω) ?_ p m cts hin)
    intro x hx
    have h1 := hne x hx
    have h2 : (normInf (freshError s e (u x ω) (e₁ x ω) (e₂ x ω)) : ℝ) < ((ε + D : ℕ) : ℝ) := by
      push_cast; linarith
    exact_mod_cast h2.le
  refine (measureReal_mono hsub (measure_ne_top μ _)).trans ?_
  refine measureReal_biUnion_list_le μ _ _ fresh fun x hx => ?_
  exact Validation.FreshNoiseL2.freshError_tail_l2 μ hN s e E2 S2 Vu V1 V2 mn md hs he
    (u x) (e₁ x) (e₂ x) (hsamp x hx) (ε : ℝ) (Nat.cast_nonneg ε)

theorem fresh_certified_kappa_l2 (P : FullParams) (E : Trace.Budget) (prog : Program)
    (B Bp κ : ℕ) (hP : SchemeParamsOK P) (hk : P.src.kind = .bgv)
    (fresh : List Var) (E2 S2 Vu V1 V2 mn md : ℕ)
    (hV : 0 < varProxyL2 E2 S2 Vu V1 V2) (hmd : 0 < md)
    (hnoise : freshNoise P.src.t Bp (epsFor (varProxyL2 E2 S2 Vu V1 V2)
      (fresh.length * (2 * P.src.N)) κ + meanDrift (E2 + 1 + S2) mn md) ≤ P.inputNoise)
    (hfresh : freshOK? P prog fresh = true)
    (h : refAnalyze P E prog = some B)
    (s e b a : IntPoly P.src.N) (hs : normSq s ≤ S2) (he : normSq e ≤ E2)
    (hpk : PublicKeyOK P.src.t (P.src.modulus P.src.qs.length) s e b a)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (u e₁ e₂ : Var → Ω → IntPoly P.src.N)
    (hsamp : ∀ x ∈ fresh, SubGaussSamplerOK μ Vu V1 V2 mn md (u x) (e₁ x) (e₂ x)) :
    μ.real {ω | FreshFails P E prog B fresh Bp s b a u e₁ e₂ ω} ≤ (2 : ℝ)⁻¹ ^ κ := by
  have h1 := Validation.FreshNoiseL2.fresh_certified_l2 P E prog B Bp _ _ hP hk hnoise fresh
    hfresh h E2 S2 Vu V1 V2 mn md (Validation.FreshNoise.meanDrift_spec _ mn md hmd)
    s e b a hs he hpk μ u e₁ e₂ hsamp
  have h2 := Validation.FreshNoise.epsFor_spec (varProxyL2 E2 S2 Vu V1 V2)
    (fresh.length * (2 * P.src.N)) κ hV
  push_cast at h2
  refine h1.trans (le_trans (le_of_eq ?_) h2)
  ring

theorem fresh_kappa_decrypts_l2 (P : FullParams) (E : Trace.Budget) (prog : Program)
    (B Bp κ : ℕ) (switched : Bool) (hP : SchemeParamsOK P) (hk : P.src.kind = .bgv)
    (fresh : List Var) (E2 S2 Vu V1 V2 mn md : ℕ)
    (hV : 0 < varProxyL2 E2 S2 Vu V1 V2) (hmd : 0 < md)
    (hnoise : freshNoise P.src.t Bp (epsFor (varProxyL2 E2 S2 Vu V1 V2)
      (fresh.length * (2 * P.src.N)) κ + meanDrift (E2 + 1 + S2) mn md) ≤ P.inputNoise)
    (hfresh : freshOK? P prog fresh = true)
    (h : refAnalyze P E prog = some B) (hc : certOK? P prog B switched = true)
    (s e b a : IntPoly P.src.N) (hs : normSq s ≤ S2) (he : normSq e ≤ E2)
    (hpk : PublicKeyOK P.src.t (P.src.modulus P.src.qs.length) s e b a)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (u e₁ e₂ : Var → Ω → IntPoly P.src.N)
    (hsamp : ∀ x ∈ fresh, SubGaussSamplerOK μ Vu V1 V2 mn md (u x) (e₁ x) (e₂ x)) :
    μ.real {ω | DecryptFails P E prog switched fresh Bp s b a u e₁ e₂ ω} ≤ (2 : ℝ)⁻¹ ^ κ := by
  have hsub : {ω | DecryptFails P E prog switched fresh Bp s b a u e₁ e₂ ω} ⊆
      {ω | FreshFails P E prog B fresh Bp s b a u e₁ e₂ ω} := by
    rintro ω ⟨p, m, cts, hin, hno⟩
    exact ⟨p, m, cts, hin, fun hex =>
      hno (outputsDecrypt_of_encrypts P E prog B switched hP hk hc s _ cts hex)⟩
  exact (measureReal_mono hsub (measure_ne_top μ _)).trans
    (Validation.FreshNoiseL2.fresh_certified_kappa_l2 P E prog B Bp κ hP hk fresh E2 S2 Vu V1 V2
      mn md hV hmd hnoise hfresh h s e b a hs he hpk μ u e₁ e₂ hsamp)

end Validation.FreshNoiseL2
