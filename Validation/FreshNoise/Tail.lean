import Challenge.FreshNoise
import Validation.Ring
import Validation.Scheme.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.MeasureTheory.Integral.Pi

/-!
# Validation.FreshNoise.Tail — the Hoeffding tail bound of a fresh encryption

Proofs of `Challenge.FreshNoise.freshError_tail`, `meanDrift_spec`, `meanDrift_zero`,
`meanDrift_lt`, `varProxy_ternary`, `epsFor_spec` and `samplerOK_rademacher`.

Reusable lemmas:
* `coeff_mul_convWt`, `abs_convWt_le`: coefficient `k` of `a * s` is `∑ i, convWt s k i * aᵢ`
  with `|convWt s k i| ≤ ‖s‖∞`;
* `coeff_freshError`: coefficient `k` of `freshError` as an explicit weighted sum;
* `coeff_freshError_coords`: the same as one sum over the `3N` coordinates with weights `wt`;
* `cmean`, `drift`, `coeff_sub_drift`, `abs_drift_le`, `sum_wt_natAbs`: the mean of a coefficient
  of `freshError` is the weighted sum of the coordinate means, at most the mean bound times the
  total weight;
* `centered_sum_subG`: a coefficient of `freshError`, minus its mean, is sub-Gaussian with the
  sum of the parameters of its centred weighted coordinates;
* `coeff_subG`: with support bounds that parameter is `varProxy`;
* `tail_union`, `normInf_tail_of_centered`: the union bound over the coefficients and the two
  signs, with a deterministic drift.
-/

namespace Validation.FreshNoise
open Spec NPoly Spec.Encrypt Challenge.FreshNoise MeasureTheory ProbabilityTheory
open Validation.Ring Validation.Scheme
open scoped NNReal

variable {N : ℕ}

/-! ### The negacyclic product as a weighted sum -/

/-- The weight of `aᵢ` in coefficient `k` of `a * s`. -/
def convWt (s : IntPoly N) (k i : Fin N) : ℤ :=
  if h : i.val ≤ k.val then s.coeff ⟨k.val - i.val, by have := k.isLt; omega⟩
  else -s.coeff ⟨N + k.val - i.val, by have := k.isLt; have := i.isLt; omega⟩

theorem coeff_mul_convWt (a s : IntPoly N) (k : Fin N) :
    (a * s).coeff k = ∑ i, convWt s k i * a.coeff i := by
  rw [coeff_mul']
  refine Finset.sum_congr rfl fun i _ => ?_
  unfold convWt
  split_ifs <;> ring

theorem abs_convWt_le (s : IntPoly N) (k i : Fin N) : |convWt s k i| ≤ (normInf s : ℤ) := by
  unfold convWt
  split_ifs
  · exact abs_coeff_le_normInf _ _
  · rw [abs_neg]; exact abs_coeff_le_normInf _ _

theorem npoly_mul_comm (hN : 0 < N) (a b : IntPoly N) : a * b = b * a := by
  have : NeZero N := ⟨hN.ne'⟩
  exact mul_comm a b

/-- Coefficient `k` of the error of a fresh encryption, as a weighted sum of the coefficients of
the randomness. -/
theorem coeff_freshError (hN : 0 < N) (s e u e₁ e₂ : IntPoly N) (k : Fin N) :
    (freshError s e u e₁ e₂).coeff k =
      ∑ i, convWt e k i * u.coeff i + e₁.coeff k + ∑ i, convWt s k i * e₂.coeff i := by
  unfold freshError
  rw [coeff_add', coeff_add', npoly_mul_comm hN e u, coeff_mul_convWt, coeff_mul_convWt]

/-- The weight of each of the `3N` coordinates in coefficient `k` of `freshError`. -/
def wt (s e : IntPoly N) (k : Fin N) : Fin N ⊕ Fin N ⊕ Fin N → ℤ :=
  Sum.elim (convWt e k) (Sum.elim (fun i => if i = k then 1 else 0) (convWt s k))

section Coords
variable {Ω : Type*} (u e₁ e₂ : Ω → IntPoly N)

theorem coords_inl (i : Fin N) (ω : Ω) :
    Challenge.FreshNoise.coords u e₁ e₂ (.inl i) ω = (u ω).coeff i := rfl
theorem coords_inrl (i : Fin N) (ω : Ω) :
    Challenge.FreshNoise.coords u e₁ e₂ (.inr (.inl i)) ω = (e₁ ω).coeff i := rfl
theorem coords_inrr (i : Fin N) (ω : Ω) :
    Challenge.FreshNoise.coords u e₁ e₂ (.inr (.inr i)) ω = (e₂ ω).coeff i := rfl

theorem coordBound_inl (Bu B1 B2 : ℕ) (i : Fin N) :
    Challenge.FreshNoise.coordBound N Bu B1 B2 (.inl i) = Bu := rfl
theorem coordBound_inrl (Bu B1 B2 : ℕ) (i : Fin N) :
    Challenge.FreshNoise.coordBound N Bu B1 B2 (.inr (.inl i)) = B1 := rfl
theorem coordBound_inrr (Bu B1 B2 : ℕ) (i : Fin N) :
    Challenge.FreshNoise.coordBound N Bu B1 B2 (.inr (.inr i)) = B2 := rfl

/-- Coefficient `k` of `freshError` as one sum over the `3N` coordinates. -/
theorem coeff_freshError_coords (hN : 0 < N) (s e : IntPoly N) (k : Fin N) (ω : Ω) :
    ((freshError s e (u ω) (e₁ ω) (e₂ ω)).coeff k : ℝ) =
      ∑ j, (wt s e k j : ℝ) * (coords u e₁ e₂ j ω : ℝ) := by
  rw [coeff_freshError hN, Fintype.sum_sum_type, Fintype.sum_sum_type]
  simp only [wt, Sum.elim_inl, Sum.elim_inr, coords_inl, coords_inrl, coords_inrr]
  push_cast
  simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  ring

end Coords

/-! ### Sub-Gaussian parameters -/

/-- The sub-Gaussian parameter of each weighted coordinate. -/
noncomputable def par (N Bs Bk Bu B1 B2 : ℕ) (k : Fin N) : Fin N ⊕ Fin N ⊕ Fin N → ℝ≥0 :=
  Sum.elim (fun _ => ((Bk : ℝ≥0) * Bu) ^ 2)
    (Sum.elim (fun i => if i = k then (B1 : ℝ≥0) ^ 2 else 0) (fun _ => ((B2 : ℝ≥0) * Bs) ^ 2))

theorem sum_par (Bs Bk Bu B1 B2 : ℕ) (k : Fin N) :
    ∑ j, par N Bs Bk Bu B1 B2 k j = ((varProxy N Bs Bk Bu B1 B2 : ℕ) : ℝ≥0) := by
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
  simp only [par, Sum.elim_inl, Sum.elim_inr, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, Finset.sum_ite_eq', Finset.mem_univ, ite_true, varProxy, nsmul_eq_mul]
  push_cast
  ring

/-- The sub-Gaussian parameter can be weakened. -/
theorem subG_mono {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω} {X : Ω → ℝ} {c c' : ℝ≥0}
    (h : HasSubgaussianMGF X c μ) (hc : c ≤ c') : HasSubgaussianMGF X c' μ := by
  have hc' : (c : ℝ) ≤ c' := by exact_mod_cast hc
  exact ⟨h.integrable_exp_mul, fun t => (h.mgf_le t).trans (Real.exp_le_exp.2 (by gcongr))⟩

/-- `r²` as a non-negative real: the factor of `HasSubgaussianMGF.const_mul`. -/
noncomputable def sqNN (r : ℝ) : ℝ≥0 := ⟨r ^ 2, sq_nonneg r⟩

theorem coe_sqNN (r : ℝ) : (sqNN r : ℝ) = r ^ 2 := rfl

theorem sqNN_intCast_le (w : ℤ) (B : ℕ) (hw : |w| ≤ (B : ℤ)) : sqNN (w : ℝ) ≤ (B : ℝ≥0) ^ 2 := by
  have hw' : |(w : ℝ)| ≤ (B : ℝ) := by exact_mod_cast hw
  rw [← NNReal.coe_le_coe, coe_sqNN]
  push_cast
  exact sq_le_sq' (neg_le_of_abs_le hw') (le_of_abs_le hw')

theorem subG_const_mul {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω} {X : Ω → ℝ} {c : ℝ≥0}
    (h : HasSubgaussianMGF X c μ) (r : ℝ) :
    HasSubgaussianMGF (fun ω => r * X ω) (sqNN r * c) μ := h.const_mul r

/-! ### Means and the drift -/

/-- The mean of coordinate `j` of the randomness. -/
noncomputable abbrev cmean {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (u e₁ e₂ : Ω → IntPoly N) (j : Fin N ⊕ Fin N ⊕ Fin N) : ℝ :=
  ∫ ω, (coords u e₁ e₂ j ω : ℝ) ∂μ

/-- The mean of coefficient `k` of `freshError`: the weighted sum of the coordinate means. -/
noncomputable def drift {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (s e : IntPoly N)
    (u e₁ e₂ : Ω → IntPoly N) (k : Fin N) : ℝ :=
  ∑ j, (wt s e k j : ℝ) * cmean μ u e₁ e₂ j

theorem natAbs_convWt_le (s : IntPoly N) (k i : Fin N) : (convWt s k i).natAbs ≤ normInf s := by
  have := abs_convWt_le s k i
  rw [Int.abs_eq_natAbs] at this
  exact_mod_cast this

/-- The total weight of the `3N` coordinates in coefficient `k`: `‖e‖₁ + 1 + ‖s‖₁`, up to the
signed permutation of the weights. -/
theorem sum_wt_natAbs (s e : IntPoly N) (k : Fin N) :
    ∑ j, (wt s e k j).natAbs =
      ∑ i, (convWt e k i).natAbs + 1 + ∑ i, (convWt s k i).natAbs := by
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
  simp only [wt, Sum.elim_inl, Sum.elim_inr]
  have h1 : ∀ i : Fin N, (if i = k then (1 : ℤ) else 0).natAbs = if i = k then 1 else 0 := by
    intro i; split_ifs <;> rfl
  simp only [h1, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  ring

section Tail
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  {Bs Bk Bu B1 B2 mn md : ℕ} {s e : IntPoly N} {u e₁ e₂ : Ω → IntPoly N}

/-- Coefficient `k` of `freshError`, minus its drift, as a sum of centred weighted coordinates. -/
theorem coeff_sub_drift (hN : 0 < N) (s e : IntPoly N) (u e₁ e₂ : Ω → IntPoly N) (k : Fin N)
    (ω : Ω) :
    ((freshError s e (u ω) (e₁ ω) (e₂ ω)).coeff k : ℝ) - drift μ s e u e₁ e₂ k =
      ∑ j, (wt s e k j : ℝ) * ((coords u e₁ e₂ j ω : ℝ) - cmean μ u e₁ e₂ j) := by
  rw [coeff_freshError_coords u e₁ e₂ hN, drift, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- **The drift is at most the mean bound times the total weight.** -/
theorem abs_drift_le {M : ℝ} (hM : 0 ≤ M) (hm : ∀ j, |cmean μ u e₁ e₂ j| ≤ M) (k : Fin N)
    (W : ℕ) (hW : ∑ j, (wt s e k j).natAbs ≤ W) : |drift μ s e u e₁ e₂ k| ≤ M * (W : ℝ) := by
  have hW' : ((∑ j, (wt s e k j).natAbs : ℕ) : ℝ) ≤ (W : ℝ) := by exact_mod_cast hW
  calc |drift μ s e u e₁ e₂ k|
      ≤ ∑ j, |(wt s e k j : ℝ) * cmean μ u e₁ e₂ j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, ((wt s e k j).natAbs : ℝ) * M := by
        refine Finset.sum_le_sum fun j _ => ?_
        rw [abs_mul, Nat.cast_natAbs, Int.cast_abs]
        exact mul_le_mul_of_nonneg_left (hm j) (abs_nonneg _)
    _ = ((∑ j, (wt s e k j).natAbs : ℕ) : ℝ) * M := by rw [← Finset.sum_mul]; push_cast; rfl
    _ ≤ (W : ℝ) * M := mul_le_mul_of_nonneg_right hW' hM
    _ = M * (W : ℝ) := mul_comm _ _

/-- A sum of independent centred weighted coordinates is sub-Gaussian with the sum of the
parameters: coefficient `k` of `freshError` about its mean. -/
theorem centered_sum_subG (hN : 0 < N) (s e : IntPoly N) (u e₁ e₂ : Ω → IntPoly N) (k : Fin N)
    (hind : iIndepFun (fun j ω => (coords u e₁ e₂ j ω : ℝ)) μ) (c : Fin N ⊕ Fin N ⊕ Fin N → ℝ≥0)
    (hc : ∀ j, HasSubgaussianMGF
      (fun ω => (wt s e k j : ℝ) * ((coords u e₁ e₂ j ω : ℝ) - cmean μ u e₁ e₂ j)) (c j) μ) :
    HasSubgaussianMGF
      (fun ω => ((freshError s e (u ω) (e₁ ω) (e₂ ω)).coeff k : ℝ) - drift μ s e u e₁ e₂ k)
      (∑ j, c j) μ := by
  have hind' : iIndepFun
      (fun j ω => (wt s e k j : ℝ) * ((coords u e₁ e₂ j ω : ℝ) - cmean μ u e₁ e₂ j)) μ :=
    hind.comp (fun j x => (wt s e k j : ℝ) * (x - cmean μ u e₁ e₂ j))
      (fun j => (measurable_id.sub_const _).const_mul _)
  have key := HasSubgaussianMGF.sum_of_iIndepFun hind' (s := Finset.univ) (fun j _ => hc j)
  exact key.congr (ae_of_all _ fun ω => (coeff_sub_drift hN s e u e₁ e₂ k ω).symm)

variable [IsProbabilityMeasure μ]

/-- The union bound over `N` sub-Gaussian variables and the two signs. -/
theorem tail_union (G : Fin N → Ω → ℝ) (V : ℕ)
    (h : ∀ k : Fin N, HasSubgaussianMGF (G k) ((V : ℕ) : ℝ≥0) μ) (ε : ℝ) (hε : 0 ≤ ε) :
    μ.real (⋃ k : Fin N, {ω | ε ≤ |G k ω|}) ≤ 2 * N * Real.exp (-ε ^ 2 / (2 * (V : ℝ))) := by
  have hcoeff : ∀ k : Fin N, μ.real {ω | ε ≤ |G k ω|} ≤
      2 * Real.exp (-ε ^ 2 / (2 * (V : ℝ))) := by
    intro k
    have h1 := (h k).measure_ge_le hε
    have h2 := (h k).neg.measure_ge_le hε
    simp only [NNReal.coe_natCast] at h1 h2
    have hsub : {ω | ε ≤ |G k ω|} ⊆ {ω | ε ≤ G k ω} ∪ {ω | ε ≤ (-G k) ω} := by
      intro ω hω
      rcases le_abs.1 (show ε ≤ |_| from hω) with h' | h'
      · exact Or.inl h'
      · exact Or.inr h'
    calc _ ≤ μ.real (_ ∪ _) := measureReal_mono hsub
      _ ≤ _ + _ := measureReal_union_le _ _
      _ ≤ _ := by linarith
  calc _ ≤ ∑ k : Fin N, μ.real {ω | ε ≤ |G k ω|} := measureReal_iUnion_fintype_le _
    _ ≤ ∑ _k : Fin N, 2 * Real.exp (-ε ^ 2 / (2 * (V : ℝ))) :=
      Finset.sum_le_sum fun k _ => hcoeff k
    _ = _ := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

/-- From coefficients that are sub-Gaussian about `d k`, `|d k| ≤ D`, to the tail of the `ℓ∞`
norm beyond `ε + D`. -/
theorem normInf_tail_of_centered (hN : 0 < N) (F : Ω → IntPoly N) (V : ℕ) (d : Fin N → ℝ)
    (D : ℝ) (hd : ∀ k, |d k| ≤ D)
    (h : ∀ k : Fin N, HasSubgaussianMGF (fun ω => ((F ω).coeff k : ℝ) - d k)
      ((V : ℕ) : ℝ≥0) μ) (ε : ℝ) (hε : 0 ≤ ε) :
    μ.real {ω | ε + D ≤ (normInf (F ω) : ℝ)} ≤ 2 * N * Real.exp (-ε ^ 2 / (2 * (V : ℝ))) := by
  have hsub : {ω | ε + D ≤ (normInf (F ω) : ℝ)} ⊆
      ⋃ k : Fin N, {ω | ε ≤ |((F ω).coeff k : ℝ) - d k|} := by
    intro ω hω
    obtain ⟨k, -, hk⟩ := Finset.exists_mem_eq_sup Finset.univ ⟨⟨0, hN⟩, Finset.mem_univ _⟩
      (fun i => ((F ω).coeff i).natAbs)
    refine Set.mem_iUnion.2 ⟨k, ?_⟩
    have hn : normInf (F ω) = ((F ω).coeff k).natAbs := hk
    have hω' : ε + D ≤ (normInf (F ω) : ℝ) := hω
    rw [hn, Nat.cast_natAbs, Int.cast_abs] at hω'
    have h1 := abs_add_le (((F ω).coeff k : ℝ) - d k) (d k)
    rw [sub_add_cancel] at h1
    have h2 := hd k
    show ε ≤ |((F ω).coeff k : ℝ) - d k|
    linarith
  exact (measureReal_mono hsub).trans
    (tail_union (fun k ω => ((F ω).coeff k : ℝ) - d k) V h ε hε)

/-- Hoeffding's lemma for one coordinate of the randomness, about its mean. -/
theorem coord_subG (h : SamplerOK μ Bu B1 B2 mn md u e₁ e₂) (j : Fin N ⊕ Fin N ⊕ Fin N) :
    HasSubgaussianMGF (fun ω => (coords u e₁ e₂ j ω : ℝ) - cmean μ u e₁ e₂ j)
      (((coordBound N Bu B1 B2 j : ℕ) : ℝ≥0) ^ 2) μ := by
  have hb : ∀ᵐ ω ∂μ, (coords u e₁ e₂ j ω : ℝ) ∈
      Set.Icc (-(coordBound N Bu B1 B2 j : ℝ)) (coordBound N Bu B1 B2 j : ℝ) := by
    filter_upwards [h.bound j] with ω hω
    rw [abs_le] at hω
    exact ⟨by exact_mod_cast hω.1, by exact_mod_cast hω.2⟩
  have key := hasSubgaussianMGF_of_mem_Icc (h.meas j) hb
  refine subG_mono key (le_of_eq ?_)
  apply NNReal.eq
  push_cast
  rw [sub_neg_eq_add, Real.norm_of_nonneg (by positivity)]
  ring

/-- Each centred weighted coordinate is sub-Gaussian with parameter `par`. -/
theorem term_subG (hs : normInf s ≤ Bs) (he : normInf e ≤ Bk)
    (h : SamplerOK μ Bu B1 B2 mn md u e₁ e₂) (k : Fin N) (j : Fin N ⊕ Fin N ⊕ Fin N) :
    HasSubgaussianMGF
      (fun ω => (wt s e k j : ℝ) * ((coords u e₁ e₂ j ω : ℝ) - cmean μ u e₁ e₂ j))
      (par N Bs Bk Bu B1 B2 k j) μ := by
  refine subG_mono (subG_const_mul (coord_subG h j) (wt s e k j : ℝ)) ?_
  rcases j with i | i | i
  · show sqNN ((convWt e k i : ℤ) : ℝ) * ((Bu : ℕ) : ℝ≥0) ^ 2 ≤ ((Bk : ℝ≥0) * Bu) ^ 2
    rw [mul_pow]
    exact mul_le_mul' (sqNN_intCast_le _ _ ((abs_convWt_le e k i).trans (by exact_mod_cast he)))
      le_rfl
  · show sqNN (((if i = k then 1 else 0 : ℤ)) : ℝ) * ((B1 : ℕ) : ℝ≥0) ^ 2 ≤
      if i = k then (B1 : ℝ≥0) ^ 2 else 0
    have h1 : sqNN (((if i = k then 1 else 0 : ℤ)) : ℝ) = if i = k then 1 else 0 := by
      apply NNReal.eq
      rw [coe_sqNN]
      split_ifs <;> simp
    rw [h1]
    split_ifs <;> simp
  · show sqNN ((convWt s k i : ℤ) : ℝ) * ((B2 : ℕ) : ℝ≥0) ^ 2 ≤ ((B2 : ℝ≥0) * Bs) ^ 2
    rw [mul_pow, mul_comm]
    exact mul_le_mul' le_rfl
      (sqNN_intCast_le _ _ ((abs_convWt_le s k i).trans (by exact_mod_cast hs)))

/-- **Each coefficient of the error of a fresh encryption is, about its mean, sub-Gaussian**
with parameter `varProxy`. -/
theorem coeff_subG (hN : 0 < N) (hs : normInf s ≤ Bs) (he : normInf e ≤ Bk)
    (h : SamplerOK μ Bu B1 B2 mn md u e₁ e₂) (k : Fin N) :
    HasSubgaussianMGF
      (fun ω => ((freshError s e (u ω) (e₁ ω) (e₂ ω)).coeff k : ℝ) - drift μ s e u e₁ e₂ k)
      ((varProxy N Bs Bk Bu B1 B2 : ℕ) : ℝ≥0) μ := by
  have key := centered_sum_subG hN s e u e₁ e₂ k h.indep _
    (fun j => term_subG (Bs := Bs) (Bk := Bk) hs he h k j)
  rwa [sum_par] at key

/-- The total weight from support bounds: `N·B_k + 1 + N·B_s`. -/
theorem sum_wt_natAbs_le (hs : normInf s ≤ Bs) (he : normInf e ≤ Bk) (k : Fin N) :
    ∑ j, (wt s e k j).natAbs ≤ N * Bk + 1 + N * Bs := by
  rw [sum_wt_natAbs]
  have h1 : ∑ i, (convWt e k i).natAbs ≤ N * Bk := by
    calc _ ≤ ∑ _i : Fin N, Bk := Finset.sum_le_sum fun i _ => (natAbs_convWt_le e k i).trans he
      _ = _ := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  have h2 : ∑ i, (convWt s k i).natAbs ≤ N * Bs := by
    calc _ ≤ ∑ _i : Fin N, Bs := Finset.sum_le_sum fun i _ => (natAbs_convWt_le s k i).trans hs
      _ = _ := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  omega

end Tail

/-! ### The locked statements -/

theorem freshError_tail {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (hN : 0 < N) (s e : IntPoly N) (Bs Bk Bu B1 B2 mn md : ℕ) (hs : normInf s ≤ Bs)
    (he : normInf e ≤ Bk) (u e₁ e₂ : Ω → IntPoly N) (h : SamplerOK μ Bu B1 B2 mn md u e₁ e₂)
    (ε : ℝ) (hε : 0 ≤ ε) :
    μ.real {ω | ε + (mn : ℝ) / md * (N * Bk + 1 + N * Bs : ℕ) ≤
        (normInf (freshError s e (u ω) (e₁ ω) (e₂ ω)) : ℝ)} ≤
      2 * N * Real.exp (-ε ^ 2 / (2 * (varProxy N Bs Bk Bu B1 B2 : ℝ))) :=
  normInf_tail_of_centered hN (fun ω => freshError s e (u ω) (e₁ ω) (e₂ ω)) _
    (drift μ s e u e₁ e₂) _
    (fun k => abs_drift_le (by positivity) h.mean k _ (sum_wt_natAbs_le hs he k))
    (fun k => coeff_subG hN hs he h k) ε hε

theorem meanDrift_spec (W mn md : ℕ) (hmd : 0 < md) :
    (mn : ℝ) / md * (W : ℝ) ≤ (meanDrift W mn md : ℝ) := by
  have h1 : mn * W ≤ md * meanDrift W mn md := by
    have := Nat.lt_mul_div_succ (mn * W + (md - 1)) hmd
    unfold meanDrift
    rw [Nat.mul_succ] at this
    omega
  have h1' : (mn : ℝ) * W ≤ md * (meanDrift W mn md : ℝ) := by exact_mod_cast h1
  have hmd' : (0 : ℝ) < md := by exact_mod_cast hmd
  rw [div_mul_eq_mul_div, div_le_iff₀ hmd']
  linarith

theorem meanDrift_zero (W md : ℕ) : meanDrift W 0 md = 0 := by
  unfold meanDrift
  rw [Nat.zero_mul, Nat.zero_add]
  rcases Nat.eq_zero_or_pos md with h | h
  · rw [h]
  · exact Nat.div_eq_of_lt (by omega)

theorem meanDrift_lt (W mn md : ℕ) (hmd : 0 < md) :
    (meanDrift W mn md : ℝ) < (mn : ℝ) / md * (W : ℝ) + 1 := by
  have h1 : md * meanDrift W mn md < mn * W + md := by
    have := Nat.mul_div_le (mn * W + (md - 1)) md
    unfold meanDrift
    omega
  have h1' : (md : ℝ) * (meanDrift W mn md : ℝ) < mn * W + md := by exact_mod_cast h1
  have hmd' : (0 : ℝ) < md := by exact_mod_cast hmd
  have h2 : (mn : ℝ) / md * (W : ℝ) + 1 = (mn * W + md) / md := by field_simp
  rw [h2, lt_div_iff₀ hmd']
  linarith

theorem varProxy_ternary (N B : ℕ) : varProxy N 1 B 1 B B = B ^ 2 * (2 * N + 1) := by
  unfold varProxy; ring

theorem epsFor_spec (V count κ : ℕ) (hV : 0 < V) :
    (count : ℝ) * Real.exp (-(epsFor V count κ : ℝ) ^ 2 / (2 * (V : ℝ))) ≤ (2 : ℝ)⁻¹ ^ κ := by
  obtain ⟨L, hL⟩ : ∃ L, L = κ + Nat.clog 2 count := ⟨_, rfl⟩
  obtain ⟨F, hF⟩ : ∃ F, F = 2 * V * L * 6931471808 / 10 ^ 10 := ⟨_, rfl⟩
  have hε : epsFor V count κ = Nat.sqrt F + 1 := by rw [hF, hL]; rfl
  have h1 : F + 1 ≤ (Nat.sqrt F + 1) ^ 2 := Nat.lt_succ_sqrt' F
  have h2 : ∀ X : ℕ, X < (X / 10 ^ 10 + 1) * 10 ^ 10 := fun X => by
    norm_num; omega
  have h3 : 2 * V * L * 6931471808 < (F + 1) * 10 ^ 10 := by rw [hF]; exact h2 _
  have h1' : (F : ℝ) + 1 ≤ (epsFor V count κ : ℝ) ^ 2 := by rw [hε]; exact_mod_cast h1
  have h3' : (2 * V * L * 6931471808 : ℝ) < ((F : ℝ) + 1) * 10 ^ 10 := by exact_mod_cast h3
  have hlog := Real.log_two_lt_d9
  have hVL : (0 : ℝ) ≤ (L : ℝ) * (2 * V) := by positivity
  have h4 : (L : ℝ) * (2 * V) * Real.log 2 ≤ (L : ℝ) * (2 * V) * 0.6931471808 :=
    mul_le_mul_of_nonneg_left hlog.le hVL
  have key : (L : ℝ) * Real.log 2 * (2 * V) ≤ (epsFor V count κ : ℝ) ^ 2 := by
    norm_num at h4 ⊢; nlinarith
  have hVpos : (0 : ℝ) < 2 * V := by positivity
  have hexp : Real.exp (-(epsFor V count κ : ℝ) ^ 2 / (2 * (V : ℝ))) ≤ (2 : ℝ)⁻¹ ^ L := by
    have : -(epsFor V count κ : ℝ) ^ 2 / (2 * (V : ℝ)) ≤ -((L : ℝ) * Real.log 2) := by
      rw [neg_div, neg_le_neg_iff, le_div_iff₀ hVpos]; exact key
    calc _ ≤ Real.exp (-((L : ℝ) * Real.log 2)) := Real.exp_le_exp.2 this
      _ = _ := by
        rw [Real.exp_neg, Real.exp_nat_mul, Real.exp_log (by norm_num), inv_pow]
  have hcount : (count : ℝ) ≤ 2 ^ Nat.clog 2 count := by
    exact_mod_cast Nat.le_pow_clog (by norm_num) count
  have hc0 : (0 : ℝ) ≤ count := Nat.cast_nonneg _
  calc (count : ℝ) * Real.exp (-(epsFor V count κ : ℝ) ^ 2 / (2 * (V : ℝ)))
      ≤ (count : ℝ) * (2 : ℝ)⁻¹ ^ L := mul_le_mul_of_nonneg_left hexp hc0
    _ = (2 : ℝ)⁻¹ ^ κ * ((count : ℝ) * (2 : ℝ)⁻¹ ^ Nat.clog 2 count) := by
      rw [hL, pow_add]; ring
    _ ≤ (2 : ℝ)⁻¹ ^ κ * 1 := by
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      rw [inv_pow, ← div_eq_mul_inv, div_le_one (by positivity)]
      exact hcount
    _ = _ := mul_one _

/-! ### The Rademacher sampler -/

theorem coin_eq (B : ℕ) (x : Bool) :
    Challenge.FreshNoise.coin B x = if x then (B : ℤ) else -B := rfl

instance coinProb : IsProbabilityMeasure
    ((2⁻¹ : NNReal) • (Measure.dirac true + Measure.dirac false) : Measure Bool) := by
  constructor
  rw [Measure.smul_apply, Measure.add_apply, measure_univ, measure_univ, ENNReal.smul_def,
    smul_eq_mul, one_add_one_eq_two]
  simp [ENNReal.inv_mul_cancel]

theorem samplerOK_rademacher (N Bu B1 B2 mn md : ℕ) :
    SamplerOK (N := N)
      (Measure.pi fun _ : Fin N ⊕ Fin N ⊕ Fin N =>
        ((2⁻¹ : NNReal) • (Measure.dirac true + Measure.dirac false) : Measure Bool))
      Bu B1 B2 mn md
      (fun ω => ⟨fun i => coin Bu (ω (.inl i))⟩)
      (fun ω => ⟨fun i => coin B1 (ω (.inr (.inl i)))⟩)
      (fun ω => ⟨fun i => coin B2 (ω (.inr (.inr i)))⟩) := by
  have hc : ∀ (j : Fin N ⊕ Fin N ⊕ Fin N) (ω : Fin N ⊕ Fin N ⊕ Fin N → Bool),
      coords (fun ω => (⟨fun i => coin Bu (ω (.inl i))⟩ : IntPoly N))
        (fun ω => ⟨fun i => coin B1 (ω (.inr (.inl i)))⟩)
        (fun ω => ⟨fun i => coin B2 (ω (.inr (.inr i)))⟩) j ω =
      coin (coordBound N Bu B1 B2 j) (ω j) := by
    rintro (i | i | i) ω <;> rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [hc]
    exact iIndepFun_pi (X := fun j b => ((coin (coordBound N Bu B1 B2 j) b : ℤ) : ℝ))
      (fun j => (measurable_of_finite _).aemeasurable)
  · intro j
    simp only [hc]
    exact ((measurable_of_finite
      (fun b : Bool => ((coin (coordBound N Bu B1 B2 j) b : ℤ) : ℝ))).comp
        (measurable_pi_apply j)).aemeasurable
  · intro j
    simp only [hc]
    refine le_of_eq_of_le (congrArg abs ?_) (abs_zero.trans_le (by positivity))
    refine (integral_comp_eval (μ := fun _ : Fin N ⊕ Fin N ⊕ Fin N =>
      ((2⁻¹ : NNReal) • (Measure.dirac true + Measure.dirac false) : Measure Bool)) (i := j)
      (f := fun b : Bool => ((coin (coordBound N Bu B1 B2 j) b : ℤ) : ℝ))
      (measurable_of_finite _).aestronglyMeasurable).trans ?_
    rw [integral_smul_nnreal_measure, integral_add_measure (Integrable.of_finite)
      (Integrable.of_finite), integral_dirac, integral_dirac, coin_eq, coin_eq]
    simp
  · intro j
    refine ae_of_all _ fun ω => ?_
    rw [hc, coin_eq]
    cases ω j <;> simp

end Validation.FreshNoise
