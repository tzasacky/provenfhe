import Validation.Source

/-!
# Validation.Switch — the t-corrected modulus switch of one integer

Scalar facts about `(x + t·[−x·t⁻¹]_q) / q`, the coefficient map of
`Challenge.Source.bgvModSwitchComp` and of `Spec.Decrypt.switchPhase`: the division is exact, the
result depends on `x` modulo `q·Q'` only up to a multiple of `Q'`, it is `q⁻¹·x` modulo `t`, and
it is bounded by `(|x| + t·⌊q/2⌋)/q`.
-/

namespace Validation.Switch
open Validation.Source

/-- The t-corrected switch of one integer by `q`. -/
def sw (t q : ℕ) (x : ℤ) : ℤ :=
  (x + (t : ℤ) * (((-x : ℤ) : ZMod q) * (t : ZMod q)⁻¹).valMinAbs) / q

/-- The correction term. -/
def corr (t q : ℕ) (x : ℤ) : ℤ := (t : ℤ) * (((-x : ℤ) : ZMod q) * (t : ZMod q)⁻¹).valMinAbs

theorem q_mul_sw {t q : ℕ} (hcop : Nat.Coprime t q) (x : ℤ) :
    (q : ℤ) * sw t q x = x + corr t q x := by
  show (q : ℤ) * ((x + (t : ℤ) * (((-x : ℤ) : ZMod q) * (t : ZMod q)⁻¹).valMinAbs) / q) = _
  apply Int.mul_ediv_cancel'
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  have := ZMod.coe_mul_inv_eq_one t hcop
  linear_combination (-(x : ZMod q)) * this

theorem abs_corr_le (t q : ℕ) [NeZero q] (x : ℤ) : |corr t q x| ≤ (t : ℤ) * ((q / 2 : ℕ) : ℤ) := by
  show |(t : ℤ) * _| ≤ _
  rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℤ) ≤ t)]
  exact mul_le_mul_of_nonneg_left (abs_valMinAbs_le _) (by positivity)

theorem corr_congr {t q : ℕ} {x y : ℤ} (h : ((x : ℤ) : ZMod q) = y) : corr t q x = corr t q y := by
  unfold corr
  push_cast
  rw [h]

/-- Inputs congruent modulo `q·Q'` give outputs congruent modulo `Q'`. -/
theorem sw_congr {t q : ℕ} (hq : 0 < q) (hcop : Nat.Coprime t q) (Q' : ℕ) {x y : ℤ}
    (h : ((x : ℤ) : ZMod (q * Q')) = y) : ((sw t q x : ℤ) : ZMod Q') = sw t q y := by
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at h ⊢
  obtain ⟨k, hk⟩ := h
  have hq' : ((x : ℤ) : ZMod q) = y := by
    rw [ZMod.intCast_eq_intCast_iff_dvd_sub]
    exact ⟨Q' * k, by rw [hk]; push_cast; ring⟩
  have h1 := q_mul_sw hcop x
  have h2 := q_mul_sw hcop y
  rw [corr_congr hq'] at h1
  refine ⟨k, ?_⟩
  have hq0 : (q : ℤ) ≠ 0 := by exact_mod_cast hq.ne'
  apply mul_left_cancel₀ hq0
  push_cast at hk
  linear_combination h2 - h1 + hk

/-- Modulo `t` the switch multiplies by `q⁻¹`. -/
theorem sw_cast_t {t q : ℕ} (hcop : Nat.Coprime t q) (x : ℤ) :
    ((sw t q x : ℤ) : ZMod t) = (q : ZMod t)⁻¹ * x := by
  have h1 := congrArg (Int.cast : ℤ → ZMod t) (q_mul_sw hcop x)
  have hc : ((corr t q x : ℤ) : ZMod t) = 0 := by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]; exact ⟨_, rfl⟩
  push_cast at h1
  rw [hc] at h1
  have hinv := ZMod.coe_mul_inv_eq_one q hcop.symm
  linear_combination (-(sw t q x : ZMod t)) * hinv + ((q : ZMod t))⁻¹ * h1

theorem natAbs_sw_le {t q : ℕ} (hq : 0 < q) (hcop : Nat.Coprime t q) {x : ℤ} {B : ℕ}
    (hx : |x| ≤ B) : |sw t q x| ≤ (((B + t * (q / 2)) / q : ℕ) : ℤ) := by
  have : NeZero q := ⟨hq.ne'⟩
  have h1 := q_mul_sw hcop x
  have h2 := abs_corr_le t q x
  have h3 : |(q : ℤ) * sw t q x| ≤ B + (t : ℤ) * ((q / 2 : ℕ) : ℤ) := by
    rw [h1]; exact (abs_add_le _ _).trans (add_le_add hx h2)
  rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℤ) ≤ q), ← Int.natCast_natAbs] at h3
  rw [← Int.natCast_natAbs]
  have h4 : q * (sw t q x).natAbs ≤ B + t * (q / 2) := by exact_mod_cast h3
  have h5 : (sw t q x).natAbs ≤ (B + t * (q / 2)) / q := by
    rw [Nat.le_div_iff_mul_le hq]; linarith
  exact_mod_cast h5

end Validation.Switch
