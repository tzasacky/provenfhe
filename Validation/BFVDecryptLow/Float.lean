import Validation.BFVDecryptLow.Drop
import FHE.Float.Sum

/-!
# Validation.BFVDecryptLow.Float — the binary64 step `t·(x/q) + 0.5`
-/

namespace Validation.BFVDecryptLow
open Spec.Float Spec.DecryptBFV Spec.DecryptBFVLow Challenge.BFVDecryptLow FHE.Float

theorem rounds_abs' {x y : ℚ} (h : Rounds x y) : |y - x| ≤ u * |x| := by
  obtain ⟨δ, hδ, rfl⟩ := h
  have e : x * (1 + δ) - x = δ * x := by ring
  rw [e, abs_mul]
  exact mul_le_mul_of_nonneg_right hδ (abs_nonneg _)

theorem rounds_nonneg {x y : ℚ} (h : Rounds x y) (hx : 0 ≤ x) : 0 ≤ y := by
  obtain ⟨δ, hδ, rfl⟩ := h
  have := (abs_le.mp hδ).1
  have hu : u < 1 := u_lt
  exact mul_nonneg hx (by linarith)

theorem multiplyAndRound_err (A : ArithD) (hA : ConformsD A) (t q x : ℕ) (ht : 2 ≤ t)
    (ht' : t < 2 ^ 60) (hq : 3 ≤ q) (hq' : q < 2 ^ 60) (hx : x ≤ q / 2) :
    let z := A.base.mulAdd (1 / 2) (A.base.ofNat t) (A.base.div (A.base.ofNat x) (A.base.ofNat q))
    |z - ((t : ℚ) * x / q + 1 / 2)| ≤ lowErr t ∧ 0 ≤ z ∧ z < 2 ^ 64 := by
  intro z
  have hu := u_pos
  have hB := hA.base
  have hqQ : (0 : ℚ) < q := by exact_mod_cast (show 0 < q by omega)
  have htQ : (2 : ℚ) ≤ t := by exact_mod_cast ht
  have htQ' : (t : ℚ) < 2 ^ 60 := by exact_mod_cast ht'
  have hqQ' : (q : ℚ) < 2 ^ 60 := by exact_mod_cast hq'
  have hxq : (x : ℚ) / q ≤ 1 / 2 := by
    rw [div_le_iff₀ hqQ]
    have : 2 * x ≤ q := by omega
    have : (2 : ℚ) * x ≤ q := by exact_mod_cast this
    linarith
  have hxq0 : 0 ≤ (x : ℚ) / q := by positivity
  -- conversions
  have hT : Approx u t (A.base.ofNat t) := approx_of_rounds (hB.ofNat t (by omega))
  have hX : Approx u x (A.base.ofNat x) := approx_of_rounds (hB.ofNat x (by omega))
  have hQ : Approx u q (A.base.ofNat q) := approx_of_rounds (hB.ofNat q (by omega))
  -- the quotient
  have hdivE : Approx f0 ((x : ℚ) / q) (A.base.ofNat x / A.base.ofNat q) :=
    hX.div hQ (by have := u_lt; linarith)
  have hvx : ((x : ℚ) / q) = 0 ∨ (1 / 2 ^ 127 ≤ (x : ℚ) / q ∧ (x : ℚ) / q ≤ 2 ^ 127) := by
    rcases Nat.eq_zero_or_pos x with h0 | h0
    · left; simp [h0]
    · right
      constructor
      · rw [le_div_iff₀ hqQ]
        have : (1 : ℚ) ≤ x := by exact_mod_cast h0
        have : (1 : ℚ) / 2 ^ 127 * q ≤ 1 := by
          rw [div_mul_eq_mul_div, one_mul, div_le_one (by positivity)]; linarith
        linarith
      · linarith
  have hQne : A.base.ofNat q ≠ 0 := by
    intro h0
    have := (hQ.bounds (by unfold u; norm_num) hqQ.le).1
    rw [h0] at this; linarith
  have hD : Approx f1 ((x : ℚ) / q) (A.base.div (A.base.ofNat x) (A.base.ofNat q)) :=
    hdivE.rounds (hB.div _ _ hQne (hdivE.inRange f0_bound.2 hvx))
  set D := A.base.div (A.base.ofNat x) (A.base.ofNat q)
  set T := A.base.ofNat t
  set a : ℚ := (t : ℚ) * x / q with ha
  have ha' : a = (x : ℚ) / q * t := by rw [ha]; ring
  have ha0 : 0 ≤ a := by positivity
  have hat : a ≤ t / 2 := by
    rw [ha']; nlinarith
  -- the exact product
  have hP : Approx f2 a (D * T) := by rw [ha']; exact hD.mul hT
  have hva : a = 0 ∨ (1 / 2 ^ 127 ≤ a ∧ a ≤ 2 ^ 127) := by
    rcases hvx with h0 | ⟨h1, _⟩
    · left; rw [ha', h0, zero_mul]
    · right
      constructor
      · rw [ha']; nlinarith
      · rw [ha']; nlinarith
  have hDT : D * T = T * D := mul_comm _ _
  obtain ⟨_, _, he5⟩ := eta5_bound
  have hf2e : f2 ≤ eta5 := by unfold eta5; have := f2_bound; have := u_pos; nlinarith
  have hf2 := f2_bound
  -- the final value
  have h128 : (1 : ℚ) / 2 ^ 128 ≤ 1 / 2 := by norm_num
  have h60 : (2 : ℚ) ^ 60 + 1 ≤ 2 ^ 128 := by norm_num
  have hua : u * a ≤ u * (t / 2) := mul_le_mul_of_nonneg_left hat hu.le
  have key : |z - (a + 1 / 2)| ≤ 25 / 4 * (u * a) + u / 2 ∧ 0 ≤ z := by
    rcases hB.mulAdd (1 / 2) T D with h | h
    · -- `add (1/2) (mul T D)`
      have hP' : Approx f2 a (T * D) := by rw [← hDT]; exact hP
      have hY : Approx eta5 a (A.base.mul T D) :=
        hP'.rounds (hB.mul T D (hP'.inRange hf2.2 hva))
      set Y := A.base.mul T D
      have hY1 := abs_le.mp (hY.abs_sub_le ha0)
      have hYb := hY.bounds (by linarith [eta5_bound.2.1]) ha0
      have hY0' : 0 ≤ Y := le_trans (by positivity) hYb.1
      have hin : InRange (1 / 2 + Y) := inRange_of_bounds (by linarith) (by linarith)
      have hr := hB.add (1 / 2) Y hin
      have hw := rounds_abs' hr
      rw [abs_of_nonneg (show (0 : ℚ) ≤ 1 / 2 + Y by linarith)] at hw
      have hww := abs_le.mp hw
      rw [show z = A.base.add (1 / 2) Y from h]
      refine ⟨?_, rounds_nonneg hr (by linarith)⟩
      have e1 : u * Y ≤ u * (a + eta5 * a) := mul_le_mul_of_nonneg_left (by linarith) hu.le
      have e2 : eta5 * (1 + u) * a ≤ 21 / 4 * u * a := mul_le_mul_of_nonneg_right he5 ha0
      rw [abs_le]
      constructor
      · nlinarith
      · nlinarith
    · -- `fma T D (1/2)`
      have hb := hP.bounds hf2.2 ha0
      have hDT0 : 0 ≤ D * T := le_trans (by positivity) hb.1
      have hin : InRange (T * D + 1 / 2) := by
        rw [← hDT]; exact inRange_of_bounds (by linarith) (by linarith)
      have hr := hB.fma T D (1 / 2) hin
      have hP1 := abs_le.mp (hP.abs_sub_le ha0)
      have hw := rounds_abs' hr
      rw [← hDT] at hw hr
      rw [abs_of_nonneg (show (0 : ℚ) ≤ D * T + 1 / 2 by linarith)] at hw
      have hww := abs_le.mp hw
      rw [show z = A.base.fma T D (1 / 2) from h]
      refine ⟨?_, rounds_nonneg hr (by linarith)⟩
      have e1 : u * (D * T) ≤ u * (a + f2 * a) := mul_le_mul_of_nonneg_left (by linarith) hu.le
      have e2 : f2 * (1 + u) * a ≤ eta5 * (1 + u) * a :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hf2e (by linarith)) ha0
      have e3 : eta5 * (1 + u) * a ≤ 21 / 4 * u * a := mul_le_mul_of_nonneg_right he5 ha0
      rw [abs_le]
      constructor
      · nlinarith
      · nlinarith
  obtain ⟨k1, k2⟩ := key
  have hlow : 25 / 4 * (u * a) + u / 2 ≤ lowErr t := by
    unfold lowErr; nlinarith
  refine ⟨k1.trans hlow, k2, ?_⟩
  have := (abs_le.mp k1).2
  have hl : lowErr t ≤ 2 ^ 10 := by
    have e : lowErr t = (7 * t / 2 + 1) / 2 ^ 53 := by unfold lowErr u; ring
    rw [e, div_le_iff₀ (by positivity)]
    linarith
  have hk := k1.trans hlow
  have := (abs_le.mp hk).2
  linarith

end Validation.BFVDecryptLow
