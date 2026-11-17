import Validation.BFVDecrypt.Words

/-!
# Validation.BFVDecrypt.Float — the error of the decryption sum, per coefficient
-/

namespace Validation.BFVDecrypt
open Spec.Float Spec.DecryptBFV FHE.Float Challenge.BFVDecrypt

theorem sumErr_ge : ∀ (start : ℚ) (cs : List ℕ), 0 ≤ start →
    6 * u * ((cs.sum : ℕ) : ℚ) ≤ sumErr start cs
  | start, [], h => by simp [sumErr]
  | start, c :: cs, h => by
    have ih := sumErr_ge (start + c) cs (by positivity)
    simp only [sumErr, List.sum_cons, Nat.cast_add]
    have hu := u_pos
    nlinarith

theorem sumErr_caps {start : ℚ} {cs : List ℕ} (h0 : 0 ≤ start) (h : sumErr start cs ≤ 1) :
    ((cs.sum : ℕ) : ℚ) ≤ 2 ^ 51 := by
  have := sumErr_ge start cs h0
  have hu := u_pos
  have : 6 * u * ((cs.sum : ℕ) : ℚ) ≤ 1 := by nlinarith
  unfold u at this
  have e : (6 : ℚ) * (1 / 2 ^ 53) * ((cs.sum : ℕ) : ℚ) = ((cs.sum : ℕ) : ℚ) * (6 / 2 ^ 53) := by
    ring
  rw [e] at this
  have : ((cs.sum : ℕ) : ℚ) ≤ 2 ^ 53 / 6 := by
    rw [le_div_iff₀ (by norm_num)]
    have := mul_le_mul_of_nonneg_right this (show (0 : ℚ) ≤ 2 ^ 53 by norm_num)
    nlinarith
  linarith [show (2 : ℚ) ^ 53 / 6 ≤ 2 ^ 51 by norm_num]

/-- **The sum from `start ∈ {0, 1/2}`**: within `sumErr start caps` of `start + exactFrac`,
nonnegative, and zero or at least `2⁻⁶³`. -/
theorem sum_err (A : Arith) (hA : Conforms A) (t : ℕ) (qs xs : List ℕ)
    (hp : decParamsOK? t qs = true) (hx : Reduced qs xs) (start : ℚ)
    (hs : start = 0 ∨ start = 1 / 2) (hδ : sumErr start (caps qs) ≤ 1) :
    |floatSum A start (allWords qs (tables A t qs) xs) - (start + exactFrac t qs xs)| ≤
        sumErr start (caps qs) ∧
      0 ≤ floatSum A start (allWords qs (tables A t qs) xs) ∧
      (floatSum A start (allWords qs (tables A t qs) xs) = 0 ∨
        1 / 2 ^ 63 ≤ floatSum A start (allWords qs (tables A t qs) xs)) := by
  have hl : xs.length = qs.length := hx.length_eq
  have hst0 : 0 ≤ start := by rcases hs with rfl | rfl <;> norm_num
  have hst1 : start ≤ 1 / 2 := by rcases hs with rfl | rfl <;> norm_num
  have hcs := sumErr_caps hst0 hδ
  rw [floatSum_eq, exactFrac_eq, ← caps_eq t qs xs hl] at *
  have hlen := spec_length (t := t) hl
  have hq := (params hp).2.2.2.1
  have key := fold_err' A hA (spec t qs xs) start start start 0 0 (spec_dok hp hx)
    (by omega) hst0 le_rfl (by
      have : (2 : ℚ) ^ 51 + 1 / 2 ≤ 2 ^ 80 := by norm_num
      linarith) le_rfl (by simp) hst0 (by
      rcases hs with h | h
      · exact Or.inl h
      · right; rw [h]; simp; norm_num)
    (by linarith)
  obtain ⟨k1, k2, k3⟩ := key
  refine ⟨by simpa using k1, k2, ?_⟩
  rcases k3 with h | h
  · exact Or.inl h
  · right
    have hlen' : ((0 + (spec t qs xs).length : ℕ) : ℚ) ≤ 256 := by
      have : 0 + (spec t qs xs).length ≤ 256 := by omega
      exact_mod_cast this
    have : (1 : ℚ) / 2 ^ 63 ≤ (1 - ((0 + (spec t qs xs).length : ℕ) : ℚ) * u) / 2 ^ 62 := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      unfold u
      nlinarith
    linarith

theorem pow2_delta {t : ℕ} {qs : List ℕ} (h2 : isPow2 t = true) :
    delta t qs = sumErr (1 / 2) (caps qs) := by
  simp [delta, h2]

/-- `Challenge.BFVDecrypt.floatSum_err_pow2`. -/
theorem floatSum_err_pow2 (A : ArithD) (hA : ConformsD A) (t : ℕ) (qs xs : List ℕ)
    (hp : decParamsOK? t qs = true) (hx : Reduced qs xs) (h2 : isPow2 t = true)
    (hδ : delta t qs ≤ 1 / 2) :
    |floatSum A.base (1 / 2) (allWords qs (tables A.base t qs) xs) - (1 / 2 + exactFrac t qs xs)|
        ≤ delta t qs ∧
      0 ≤ floatSum A.base (1 / 2) (allWords qs (tables A.base t qs) xs) ∧
      floatSum A.base (1 / 2) (allWords qs (tables A.base t qs) xs) < 2 ^ 64 := by
  rw [pow2_delta h2] at hδ ⊢
  obtain ⟨k1, k2, _⟩ := sum_err A.base hA.base t qs xs hp hx (1 / 2) (Or.inr rfl) (by linarith)
  refine ⟨k1, k2, ?_⟩
  have hcs := sumErr_caps (by norm_num) (show sumErr (1 / 2) (caps qs) ≤ 1 by linarith)
  have hF : exactFrac t qs xs ≤ (((caps qs).sum : ℕ) : ℚ) := by
    rw [exactFrac_eq, ← caps_eq t qs xs hx.length_eq]
    have := sum_map_le (spec t qs xs) val (fun d => ((cap d : ℕ) : ℚ))
      (fun d hd => val_le_cap d (spec_dok hp hx d hd))
    have e : (((spec t qs xs).map cap).sum : ℚ) = ((spec t qs xs).map fun d => ((cap d : ℕ) : ℚ)).sum := by
      push_cast [List.map_map]; rfl
    rw [e]; exact this
  have := (abs_le.mp k1).2
  linarith [show (2 : ℚ) ^ 51 + 2 < 2 ^ 64 by norm_num]

end Validation.BFVDecrypt
