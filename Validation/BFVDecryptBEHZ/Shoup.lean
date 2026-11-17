import Challenge.BFVDecryptBEHZ
import Validation.BFVDecryptLow.Words

/-!
# Validation.BFVDecryptBEHZ.Shoup — `ModMulFastConst` with the signed fix-up
-/

namespace Validation.BFVDecryptBEHZ
open Spec.DecryptBFV Spec.DecryptBFVLow Spec.DecryptBFVBEHZ Challenge.BFVDecryptBEHZ
open Validation.BFVDecryptLow (subFast_of_le subFast_of_lt addFast_of_lt mulFast_of_lt)

/-- `subFast` of two 64-bit words is the difference modulo `2⁶⁴`. -/
theorem subFast_int (u w : ℕ) (hu : u < 2 ^ 64) (hw : w < 2 ^ 64) :
    (subFast u w : ℤ) = ((u : ℤ) - w) % 2 ^ 64 := by
  by_cases h : w ≤ u
  · rw [subFast_of_le h hu, Int.emod_eq_of_lt (by omega) (by omega)]; push_cast [h]; ring
  · push Not at h
    rw [subFast_of_lt h hw]
    rw [show ((u : ℤ) - w) = ((u + 2 ^ 64 - w : ℕ) : ℤ) + (-1) * 2 ^ 64 by omega,
      Int.add_mul_emod_self_right, Int.emod_eq_of_lt (by omega) (by omega)]

theorem modMulFastConst_spec (a b m : ℕ) (ha : a < 2 ^ 64) (hb : b < m) (hm : 2 ≤ m)
    (hm' : m < 2 ^ 63) : modMulFastConst a b m (prepModMulConst b m) = a * b % m := by
  have hm0 : 0 < m := by omega
  -- the precomputation
  set bInv := b * 2 ^ 64 / m with hbInv
  have hp : prepModMulConst b m = bInv := by
    unfold prepModMulConst divD
    rw [add_zero]
    apply Nat.mod_eq_of_lt
    rw [Nat.div_lt_iff_lt_mul hm0, mul_comm (2 ^ 64)]
    exact Nat.mul_lt_mul_of_pos_right hb (Nat.two_pow_pos 64)
  rw [hp]
  have hb1 : bInv * m ≤ b * 2 ^ 64 := Nat.div_mul_le_self _ _
  have hb2 : b * 2 ^ 64 < (bInv + 1) * m := by
    have := Nat.lt_div_mul_add (a := b * 2 ^ 64) hm0
    rw [add_mul, one_mul]; exact this
  set Qt := a * b / m with hQt
  set M := a * bInv / 2 ^ 64 with hM
  have hM1 : M * 2 ^ 64 ≤ a * bInv := Nat.div_mul_le_self _ _
  have hM2 : a * bInv < (M + 1) * 2 ^ 64 := by
    have := Nat.lt_div_mul_add (a := a * bInv) (by positivity : 0 < 2 ^ 64)
    rw [add_mul, one_mul]; exact this
  have hQ1 : Qt * m ≤ a * b := Nat.div_mul_le_self _ _
  have hQ2 : a * b < (Qt + 1) * m := by
    have := Nat.lt_div_mul_add (a := a * b) hm0
    rw [add_mul, one_mul]; exact this
  -- `M ≤ Qt`
  have hMle : M ≤ Qt := by
    have h1 : M * m * 2 ^ 64 ≤ a * b * 2 ^ 64 := by
      calc M * m * 2 ^ 64 = M * 2 ^ 64 * m := by ring
        _ ≤ a * bInv * m := Nat.mul_le_mul_right _ hM1
        _ = a * (bInv * m) := by ring
        _ ≤ a * (b * 2 ^ 64) := Nat.mul_le_mul_left _ hb1
        _ = a * b * 2 ^ 64 := by ring
    have h2 : M * m ≤ a * b := Nat.le_of_mul_le_mul_right h1 (by positivity)
    exact (Nat.le_div_iff_mul_le hm0).mpr h2
  -- `Qt ≤ M + 1`
  have hMge : Qt ≤ M + 1 := by
    have h1 : a * b * 2 ^ 64 < (M + 2) * m * 2 ^ 64 := by
      have e1 : a * (b * 2 ^ 64) ≤ a * ((bInv + 1) * m) := Nat.mul_le_mul_left _ hb2.le
      have e2 : a * bInv * m < (M + 1) * 2 ^ 64 * m := Nat.mul_lt_mul_of_pos_right hM2 hm0
      have e3 : a * m < 2 ^ 64 * m := Nat.mul_lt_mul_of_pos_right ha hm0
      calc a * b * 2 ^ 64 = a * (b * 2 ^ 64) := by ring
        _ ≤ a * ((bInv + 1) * m) := e1
        _ = a * bInv * m + a * m := by ring
        _ < (M + 1) * 2 ^ 64 * m + 2 ^ 64 * m := Nat.add_lt_add e2 e3
        _ = (M + 2) * m * 2 ^ 64 := by ring
    have h2 : a * b < (M + 2) * m := Nat.lt_of_mul_lt_mul_right h1
    have : a * b / m < M + 2 := (Nat.div_lt_iff_lt_mul hm0).mpr h2
    omega
  -- `q = M + 1` does not wrap
  have hMa : M + 1 < 2 ^ 64 := by
    rcases Nat.eq_zero_or_pos a with h0 | h0
    · simp [hM, h0]
    · have e1 : a * b < a * m := Nat.mul_lt_mul_of_pos_left hb h0
      have e2 : Qt * m < a * m := lt_of_le_of_lt hQ1 e1
      have := Nat.lt_of_mul_lt_mul_right e2
      omega
  have hq : addFast (multDHi a bInv) 1 = M + 1 := by
    unfold multDHi; rw [← hM]; exact addFast_of_lt hMa
  unfold modMulFastConst
  simp only
  rw [hq]
  set y := subFast (mulFast a b) (mulFast (M + 1) m) with hy
  -- y as an integer
  have hyI : (y : ℤ) = ((a * b : ℤ) - (M + 1) * m) % 2 ^ 64 := by
    rw [hy, subFast_int _ _ (by unfold mulFast; exact Nat.mod_lt _ (by norm_num))
      (by unfold mulFast; exact Nat.mod_lt _ (by norm_num))]
    unfold mulFast
    push_cast
    rw [Int.sub_emod, Int.emod_emod_of_dvd _ (dvd_refl _), Int.emod_emod_of_dvd _ (dvd_refl _),
      ← Int.sub_emod]
  have hdm := Nat.div_add_mod (a * b) m
  have hmodlt := Nat.mod_lt (a * b) hm0
  obtain ⟨R, hR⟩ : ∃ R, R = a * b % m := ⟨_, rfl⟩
  have hRlt : R < m := by rw [hR]; exact Nat.mod_lt _ hm0
  have h1 : (a : ℤ) * b = (Qt : ℤ) * m + R := by
    have : a * b = Qt * m + R := by rw [hR, hQt]; exact (Nat.div_add_mod' (a * b) m).symm
    exact_mod_cast this
  rw [← hR]
  rcases Nat.lt_or_ge M Qt with hlt | hge
  · -- q = Qt: the difference is `a·b mod m ≥ 0`
    have hMq' : M + 1 = Qt := by omega
    have hMq : (M : ℤ) + 1 = Qt := by exact_mod_cast hMq'
    have hD : ((a * b : ℤ) - (M + 1) * m) = (R : ℤ) := by rw [hMq]; linarith
    rw [hD, Int.emod_eq_of_lt (by omega) (by omega)] at hyI
    have hyv : y = R := by exact_mod_cast hyI
    rw [if_pos (by omega), hyv]
  · -- q = Qt + 1: the difference is `a·b mod m − m < 0`
    have hMq' : M = Qt := by omega
    have hMq : (M : ℤ) = Qt := by exact_mod_cast hMq'
    have hD : ((a * b : ℤ) - (M + 1) * m) = ((R + (2 ^ 64 - m) : ℕ) : ℤ) + (-1) * 2 ^ 64 := by
      rw [hMq, Nat.cast_add, Nat.cast_sub (by omega)]; push_cast; linarith
    rw [hD, Int.add_mul_emod_self_right, Int.emod_eq_of_lt (by omega) (by omega)] at hyI
    have hyv : y = R + (2 ^ 64 - m) := by exact_mod_cast hyI
    rw [if_neg (by omega), hyv, addFast]
    rw [show R + (2 ^ 64 - m) + m = R + 1 * 2 ^ 64 by omega,
      Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]

end Validation.BFVDecryptBEHZ
