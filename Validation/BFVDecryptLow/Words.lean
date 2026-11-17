import Challenge.BFVDecryptLow
import Mathlib.Data.Nat.Size

/-!
# Validation.BFVDecryptLow.Words — the lanes, the Barrett loop and the modulus switch
-/

namespace Validation.BFVDecryptLow
open Spec.DecryptBFV Spec.DecryptBFVLow Challenge.BFVDecryptLow

theorem subFast_of_le {a b : ℕ} (hb : b ≤ a) (ha : a < 2 ^ 64) : subFast a b = a - b := by
  unfold subFast
  rw [Nat.mod_eq_of_lt (lt_of_le_of_lt hb ha)]
  omega

theorem subFast_of_lt {a b : ℕ} (h : a < b) (hb : b < 2 ^ 64) : subFast a b = a + 2 ^ 64 - b := by
  unfold subFast
  rw [Nat.mod_eq_of_lt hb]
  omega

theorem addFast_of_lt {a b : ℕ} (h : a + b < 2 ^ 64) : addFast a b = a + b := by
  unfold addFast; exact Nat.mod_eq_of_lt h

theorem mulFast_of_lt {a b : ℕ} (h : a * b < 2 ^ 64) : mulFast a b = a * b := by
  unfold mulFast; exact Nat.mod_eq_of_lt h

theorem topBitMask_lo {x : ℕ} (h : x < 2 ^ 63) : topBitMask x = 0 := by
  unfold topBitMask rshift
  rw [Nat.div_eq_of_lt h]
  rfl

theorem topBitMask_hi {x : ℕ} (h1 : 2 ^ 63 ≤ x) (h2 : x < 2 ^ 64) : topBitMask x = 2 ^ 64 - 1 := by
  unfold topBitMask rshift
  have : x / 2 ^ 63 = 1 := Nat.div_eq_of_lt_le (by omega) (by omega)
  rw [this]
  rfl

theorem and_zero' (d : ℕ) : d &&& 0 = 0 := Nat.and_zero d

theorem and_ones {d : ℕ} (h : d < 2 ^ 64) : d &&& (2 ^ 64 - 1) = d := by
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt h]

/-- `centeredCorrectionLane` is the compare-select `v > halfQ ? diff : 0`. -/
theorem ccl_eq {v halfQ diff : ℕ} (hv : v < 2 ^ 63) (hh : halfQ < 2 ^ 63) (hd : diff < 2 ^ 64) :
    centeredCorrectionLane v halfQ diff = if v > halfQ then diff else 0 := by
  unfold centeredCorrectionLane
  split_ifs with h
  · rw [subFast_of_lt h (by omega), topBitMask_hi (by omega) (by omega), and_ones hd]
  · rw [subFast_of_le (by omega) (by omega), topBitMask_lo (by omega), and_zero']

/-- `modSubLane` is the compare-select `a − b (+ m if a < b)`. -/
theorem modSubLane_eq {a b m : ℕ} (ha : a < m) (hb : b < m) (hm : m < 2 ^ 63) :
    modSubLane a b m = if b ≤ a then a - b else a + m - b := by
  unfold modSubLane
  simp only
  split_ifs with h
  · rw [subFast_of_le h (by omega), topBitMask_lo (by omega), and_zero', addFast_of_lt (by omega)]
    omega
  · rw [subFast_of_lt (by omega) (by omega), topBitMask_hi (by omega) (by omega),
      and_ones (by omega)]
    unfold addFast
    rw [show a + 2 ^ 64 - b + m = (a + m - b) + 2 ^ 64 by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt (by omega)]

/-- `modSubLane` of reduced operands is the subtraction modulo `m`. -/
theorem modSubLane_spec {a b m : ℕ} (ha : a < m) (hb : b < m) (hm : m < 2 ^ 63) :
    (modSubLane a b m : ℤ) = ((a : ℤ) - b) % m := by
  rw [modSubLane_eq ha hb hm]
  split_ifs with h
  · rw [Int.emod_eq_of_lt (by omega) (by omega)]; omega
  · rw [show ((a : ℤ) - b) = ((a + m - b : ℕ) : ℤ) + (-1) * m by
        push_cast [Nat.cast_sub (show b ≤ a + m by omega)]; ring,
      Int.add_mul_emod_self_right, Int.emod_eq_of_lt (by omega) (by omega)]

/-! ### The Barrett branch of `GeneralShrinkLoop` -/

theorem msb_bounds {n : ℕ} (hn : 1 ≤ n) : 2 ^ (msb n - 1) ≤ n ∧ n < 2 ^ msb n := by
  unfold msb
  refine ⟨?_, Nat.lt_size_self n⟩
  have hs : 1 ≤ Nat.size n := Nat.size_pos.mpr (by omega)
  exact Nat.lt_size.mp (by omega)

/-- The Barrett quotient estimate is the true quotient or one less. -/
theorem barrett (v nv e : ℕ) (hv : v < 2 ^ 64) (he : 1 ≤ e) (h1 : 2 ^ (e + 1) ≤ nv) :
    let mu := 2 ^ (64 + e) / nv
    let q := v * mu / 2 ^ 64 / 2 ^ e
    q * nv ≤ v ∧ v < (q + 2) * nv := by
  intro mu q
  have hnv : 0 < nv := lt_of_lt_of_le (by positivity) h1
  have hq : q = v * mu / 2 ^ (64 + e) := by
    show v * mu / 2 ^ 64 / 2 ^ e = _
    rw [Nat.div_div_eq_div_mul, ← pow_add]
  have hP : (0 : ℕ) < 2 ^ (64 + e) := by positivity
  have hmu1 : mu * nv ≤ 2 ^ (64 + e) := Nat.div_mul_le_self _ _
  have hmu2 : 2 ^ (64 + e) < (mu + 1) * nv := by
    have := Nat.lt_div_mul_add (a := 2 ^ (64 + e)) hnv
    show 2 ^ (64 + e) < (2 ^ (64 + e) / nv + 1) * nv
    rw [add_mul, one_mul]; exact this
  constructor
  · rw [hq]
    have h3 : v * mu / 2 ^ (64 + e) * 2 ^ (64 + e) ≤ v * mu := Nat.div_mul_le_self _ _
    have h4 : v * mu / 2 ^ (64 + e) * nv * 2 ^ (64 + e) ≤ v * 2 ^ (64 + e) := by
      calc v * mu / 2 ^ (64 + e) * nv * 2 ^ (64 + e)
          = v * mu / 2 ^ (64 + e) * 2 ^ (64 + e) * nv := by ring
        _ ≤ v * mu * nv := Nat.mul_le_mul_right _ h3
        _ = v * (mu * nv) := by ring
        _ ≤ v * 2 ^ (64 + e) := Nat.mul_le_mul_left _ hmu1
    exact Nat.le_of_mul_le_mul_right h4 hP
  · rw [hq]
    set Q := v * mu / 2 ^ (64 + e)
    have h3 : v * mu < (Q + 1) * 2 ^ (64 + e) := by
      have := Nat.lt_div_mul_add (a := v * mu) hP
      rw [add_mul, one_mul]; exact this
    -- v·2^(64+e) < v·(mu+1)·nv = v·mu·nv + v·nv < (Q+1)·2^(64+e)·nv + 2^64·nv
    have h5 : v * 2 ^ (64 + e) < (Q + 1) * 2 ^ (64 + e) * nv + 2 ^ 64 * nv := by
      have a1 : v * 2 ^ (64 + e) ≤ v * ((mu + 1) * nv) := Nat.mul_le_mul_left _ hmu2.le
      have a2 : v * mu * nv < (Q + 1) * 2 ^ (64 + e) * nv := Nat.mul_lt_mul_of_pos_right h3 hnv
      have a3 : v * nv < 2 ^ 64 * nv := Nat.mul_lt_mul_of_pos_right hv hnv
      calc v * 2 ^ (64 + e) ≤ v * ((mu + 1) * nv) := a1
        _ = v * mu * nv + v * nv := by ring
        _ < (Q + 1) * 2 ^ (64 + e) * nv + 2 ^ 64 * nv := Nat.add_lt_add a2 a3
    -- 2^64·nv ≤ 2^(64+e)·nv / 2 ≤ 2^(64+e) * nv (as e ≥ 1): so v < (Q+1)·nv + nv
    have h6 : 2 ^ 64 * nv ≤ 2 ^ (64 + e) * nv := by
      apply Nat.mul_le_mul_right
      exact Nat.pow_le_pow_right (by norm_num) (by omega)
    have h7 : v * 2 ^ (64 + e) < (Q + 2) * nv * 2 ^ (64 + e) := by
      calc v * 2 ^ (64 + e) < (Q + 1) * 2 ^ (64 + e) * nv + 2 ^ 64 * nv := h5
        _ ≤ (Q + 1) * 2 ^ (64 + e) * nv + 2 ^ (64 + e) * nv := Nat.add_le_add_left h6 _
        _ = (Q + 2) * nv * 2 ^ (64 + e) := by ring
    exact Nat.lt_of_mul_lt_mul_right h7

/-- `GeneralShrinkLoop` reduces: before the final lane, `av = v mod nv`. -/
theorem gs_eq (ov nv v : ℕ) (hv : v < 2 ^ 63) (hnv : 2 ≤ nv) (hnv' : nv < 2 ^ 63) :
    generalShrink ov nv v =
      modSubLane (v % nv) (centeredCorrectionLane v (rshift ov 1) (subFast ov nv % nv)) nv := by
  unfold generalShrink
  simp only
  split_ifs with h3 hge h4 hge' <;> congr 1
  · -- Barrett branch, two subtractions
    set e := msb nv - 2 with hedef
    obtain ⟨hb1, hb2⟩ := msb_bounds (n := nv) (by omega)
    have he : 1 ≤ e := by omega
    have he1 : 2 ^ (e + 1) ≤ nv := by
      rw [show e + 1 = msb nv - 1 by omega]; exact hb1
    have he62 : e ≤ 61 := by
      by_contra hc
      have : 2 ^ 63 ≤ 2 ^ (e + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have hl : lshift 1 e = 2 ^ e := by
      unfold lshift
      rw [one_mul, Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by norm_num) (by omega))]
    have hmu : divD (2 ^ e) 0 nv = 2 ^ (64 + e) / nv := by
      unfold divD
      rw [add_zero, ← pow_add, add_comm e 64]
      apply Nat.mod_eq_of_lt
      calc 2 ^ (64 + e) / nv ≤ 2 ^ (64 + e) / 2 ^ (e + 1) := Nat.div_le_div_left he1 (by positivity)
        _ = 2 ^ 63 := by
          rw [Nat.pow_div (by omega) (by norm_num)]; congr 1; omega
        _ < 2 ^ 64 := by norm_num
    obtain ⟨hq1, hq2⟩ := barrett v nv e (by omega) he he1
    rw [hl, hmu] at h4 ⊢
    unfold multDHi rshift at h4 ⊢
    set q := v * (2 ^ (64 + e) / nv) / 2 ^ 64 / 2 ^ e
    rw [mulFast_of_lt (by omega), subFast_of_le hq1 (by omega)] at h4 ⊢
    rw [subFast_of_le h4 (by omega)]
    have : v = (v - q * nv - nv) + (q + 1) * nv := by
      have := Nat.add_mul q 1 nv; omega
    conv_rhs => rw [this, Nat.add_mul_mod_self_right]
    rw [Nat.mod_eq_of_lt (by have := Nat.add_mul q 2 nv; omega)]
  · set e := msb nv - 2 with hedef
    obtain ⟨hb1, hb2⟩ := msb_bounds (n := nv) (by omega)
    have he : 1 ≤ e := by omega
    have he1 : 2 ^ (e + 1) ≤ nv := by
      rw [show e + 1 = msb nv - 1 by omega]; exact hb1
    have he62 : e ≤ 61 := by
      by_contra hc
      have : 2 ^ 63 ≤ 2 ^ (e + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have hl : lshift 1 e = 2 ^ e := by
      unfold lshift
      rw [one_mul, Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by norm_num) (by omega))]
    have hmu : divD (2 ^ e) 0 nv = 2 ^ (64 + e) / nv := by
      unfold divD
      rw [add_zero, ← pow_add, add_comm e 64]
      apply Nat.mod_eq_of_lt
      calc 2 ^ (64 + e) / nv ≤ 2 ^ (64 + e) / 2 ^ (e + 1) := Nat.div_le_div_left he1 (by positivity)
        _ = 2 ^ 63 := by
          rw [Nat.pow_div (by omega) (by norm_num)]; congr 1; omega
        _ < 2 ^ 64 := by norm_num
    obtain ⟨hq1, hq2⟩ := barrett v nv e (by omega) he he1
    rw [hl, hmu] at h4 ⊢
    unfold multDHi rshift at h4 ⊢
    set q := v * (2 ^ (64 + e) / nv) / 2 ^ 64 / 2 ^ e
    rw [mulFast_of_lt (by omega), subFast_of_le hq1 (by omega)] at h4 ⊢
    have : v = (v - q * nv) + q * nv := by omega
    conv_rhs => rw [this, Nat.add_mul_mod_self_right]
    rw [Nat.mod_eq_of_lt (by omega)]
  · exact (Nat.mod_eq_of_lt (by omega)).symm
  · exact (Nat.mod_eq_of_lt (by omega)).symm

theorem generalShrink_spec (ov nv v : ℕ) (hov : ov < 2 ^ 63) (hnv : 2 ≤ nv) (hnv2 : nv ≤ ov / 2)
    (hv : v ≤ ov) :
    (generalShrink ov nv v : ℤ) = centredOf ov v % nv := by
  have hcc := ccl_eq (v := v) (halfQ := rshift ov 1) (diff := subFast ov nv % nv) (by omega)
    (by unfold rshift; omega) (by have := Nat.mod_lt (subFast ov nv) (by omega : 0 < nv); omega)
  rw [gs_eq ov nv v (by omega) hnv (by omega), hcc]
  have hd : subFast ov nv % nv = ov % nv := by
    rw [subFast_of_le (by omega) (by omega)]
    conv_rhs => rw [show ov = (ov - nv) + 1 * nv by omega, Nat.add_mul_mod_self_right]
  rw [hd]
  have hr : rshift ov 1 = ov / 2 := by unfold rshift; norm_num
  rw [hr]
  unfold centredOf
  have hm1 := Nat.mod_lt v (by omega : 0 < nv)
  have hm2 := Nat.mod_lt ov (by omega : 0 < nv)
  split_ifs with h
  · rw [modSubLane_spec hm1 hm2 (by omega)]
    push_cast
    rw [Int.sub_emod, Int.emod_emod_of_dvd _ (dvd_refl _), Int.emod_emod_of_dvd _ (dvd_refl _),
      ← Int.sub_emod]
  · rw [modSubLane_spec hm1 (by omega) (by omega)]
    push_cast
    rw [sub_zero, Int.emod_emod_of_dvd _ (dvd_refl _)]

theorem switchModulus_spec (ov nv v : ℕ) (hov : 3 ≤ ov) (hov' : ov < 2 ^ 63) (hnv : 2 ≤ nv)
    (hnv' : nv < 2 ^ 63) (hv : v < ov ∨ (v = ov ∧ 2 * nv < ov)) :
    (switchModulus ov nv v : ℤ) = centredOf ov v % nv ∧ switchModulus ov nv v < nv := by
  have hv' : v ≤ ov := by rcases hv with h | h <;> omega
  have key : (switchModulus ov nv v : ℤ) = centredOf ov v % nv := by
    have hr : rshift ov 1 = ov / 2 := by unfold rshift; norm_num
    unfold switchModulus
    simp only [hr]
    split_ifs with h1 h2
    · have hvo : v < ov := by rcases hv with h | h <;> omega
      rw [show subFast nv ov = nv - ov from subFast_of_le h1.le (by omega),
        ccl_eq (by omega) (by omega) (by omega)]
      unfold centredOf
      split_ifs with h3
      · rw [addFast_of_lt (by omega)]
        rw [show ((v : ℤ) - ov) = ((v + (nv - ov) : ℕ) : ℤ) + (-1) * nv by
          push_cast [Nat.cast_sub h1.le]; ring, Int.add_mul_emod_self_right,
          Int.emod_eq_of_lt (by omega) (by omega)]
      · rw [addFast_of_lt (by omega), add_zero, Int.emod_eq_of_lt (by omega) (by omega)]
    · have hvo : v < ov := by rcases hv with h | h <;> omega
      rw [show subFast ov nv = ov - nv from subFast_of_le (by omega) (by omega),
        ccl_eq (by omega) (by omega) (by omega)]
      unfold centredOf
      split_ifs with h3
      · rw [subFast_of_le (by omega) (by omega)]
        rw [show ((v : ℤ) - ov) = ((v - (ov - nv) : ℕ) : ℤ) + (-1) * nv by
          push_cast [Nat.cast_sub (show ov - nv ≤ v by omega), Nat.cast_sub (show nv ≤ ov by omega)]
          ring, Int.add_mul_emod_self_right, Int.emod_eq_of_lt (by omega) (by omega)]
      · rw [subFast_of_le (by omega) (by omega), Nat.sub_zero,
          Int.emod_eq_of_lt (by omega) (by omega)]
    · exact generalShrink_spec ov nv v hov' hnv (by omega) hv'
  refine ⟨key, ?_⟩
  have h0 : 0 ≤ centredOf ov v % nv := Int.emod_nonneg _ (by omega)
  have h1 : centredOf ov v % nv < nv := Int.emod_lt_of_pos _ (by omega)
  omega

end Validation.BFVDecryptLow
