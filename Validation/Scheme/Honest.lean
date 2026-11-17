import Validation.Scheme.Basic

/-!
# Validation.Scheme.Honest — honest encryptions decrypt correctly

Proofs of the pins `phase_two`, `phase_three`, `bgv_decrypt_honest` and `bfv_decrypt_honest` of
`Challenge.Scheme`.
-/

namespace Validation.Scheme
open Spec NPoly Scheme Validation.Ring

variable {N : ℕ}

/-- Phase of a two-component ciphertext is `c₀ + c₁·s`. -/
theorem phase_two {q : ℕ} (s c₀ c₁ : Poly q N) : phase s [c₀, c₁] = c₀ + s * c₁ :=
  phase_two' s c₀ c₁

/-- Phase of a three-component ciphertext is `c₀ + c₁·s + c₂·s²`. -/
theorem phase_three {q : ℕ} (s c₀ c₁ c₂ : Poly q N) :
    phase s [c₀, c₁, c₂] = c₀ + s * c₁ + (s * s) * c₂ :=
  phase_three' s c₀ c₁ c₂

/-- The phase of a fresh symmetric encryption `(v − a·s, a)` is `v`. -/
theorem phase_fresh {Q : ℕ} (s v : IntPoly N) (a : Poly Q N) :
    phase (ofInt Q s) [ofInt Q v - a * ofInt Q s, a] = ofInt Q v := by
  rw [phase_two']
  apply eq_of_neZero; intro; ring

theorem centeredPhase_fresh {Q : ℕ} (s v : IntPoly N) (a : Poly Q N)
    (hv : ∀ i, 2 * |v.coeff i| < Q) :
    centeredPhase s [ofInt Q v - a * ofInt Q s, a] = v := by
  rw [centeredPhase, phase_fresh, centered_ofInt v hv]

/-- Textbook BGV. -/
theorem bgv_decrypt_honest (t Q : ℕ) (s e : IntPoly N) (a : Poly Q N) (m : Poly t N)
    (hsmall : ∀ i, 2 * |(centered m).coeff i + (t : ℤ) * e.coeff i| < Q) :
    bgvDecrypt t s [ofInt Q (centered m + (t : ℤ) • e) - a * ofInt Q s, a] = m := by
  have hv : ∀ i, 2 * |(centered m + (t : ℤ) • e).coeff i| < Q := fun i => hsmall i
  rw [bgvDecrypt, centeredPhase_fresh _ _ _ hv]
  ext i
  show (((centered m).coeff i + (t : ℤ) * e.coeff i : ℤ) : ZMod t) = m.coeff i
  push_cast
  rw [ZMod.natCast_self, zero_mul, add_zero]
  exact ZMod.coe_valMinAbs _

/-- Rounding step of BFV decryption. -/
theorem roundDiv_bfv (t Q : ℕ) (ht : 0 < t) (mv : ℕ) (hm : mv < t) (e j : ℤ)
    (hsmall : 2 * (t : ℤ) * (|e| + t) < Q) :
    roundDiv (t * (((Q / t * mv : ℕ) : ℤ) + e + Q * j)) Q = mv + t * j := by
  unfold roundDiv
  have hQ : (0 : ℤ) < Q := by nlinarith [abs_nonneg e]
  -- `t·⌊Q/t⌋ = Q - r` with `0 ≤ r < t`.
  have hdiv := Nat.div_add_mod Q t
  have hr := Nat.mod_lt Q ht
  set D := Q / t
  set r := Q % t
  have hD : (t : ℤ) * D = Q - r := by
    have : ((t * D + r : ℕ) : ℤ) = Q := by exact_mod_cast hdiv
    push_cast at this; linarith
  have hrz : (r : ℤ) < t := by exact_mod_cast hr
  have hmz : (mv : ℤ) < t := by exact_mod_cast hm
  have hm0 : (0 : ℤ) ≤ mv := by positivity
  have hr0 : (0 : ℤ) ≤ r := by positivity
  have hrm : (r : ℤ) * mv ≤ t * t := by nlinarith
  have hte : |(t : ℤ) * e| ≤ t * |e| := by rw [abs_mul, abs_of_nonneg (by positivity)]
  have h1 := neg_abs_le ((t : ℤ) * e)
  have h2 := le_abs_self ((t : ℤ) * e)
  set X : ℤ := Q - 2 * r * mv + 2 * t * e
  have hX0 : 0 ≤ X := by nlinarith
  have hX1 : X < 2 * Q := by nlinarith
  have heq : 2 * ((t : ℤ) * (((D * mv : ℕ) : ℤ) + e + Q * j)) + Q
      = X + 2 * Q * (mv + t * j) := by
    push_cast
    have : (t : ℤ) * (D * mv) = (Q - r) * mv := by rw [← mul_assoc, hD]
    linear_combination 2 * this
  rw [heq, Int.add_mul_ediv_left _ _ (by positivity), Int.ediv_eq_zero_of_lt hX0 hX1, zero_add]

/-- Textbook BFV. -/
theorem bfv_decrypt_honest (t Q : ℕ) (ht : 0 < t) (s e : IntPoly N) (a : Poly Q N) (m : Poly t N)
    (hsmall : ∀ i, 2 * (t : ℤ) * (|e.coeff i| + t) < Q) :
    bfvDecrypt t s
      [ofInt Q (⟨fun i => ((Q / t * (m.coeff i).val : ℕ) : ℤ)⟩ + e) - a * ofInt Q s, a] = m := by
  have : NeZero t := ⟨ht.ne'⟩
  ext i
  simp only [bfvDecrypt, centeredPhase, phase_fresh, coeff_centered, coeff_ofInt, coeff_add']
  set v : ℤ := ((Q / t * (m.coeff i).val : ℕ) : ℤ) + e.coeff i
  obtain ⟨j, hj⟩ := exists_eq_add_mul_of_cast_eq (Q := Q)
    (a := ((v : ZMod Q)).valMinAbs) (b := v) (ZMod.coe_valMinAbs _)
  rw [hj, roundDiv_bfv t Q ht _ (ZMod.val_lt _) _ _ (hsmall i)]
  push_cast
  rw [ZMod.natCast_self, zero_mul, add_zero, ZMod.natCast_zmod_val]

end Validation.Scheme
