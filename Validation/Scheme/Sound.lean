import Validation.Scheme.Basic

/-!
# Validation.Scheme.Sound — BGV soundness and non-vacuity pins of `Challenge.Scheme`
-/

namespace Validation.Scheme
open Spec NPoly Scheme Validation.Ring

variable {N : ℕ}

/-- BGV addition is sound at the level of the invariant. -/
theorem bgv_add_sound (t B B' Q : ℕ) (s : IntPoly N) (c₀ c₁ d₀ d₁ : Poly Q N) (m m' : Poly t N)
    (h : BGVEncrypts t B s [c₀, c₁] m) (h' : BGVEncrypts t B' s [d₀, d₁] m')
    (hQ : 2 * (B + B') < Q) :
    BGVEncrypts t (B + B') s [c₀ + d₀, c₁ + d₁] (m + m') :=
  bgvEncrypts_zipWith_add (c := [c₀, c₁]) (d := [d₀, d₁]) rfl h h' hQ

/-- BGV tensoring is sound at the level of the invariant (the `N·B·B'` bound is the standard
worst case for the negacyclic product). -/
theorem bgv_mul_sound (t B B' Q : ℕ) (s : IntPoly N) (c₀ c₁ d₀ d₁ : Poly Q N) (m m' : Poly t N)
    (h : BGVEncrypts t B s [c₀, c₁] m) (h' : BGVEncrypts t B' s [d₀, d₁] m')
    (hQ : 2 * (N * B * B') < Q) :
    BGVEncrypts t (N * B * B') s [c₀ * d₀, c₀ * d₁ + c₁ * d₀, c₁ * d₁] (m * m') :=
  bgvEncrypts_tensor h h' hQ

/-- Non-vacuity: every key requirement has a valid key, for every secret. -/
theorem keyValid_exists (kind : Kind) (t B : ℕ) (s : IntPoly N) (req : KeyReq N) :
    ∃ b a : Poly req.modulus N, KeyValid kind t B s req b a := by
  refine ⟨req.factor * ofInt req.modulus (req.target.eval s), 0, ?_⟩
  have he : centered (req.factor * ofInt req.modulus (req.target.eval s) +
      0 * ofInt req.modulus s - req.factor * ofInt req.modulus (req.target.eval s)) = 0 := by
    have : req.factor * ofInt req.modulus (req.target.eval s) +
        0 * ofInt req.modulus s - req.factor * ofInt req.modulus (req.target.eval s) = 0 := by
      apply eq_of_neZero; intro; ring
    rw [this, centered_zero]
  refine ⟨?_, fun _ i => ?_⟩
  · show normInf (centered _) ≤ B
    rw [he, normInf_zero]; exact Nat.zero_le _
  · show (t : ℤ) ∣ (centered _).coeff i
    rw [he]; exact dvd_zero _

/-- Non-vacuity: every message has a BGV encryption with noise at most `t/2 + 1`, under every
secret, for `Q > t + 2`. -/
theorem bgvEncrypts_exists (t Q : ℕ) (ht : 0 < t) (hQ : t + 2 < Q) (s : IntPoly N) (m : Poly t N) :
    ∃ ct : List (Poly Q N), ct.length = 2 ∧ BGVEncrypts t (t / 2 + 1) s ct m := by
  have : NeZero t := ⟨ht.ne'⟩
  refine ⟨[ofInt Q (centered m), 0], rfl, ?_⟩
  refine bgvEncrypts_of_phase (centered m) ?_ ?_ (by omega) (ofInt_centered m)
  · rw [phase_two']
    apply eq_of_neZero; intro; ring
  · intro i
    rw [coeff_centered, ← Int.natCast_natAbs]
    have := ZMod.natAbs_valMinAbs_le (m.coeff i)
    exact_mod_cast (by omega : (m.coeff i).valMinAbs.natAbs ≤ t / 2 + 1)

end Validation.Scheme
