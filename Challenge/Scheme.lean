import Spec.Scheme

/-!
# Challenge.Scheme — pins for `Spec.Scheme`   (LOCKED statements; proofs live in `Validation/`)

Each pin checks a trusted definition against the textbook formula it is meant to capture. If
`bgvDecrypt`, `bfvDecrypt`, `phase` or `centeredPhase` were written wrong, one of these would be
false. The non-vacuity pins show that the validity predicates used as hypotheses of headline
theorems can be satisfied.
-/

namespace Challenge.Scheme
open Spec NPoly Scheme

variable {N : ℕ}

/-- Phase of a two-component ciphertext is `c₀ + c₁·s`. -/
theorem phase_two {q : ℕ} (s c₀ c₁ : Poly q N) : phase s [c₀, c₁] = c₀ + s * c₁ := sorry

/-- Phase of a three-component ciphertext is `c₀ + c₁·s + c₂·s²`. -/
theorem phase_three {q : ℕ} (s c₀ c₁ c₂ : Poly q N) :
    phase s [c₀, c₁, c₂] = c₀ + s * c₁ + (s * s) * c₂ := sorry

/-- Textbook BGV: `(m + t·e − a·s, a)` decrypts to `m` when `m + t·e` (with `m` centered) has
coefficients below `Q/2` in absolute value. -/
theorem bgv_decrypt_honest (t Q : ℕ) (s e : IntPoly N) (a : Poly Q N) (m : Poly t N)
    (hsmall : ∀ i, 2 * |(centered m).coeff i + (t : ℤ) * e.coeff i| < Q) :
    bgvDecrypt t s [ofInt Q (centered m + (t : ℤ) • e) - a * ofInt Q s, a] = m := sorry

/-- Textbook BFV: `(⌊Q/t⌋·m + e − a·s, a)` decrypts to `m` (with `m`'s representatives in
`[0, t)`) when `2·t·(|eᵢ| + t) < Q`. -/
theorem bfv_decrypt_honest (t Q : ℕ) (ht : 0 < t) (s e : IntPoly N) (a : Poly Q N) (m : Poly t N)
    (hsmall : ∀ i, 2 * (t : ℤ) * (|e.coeff i| + t) < Q) :
    bfvDecrypt t s
      [ofInt Q (⟨fun i => ((Q / t * (m.coeff i).val : ℕ) : ℤ)⟩ + e) - a * ofInt Q s, a] = m :=
  sorry

/-- BGV addition is sound at the level of the invariant. -/
theorem bgv_add_sound (t B B' Q : ℕ) (s : IntPoly N) (c₀ c₁ d₀ d₁ : Poly Q N) (m m' : Poly t N)
    (h : BGVEncrypts t B s [c₀, c₁] m) (h' : BGVEncrypts t B' s [d₀, d₁] m')
    (hQ : 2 * (B + B') < Q) :
    BGVEncrypts t (B + B') s [c₀ + d₀, c₁ + d₁] (m + m') := sorry

/-- BGV tensoring is sound at the level of the invariant (the `N·B·B'` bound is the standard
worst case for the negacyclic product). -/
theorem bgv_mul_sound (t B B' Q : ℕ) (s : IntPoly N) (c₀ c₁ d₀ d₁ : Poly Q N) (m m' : Poly t N)
    (h : BGVEncrypts t B s [c₀, c₁] m) (h' : BGVEncrypts t B' s [d₀, d₁] m')
    (hQ : 2 * (N * B * B') < Q) :
    BGVEncrypts t (N * B * B') s [c₀ * d₀, c₀ * d₁ + c₁ * d₀, c₁ * d₁] (m * m') := sorry

/-- Non-vacuity only: `KeyValid` is satisfiable for every key requirement and every secret. The
witness is the degenerate key `a = 0`, `b = factor · target(s)` (noise `0`), which hides nothing:
this statement says nothing about keys a library would generate, and nothing about security. -/
theorem keyValid_exists (kind : Kind) (t B : ℕ) (s : IntPoly N) (req : KeyReq N) :
    ∃ b a : Poly req.modulus N, KeyValid kind t B s req b a := sorry

/-- Non-vacuity: every message has a BGV encryption with noise at most `t/2 + 1`, under every
secret, for `Q > t + 2`. -/
theorem bgvEncrypts_exists (t Q : ℕ) (ht : 0 < t) (hQ : t + 2 < Q) (s : IntPoly N) (m : Poly t N) :
    ∃ ct : List (Poly Q N), ct.length = 2 ∧ BGVEncrypts t (t / 2 + 1) s ct m := sorry

end Challenge.Scheme
