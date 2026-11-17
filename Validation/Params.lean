import Spec.Params
import Mathlib.NumberTheory.LucasPrimality
import Mathlib.Tactic.NormNum.Prime

/-!
# Validation.Params — `ParamsOK FullParams.exampleBGV31`

No native evaluation; kernel arithmetic only. Large primes: Lucas certificates (`lucas_primality`) whose modular powers are
computed by a fuel-recursive square-and-multiply `powMod`, checked by `decide +kernel` (kernel
`Nat` arithmetic is GMP-accelerated). Small primes (factors of `p - 1`):
`norm_num`. Roots of unity: kernel `Nat` arithmetic on `ψ^N + 1 mod q`.
-/

namespace Validation.Params
open Spec Layout

/-- Square-and-multiply `b^e mod m`, structurally recursive on `fuel` (correct when
`e < 2^fuel`) so that the kernel can evaluate it. -/
def powMod : ℕ → ℕ → ℕ → ℕ → ℕ
  | 0, _, _, _ => 1
  | f + 1, b, e, m =>
    if e = 0 then 1 else
      let r := powMod f (b * b % m) (e / 2) m
      if e % 2 = 0 then r else r * b % m

theorem powMod_cast (m : ℕ) : ∀ (f b e : ℕ), e < 2 ^ f →
    ((powMod f b e m : ℕ) : ZMod m) = (b : ZMod m) ^ e
  | 0, b, e, he => by
    have : e = 0 := by simpa using he
    subst this; simp [powMod]
  | f + 1, b, e, he => by
    have hlt : e / 2 < 2 ^ f := by rw [pow_succ] at he; omega
    have ih := powMod_cast m f (b * b % m) (e / 2) hlt
    have key : (((b * b % m : ℕ)) : ZMod m) ^ (e / 2) = (b : ZMod m) ^ (2 * (e / 2)) := by
      rw [ZMod.natCast_mod, Nat.cast_mul, pow_mul, sq]
    by_cases h0 : e = 0
    · subst h0; simp [powMod]
    · simp only [powMod, h0, ite_false]
      by_cases h2 : e % 2 = 0
      · simp only [h2, ite_true]
        rw [ih, key]; congr 1; omega
      · simp only [h2, ite_false]
        rw [ZMod.natCast_mod, Nat.cast_mul, ih, key, ← pow_succ]; congr 1; omega

/-- A Lucas certificate with `p - 1 = 2^e · r₂ · r₃`. -/
theorem prime_of_cert (p a e r₂ r₃ : ℕ) (h₂ : r₂.Prime) (h₃ : r₃.Prime)
    (hp : p - 1 = 2 ^ e * r₂ * r₃) (hlt : p - 1 < 2 ^ 32) (hp1 : 1 < p)
    (ha : powMod 32 a (p - 1) p % p = 1)
    (hd₁ : powMod 32 a ((p - 1) / 2) p % p ≠ 1)
    (hd₂ : powMod 32 a ((p - 1) / r₂) p % p ≠ 1)
    (hd₃ : powMod 32 a ((p - 1) / r₃) p % p ≠ 1) : p.Prime := by
  have iff : ∀ n, n ≤ p - 1 → ((a : ZMod p) ^ n = 1 ↔ powMod 32 a n p % p = 1) := by
    intro n hn
    rw [← powMod_cast p 32 a n (by omega), ← Nat.cast_one, ZMod.natCast_eq_natCast_iff',
      Nat.mod_eq_of_lt hp1]
  refine lucas_primality p (a : ZMod p) ((iff _ le_rfl).2 ha) ?_
  intro r hr hdvd
  have hr' : r = 2 ∨ r = r₂ ∨ r = r₃ := by
    rw [hp] at hdvd
    rcases (Nat.Prime.dvd_mul hr).1 hdvd with h | h
    · rcases (Nat.Prime.dvd_mul hr).1 h with h | h
      · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 (hr.dvd_of_dvd_pow h))
      · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hr h₂).1 h))
    · exact Or.inr (Or.inr ((Nat.prime_dvd_prime_iff_eq hr h₃).1 h))
  rw [Ne, iff _ (Nat.div_le_self _ _)]
  rcases hr' with rfl | rfl | rfl <;> assumption

/-- `ψ^n = -1` in `ZMod q` from the kernel-checkable `(ψ^n + 1) % q = 0`. -/
theorem pow_eq_neg_one_of_mod {q ψ n : ℕ} (h : (ψ ^ n + 1) % q = 0) :
    (ψ : ZMod q) ^ n = -1 := by
  have : ((ψ ^ n + 1 : ℕ) : ZMod q) = 0 :=
    (ZMod.natCast_eq_zero_iff _ _).2 (Nat.dvd_of_mod_eq_zero h)
  push_cast at this
  exact eq_neg_of_add_eq_zero_left this

theorem prime_q0 : Nat.Prime 1073872897 :=
  prime_of_cert 1073872897 7 17 3 2731 (by norm_num) (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

theorem prime_q1 : Nat.Prime 1074266113 :=
  prime_of_cert 1074266113 5 19 3 683 (by norm_num) (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

theorem prime_p0 : Nat.Prime 1077477377 :=
  prime_of_cert 1077477377 3 16 41 401 (by norm_num) (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

theorem exampleBGV31_scheme : SchemeParamsOK FullParams.exampleBGV31 where
  N_pow2 := ⟨14, rfl⟩
  qs_nonempty := List.cons_ne_nil _ _
  prime := by
    simp only [FullParams.exampleBGV31, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq]
    exact ⟨prime_q0, prime_q1⟩
  distinct := by decide
  plaintext := by
    simp only [FullParams.exampleBGV31, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq]
    refine ⟨by decide, ?_, ?_⟩ <;> decide +kernel
  msgRange := fun _ => by decide

theorem exampleBGV31_ok : ParamsOK FullParams.exampleBGV31 := by
  refine
    { scheme := exampleBGV31_scheme
      W_pos := by decide
      W_dvd := ⟨2, rfl⟩
      limbs_match := rfl
      limbs_nonempty := by simp [FullParams.exampleBGV31]
      prime := ?_
      odd := ?_
      fits := ?_
      root := ?_
      distinct := ?_
      plaintext := ?_ }
  all_goals simp only [FullParams.allLimbs, FullParams.exampleBGV31, List.cons_append,
    List.nil_append, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  · exact ⟨prime_q0, prime_q1, prime_p0⟩
  · decide
  · decide
  · refine ⟨?_, ?_, ?_⟩ <;> apply pow_eq_neg_one_of_mod <;> decide +kernel
  · decide
  · refine ⟨by decide, ?_, ?_, ?_⟩ <;> decide +kernel

end Validation.Params
