import Challenge.Params
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.GroupTheory.OrderOfElement

/-!
# Validation.ParamsCheck — soundness of `Spec.paramsOK?` and its acceptance/rejection pins

Primality needs no certificate: `x^(2^k) = -1 (mod q)` with `q` odd forces every prime factor `r`
of `q` to be `≡ 1 (mod 2^(k+1))`; `noDivisorFrom` excludes such factors up to `√q`. At storage
level `x` is the limb's `ψ` (`2^k = N`); at scheme level (`primeOK?`) it is `a^((q-1)/2^e)` for a
quadratic non-residue `a`, `2^e = twoPart (q - 1)`.
Acceptance and rejection are by kernel evaluation (`decide +kernel`).
-/

namespace Validation.Params
open Spec Layout

private theorem powModCheck_cast (m : ℕ) : ∀ (f b e : ℕ), e < 2 ^ f →
    ((Spec.powMod f b e m : ℕ) : ZMod m) = (b : ZMod m) ^ e
  | 0, b, e, he => by
    have : e = 0 := by simpa using he
    subst this; simp [Spec.powMod, ZMod.natCast_mod]
  | f + 1, b, e, he => by
    have hlt : e / 2 < 2 ^ f := by rw [pow_succ] at he; omega
    have ih := powModCheck_cast m f (b * b % m) (e / 2) hlt
    have key : (((b * b % m : ℕ)) : ZMod m) ^ (e / 2) = (b : ZMod m) ^ (2 * (e / 2)) := by
      rw [ZMod.natCast_mod, Nat.cast_mul, pow_mul, sq]
    by_cases h0 : e = 0
    · subst h0; simp [Spec.powMod, ZMod.natCast_mod]
    · simp only [Spec.powMod, h0, ite_false]
      by_cases h2 : e % 2 = 0
      · simp only [h2, ite_true]
        rw [ih, key]; congr 1; omega
      · simp only [h2, ite_false]
        rw [ZMod.natCast_mod, Nat.cast_mul, ih, key, ← pow_succ]; congr 1; omega

private theorem noDivisorFrom_spec (q step : ℕ) : ∀ (f d : ℕ),
    noDivisorFrom q step f d = true →
    ∀ j, (d + j * step) * (d + j * step) ≤ q → ¬ (d + j * step) ∣ q
  | 0, d, h => by simp [noDivisorFrom] at h
  | f + 1, d, h => by
    intro j hj
    unfold noDivisorFrom at h
    by_cases h1 : q < d * d
    · exfalso
      have : d * d ≤ (d + j * step) * (d + j * step) :=
        Nat.mul_le_mul (Nat.le_add_right _ _) (Nat.le_add_right _ _)
      omega
    · simp only [h1, ↓reduceIte] at h
      by_cases h2 : q % d = 0
      · simp [h2] at h
      · simp only [h2, ↓reduceIte] at h
        cases j with
        | zero =>
          simp only [Nat.zero_mul, Nat.add_zero]
          exact fun hd => h2 (Nat.mod_eq_zero_of_dvd hd)
        | succ j =>
          have e : d + (j + 1) * step = (d + step) + j * step := by ring
          rw [e] at hj ⊢
          exact noDivisorFrom_spec q step f (d + step) h j hj

/-- Every prime factor of an odd `q` with `x^(2^k) = -1` in `ZMod q` is `≡ 1 (mod 2^(k+1))`. -/
private theorem prime_factor_mod (q k r : ℕ) (x : ZMod q) (hodd : q % 2 = 1)
    (hroot : x ^ (2 ^ k) = -1) (hr : r.Prime) (hrq : r ∣ q) :
    r % 2 ^ (k + 1) = 1 := by
  have : Fact r.Prime := ⟨hr⟩
  have hr2 : r ≠ 2 := by
    rintro rfl
    have := Nat.mod_eq_zero_of_dvd hrq
    omega
  obtain ⟨y, hy⟩ : ∃ y : ZMod r, y = ZMod.castHom hrq (ZMod r) x := ⟨_, rfl⟩
  have hx : y ^ (2 ^ k) = -1 := by
    have := congrArg (ZMod.castHom hrq (ZMod r)) hroot
    rwa [map_pow, map_neg, map_one, ← hy] at this
  have hne : ¬ y ^ (2 ^ k) = 1 := by
    intro h1
    rw [hx] at h1
    have h2 : ((2 : ℕ) : ZMod r) = 0 := by
      have : (1 : ZMod r) + 1 = 0 := by
        nth_rewrite 1 [← h1]; simp
      push_cast; rw [← this]; norm_num
    have hdvd := (ZMod.natCast_eq_zero_iff _ _).1 h2
    exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 hdvd)
  have hfin : y ^ (2 ^ (k + 1)) = 1 := by
    rw [pow_succ, pow_mul, hx]; norm_num
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hord : orderOf y = 2 ^ (k + 1) := orderOf_eq_prime_pow hne hfin
  have h0 : y ≠ 0 := by
    intro h0
    rw [h0, zero_pow (by positivity)] at hfin
    exact zero_ne_one hfin
  have hdvd : 2 ^ (k + 1) ∣ r - 1 := by
    rw [← hord]
    exact orderOf_dvd_of_pow_eq_one (ZMod.pow_card_sub_one_eq_one h0)
  obtain ⟨c, hc⟩ := hdvd
  have hr1 : r = 2 ^ (k + 1) * c + 1 := by have := hr.two_le; omega
  have h2k : 1 < 2 ^ (k + 1) := Nat.one_lt_two_pow (by omega)
  rw [hr1, Nat.mul_add_mod, Nat.mod_eq_of_lt h2k]

private theorem prime_of_check (q k M : ℕ) (x : ZMod q) (hM : M = 2 ^ (k + 1)) (h1 : 1 < q)
    (hodd : q % 2 = 1) (hroot : x ^ (2 ^ k) = -1)
    (hnd : noDivisorFrom q M q (M + 1) = true) : q.Prime := by
  by_contra hnp
  have hr : q.minFac.Prime := Nat.minFac_prime (by omega)
  have hrq : q.minFac ∣ q := Nat.minFac_dvd q
  have hmod := prime_factor_mod q k q.minFac x hodd hroot hr hrq
  have hsq : q.minFac ^ 2 ≤ q := Nat.minFac_sq_le_self (by omega) hnp
  rw [← hM] at hmod
  set r := q.minFac with hrdef
  have hMpos : 1 < M := by rw [hM]; exact Nat.one_lt_two_pow (by omega)
  have hdm := Nat.div_add_mod r M
  rw [hmod] at hdm
  have ha : 1 ≤ r / M := by
    rcases Nat.eq_zero_or_pos (r / M) with h | h
    · rw [h] at hdm; have := hr.two_le; omega
    · exact h
  have hrform : M + 1 + (r / M - 1) * M = r := by
    obtain ⟨a, haa⟩ : ∃ a, r / M = a + 1 := ⟨r / M - 1, by omega⟩
    rw [haa] at hdm ⊢
    rw [← hdm]; simp only [Nat.add_sub_cancel]; ring
  have := noDivisorFrom_spec q M q (M + 1) hnd (r / M - 1)
  rw [hrform] at this
  exact this (by rw [← sq]; exact hsq) hrq

private theorem twoPart_spec : ∀ (f n : ℕ), ∃ e, twoPart f n = 2 ^ e ∧ 2 ^ e ∣ n ∧
    (1 ≤ f → n ≠ 0 → n % 2 = 0 → 1 ≤ e)
  | 0, n => ⟨0, by simp [twoPart]⟩
  | f + 1, n => by
    by_cases h : n ≠ 0 ∧ n % 2 = 0
    · obtain ⟨e, he, hd, _⟩ := twoPart_spec f (n / 2)
      refine ⟨e + 1, ?_, ?_, fun _ _ _ => by omega⟩
      · rw [twoPart, ite_eq_left_of_eq_true _ _ (eq_true h), he, pow_succ, Nat.mul_comm]
      · have hn : n = n / 2 * 2 := by omega
        rw [pow_succ, hn]
        exact Nat.mul_dvd_mul hd (dvd_refl 2)
    · refine ⟨0, ?_, by simp, fun _ h1 h2 => absurd ⟨h1, h2⟩ h⟩
      rw [twoPart, ite_eq_right_of_eq_false _ _ (eq_false h), pow_zero]

private theorem primeOK_sound (q : ℕ) (h : primeOK? q = true) : q.Prime := by
  simp only [primeOK?, Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨h1, hodd⟩, ⟨a, _, hpow⟩⟩, hnd⟩ := h
  obtain ⟨e, hF, hdvd, hpos⟩ := twoPart_spec q (q - 1)
  have he : 1 ≤ e := hpos (by omega) (by omega) (by omega)
  obtain ⟨k, rfl⟩ : ∃ k, e = k + 1 := ⟨e - 1, by omega⟩
  obtain ⟨m, hm⟩ := hdvd
  have hhalf : (q - 1) / 2 = 2 ^ k * m := by
    rw [hm, pow_succ, Nat.mul_assoc, Nat.mul_comm 2 m, ← Nat.mul_assoc]
    exact Nat.mul_div_cancel _ (by omega)
  have hlt : (q - 1) / 2 < 2 ^ q :=
    lt_of_le_of_lt (by omega : (q - 1) / 2 ≤ q) Nat.lt_two_pow_self
  have hc := powModCheck_cast q q a ((q - 1) / 2) hlt
  rw [hpow, Nat.cast_sub (by omega), ZMod.natCast_self, hhalf, pow_mul'] at hc
  rw [hF] at hnd
  refine prime_of_check q k (2 ^ (k + 1)) ((a : ZMod q) ^ m) rfl h1 hodd ?_ hnd
  rw [← hc]; simp

private theorem limbOK_sound (k : ℕ) (lp : LimbParams) (h : limbOK? (2 ^ k) lp = true) :
    Nat.Prime lp.q ∧ lp.q % 2 = 1 ∧ lp.q < 2 ^ 32 ∧ (lp.ψ : ZMod lp.q) ^ (2 ^ k) = -1 := by
  simp only [limbOK?, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨h1, hlt⟩, hodd⟩, hpow⟩, hnd⟩ := h
  have hroot : (lp.ψ : ZMod lp.q) ^ (2 ^ k) = -1 := by
    have hN : 2 ^ k < 2 ^ (2 ^ k + 1) :=
      lt_trans Nat.lt_two_pow_self (Nat.pow_lt_pow_right (by omega) (by omega))
    have hc := powModCheck_cast lp.q (2 ^ k + 1) (lp.ψ % lp.q) (2 ^ k) hN
    rw [hpow, ZMod.natCast_mod, Nat.cast_sub (by omega), ZMod.natCast_self] at hc
    rw [← hc]; simp
  exact ⟨prime_of_check lp.q k (2 * 2 ^ k) (lp.ψ : ZMod lp.q) (by rw [pow_succ, Nat.mul_comm])
    h1 hodd hroot hnd, hodd, hlt, hroot⟩

/-- **Soundness of the scheme-level check**: whatever `schemeParamsOK?` accepts is valid at the
scheme level, whatever the size of its primes. -/
theorem schemeParamsOK?_sound (P : FullParams) (h : schemeParamsOK? P = true) :
    SchemeParamsOK P := by
  simp only [schemeParamsOK?, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    Bool.or_eq_true, beq_iff_eq, Bool.not_eq_true', bne_iff_ne, ne_eq] at h
  obtain ⟨⟨⟨⟨⟨hN, hne⟩, hprime⟩, hnodup⟩, hpt⟩, hmsg⟩ := h
  refine
    { N_pow2 := ⟨_, hN⟩
      qs_nonempty := ?_
      prime := fun q hq => primeOK_sound q (hprime q hq)
      distinct := hnodup
      plaintext := ?_
      msgRange := ?_ }
  · intro he; rw [he] at hne; simp at hne
  · exact ⟨hpt.1, fun q hq => hpt.2 q hq⟩
  · intro hk
    rcases hmsg with hc | hc
    · exact absurd hk hc
    · exact hc

/-- The scheme-level check accepts a 60-bit prime (so the noise headline applies there), and the
full check rejects the same parameters (they do not fit 32-bit words). -/
theorem schemeParamsOK?_wideBGV :
    schemeParamsOK? Challenge.Params.wideBGV = true ∧
      paramsOK? Challenge.Params.wideBGV = false := by
  have h : schemeParamsOK? Challenge.Params.wideBGV = true := by decide +kernel
  refine ⟨h, ?_⟩
  show (schemeParamsOK? Challenge.Params.wideBGV && _ && _ && _ && _ && _ && _ && _) = false
  rw [h]; decide +kernel

/-- **Soundness of the parameter check**: whatever `paramsOK?` accepts is valid. -/
theorem paramsOK?_sound (P : FullParams) (h : paramsOK? P = true) : ParamsOK P := by
  simp only [paramsOK?, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    Bool.or_eq_true, beq_iff_eq, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨hs, hW⟩, hWd⟩, hmatch⟩, hne⟩, hlimb⟩, hnodup⟩, hpt⟩ := h
  have hS := schemeParamsOK?_sound P hs
  obtain ⟨k, hN⟩ := hS.N_pow2
  have hl : ∀ lp ∈ P.allLimbs, Nat.Prime lp.q ∧ lp.q % 2 = 1 ∧ lp.q < 2 ^ 32 ∧
      (lp.ψ : ZMod lp.q) ^ P.src.N = -1 := by
    intro lp hlp
    have := hlimb lp hlp
    rw [hN] at this ⊢
    exact limbOK_sound _ lp this
  refine
    { scheme := hS
      W_pos := hW
      W_dvd := Nat.dvd_of_mod_eq_zero hWd
      limbs_match := hmatch
      limbs_nonempty := ?_
      prime := fun lp hlp => (hl lp hlp).1
      odd := fun lp hlp => (hl lp hlp).2.1
      fits := fun lp hlp => (hl lp hlp).2.2.1
      root := fun lp hlp => (hl lp hlp).2.2.2
      distinct := hnodup
      plaintext := ?_ }
  · intro he; rw [he] at hne; simp at hne
  · exact ⟨hS.plaintext.1, fun lp hlp => hpt lp hlp⟩

/-- The check accepts the 31-bit example instance. -/
theorem paramsOK?_exampleBGV31 : paramsOK? FullParams.exampleBGV31 = true := by decide +kernel

/-- A composite modulus is rejected even when it has a `ψ` with `ψ^N = -1`, at both levels. -/
theorem paramsOK?_rejects_composite :
    ((495 : ℕ) : ZMod 697) ^ 4 = -1 ∧ primeOK? 697 = false ∧ limbOK? 4 ⟨697, 495⟩ = false ∧
      schemeParamsOK? Challenge.Params.compositeParams = false ∧
      paramsOK? Challenge.Params.compositeParams = false := by
  refine ⟨?_, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩
  have h : ((495 ^ 4 + 1 : ℕ) : ZMod 697) = 0 :=
    (ZMod.natCast_eq_zero_iff _ _).2 (by decide +kernel)
  push_cast at h
  exact eq_neg_of_add_eq_zero_left h

/-- A `ψ` that is not a primitive `2N`-th root of unity is rejected (`ψ = 1`). -/
theorem paramsOK?_rejects_root :
    paramsOK? { FullParams.exampleBGV31 with
      store := { FullParams.exampleBGV31.store with
        limbs := [⟨1073872897, 1⟩, ⟨1074266113, 639594595⟩] } } = false := by decide +kernel

/-- An input noise bound below `t / 2` is rejected (`SchemeParamsOK.msgRange`), by both checks. -/
theorem paramsOK?_rejects_msgRange :
    schemeParamsOK? { FullParams.exampleBGV31 with inputNoise := 32767 } = false ∧
      paramsOK? { FullParams.exampleBGV31 with inputNoise := 32767 } = false := by
  constructor <;> decide +kernel

end Validation.Params
