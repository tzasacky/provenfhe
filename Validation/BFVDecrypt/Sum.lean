import FHE.Float.Sum
import Spec.DecryptBFV

/-!
# Validation.BFVDecrypt.Sum — the binary64 sum of OpenFHE's BFV decryption

`floatSum` of `Spec.DecryptBFV` over a list of words, each given by a datum
`(word, integer table entry, numerator, modulus, cap)`: for every conforming arithmetic, the
computed sum is within `sumErr start caps` of `start + Σ word·numerator/modulus` (`fold_err'`),
from any start in `[0, 2⁸⁰]`. Unlike `FHE.Float.fold_err` the state may start at `0` (the
non-power-of-two paths), and the error of each step is charged to the cap of its word rather
than to its modulus (the split paths).
-/

namespace Validation.BFVDecrypt
open Spec.Float Spec.DecryptBFV FHE.Float

/-- A word datum: `(word, integer table entry, numerator, modulus, cap)`. -/
abbrev D := ℕ × ℕ × ℕ × ℕ × ℕ

/-- The exact term of a word: `word · numerator / modulus`. -/
def val (d : D) : ℚ := (d.1 : ℚ) * (d.2.2.1 : ℚ) / (d.2.2.2.1 : ℚ)

/-- The cap of a word. -/
def cap (d : D) : ℕ := d.2.2.2.2

/-- What the analysis needs of a datum. -/
def DOK (d : D) : Prop :=
  d.1 < d.2.2.2.2 ∧ d.2.2.1 < d.2.2.2.1 ∧ 1 ≤ d.2.2.2.1 ∧ d.2.2.2.1 < 2 ^ 60 ∧ d.2.2.2.2 ≤ 2 ^ 60

/-- The step function of `floatSum` on a datum. -/
def stepD (A : Arith) (s : ℚ) (d : D) : ℚ := A.mulAdd s (A.ofNat d.1) (frac A d.2.2.1 d.2.2.2.1)

theorem val_nonneg (d : D) : 0 ≤ val d := by unfold val; positivity

theorem val_le (d : D) (hd : DOK d) : val d ≤ d.1 := by
  obtain ⟨_, h2, h3, _, _⟩ := hd
  unfold val
  have hq : (1 : ℚ) ≤ d.2.2.2.1 := by exact_mod_cast h3
  have hn : (d.2.2.1 : ℚ) ≤ d.2.2.2.1 := by exact_mod_cast h2.le
  rw [div_le_iff₀ (by linarith)]
  exact mul_le_mul_of_nonneg_left hn (by positivity)

theorem val_le_cap (d : D) (hd : DOK d) : val d ≤ cap d := by
  have := val_le d hd
  have h1 : (d.1 : ℚ) ≤ d.2.2.2.2 := by exact_mod_cast hd.1.le
  unfold cap; linarith

/-- A nonzero term is at least `2⁻⁶⁰`. -/
theorem val_pos (d : D) (hd : DOK d) : val d = 0 ∨ 1 / 2 ^ 60 ≤ val d := by
  obtain ⟨_, _, h3, h4, _⟩ := hd
  rcases Nat.eq_zero_or_pos d.1 with h | h
  · left; unfold val; rw [h]; simp
  rcases Nat.eq_zero_or_pos d.2.2.1 with h' | h'
  · left; unfold val; rw [h']; simp
  right
  unfold val
  have hx : (1 : ℚ) ≤ d.1 := by exact_mod_cast h
  have hn : (1 : ℚ) ≤ d.2.2.1 := by exact_mod_cast h'
  have hq : (0 : ℚ) < d.2.2.2.1 := by exact_mod_cast (show 0 < d.2.2.2.1 by omega)
  have hq' : (d.2.2.2.1 : ℚ) ≤ 2 ^ 60 := by exact_mod_cast h4.le
  rw [div_le_div_iff₀ (by positivity) hq]
  nlinarith

/-- The two forms of a term (product rounded, or exact product for a fused multiply-add) both
approximate `val` with relative error `eta5`. -/
theorem term (A : Arith) (hA : Conforms A) (d : D) (hd : DOK d) :
    Approx eta5 (val d) (A.ofNat d.1 * frac A d.2.2.1 d.2.2.2.1) ∧
      Approx eta5 (val d) (A.mul (A.ofNat d.1) (frac A d.2.2.1 d.2.2.2.1)) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hd
  set x := d.1
  set n := d.2.2.1
  set m := d.2.2.2.1
  have hm64 : m < 2 ^ 64 := lt_trans h4 (by norm_num)
  have hx64 : x < 2 ^ 64 := by omega
  have hn64 : n < 2 ^ 64 := by omega
  have hmQ : (1 : ℚ) ≤ m := by exact_mod_cast h3
  have hnQ0 : (0 : ℚ) ≤ n := Nat.cast_nonneg _
  have hnQ : (n : ℚ) < m := by exact_mod_cast h2
  have hxQ0 : (0 : ℚ) ≤ x := Nat.cast_nonneg _
  have hxQ : (x : ℚ) < 2 ^ 64 := by exact_mod_cast hx64
  obtain ⟨hm127, _⟩ := one_div_pow_le h3 hm64
  have ham : Approx u m (A.ofNat m) := approx_of_rounds (hA.ofNat m hm64)
  have ham0 : A.ofNat m ≠ 0 := by
    have := (ham.bounds (by unfold u; norm_num) (by linarith)).1
    intro h; rw [h] at this; linarith
  have han : Approx u n (A.ofNat n) := approx_of_rounds (hA.ofNat n hn64)
  have hq0 : Approx f0 ((n : ℚ) / (m : ℚ)) (A.ofNat n / A.ofNat m) := by
    have := han.div ham u_lt
    refine this.mono (le_of_eq ?_)
    unfold f0 eInv; ring
  have hf0 : (0 : ℚ) ≤ (n : ℚ) / (m : ℚ) := div_nonneg hnQ0 (by linarith)
  have hf1 : (n : ℚ) / (m : ℚ) ≤ 1 := by rw [div_le_one (by linarith)]; exact hnQ.le
  have hfr : (n : ℚ) / (m : ℚ) = 0 ∨
      ((1 : ℚ) / 2 ^ 127 ≤ (n : ℚ) / (m : ℚ) ∧ (n : ℚ) / (m : ℚ) ≤ 2 ^ 127) := by
    rcases Nat.eq_zero_or_pos n with h | h
    · left; rw [h]; simp
    · right
      have hn1 : (1 : ℚ) ≤ n := by exact_mod_cast h
      refine ⟨hm127.trans ?_, hf1.trans (by norm_num)⟩
      exact div_le_div_of_nonneg_right hn1 (by linarith)
  have hin1 : InRange (A.ofNat n / A.ofNat m) := hq0.inRange f0_bound.2 hfr
  have hF : Approx f1 ((n : ℚ) / (m : ℚ)) (frac A n m) := hq0.rounds (hA.div _ _ ham0 hin1)
  have hcx : Approx u x (A.ofNat x) := approx_of_rounds (hA.ofNat x hx64)
  have hval : (x : ℚ) * ((n : ℚ) / (m : ℚ)) = val d := by unfold val; ring
  have hFx : Approx f2 (val d) (A.ofNat x * frac A n m) := by
    have := hcx.mul hF
    rw [hval] at this
    refine this.mono (le_of_eq ?_)
    unfold f2; ring
  have hv0 : 0 ≤ val d := val_nonneg d
  have hvr : val d = 0 ∨ ((1 : ℚ) / 2 ^ 127 ≤ val d ∧ val d ≤ 2 ^ 127) := by
    rcases val_pos d ⟨h1, h2, h3, h4, h5⟩ with h | h
    · exact Or.inl h
    · right
      refine ⟨le_trans (by norm_num) h, ?_⟩
      have := val_le d ⟨h1, h2, h3, h4, h5⟩
      have : (x : ℚ) ≤ 2 ^ 127 := by linarith [show (2 : ℚ) ^ 64 ≤ 2 ^ 127 by norm_num]
      linarith
  have hin2 : InRange (A.ofNat x * frac A n m) := hFx.inRange f2_bound.2 hvr
  have hm' : Approx eta5 (val d) (A.mul (A.ofNat x) (frac A n m)) :=
    hFx.rounds (hA.mul _ _ hin2)
  refine ⟨hFx.mono ?_, hm'⟩
  have := f2_bound.1
  unfold eta5
  nlinarith [u_pos]

/-- One step: `stepD A s d = (s + τ)·(1 + δ)` with `τ` within `eta5·val` of `val`, and `τ` zero
or at least `2⁻⁶¹`. -/
theorem dstep (A : Arith) (hA : Conforms A) (d : D) (hd : DOK d) (s : ℚ) (hs0 : 0 ≤ s)
    (hsW : s ≤ 2 ^ 100) (hs : s = 0 ∨ 1 / 2 ^ 63 ≤ s) :
    ∃ τ δ : ℚ, |δ| ≤ u ∧ 0 ≤ τ ∧ |τ - val d| ≤ eta5 * val d ∧ (τ = 0 ∨ 1 / 2 ^ 61 ≤ τ) ∧
      stepD A s d = (s + τ) * (1 + δ) := by
  obtain ⟨h1, h2⟩ := term A hA d hd
  have hv0 := val_nonneg d
  have hvc := val_le d hd
  have hx64 : (d.1 : ℚ) ≤ 2 ^ 60 := by
    have : d.1 < 2 ^ 60 := lt_of_lt_of_le hd.1 hd.2.2.2.2
    exact_mod_cast this.le
  have key : ∀ τ : ℚ, Approx eta5 (val d) τ →
      0 ≤ τ ∧ |τ - val d| ≤ eta5 * val d ∧ (τ = 0 ∨ 1 / 2 ^ 61 ≤ τ) ∧ InRange (s + τ) := by
    intro τ h
    obtain ⟨b1, b2⟩ := h.bounds eta5_bound.2.1 hv0
    have hτ0 : 0 ≤ τ := le_trans (by positivity) b1
    have hτz : τ = 0 ∨ 1 / 2 ^ 61 ≤ τ := by
      rcases val_pos d hd with hz | hz
      · left; rw [hz] at h; exact h.eq_zero
      · right
        have : (1 : ℚ) / 2 ^ 61 = 1 / 2 ^ 60 / 2 := by norm_num
        linarith
    refine ⟨hτ0, h.abs_sub_le hv0, hτz, ?_⟩
    rcases hs with hs' | hs'
    · rcases hτz with hτ' | hτ'
      · left; rw [hs', hτ']; ring
      · refine inRange_of_bounds ?_ ?_
        · have : (1 : ℚ) / 2 ^ 128 ≤ 1 / 2 ^ 61 := by norm_num
          linarith
        · have : (2 : ℚ) ^ 100 + 2 * 2 ^ 60 ≤ 2 ^ 128 := by norm_num
          linarith
    · refine inRange_of_bounds ?_ ?_
      · have : (1 : ℚ) / 2 ^ 128 ≤ 1 / 2 ^ 63 := by norm_num
        linarith
      · have : (2 : ℚ) ^ 100 + 2 * 2 ^ 60 ≤ 2 ^ 128 := by norm_num
        linarith
  unfold stepD
  rcases hA.mulAdd s (A.ofNat d.1) (frac A d.2.2.1 d.2.2.2.1) with h | h
  · obtain ⟨t0, t1, t2, t3⟩ := key _ h2
    obtain ⟨δ, hδ, e⟩ := hA.add s _ t3
    exact ⟨_, δ, hδ, t0, t1, t2, by rw [h, e]⟩
  · obtain ⟨t0, t1, t2, t3⟩ := key _ h1
    obtain ⟨δ, hδ, e⟩ := hA.fma (A.ofNat d.1) (frac A d.2.2.1 d.2.2.2.1) s (by rwa [add_comm])
    exact ⟨_, δ, hδ, t0, t1, t2, by rw [h, e, add_comm]⟩

theorem sumErr_nonneg : ∀ (start : ℚ) (cs : List ℕ), 0 ≤ start → 0 ≤ sumErr start cs
  | _, [], _ => by simp [sumErr]
  | start, c :: cs, h => by
    simp only [sumErr]
    have := sumErr_nonneg (start + c) cs (by positivity)
    have hu := u_pos
    positivity

/-- **The accumulated error.** From a state `s` within `E` of an exact partial sum
`S ∈ [0, start]`, the computed sum over the data `L` is within `E + sumErr start (caps)` of
`S + Σ val`, provided that total is at most `1`. -/
theorem fold_err' (A : Arith) (hA : Conforms A) :
    ∀ (L : List D) (start s S E : ℚ) (j : ℕ),
      (∀ d ∈ L, DOK d) → j + L.length ≤ 2 ^ 16 →
      0 ≤ S → S ≤ start → start + (((L.map cap).sum : ℕ) : ℚ) ≤ 2 ^ 80 → 0 ≤ E → |s - S| ≤ E → 0 ≤ s →
      (s = 0 ∨ (1 - j * u) / 2 ^ 62 ≤ s) →
      E + sumErr start (L.map cap) ≤ 1 →
      |L.foldl (stepD A) s - (S + (L.map val).sum)| ≤ E + sumErr start (L.map cap) ∧
        0 ≤ L.foldl (stepD A) s ∧
        (L.foldl (stepD A) s = 0 ∨ (1 - ((j + L.length : ℕ) : ℚ) * u) / 2 ^ 62 ≤ L.foldl (stepD A) s)
        := by
  intro L
  induction L with
  | nil =>
    intro start s S E j _ _ _ _ _ _ hE hs0 hlow _
    simp only [List.foldl_nil, List.map_nil, List.sum_nil, add_zero, sumErr, List.length_nil]
    exact ⟨hE, hs0, hlow⟩
  | cons d L ih =>
    intro start s S E j hL hj hS0 hSs hst hE0 hE hs0 hslow htot
    have hu := u_pos
    have hd := hL d List.mem_cons_self
    simp only [List.map_cons, sumErr] at htot ⊢
    simp only [List.map_cons, List.sum_cons, Nat.cast_add] at hst
    have hrs0 : (0 : ℚ) ≤ (((L.map cap).sum : ℕ) : ℚ) := Nat.cast_nonneg _
    have hrest0 := sumErr_nonneg (start + (cap d : ℚ)) (L.map cap) (by
      have : (0 : ℚ) ≤ start := hS0.trans hSs
      positivity)
    have hc0 : (0 : ℚ) ≤ cap d := Nat.cast_nonneg _
    have hcap : (cap d : ℚ) ≤ 2 ^ 60 := by exact_mod_cast hd.2.2.2.2
    have hE1 : E ≤ 1 := by nlinarith
    have hjle : (j : ℚ) ≤ 2 ^ 16 := by
      have : j ≤ 2 ^ 16 := by simp at hj; omega
      exact_mod_cast this
    have hju : (j : ℚ) * u ≤ 1 / 2 ^ 37 := by
      have : (j : ℚ) * u ≤ 2 ^ 16 * u := mul_le_mul_of_nonneg_right hjle hu.le
      have e : (2 : ℚ) ^ 16 * u = 1 / 2 ^ 37 := by unfold u; norm_num
      linarith
    have hj0 : (0 : ℚ) ≤ j := Nat.cast_nonneg j
    have hju0 : 0 ≤ (j : ℚ) * u := mul_nonneg hj0 hu.le
    -- the state is in the range of the step lemma
    have hEabs := abs_le.mp hE
    have hsW : s ≤ 2 ^ 100 := by
      have : (2 : ℚ) ^ 80 + 1 ≤ 2 ^ 100 := by norm_num
      linarith
    have hs63 : s = 0 ∨ 1 / 2 ^ 63 ≤ s := by
      rcases hslow with h | h
      · exact Or.inl h
      · right
        have : (1 : ℚ) / 2 ^ 63 ≤ (1 - j * u) / 2 ^ 62 := by
          rw [div_le_div_iff₀ (by positivity) (by positivity)]
          have : (1 : ℚ) / 2 ^ 37 ≤ 1 / 2 := by norm_num
          nlinarith
        linarith
    obtain ⟨τ, δ, hδ, hτ0, hτ, hτz, hst'⟩ := dstep A hA d hd s hs0 hsW hs63
    have hδ' := abs_le.mp hδ
    have hτ' := abs_le.mp hτ
    have hv0 := val_nonneg d
    have hvc := val_le_cap d hd
    have heta := eta5_bound
    have hηv : eta5 * val d ≤ eta5 * cap d := mul_le_mul_of_nonneg_left hvc heta.1
    have hsτ0 : 0 ≤ s + τ := add_nonneg hs0 hτ0
    -- the new error
    have hsτ : s + τ ≤ start + cap d + E + eta5 * cap d := by linarith
    have hprod : |δ * (s + τ)| ≤ u * (start + cap d + E + eta5 * cap d) := by
      rw [abs_mul, abs_of_nonneg hsτ0]
      exact mul_le_mul hδ hsτ hsτ0 hu.le
    have hnew : |(s + τ) * (1 + δ) - (S + val d)| ≤
        E + (6 * u * cap d + u * (start + cap d + 1)) := by
      have e : (s + τ) * (1 + δ) - (S + val d) = (s - S) + (τ - val d) + δ * (s + τ) := by ring
      rw [e]
      have h6 : eta5 * cap d + u * (eta5 * cap d) ≤ 6 * u * cap d := by
        have : eta5 * (1 + u) * cap d ≤ 21 / 4 * u * cap d :=
          mul_le_mul_of_nonneg_right heta.2.2 hc0
        nlinarith
      calc |(s - S) + (τ - val d) + δ * (s + τ)|
          ≤ |s - S| + |τ - val d| + |δ * (s + τ)| := abs_add_three _ _ _
        _ ≤ E + eta5 * cap d + u * (start + cap d + E + eta5 * cap d) := by
            have := hτ.trans hηv
            linarith
        _ ≤ E + (6 * u * cap d + u * (start + cap d + 1)) := by nlinarith
    have hlow : (s + τ) * (1 + δ) = 0 ∨ (1 - ((j + 1 : ℕ) : ℚ) * u) / 2 ^ 62 ≤ (s + τ) * (1 + δ) := by
      push_cast
      have hu1 : u < 1 := u_lt
      rcases hτz with hτ0' | hτ1
      · rcases hslow with h | h
        · left; rw [h, hτ0']; ring
        · right
          rw [hτ0', add_zero]
          have : s * (1 - u) ≤ s * (1 + δ) := mul_le_mul_of_nonneg_left (by linarith) hs0
          have h2 : (1 - j * u) / 2 ^ 62 * (1 - u) ≤ s * (1 - u) :=
            mul_le_mul_of_nonneg_right h (by linarith)
          have h3 : (1 - (j + 1) * u) / 2 ^ 62 ≤ (1 - j * u) / 2 ^ 62 * (1 - u) := by
            rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right (by positivity)]
            nlinarith
          linarith
      · right
        have : (s + τ) * (1 - u) ≤ (s + τ) * (1 + δ) :=
          mul_le_mul_of_nonneg_left (by linarith) hsτ0
        have h2 : 1 / 2 ^ 61 * (1 - u) ≤ (s + τ) * (1 - u) :=
          mul_le_mul_of_nonneg_right (by linarith) (by linarith)
        have h3 : (1 - (j + 1) * u) / 2 ^ 62 ≤ 1 / 2 ^ 61 * (1 - u) := by
          rw [div_le_iff₀ (by positivity)]
          have : (0 : ℚ) ≤ (j + 1) * u := by positivity
          have e : (1 : ℚ) / 2 ^ 61 * (1 - u) * 2 ^ 62 = 2 * (1 - u) := by ring
          rw [e]
          unfold u at *
          nlinarith
        linarith
    have hnn : 0 ≤ (s + τ) * (1 + δ) := mul_nonneg hsτ0 (by linarith [u_lt])
    have := ih (start + cap d) ((s + τ) * (1 + δ)) (S + val d)
      (E + (6 * u * cap d + u * (start + cap d + 1))) (j + 1)
      (fun b hb => hL b (List.mem_cons_of_mem _ hb)) (by simp at hj ⊢; omega)
      (by linarith) (by linarith) (by linarith) (by
        have : (0 : ℚ) ≤ start := hS0.trans hSs
        positivity) hnew hnn hlow (by linarith)
    rw [List.foldl_cons, show stepD A s d = (s + τ) * (1 + δ) from hst']
    have e2 : S + (val d + (L.map val).sum) = S + val d + (L.map val).sum := by ring
    have e3 : E + (6 * u * cap d + u * (start + cap d + 1) + sumErr (start + cap d) (L.map cap))
        = E + (6 * u * cap d + u * (start + cap d + 1)) + sumErr (start + cap d) (L.map cap) := by
      ring
    rw [List.sum_cons, e2, e3]
    have e4 : j + 1 + L.length = j + (d :: L).length := by simp; omega
    rw [e4] at this
    exact this

end Validation.BFVDecrypt
