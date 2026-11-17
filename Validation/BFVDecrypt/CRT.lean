import Validation.BFVDecrypt.Words
import Mathlib.Data.Nat.ChineseRemainder

/-!
# Validation.BFVDecrypt.CRT — what the tables encode

For canonical residues `xᵢ = x mod qᵢ`: `Σᵢ xᵢ·θᵢ/qᵢ = t·x/Q + t·k` for an integer `k`
(`crt_value`), and the words split this sum into an integer part, congruent mod `t` to what the
code accumulates in `intSum`, and the fractional part `exactFrac` (`limbs_value`).
-/

namespace Validation.BFVDecrypt
open Spec.Float Spec.DecryptBFV FHE.Float Challenge.BFVDecrypt

theorem dvd_prod_div {l : List ℕ} (_hl : l.Nodup) {q q' : ℕ} (hq : q ∈ l) (hq' : q' ∈ l)
    (hne : q ≠ q') (hpos : 0 < q') : q ∣ l.prod / q' := by
  have e : l.prod = q' * (l.erase q').prod := (List.prod_erase hq').symm
  rw [e, Nat.mul_div_cancel_left _ hpos]
  exact List.dvd_prod ((List.mem_erase_of_ne hne).mpr hq)

theorem sum_modEq_single {f : ℕ → ℕ} {q0 : ℕ} :
    ∀ (l : List ℕ), l.Nodup → (∀ q ∈ l, q ≠ q0 → f q ≡ 0 [MOD q0]) →
      (l.map f).sum ≡ (if q0 ∈ l then f q0 else 0) [MOD q0]
  | [], _, _ => by simp [Nat.ModEq]
  | a :: l, hnd, hf => by
    have ih := sum_modEq_single l (List.nodup_cons.mp hnd).2
      (fun q hq => hf q (List.mem_cons_of_mem _ hq))
    simp only [List.map_cons, List.sum_cons, List.mem_cons]
    by_cases ha : a = q0
    · subst ha
      have hn : a ∉ l := (List.nodup_cons.mp hnd).1
      simp only [true_or, ite_true, hn, ite_false] at ih ⊢
      simpa using Nat.ModEq.add_left (f a) ih
    · have h0 := hf a List.mem_cons_self ha
      have e : (if q0 = a ∨ q0 ∈ l then f q0 else 0) = 0 + (if q0 ∈ l then f q0 else 0) := by
        by_cases h : q0 ∈ l
        · simp [h]
        · simp [h, Ne.symm ha]
      rw [e]
      exact Nat.ModEq.add h0 ih

theorem coprime_of_mem {l : List ℕ} (hco : l.Pairwise Nat.Coprime) {a b : ℕ} (ha : a ∈ l)
    (hb : b ∈ l) (hne : a ≠ b) : Nat.Coprime a b := by
  induction l with
  | nil => simp at ha
  | cons c l ih =>
    rw [List.pairwise_cons] at hco
    rcases List.mem_cons.mp ha with h1 | h1 <;> rcases List.mem_cons.mp hb with h2 | h2
    · exact absurd (h1.trans h2.symm) hne
    · rw [h1]; exact hco.1 b h2
    · rw [h2]; exact (hco.1 a h1).symm
    · exact ih hco.2 h1 h2

theorem nodup_of_coprime {qs : List ℕ} (hco : qs.Pairwise Nat.Coprime) (hq : ∀ q ∈ qs, 2 ≤ q) :
    qs.Nodup := by
  refine List.Pairwise.imp_of_mem ?_ hco
  intro a b ha _ h hab
  subst hab
  have : a = 1 := by simpa [Nat.Coprime, Nat.gcd_self] using h
  have := hq a ha
  omega

/-- **The CRT sum.** `Σ_q (x mod q)·[(Q/q)⁻¹]_q·(Q/q) ≡ x (mod Q)`. -/
theorem crt (qs : List ℕ) (hco : qs.Pairwise Nat.Coprime) (hq : ∀ q ∈ qs, 2 ≤ q) (x : ℕ) :
    (qs.map fun q => x % q * invMod (qs.prod / q) q * (qs.prod / q)).sum ≡ x [MOD qs.prod] := by
  have hnd := nodup_of_coprime hco hq
  have h := (Nat.modEq_list_map_prod_iff (s := id) (l := qs)
    (a := (qs.map fun q => x % q * invMod (qs.prod / q) q * (qs.prod / q)).sum) (b := x)
    (by exact hco)).mpr
  rw [List.map_id] at h
  apply h
  intro q0 hq0
  simp only [id]
  have hq02 := hq q0 hq0
  have hs := sum_modEq_single (f := fun q => x % q * invMod (qs.prod / q) q * (qs.prod / q))
    (q0 := q0) qs hnd (by
      intro q hqm hne
      have hd := dvd_prod_div hnd hq0 hqm (Ne.symm hne) (by have := hq q hqm; omega)
      exact (Nat.modEq_zero_iff_dvd.mpr (Dvd.dvd.mul_left hd _)))
  rw [ite_eq_left_iff.mpr (fun h => absurd hq0 h)] at hs
  refine hs.trans ?_
  -- (x mod q0)·h·(Q/q0) ≡ x (mod q0)
  have hcop : Nat.Coprime (qs.prod / q0) q0 := by
    have e : qs.prod / q0 = (qs.erase q0).prod := by
      rw [← List.prod_erase hq0, Nat.mul_div_cancel_left _ (by omega)]
    rw [e]
    apply Nat.Coprime.symm
    apply Nat.coprime_list_prod_right_iff.mpr
    intro b hb
    have hb' := List.mem_of_mem_erase hb
    have hne : b ≠ q0 := fun h => by
      subst h
      exact (List.Nodup.not_mem_erase hnd) hb
    exact coprime_of_mem hco hq0 hb' (Ne.symm hne)
  have : NeZero q0 := ⟨by omega⟩
  rw [← ZMod.natCast_eq_natCast_iff]
  push_cast
  unfold invMod
  rw [ZMod.natCast_zmod_val, ZMod.natCast_mod, mul_assoc,
    mul_comm (((qs.prod / q0 : ℕ) : ZMod q0))⁻¹, ZMod.coe_mul_inv_eq_one _ hcop, mul_one]

theorem sum_map_flatMap {α β M : Type} [AddCommMonoid M] (l : List α) (f : α → List β)
    (g : β → M) : ((l.flatMap f).map g).sum = (l.map fun a => ((f a).map g).sum).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [List.flatMap_cons, List.map_append, List.sum_append, ih]

/-- **The tables encode `t·x/Q` modulo `t`**: `Σ_q (x mod q)·θ_q/q = t·x/Q + t·k`. -/
theorem crt_value {t : ℕ} {qs : List ℕ} (hp : decParamsOK? t qs = true) (x : ℕ) :
    ∃ k : ℤ, (qs.map fun q => ((x % q : ℕ) : ℚ) * (theta t qs q : ℚ) / q).sum =
      t * x / qs.prod + t * k := by
  obtain ⟨_, _, _, _, hq, hco⟩ := params hp
  have hq2 : ∀ q ∈ qs, 2 ≤ q := fun q h => by have := (hq q h).1; omega
  have hQ : 0 < qs.prod := List.prod_pos fun q h => by have := hq2 q h; omega
  have hc := crt qs hco hq2 x
  set N := (qs.map fun q => x % q * invMod (qs.prod / q) q * (qs.prod / q)).sum with hN
  have hd : (qs.prod : ℤ) ∣ (N : ℤ) - x := (Nat.modEq_iff_dvd.mp hc.symm)
  obtain ⟨k, hk⟩ := hd
  refine ⟨k, ?_⟩
  have hQQ : (qs.prod : ℚ) ≠ 0 := by exact_mod_cast hQ.ne'
  have hterm : ∀ q ∈ qs, ((x % q : ℕ) : ℚ) * (theta t qs q : ℚ) / q =
      t / qs.prod * ((x % q * invMod (qs.prod / q) q * (qs.prod / q) : ℕ) : ℚ) := by
    intro q hqm
    have hq0 : (q : ℚ) ≠ 0 := by have := hq2 q hqm; exact_mod_cast (show q ≠ 0 by omega)
    have hdq : qs.prod / q * q = qs.prod := Nat.div_mul_cancel (List.dvd_prod hqm)
    have e : ((qs.prod / q : ℕ) : ℚ) * q = qs.prod := by exact_mod_cast hdq
    have hP : ((qs.prod / q : ℕ) : ℚ) ≠ 0 := by
      intro h0; rw [h0, zero_mul] at e; exact hQQ e.symm
    unfold theta
    simp only [Nat.cast_mul]
    rw [← e]
    field_simp
  rw [List.map_congr_left hterm, List.sum_map_mul_left]
  have hsum : (qs.map fun a => ((x % a * invMod (qs.prod / a) a * (qs.prod / a) : ℕ) : ℚ)).sum
      = (N : ℚ) := by
    rw [hN, Nat.cast_list_sum, List.map_map]; rfl
  rw [hsum]
  have hNk : (N : ℚ) = x + qs.prod * k := by
    have : ((N : ℤ) : ℚ) = ((x + qs.prod * k : ℤ) : ℚ) := by rw [← hk]; ring
    rw [Int.cast_add, Int.cast_mul, Int.cast_natCast, Int.cast_natCast, Int.cast_natCast] at this
    exact this
  rw [hNk]
  field_simp

/-- One word: `w·θ/q = w·⌊θ/q⌋ + w·(θ mod q)/q`. -/
theorem word_value (w θ q : ℕ) (hq : 0 < q) :
    (w : ℚ) * θ / q = ((w * (θ / q) : ℕ) : ℚ) + (w : ℚ) * ((θ % q : ℕ) : ℚ) / q := by
  have hq0 : (q : ℚ) ≠ 0 := by exact_mod_cast hq.ne'
  have e : (θ : ℚ) = q * ((θ / q : ℕ) : ℚ) + ((θ % q : ℕ) : ℚ) := by
    exact_mod_cast (Nat.div_add_mod θ q).symm
  rw [e]
  push_cast
  field_simp

/-- **One limb**: `x·θ/q` is an integer congruent mod `t` to `Σ word·entry` plus the exact
fractional terms of its words. -/
theorem limb_value {t : ℕ} {qs : List ℕ} (hp : decParamsOK? t qs = true) (q x : ℕ) (hqm : q ∈ qs)
    (hx : x < q) : ∃ I : ℕ, (I : ZMod t) = (((wspec t qs q x).map fun d => d.1 * d.2.1).sum : ℕ) ∧
      (x : ℚ) * (theta t qs q : ℚ) / q = I + ((wspec t qs q x).map val).sum := by
  obtain ⟨_, _, _, _, hq, _⟩ := params hp
  obtain ⟨h3, _, h60⟩ := hq q hqm
  obtain ⟨_, _, hh⟩ := qMSB_facts hp
  have hq0 : 0 < q := by omega
  unfold wspec
  split
  · set h := qMSBHf qs
    have hsplit := rshift_mul_add h x (by omega) (by omega)
    set lo := subFast x (lshift (rshift x h) h)
    set hi := rshift x h
    refine ⟨lo * (theta t qs q / q) + hi * (theta t qs q * 2 ^ h / q), ?_, ?_⟩
    · simp [Nat.cast_add, Nat.cast_mul, ZMod.natCast_mod]
    · simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, val]
      have e : (x : ℚ) * theta t qs q / q =
          (lo : ℚ) * theta t qs q / q + (hi : ℚ) * ((theta t qs q * 2 ^ h : ℕ) : ℚ) / q := by
        have : (x : ℚ) = lo + hi * 2 ^ h := by exact_mod_cast hsplit.symm
        rw [this]; push_cast; ring
      rw [e, word_value lo _ q hq0, word_value hi _ q hq0]
      push_cast
      ring
  · refine ⟨x * (theta t qs q / q), ?_, ?_⟩
    · simp [Nat.cast_mul, ZMod.natCast_mod]
    · simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, val]
      rw [word_value x _ q hq0]

end Validation.BFVDecrypt
