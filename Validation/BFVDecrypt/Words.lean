import Validation.BFVDecrypt.Sum
import Challenge.BFVDecrypt
import Mathlib.Data.Nat.Size

/-!
# Validation.BFVDecrypt.Words — the words of a coefficient, as data

`allWords qs (tables A t qs) xs` is the list `spec t qs xs` of data `(word, integer entry,
numerator, modulus, cap)` with the arithmetic applied only to the `…Frac` entries
(`allWords_eq`); its caps are `caps qs` (`caps_eq`); every datum satisfies `DOK`
(`spec_dok`); the word split is exact (`split_exact`).
-/

namespace Validation.BFVDecrypt
open Spec.Float Spec.DecryptBFV FHE.Float

/-- The data of one limb `q` with residue `x`. -/
def wspec (t : ℕ) (qs : List ℕ) (q x : ℕ) : List D :=
  if pathSplit qs then
    [(subFast x (lshift (rshift x (qMSBHf qs)) (qMSBHf qs)), theta t qs q / q % t,
        theta t qs q % q, q, min (2 ^ qMSBHf qs) q),
      (rshift x (qMSBHf qs), theta t qs q * 2 ^ qMSBHf qs / q % t,
        theta t qs q * 2 ^ qMSBHf qs % q, q, (q - 1) / 2 ^ qMSBHf qs + 1)]
  else [(x, theta t qs q / q % t, theta t qs q % q, q, q)]

/-- The data of a coefficient. -/
def spec (t : ℕ) (qs xs : List ℕ) : List D := (qs.zip xs).flatMap fun p => wspec t qs p.1 p.2

/-- A datum as the word the code uses. -/
def toW (A : Arith) (d : D) : ℕ × ℕ × ℚ := (d.1, d.2.1, frac A d.2.2.1 d.2.2.2.1)

theorem allWords_eq (A : Arith) (t : ℕ) (qs xs : List ℕ) :
    allWords qs (tables A t qs) xs = (spec t qs xs).map (toW A) := by
  unfold allWords spec tables
  rw [List.zip_map_left, List.flatMap_map, List.map_flatMap]
  congr 1
  funext p
  unfold words wspec toW
  by_cases h : pathSplit qs <;> simp [h]

theorem floatSum_eq (A : Arith) (start : ℚ) (t : ℕ) (qs xs : List ℕ) :
    floatSum A start (allWords qs (tables A t qs) xs) = (spec t qs xs).foldl (stepD A) start := by
  rw [allWords_eq, floatSum, List.foldl_map]
  rfl

theorem caps_eq (t : ℕ) (qs xs : List ℕ) (hl : xs.length = qs.length) :
    (spec t qs xs).map cap = caps qs := by
  unfold spec caps
  rw [List.map_flatMap]
  have : (fun p : ℕ × ℕ => (wspec t qs p.1 p.2).map cap) = (fun p => wordCaps qs p.1) := by
    funext p
    unfold wspec wordCaps cap
    by_cases h : pathSplit qs <;> simp [h]
  rw [this, ← List.flatMap_map (f := Prod.fst) (g := wordCaps qs)]
  rw [List.map_fst_zip (by omega)]

/-! ### The word split -/

theorem split_exact (h x : ℕ) (_hh : h ≤ 60) (hx : x < 2 ^ 64) :
    rshift x h * 2 ^ h < 2 ^ 64 ∧ lshift (rshift x h) h = rshift x h * 2 ^ h ∧
      subFast x (lshift (rshift x h) h) = x % 2 ^ h := by
  have h1 : rshift x h * 2 ^ h ≤ x := Nat.div_mul_le_self x (2 ^ h)
  have h2 : rshift x h * 2 ^ h < 2 ^ 64 := lt_of_le_of_lt h1 hx
  have h3 : lshift (rshift x h) h = rshift x h * 2 ^ h := Nat.mod_eq_of_lt h2
  refine ⟨h2, h3, ?_⟩
  rw [h3]
  unfold subFast
  rw [Nat.mod_eq_of_lt h2]
  have e : x + (2 ^ 64 - rshift x h * 2 ^ h) = (x - rshift x h * 2 ^ h) + 2 ^ 64 := by omega
  rw [e, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
  unfold rshift
  have := Nat.mod_add_div x (2 ^ h)
  rw [mul_comm] at this
  omega

theorem rshift_mul_add (h x : ℕ) (hh : h ≤ 60) (hx : x < 2 ^ 64) :
    subFast x (lshift (rshift x h) h) + rshift x h * 2 ^ h = x := by
  rw [(split_exact h x hh hx).2.2]
  unfold rshift
  have := Nat.mod_add_div x (2 ^ h)
  rw [mul_comm] at this
  omega

/-! ### The parameters -/

theorem params {t : ℕ} {qs : List ℕ} (hp : decParamsOK? t qs = true) :
    2 ≤ t ∧ t < 2 ^ 50 ∧ 1 ≤ qs.length ∧ qs.length ≤ 128 ∧
      (∀ q ∈ qs, 3 ≤ q ∧ q % 2 = 1 ∧ q < 2 ^ 60) ∧ qs.Pairwise Nat.Coprime := by
  simp only [decParamsOK?, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hp
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := hp
  exact ⟨h1, h2, h3, h4, fun q h => ⟨(h5 q h).1.1, (h5 q h).1.2, (h5 q h).2⟩, h6⟩

theorem foldr_max_ge : ∀ (qs : List ℕ), ∀ q ∈ qs, q ≤ qs.foldr max 0
  | [], _, h => absurd h List.not_mem_nil
  | a :: l, q, h => by
    simp only [List.foldr_cons]
    rcases List.mem_cons.mp h with rfl | h
    · exact le_max_left _ _
    · exact (foldr_max_ge l q h).trans (le_max_right _ _)

theorem foldr_max_lt (qs : List ℕ) (B : ℕ) (hB : 0 < B) (h : ∀ q ∈ qs, q < B) :
    qs.foldr max 0 < B := by
  induction qs with
  | nil => simpa using hB
  | cons a l ih =>
    simp only [List.foldr_cons]
    exact max_lt (h a List.mem_cons_self) (ih fun q hq => h q (List.mem_cons_of_mem _ hq))

/-- Every modulus is below `2^qMSB`; `qMSB ≤ 60`. -/
theorem qMSB_facts {t : ℕ} {qs : List ℕ} (hp : decParamsOK? t qs = true) :
    (∀ q ∈ qs, q < 2 ^ qMSB qs) ∧ qMSB qs ≤ 60 ∧ qMSBHf qs ≤ 30 := by
  obtain ⟨_, _, _, _, hq, _⟩ := params hp
  have hlt : qs.foldr max 0 < 2 ^ 60 := foldr_max_lt qs _ (by norm_num) fun q h => (hq q h).2.2
  have h60 : qMSB qs ≤ 60 := by
    unfold qMSB msb
    exact Nat.size_le.mpr hlt
  refine ⟨fun q h => lt_of_le_of_lt (foldr_max_ge qs q h) (Nat.lt_size_self _), h60, ?_⟩
  unfold qMSBHf; omega

theorem mem_zip_lt {qs xs : List ℕ} (hx : List.Forall₂ (fun x q => x < q) xs qs) :
    ∀ p ∈ qs.zip xs, p.2 < p.1 ∧ p.1 ∈ qs := by
  induction hx with
  | nil => simp
  | cons h _ ih =>
    intro p hp
    simp only [List.zip_cons_cons, List.mem_cons] at hp
    rcases hp with rfl | hp
    · exact ⟨h, List.mem_cons_self⟩
    · obtain ⟨a, b⟩ := ih p hp
      exact ⟨a, List.mem_cons_of_mem _ b⟩

/-- Every datum of a coefficient with canonical residues satisfies `DOK`. -/
theorem spec_dok {t : ℕ} {qs xs : List ℕ} (hp : decParamsOK? t qs = true)
    (hx : List.Forall₂ (fun x q => x < q) xs qs) : ∀ d ∈ spec t qs xs, DOK d := by
  obtain ⟨_, _, _, _, hq, _⟩ := params hp
  obtain ⟨_, _, hh⟩ := qMSB_facts hp
  intro d hd
  unfold spec at hd
  obtain ⟨p, hpz, hdp⟩ := List.mem_flatMap.mp hd
  obtain ⟨hxq, hqm⟩ := mem_zip_lt hx p hpz
  obtain ⟨h3, _, h60⟩ := hq p.1 hqm
  have hx64 : p.2 < 2 ^ 64 := by omega
  unfold DOK
  unfold wspec at hdp
  split at hdp
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hdp
    obtain ⟨_, _, hsub⟩ := split_exact (qMSBHf qs) p.2 (by omega) hx64
    rcases hdp with rfl | rfl
    · refine ⟨?_, Nat.mod_lt _ (by omega : 0 < p.1), (by omega : 1 ≤ p.1), h60, ?_⟩
      · simp only
        rw [hsub]
        exact lt_min (Nat.mod_lt _ (by positivity)) (lt_of_le_of_lt (Nat.mod_le _ _) hxq)
      · exact (min_le_right _ _).trans h60.le
    · refine ⟨?_, Nat.mod_lt _ (by omega : 0 < p.1), (by omega : 1 ≤ p.1), h60, ?_⟩
      · simp only [rshift]
        have : p.2 / 2 ^ qMSBHf qs ≤ (p.1 - 1) / 2 ^ qMSBHf qs := Nat.div_le_div_right (by omega)
        omega
      · simp only
        have : (p.1 - 1) / 2 ^ qMSBHf qs ≤ p.1 - 1 := Nat.div_le_self _ _
        omega
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hdp
    subst hdp
    exact ⟨hxq, Nat.mod_lt _ (by omega : 0 < p.1), (by omega : 1 ≤ p.1), h60, h60.le⟩

theorem spec_length {t : ℕ} {qs xs : List ℕ} (hl : xs.length = qs.length) :
    (spec t qs xs).length ≤ 2 * qs.length := by
  unfold spec
  rw [List.length_flatMap]
  have : ∀ p ∈ qs.zip xs, (wspec t qs p.1 p.2).length ≤ 2 := by
    intro p _
    unfold wspec; split <;> simp
  calc ((qs.zip xs).map fun p => (wspec t qs p.1 p.2).length).sum
      ≤ ((qs.zip xs).map fun _ => 2).sum := List.sum_le_sum (by simpa using this)
    _ = 2 * qs.length := by simp [List.length_zip, hl, mul_comm]

/-- The exact fractional part is the sum of the exact terms. -/
theorem exactFrac_eq (t : ℕ) (qs xs : List ℕ) :
    Challenge.BFVDecrypt.exactFrac t qs xs = ((spec t qs xs).map val).sum := by
  unfold Challenge.BFVDecrypt.exactFrac
  rw [allWords_eq, List.map_map]
  congr 1
  apply List.map_congr_left
  intro d _
  simp [toW, frac, Spec.Float.exact, val, mul_div_assoc]

end Validation.BFVDecrypt
