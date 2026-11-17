import Challenge.Word

/-!
# Validation.Word — the base conversions of hybrid key switching cannot wrap

Proofs of the statements of `Challenge.Word`: every product `xᵢ·cᵢ` of a reduced residue and a
table entry is at most `(qᵢ − 1)·(p − 1)`, a digit's moduli are a sublist of the ciphertext
moduli, and `ksWordOK?` bounds the sum over all of them.
-/

namespace Validation.Word
open Challenge.Word

theorem accOK?_def (src : List ℕ) (p : ℕ) :
    accOK? src p = decide ((src.map (· - 1)).sum * (p - 1) < 2 ^ 128) := rfl

theorem ksWordOK?_def (qs ps : List ℕ) :
    ksWordOK? qs ps = ((qs ++ ps).all (fun m => decide (2 ≤ m) && decide (m < 2 ^ 60)) &&
      (qs ++ ps).all (fun p => accOK? qs p) && qs.all (fun q => accOK? ps q)) := rfl

theorem accOK?_iff (src : List ℕ) (p : ℕ) :
    accOK? src p = true ↔ (src.map (· - 1)).sum * (p - 1) < 2 ^ 128 := by
  rw [accOK?_def, decide_eq_true_iff]

theorem ksWordOK?_iff (qs ps : List ℕ) :
    ksWordOK? qs ps = true ↔
      (∀ m ∈ qs ++ ps, 2 ≤ m ∧ m < 2 ^ 60) ∧ (∀ p ∈ qs ++ ps, accOK? qs p = true) ∧
        ∀ q ∈ qs, accOK? ps q = true := by
  rw [ksWordOK?_def]
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, and_assoc]

/-- Each product of a reduced residue and an entry below `p` is at most `(q − 1)·(p − 1)`. -/
theorem sum_le (p : ℕ) :
    ∀ (x d c : List ℕ), List.Forall₂ (· < ·) x d → (∀ v ∈ c, v < p) →
      (List.zipWith (· * ·) x c).sum ≤ (d.map (· - 1)).sum * (p - 1)
  | [], [], _, _, _ => by simp
  | _ :: _, _ :: _, [], _, _ => by simp
  | a :: x, b :: d, e :: c, h, hc => by
    rcases List.forall₂_cons.mp h with ⟨hab, hxd⟩
    have ih := sum_le p x d c hxd (fun v hv => hc v (List.mem_cons_of_mem _ hv))
    have he : e ≤ p - 1 := by have := hc e List.mem_cons_self; omega
    have ha : a ≤ b - 1 := by omega
    simp only [List.zipWith_cons_cons, List.sum_cons, List.map_cons, Nat.add_mul]
    have := Nat.mul_le_mul ha he
    omega
  | [], _ :: _, _, h, _ => by simp at h
  | _ :: _, [], _, h, _ => by simp at h

theorem modUp_acc_no_overflow (qs ps : List ℕ) (h : ksWordOK? qs ps = true)
    (d : List ℕ) (hd : d.Sublist qs) (p : ℕ) (hp : p ∈ qs ++ ps)
    (x c : List ℕ) (hx : List.Forall₂ (· < ·) x d) (hc : ∀ v ∈ c, v < p) :
    (List.zipWith (· * ·) x c).sum < 2 ^ 128 := by
  obtain ⟨-, hacc, -⟩ := (ksWordOK?_iff qs ps).mp h
  have h1 := (accOK?_iff qs p).mp (hacc p hp)
  have h2 := sum_le p x d c hx hc
  have h3 : (d.map (· - 1)).sum ≤ (qs.map (· - 1)).sum := (hd.map _).sum_le_sum (by simp)
  have := Nat.mul_le_mul_right (p - 1) h3
  omega

theorem modDown_acc_no_overflow (qs ps : List ℕ) (h : ksWordOK? qs ps = true)
    (q : ℕ) (hq : q ∈ qs) (x c : List ℕ) (hx : List.Forall₂ (· < ·) x ps) (hc : ∀ v ∈ c, v < q) :
    (List.zipWith (· * ·) x c).sum < 2 ^ 128 := by
  obtain ⟨-, -, hacc⟩ := (ksWordOK?_iff qs ps).mp h
  have h1 := (accOK?_iff ps q).mp (hacc q hq)
  have h2 := sum_le q x ps c hx hc
  omega

theorem acc_wraps_without :
    ksWordOK? (List.replicate 257 (2 ^ 60 - 1)) [] = false ∧
      2 ^ 128 ≤ (List.zipWith (· * ·) (List.replicate 257 (2 ^ 60 - 2))
        (List.replicate 257 (2 ^ 60 - 2))).sum := by
  refine ⟨?_, ?_⟩
  · have : accOK? (List.replicate 257 (2 ^ 60 - 1)) (2 ^ 60 - 1) = false := by
      rw [accOK?_def]; simp only [List.map_replicate, List.sum_replicate, smul_eq_mul]; norm_num
    have hB : ((List.replicate 257 (2 ^ 60 - 1) ++ []).all fun p =>
        accOK? (List.replicate 257 (2 ^ 60 - 1)) p) = false := by
      rw [List.all_eq_false]
      exact ⟨2 ^ 60 - 1, List.mem_append_left _ (List.mem_replicate.mpr ⟨by omega, rfl⟩),
        by rw [this]; decide⟩
    rw [ksWordOK?_def]
    rw [hB, Bool.and_false, Bool.false_and]
  rw [List.zipWith_replicate, List.sum_replicate]
  norm_num

example : type_of% @Validation.Word.modUp_acc_no_overflow =
    type_of% @Challenge.Word.modUp_acc_no_overflow := rfl
example : type_of% @Validation.Word.modDown_acc_no_overflow =
    type_of% @Challenge.Word.modDown_acc_no_overflow := rfl
example : type_of% @Validation.Word.acc_wraps_without =
    type_of% @Challenge.Word.acc_wraps_without := rfl

end Validation.Word
