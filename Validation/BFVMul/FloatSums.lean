import Challenge.BFVMul.Float
import FHE.Float.Sum

/-!
# Validation.BFVMul.FloatSums — the binary64 sums are within the tolerances

Proofs of `Challenge.BFVMul.exact_conforms`, `nuSw_tol`, `nuSr_tol`, `nu_range`, `floatSums_ok`
from the error analysis in `FHE.Float.Sum` (`nuSw_err`, `nuSr_err`).
-/

namespace Validation.BFVMul
open Spec Spec.Float Challenge.BFVMul FHE.Float

theorem exact_conforms : Conforms Spec.Float.exact :=
  { ofNat := fun n _ => ⟨0, by simp [u], by simp [Spec.Float.exact]⟩
    mul := fun a b _ => ⟨0, by simp [u], by simp [Spec.Float.exact]⟩
    div := fun a b _ _ => ⟨0, by simp [u], by simp [Spec.Float.exact]⟩
    add := fun a b _ => ⟨0, by simp [u], by simp [Spec.Float.exact]⟩
    fma := fun a b c _ => ⟨0, by simp [u], by simp [Spec.Float.exact]⟩
    mulAdd := fun s a b => Or.inl rfl }

/-! ### Unfolding the locked definitions -/

theorem floatBasisOK_def (ms : List ℕ) :
    floatBasisOK ms =
      (decide (ms.length ≤ 128) && ms.all fun m => decide (1 ≤ m) && decide (m < 2 ^ 60)) :=
  rfl

theorem floatBasisOK_iff' (ms : List ℕ) :
    floatBasisOK ms = true ↔ ms.length ≤ 128 ∧ ∀ m ∈ ms, 1 ≤ m ∧ m < 2 ^ 60 := by
  simp only [floatBasisOK_def, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq]

/-- What the error analysis uses of `floatBasisOK`: at most `2¹⁶` moduli in `[1, 2⁶⁴)`. -/
theorem floatBasisOK_weak (ms : List ℕ) (h : floatBasisOK ms = true) :
    ms.length ≤ 2 ^ 16 ∧ ∀ m ∈ ms, 1 ≤ m ∧ m < 2 ^ 64 := by
  obtain ⟨h1, h2⟩ := (floatBasisOK_iff' ms).mp h
  exact ⟨by omega, fun m hm => ⟨(h2 m hm).1, by have := (h2 m hm).2; omega⟩⟩

theorem nuSw_def (A : Arith) (qs : List ℕ) (y : List ℤ) :
    Fl.nuSw A qs y =
      (qs.zip y).foldl (fun s p => A.mulAdd s (A.ofNat p.2.toNat) (Fl.qInv A p.1)) (1 / 2) :=
  rfl

theorem nuSr_def (A : Arith) (ms : List ℕ) (ns x : List ℤ) :
    Fl.nuSr A ms ns x = ((ms.zip ns).zip x).foldl
      (fun s p => A.mulAdd s (Fl.frac A p.1.2.toNat p.1.1) (A.ofNat p.2.toNat)) (1 / 2) :=
  rfl

theorem exactSw_def (qs : List ℕ) (y : List ℤ) :
    Fl.exactSw qs y = 1 / 2 + ((qs.zip y).map fun p => (p.2 : ℚ) / (p.1 : ℚ)).sum :=
  rfl

theorem exactSr_def (ms : List ℕ) (ns x : List ℤ) :
    Fl.exactSr ms ns x =
      1 / 2 + (((ms.zip ns).zip x).map fun p => (p.2 : ℚ) * (p.1.2 : ℚ) / (p.1.1 : ℚ)).sum :=
  rfl

theorem reduced_def (ms : List ℕ) (v : List ℤ) :
    Fl.Reduced ms v = ∀ p ∈ ms.zip v, 0 ≤ p.2 ∧ p.2 < (p.1 : ℤ) :=
  rfl

theorem doubleSw_def (k : ℕ) : BudgetBFV.doubleSw k = k * (k + 5) := rfl
theorem doubleSr_def (ms : List ℕ) : BudgetBFV.doubleSr ms = (ms.length + 6) * (1 + ms.sum) := rfl
theorem floatDen_def : BudgetBFV.floatDen = 2 ^ 53 := rfl

/-! ### Lists -/

theorem mem_zip_zip {α β γ : Type} :
    ∀ (l : List α) (r : List β) (t : List γ) (a : α) (b : β) (c : γ),
      ((a, b), c) ∈ (l.zip r).zip t → (a, c) ∈ l.zip t
  | [], _, _, _, _, _, h => by simp at h
  | _ :: _, [], _, _, _, _, h => by simp at h
  | _ :: _, _ :: _, [], _, _, _, h => by simp at h
  | x :: l, y :: r, z :: t, a, b, c, h => by
    simp only [List.zip_cons_cons, List.mem_cons, Prod.mk.injEq] at h ⊢
    rcases h with ⟨⟨h1, _⟩, h3⟩ | h
    · exact Or.inl ⟨h1, h3⟩
    · exact Or.inr (mem_zip_zip l r t a b c h)

theorem sum_fst_zip_le {β : Type} :
    ∀ (l : List ℕ) (r : List β), ((l.zip r).map fun p => (p.1 : ℚ)).sum ≤ ((l.sum : ℕ) : ℚ)
  | [], _ => by simp
  | x :: l, [] => by
    simp only [List.zip_nil_right, List.map_nil, List.sum_nil]
    exact Nat.cast_nonneg _
  | x :: l, y :: r => by
    simp only [List.zip_cons_cons, List.map_cons, List.sum_cons, Nat.cast_add]
    exact add_le_add le_rfl (sum_fst_zip_le l r)

theorem sum_fst_fst_zip_le {β γ : Type} :
    ∀ (l : List ℕ) (r : List β) (t : List γ),
      (((l.zip r).zip t).map fun p => (p.1.1 : ℚ)).sum ≤ ((l.sum : ℕ) : ℚ)
  | [], _, _ => by simp
  | x :: l, [], _ => by
    simp only [List.zip_nil_right, List.zip_nil_left, List.map_nil, List.sum_nil]
    exact Nat.cast_nonneg _
  | x :: l, y :: r, [] => by
    simp only [List.zip_nil_right, List.map_nil, List.sum_nil]
    exact Nat.cast_nonneg _
  | x :: l, y :: r, z :: t => by
    simp only [List.zip_cons_cons, List.map_cons, List.sum_cons, Nat.cast_add]
    exact add_le_add le_rfl (sum_fst_fst_zip_le l r t)

theorem length_zip_le {α β : Type} (l : List α) (r : List β) : (l.zip r).length ≤ l.length := by
  rw [List.length_zip]; exact Nat.min_le_left _ _

/-! ### The sums -/

/-- The hypotheses of `nuSw_err` from the locked side conditions. -/
theorem sw_hyps (qs : List ℕ) (y : List ℤ) (hqs : floatBasisOK qs = true)
    (hy : Fl.Reduced qs y) :
    (qs.zip y).length ≤ 2 ^ 16 ∧
      ∀ p ∈ qs.zip y, 1 ≤ p.1 ∧ p.1 < 2 ^ 64 ∧ 0 ≤ p.2 ∧ p.2 < (p.1 : ℤ) := by
  obtain ⟨h1, h2⟩ := floatBasisOK_weak qs hqs
  rw [reduced_def] at hy
  refine ⟨(length_zip_le _ _).trans h1, fun p hp => ?_⟩
  obtain ⟨a, b⟩ := p
  have := h2 a (List.of_mem_zip hp).1
  exact ⟨this.1, this.2, hy _ hp⟩

/-- The hypotheses of `nuSr_err` from the locked side conditions. -/
theorem sr_hyps (ms : List ℕ) (ns x : List ℤ) (hms : floatBasisOK ms = true)
    (hn : Fl.Reduced ms ns) (hx : Fl.Reduced ms x) :
    ((ms.zip ns).zip x).length ≤ 2 ^ 16 ∧
      ∀ p ∈ (ms.zip ns).zip x, 1 ≤ p.1.1 ∧ p.1.1 < 2 ^ 64 ∧
        (0 ≤ p.1.2 ∧ p.1.2 < (p.1.1 : ℤ)) ∧ 0 ≤ p.2 ∧ p.2 < (p.1.1 : ℤ) := by
  obtain ⟨h1, h2⟩ := floatBasisOK_weak ms hms
  rw [reduced_def] at hn hx
  refine ⟨((length_zip_le _ _).trans (length_zip_le _ _)).trans h1, fun p hp => ?_⟩
  obtain ⟨⟨a, b⟩, c⟩ := p
  have hab : (a, b) ∈ ms.zip ns := (List.of_mem_zip hp).1
  have := h2 a (List.of_mem_zip hab).1
  exact ⟨this.1, this.2, hn _ hab, hx _ (mem_zip_zip ms ns x a b c hp)⟩

theorem nuSw_tol (A : Arith) (hA : Conforms A) (qs : List ℕ) (y : List ℤ)
    (hqs : floatBasisOK qs = true) (hy : Fl.Reduced qs y) :
    |Fl.nuSw A qs y - Fl.exactSw qs y| ≤
      (BudgetBFV.doubleSw qs.length : ℚ) / BudgetBFV.floatDen := by
  obtain ⟨hlen, hl⟩ := sw_hyps qs y hqs hy
  obtain ⟨h, -, -⟩ := nuSw_err A hA (qs.zip y) hlen hl
  rw [nuSw_def, exactSw_def]
  refine h.trans ?_
  rw [doubleSw_def, floatDen_def]
  have hk : ((qs.zip y).length : ℚ) ≤ (qs.length : ℚ) := by
    exact_mod_cast length_zip_le qs y
  have h0 : (0 : ℚ) ≤ ((qs.zip y).length : ℚ) := Nat.cast_nonneg _
  have hmul : ((qs.zip y).length : ℚ) * (((qs.zip y).length : ℚ) + 5) ≤
      (qs.length : ℚ) * ((qs.length : ℚ) + 5) :=
    mul_le_mul hk (by linarith) (by linarith) (by linarith)
  have e : (((qs.length * (qs.length + 5) : ℕ) : ℚ)) / ((2 ^ 53 : ℕ) : ℚ) =
      (qs.length : ℚ) * ((qs.length : ℚ) + 5) * u := by
    unfold u; push_cast; ring
  rw [e]
  exact mul_le_mul_of_nonneg_right hmul u_pos.le

theorem nuSr_tol (A : Arith) (hA : Conforms A) (ms : List ℕ) (ns x : List ℤ)
    (hms : floatBasisOK ms = true) (hn : Fl.Reduced ms ns) (hx : Fl.Reduced ms x) :
    |Fl.nuSr A ms ns x - Fl.exactSr ms ns x| ≤
      (BudgetBFV.doubleSr ms : ℚ) / BudgetBFV.floatDen := by
  obtain ⟨hlen, hl⟩ := sr_hyps ms ns x hms hn hx
  obtain ⟨h, -, -, -⟩ := nuSr_err A hA ((ms.zip ns).zip x) hlen hl
  rw [nuSr_def, exactSr_def]
  refine h.trans ?_
  rw [doubleSr_def, floatDen_def]
  have hk : (((ms.zip ns).zip x).length : ℚ) ≤ (ms.length : ℚ) := by
    exact_mod_cast (length_zip_le _ x).trans (length_zip_le ms ns)
  have h0 : (0 : ℚ) ≤ (((ms.zip ns).zip x).length : ℚ) := Nat.cast_nonneg _
  have hM := sum_fst_fst_zip_le ms ns x
  have hM0 : (0 : ℚ) ≤ (((ms.zip ns).zip x).map fun p => (p.1.1 : ℚ)).sum :=
    List.sum_nonneg fun v hv => by
      obtain ⟨b, _, rfl⟩ := List.mem_map.mp hv
      exact Nat.cast_nonneg _
  have hmul : ((((ms.zip ns).zip x).length : ℚ) + 6) *
        (1 + (((ms.zip ns).zip x).map fun p => (p.1.1 : ℚ)).sum) ≤
      ((ms.length : ℚ) + 6) * (1 + ((ms.sum : ℕ) : ℚ)) :=
    mul_le_mul (by linarith) (by linarith) (by linarith) (by linarith)
  have e : ((((ms.length + 6) * (1 + ms.sum) : ℕ) : ℚ)) / ((2 ^ 53 : ℕ) : ℚ) =
      ((ms.length : ℚ) + 6) * (1 + ((ms.sum : ℕ) : ℚ)) * u := by
    unfold u; push_cast; ring
  rw [e]
  exact mul_le_mul_of_nonneg_right hmul u_pos.le

theorem nu_range (A : Arith) (hA : Conforms A) (ms : List ℕ) (ns x : List ℤ)
    (hms : floatBasisOK ms = true) (hn : Fl.Reduced ms ns) (hx : Fl.Reduced ms x) :
    (0 ≤ Fl.nuSw A ms x ∧ Fl.nuSw A ms x < 2 ^ 17) ∧
    (0 ≤ Fl.nuSr A ms ns x ∧ Fl.nuSr A ms ns x < 2 ^ 81) := by
  have hu := u_pos
  constructor
  · obtain ⟨hlen, hl⟩ := sw_hyps ms x hms hx
    obtain ⟨h1, h2, h3⟩ := nuSw_err A hA (ms.zip x) hlen hl
    rw [nuSw_def]
    refine ⟨le_trans (by norm_num) h2, ?_⟩
    have hn : ((ms.zip x).length : ℚ) ≤ 2 ^ 16 := by exact_mod_cast hlen
    have hn0 : (0 : ℚ) ≤ ((ms.zip x).length : ℚ) := Nat.cast_nonneg _
    have htol : ((ms.zip x).length : ℚ) * (((ms.zip x).length : ℚ) + 5) * u ≤ 1 := by
      have a1 : ((ms.zip x).length : ℚ) * (((ms.zip x).length : ℚ) + 5) ≤ 2 ^ 16 * (2 ^ 16 + 5) :=
        mul_le_mul hn (by linarith) (by linarith) (by norm_num)
      have a2 := mul_le_mul_of_nonneg_right a1 hu.le
      have a3 : (2 : ℚ) ^ 16 * (2 ^ 16 + 5) * u ≤ 1 := by unfold u; norm_num
      linarith
    have := (abs_le.mp h1).2
    have b : (1 : ℚ) / 2 + 2 ^ 16 + 1 < 2 ^ 17 := by norm_num
    linarith
  · obtain ⟨hlen, hl⟩ := sr_hyps ms ns x hms hn hx
    obtain ⟨h1, h2, h3, h4⟩ := nuSr_err A hA ((ms.zip ns).zip x) hlen hl
    rw [nuSr_def]
    refine ⟨le_trans (by norm_num) h2, ?_⟩
    have hn : (((ms.zip ns).zip x).length : ℚ) ≤ 2 ^ 16 := by exact_mod_cast hlen
    have hn0 : (0 : ℚ) ≤ (((ms.zip ns).zip x).length : ℚ) := Nat.cast_nonneg _
    generalize (((ms.zip ns).zip x).map fun p => (p.1.1 : ℚ)).sum = M at h1 h3 h4
    have hM : M ≤ 2 ^ 80 := by
      have : (((ms.zip ns).zip x).length : ℚ) * 2 ^ 64 ≤ 2 ^ 16 * 2 ^ 64 :=
        mul_le_mul_of_nonneg_right hn (by positivity)
      have e : (2 : ℚ) ^ 16 * 2 ^ 64 = 2 ^ 80 := by norm_num
      linarith
    have hM0 : 0 ≤ 1 + M := by
      have : 0 ≤ (((ms.zip ns).zip x).length : ℚ) * 2 ^ 64 := by positivity
      by_contra hneg
      rw [not_le] at hneg
      -- the error bound would be negative
      have a := abs_nonneg (List.foldl
        (fun s (p : (ℕ × ℤ) × ℤ) => A.mulAdd s (Fl.frac A p.1.2.toNat p.1.1) (A.ofNat p.2.toNat))
        (1 / 2) ((ms.zip ns).zip x) - (1 / 2 + (((ms.zip ns).zip x).map
          fun p => (p.2 : ℚ) * (p.1.2 : ℚ) / (p.1.1 : ℚ)).sum))
      have b : ((((ms.zip ns).zip x).length : ℚ) + 6) * (1 + M) * u < 0 :=
        mul_neg_of_neg_of_pos (mul_neg_of_pos_of_neg (by linarith) hneg) hu
      linarith
    have htol : ((((ms.zip ns).zip x).length : ℚ) + 6) * (1 + M) * u ≤ 2 ^ 46 := by
      have a1 : ((((ms.zip ns).zip x).length : ℚ) + 6) * (1 + M) ≤ (2 ^ 16 + 6) * (1 + 2 ^ 80) :=
        mul_le_mul (by linarith) (by linarith) hM0 (by norm_num)
      have a2 := mul_le_mul_of_nonneg_right a1 hu.le
      have a3 : ((2 : ℚ) ^ 16 + 6) * (1 + 2 ^ 80) * u ≤ 2 ^ 46 := by unfold u; norm_num
      linarith
    have := (abs_le.mp h1).2
    have b : (1 : ℚ) / 2 + 2 ^ 80 + 2 ^ 46 < 2 ^ 81 := by norm_num
    linarith

theorem nuSw_index (A : Arith) (hA : Conforms A) (qs : List ℕ) (y : List ℤ)
    (hqs : floatBasisOK qs = true) (hy : Fl.Reduced qs y) :
    0 ≤ ⌊Fl.nuSw A qs y⌋ ∧ ⌊Fl.nuSw A qs y⌋ ≤ (qs.length : ℤ) := by
  have hu := u_pos
  obtain ⟨hlen, hl⟩ := sw_hyps qs y hqs hy
  obtain ⟨h1, h2, h3⟩ := nuSw_err A hA (qs.zip y) hlen hl
  rw [nuSw_def]
  refine ⟨Int.floor_nonneg.mpr (le_trans (by norm_num) h2), ?_⟩
  have hn : ((qs.zip y).length : ℚ) ≤ 2 ^ 16 := by exact_mod_cast hlen
  have hn0 : (0 : ℚ) ≤ ((qs.zip y).length : ℚ) := Nat.cast_nonneg _
  have htol : ((qs.zip y).length : ℚ) * (((qs.zip y).length : ℚ) + 5) * u ≤ 1 / 4 := by
    have a1 : ((qs.zip y).length : ℚ) * (((qs.zip y).length : ℚ) + 5) ≤ 2 ^ 16 * (2 ^ 16 + 5) :=
      mul_le_mul hn (by linarith) (by linarith) (by norm_num)
    have a2 := mul_le_mul_of_nonneg_right a1 hu.le
    have a3 : (2 : ℚ) ^ 16 * (2 ^ 16 + 5) * u ≤ 1 / 4 := by unfold u; norm_num
    linarith
  have hk : ((qs.zip y).length : ℚ) ≤ (qs.length : ℚ) := by
    exact_mod_cast length_zip_le qs y
  have hub := (abs_le.mp h1).2
  have hlt : (qs.zip y).foldl
      (fun s p => A.mulAdd s (A.ofNat p.2.toNat) (Fl.qInv A p.1)) (1 / 2) <
      (((qs.length : ℤ) + 1 : ℤ) : ℚ) := by
    push_cast
    linarith
  have := Int.floor_lt.mpr hlt
  omega

theorem sum_zipWith_mul_le :
    ∀ (x c : List ℕ), (∀ v ∈ x, v < 2 ^ 60) → (∀ v ∈ c, v < 2 ^ 60) →
      (List.zipWith (· * ·) x c).sum ≤ x.length * 2 ^ 120
  | [], _, _, _ => by simp
  | _ :: _, [], _, _ => by simp
  | a :: x, b :: c, hx, hc => by
    have ih := sum_zipWith_mul_le x c (fun v hv => hx v (List.mem_cons_of_mem _ hv))
      (fun v hv => hc v (List.mem_cons_of_mem _ hv))
    have ha := hx a List.mem_cons_self
    have hb := hc b List.mem_cons_self
    have hab : a * b ≤ 2 ^ 60 * 2 ^ 60 := Nat.mul_le_mul ha.le hb.le
    simp only [List.zipWith_cons_cons, List.sum_cons, List.length_cons]
    have e : (2 : ℕ) ^ 60 * 2 ^ 60 = 2 ^ 120 := by norm_num
    rw [e] at hab
    rw [Nat.add_mul, Nat.one_mul]
    omega

theorem acc_no_overflow (ms : List ℕ) (hms : floatBasisOK ms = true) (x c : List ℕ)
    (hlen : x.length ≤ ms.length) (hx : ∀ v ∈ x, v < 2 ^ 60) (hc : ∀ v ∈ c, v < 2 ^ 60)
    (xo co : ℕ) (hxo : xo < 2 ^ 60) (hco : co < 2 ^ 60) :
    (List.zipWith (· * ·) x c).sum + xo * co < 2 ^ 128 := by
  obtain ⟨h1, -⟩ := (floatBasisOK_iff' ms).mp hms
  have hs := sum_zipWith_mul_le x c hx hc
  have hab : xo * co ≤ 2 ^ 60 * 2 ^ 60 := Nat.mul_le_mul hxo.le hco.le
  have e : (2 : ℕ) ^ 60 * 2 ^ 60 = 2 ^ 120 := by norm_num
  rw [e] at hab
  have hl : x.length * 2 ^ 120 ≤ 128 * 2 ^ 120 := Nat.mul_le_mul_right _ (hlen.trans h1)
  have e2 : (128 : ℕ) * 2 ^ 120 + 2 ^ 120 < 2 ^ 128 := by norm_num
  omega

theorem floatSums_def (A : Arith) :
    Fl.floatSums A =
      { sw := fun qs y => ⌊Fl.nuSw A qs y⌋, sr := fun ms ns x => ⌊Fl.nuSr A ms ns x⌋ } :=
  rfl

theorem sumsOK_def (S : Fl.Sums) :
    Fl.SumsOK S =
      ((∀ (qs : List ℕ) (y : List ℤ), floatBasisOK qs = true → Fl.Reduced qs y →
        ∃ s : ℚ, S.sw qs y = ⌊s⌋ ∧
          |s - Fl.exactSw qs y| ≤ (BudgetBFV.doubleSw qs.length : ℚ) / BudgetBFV.floatDen) ∧
      (∀ (ms : List ℕ) (ns x : List ℤ), floatBasisOK ms = true → Fl.Reduced ms ns →
        Fl.Reduced ms x →
        ∃ s : ℚ, S.sr ms ns x = ⌊s⌋ ∧
          |s - Fl.exactSr ms ns x| ≤ (BudgetBFV.doubleSr ms : ℚ) / BudgetBFV.floatDen)) :=
  rfl

theorem floatSums_ok (A : Arith) (hA : Conforms A) : Fl.SumsOK (Fl.floatSums A) := by
  rw [sumsOK_def, floatSums_def]
  exact ⟨fun qs y hqs hy => ⟨_, rfl, nuSw_tol A hA qs y hqs hy⟩,
    fun ms ns x hms hn hx => ⟨_, rfl, nuSr_tol A hA ms ns x hms hn hx⟩⟩

example : type_of% @Validation.BFVMul.nuSw_tol = type_of% @Challenge.BFVMul.nuSw_tol := rfl
example : type_of% @Validation.BFVMul.nuSr_tol = type_of% @Challenge.BFVMul.nuSr_tol := rfl
example : type_of% @Validation.BFVMul.nuSw_index = type_of% @Challenge.BFVMul.nuSw_index := rfl
example : type_of% @Validation.BFVMul.acc_no_overflow =
    type_of% @Challenge.BFVMul.acc_no_overflow := rfl
example : type_of% @Validation.BFVMul.nu_range = type_of% @Challenge.BFVMul.nu_range := rfl
example : type_of% @Validation.BFVMul.floatSums_ok = type_of% @Challenge.BFVMul.floatSums_ok :=
  rfl
example : type_of% @Validation.BFVMul.exact_conforms =
    type_of% @Challenge.BFVMul.exact_conforms := rfl

end Validation.BFVMul
