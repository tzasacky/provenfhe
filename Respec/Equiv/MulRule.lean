import Respec.Equiv.Rules
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Data.List.GetD

/-!
# Respec.Equiv.MulRule — B's `MulRule` for operands with any numbers of components

In this module `A` is the specification (`Spec`, `Challenge`) and `B` the independent
re-specification (`Respec`); "A's `x`" and "B's `x`" are the corresponding definitions of each.

## Verdicts (PROVED, no `sorry`)

* `phase_mulTensor` : for lists `a`, `b` of any lengths (empty ones included),
  `phase x (mulTensor a b) = phase x a * phase x b`: B's index-based tensor product
  (`mulTensor`, coefficient `k` the sum over `i ≤ k` of `a[i]·b[k−i]`) has the product of the
  phases as its phase. Proved through `Polynomial` (`listPoly c` has coefficient list `c`, its
  value at `x` is the phase, and `Polynomial.coeff_mul` is the Cauchy product). This is B's
  counterpart of A's `Validation.Source.phase_tensorParts` (A's recursive `tensorParts`); the two
  tensor products are not compared entry by entry here.
* `mulRule_general` : **B's `MulRule N t Q` holds for all `N`, `t`, `Q`** (formerly open): from `phase_mulTensor` and A's `Validation.Scheme.bgvEncrypts_of_phase`,
  `abs_coeff_mul_le_N` (the same two steps as A's 2×2 `bgvEncrypts_tensor`).
-/

namespace Respec.Equiv

open Spec Spec.NPoly Spec.Scheme Respec Respec.BGV Respec.Noise Validation.Ring Validation.Scheme

variable {N : ℕ}

/-- A left fold of `+` over a mapped range is the `Finset.range` sum. -/
theorem foldl_map_range_eq_sum {M : Type} [AddCommMonoid M] (f : ℕ → M) (n : ℕ) :
    ((List.range n).map f).foldl (· + ·) 0 = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.foldl_append, ih, Finset.sum_range_succ]
    simp

section
variable [NeZero N] {Q : ℕ}

/-- The polynomial in one variable over `R_Q` whose coefficient list is `c`. -/
noncomputable def listPoly (c : List (Poly Q N)) : Polynomial (Poly Q N) :=
  ∑ i ∈ Finset.range c.length, Polynomial.monomial i (c.getD i 0)

theorem coeff_listPoly (c : List (Poly Q N)) (k : ℕ) : (listPoly c).coeff k = c.getD k 0 := by
  unfold listPoly
  rw [Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_monomial, Finset.sum_ite_eq', Finset.mem_range]
  split_ifs with h
  · rfl
  · rw [List.getD_eq_default _ _ (by omega)]

/-- The phase as a sum over the components. -/
theorem phase_eq_sum (x : Poly Q N) : ∀ c : List (Poly Q N),
    Scheme.phase x c = ∑ i ∈ Finset.range c.length, c.getD i 0 * x ^ i
  | [] => by simp [Scheme.phase]
  | c :: cs => by
    rw [List.length_cons, Finset.sum_range_succ', phase_cons, phase_eq_sum x cs, Finset.mul_sum]
    simp only [List.getD_cons_succ, List.getD_cons_zero, pow_zero, mul_one]
    rw [add_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    ring

theorem eval_listPoly (x : Poly Q N) (c : List (Poly Q N)) :
    (listPoly c).eval x = Scheme.phase x c := by
  unfold listPoly
  rw [Polynomial.eval_finsetSum, phase_eq_sum]
  simp only [Polynomial.eval_monomial]

theorem natDegree_listPoly_le (c : List (Poly Q N)) : (listPoly c).natDegree ≤ c.length - 1 := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro k hk
  rw [coeff_listPoly, List.getD_eq_default _ _ (by omega)]

omit [NeZero N] in
theorem length_mulTensor (a b : List (Poly Q N)) :
    (mulTensor a b).length = a.length + b.length - 1 := by
  simp [mulTensor]

/-- Component `k` of B's tensor product is the Cauchy coefficient. -/
theorem getD_mulTensor (a b : List (Poly Q N)) (k : ℕ) (hk : k < a.length + b.length - 1) :
    (mulTensor a b).getD k 0 = ∑ i ∈ Finset.range (k + 1), a.getD i 0 * b.getD (k - i) 0 := by
  unfold mulTensor
  rw [forceAll_eq, List.getD_eq_getElem _ _ (by simpa using hk), List.getElem_map,
    List.getElem_range, psum_eq, foldl_map_range_eq_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
  cases a[i]? <;> cases b[k - i]? <;> simp

/-- **The phase of B's tensor product is the product of the phases**, for any numbers of
components. -/
theorem phase_mulTensor (x : Poly Q N) (a b : List (Poly Q N)) :
    Scheme.phase x (mulTensor a b) = Scheme.phase x a * Scheme.phase x b := by
  rw [phase_eq_sum x (mulTensor a b), length_mulTensor]
  have hL : ∑ k ∈ Finset.range (a.length + b.length - 1), (mulTensor a b).getD k 0 * x ^ k =
      ∑ k ∈ Finset.range (a.length + b.length - 1), (listPoly a * listPoly b).coeff k * x ^ k := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [getD_mulTensor a b k (Finset.mem_range.mp hk), Polynomial.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    simp only [coeff_listPoly]
  rw [hL, ← eval_listPoly x a, ← eval_listPoly x b, ← Polynomial.eval_mul]
  rcases Nat.eq_zero_or_pos a.length with ha | ha
  · have : listPoly a = 0 := by unfold listPoly; rw [ha]; simp
    simp [this]
  rcases Nat.eq_zero_or_pos b.length with hb | hb
  · have : listPoly b = 0 := by unfold listPoly; rw [hb]; simp
    simp [this]
  refine (Polynomial.eval_eq_sum_range' ?_ x).symm
  have h1 := Polynomial.natDegree_mul_le (p := listPoly a) (q := listPoly b)
  have h2 := natDegree_listPoly_le a
  have h3 := natDegree_listPoly_le b
  omega

end

/-- **B's `MulRule`, for operands with any numbers of components.** -/
theorem mulRule_general (N t Q : ℕ) : MulRule N t Q := by
  intro s c1 c2 m1 m2 B1 B2 h1 h2 hQ
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    rw [← bgvEncrypts_iff] at h1 h2 ⊢
    refine ⟨?_, by simp [normInf_unfold]⟩
    exact eq_of_N_zero rfl _ _
  haveI : NeZero N := ⟨hN.ne'⟩
  rw [← bgvEncrypts_iff] at h1 h2 ⊢
  refine bgvEncrypts_of_phase (centeredPhase s c1 * centeredPhase s c2) ?_ ?_ hQ ?_
  · rw [ofInt_mul, ← phase_eq_ofInt_centeredPhase, ← phase_eq_ofInt_centeredPhase, phase_mulTensor]
  · intro i
    have := abs_coeff_mul_le_N _ _ (B1 : ℤ) (B2 : ℤ) (BGVEncrypts.bound h1) (BGVEncrypts.bound h2) i
    simp only [mulBound]
    push_cast
    exact this
  · rw [ofInt_mul, BGVEncrypts.msg h1, BGVEncrypts.msg h2]

end Respec.Equiv
