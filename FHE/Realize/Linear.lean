import FHE.Pin.Algo
import Validation.Source

/-!
# FHE.Realize.Linear — the other bit-exact functions of the harness are the locked textbook ones

Two `algo.*` checks of the conformance harness (`harness/openfhe-pin/algo/README.md`) run a Lean
function that is not literally the one a locked contract statement names:

* `algo.tensorN` (products with other numbers of components than `2 × 2`) runs
  `FHE.Pin.Algo.tensorGen` (a convolution written for the harness). `tensorGen_eq_tensorParts`:
  on operands with at least one component each (what `Spec.Source.step` requires of `mul`), it
  is `Challenge.Source.tensorParts`, which `Challenge.Trace.stepOK_mul_tensor` and
  `stepOK_square_textbook` name.
* `algo.negate` compares `-·` componentwise. The frontend maps `EvalNegate` to `mulConst … (−1)`
  (`FHE.Check.Ops`), whose locked contract `Challenge.Trace.stepOK_mulConst_textbook` names
  `ca.map ((-1 : ℤ) • ·)`. `negate_eq_mulConst`: the two are equal.

This file is not imported by `Validation` (it imports the harness's trace walker); the gate builds,
axiom-scans and kernel-replays it with the rest of `FHE`.
-/

namespace FHE.Realize

open Finset Spec Spec.NPoly Validation.Ring Validation.Scheme Validation.Source

variable {N : ℕ}

/-- Negation is multiplication by the integer `−1`, componentwise. -/
theorem negate_eq_mulConst (ca : List (IntPoly N)) :
    ca.map (fun c => -c) = ca.map (((-1 : ℤ)) • ·) := by
  congr 1
  funext c
  ext k
  show -c.coeff k = -1 * c.coeff k
  ring

variable [NeZero N]

theorem zero_add' (a : IntPoly N) : 0 + a = a := by ext; simp
theorem add_zero' (a : IntPoly N) : a + 0 = a := by ext; simp

theorem getD_zero_nil (k : ℕ) : ([] : List (IntPoly N)).getD k 0 = 0 := by simp

/-- Coefficient-list view of the padded sum. -/
theorem padZip_add_getD : ∀ (xs ys : List (IntPoly N)) (k : ℕ),
    (Challenge.Source.padZip (· + ·) xs ys).getD k 0 = xs.getD k 0 + ys.getD k 0
  | [], ys, k => by
      rw [padZip_nil, getD_zero_nil, zero_add', List.getD_eq_getElem?_getD, List.getElem?_map,
        List.getD_eq_getElem?_getD]
      cases ys[k]? with
      | none => rfl
      | some y => exact zero_add' y
  | x :: xs, [], k => by
      rw [padZip_cons_nil, getD_zero_nil, add_zero', List.getD_eq_getElem?_getD, List.getElem?_map,
        List.getD_eq_getElem?_getD]
      cases (x :: xs)[k]? with
      | none => rfl
      | some y => exact add_zero' y
  | x :: xs, y :: ys, 0 => by rw [padZip_cons_cons]; rfl
  | x :: xs, y :: ys, k + 1 => by
      rw [padZip_cons_cons]
      exact padZip_add_getD xs ys k

theorem map_mul_getD (c : IntPoly N) (ds : List (IntPoly N)) (k : ℕ) :
    (ds.map (c * ·)).getD k 0 = if k < ds.length then c * ds.getD k 0 else 0 := by
  split_ifs with h
  · simp [List.getD_eq_getElem?_getD, h]
  · simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega : ds.length ≤ k)]

/-- Coefficient `k` of the tensor product: `Σᵢ cᵢ · d_{k−i}` over the defined indices. -/
theorem tensorParts_getD : ∀ (cs ds : List (IntPoly N)) (k : ℕ),
    (Challenge.Source.tensorParts cs ds).getD k 0 =
      ∑ i ∈ range cs.length,
        if i ≤ k ∧ k - i < ds.length then cs.getD i 0 * ds.getD (k - i) 0 else 0
  | [], ds, k => by rw [tensorParts_nil]; simp
  | c :: cs, ds, k => by
      rw [tensorParts_cons, padZip_add_getD, map_mul_getD, List.length_cons,
        Finset.sum_range_succ']
      cases k with
      | zero =>
        have h0 : ∀ i ∈ range cs.length,
            (if i + 1 ≤ 0 ∧ 0 - (i + 1) < ds.length then
              (c :: cs).getD (i + 1) 0 * ds.getD (0 - (i + 1)) 0 else 0) = (0 : IntPoly N) := by
          intro i _; rw [if_neg (by omega)]
        rw [Finset.sum_congr rfl h0, Finset.sum_const_zero]
        show _ + (0 : IntPoly N) = 0 + _
        rw [add_zero', zero_add']
        simp
      | succ k =>
        rw [show (0 :: Challenge.Source.tensorParts cs ds).getD (k + 1) 0 =
          (Challenge.Source.tensorParts cs ds).getD k 0 by simp, tensorParts_getD cs ds k]
        have h1 : ∀ i ∈ range cs.length,
            (if i + 1 ≤ k + 1 ∧ k + 1 - (i + 1) < ds.length then
              (c :: cs).getD (i + 1) 0 * ds.getD (k + 1 - (i + 1)) 0 else 0) =
            (if i ≤ k ∧ k - i < ds.length then cs.getD i 0 * ds.getD (k - i) 0 else 0) := by
          intro i _
          have e : k + 1 - (i + 1) = k - i := by omega
          by_cases h : i ≤ k ∧ k - i < ds.length
          · rw [if_pos (by omega), if_pos h, e]; simp
          · rw [if_neg (by omega), if_neg h]
        rw [Finset.sum_congr rfl h1]
        simp only [zero_le, true_and, Nat.sub_zero, List.getD_cons_zero]
        split_ifs <;> simp [add_comm]

/-- A conditional fold is a conditional sum. -/
theorem foldl_ite_eq_sum (n : ℕ) (p : ℕ → Prop) [DecidablePred p] (g : ℕ → IntPoly N)
    (init : IntPoly N) :
    (List.range n).foldl (fun acc i => if p i then acc + g i else acc) init =
      init + ∑ i ∈ range n, if p i then g i else 0 := by
  induction n with
  | zero => simp [add_zero']
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, ih, Finset.sum_range_succ]
    simp only [List.foldl_cons, List.foldl_nil]
    split_ifs <;> simp [add_assoc]

/-- A conditional fold of array additions is a conditional sum. -/
theorem foldl_ite_addArr (n : ℕ) (p : ℕ → Prop) [DecidablePred p] (g : ℕ → Array ℤ)
    (init : Array ℤ) :
    FHE.Pin.ofArr (N := N)
        ((List.range n).foldl (fun acc i => if p i then FHE.Pin.addArr N acc (g i) else acc) init) =
      FHE.Pin.ofArr (N := N) init + ∑ i ∈ range n, if p i then FHE.Pin.ofArr (N := N) (g i) else 0 := by
  induction n with
  | zero => simp [add_zero']
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, Finset.sum_range_succ]
    simp only [List.foldl_cons, List.foldl_nil]
    split_ifs
    · rw [FHE.Pin.ofArr_addArr, ih]; simp [add_assoc]
    · rw [ih]; simp

theorem getD_of_lt {α : Type} (l : List α) (d : α) {k : ℕ} (h : k < l.length) :
    l.getD k d = l[k] := by
  simp [List.getD_eq_getElem?_getD, h]

/-- **The harness's convolution is the locked tensor product** (both operands nonempty). -/
theorem tensorGen_eq_tensorParts (cs ds : List (IntPoly N)) (hc : 1 ≤ cs.length)
    (hd : 1 ≤ ds.length) :
    FHE.Pin.Algo.tensorGen cs ds = Challenge.Source.tensorParts cs ds := by
  have hne : (cs.isEmpty || ds.isEmpty) = false := by
    cases cs <;> cases ds <;> simp_all
  have hlen : (FHE.Pin.Algo.tensorGen cs ds).length = cs.length + ds.length - 1 := by
    unfold FHE.Pin.Algo.tensorGen; rw [hne]; simp
  apply List.ext_getElem
  · rw [hlen, length_tensorParts cs ds hc hd]
  · intro k h1 h2
    rw [← getD_of_lt _ 0 h1, ← getD_of_lt _ 0 h2, tensorParts_getD]
    unfold FHE.Pin.Algo.tensorGen
    rw [hne]
    rw [hlen] at h1
    simp only [Bool.false_eq_true, ite_false]
    rw [getD_of_lt _ 0 (by simpa using h1), List.getElem_map, List.getElem_map, List.getElem_range,
      foldl_ite_addArr, FHE.Pin.ofArr_replicate_zero, zero_add']
    refine Finset.sum_congr rfl fun i _ => ?_
    split_ifs <;> simp
