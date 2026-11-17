import Respec.Noise
import Spec.Budget
import Validation.Budget.Basic
import Mathlib.Data.List.GetD
import Mathlib.Algebra.Order.Floor.Semifield

/-!
# Respec.Equiv.KsBound — item 6: the key-switching noise bound

In this module `A` is the specification (`Spec`, `Challenge`) and `B` the independent
re-specification (`Respec`); "A's `x`" and "B's `x`" are the corresponding definitions of each.

A: `Spec.Budget.ksBoundAt P lay ℓ =
  ⌊(N·B_k·Σⱼ wⱼ + t·F·(1 + N·B_s)) / (2P)⌋` with `wⱼ = ℓⱼ·Qⱼ`, `F = k·P` (centred) or
`wⱼ = 2ℓⱼ(Qⱼ − 1)`, `F = 2k(P − 1)` (canonical); `B_k = P.keyNoise` bounds the key error `t·e`.
B: `Respec.Noise.ksAddedBound c N t B_s B_e digits ps =
  (t·N·B_e·Σⱼ bconvBound2 c digitⱼ + t·bconvBound2 c ps·(1 + N·B_s)) / (2P)` (a rational, no floor),
`B_e` bounds `e` (factor `t` excluded), `bconvBound2 .centred qs = |qs|·∏qs`,
`bconvBound2 .canonical qs = Σᵢ 2(qᵢ − 1)·Q̂ᵢ`.

## Verdicts (PROVED)

* `bconvBound2_centred` : `bconvBound2 .centred qs = qs.length * qs.prod` (any list).
* `bconvBound2_canonical_le` : `bconvBound2 .canonical qs ≤ 2·(|qs|·(∏qs − 1))` for positive
  moduli, with equality for one modulus (`bconvBound2_canonical_single`), strict for ≥ 2 moduli.
* **Centred: EQUAL UP TO THE FLOOR, under `keyNoise = t·Be`** (`ksBoundAt_centred_eq`): for every
  usable layout (`Σ sizes = ℓ ≤ L`) A's bound is exactly `⌊B's bound⌋₊`, with B's digits the
  layout's slices of the chain (`digitsB`) and B's `ps` the special primes. The floor is sound
  (the error is an integer). The constants agree exactly: the `t` that B writes in front of `N·B_e`
  is inside A's `B_k`; the rounding term is `t·(k/2)·(1 + N·B_s)` on both sides.
* **Canonical: A ≥ B** (`ksBoundAt_canonical_ge`): `⌊B's bound⌋₊ ≤` A's bound for every layout.
  A's canonical weights `2ℓⱼ(Qⱼ − 1)` and `2k(P − 1)` over-approximate the exact worst case
  `Σᵢ 2(qᵢ − 1)·Q̂ᵢ` of a canonical fast base conversion; they coincide only for single-limb digits
  and one special prime. Witness (`canonical_strict`, kernel-checked): B's test parameters
  (`N = 4`, `t = 5`, chain `97·113·193`, digits `{97,113},{193}`, `P = 257·337`, `B_e = 2`,
  i.e. `keyNoise = 10`): A = 60, B = 5191760/86609 ≈ 59.94. Sound but looser; not an error.
  (Centred at the same parameters: A = 30 = ⌊2607525/86609⌋.)
-/

namespace Respec.Equiv

open Spec Spec.Budget Respec Respec.Noise

/-! ### List sums -/

theorem lsum_eq_sum (l : List ℕ) : lsum l = l.sum := by
  unfold lsum
  suffices ∀ a, l.foldl (· + ·) a = a + l.sum by simpa using this 0
  induction l with
  | nil => intro a; simp
  | cons x l ih => intro a; rw [List.foldl_cons, ih, List.sum_cons, Nat.add_assoc]

theorem sum_zipIdx (F : ℕ → ℕ → ℕ) : ∀ (l : List ℕ) (n : ℕ),
    ((l.zipIdx n).map fun p => F p.1 p.2).sum =
      ∑ i ∈ Finset.range l.length, F (l.getD i 0) (n + i)
  | [], n => by simp
  | a :: l, n => by
    rw [List.zipIdx_cons, List.map_cons, List.sum_cons, sum_zipIdx F l (n + 1), List.length_cons,
      Finset.sum_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero, Nat.add_zero]
    rw [Nat.add_comm]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1; omega

theorem bconvBound2_eq (c : Lift) (qs : List ℕ) :
    bconvBound2 c qs = ∑ i ∈ Finset.range qs.length, c.bound2 (qs.getD i 0) * (qs.eraseIdx i).prod := by
  unfold bconvBound2
  rw [lsum_eq_sum, sum_zipIdx (fun a i => c.bound2 a * (qs.eraseIdx i).prod) qs 0]
  simp

/-- `bconvBound2 .centred qs = |qs|·∏ qs`. -/
theorem bconvBound2_centred (qs : List ℕ) : bconvBound2 .centred qs = qs.length * qs.prod := by
  rw [bconvBound2_eq]
  rw [Finset.sum_congr rfl (g := fun _ => qs.prod) fun i hi => by
    have hi' : i < qs.length := Finset.mem_range.mp hi
    simp only [Lift.bound2]
    rw [List.getD_eq_getElem (hn := hi')]
    exact Validation.Budget.getElem_mul_prod_eraseIdx qs i hi']
  simp

theorem prod_eraseIdx_pos (qs : List ℕ) (hpos : ∀ q ∈ qs, 0 < q) (i : ℕ) :
    0 < (qs.eraseIdx i).prod :=
  List.prod_pos fun x hx => hpos x (List.mem_of_mem_eraseIdx hx)

/-- The canonical fast-base-conversion weight is at most A's `2·|qs|·(∏qs − 1)`. -/
theorem bconvBound2_canonical_le (qs : List ℕ) (hpos : ∀ q ∈ qs, 0 < q) :
    bconvBound2 .canonical qs ≤ 2 * (qs.length * (qs.prod - 1)) := by
  rw [bconvBound2_eq]
  calc ∑ i ∈ Finset.range qs.length, Lift.bound2 .canonical (qs.getD i 0) * (qs.eraseIdx i).prod
      ≤ ∑ _i ∈ Finset.range qs.length, 2 * (qs.prod - 1) := by
        refine Finset.sum_le_sum fun i hi => ?_
        have hi' : i < qs.length := Finset.mem_range.mp hi
        simp only [Lift.bound2]
        rw [List.getD_eq_getElem (hn := hi')]
        have h1 := Validation.Budget.getElem_mul_prod_eraseIdx qs i hi'
        have h2 := prod_eraseIdx_pos qs hpos i
        have h3 : 0 < qs[i] := hpos _ (List.getElem_mem _)
        have : (qs[i] - 1) * (qs.eraseIdx i).prod ≤ qs.prod - 1 := by
          rw [Nat.sub_mul, one_mul, h1]; omega
        calc 2 * (qs[i] - 1) * (qs.eraseIdx i).prod = 2 * ((qs[i] - 1) * (qs.eraseIdx i).prod) := by ring
          _ ≤ 2 * (qs.prod - 1) := Nat.mul_le_mul_left _ this
    _ = 2 * (qs.length * (qs.prod - 1)) := by simp; ring

theorem bconvBound2_canonical_single (q : ℕ) : bconvBound2 .canonical [q] = 2 * (1 * ([q].prod - 1)) := by
  simp [bconvBound2, lsum, Lift.bound2]

/-! ### The layout's digits as B's lists -/

/-- The digits of a layout at level `ℓ`, as lists of primes (B's `digits` argument). -/
def digitsB (P : FullParams) (lay : KSLayout) (ℓ : ℕ) : List (List ℕ) :=
  (List.range (lay.sizes ℓ).length).map fun j =>
    ((P.src.qs.take ℓ).drop ((lay.sizes ℓ).take j).sum).take ((lay.sizes ℓ).getD j 0)

theorem digitModuli_eq_B (P : FullParams) (lay : KSLayout) (ℓ : ℕ) :
    digitModuli P lay ℓ = (digitsB P lay ℓ).map List.prod := by
  show (List.range (lay.sizes ℓ).length).map (fun j =>
      (((P.src.qs.take ℓ).drop ((lay.sizes ℓ).take j).sum).take ((lay.sizes ℓ).getD j 0)).prod) = _
  simp [digitsB, Function.comp_def]

theorem length_digitsB_le (P : FullParams) (lay : KSLayout) (ℓ j : ℕ) :
    (((P.src.qs.take ℓ).drop ((lay.sizes ℓ).take j).sum).take ((lay.sizes ℓ).getD j 0)).length ≤
      (lay.sizes ℓ).getD j 0 := by
  simp

theorem length_digitsB (P : FullParams) (lay : KSLayout) (ℓ j : ℕ) (hℓ : ℓ ≤ P.src.qs.length)
    (hlay : (lay.sizes ℓ).sum = ℓ) :
    (((P.src.qs.take ℓ).drop ((lay.sizes ℓ).take j).sum).take ((lay.sizes ℓ).getD j 0)).length =
      (lay.sizes ℓ).getD j 0 := by
  have := Validation.Budget.sum_take_succ_le (lay.sizes ℓ) j
  simp only [List.length_take, List.length_drop]
  omega

/-- The digit weight sums agree (centred), for a usable layout. -/
theorem weights_centred (P : FullParams) (lay : KSLayout) (ℓ : ℕ) (hℓ : ℓ ≤ P.src.qs.length)
    (hlay : (lay.sizes ℓ).sum = ℓ) :
    (List.zipWith (fun n Q => n * Q) (lay.sizes ℓ) (digitModuli P lay ℓ)).sum =
      lsum ((digitsB P lay ℓ).map (bconvBound2 .centred)) := by
  rw [lsum_eq_sum, digitModuli_eq_B]
  congr 1
  apply List.ext_getElem
  · simp [digitsB]
  · intro j h1 h2
    simp only [List.getElem_zipWith, List.getElem_map, bconvBound2_centred, digitsB,
      List.getElem_range]
    rw [length_digitsB P lay ℓ j hℓ hlay]
    have hj : j < (lay.sizes ℓ).length := by simpa [digitsB] using h2
    simp [List.getElem?_eq_getElem hj]

/-- The digit weight sums (canonical): B's at most A's. -/
theorem weights_canonical (P : FullParams) (lay : KSLayout) (ℓ : ℕ)
    (hpos : ∀ q ∈ P.src.qs, 0 < q) :
    lsum ((digitsB P lay ℓ).map (bconvBound2 .canonical)) ≤
      (List.zipWith (fun n Q => 2 * (n * (Q - 1))) (lay.sizes ℓ) (digitModuli P lay ℓ)).sum := by
  rw [lsum_eq_sum, digitModuli_eq_B]
  set n := (lay.sizes ℓ).length
  set sl : ℕ → List ℕ := fun j =>
    ((P.src.qs.take ℓ).drop ((lay.sizes ℓ).take j).sum).take ((lay.sizes ℓ).getD j 0) with hsl
  have e1 : (digitsB P lay ℓ).map (bconvBound2 .canonical) =
      (List.range n).map fun j => bconvBound2 .canonical (sl j) := by
    simp [digitsB, sl, n, Function.comp_def]
  have e2 : List.zipWith (fun n Q => 2 * (n * (Q - 1))) (lay.sizes ℓ)
      ((digitsB P lay ℓ).map List.prod) =
      (List.range n).map fun j => 2 * ((lay.sizes ℓ).getD j 0 * ((sl j).prod - 1)) := by
    apply List.ext_getElem
    · simp [digitsB, n]
    · intro j h1 h2
      have hj : j < (lay.sizes ℓ).length := by simpa [digitsB] using h1
      simp [digitsB, sl, List.getElem?_eq_getElem hj]
  rw [e1, e2]
  apply List.sum_le_sum
  intro j _
  have hp : ∀ q ∈ sl j, 0 < q := fun q hq =>
    hpos q (List.mem_of_mem_take (List.mem_of_mem_drop (List.mem_of_mem_take hq)))
  have h1 := bconvBound2_canonical_le (sl j) hp
  have h2 : (sl j).length ≤ (lay.sizes ℓ).getD j 0 := length_digitsB_le P lay ℓ j
  calc bconvBound2 .canonical (sl j) ≤ 2 * ((sl j).length * ((sl j).prod - 1)) := h1
    _ ≤ 2 * ((lay.sizes ℓ).getD j 0 * ((sl j).prod - 1)) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ h2)

/-! ### The bounds -/

theorem specialProd_eq (P : FullParams) : specialProd P = (P.store.special.map (·.q)).prod := rfl

/-- **Centred: A's bound is B's rounded down**, under `keyNoise = t·Be`, for a usable layout. -/
theorem ksBoundAt_centred_eq (P : FullParams) (lay : KSLayout) (hc : lay.canonical = false)
    (ℓ : ℕ) (hℓ : ℓ ≤ P.src.qs.length) (hlay : (lay.sizes ℓ).sum = ℓ) (Be : ℕ)
    (hBk : P.keyNoise = P.src.t * Be) :
    ksBoundAt P lay ℓ = ⌊ksAddedBound .centred P.src.N P.src.t P.secretBound Be
      (digitsB P lay ℓ) (P.store.special.map (·.q))⌋₊ := by
  unfold ksBoundAt ksAddedBound
  simp only [hc, Bool.false_eq_true, ite_false]
  rw [Nat.floor_div_eq_div, ← weights_centred P lay ℓ hℓ hlay, bconvBound2_centred, hBk,
    specialProd_eq]
  simp only [List.length_map]
  congr 1
  ring

/-- **Canonical: B's bound (rounded down) is at most A's**, for every layout. -/
theorem ksBoundAt_canonical_ge (P : FullParams) (lay : KSLayout) (hc : lay.canonical = true)
    (ℓ : ℕ) (hpos : ∀ q ∈ P.src.qs, 0 < q) (hposP : ∀ p ∈ P.store.special.map (·.q), 0 < p)
    (Be : ℕ) (hBk : P.keyNoise = P.src.t * Be) :
    ⌊ksAddedBound .canonical P.src.N P.src.t P.secretBound Be
      (digitsB P lay ℓ) (P.store.special.map (·.q))⌋₊ ≤ ksBoundAt P lay ℓ := by
  unfold ksBoundAt ksAddedBound
  simp only [hc, ite_true]
  rw [Nat.floor_div_eq_div, hBk, specialProd_eq]
  apply Nat.div_le_div_right
  have hw := weights_canonical P lay ℓ hpos
  have hp := bconvBound2_canonical_le (P.store.special.map (·.q)) hposP
  simp only [List.length_map] at hp
  have e : P.src.N * (P.src.t * Be) *
      (List.zipWith (fun n Q => 2 * (n * (Q - 1))) (lay.sizes ℓ) (digitModuli P lay ℓ)).sum =
      P.src.t * P.src.N * Be *
      (List.zipWith (fun n Q => 2 * (n * (Q - 1))) (lay.sizes ℓ) (digitModuli P lay ℓ)).sum := by ring
  rw [e]
  apply Nat.add_le_add
  · exact Nat.mul_le_mul_left _ hw
  · rw [Nat.mul_assoc (P.src.t), Nat.mul_assoc (P.src.t)]
    exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hp)

/-- **Strictness witness** (B's test parameters): B's canonical bound `5191760/86609 < 60`, A's
canonical `ksBoundAt` is `60`; centred both give `30`. -/
theorem canonical_strict :
    ksAddedBound .canonical 4 5 1 2 [[97, 113], [193]] [257, 337] = 5191760 / 86609 ∧
    ksAddedBound .centred 4 5 1 2 [[97, 113], [193]] [257, 337] = 2607525 / 86609 := by
  constructor <;> decide +kernel

end Respec.Equiv
