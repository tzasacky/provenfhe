import Validation.Ring
import Validation.Scheme.Basic

/-!
# FHE.Pin.Kron — the negacyclic product over `ℤ` by Kronecker substitution, PROVED equal to the
trusted `*` of `Spec.NPoly`   (UNTRUSTED glue; the theorems are kernel-checked)

`Spec.NPoly`'s `*` is the schoolbook negacyclic convolution: `N²` big-integer multiply-adds. At
`N = 16384` that is `2.7·10⁸` per product, and the forced phases and staged key switches of
`openfhe_pin` take thousands of products per case. `mulNeg N a b` computes the same product with one
big-integer multiplication (GMP) of two `N`-slot packings:

1. `w` is chosen from the data so that every coefficient `C m` of the integer convolution
   `C = (Σ aᵢXⁱ)(Σ bⱼXʲ)` satisfies `|C m| < h = 2^(w-1)` (`|C m| ≤ 2N·max|a|·max|b|`);
2. `E(a) = Σ aᵢ 2^(wi)` is packed from non-negative slots (`aᵢ + max|a|`, minus `max|a|·Σ 2^(wi)`),
   divide and conquer (`packF`);
3. `y = E(a)·E(b) + Σ_{m<2N} h·2^(wm) = Σ_{m<2N} (C m + h)·2^(wm)`, every slot in `[0, 2^w)`;
4. the slots are read back divide and conquer (`unpackL`), and coefficient `k` of the negacyclic
   product is `C k − C (k+N)` (`X^N = −1`).

**`mulNeg_eq`**: `ofArrZ N (mulNeg N a b) = ofArrZ N a * ofArrZ N b` for ALL arrays `a`, `b` (no
hypothesis: the slot width is computed from the data). `ofArrZ` is `FHE.Pin.ofArr` at `ℤ`
(definitionally; `FHE.Pin.ofArr_mulArr` in `FHE/Pin/Force.lean` restates it for the forced path).
**`autoL_eq`**: the linear-time scatter `autoL g a` is `Spec.NPoly.automorph g a`. Axioms of both:
`propext`, `Classical.choice`, `Quot.sound`.

The products are returned as ARRAYS on purpose: `Spec.NPoly` is a structure with one function
field, and compiled code re-evaluates an `NPoly`-valued intermediate for every coefficient where
it is used inside a coefficient lambda (see `FHE.Pin.mulArr`).
-/

namespace FHE.Pin.Kron
open Spec Spec.NPoly Validation.Ring

/-! ## Packing and unpacking in base `2^w` -/

/-- `Σ_{i<n} f (lo+i) · 2^(w·i)`, divide and conquer (one shift per node). -/
def packF (f : ℕ → ℕ) (w : ℕ) (lo n : ℕ) : ℕ :=
  if _h0 : n = 0 then 0
  else if _h1 : n = 1 then f lo
  else
    packF f w lo (n / 2) + (packF f w (lo + n / 2) (n - n / 2) <<< (w * (n / 2)))
termination_by n
decreasing_by all_goals omega

theorem packF_spec (f : ℕ → ℕ) (w : ℕ) (n : ℕ) : ∀ lo,
    packF f w lo n = ∑ i ∈ Finset.range n, f (lo + i) * 2 ^ (w * i) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro lo
    rw [packF]
    by_cases h0 : n = 0
    · subst h0; simp
    by_cases h1 : n = 1
    · subst h1; simp
    simp only [h0, h1, ↓reduceDIte]
    rw [ih (n / 2) (by omega), ih (n - n / 2) (by omega), Nat.shiftLeft_eq]
    have hn : n = n / 2 + (n - n / 2) := by omega
    conv_rhs => rw [hn, Finset.sum_range_add]
    congr 1
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [show lo + (n / 2 + i) = lo + n / 2 + i by omega, mul_add, pow_add]
    ring

/-- The `n` slots of `w` bits of `y`, low first, divide and conquer. -/
def unpackL (w : ℕ) (y n : ℕ) : List ℕ :=
  if _h0 : n = 0 then []
  else if _h1 : n = 1 then [y % 2 ^ w]
  else
    let hi := y >>> (w * (n / 2))
    let lo := y - (hi <<< (w * (n / 2)))
    unpackL w lo (n / 2) ++ unpackL w hi (n - n / 2)
termination_by n
decreasing_by all_goals omega

theorem lo_eq_mod (y s : ℕ) : y - ((y >>> s) <<< s) = y % 2 ^ s := by
  rw [Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
  have := Nat.mod_add_div y (2 ^ s)
  rw [Nat.mul_comm] at this
  omega

theorem unpackL_spec (w : ℕ) (n : ℕ) : ∀ y,
    unpackL w y n = (List.range n).map fun m => y / 2 ^ (w * m) % 2 ^ w := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro y
    rw [unpackL]
    by_cases h0 : n = 0
    · subst h0; simp
    by_cases h1 : n = 1
    · subst h1; simp
    simp only [h0, h1, ↓reduceDIte]
    rw [ih (n / 2) (by omega), ih (n - n / 2) (by omega), lo_eq_mod, Nat.shiftRight_eq_div_pow]
    have hn : n = n / 2 + (n - n / 2) := by omega
    conv_rhs => rw [hn, List.range_add, List.map_append, List.map_map]
    congr 1
    · refine List.map_congr_left fun m hm => ?_
      rw [List.mem_range] at hm
      have hk : w * (n / 2) = w * m + w * (n / 2 - m) := by
        rw [← mul_add]; congr 1; omega
      rw [hk, pow_add, Nat.mod_mul_right_div_self]
      apply Nat.mod_mod_of_dvd
      exact pow_dvd_pow 2 (by
        have : 1 ≤ n / 2 - m := by omega
        calc w = w * 1 := (mul_one w).symm
          _ ≤ w * (n / 2 - m) := Nat.mul_le_mul_left w this)
    · refine List.map_congr_left fun m _ => ?_
      simp only [Function.comp]
      rw [Nat.div_div_eq_div_mul, ← pow_add, ← mul_add]

/-- Digit `k` of `Σ_{m<M} d m · B^m` (every `d m < B`) is `d k`. -/
theorem digit_of_sum (B : ℕ) (hB : 0 < B) : ∀ (M : ℕ) (d : ℕ → ℕ), (∀ m, m < M → d m < B) →
    ∀ k, k < M → (∑ m ∈ Finset.range M, d m * B ^ m) / B ^ k % B = d k := by
  intro M
  induction M with
  | zero => intro d _ k hk; omega
  | succ M ih =>
    intro d hd k hk
    have hsplit : (∑ m ∈ Finset.range (M + 1), d m * B ^ m) =
        d 0 + B * ∑ m ∈ Finset.range M, d (m + 1) * B ^ m := by
      rw [Finset.sum_range_succ', Finset.mul_sum, pow_zero, mul_one, add_comm]
      congr 1
      exact Finset.sum_congr rfl fun i _ => by ring
    have h0 : d 0 < B := hd 0 (by omega)
    rw [hsplit]
    cases k with
    | zero =>
      simp only [pow_zero, Nat.div_one]
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h0]
    | succ k =>
      rw [pow_succ', ← Nat.div_div_eq_div_mul]
      rw [show (d 0 + B * ∑ m ∈ Finset.range M, d (m + 1) * B ^ m) / B =
          (∑ m ∈ Finset.range M, d (m + 1) * B ^ m : ℕ) by
        rw [Nat.add_mul_div_left _ _ hB, Nat.div_eq_of_lt h0, zero_add]]
      exact ih (fun m => d (m + 1)) (fun m hm => hd (m + 1) (by omega)) k (by omega)


/-! ## The negacyclic fold of a product of degree `< 2N` -/

section Fold
variable {R : Type} [CommRing R] {N : ℕ}

/-- Folding a polynomial of degree `< 2N` with `X^N = −1` gives its class in `R[X]/(X^N+1)`. -/
theorem toQuot_fold (C : Polynomial R) (hC : C.natDegree < 2 * N) (r : NPoly R N)
    (hr : ∀ k : Fin N, r.coeff k = C.coeff k.val - C.coeff (k.val + N)) :
    toQuot r = mkQ R N C := by
  have hL : (∑ i : Fin N, mkQ R N (Polynomial.C (r.coeff i)) * mkQ R N Polynomial.X ^ (i : ℕ)) =
      ∑ i ∈ Finset.range N,
        mkQ R N (Polynomial.C (C.coeff i - C.coeff (i + N))) * mkQ R N Polynomial.X ^ i := by
    rw [← Fin.sum_univ_eq_sum_range]
    simp only [hr]
  rw [toQuot_eq_sum, hL]
  have hCs := Polynomial.as_sum_range' C (2 * N) hC
  conv_rhs => rw [hCs]
  rw [map_sum, two_mul, Finset.sum_range_add]
  simp only [← Polynomial.C_mul_X_pow_eq_monomial, map_mul, map_pow, pow_add, root_pow_N]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Polynomial.C_sub, map_sub, add_comm N i]
  ring
end Fold

/-! ## The product -/

/-- `FHE.Pin.ofArr` at `ℤ`: coefficient `i` is `arr[i]!`. -/
def ofArrZ (N : ℕ) (arr : Array ℤ) : IntPoly N := ⟨fun i => arr[i.val]!⟩

/-- `max_{i<N} |a[i]!|`. -/
def maxAbs (N : ℕ) (a : Array ℤ) : ℕ := (List.range N).foldl (fun m i => max m (a[i]!).natAbs) 0

theorem foldl_max_ge (f : ℕ → ℕ) : ∀ (l : List ℕ) (m0 : ℕ),
    m0 ≤ l.foldl (fun m i => max m (f i)) m0 ∧ ∀ i ∈ l, f i ≤ l.foldl (fun m i => max m (f i)) m0 := by
  intro l
  induction l with
  | nil => intro m0; simp
  | cons x xs ih =>
    intro m0
    obtain ⟨h1, h2⟩ := ih (max m0 (f x))
    refine ⟨le_trans (le_max_left _ _) h1, fun i hi => ?_⟩
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp hi with rfl | hi
    · exact le_trans (le_max_right _ _) h1
    · exact h2 i hi

theorem le_maxAbs (N : ℕ) (a : Array ℤ) (i : ℕ) (hi : i < N) : (a[i]!).natAbs ≤ maxAbs N a :=
  (foldl_max_ge (fun i => (a[i]!).natAbs) (List.range N) 0).2 i (List.mem_range.mpr hi)

/-- The slot width: `2^(w-1) > 2N·ma·mb`. -/
def slotWidth (N ma mb : ℕ) : ℕ := (2 * N * ma * mb).log2 + 2

/-- `Σ_{i<N} a[i]!·2^(wi)` from non-negative slots `a[i]! + ma`. -/
def packSigned (w N : ℕ) (a : Array ℤ) (ma : ℕ) : ℤ :=
  ((packF (fun i => (a[i]! + ma).toNat) w 0 N : ℕ) : ℤ) - ma * ((packF (fun _ => 1) w 0 N : ℕ) : ℤ)

/-- `E(a)·E(b) + Σ_{m<2N} h·2^(wm)`, as a natural number. -/
def kronY (N w h : ℕ) (Ea Eb : ℤ) : ℕ :=
  (Ea * Eb + ((packF (fun _ => h) w 0 (2 * N) : ℕ) : ℤ)).toNat

/-- **The negacyclic product by Kronecker substitution** (one GMP product of `N`-slot packings). -/
def mulNeg (N : ℕ) (a b : Array ℤ) : Array ℤ :=
  let ma := maxAbs N a
  let mb := maxAbs N b
  let w := slotWidth N ma mb
  let D := (unpackL w (kronY N w (2 ^ (w - 1)) (packSigned w N a ma) (packSigned w N b mb)) (2 * N)).toArray
  Array.ofFn (n := N) fun k => (D[k.val]! : ℤ) - (D[k.val + N]! : ℤ)

theorem pack_signed (N w : ℕ) (a : Array ℤ) (ma : ℕ) (hma : ∀ i, i < N → (a[i]!).natAbs ≤ ma) :
    packSigned w N a ma = ∑ i ∈ Finset.range N, a[i]! * (2 ^ w) ^ i := by
  rw [packSigned, packF_spec, packF_spec]
  push_cast
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' := hma i (Finset.mem_range.mp hi)
  rw [zero_add, Int.toNat_of_nonneg (by omega), ← pow_mul]
  ring

theorem eval_toPolynomial (N w : ℕ) (a : Array ℤ) :
    (toPolynomial (ofArrZ N a)).eval (2 ^ w : ℤ) = ∑ i ∈ Finset.range N, a[i]! * (2 ^ w) ^ i := by
  rw [toPolynomial_def, Polynomial.eval_finsetSum]
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  exact Fin.sum_univ_eq_sum_range (fun i => a[i]! * (2 ^ w : ℤ) ^ i) N

theorem natDegree_toPolynomial_le (N : ℕ) (a : Array ℤ) :
    (toPolynomial (ofArrZ N a)).natDegree ≤ N - 1 := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro m hm
  rw [toPolynomial_coeff]
  split_ifs with h
  · omega
  · rfl

theorem coeff_toPolynomial_abs (N : ℕ) (a : Array ℤ) (ma : ℕ)
    (hma : ∀ i, i < N → (a[i]!).natAbs ≤ ma) (i : ℕ) :
    ((toPolynomial (ofArrZ N a)).coeff i).natAbs ≤ ma := by
  rw [toPolynomial_coeff]
  split_ifs with h
  · exact hma i h
  · simp

theorem coeff_mul_abs (N : ℕ) (a b : Array ℤ) (ma mb : ℕ)
    (hma : ∀ i, i < N → (a[i]!).natAbs ≤ ma) (hmb : ∀ i, i < N → (b[i]!).natAbs ≤ mb)
    (m : ℕ) (hm : m < 2 * N) :
    |((toPolynomial (ofArrZ N a) * toPolynomial (ofArrZ N b)).coeff m)| ≤ (2 * N * ma * mb : ℕ) := by
  rw [Polynomial.coeff_mul]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  have hterm : ∀ x ∈ Finset.HasAntidiagonal.antidiagonal m,
      |(toPolynomial (ofArrZ N a)).coeff x.1 * (toPolynomial (ofArrZ N b)).coeff x.2| ≤ (ma * mb : ℕ) := by
    intro x _
    have h1 : |(toPolynomial (ofArrZ N a)).coeff x.1| ≤ (ma : ℤ) := by
      rw [Int.abs_eq_natAbs]; exact_mod_cast coeff_toPolynomial_abs N a ma hma x.1
    have h2 : |(toPolynomial (ofArrZ N b)).coeff x.2| ≤ (mb : ℤ) := by
      rw [Int.abs_eq_natAbs]; exact_mod_cast coeff_toPolynomial_abs N b mb hmb x.2
    rw [abs_mul]
    push_cast
    exact mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [Finset.sum_const, Finset.Nat.card_antidiagonal, nsmul_eq_mul]
  push_cast
  have : ((m : ℤ) + 1) ≤ 2 * N := by omega
  calc ((m : ℤ) + 1) * ((ma : ℤ) * mb) ≤ 2 * N * ((ma : ℤ) * mb) :=
        mul_le_mul_of_nonneg_right this (by positivity)
    _ = 2 * N * ma * mb := by ring

theorem getElem!_toArray_map_range (g : ℕ → ℕ) (n m : ℕ) (hm : m < n) :
    ((List.range n).map g).toArray[m]! = g m := by
  rw [getElem!_pos _ _ (by simp [hm])]
  simp

/-- Coefficient `k` of `mulNeg` is `C k − C (k+N)` for the integer product `C`. -/
theorem mulNeg_coeff (N : ℕ) (a b : Array ℤ) (k : ℕ) (hk : k < N) :
    (mulNeg N a b)[k]! = (toPolynomial (ofArrZ N a) * toPolynomial (ofArrZ N b)).coeff k -
      (toPolynomial (ofArrZ N a) * toPolynomial (ofArrZ N b)).coeff (k + N) := by
  set C := toPolynomial (ofArrZ N a) * toPolynomial (ofArrZ N b) with hC
  set ma := maxAbs N a
  set mb := maxAbs N b
  set w := slotWidth N ma mb with hw
  set h := 2 ^ (w - 1) with hh
  have hma := le_maxAbs N a
  have hmb := le_maxAbs N b
  have hbound : 2 * N * ma * mb < h := by
    rw [hh, hw, slotWidth, show (2 * N * ma * mb).log2 + 2 - 1 = (2 * N * ma * mb).log2 + 1 by omega]
    exact Nat.lt_log2_self
  have hw2 : (2 : ℕ) ^ w = 2 * h := by
    have e1 : w - 1 + 1 = w := by rw [hw, slotWidth]; omega
    rw [hh, ← pow_succ', e1]
  have hCdeg : C.natDegree < 2 * N := by
    calc C.natDegree ≤ (toPolynomial (ofArrZ N a)).natDegree + (toPolynomial (ofArrZ N b)).natDegree :=
          Polynomial.natDegree_mul_le
      _ ≤ (N - 1) + (N - 1) :=
          add_le_add (natDegree_toPolynomial_le N a) (natDegree_toPolynomial_le N b)
      _ < 2 * N := by omega
  let d : ℕ → ℕ := fun m => (C.coeff m + h).toNat
  have hdC : ∀ m, m < 2 * N → (d m : ℤ) = C.coeff m + h := by
    intro m hm
    have := coeff_mul_abs N a b ma mb hma hmb m hm
    rw [← hC] at this
    have hb : ((2 * N * ma * mb : ℕ) : ℤ) < h := by exact_mod_cast hbound
    simp only [d]
    rw [Int.toNat_of_nonneg (by rw [abs_le] at this; omega)]
  have hdlt : ∀ m, m < 2 * N → d m < 2 ^ w := by
    intro m hm
    have h1 := hdC m hm
    have := coeff_mul_abs N a b ma mb hma hmb m hm
    rw [← hC] at this
    have hb : ((2 * N * ma * mb : ℕ) : ℤ) < h := by exact_mod_cast hbound
    have : (d m : ℤ) < ((2 ^ w : ℕ) : ℤ) := by
      rw [h1, hw2]; push_cast; rw [abs_le] at this; omega
    exact_mod_cast this
  have hsum : packSigned w N a ma * packSigned w N b mb + ((packF (fun _ => h) w 0 (2 * N) : ℕ) : ℤ)
      = ((∑ m ∈ Finset.range (2 * N), d m * (2 ^ w) ^ m : ℕ) : ℤ) := by
    rw [pack_signed N w a ma hma, pack_signed N w b mb hmb, ← eval_toPolynomial,
      ← eval_toPolynomial, ← Polynomial.eval_mul, ← hC, Polynomial.eval_eq_sum_range' hCdeg, packF_spec]
    push_cast
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun m hm => ?_
    rw [hdC m (Finset.mem_range.mp hm)]
    ring
  have hy : kronY N w h (packSigned w N a ma) (packSigned w N b mb) =
      ∑ m ∈ Finset.range (2 * N), d m * (2 ^ w) ^ m := by
    rw [kronY, hsum, Int.toNat_natCast]
  have hD : ∀ m, m < 2 * N →
      ((unpackL w (kronY N w h (packSigned w N a ma) (packSigned w N b mb)) (2 * N)).toArray[m]! : ℤ)
        = C.coeff m + h := by
    intro m hm
    rw [unpackL_spec, getElem!_toArray_map_range _ _ _ hm, hy, pow_mul,
      digit_of_sum (2 ^ w) (by positivity) (2 * N) d hdlt m hm, hdC m hm]
  have e : (mulNeg N a b)[k]! =
      ((unpackL w (kronY N w h (packSigned w N a ma) (packSigned w N b mb)) (2 * N)).toArray[k]! : ℤ) -
      ((unpackL w (kronY N w h (packSigned w N a ma) (packSigned w N b mb)) (2 * N)).toArray[k + N]! : ℤ) := by
    rw [mulNeg, getElem!_pos _ _ (by simp [hk]), Array.getElem_ofFn]
  rw [e, hD k (by omega), hD (k + N) (by omega)]
  ring

/-- **The Kronecker product is the trusted negacyclic product**, for all arrays. -/
theorem mulNeg_eq (N : ℕ) (a b : Array ℤ) :
    ofArrZ N (mulNeg N a b) = ofArrZ N a * ofArrZ N b := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN; ext i; exact i.elim0
  apply toQuot_injective hN
  rw [toQuot_mul, toQuot_def (ofArrZ N a), toQuot_def (ofArrZ N b), ← map_mul]
  apply toQuot_fold
  · calc (toPolynomial (ofArrZ N a) * toPolynomial (ofArrZ N b)).natDegree
          ≤ (toPolynomial (ofArrZ N a)).natDegree + (toPolynomial (ofArrZ N b)).natDegree :=
            Polynomial.natDegree_mul_le
      _ ≤ (N - 1) + (N - 1) :=
          add_le_add (natDegree_toPolynomial_le N a) (natDegree_toPolynomial_le N b)
      _ < 2 * N := by omega
  · intro k
    exact mulNeg_coeff N a b k.val k.isLt

/-! ## Integer representatives of `Z_q` polynomials -/

theorem ofInt_map_cast {q N : ℕ} (a : Poly q N) : ofInt q (NPoly.map (ZMod.cast : ZMod q → ℤ) a) = a := by
  ext i
  show ((ZMod.cast (a.coeff i) : ℤ) : ZMod q) = a.coeff i
  exact ZMod.intCast_zmod_cast _

/-! ## The automorphism in linear time

`Spec.NPoly.automorph g a` is a sum over all `i` for every output coefficient (`N²` terms, almost
all zero). `autoL` scatters each input coefficient to its one destination instead. -/

section Auto
variable {R : Type} [CommRing R] {N : ℕ}

/-- One scatter step: coefficient `i` of `a` to `±X^((i·g) mod 2N)`. -/
def autoStep (g : ℕ) (a : NPoly R N) (acc : Array R) (i : ℕ) : Array R :=
  if h : i < N then
    let j := (i * g) % (2 * N)
    if j < N then acc.modify j (· + a.coeff ⟨i, h⟩) else acc.modify (j - N) (· - a.coeff ⟨i, h⟩)
  else acc

/-- The coefficients of `automorph g a`, scattered. -/
def autoArr (g : ℕ) (a : NPoly R N) : Array R :=
  (List.range N).foldl (autoStep g a) (Array.replicate N 0)

/-- Wrap an array (`getD`, default `0`); `@[noinline]` so that the array is computed once. -/
@[noinline] def ofArrD (arr : Array R) : NPoly R N := ⟨fun k => arr.getD k.val 0⟩

/-- **The automorphism in linear time.** -/
def autoL (g : ℕ) (a : NPoly R N) : NPoly R N := ofArrD (autoArr g a)

/-- The term of `automorph` for input `i` and output `k`. -/
def autoTerm (g : ℕ) (a : NPoly R N) (k : ℕ) (i : ℕ) : R :=
  if h : i < N then
    (if (i * g) % (2 * N) = k then a.coeff ⟨i, h⟩
     else if (i * g) % (2 * N) = k + N then -a.coeff ⟨i, h⟩ else 0)
  else 0

theorem autoArr_prefix (g : ℕ) (a : NPoly R N) (n : ℕ) :
    ((List.range n).foldl (autoStep g a) (Array.replicate N 0)).size = N ∧
    ∀ k, k < N → ((List.range n).foldl (autoStep g a) (Array.replicate N 0)).getD k 0 =
      ∑ i ∈ Finset.range n, autoTerm g a k i := by
  induction n with
  | zero =>
    refine ⟨by simp, fun k hk => ?_⟩
    simp [Array.getD, hk]
  | succ n ih =>
    obtain ⟨hs, hv⟩ := ih
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    set acc := (List.range n).foldl (autoStep g a) (Array.replicate N 0)
    refine ⟨?_, fun k hk => ?_⟩
    · unfold autoStep
      by_cases hn : n < N
      · simp only [hn, dite_true]
        split <;> simp [hs]
      · simp [hn, hs]
    · rw [Finset.sum_range_succ, ← hv k hk]
      unfold autoStep autoTerm
      by_cases hn : n < N
      · simp only [hn, dite_true]
        have hj := Nat.mod_lt (n * g) (show 0 < 2 * N by omega)
        by_cases hjN : (n * g) % (2 * N) < N
        · simp only [hjN, ite_true]
          simp only [Array.getD, Array.size_modify, hs, hk, dite_true]
          by_cases hkj : (n * g) % (2 * N) = k
          · simp [hkj, Array.getElem_modify]
          · have : ¬ (n * g) % (2 * N) = k + N := by omega
            simp [hkj, this, Array.getElem_modify]
        · simp only [hjN, ite_false]
          simp only [Array.getD, Array.size_modify, hs, hk, dite_true]
          have hk1 : ¬ (n * g) % (2 * N) = k := by omega
          by_cases hkj : (n * g) % (2 * N) = k + N
          · have : (n * g) % (2 * N) - N = k := by omega
            simp [Array.getElem_modify, hk1, this, show (n * g % (2 * N) = k + N) = True from eq_true hkj,
              sub_eq_add_neg]
          · have : ¬ (n * g) % (2 * N) - N = k := by omega
            simp [hk1, hkj, this, Array.getElem_modify]
      · simp [hn]

/-- **`autoL` is the trusted automorphism.** -/
theorem autoL_eq (g : ℕ) (a : NPoly R N) : autoL g a = automorph g a := by
  ext k
  rw [coeff_automorph']
  show (autoArr g a).getD k.val 0 = _
  rw [autoArr, (autoArr_prefix g a N).2 k.val k.isLt, ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [autoTerm, i.isLt]

end Auto

end FHE.Pin.Kron
