import Spec.Ring
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Algebra.Defs
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FastInstance

/-!
# Validation.Ring — proofs of the pins in `Challenge.Ring`

Every theorem of `Challenge/Ring.lean` is proved here under the same name and with the same
statement. Afterwards the pins are used to transfer Mathlib's ring structure on
`R[X]/(X^N + 1)` back to `NPoly R N` along the injective map `toQuot`, giving
`instance [NeZero N] : CommRing (NPoly R N)` (and an `R`-algebra structure) whose operations are
the `Spec` operations themselves (see the agreement lemmas at the end).
-/

namespace Validation.Ring
open Spec NPoly

variable {R : Type} [CommRing R] {N : ℕ}

/-! ### Coefficients of the `Spec` operations -/

@[simp] theorem coeff_zero' (i : Fin N) : (0 : NPoly R N).coeff i = 0 := rfl

@[simp] theorem coeff_one' (i : Fin N) :
    (1 : NPoly R N).coeff i = if i.val = 0 then 1 else 0 := rfl

@[simp] theorem coeff_add' (a b : NPoly R N) (i : Fin N) :
    (a + b).coeff i = a.coeff i + b.coeff i := rfl

@[simp] theorem coeff_neg' (a : NPoly R N) (i : Fin N) : (-a).coeff i = -a.coeff i := rfl

@[simp] theorem coeff_sub' (a b : NPoly R N) (i : Fin N) :
    (a - b).coeff i = a.coeff i - b.coeff i := rfl

@[simp] theorem coeff_smul' (c : R) (a : NPoly R N) (i : Fin N) :
    (c • a).coeff i = c * a.coeff i := rfl

@[simp] theorem coeff_const' (c : R) (i : Fin N) :
    (const c : NPoly R N).coeff i = if i.val = 0 then c else 0 := rfl

theorem coeff_mul' (a b : NPoly R N) (k : Fin N) :
    (a * b).coeff k = ∑ i : Fin N,
      if h : i.val ≤ k.val then
        a.coeff i * b.coeff ⟨k.val - i.val, by have := k.isLt; omega⟩
      else
        -(a.coeff i * b.coeff ⟨N + k.val - i.val, by have := k.isLt; have := i.isLt; omega⟩) :=
  rfl

theorem coeff_automorph' (g : ℕ) (a : NPoly R N) (k : Fin N) :
    (automorph g a).coeff k = ∑ i : Fin N,
      if (i.val * g) % (2 * N) = k.val then a.coeff i
      else if (i.val * g) % (2 * N) = k.val + N then -a.coeff i
      else 0 :=
  rfl

theorem one_eq_const : (1 : NPoly R N) = const 1 := rfl

/-! ### The representative `toPolynomial` -/

theorem toPolynomial_def (a : NPoly R N) :
    toPolynomial a = ∑ i : Fin N, Polynomial.C (a.coeff i) * Polynomial.X ^ (i : ℕ) := rfl

theorem toPolynomial_coeff (a : NPoly R N) (n : ℕ) :
    (toPolynomial a).coeff n = if h : n < N then a.coeff ⟨n, h⟩ else 0 := by
  rw [toPolynomial_def, Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_C_mul_X_pow]
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨n, h⟩]
    · simp
    · intro b _ hb
      exact ite_eq_right fun hnb => hb (Fin.ext hnb.symm)
    · intro h'; exact absurd (Finset.mem_univ _) h'
  · exact Finset.sum_eq_zero fun i _ =>
      ite_eq_right fun (hni : n = (i : ℕ)) => h (hni ▸ i.isLt)

theorem toPolynomial_coeff_fin (a : NPoly R N) (k : Fin N) :
    (toPolynomial a).coeff k = a.coeff k := by
  rw [toPolynomial_coeff, dite_eq_left k.isLt]

theorem degree_toPolynomial_lt (a : NPoly R N) : (toPolynomial a).degree < N := by
  rw [Polynomial.degree_lt_iff_coeff_zero]
  intro m hm
  rw [toPolynomial_coeff, dite_eq_right (by omega)]

theorem toPolynomial_injective : Function.Injective (toPolynomial : NPoly R N → _) := by
  intro a b h
  ext k
  rw [← toPolynomial_coeff_fin, ← toPolynomial_coeff_fin, h]

theorem toPolynomial_zero : toPolynomial (0 : NPoly R N) = 0 := by
  simp [toPolynomial_def]

theorem toPolynomial_add (a b : NPoly R N) :
    toPolynomial (a + b) = toPolynomial a + toPolynomial b := by
  simp [toPolynomial_def, add_mul, Finset.sum_add_distrib]

theorem toPolynomial_neg (a : NPoly R N) : toPolynomial (-a) = -toPolynomial a := by
  simp [toPolynomial_def, neg_mul, Finset.sum_neg_distrib]

theorem toPolynomial_sub (a b : NPoly R N) :
    toPolynomial (a - b) = toPolynomial a - toPolynomial b := by
  simp [toPolynomial_def, sub_mul, Finset.sum_sub_distrib]

theorem toPolynomial_smul (c : R) (a : NPoly R N) :
    toPolynomial (c • a) = Polynomial.C c * toPolynomial a := by
  simp [toPolynomial_def, Finset.mul_sum, mul_assoc]

theorem toPolynomial_const (hN : 0 < N) (c : R) :
    toPolynomial (const c : NPoly R N) = Polynomial.C c := by
  rw [toPolynomial_def, Finset.sum_eq_single ⟨0, hN⟩]
  · simp
  · intro b _ hb
    have : b.val ≠ 0 := fun h => hb (Fin.ext h)
    simp [this]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem toPolynomial_one (hN : 0 < N) : toPolynomial (1 : NPoly R N) = 1 := by
  rw [one_eq_const, toPolynomial_const hN, map_one]

/-! ### The quotient map and the root `x = [X]`, with `x ^ N = -1` -/

/-- The quotient map `R[X] → R[X]/(X^N + 1)`. -/
noncomputable abbrev mkQ (R : Type) [CommRing R] (N : ℕ) : Polynomial R →+* Quot R N :=
  Ideal.Quotient.mk (Ideal.span {(Polynomial.X ^ N + 1 : Polynomial R)})

theorem toQuot_def (a : NPoly R N) : toQuot a = mkQ R N (toPolynomial a) := rfl

theorem toQuot_eq_sum (a : NPoly R N) :
    toQuot a = ∑ i : Fin N,
      mkQ R N (Polynomial.C (a.coeff i)) * mkQ R N Polynomial.X ^ (i : ℕ) := by
  rw [toQuot_def, toPolynomial_def, map_sum]
  simp only [map_mul, map_pow]

theorem root_pow_N : mkQ R N Polynomial.X ^ N = -1 := by
  have h : mkQ R N (Polynomial.X ^ N + 1) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))
  rw [map_add, map_pow, map_one] at h
  exact eq_neg_of_add_eq_zero_left h

theorem root_pow_two_N : mkQ R N Polynomial.X ^ (2 * N) = 1 := by
  rw [pow_mul', root_pow_N]; ring

theorem root_pow_mod (n : ℕ) :
    mkQ R N Polynomial.X ^ n = mkQ R N Polynomial.X ^ (n % (2 * N)) := by
  calc mkQ R N Polynomial.X ^ n
      = mkQ R N Polynomial.X ^ (2 * N * (n / (2 * N)) + n % (2 * N)) := by
        rw [Nat.div_add_mod]
    _ = mkQ R N Polynomial.X ^ (n % (2 * N)) := by
        rw [pow_add, pow_mul, root_pow_two_N, one_pow, one_mul]

/-! ### The challenge statements -/

theorem toQuot_zero : toQuot (0 : NPoly R N) = 0 := by
  rw [toQuot_def, toPolynomial_zero, map_zero]

theorem toQuot_one (hN : 0 < N) : toQuot (1 : NPoly R N) = 1 := by
  rw [toQuot_def, toPolynomial_one hN, map_one]

theorem toQuot_add (a b : NPoly R N) : toQuot (a + b) = toQuot a + toQuot b := by
  rw [toQuot_def, toPolynomial_add, map_add]; rfl

theorem toQuot_neg (a : NPoly R N) : toQuot (-a) = -toQuot a := by
  rw [toQuot_def, toPolynomial_neg, map_neg]; rfl

theorem toQuot_sub (a b : NPoly R N) : toQuot (a - b) = toQuot a - toQuot b := by
  rw [toQuot_def, toPolynomial_sub, map_sub]; rfl

/-- For fixed `i`, the map `k ↦ (k - i) mod N` on `Fin N` (the index of `b` paired with `aᵢ` in
coefficient `k` of the negacyclic convolution). -/
def subMod (i k : Fin N) : Fin N :=
  if h : i.val ≤ k.val then ⟨k.val - i.val, by have := k.isLt; omega⟩
  else ⟨N + k.val - i.val, by have := k.isLt; have := i.isLt; omega⟩

theorem subMod_bijective (i : Fin N) : Function.Bijective (subMod i) := by
  rw [← Finite.injective_iff_bijective]
  intro k₁ k₂ hk
  have h1 := k₁.isLt
  have h2 := k₂.isLt
  have h3 := i.isLt
  apply Fin.ext
  have hv := congrArg Fin.val hk
  unfold subMod at hv
  split_ifs at hv <;> simp only [] at hv <;> omega

theorem toQuot_mul (a b : NPoly R N) : toQuot (a * b) = toQuot a * toQuot b := by
  have hx : mkQ R N Polynomial.X ^ N = -1 := root_pow_N
  rw [toQuot_eq_sum, toQuot_eq_sum, toQuot_eq_sum, Finset.sum_mul_sum]
  simp only [coeff_mul', map_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  refine Fintype.sum_bijective (subMod i) (subMod_bijective i) _ _ (fun k => ?_)
  have hi := i.isLt
  have hk := k.isLt
  by_cases h : i.val ≤ k.val
  · simp only [subMod, h, dite_true, map_mul]
    have e : mkQ R N Polynomial.X ^ (k : ℕ) =
        mkQ R N Polynomial.X ^ (i : ℕ) * mkQ R N Polynomial.X ^ ((k : ℕ) - i) := by
      rw [← pow_add]; congr 1; omega
    rw [e]; ring
  · simp only [subMod, h, dite_false, map_mul, map_neg]
    have e : mkQ R N Polynomial.X ^ (i : ℕ) * mkQ R N Polynomial.X ^ (N + (k : ℕ) - i) =
        -mkQ R N Polynomial.X ^ (k : ℕ) := by
      rw [← pow_add, show (i : ℕ) + (N + k - i) = N + k by omega, pow_add, hx]; ring
    linear_combination (-(mkQ R N (Polynomial.C (a.coeff i)) *
      mkQ R N (Polynomial.C (b.coeff ⟨N + k.val - i.val, by omega⟩)))) * e

theorem toQuot_pow (hN : 0 < N) (a : NPoly R N) (n : ℕ) : toQuot (a ^ n) = toQuot a ^ n := by
  induction n with
  | zero => exact (toQuot_one hN).trans (pow_zero _).symm
  | succ n ih =>
    show toQuot (a ^ n * a) = _
    rw [toQuot_mul, ih, pow_succ]

theorem toQuot_smul (c : R) (a : NPoly R N) :
    toQuot (c • a) = Ideal.Quotient.mk _ (Polynomial.C c) * toQuot a := by
  rw [toQuot_def, toPolynomial_smul, map_mul]; rfl

theorem toQuot_const (hN : 0 < N) (c : R) :
    toQuot (const c : NPoly R N) = Ideal.Quotient.mk _ (Polynomial.C c) := by
  rw [toQuot_def, toPolynomial_const hN]

theorem monic_X_pow_add_one (hN : 0 < N) : (Polynomial.X ^ N + 1 : Polynomial R).Monic := by
  simpa using Polynomial.monic_X_pow_add_C (1 : R) (Nat.pos_iff_ne_zero.mp hN)

theorem degree_X_pow_add_one [Nontrivial R] (hN : 0 < N) :
    (Polynomial.X ^ N + 1 : Polynomial R).degree = N := by
  simpa using Polynomial.degree_X_pow_add_C hN (1 : R)

theorem toQuot_injective (hN : 0 < N) : Function.Injective (toQuot : NPoly R N → Quot R N) := by
  intro a b h
  rcases subsingleton_or_nontrivial R with hR | hR
  · ext k; exact Subsingleton.elim _ _
  have hmem : (Polynomial.X ^ N + 1 : Polynomial R) ∣ toPolynomial (a - b) := by
    rw [toPolynomial_sub, ← Ideal.mem_span_singleton]
    rw [toQuot_def, toQuot_def] at h
    exact Ideal.Quotient.eq.mp h
  by_contra hab
  have hne : toPolynomial (a - b) ≠ 0 := by
    intro h0
    apply hab
    ext k
    have := toPolynomial_coeff_fin (a - b) k
    rw [h0, Polynomial.coeff_zero, coeff_sub'] at this
    exact sub_eq_zero.mp this.symm
  exact (monic_X_pow_add_one hN).not_dvd_of_degree_lt hne
    (by rw [degree_X_pow_add_one hN]; exact degree_toPolynomial_lt _) hmem

theorem toQuot_surjective (hN : 0 < N) : Function.Surjective (toQuot : NPoly R N → Quot R N) := by
  intro y
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective y
  rcases subsingleton_or_nontrivial R with hR | hR
  · refine ⟨0, ?_⟩
    rw [toQuot_def]
    congr 1
    ext n
    exact Subsingleton.elim _ _
  have hr : (p %ₘ (Polynomial.X ^ N + 1)).degree < N := by
    have := Polynomial.degree_modByMonic_lt p (monic_X_pow_add_one (R := R) hN)
    rwa [degree_X_pow_add_one hN] at this
  refine ⟨⟨fun i => (p %ₘ (Polynomial.X ^ N + 1)).coeff i⟩, ?_⟩
  have hrep : toPolynomial (⟨fun i => (p %ₘ (Polynomial.X ^ N + 1)).coeff i⟩ : NPoly R N) =
      p %ₘ (Polynomial.X ^ N + 1) := by
    ext n
    rw [toPolynomial_coeff]
    split_ifs with h
    · rfl
    · exact (Polynomial.coeff_eq_zero_of_degree_lt
        (lt_of_lt_of_le hr (by exact_mod_cast (not_lt.mp h)))).symm
  rw [toQuot_def, hrep]
  apply Ideal.Quotient.eq.mpr
  rw [Ideal.mem_span_singleton, Polynomial.modByMonic_eq_sub_mul_div]
  exact ⟨-(p /ₘ (Polynomial.X ^ N + 1)), by ring⟩

theorem toQuot_bijective (hN : 0 < N) : Function.Bijective (toQuot : NPoly R N → Quot R N) :=
  ⟨toQuot_injective hN, toQuot_surjective hN⟩

/-- Contribution of the single coefficient `aᵢ` to `toQuot (automorph g a)`. -/
theorem automorph_term (g : ℕ) (a : NPoly R N) (i : Fin N) :
    ∑ k : Fin N, mkQ R N (Polynomial.C
      (if (i.val * g) % (2 * N) = k.val then a.coeff i
       else if (i.val * g) % (2 * N) = k.val + N then -a.coeff i else 0)) *
        mkQ R N Polynomial.X ^ (k : ℕ)
    = mkQ R N (Polynomial.C (a.coeff i)) * mkQ R N Polynomial.X ^ (i.val * g) := by
  have hN : 0 < N := Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt
  have hm2 : (i.val * g) % (2 * N) < 2 * N := Nat.mod_lt _ (by omega)
  rw [root_pow_mod (i.val * g)]
  by_cases hmN : (i.val * g) % (2 * N) < N
  · rw [Finset.sum_eq_single ⟨(i.val * g) % (2 * N), hmN⟩]
    · simp
    · intro k _ hk
      have h1 : (i.val * g) % (2 * N) ≠ k.val := fun h => hk (Fin.ext h.symm)
      have h2 : (i.val * g) % (2 * N) ≠ k.val + N := by omega
      simp [h1, h2]
    · intro h; exact absurd (Finset.mem_univ _) h
  · rw [Finset.sum_eq_single ⟨(i.val * g) % (2 * N) - N, by omega⟩]
    · have h1 : (i.val * g) % (2 * N) ≠ (i.val * g) % (2 * N) - N := by omega
      have h2 : (i.val * g) % (2 * N) = (i.val * g) % (2 * N) - N + N := by omega
      simp only [ite_eq_right h1, ite_eq_left h2, map_neg]
      have e : mkQ R N Polynomial.X ^ ((i.val * g) % (2 * N)) =
          -mkQ R N Polynomial.X ^ ((i.val * g) % (2 * N) - N) := by
        conv_lhs => rw [h2]
        rw [pow_add, root_pow_N]; ring
      rw [e]; ring
    · intro k _ hk
      have h1 : (i.val * g) % (2 * N) ≠ k.val := by omega
      have h2 : (i.val * g) % (2 * N) ≠ k.val + N := fun h => hk (Fin.ext (by simp; omega))
      simp [h1, h2]
    · intro h; exact absurd (Finset.mem_univ _) h

theorem toQuot_automorph (g : ℕ) (a : NPoly R N) :
    toQuot (automorph g a) = Ideal.Quotient.mk _ ((toPolynomial a).comp (Polynomial.X ^ g)) := by
  have hcomp : (toPolynomial a).comp (Polynomial.X ^ g) =
      ∑ i : Fin N, Polynomial.C (a.coeff i) * Polynomial.X ^ (i.val * g) := by
    rw [toPolynomial_def, Polynomial.sum_comp]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Polynomial.mul_comp, Polynomial.C_comp, Polynomial.X_pow_comp, ← pow_mul']
  rw [hcomp, toQuot_eq_sum]
  simp only [coeff_automorph', map_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [map_mul, map_pow]
  exact automorph_term g a i

/-- `map f` is coefficient-wise `f` on the anchor representative. Pins `map`, and with it `ofInt`
(which is `map` of the cast `ℤ → ZMod q`). -/
theorem toPolynomial_map {S : Type} [CommRing S] (f : R →+* S) (a : NPoly R N) :
    toPolynomial (map f a) = Polynomial.map f (toPolynomial a) := by
  simp [toPolynomial_def, map, Polynomial.map_sum]

theorem ofInt_eq_map (q : ℕ) (a : IntPoly N) : ofInt q a = map (Int.castRingHom (ZMod q)) a := rfl

/-! ### The commutative ring structure on `NPoly R N`

The pins say that `toQuot` is an injective map (for `0 < N`) preserving every operation, so
Mathlib's ring structure on `R[X]/(X^N + 1)` pulls back along it. The extra data that
`CommRing` needs and `Spec` does not provide (`ℕ`/`ℤ`-scalar multiplication and the casts from
`ℕ`, `ℤ`) is defined coefficient-wise / via `const` below. -/

/-- `ℕ`-scalar multiplication, coefficient by coefficient. -/
instance instSMulNat : SMul ℕ (NPoly R N) := ⟨fun n a => ⟨fun i => n • a.coeff i⟩⟩

/-- `ℤ`-scalar multiplication, coefficient by coefficient. -/
instance instSMulInt : SMul ℤ (NPoly R N) := ⟨fun n a => ⟨fun i => n • a.coeff i⟩⟩

/-- The cast `ℕ → NPoly R N`: the constant polynomial. -/
instance instNatCast : NatCast (NPoly R N) := ⟨fun n => const (n : R)⟩

/-- The cast `ℤ → NPoly R N`: the constant polynomial. -/
instance instIntCast : IntCast (NPoly R N) := ⟨fun n => const (n : R)⟩

@[simp] theorem coeff_nsmul' (n : ℕ) (a : NPoly R N) (i : Fin N) :
    (n • a).coeff i = n • a.coeff i := rfl

@[simp] theorem coeff_zsmul' (n : ℤ) (a : NPoly R N) (i : Fin N) :
    (n • a).coeff i = n • a.coeff i := rfl

theorem natCast_def (n : ℕ) : (n : NPoly R N) = const (n : R) := rfl

theorem intCast_def (n : ℤ) : (n : NPoly R N) = const (n : R) := rfl

theorem nsmul_eq_smul_cast (n : ℕ) (a : NPoly R N) : n • a = (n : R) • a := by
  ext i; simp [nsmul_eq_mul]

theorem zsmul_eq_smul_cast (n : ℤ) (a : NPoly R N) : n • a = (n : R) • a := by
  ext i; simp [zsmul_eq_mul]

theorem toQuot_nsmul (n : ℕ) (a : NPoly R N) : toQuot (n • a) = n • toQuot a := by
  rw [nsmul_eq_smul_cast, toQuot_smul, map_natCast, map_natCast]
  exact (nsmul_eq_mul _ _).symm

theorem toQuot_zsmul (n : ℤ) (a : NPoly R N) : toQuot (n • a) = n • toQuot a := by
  rw [zsmul_eq_smul_cast, toQuot_smul, map_intCast, map_intCast]
  exact (zsmul_eq_mul _ _).symm

theorem toQuot_natCast (hN : 0 < N) (n : ℕ) : toQuot (n : NPoly R N) = n := by
  rw [natCast_def, toQuot_const hN, map_natCast, map_natCast]

theorem toQuot_intCast (hN : 0 < N) (n : ℤ) : toQuot (n : NPoly R N) = n := by
  rw [intCast_def, toQuot_const hN, map_intCast, map_intCast]

/-- `NPoly R N` is a commutative ring, with the `Spec` operations, by transfer along the injective
ring-operation-preserving map `toQuot` into `R[X]/(X^N + 1)`. -/
instance instCommRing [NeZero N] : CommRing (NPoly R N) := fast_instance%
  Function.Injective.commRing toQuot (toQuot_injective (Nat.pos_of_neZero N)) toQuot_zero
    (toQuot_one (Nat.pos_of_neZero N)) toQuot_add toQuot_mul toQuot_neg toQuot_sub toQuot_nsmul
    toQuot_zsmul (toQuot_pow (Nat.pos_of_neZero N)) (toQuot_natCast (Nat.pos_of_neZero N))
    (toQuot_intCast (Nat.pos_of_neZero N))

/-- `const` as a ring homomorphism. -/
def constRingHom [NeZero N] : R →+* NPoly R N where
  toFun := const
  map_one' := rfl
  map_mul' c d := toQuot_injective (Nat.pos_of_neZero N) <| by
    rw [toQuot_mul, toQuot_const (Nat.pos_of_neZero N), toQuot_const (Nat.pos_of_neZero N),
      toQuot_const (Nat.pos_of_neZero N), map_mul, map_mul]
  map_zero' := by ext i; simp
  map_add' c d := by ext i; simp only [coeff_const', coeff_add']; split_ifs <;> simp

/-- `NPoly R N` is an `R`-algebra; its scalar multiplication is the `Spec` one. -/
instance instAlgebra [NeZero N] : Algebra R (NPoly R N) where
  toSMul := NPoly.instSMul
  algebraMap := constRingHom
  commutes' _ _ := mul_comm _ _
  smul_def' c a := toQuot_injective (Nat.pos_of_neZero N) <| by
    show toQuot (c • a) = toQuot (const c * a)
    rw [toQuot_smul, toQuot_mul, toQuot_const (Nat.pos_of_neZero N)]

/-! ### Agreement of the ring structure with the `Spec` operations

`fast_instance%` unfolds the transferred structure, so every data field of `instCommRing` is
literally the corresponding `Spec` instance (resp. the coefficient-wise `ℕ`/`ℤ` actions and casts
defined above). The lemmas below record this; all are `rfl`. In particular a ring-tactic proof
about `+ - * ^ 0 1` on `NPoly R N` is a proof about the `Spec` operations. -/

section Agreement
variable [NeZero N]

/-- The ring's `0` is `Spec`'s `0`. -/
theorem instCommRing_toZero : (instCommRing : CommRing (NPoly R N)).toZero = NPoly.instZero := rfl

/-- The ring's `1` is `Spec`'s `1`. -/
theorem instCommRing_toOne : (instCommRing : CommRing (NPoly R N)).toOne = NPoly.instOne := rfl

/-- The ring's `+` is `Spec`'s `+`. -/
theorem instCommRing_toAdd : (instCommRing : CommRing (NPoly R N)).toAdd = NPoly.instAdd := rfl

/-- The ring's `*` is `Spec`'s negacyclic convolution. -/
theorem instCommRing_toMul : (instCommRing : CommRing (NPoly R N)).toMul = NPoly.instMul := rfl

/-- The ring's `-` (negation) is `Spec`'s. -/
theorem instCommRing_toNeg : (instCommRing : CommRing (NPoly R N)).toNeg = NPoly.instNeg := rfl

/-- The ring's `-` (subtraction) is `Spec`'s. -/
theorem instCommRing_toSub : (instCommRing : CommRing (NPoly R N)).toSub = NPoly.instSub := rfl

/-- The monoid power `x ^ n` of the ring is `Spec`'s `^` (repeated multiplication). -/
theorem instCommRing_toPow :
    @NPow.toPow (NPoly R N) (instCommRing : CommRing (NPoly R N)).toNPow = NPoly.instPowNat := rfl

/-- The ring's `ℕ`-action is the coefficient-wise one, `n • a = (n : R) • a`
(see `nsmul_eq_smul_cast`). -/
theorem instCommRing_toNSMul :
    (instCommRing : CommRing (NPoly R N)).toNSMul = @NSMul.ofSMul _ instSMulNat := rfl

/-- The ring's `ℤ`-action is the coefficient-wise one, `n • a = (n : R) • a`
(see `zsmul_eq_smul_cast`). -/
theorem instCommRing_toZSMul :
    (instCommRing : CommRing (NPoly R N)).toZSMul = @ZSMul.ofSMul _ instSMulInt := rfl

/-- The ring's cast `ℕ → NPoly R N` is `n ↦ const n`. -/
theorem instCommRing_toNatCast :
    (instCommRing : CommRing (NPoly R N)).toNatCast = instNatCast := rfl

/-- The ring's cast `ℤ → NPoly R N` is `n ↦ const n`. -/
theorem instCommRing_toIntCast :
    (instCommRing : CommRing (NPoly R N)).toIntCast = instIntCast := rfl

/-- The algebra's scalar multiplication `c • a` is `Spec`'s `•`. -/
theorem instAlgebra_toSMul : (instAlgebra : Algebra R (NPoly R N)).toSMul = NPoly.instSMul := rfl

/-- The algebra map is `const`. -/
theorem algebraMap_eq_const (c : R) : algebraMap R (NPoly R N) c = const c := rfl

/-- `Spec`'s `•` is multiplication by a constant. -/
theorem smul_eq_const_mul (c : R) (a : NPoly R N) : c • a = const c * a :=
  Algebra.smul_def c a

/-- `toQuot` as a ring isomorphism `NPoly R N ≃+* R[X]/(X^N + 1)`. -/
noncomputable def toQuotRingEquiv : NPoly R N ≃+* Quot R N :=
  RingEquiv.ofBijective
    ({ toFun := toQuot
       map_one' := toQuot_one (Nat.pos_of_neZero N)
       map_mul' := toQuot_mul
       map_zero' := toQuot_zero
       map_add' := toQuot_add } : NPoly R N →+* Quot R N)
    (toQuot_bijective (Nat.pos_of_neZero N))

@[simp] theorem toQuotRingEquiv_apply (a : NPoly R N) : toQuotRingEquiv a = toQuot a := rfl

/-! Sanity checks: ring tactics work on `NPoly R N`. -/

example (a b c : NPoly R N) : a * (b + c) - a * c = b * a := by ring
example (a b : NPoly R N) : (a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2 := by ring
example (a b : NPoly R N) (h : a - b = 0) : a = b := by linear_combination h
example (a b : NPoly R N) (c : R) : c • (a * b) = (c • a) * b := by simp
example (a b : NPoly R N) (i : Fin N) :
    (@HAdd.hAdd _ _ _ (@instHAdd _ (instCommRing.toAdd)) a b).coeff i = a.coeff i + b.coeff i := by
  simp

end Agreement

end Validation.Ring
