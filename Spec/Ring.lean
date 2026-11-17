import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.ZMod.ValMinAbs
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.RingTheory.Ideal.Span

/-!
# Spec.Ring — the negacyclic ring R[X]/(X^N + 1)   (TRUSTED)

`NPoly R N` stores an element of `R[X]/(X^N + 1)` as its `N` coefficients. Every operation here
is computable so that it can be executed in differential tests.

**Anchor.** `NPoly.toQuot` sends a coefficient vector to the class of `Σ aᵢ Xⁱ` in Mathlib's
quotient ring. The pins `Challenge.Ring.toQuot_*` (`Challenge/Ring.lean`) state that `toQuot` is
a bijective ring homomorphism and that `automorph` is substitution `X ↦ X^g`. With those proved,
the operations below mean exactly what Mathlib means by them, whoever wrote them.
-/

namespace Spec

/-- An element of `R[X]/(X^N + 1)`, stored as the coefficients of its representative of degree
`< N`: `coeff i` is the coefficient of `X^i`. -/
@[ext]
structure NPoly (R : Type) (N : ℕ) where
  coeff : Fin N → R

/-- `Z_q[X]/(X^N + 1)`. -/
abbrev Poly (q N : ℕ) := NPoly (ZMod q) N

/-- Integer polynomials of degree `< N`. Used for noise terms and secrets, never reduced. -/
abbrev IntPoly (N : ℕ) := NPoly ℤ N

namespace NPoly

variable {R : Type} {N : ℕ}

section Ops
variable [CommRing R]

instance : Zero (NPoly R N) := ⟨⟨fun _ => 0⟩⟩
/-- The constant polynomial `1`. -/
instance : One (NPoly R N) := ⟨⟨fun i => if i.val = 0 then 1 else 0⟩⟩
instance : Add (NPoly R N) := ⟨fun a b => ⟨fun i => a.coeff i + b.coeff i⟩⟩
instance : Neg (NPoly R N) := ⟨fun a => ⟨fun i => -a.coeff i⟩⟩
instance : Sub (NPoly R N) := ⟨fun a b => ⟨fun i => a.coeff i - b.coeff i⟩⟩
/-- Scalar multiplication, coefficient by coefficient. -/
instance : SMul R (NPoly R N) := ⟨fun c a => ⟨fun i => c * a.coeff i⟩⟩

/-- Negacyclic convolution (`X^N = -1`). Coefficient `k` of `a * b` is
`Σ_{i ≤ k} aᵢ·b_{k-i} − Σ_{i > k} aᵢ·b_{N+k-i}`. -/
instance : Mul (NPoly R N) :=
  ⟨fun a b => ⟨fun k => ∑ i : Fin N,
    if h : i.val ≤ k.val then
      a.coeff i * b.coeff ⟨k.val - i.val, by have := k.isLt; omega⟩
    else
      -(a.coeff i * b.coeff ⟨N + k.val - i.val, by have := k.isLt; have := i.isLt; omega⟩)⟩⟩

/-- `a ^ n` by repeated multiplication. -/
instance : Pow (NPoly R N) ℕ := ⟨fun a n => Nat.rec 1 (fun _ acc => acc * a) n⟩

/-- The constant polynomial `c`. -/
def const (c : R) : NPoly R N := ⟨fun i => if i.val = 0 then c else 0⟩

/-- The Galois automorphism `X ↦ X^g` (meaningful for odd `g`). Since `X^N = -1`, the monomial
`Xⁱ` goes to `X^{(i·g) mod 2N}`, which is `+X^j` if `(i·g) mod 2N = j < N` and `-X^j` if it is
`j + N`. -/
def automorph (g : ℕ) (a : NPoly R N) : NPoly R N :=
  ⟨fun k => ∑ i : Fin N,
    if (i.val * g) % (2 * N) = k.val then a.coeff i
    else if (i.val * g) % (2 * N) = k.val + N then -a.coeff i
    else 0⟩

/-- Apply a ring map to every coefficient. -/
def map {S : Type} (f : R → S) (a : NPoly R N) : NPoly S N := ⟨fun i => f (a.coeff i)⟩

end Ops

/-! ### Anchor to Mathlib -/

open Polynomial in
/-- The Mathlib ring `NPoly R N` is meant to be: `R[X] ⧸ (X^N + 1)`. -/
abbrev Quot (R : Type) [CommRing R] (N : ℕ) : Type :=
  R[X] ⧸ Ideal.span {(X ^ N + 1 : R[X])}

open Polynomial in
/-- The representative `Σ aᵢ Xⁱ` as a Mathlib polynomial. -/
noncomputable def toPolynomial [CommRing R] (a : NPoly R N) : R[X] :=
  ∑ i : Fin N, C (a.coeff i) * X ^ (i : ℕ)

/-- **The anchor**: the class of `Σ aᵢ Xⁱ` in `R[X]/(X^N + 1)`. -/
noncomputable def toQuot [CommRing R] (a : NPoly R N) : Quot R N :=
  Ideal.Quotient.mk _ (toPolynomial a)

/-! ### Integers, residues and norms -/

/-- Reduce an integer polynomial modulo `q`. -/
def ofInt (q : ℕ) (a : IntPoly N) : NPoly (ZMod q) N := ⟨fun i => (a.coeff i : ZMod q)⟩

/-- Centered lift: each coefficient to its representative in `(-q/2, q/2]` (`ZMod.valMinAbs`). -/
def centered {q : ℕ} (a : NPoly (ZMod q) N) : IntPoly N := ⟨fun i => (a.coeff i).valMinAbs⟩

/-- Canonical lift: each coefficient to its representative in `[0, q)`. -/
def canonical {q : ℕ} (a : NPoly (ZMod q) N) : NPoly ℕ N := ⟨fun i => (a.coeff i).val⟩

/-- Infinity norm of an integer polynomial. -/
def normInf (a : IntPoly N) : ℕ := Finset.univ.sup fun i => (a.coeff i).natAbs

/-- Every coefficient of a rational polynomial has absolute value at most `B`. -/
def BoundedQ (a : NPoly ℚ N) (B : ℚ) : Prop := ∀ i, |a.coeff i| ≤ B

instance (a : NPoly ℚ N) (B : ℚ) : Decidable (BoundedQ a B) :=
  inferInstanceAs (Decidable (∀ i : Fin N, |a.coeff i| ≤ B))

end NPoly
end Spec
