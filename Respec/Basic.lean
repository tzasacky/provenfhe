import Spec.Ring
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Rat.Floor

/-!
# Respec.Basic — conventions shared by the independent re-specification

This library is an *independent* formalization of BGV / BFV / RNS material, written from
the primary literature and from library source code, to be compared with another formalization.
It shares only the ring type `Spec.NPoly` (file `Spec/Ring.lean`).

## Conventions fixed here (every one of them is a place where sources differ)

* **Centred representative** `[x]_q`: the representative in `(-q/2, q/2]`, i.e. `ZMod.valMinAbs`
  (`cmod`). For odd `q` this is the symmetric interval `[-(q-1)/2, (q-1)/2]` and no source
  disagrees. For even `q` (only the plaintext modulus `t = 2^k` in practice) sources differ on the
  tie `q/2`: BGV'12 §2 uses `(-q/2, q/2]`; FV'12 §2 uses `[-q/2, q/2)`; HPS'18 §2.1 uses
  `[-q/2, q/2)`; OpenFHE `NativeVectorT::SwitchModulus` (src/core/lib/math/hal/intnat/
  mubintvecnat.cpp:109-134, v1.2.3) treats `v > ⌊q/2⌋` as negative, i.e. `(-q/2, q/2]`.
* **Canonical representative**: the one in `[0, q)` (`ZMod.val`).
* **Rounding** `⌊a/b⌉` (`rdiv`): nearest integer, ties rounded *up* (`⌊a/b + 1/2⌋`). FV'12 §2
  defines `⌊x⌉` as "rounding to the nearest integer" without fixing ties; HPS'18 §2.1 rounds ties
  up; OpenFHE `MultiplyAndRound` rounds ties up on canonical representatives.

All of these are computable.
-/

namespace Respec

open Spec

/-- Centred remainder: the representative of `x mod q` in `(-q/2, q/2]`.
Source: BGV'12 (ePrint 2011/277) §2 "Basic notation": `[z]_q` denotes the reduction into
`(-q/2, q/2]`. Agrees with `ZMod.valMinAbs`. -/
def cmod (x : ℤ) (q : ℕ) : ℤ :=
  let r := x % (q : ℤ)
  if (q : ℤ) < 2 * r then r - q else r

/-- Canonical remainder in `[0, q)` as an integer. -/
def nmod (x : ℤ) (q : ℕ) : ℤ := x % (q : ℤ)

/-- Round-to-nearest division `⌊a / b⌉`, ties up: `⌊(2a + b) / (2b)⌋`. (`/` on `ℤ` is the
Euclidean/floor division for a positive divisor.) Source: HPS'18 (ePrint 2018/117) §2.1. -/
def rdiv (a : ℤ) (b : ℕ) : ℤ := (2 * a + b) / (2 * (b : ℤ))

/-- Floor division. -/
def fdiv (a : ℤ) (b : ℕ) : ℤ := a / (b : ℤ)

/-- Which integer representative of a residue an algorithm uses when it leaves `ℤ_q`.
Libraries differ, sometimes between two code paths of the same function. -/
inductive Lift
  /-- representative in `[0, q)` -/
  | canonical
  /-- representative in `(-q/2, q/2]` -/
  | centred
  deriving DecidableEq, Repr

/-- The integer representative of `x : ZMod q` selected by a `Lift` convention. -/
def Lift.rep (c : Lift) {q : ℕ} (x : ZMod q) : ℤ :=
  match c with
  | .canonical => (x.val : ℤ)
  | .centred => x.valMinAbs

/-- The worst-case size of a `Lift` representative of a residue modulo `q`, times two
(`2·|rep| ≤ lift2 q`): `2(q-1)` for canonical, `q` for centred. Used in noise bounds. -/
def Lift.bound2 (c : Lift) (q : ℕ) : ℕ :=
  match c with
  | .canonical => 2 * (q - 1)
  | .centred => q

/-! ### Polynomial helpers -/

section Poly
variable {R : Type} {N : ℕ}

/-- Evaluate all coefficients once and store them in an array. Propositionally the identity
(`force_eq`); operationally it stops `#eval` from recomputing nested closures. -/
def force (a : NPoly R N) : NPoly R N :=
  let arr := Array.ofFn a.coeff
  ⟨fun i => arr[i.val]'(by simp [arr])⟩

@[simp] theorem force_eq (a : NPoly R N) : force a = a := by
  ext i; simp [force]

/-- Coefficient list (for display and tests). -/
def coeffs (a : NPoly R N) : List R := List.ofFn a.coeff

/-- Build from a list, padding with a default. -/
def ofList [Inhabited R] (l : List R) : NPoly R N := ⟨fun i => l.getD i.val default⟩

/-- Decidable equality of coefficient vectors (scoped, to avoid clashing with other libraries). -/
scoped instance [DecidableEq R] : DecidableEq (NPoly R N) := fun a b =>
  decidable_of_iff (a.coeff = b.coeff) ⟨fun h => NPoly.ext h, fun h => h ▸ rfl⟩

end Poly

/-! ### Strict ring operations

**Why these exist.** `Spec.NPoly` stores a polynomial as a *function* `Fin N → R`, and the ring
operations of `Spec/Ring.lean` build closures. When an operand of `+`/`*` is itself a compound
expression, compiled code re-evaluates that operand at every coefficient access, which is
exponential in the nesting depth (measured: `force (f n a * a)` recursing 6 levels at `N = 4` does
not terminate in 30 s; the same through `pmul` takes 1 ms). The operations below evaluate their
arguments first (they are ordinary function parameters) and store the result in an array.
Each is *propositionally equal* to the plain operation (`padd_eq`, … are `simp` lemmas), so a
definition written with `⊞ ⊟ ⊠ ⊡` means exactly what it would mean with `+ - * •`. -/

section Strict
variable {R : Type} [CommRing R] {N : ℕ}

/-- Strict `a + b`. -/
@[noinline] def padd (a b : NPoly R N) : NPoly R N := force (a + b)
/-- Strict `a - b`. -/
@[noinline] def psub (a b : NPoly R N) : NPoly R N := force (a - b)
/-- Strict `-a`. -/
@[noinline] def pneg (a : NPoly R N) : NPoly R N := force (-a)
/-- Strict negacyclic product `a * b`. -/
@[noinline] def pmul (a b : NPoly R N) : NPoly R N := force (a * b)
/-- Strict scalar multiple `c • a`. -/
@[noinline] def psmul (c : R) (a : NPoly R N) : NPoly R N := force (c • a)
/-- Strict power, `a ^ n` by repeated multiplication on the right (as `Spec`'s `Pow`). -/
def ppow (a : NPoly R N) : ℕ → NPoly R N
  | 0 => 1
  | n + 1 => pmul (ppow a n) a
/-- Strict sum of a list (left fold from `0`). -/
def psum (l : List (NPoly R N)) : NPoly R N := l.foldl padd 0
/-- Strict Galois automorphism `X ↦ X^g`. -/
@[noinline] def pauto (g : ℕ) (a : NPoly R N) : NPoly R N := force (NPoly.automorph g a)

@[inherit_doc] scoped infixl:65 " ⊞ " => padd
@[inherit_doc] scoped infixl:65 " ⊟ " => psub
@[inherit_doc] scoped infixl:70 " ⊠ " => pmul
@[inherit_doc] scoped infixr:73 " ⊡ " => psmul

@[simp] theorem padd_eq (a b : NPoly R N) : a ⊞ b = a + b := force_eq _
@[simp] theorem psub_eq (a b : NPoly R N) : a ⊟ b = a - b := force_eq _
@[simp] theorem pneg_eq (a : NPoly R N) : pneg a = -a := force_eq _
@[simp] theorem pmul_eq (a b : NPoly R N) : a ⊠ b = a * b := force_eq _
@[simp] theorem psmul_eq (c : R) (a : NPoly R N) : c ⊡ a = c • a := force_eq _
@[simp] theorem pauto_eq (g : ℕ) (a : NPoly R N) : pauto g a = NPoly.automorph g a := force_eq _
@[simp] theorem ppow_eq (a : NPoly R N) (n : ℕ) : ppow a n = a ^ n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [ppow, pmul_eq, ih]; rfl
@[simp] theorem psum_eq (l : List (NPoly R N)) : psum l = l.foldl (· + ·) 0 := by
  unfold psum
  generalize (0 : NPoly R N) = z
  induction l generalizing z with
  | nil => rfl
  | cons x xs ih => simp [List.foldl, ih]

/-- Evaluate every polynomial of a list (the identity, `forceAll_eq`). Needed after a
`List.map (fun k => …)` whose body is a polynomial: such list entries are otherwise stored
unevaluated. -/
def forceAll {R : Type} {N : ℕ} (l : List (NPoly R N)) : List (NPoly R N) := l.map force

omit [CommRing R] in
@[simp] theorem forceAll_eq (l : List (NPoly R N)) : forceAll l = l := by
  induction l with
  | nil => rfl
  | cons x xs ih => simpa [forceAll] using ih

end Strict

section Lifts
variable {N : ℕ}

/-- Integer polynomial from a list. -/
def zpoly (l : List ℤ) : IntPoly N := force ⟨fun i => l.getD i.val 0⟩

/-- Canonical lift `[0,q)` as an *integer* polynomial. -/
@[noinline] def liftN {q : ℕ} (a : Poly q N) : IntPoly N := force ⟨fun i => ((a.coeff i).val : ℤ)⟩

/-- Centred lift `(-q/2, q/2]` (same as `Spec.NPoly.centered`). -/
@[noinline] def liftC {q : ℕ} (a : Poly q N) : IntPoly N := force (NPoly.centered a)

/-- Lift under a convention. -/
@[noinline] def liftBy (c : Lift) {q : ℕ} (a : Poly q N) : IntPoly N :=
  force ⟨fun i => c.rep (a.coeff i)⟩

/-- Reduce an integer polynomial mod `q` (same as `Spec.NPoly.ofInt`). -/
@[noinline] def red (q : ℕ) (a : IntPoly N) : Poly q N := force (NPoly.ofInt q a)

/-- Change modulus through the canonical lift: for `q' ∣ q` this is the ring map
`ℤ_q → ℤ_{q'}`. -/
@[noinline] def castPoly {q : ℕ} (q' : ℕ) (a : Poly q N) : Poly q' N :=
  force ⟨fun i => (((a.coeff i).val : ℕ) : ZMod q')⟩

/-- Multiply a polynomial mod `q` by an integer constant. -/
@[noinline] def zsmul {q : ℕ} (c : ℤ) (a : Poly q N) : Poly q N := force ((c : ZMod q) • a)

/-- Integer scalar times integer polynomial. -/
@[noinline] def zscale (c : ℤ) (a : IntPoly N) : IntPoly N := force (c • a)

@[simp] theorem liftC_eq {q : ℕ} (a : Poly q N) : liftC a = NPoly.centered a := force_eq _
@[simp] theorem red_eq (q : ℕ) (a : IntPoly N) : red q a = NPoly.ofInt q a := force_eq _
@[simp] theorem zsmul_eq {q : ℕ} (c : ℤ) (a : Poly q N) : zsmul c a = (c : ZMod q) • a := force_eq _
@[simp] theorem zscale_eq (c : ℤ) (a : IntPoly N) : zscale c a = c • a := force_eq _

/-- `∞`-norm of the centred lift. -/
def cnorm {q : ℕ} (a : Poly q N) : ℕ := NPoly.normInf (liftC a)

/-- `ℓ₁` norm of an integer polynomial (appears in worst-case product bounds:
`‖a·b‖∞ ≤ ‖a‖₁·‖b‖∞`). -/
def norm1 (a : IntPoly N) : ℕ := ∑ i : Fin N, (a.coeff i).natAbs

/-- Every coefficient is divisible by `d`. -/
def DivisibleBy (d : ℕ) (a : IntPoly N) : Prop := ∀ i, (d : ℤ) ∣ a.coeff i

instance (d : ℕ) (a : IntPoly N) : Decidable (DivisibleBy d a) :=
  inferInstanceAs (Decidable (∀ i : Fin N, (d : ℤ) ∣ a.coeff i))

/-- Coefficient-wise exact/floor division of an integer polynomial. -/
@[noinline] def zdiv (a : IntPoly N) (d : ℕ) : IntPoly N := force ⟨fun i => a.coeff i / (d : ℤ)⟩

/-- The coefficient list of the product of two "polynomials in `Y`" given as lists
(`c_k = Σ_{i+j=k} a_i·b_j`), over any type with a product, a sum and a zero. Used for the
ciphertext tensor product in several representations. -/
def tensorWith {α : Type} (mul add : α → α → α) (zero : α) (a b : List α) : List α :=
  (List.range (a.length + b.length - 1)).map fun k =>
    ((List.range (k + 1)).map fun i =>
      match a[i]?, b[k - i]? with
      | some x, some y => mul x y
      | _, _ => zero).foldl add zero

/-- Sum of a list of ring elements using only `+` and `0`. -/
def lsum {α : Type} [Add α] [Zero α] (l : List α) : α := l.foldl (· + ·) 0

/-- A finite family stored in an array (used to memoize `Fin n → α`).

**Compilation note.** A Lean definition whose result type is a bare function type is compiled as
a function of higher arity, so `def memo f := let arr := Array.ofFn f; fun i => arr[i]` does
*not* memoize: a partial application `memo f` recomputes `arr` at every call (measured). A value
of a `structure` type is evaluated once. Hence the table is a structure, and callers store
`(Table.ofFn f).get`, whose table argument is an evaluated value. -/
structure Table (n : ℕ) (α : Type) where
  /-- the entries -/
  arr : Array α
  /-- there are `n` of them -/
  size_eq : arr.size = n

/-- Tabulate a finite family. -/
def Table.ofFn {n : ℕ} {α : Type} (f : Fin n → α) : Table n α := ⟨Array.ofFn f, by simp⟩

/-- Look up an entry. -/
def Table.get {n : ℕ} {α : Type} (t : Table n α) (i : Fin n) : α :=
  t.arr[i.val]'(by rw [t.size_eq]; exact i.isLt)

@[simp] theorem Table.get_ofFn {n : ℕ} {α : Type} (f : Fin n → α) (i : Fin n) :
    (Table.ofFn f).get i = f i := by
  simp [Table.get, Table.ofFn]

end Lifts

/-! ### Sanity checks of the conventions -/

#guard cmod 7 5 = 2 ∧ cmod 8 5 = -2 ∧ cmod (-8) 5 = 2 ∧ cmod 2 4 = 2 ∧ cmod (-2) 4 = 2
#guard (List.range 12).all fun x => cmod x 12 = ((x : ZMod 12)).valMinAbs
#guard (List.range 11).all fun x => cmod (x : ℤ) 11 = ((x : ZMod 11)).valMinAbs
#guard rdiv 7 2 = 4 ∧ rdiv (-7) 2 = -3 ∧ rdiv 5 3 = 2 ∧ rdiv 4 3 = 1 ∧ rdiv (-4) 3 = -1
-- X^3 * X = X^4 = -1 in Z[X]/(X^4+1)
#guard coeffs ((zpoly [0, 0, 0, 1] : IntPoly 4) ⊠ zpoly [0, 1]) = [-1, 0, 0, 0]
#guard coeffs (ppow (zpoly [0, 1] : IntPoly 4) 5) = [0, -1, 0, 0]
-- sigma_3 (X) = X^3 ; sigma_3 (X^3) = X^9 = X
#guard coeffs (NPoly.automorph 3 (zpoly [0, 1, 0, 5] : IntPoly 4)) = [0, 5, 0, 1]

end Respec
