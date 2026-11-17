import Mathlib.Data.Rat.Floor
import Mathlib.Algebra.Order.Field.Basic

/-!
# Spec.Float — the standard model of binary64 arithmetic   (TRUSTED)

OpenFHE's HPS-family BFV multiplications compute two sums in `double`
(`Challenge.BFVMul.Float`). What is assumed of that arithmetic is stated here, as a predicate on
an abstract arithmetic, and nowhere else: the theorems about the floating-point code quantify
over *every* arithmetic satisfying `Conforms`. Nothing here is a Lean axiom, and no IEEE 754
encoding is formalised.

**The model.** A floating-point number is represented by the rational number it denotes (every
finite binary64 value is a rational). An `Arith` gives the four operations the code uses
(conversion of an unsigned 64-bit integer to `double`, `*`, `/`, `+`), a fused multiply-add, and
the compiled form `mulAdd` of the C++ statement `s += a * b`. `Conforms` is the *standard model of
floating-point arithmetic* (Higham, *Accuracy and Stability of Numerical Algorithms*, 2nd ed.,
§2.2, model (2.4)), with unit roundoff `u = 2⁻⁵³`:

  `fl(x op y) = (x op y)·(1 + δ)`,   `|δ| ≤ u`,

required only when the exact result `x op y` is zero or has magnitude in `[2⁻¹²⁸, 2¹²⁸]`
(`InRange`); outside that window nothing is assumed. The operations are functions on all
rationals; `Conforms` constrains them on all rational arguments, which is more than hardware
offers (hardware operations take floating-point arguments only), and the code applies them only
to results of earlier operations. An arithmetic defined on floating-point numbers only is
covered by extending it arbitrarily within the model (for instance by the exact operation).

**What a reader must believe for a given build of the library**, in order to apply a theorem
stated for all conforming arithmetics to it:

1. `double` is IEEE 754 binary64 and every operation below is rounded to nearest (either tie
   rule): then the relative error of a result whose exact value has magnitude in
   `[2⁻¹⁰²², 2¹⁰²⁴·(1 − 2⁻⁵⁴))` (the normal range, no overflow) is at most `2⁻⁵³/(1 + 2⁻⁵³)`, and
   an exact zero is returned as zero. The window `[2⁻¹²⁸, 2¹²⁸]` of `InRange` lies inside that
   range, so the hypothesis here is weaker. No property of subnormal numbers, infinities, NaNs,
   signed zeros or exception flags is used.
2. *Conversion* `static_cast<double>(n)` of an unsigned 64-bit integer is correctly rounded to
   nearest. (ISO C++ alone leaves the choice between the two neighbouring values to the
   implementation; IEEE 754 `convertFromInt`, which C Annex F binds the cast to, rounds in the
   current mode. AArch64 has the unsigned instruction `ucvtf`. x86-64 before AVX-512 has only the
   signed `cvtsi2sd`: compilers use it directly for values below `2⁶³` (every value this code
   converts is below `2⁶⁰` under `Challenge.BFVMul.floatBasisOK`) and emit a halve-with-sticky-bit
   sequence above, which is also correctly rounded.) No
   exactness of small integers is assumed: `ofNat n = n·(1 + δ)` for every `n < 2⁶⁴`.
3. *Evaluation precision*: every operation is rounded once, to binary64 (`FLT_EVAL_METHOD == 0`:
   x86-64 with SSE2, AArch64). x87 extended-precision evaluation (32-bit x86 without SSE2)
   rounds twice and can exceed `u`; it is NOT covered.
4. *No value-changing optimisation*: no `-ffast-math`, `-fassociative-math`,
   `-freciprocal-math` or the like (the sums are evaluated in source order, a division is a
   division). OpenFHE v1.6.1 builds with `-O3` and none of these (`CMakeLists.txt:254-255` of commit b59e1f29).
5. *Contraction is covered*: a compiler may or may not fuse `s += a * b` into one fused
   multiply-add (`-ffp-contract`; GCC contracts by default where the target has FMA, e.g. on
   AArch64 or under `-march=native`). `mulAdd` is any function that at every argument triple
   equals one of the two forms, so the choice may differ from one loop iteration to the next.
6. The rounding mode is not changed from round-to-nearest while the library runs.

The transcriptions that use this model are of OpenFHE v1.6.1 built with its default CMake
options, in particular `WITH_REDUCED_NOISE=OFF` (`CMakeLists.txt:95`): a build with that option
on is not covered.

Truncation of a nonnegative `double` to an unsigned integer (`static_cast<size_t>`) is exact
whenever the value is below the range of the integer type; it is `Int.floor` in the
transcription and is not part of the model.
-/

namespace Spec.Float

/-- The unit roundoff of binary64 under round-to-nearest: `2⁻⁵³`. -/
def u : ℚ := 1 / 2 ^ 53

/-- The exact results for which the model promises anything: zero, or magnitude in
`[2⁻¹²⁸, 2¹²⁸]` (far inside the normal range of binary64). -/
def InRange (x : ℚ) : Prop := x = 0 ∨ (1 / 2 ^ 128 ≤ |x| ∧ |x| ≤ 2 ^ 128)

/-- `y` is `x` rounded with relative error at most `u`: `y = x·(1 + δ)`, `|δ| ≤ u`. -/
def Rounds (x y : ℚ) : Prop := ∃ δ : ℚ, |δ| ≤ u ∧ y = x * (1 + δ)

/-- An arithmetic: the floating-point operations the transcribed code uses, on the rational
values of floating-point numbers (module docstring). -/
structure Arith where
  /-- `static_cast<double>(n)` for an unsigned 64-bit integer `n`. -/
  ofNat : ℕ → ℚ
  /-- `a * b` -/
  mul : ℚ → ℚ → ℚ
  /-- `a / b` -/
  div : ℚ → ℚ → ℚ
  /-- `a + b` -/
  add : ℚ → ℚ → ℚ
  /-- `fma(a, b, c)`: `a·b + c` rounded once. -/
  fma : ℚ → ℚ → ℚ → ℚ
  /-- The compiled form of `s += a * b` (arguments `s`, `a`, `b`): contracted or not. -/
  mulAdd : ℚ → ℚ → ℚ → ℚ

/-- **The standard model** (module docstring): each operation returns its exact result with
relative error at most `u = 2⁻⁵³` whenever that exact result is `InRange`, and `mulAdd` is, at
each argument triple, either `add s (mul a b)` or `fma a b s`. -/
structure Conforms (A : Arith) : Prop where
  ofNat : ∀ n : ℕ, n < 2 ^ 64 → Rounds (n : ℚ) (A.ofNat n)
  mul : ∀ a b : ℚ, InRange (a * b) → Rounds (a * b) (A.mul a b)
  div : ∀ a b : ℚ, b ≠ 0 → InRange (a / b) → Rounds (a / b) (A.div a b)
  add : ∀ a b : ℚ, InRange (a + b) → Rounds (a + b) (A.add a b)
  fma : ∀ a b c : ℚ, InRange (a * b + c) → Rounds (a * b + c) (A.fma a b c)
  mulAdd : ∀ s a b : ℚ, A.mulAdd s a b = A.add s (A.mul a b) ∨ A.mulAdd s a b = A.fma a b s

/-- The two truncated sums an HPS-family multiplication takes from floating point
(`Challenge.BFVMul.Float`): `sw qs y` is the overflow count of a base switch from the moduli `qs`
with digits `y`; `sr ms ns x` is the truncated fractional sum of a scaling with input moduli
`ms`, table numerators `ns` and residues `x`. A plain record of two functions; what they are for
the library is `Challenge.BFVMul.Fl.floatSums`. -/
structure Sums where
  sw : List ℕ → List ℤ → ℤ
  sr : List ℕ → List ℤ → List ℤ → ℤ

/-- The exact arithmetic (no rounding at all): it conforms (`Challenge.BFVMul.exact_conforms`),
so the model is satisfiable, and the transcription run with it is the idealised algorithm. -/
def exact : Arith :=
  { ofNat := fun n => n, mul := (· * ·), div := (· / ·), add := (· + ·),
    fma := fun a b c => a * b + c, mulAdd := fun s a b => s + a * b }

end Spec.Float
