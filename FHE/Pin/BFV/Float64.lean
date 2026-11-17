import Spec.Float
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Nat.Log

/-!
# FHE.Pin.BFV.Float64 — an executable, correctly rounded binary64 arithmetic   (UNTRUSTED glue)

`A64 : Spec.Float.Arith` is IEEE 754 binary64 with round-to-nearest, ties-to-even, on the rational
values of floating-point numbers: every operation computes its exact rational result and rounds it
**once** (`round53`). `A64.mulAdd` is the uncontracted `s + a * b` (two roundings); `A64fma` is the
same arithmetic with `mulAdd` one fused multiply-add. No hardware float is used anywhere.

**Range.** `roundP` rounds to `p` significant bits with an unbounded exponent: it is the IEEE
result exactly when the exact value is zero or has magnitude in the normal range
`[2⁻¹⁰²², 2¹⁰²⁴)` of binary64 (no subnormals, no overflow). Every value the transcribed OpenFHE
code computes lies in `[2⁻¹²⁸, 2¹²⁸]` (`Challenge.BFVMul.nu_range`, and the window of
`Spec.Float.InRange`).

**Not proved:** `Spec.Float.Conforms A64` (it holds on paper: the relative error of rounding to
nearest at 53 bits is at most `2⁻⁵³`, and `mulAdd` is one of the two forms by definition). The
arithmetic is validated by execution instead: the `#guard`s below, the agreement of the fast dyadic
form `D` with it on every sum spot-checked by `FHE.Pin.BFV.Algo`, and the bit-for-bit agreement of
the multiplications computed with it with OpenFHE's recorded outputs.

`D` is the same arithmetic on dyadic numbers `m·2^e` (integer mantissa, no rationals), used by the
staged execution.
-/

namespace FHE.Pin.BFV

/-- Round to the nearest integer, ties to even. -/
def rne (x : ℚ) : ℤ :=
  let f := ⌊x⌋
  let r := x - f
  if r < 1 / 2 then f else if 1 / 2 < r then f + 1 else if f % 2 = 0 then f else f + 1

/-- `⌊log₂ x⌋` for `x > 0`. -/
def ilog2 (x : ℚ) : ℤ :=
  let e : ℤ := (Nat.log2 x.num.natAbs : ℤ) - (Nat.log2 x.den : ℤ)
  if (2 : ℚ) ^ e ≤ x then e else e - 1

/-- Round to `p` significant bits, nearest, ties to even, unbounded exponent. -/
def roundP (p : ℕ) (x : ℚ) : ℚ :=
  if x = 0 then 0 else
  let e := ilog2 |x|
  let ulp : ℚ := (2 : ℚ) ^ (e - ((p : ℤ) - 1))
  (rne (x / ulp) : ℚ) * ulp

/-- binary64 rounding. -/
def round53 (x : ℚ) : ℚ := roundP 53 x

/-- **binary64, round to nearest even, no contraction** (`s += a * b` is a rounded product, then
a rounded sum). -/
def A64 : Spec.Float.Arith where
  ofNat n := round53 n
  mul a b := round53 (a * b)
  div a b := round53 (a / b)
  add a b := round53 (a + b)
  fma a b c := round53 (a * b + c)
  mulAdd s a b := round53 (s + round53 (a * b))

/-- **binary64 with contraction**: `s += a * b` is one fused multiply-add. -/
def A64fma : Spec.Float.Arith := { A64 with mulAdd := fun s a b => round53 (a * b + s) }

-- small integers and powers of two are exact; 2^53 + 1 rounds to even; 1/3, 1/10 are the binary64 values
#guard round53 1 == 1 && round53 (1 / 2) == 1 / 2 && round53 (2 ^ 60) == 2 ^ 60
#guard round53 (2 ^ 53 + 1) == 2 ^ 53 && round53 (2 ^ 53 + 3) == 2 ^ 53 + 4
#guard round53 (2 ^ 53 + 2) == 2 ^ 53 + 2 && round53 (-(2 ^ 53 + 1)) == -(2 ^ 53)
#guard A64.div 1 3 == 6004799503160661 / 2 ^ 54
#guard A64.ofNat 1152921504606846883 == 2 ^ 60 - 128 && A64.ofNat (2 ^ 60 - 63) == 2 ^ 60
#guard A64.ofNat (2 ^ 60 - 64) == 2 ^ 60 && A64.ofNat (2 ^ 60 - 192) == 2 ^ 60 - 256
#guard A64.div 1 10 == 3602879701896397 / 2 ^ 55
-- fused and unfused differ: 0.1·10 − 1 is 0 unfused and 2⁻⁵⁴ fused
#guard A64.mulAdd (-1) (A64.div 1 10) 10 == 0
#guard A64fma.mulAdd (-1) (A64.div 1 10) 10 == 1 / 2 ^ 54

/-! ## Dyadic form -/

/-- A dyadic number `m·2^e`. -/
structure D where
  m : Int
  e : Int
  deriving Inhabited

namespace D

def toRat (a : D) : ℚ := (a.m : ℚ) * (2 : ℚ) ^ a.e

/-- `m·2^e` rounded to `p` significant bits (nearest, ties to even). -/
@[inline] def norm (p : Nat) (m : Int) (e : Int) : D :=
  let n := m.natAbs
  let L := Nat.log2 n + 1
  if n == 0 then ⟨0, 0⟩
  else if L ≤ p then ⟨m, e⟩
  else
    let sh := L - p
    let q := n >>> sh
    let r := n - (q <<< sh)
    let half := 1 <<< (sh - 1)
    let q' := if r > half || (r == half && q % 2 == 1) then q + 1 else q
    ⟨if m < 0 then -(q' : Int) else (q' : Int), e + sh⟩

/-- The exact sum (no rounding). -/
@[inline] def addX (a b : D) : D :=
  if a.m == 0 then b else if b.m == 0 then a
  else if a.e ≥ b.e then ⟨a.m * (2 : Int) ^ (a.e - b.e).toNat + b.m, b.e⟩
  else ⟨b.m * (2 : Int) ^ (b.e - a.e).toNat + a.m, a.e⟩

@[inline] def ofNat (n : Nat) : D := norm 53 n 0
@[inline] def mul (a b : D) : D := norm 53 (a.m * b.m) (a.e + b.e)
@[inline] def add (a b : D) : D := let s := addX a b; norm 53 s.m s.e
@[inline] def neg (a : D) : D := ⟨-a.m, a.e⟩
@[inline] def sub (a b : D) : D := add a (neg b)
/-- `a·b + c` rounded once. -/
@[inline] def fma (a b c : D) : D := let s := addX ⟨a.m * b.m, a.e + b.e⟩ c; norm 53 s.m s.e
/-- `s += a * b`, contracted or not. -/
@[inline] def mulAdd (useFma : Bool) (s a b : D) : D := if useFma then fma a b s else add s (mul a b)

/-- A dyadic rational as a `D` (exact; `x` must have a power-of-two denominator). -/
def ofRat (x : ℚ) : D := ⟨x.num, -(Nat.log2 x.den : Int)⟩

/-- `a / b` rounded (through the rational arithmetic; used for tables only). -/
def div (a b : D) : D := ofRat (round53 (a.toRat / b.toRat))

def half : D := ⟨1, -1⟩

/-- `⌊a⌋`. -/
@[inline] def floor (a : D) : Int :=
  if a.e ≥ 0 then a.m * (2 : Int) ^ a.e.toNat else a.m / (2 : Int) ^ (-a.e).toNat

end D

#guard (D.ofNat (2 ^ 53 + 1)).toRat == A64.ofNat (2 ^ 53 + 1)
#guard (D.div (D.ofNat 1) (D.ofNat 10)).toRat == A64.div 1 10
#guard (D.mulAdd false (D.ofNat 1).neg (D.div (D.ofNat 1) (D.ofNat 10)) (D.ofNat 10)).toRat == 0
#guard (D.mulAdd true (D.ofNat 1).neg (D.div (D.ofNat 1) (D.ofNat 10)) (D.ofNat 10)).toRat == 1 / 2 ^ 54
#guard (D.mul (D.ofNat 1152921504606846883) (D.div (D.ofNat 1) (D.ofNat 1152921504606846869))).toRat
  == A64.mul (A64.ofNat 1152921504606846883) (A64.div 1 (A64.ofNat 1152921504606846869))
#guard D.floor (D.add D.half (D.ofNat 7)) == 7 && D.floor ⟨15, -1⟩ == 7 && D.floor ⟨-15, -1⟩ == -8

end FHE.Pin.BFV
