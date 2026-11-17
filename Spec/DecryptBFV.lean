import Spec.Float
import Spec.Scheme

/-!
# Spec.DecryptBFV — OpenFHE's floating-point BFV decryption, transcribed   (TRUSTED)

OpenFHE v1.6.1 decrypts a BFV ciphertext that still has all its limbs, under the multiplication
techniques `HPS`, `HPSPOVERQ` and `HPSPOVERQLEVELED`, with the overload
`DCRTPolyImpl::ScaleAndRound(t, tQHatInvModqDivqModt, …, tQHatInvModqDivqFrac,
tQHatInvModqBDivqFrac)` (`PKEBFVRNS::Decrypt`, `src/pke/lib/scheme/bfvrns/bfvrns-pke.cpp:238-248`).
It computes `[⌊t·x/Q⌉]_t` of the phase `x` from the residues `xᵢ = x mod qᵢ` without
reconstructing `x`, partly in `double`. This file transcribes that computation, operation by
operation, for one coefficient (`decrypt1`), together with the tables it reads (`tables`), and
the whole polynomial from a ciphertext (`bfvDecryptLib`); it also defines the side conditions
and the margin (`decParamsOK?`, `delta`, `decLibOK?`) of the locked statements in
`Challenge/BFVDecrypt.lean`.

Source: upstream OpenFHE v1.6.1, tag `v1.6.1`, commit
`b59e1f291965f14fbee5172cd83a20f5b856204f`. File and line numbers are that commit's.
`NATIVEINT == 64`, `HAVE_INT128`, `NATIVEINT_DO_CHECKS == false` (`ubintnat.h:64`; the installed
`config_core.h` of the project's build has `NATIVEINT 64`, `HAVE_INT128 TRUE`).
`D` = `src/core/include/lattice/hal/default/dcrtpoly-impl.h`,
`C` = `src/pke/lib/scheme/bfvrns/bfvrns-cryptoparameters.cpp`,
`U` = `src/core/include/math/hal/intnat/ubintnat.h`.

## What is transcribed and what is not

* *Transcribed*: `D:1220-1490` (all eight code paths of the overload, selected exactly as the
  code selects them, `pathSplit`, `pathReduce`, `isPow2`), and the tables `C:432-481`
  (`tables`). Every `double` operation is an operation of an arithmetic `A : ArithD`
  (below); every `uint64_t`/`NativeInteger` operation is natural-number arithmetic with the
  wrap-around of the machine operation written out (`mulFast`, `addFast`, `subFast`, `lshift`),
  so that the statements can PROVE that nothing wraps.
* *Modelled as exact, NOT verified*: `ModMulFastConst(Eq)` (`U:1248-1270`, Shoup's
  multiplication with a precomputed quotient) is `a·b mod t` (`modMulConst`); the big-integer
  table arithmetic of `C:444-479` (`BigInteger` division, `Mod`, `ModInverse`, `LShiftEq`) is
  exact integer arithmetic.
* *Not transcribed, outside this file*: `DecryptCore` (`c₀ + c₁·s + …` limb by limb, in NTT
  form, word-level modular arithmetic) and the switch to coefficient form. `bfvDecryptLib`
  starts from the canonical residues `x mod qᵢ ∈ [0, qᵢ)` of the exact phase
  `⟨ct, (1, s, …)⟩ mod Q` (`Spec.Scheme.phase`): that `DecryptCore` and the inverse NTT produce
  exactly these residues is assumed, not proved. Also not transcribed: the decoding of the
  returned `NativePoly` (`PackedEncoding::Decode` etc.).
* *Transcribed in other files*: the other decryption paths of `PKEBFVRNS::Decrypt` are in
  `Spec.DecryptBFVBEHZ` (multiplication technique `BEHZ`, `bfvrns-pke.cpp:249-253`) and
  `Spec.DecryptBFVLow` (ciphertexts with fewer limbs than `Q`, `:254-275`); the choice between
  the three routines is `Spec.DecryptBFVLib`.
* The loop over limbs (`D:1260-1268` etc.) updates two independent accumulators (`floatSum`,
  `intSum`); the transcription runs the two folds one after the other, which computes the same
  two values.

## The arithmetic

`Spec.Float.Arith` has no subtraction. The code computes `floatSum -= td * q` (`D:1387`,
`:1414`, `:1448`, `:1474`), which a compiler may contract into one fused negative
multiply-add. `ArithD` adds the two operations and the compiled form; `ConformsD` is
`Spec.Float.Conforms` of the base arithmetic plus the standard-model clauses for the new
operations, plus one clause for results of magnitude below `2⁻¹²⁸` (`subSmall`, `fnmaSmall`).
`Spec.Float.Arith`/`Conforms` are not changed.

**What a reader must believe of a build** to apply a theorem stated for every `ConformsD`
arithmetic: items 1-6 of the docstring of `Spec.Float` (binary64, round to nearest, one rounding
per operation, no value-changing optimisation, contraction allowed, rounding mode unchanged), and
in addition:

7. the conversions `static_cast<double>(int64_t)` of the table numerators and denominators
   (`C:451-453`, `:465-467`, `:476-477`) are correctly rounded (they are converted with
   `A.ofNat`: the value converted is nonnegative and below `2⁶⁰`, where signed and unsigned
   conversion round the same value);
8. subtraction `a - b` and `fnmadd` (`c - a·b` rounded once) are correctly rounded;
   `s -= a * b` compiles to one of the two forms at each execution (`mulSub`);
9. a subtraction or `fnmadd` whose exact result has magnitude below `2⁻¹²⁸` returns a value of
   magnitude at most `2⁻¹²⁸` (true of every rounding to nearest, since `2⁻¹²⁸` is representable
   and rounding is monotone; gradual underflow is not needed);
10. integers up to `2⁵³` are exact: the conversion of an integer `n ≤ 2⁵³` returns `n`, and the
   product of two such integers whose value is at most `2⁵³` is returned exactly (every rounding
   returns a representable exact result unchanged, and these integers are representable).
   `Spec.Float.Conforms` alone does not assume this; it is used only for the non-power-of-two
   reduction `td * q` and the conversion of `intSum`.

`static_cast<uint64_t>(v)` of a `double` truncates toward zero (`truncU64`); it is defined
behaviour only for `-1 < v < 2⁶⁴`, and the statements prove that every argument is in
`[0, 2⁶⁴)`.
-/

namespace Spec.DecryptBFV
open Spec.Float Spec.Scheme NPoly

/-! ## The arithmetic -/

/-- A binary64 arithmetic for the decryption code: the operations of `Spec.Float.Arith` plus
subtraction, the fused negative multiply-add, and the compiled form of `s -= a * b`. -/
structure ArithD where
  /-- The operations of `Spec.Float.Arith` (conversion, `*`, `/`, `+`, `fma`, `s += a*b`). -/
  base : Arith
  /-- `a - b` -/
  sub : ℚ → ℚ → ℚ
  /-- `fnmadd(a, b, c)`: `c - a·b` rounded once. -/
  fnma : ℚ → ℚ → ℚ → ℚ
  /-- The compiled form of `s -= a * b` (arguments `s`, `a`, `b`): contracted or not. -/
  mulSub : ℚ → ℚ → ℚ → ℚ

/-- **The standard model for `ArithD`** (module docstring, items 1-9): the base arithmetic
conforms (`Spec.Float.Conforms`); `sub` and `fnma` return their exact result with relative error
at most `u` whenever it is `InRange`, and a result of magnitude at most `2⁻¹²⁸` whenever the
exact one has magnitude below `2⁻¹²⁸`; `mulSub` is, at each argument triple, either
`sub s (mul a b)` or `fnma a b s`; integers up to `2⁵³` and their products up to `2⁵³` are
exact. -/
structure ConformsD (A : ArithD) : Prop where
  base : Conforms A.base
  sub : ∀ a b : ℚ, InRange (a - b) → Rounds (a - b) (A.sub a b)
  fnma : ∀ a b c : ℚ, InRange (c - a * b) → Rounds (c - a * b) (A.fnma a b c)
  subSmall : ∀ a b : ℚ, |a - b| < 1 / 2 ^ 128 → |A.sub a b| ≤ 1 / 2 ^ 128
  fnmaSmall : ∀ a b c : ℚ, |c - a * b| < 1 / 2 ^ 128 → |A.fnma a b c| ≤ 1 / 2 ^ 128
  mulSub : ∀ s a b : ℚ,
    A.mulSub s a b = A.sub s (A.base.mul a b) ∨ A.mulSub s a b = A.fnma a b s
  ofNatExact : ∀ n : ℕ, n ≤ 2 ^ 53 → A.base.ofNat n = n
  mulExact : ∀ a b : ℕ, a * b ≤ 2 ^ 53 → A.base.mul a b = a * b

/-- The exact arithmetic (no rounding at all), extended. -/
def exactD : ArithD :=
  { base := Spec.Float.exact, sub := (· - ·), fnma := fun a b c => c - a * b,
    mulSub := fun s a b => s - a * b }

/-! ## Machine integers -/

/-- `GetMSB` (`src/core/include/math/nbtheory.h:164-193`, and `NativeInteger::GetMSB`,
`U:1459-1461`): the bit length, `0` for `0`, `k + 1` for `x ∈ [2ᵏ, 2ᵏ⁺¹)`. -/
def msb (x : ℕ) : ℕ := Nat.size x

/-- `IsPowerOfTwo` (`src/core/include/utils/utilities.h:57-60`): `x ≠ 0 && !(x & (x - 1))`. -/
def isPow2 (x : ℕ) : Bool := x != 0 && (x &&& (x - 1)) == 0

/-- `MulEqFast` (`U:594-596`): the 64-bit product, wrapping. -/
def mulFast (a b : ℕ) : ℕ := a * b % 2 ^ 64

/-- `AddEqFast` (`U:451-453`), and `operator+=` (`U:426-428`, which is `AddEqFast` since
`NATIVEINT_DO_CHECKS` is `false`, `U:64`): the 64-bit sum, wrapping. -/
def addFast (a b : ℕ) : ℕ := (a + b) % 2 ^ 64

/-- `SubEqFast` (`U:516-518`): the 64-bit difference, wrapping (`a, b < 2⁶⁴`). -/
def subFast (a b : ℕ) : ℕ := (a + (2 ^ 64 - b % 2 ^ 64)) % 2 ^ 64

/-- `LShift` (`U:1369-1371`): `a << k`, wrapping. -/
def lshift (a k : ℕ) : ℕ := a * 2 ^ k % 2 ^ 64

/-- `RShift` (`U:1389-1391`): `a >> k`. -/
def rshift (a k : ℕ) : ℕ := a / 2 ^ k

/-- `ModMulFastConst(Eq)(b, t, bPrecon)` (`U:1248-1270`), modelled as exact: `a·b mod t`
(NOT verified: the word-level Shoup multiplication is assumed to compute this for `b < t`). -/
def modMulConst (a b t : ℕ) : ℕ := a * b % t

/-- `static_cast<uint64_t>(v)` of a `double`: truncation toward zero. Defined behaviour only
for `-1 < v < 2⁶⁴` (outside, the value here is arbitrary; the statements prove the range). -/
def truncU64 (v : ℚ) : ℕ := (if 0 ≤ v then ⌊v⌋ else ⌈v⌉).toNat

/-! ## Path selection (`D:1228-1243`, `:1246`, `:1251`, `:1301-1302`, `:1361`, `:1366`,
`:1420-1421`) -/

/-- `qMSB` (`D:1228-1234`): `GetMSB` of the largest modulus. -/
def qMSB (qs : List ℕ) : ℕ := msb (qs.foldr max 0)

/-- `sizeQMSB` (`D:1238`): `GetMSB(sizeQ)`; the tables use `GetMSB64(sizeQ)` (`C:436`), which is
the same function (`nbtheory.h:197-199`). -/
def sizeQMSB (qs : List ℕ) : ℕ := msb qs.length

/-- `qMSBHf = qMSB >> 1` (`D:1301`, `:1420`; `C:458`). -/
def qMSBHf (qs : List ℕ) : ℕ := qMSB qs / 2

/-- The residues are split at `2^qMSBHf` ("split" paths): `qMSB + sizeQMSB < 52` fails
(`D:1246`, `:1361`; the tables `C:441`). -/
def pathSplit (qs : List ℕ) : Bool := !decide (qMSB qs + sizeQMSB qs < 52)

/-- The integer products are reduced mod `t` term by term (`ModMulFastConst`) rather than
accumulated unreduced (`MulEqFast`): the negation of the inner test (`D:1251`, `:1302`, `:1366`,
`:1421`). -/
def pathReduce (t : ℕ) (qs : List ℕ) : Bool :=
  if isPow2 t then
    if pathSplit qs then !decide (qMSBHf qs + msb t + sizeQMSB qs < 62)
    else !decide (qMSB qs + sizeQMSB qs + msb t < 63)
  else
    if pathSplit qs then !decide (qMSBHf qs + msb t + sizeQMSB qs < 52)
    else !decide (qMSB qs + msb t + sizeQMSB qs < 52)

/-! ## The tables (`C:432-481`) -/

/-- `ModInverse` of the big-integer library: the inverse of `a` modulo `q` in `[0, q)`. -/
def invMod (a q : ℕ) : ℕ := ((a : ZMod q)⁻¹).val

/-- `tQHatInvModqi = (Q/qᵢ).ModInverse(qᵢ) · t` (`C:446-447`, `:461-462`): NOT reduced mod `qᵢ`. -/
def theta (t : ℕ) (qs : List ℕ) (q : ℕ) : ℕ := invMod (qs.prod / q) q * t

/-- The entries of the four tables for one modulus. -/
structure Tab where
  /-- `tQHatInvModqDivqModt[i]` -/
  intLo : ℕ
  /-- `tQHatInvModqDivqFrac[i]` -/
  fracLo : ℚ
  /-- `tQHatInvModqBDivqModt[i]` (split paths only; `0` otherwise: the vector is empty) -/
  intHi : ℕ
  /-- `tQHatInvModqBDivqFrac[i]` (split paths only; `0` otherwise: the vector is empty) -/
  fracHi : ℚ

/-- `static_cast<double>(numerator) / static_cast<double>(denominator)` with `int64_t`
numerator `n` and denominator `q` (`C:451-453`, `:465-467`, `:476-477`). -/
def frac (A : Arith) (n q : ℕ) : ℚ := A.div (A.ofNat n) (A.ofNat q)

/-- The tables (`C:432-481`): for each modulus `qᵢ`, with `θ = theta t qs qᵢ`:
`⌊θ/qᵢ⌋ mod t` and `fl(θ mod qᵢ)/fl(qᵢ)`; on the split branch also the same for `θ·2^qMSBHf`
(`tQHatInvModqi.LShiftEq(qMSBHf)`, `C:471`). -/
def tables (A : Arith) (t : ℕ) (qs : List ℕ) : List Tab :=
  qs.map fun q =>
    let θ := theta t qs q
    let θB := θ * 2 ^ qMSBHf qs
    { intLo := θ / q % t, fracLo := frac A (θ % q) q,
      intHi := if pathSplit qs then θB / q % t else 0,
      fracHi := if pathSplit qs then frac A (θB % q) q else 0 }

/-! ## One coefficient (`D:1255-1272`, `:1282-1298`, `:1306-1329`, `:1330-1352`,
`:1370-1390`, `:1400-1417`, `:1425-1451`, `:1452-1477`) -/

/-- The words one residue `x` contributes, each with its two table entries: `x` itself, or on
the split paths `tmpLo = x − ((x >> qMSBHf) << qMSBHf)` and `tmpHi = x >> qMSBHf`
(`D:1313-1315`, `:1337-1339`, `:1432-1434`, `:1459-1461`), in that order. -/
def words (qs : List ℕ) (tb : Tab) (x : ℕ) : List (ℕ × ℕ × ℚ) :=
  if pathSplit qs then
    let hi := rshift x (qMSBHf qs)
    let lo := subFast x (lshift hi (qMSBHf qs))
    [(lo, tb.intLo, tb.fracLo), (hi, tb.intHi, tb.fracHi)]
  else [(x, tb.intLo, tb.fracLo)]

/-- All words of a coefficient, limb by limb. -/
def allWords (qs : List ℕ) (tab : List Tab) (xs : List ℕ) : List (ℕ × ℕ × ℚ) :=
  (tab.zip xs).flatMap fun p => words qs p.1 p.2

/-- `intSum` after the loop: `intSum.AddEqFast(tmp)` of `tmp.MulEqFast(table)` (unreduced) or
`tmp.ModMulFastConst(Eq)(table, t, …)` (reduced) for every word. -/
def intSum (t : ℕ) (qs : List ℕ) (ws : List (ℕ × ℕ × ℚ)) : ℕ :=
  ws.foldl (fun s w =>
    addFast s (if pathReduce t qs then modMulConst w.1 w.2.1 t else mulFast w.1 w.2.1)) 0

/-- `floatSum` after the loop, from `start` (`0.5` for power-of-two `t`, `D:1258` etc.; `0.0`
otherwise, `D:1373` etc.): `floatSum += tmp.ConvertToDouble() * frac` for every word
(`ConvertToDouble` is `static_cast<double>`, `U:1431-1433`). -/
def floatSum (A : Arith) (start : ℚ) (ws : List (ℕ × ℕ × ℚ)) : ℚ :=
  ws.foldl (fun s w => A.mulAdd s (A.ofNat w.1) w.2.2) start

/-- Non-power-of-two `t`, after the loop: `floatSum += intSum` (`D:1386`, `:1413`, `:1447`,
`:1473`; a `uint64_t` converted to `double`). -/
def floatSumInt (A : ArithD) (t : ℕ) (qs : List ℕ) (ws : List (ℕ × ℕ × ℚ)) : ℚ :=
  A.base.add (floatSum A.base 0 ws) (A.base.ofNat (intSum t qs ws))

/-- The quotient `static_cast<uint64_t>(floatSum * tInv)` with `td = t.ConvertToInt()` (to
`double`) and `tInv = 1. / td` (`D:1357-1358`, `:1387`). -/
def quot (A : ArithD) (t : ℕ) (f : ℚ) : ℕ :=
  truncU64 (A.base.mul f (A.base.div 1 (A.base.ofNat t)))

/-- `floatSum -= td * static_cast<uint64_t>(floatSum * tInv)` (`D:1387` etc.): the reduced
value. -/
def reduced (A : ArithD) (t : ℕ) (f : ℚ) : ℚ :=
  A.mulSub f (A.base.ofNat t) (A.base.ofNat (quot A t f))

/-- **One coefficient of the decryption**, from the canonical residues `xs` (`xᵢ ∈ [0, qᵢ)`)
with the tables `tab`:

* `t` a power of two: `intSum += static_cast<uint64_t>(floatSum)`, then
  `intSum & (t − 1)` (`D:1269-1271`, `:1295-1297`, `:1326-1328`, `:1349-1351`);
* otherwise: `static_cast<uint64_t>(floatSum + 0.5)` of the reduced value (`D:1389`, `:1416`,
  `:1450`, `:1476`). -/
def decrypt1 (A : ArithD) (t : ℕ) (qs : List ℕ) (tab : List Tab) (xs : List ℕ) : ℕ :=
  let ws := allWords qs tab xs
  if isPow2 t then
    addFast (intSum t qs ws) (truncU64 (floatSum A.base (1 / 2) ws)) &&& (t - 1)
  else
    truncU64 (A.base.add (reduced A t (floatSumInt A t qs ws)) (1 / 2))

/-- The canonical residues of `x` modulo the limbs. -/
def residues (qs : List ℕ) (x : ℕ) : List ℕ := qs.map fun q => x % q

/-- **The library's decryption** of `ct` under the integer secret `s` with plaintext modulus `t`
and limbs `qs` (all of them: `Q = qs.prod`): the native coefficients the overload returns
(`D:1480-1487`: a `NativePoly` modulo `t` whose values are these numbers, unreduced). Starts from
the canonical residues of the exact phase (module docstring: `DecryptCore` and the NTT are not
transcribed). -/
def bfvDecryptLib (A : ArithD) (t : ℕ) (qs : List ℕ) {N : ℕ} (s : IntPoly N)
    (ct : List (Poly qs.prod N)) : NPoly ℕ N :=
  let tab := tables A.base t qs
  ⟨fun i => decrypt1 A t qs tab (residues qs ((phase (ofInt qs.prod s) ct).coeff i).val)⟩

/-! ## Side conditions and the margin -/

/-- **The parameters for which the statements are made**: `2 ≤ t < 2⁵⁰`; between 1 and 128
limbs; every limb odd, at least 3 and below `2⁶⁰` (OpenFHE's `MAX_MODULUS_SIZE64`); pairwise
coprime. (`t < 2⁵⁰` keeps the reduced integer sums, at most `2·128` terms below `t`, far from
`2⁶⁴`; larger `t` is not analysed here.) -/
def decParamsOK? (t : ℕ) (qs : List ℕ) : Bool :=
  decide (2 ≤ t) && decide (t < 2 ^ 50) && decide (1 ≤ qs.length) && decide (qs.length ≤ 128) &&
  qs.all (fun q => decide (3 ≤ q) && decide (q % 2 = 1) && decide (q < 2 ^ 60)) &&
  decide (qs.Pairwise Nat.Coprime)

/-- Strict upper bounds on the words of one limb `q`: `x < q`; on the split paths
`tmpLo < min(2^qMSBHf, q)` and `tmpHi < (q − 1)/2^qMSBHf + 1`. -/
def wordCaps (qs : List ℕ) (q : ℕ) : List ℕ :=
  if pathSplit qs then [min (2 ^ qMSBHf qs) q, (q - 1) / 2 ^ qMSBHf qs + 1] else [q]

/-- The caps of all words, limb by limb. -/
def caps (qs : List ℕ) : List ℕ := qs.flatMap (wordCaps qs)

/-- Error bound of the recursive binary64 sum `floatSum` from `start` over words with caps `cs`:
`Σⱼ (6u·capⱼ + u·(start + cap₁ + … + capⱼ + 1))`, `u = 2⁻⁵³`. -/
def sumErr (start : ℚ) : List ℕ → ℚ
  | [] => 0
  | c :: cs => 6 * u * c + u * (start + c + 1) + sumErr (start + c) cs

/-- A bound on `intSum` (exact, before any wrap): `Σ (t − 1)` (reduced) or
`Σ (cap − 1)(t − 1)` (unreduced). -/
def intMax (t : ℕ) (qs : List ℕ) : ℕ :=
  ((caps qs).map fun c => if pathReduce t qs then t - 1 else (c - 1) * (t - 1)).sum

/-- A bound on the value `floatSum + intSum` of the non-power-of-two paths:
`Σ caps + intMax + 2`. -/
def floatMax (t : ℕ) (qs : List ℕ) : ℕ := (caps qs).sum + intMax t qs + 2

/-- **The proved floating-point error δ of the decision value** for the code path the
parameters select (`Challenge.BFVDecrypt.floatSum_err_pow2`, `reduced_err_odd`,
`decrypt1_correct`): for power-of-two `t` the error of the sum `floatSum` from `0.5`; otherwise that of the sum from `0`, plus
`u·(F + 2t + 8) + 2⁻¹²⁰` for adding `intSum` (`F = floatMax`) and for the floating-point
reduction mod `t` and the final `+ 0.5`. -/
def delta (t : ℕ) (qs : List ℕ) : ℚ :=
  if isPow2 t then sumErr (1 / 2) (caps qs)
  else sumErr 0 (caps qs) + u * ((floatMax t qs : ℚ) + 2 * t + 8) + 1 / 2 ^ 120

/-- Non-power-of-two `t` only: how far below `0`, and above `t`, the reduced value can be when the
floating-point quotient `static_cast<uint64_t>(floatSum * tInv)` is one too large or too small
(`Challenge.BFVDecrypt.reduced_err_odd`): `sumErr + 4u·F`. -/
def overshoot (t : ℕ) (qs : List ℕ) : ℚ := sumErr 0 (caps qs) + 4 * u * floatMax t qs

/-- **The margin condition**: with `Q = qs.prod`, `r = Q mod t` and noise bound `B`,
`2·(t·B + r·(t − 1)) + 2·Q·(δ + 2⁻⁶⁴) < Q`, exactly, in the rationals; and for
non-power-of-two `t` also `floatMax ≤ 2⁵²` (the integers the reduction multiplies are exact in
`double`) and `2·(t·B + r·(t − 1)) + 2·Q·overshoot < 2·Q` (a quotient one too large cannot push
the value below `−1/2`, where truncation toward zero would return `0` instead of `t − 1`). The
textbook condition (`Challenge.BFV.decOK`) is the first without the `δ` term; `2⁻⁶⁴` keeps the
decision value a fixed distance away from the rounding boundary. -/
def decLibOK? (t : ℕ) (qs : List ℕ) (B : ℕ) : Bool :=
  let Q := qs.prod
  let η2 : ℚ := ((2 * (t * B + Q % t * (t - 1)) : ℕ) : ℚ)
  decide (η2 + 2 * Q * (delta t qs + 1 / 2 ^ 64) < Q) &&
    (isPow2 t || (decide (floatMax t qs ≤ 2 ^ 52) && decide (η2 + 2 * Q * overshoot t qs < 2 * Q)))

end Spec.DecryptBFV
