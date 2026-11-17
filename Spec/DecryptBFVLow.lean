import Spec.DecryptBFV
import Spec.Decrypt

/-!
# Spec.DecryptBFVLow — OpenFHE's BFV decryption of a ciphertext with fewer limbs, transcribed   (TRUSTED)

OpenFHE v1.6.1 decrypts a BFV ciphertext that has FEWER limbs than the context's `Q` (after
`Compress`, or any other limb drop) on a separate path (`PKEBFVRNS::Decrypt`,
`src/pke/lib/scheme/bfvrns/bfvrns-pke.cpp:254-275`), whatever the multiplication technique:

1. drop the last limb, one at a time, until one is left: `DCRTPolyImpl::DropLastElementAndScale(
   GetqlInvModq(diffQl + l))` for `l = 0 … sizeQl − 2`, `diffQl = sizeQ − sizeQl` (`:256-260`);
   each drop computes `(x − [x]_{q_l})·q_l⁻¹` limb by limb, with the centred `[x]_{q_l}` produced by
   the modulus switch of the vector constructor (`D:737-755`, `V:190-215`);
2. on the remaining limb `q₀`: `NativePoly::MultiplyAndRound(t, q₀)` (`:265-266`), a centred
   binary64 rounding of `t·x/q₀` (`V:539-553`, `U:657-661`);
3. `SwitchModulus(t, 1, 0, 0)` (`:271`): the centred value reduced modulo `t` (`V:218-237`,
   `V:90-127`).

This file transcribes that path for one coefficient (`decLow1`) and for a ciphertext
(`bfvDecryptLow`), and defines the side condition `decLowParamsOK?`, the proved error `lowErr`,
the noise after the drops `lowNoise` and the margin `decLowOK?` of the locked statements in
`Challenge/BFVDecryptLow.lean`.

Source: upstream OpenFHE v1.6.1, tag `v1.6.1`, commit `b59e1f291965f14fbee5172cd83a20f5b856204f`.
`NATIVEINT == 64`, `HAVE_INT128`, `NATIVEINT_DO_CHECKS == false` (as `Spec.DecryptBFV`).
`P` = `src/pke/lib/scheme/bfvrns/bfvrns-pke.cpp`,
`C` = `src/pke/lib/scheme/bfvrns/bfvrns-cryptoparameters.cpp`,
`D` = `src/core/include/lattice/hal/default/dcrtpoly-impl.h`,
`V` = `src/core/lib/math/hal/intnat/mubintvecnat.cpp`,
`U` = `src/core/include/math/hal/intnat/ubintnat.h`,
`I` = `src/core/include/math/hal/integer.h`.

## What is transcribed and what is not

* *Transcribed*: the loop and the table index of `P:254-275`; the table `m_qlInvModq`
  (`C:643-654`); the modulus switch of a vector (`V:190-237`, its three branches) with
  `GeneralShrinkLoop` (`V:90-127`, the Barrett branch with `mu = DivD(1 << e, 0, nv)`,
  `MultDHi`) and the lanes `topBitMask`, `modSubLane`, `centeredCorrectionLane` (`V:54-89`);
  `NativeVectorT::MultiplyAndRound` (`V:539-553`) with `NativeIntegerT::MultiplyAndRound`
  (`U:657-661`), `Mod` (`U:720-722`), `operator-` (`I:117-119` → `Sub` → `SubFast`,
  `U:461-462`, `:482-484`, a wrapping subtraction).
* *Compiler-dependent lanes*: `V:50-52` defines `OPENFHE_COMPARE_SELECT_LANES` for GCC < 12;
  `modAddLane` also has a clang branch (not used here). Transcribed are the `topBitMask` variants
  (`V:65-66`, `:76-77`, `:87-88`) that GCC ≥ 12 (the build the recorded runs come from: GCC 13.3) and clang compile;
  `Challenge.BFVDecryptLow.switchModulus_spec` proves that their results equal the centred
  reduction, which is also what the compare-select variants compute on the same ranges.
* *Modelled as exact, NOT verified*: the two vector operations of a drop
  (`m_vectors[i] -= tmp; m_vectors[i] *= qlInvModq[i]`, `D:750-751`). They run on the
  EVALUATION (NTT) form of the limbs; the transcription applies them to the coefficients as exact
  modular subtraction and multiplication (`(x − y) mod qᵢ`, `x·c mod qᵢ`), which is what they
  compute if the NTT is linear and the word-level modular arithmetic is exact (the same
  assumption as `DecryptCore` and the NTT in `Spec.DecryptBFV`). `ModInverse` (`C:651`) is exact
  (`Spec.DecryptBFV.invMod`).
* *Not transcribed*: `DecryptCore` and the NTTs; `bfvDecryptLow` starts from the canonical
  residues `x mod qᵢ` (`i < ℓ`) of the exact phase modulo `Q_ℓ = q₀⋯q_{ℓ-1}`. The table
  `m_qlInvModq` is read from the context only when the multiplication technique is not `BEHZ`
  (`C:128-655`); under `BEHZ` this transcription is meant for ciphertexts of one limb only (the
  loop over drops does not run). The dispatch is `Spec.DecryptBFVLib`.

## The binary64 step

`p.ConvertToDouble() * (x.ConvertToDouble() / q.ConvertToDouble()) + 0.5` (`U:660`) is written
`A.mulAdd (1/2) (A.ofNat p) (A.div (A.ofNat x) (A.ofNat q))`: the expression `a * b + 0.5` may be
contracted into one fused multiply-add like `s += a * b` (`Spec.Float` item 5), and `mulAdd` is
either form at each evaluation. The conversion of `t` is `A.ofNat t`, correctly rounded but NOT
assumed exact (it is not exact for `t > 2⁵³`; the error bound `lowErr` accounts for this). The cast
`static_cast<NativeInt>` is `truncU64` (defined behaviour only on `(−1, 2⁶⁴)`; the statements
prove the range).
-/

namespace Spec.DecryptBFVLow
open Spec.Float Spec.DecryptBFV Spec.Scheme NPoly

/-! ## Lanes (`V:54-89`) -/

/-- `topBitMask(x) = 0 − (x >> 63)` (`V:54-57`): all ones if bit 63 of `x` is set, else `0`. -/
def topBitMask (x : ℕ) : ℕ := subFast 0 (rshift x 63)

/-- `modSubLane(a, b, m)` (`V:70-79`, the variant without `OPENFHE_COMPARE_SELECT_LANES`):
`t = a − b; t + (m & topBitMask(t))`, wrapping. -/
def modSubLane (a b m : ℕ) : ℕ :=
  let d := subFast a b
  addFast d (m &&& topBitMask d)

/-- `centeredCorrectionLane(v, halfQ, diff)` (`V:81-89`, the variant without
`OPENFHE_COMPARE_SELECT_LANES`): `diff & topBitMask(halfQ − v)`, i.e. `diff` if `v > halfQ`. -/
def centeredCorrectionLane (v halfQ diff : ℕ) : ℕ := diff &&& topBitMask (subFast halfQ v)

/-! ## Double-word helpers (`U:1678-1681`, `U:1741-1752`, `U:1779-1783`; `HAVE_INT128`) -/

/-- `MultDHi(a, b)`: the high word of the 128-bit product. -/
def multDHi (a b : ℕ) : ℕ := a * b / 2 ^ 64

/-- `DivD(hi, lo, divisor)`: `static_cast<NativeInt>((hi·2⁶⁴ + lo) / divisor)` (the caller
guarantees `hi < divisor`, so nothing is truncated). -/
def divD (hi lo d : ℕ) : ℕ := (hi * 2 ^ 64 + lo) / d % 2 ^ 64

/-! ## The modulus switch of a vector (`V:90-127`, `V:190-237`) -/

/-- `GeneralShrinkLoop(dst, src, size, ov, nv)` for one value `v` (`V:90-127`, with
`sizeof(DInt) > sizeof(BasicInt)`): `diffR = (ov − nv) % nv`; for `e = GetMSB(nv) − 2 ≥ 1` the
Barrett reduction with `mu = DivD(1 << e, 0, nv)`: if `av ≥ nv`,
`av −= (MultDHi(v, mu) >> e)·nv`, then once more `av −= nv` if `av ≥ nv`; otherwise
`av %= nv` if `av ≥ nv`; finally `modSubLane(av, centeredCorrectionLane(v, halfQ, diffR), nv)`. -/
def generalShrink (ov nv v : ℕ) : ℕ :=
  let halfQ := rshift ov 1
  let diffR := subFast ov nv % nv
  if 3 ≤ msb nv then
    let e := msb nv - 2
    let mu := divD (lshift 1 e) 0 nv
    let av :=
      if v ≥ nv then
        let a1 := subFast v (mulFast (rshift (multDHi v mu) e) nv)
        if a1 ≥ nv then subFast a1 nv else a1
      else v
    modSubLane av (centeredCorrectionLane v halfQ diffR) nv
  else
    let av := if v ≥ nv then v % nv else v
    modSubLane av (centeredCorrectionLane v halfQ diffR) nv

/-- The modulus switch of one value `v` from `ov` to `nv`: the vector constructor
`NativeVectorT(v, modulus)` (`V:190-215`) and `NativeVectorT::SwitchModulus` (`V:218-237`) run the
same three branches: `nv > ov`: `x + centeredCorrectionLane(x, halfQ, nv − ov)`;
`nv > halfQ`: `x − centeredCorrectionLane(x, halfQ, ov − nv)`; otherwise `GeneralShrinkLoop`. -/
def switchModulus (ov nv v : ℕ) : ℕ :=
  let halfQ := rshift ov 1
  if nv > ov then addFast v (centeredCorrectionLane v halfQ (subFast nv ov))
  else if nv > halfQ then subFast v (centeredCorrectionLane v halfQ (subFast ov nv))
  else generalShrink ov nv v

/-! ## The drops (`P:254-260`, `D:737-755`, `C:643-654`) -/

/-- `m_qlInvModq[k][i] = moduliQ[sizeQ − (k + 1)].ModInverse(moduliQ[i])` (`C:646-651`). -/
def qlInvModq (qs : List ℕ) (k i : ℕ) : ℕ := invMod (qs.getD (qs.length - (k + 1)) 0) (qs.getD i 0)

/-- `DropLastElementAndScale(qlInvModq)` on one coefficient (`D:737-755`) with residues `xs`
(limb `i` modulo `qs[i]`; the limbs in use are the first `xs.length`), the table row `k`:
the last residue is switched to each remaining modulus (`D:746`, the vector constructor), then
`m_vectors[i] -= tmp` and `m_vectors[i] *= qlInvModq[i]` (`D:749-751`; exact modular operations,
module docstring). -/
def dropLastElementAndScale (qs : List ℕ) (k : ℕ) (xs : List ℕ) : List ℕ :=
  let ql := qs.getD (xs.length - 1) 0
  let last := xs.getLastD 0
  xs.dropLast.mapIdx fun i x =>
    let qi := qs.getD i 0
    (x + (qi - switchModulus ql qi last)) % qi * qlInvModq qs k i % qi

/-- The loop `for (l = 0; l < levels; ++l) b.DropLastElementAndScale(GetqlInvModq(diffQl + l))`
(`P:256-260`): `sizeQl = xs.length`, `diffQl = sizeQ − sizeQl`, `levels = sizeQl − 1`. -/
def dropAll (qs xs : List ℕ) : List ℕ :=
  (List.range (xs.length - 1)).foldl
    (fun ys l => dropLastElementAndScale qs (qs.length - xs.length + l) ys) xs

/-! ## The rounding (`P:262-271`, `V:539-553`, `U:657-661`) -/

/-- `NativeIntegerT::MultiplyAndRound(p, q)` of `x` (`U:657-661`):
`static_cast<NativeInt>(p.ConvertToDouble() * (x.ConvertToDouble() / q.ConvertToDouble()) + 0.5)`
(module docstring: the `+ 0.5` may be contracted). -/
def multiplyAndRound (A : Arith) (x p q : ℕ) : ℕ :=
  truncU64 (A.mulAdd (1 / 2) (A.ofNat p) (A.div (A.ofNat x) (A.ofNat q)))

/-- `NativeVectorT::MultiplyAndRound(p, q)` on one value `x` of a vector modulo `q`
(`V:539-553`, with `mv = m_modulus = q`, `halfQ = q >> 1`): if `x > halfQ`,
`mv − (mv − x).MultiplyAndRound(p, q)` (wrapping `operator-`; NOT reduced: it is `q` when the
rounding is `0`), else `x.MultiplyAndRound(p, q).Mod(mv)`. -/
def multiplyAndRoundVec (A : Arith) (p q x : ℕ) : ℕ :=
  if x > rshift q 1 then subFast q (multiplyAndRound A (subFast q x) p q)
  else multiplyAndRound A x p q % q

/-- **One coefficient of the low-limb decryption** from the residues `xs` (limb `i` modulo
`qs[i]`, `xs.length < qs.length` limbs in use): the drops, then on limb `q₀ = qs[0]`
`MultiplyAndRound(t, q₀)` and `SwitchModulus(t)` (`P:256-271`). -/
def decLow1 (A : Arith) (t : ℕ) (qs xs : List ℕ) : ℕ :=
  let q0 := qs.getD 0 0
  switchModulus q0 t (multiplyAndRoundVec A t q0 ((dropAll qs xs).headD 0))

/-- **The library's decryption of a ciphertext at level `ℓ`** (limbs `qs.take ℓ`, `Q_ℓ` their
product) under the integer secret `s`: the native coefficients of the returned `NativePoly`
(`P:273`). Starts from the canonical residues of the exact phase modulo `Q_ℓ` (module
docstring). -/
def bfvDecryptLow (A : ArithD) (t : ℕ) (qs : List ℕ) (ℓ : ℕ) {N : ℕ} (s : IntPoly N)
    (ct : List (Poly (qs.take ℓ).prod N)) : NPoly ℕ N :=
  ⟨fun i => decLow1 A.base t qs
    (residues (qs.take ℓ) ((phase (ofInt (qs.take ℓ).prod s) ct).coeff i).val)⟩

/-! ## Side conditions and the margin -/

/-- **The parameters for which the statements are made**, at level `ℓ`: `2 ≤ t`;
`1 ≤ ℓ ≤ qs.length`; every limb odd, at least `3` and below `2⁶⁰`; the limbs pairwise coprime;
`2t < q₀` (the rounded value, at most about `t/2`, stays in the lower half of `q₀`, and the final
`SwitchModulus(t)` takes the `GeneralShrinkLoop` branch). -/
def decLowParamsOK? (t : ℕ) (qs : List ℕ) (ℓ : ℕ) : Bool :=
  decide (2 ≤ t) && decide (1 ≤ ℓ) && decide (ℓ ≤ qs.length) &&
  qs.all (fun q => decide (3 ≤ q) && decide (q % 2 = 1) && decide (q < 2 ^ 60)) &&
  decide (qs.Pairwise Nat.Coprime) && decide (2 * t < qs.headD 0)

/-- **The proved error of the binary64 rounding step** (`Challenge.BFVDecryptLow.multiplyAndRound_err`):
for `x ≤ q/2`, the double `t·(x/q) + 0.5` is within `u·(7t/2 + 1)` of `t·x/q + 1/2`
(four roundings of the product chain, up to `5u` relative on a value at most `t/2`, one of the
final addition; `t` is NOT assumed exact in `double`). -/
def lowErr (t : ℕ) : ℚ := u * (7 * t / 2 + 1)

/-- **The noise after the drops**: with `V = t·B + (Q_ℓ mod t)·(t − 1)` the bound on the invariant
noise `t·x − Q_ℓ·m` at level `ℓ`, each drop of a limb `q` maps `V` to `⌊(V + t·⌊q/2⌋)/q⌋`
(`Spec.Decrypt.decBoundRev`, limbs last first, stopping at `q₀`). -/
def lowNoise (t : ℕ) (qs : List ℕ) (ℓ B : ℕ) : ℕ :=
  Spec.Decrypt.decBoundRev t (qs.take ℓ).reverse (t * B + (qs.take ℓ).prod % t * (t - 1))

/-- **The margin condition** at level `ℓ` for noise bound `B` (the noise of `BFVEncrypts` at
modulus `Q_ℓ`): with `V₀ = lowNoise t qs ℓ B`, `2·V₀ + 2·q₀·lowErr t < q₀`, exactly, in the
rationals. It implies `t < 2⁵¹` (`Challenge.BFVDecryptLow.decLowOK?_t_lt`). -/
def decLowOK? (t : ℕ) (qs : List ℕ) (ℓ B : ℕ) : Bool :=
  decide ((2 * lowNoise t qs ℓ B : ℚ) + 2 * (qs.headD 0 : ℚ) * lowErr t < qs.headD 0)

end Spec.DecryptBFVLow
