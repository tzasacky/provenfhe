import Spec.DecryptBFVLow
import Challenge.BFVDecrypt

/-!
# Challenge.BFVDecryptLow — OpenFHE's low-limb BFV decryption is textbook decryption under a computed margin   (LOCKED definitions and statements; proofs in `Validation/BFVDecryptLow*.lean`)

`Spec.DecryptBFVLow` transcribes OpenFHE v1.6.1's decryption of a BFV ciphertext with fewer limbs
than `Q` (`bfvrns-pke.cpp:254-275`): limb drops with the centred modulus switch, then one binary64
rounding `t·x/q₀` on the last limb, then a centred reduction mod `t`. The statements:

* **The integer part is exact** (`switchModulus_spec`, `dropAll_spec`, `roundStep_exact`): the
  modulus switch (all three branches, the Barrett loop and the bit-mask lanes) returns the centred
  value reduced modulo the new modulus; the drops return the residue mod `q₀` of the exact
  iterated centred rounding `scaleDown`; with exact arithmetic the rounding step returns `k mod t`
  for every integer `k` with `2·|t·x − q₀·k| < q₀` (`x` centred), and a value below `t`.
* **The binary64 step** (`multiplyAndRound_err`): for every conforming arithmetic and
  `x ≤ q/2`, the double `t·(x/q) + 0.5` is within `lowErr t` of `t·x/q + 1/2`, and the argument
  of the cast `static_cast<NativeInt>` is in `[0, 2⁶⁴)` (no undefined behaviour).
* **The noise of the drops** (`dropAll_noise`): each drop maps a bound `V` on `t·X − Q·k` to
  `⌊(V + t·⌊q/2⌋)/q⌋` (`Spec.Decrypt.decBoundRev`), with the same `k`.
* **The main theorem** (`decLow1_correct`, `bfvDecryptLow_correct`): for every conforming
  arithmetic, if the noise of `BFVEncrypts` at the level's modulus `Q_ℓ` is at most `B` and
  `decLowOK? t qs ℓ B`, every native coefficient `c` the library returns satisfies
  `c ≡ mᵢ (mod t)` and `c < t`.
* **Pins**: `decLowOK?_t_lt` (the margin refuses every `t ≥ 2⁵¹`, in particular every `t` with
  `double(t) ≠ t`); `lowMargin_needed` (a conforming
  arithmetic, a level-1 ciphertext whose noise the textbook condition accepts, on which the
  transcription returns a wrong value; the margin refuses it); `#guard`s at OpenFHE parameters.

**What is NOT shown.** The drops' vector operations in NTT form, `DecryptCore`, the NTTs and
`ModInverse` are modelled, not verified (`Spec.DecryptBFVLow` docstring). Nothing is said between
`decLowOK?` and the textbook threshold. The decoding of the returned `NativePoly` is not covered.
-/

namespace Challenge.BFVDecryptLow
open Spec Spec.Float Spec.DecryptBFV Spec.DecryptBFVLow Spec.Scheme NPoly

/-! ## Exact quantities -/

/-- The centred representative the library takes of `v` modulo `ov`: `v − ov` if
`v > ov >> 1`, else `v`. -/
def centredOf (ov v : ℕ) : ℤ := if v > ov / 2 then (v : ℤ) - ov else v

/-- The exact integer the drops compute: `X` divided by each limb of the list in turn (the dropped
limbs, last first), each time as `(X − [X]_q)/q` with `[X]_q = centredOf q (X mod q)`. -/
def scaleDown : List ℕ → ℤ → ℤ
  | [], X => X
  | q :: rest, X => scaleDown rest ((X - centredOf q (X % (q : ℤ)).toNat) / q)

/-- The canonical residues of an integer on the limbs `qs`. -/
def residuesZ (qs : List ℕ) (X : ℤ) : List ℕ := qs.map fun q : ℕ => (X % (q : ℤ)).toNat

/-! ## The integer part -/

/-- **The modulus switch is the centred reduction**, in all three branches (and with the
bit-mask lanes), for `v < ov`, and for `v = ov` when `2·nv < ov` (the `GeneralShrinkLoop`
branch; the rounding step can hand it `q₀` itself). -/
theorem switchModulus_spec (ov nv v : ℕ) (hov : 3 ≤ ov) (hov' : ov < 2 ^ 63) (hnv : 2 ≤ nv)
    (hnv' : nv < 2 ^ 63) (hv : v < ov ∨ (v = ov ∧ 2 * nv < ov)) :
    (switchModulus ov nv v : ℤ) = centredOf ov v % nv ∧ switchModulus ov nv v < nv := sorry

/-- **The drops are exact**: from the residues of any integer `X` at level `ℓ`, the loop of
`DropLastElementAndScale` leaves the single residue mod `q₀` of `scaleDown` of `X` by
`q_{ℓ-1}, …, q₁` (with the table row `diffQl + l` the code reads). -/
theorem dropAll_spec (t : ℕ) (qs : List ℕ) (ℓ : ℕ) (hp : decLowParamsOK? t qs ℓ = true) (X : ℤ) :
    dropAll qs (residuesZ (qs.take ℓ) X) =
      [(scaleDown ((qs.take ℓ).drop 1).reverse X % (qs.headD 0 : ℤ)).toNat] := sorry

/-- **The rounding step is exact with exact arithmetic**: on a residue `x < q₀`, for every
integer `k` with `2·|t·[x]_{q₀} − q₀·k| < q₀`, `MultiplyAndRound(t, q₀)` then `SwitchModulus(t)`
return a value `c < t` with `c ≡ k (mod t)`. -/
theorem roundStep_exact (t : ℕ) (qs : List ℕ) (ℓ : ℕ) (hp : decLowParamsOK? t qs ℓ = true) (x : ℕ)
    (hx : x < qs.headD 0) (k : ℤ)
    (hk : 2 * |(t : ℤ) * centredOf (qs.headD 0) x - (qs.headD 0 : ℤ) * k| < qs.headD 0) :
    let c := switchModulus (qs.headD 0) t (multiplyAndRoundVec Spec.Float.exact t (qs.headD 0) x)
    (c : ZMod t) = (k : ZMod t) ∧ c < t := sorry

/-! ## The binary64 step -/

/-- **The rounding step's error** for every conforming arithmetic: for `x ≤ q/2`, the double
`t·(x/q) + 0.5` (contracted or not) is within `lowErr t` of `t·x/q + 1/2`, and lies in
`[0, 2⁶⁴)`, where the cast is defined. -/
theorem multiplyAndRound_err (A : ArithD) (hA : ConformsD A) (t q x : ℕ) (ht : 2 ≤ t)
    (ht' : t < 2 ^ 60) (hq : 3 ≤ q) (hq' : q < 2 ^ 60) (hx : x ≤ q / 2) :
    let z := A.base.mulAdd (1 / 2) (A.base.ofNat t) (A.base.div (A.base.ofNat x) (A.base.ofNat q))
    |z - ((t : ℚ) * x / q + 1 / 2)| ≤ lowErr t ∧ 0 ≤ z ∧ z < 2 ^ 64 := sorry

/-! ## The noise of the drops -/

/-- **Each drop adds at most `t/2` to the invariant noise, then divides by the limb**: if
`t·X = Q_ℓ·k + v` with `|v| ≤ V`, then `t·scaleDown X = q₀·k + v'` with
`|v'| ≤ decBoundRev t (qs.take ℓ).reverse V`, with the same `k`. -/
theorem dropAll_noise (t : ℕ) (qs : List ℕ) (ℓ : ℕ) (hp : decLowParamsOK? t qs ℓ = true)
    (X k v : ℤ) (V : ℕ) (h : (t : ℤ) * X = ((qs.take ℓ).prod : ℤ) * k + v) (hv : |v| ≤ V) :
    ∃ v' : ℤ, (t : ℤ) * scaleDown ((qs.take ℓ).drop 1).reverse X = (qs.headD 0 : ℤ) * k + v' ∧
      |v'| ≤ Spec.Decrypt.decBoundRev t (qs.take ℓ).reverse V := sorry

/-! ## The main theorem -/

/-- **One coefficient.** For every conforming arithmetic: if the phase `x ∈ [0, Q_ℓ)` is within
`B` (centred) of `⌊Q_ℓ/t⌋·m` modulo `Q_ℓ`, and `decLowOK? t qs ℓ B`, the library returns `c < t`
with `c ≡ m (mod t)`; the residue the drops leave is below `q₀` (so `MultiplyAndRound` is applied
to a value at most `q₀/2`, where `multiplyAndRound_err` shows the cast is defined). -/
theorem decLow1_correct (A : ArithD) (hA : ConformsD A) (t : ℕ) (qs : List ℕ) (ℓ : ℕ)
    (hp : decLowParamsOK? t qs ℓ = true) (B : ℕ) (hB : decLowOK? t qs ℓ B = true) (x m : ℕ)
    (hm : m < t) (hx : x < (qs.take ℓ).prod)
    (hnoise : (((x : ℤ) - ((qs.take ℓ).prod / t * m : ℕ) : ℤ) :
      ZMod (qs.take ℓ).prod).valMinAbs.natAbs ≤ B) :
    let c := decLow1 A.base t qs (residues (qs.take ℓ) x)
    (c : ZMod t) = (m : ZMod t) ∧ c < t ∧
      (dropAll qs (residues (qs.take ℓ) x)).headD 0 < qs.headD 0 := sorry

/-- **OpenFHE's BFV decryption of a ciphertext at level `ℓ` (fewer limbs) returns the encrypted
message**, for every conforming arithmetic, when the noise clause of `BFVEncrypts` at modulus
`Q_ℓ = (qs.take ℓ).prod` holds at `B` and `decLowOK? t qs ℓ B`: every native coefficient `c`
satisfies `c ≡ mᵢ (mod t)` and `c < t`. -/
theorem bfvDecryptLow_correct (A : ArithD) (hA : ConformsD A) (t : ℕ) (qs : List ℕ) (ℓ : ℕ)
    (hp : decLowParamsOK? t qs ℓ = true) {N : ℕ} (s : IntPoly N)
    (ct : List (Poly (qs.take ℓ).prod N)) (m : Poly t N) (B : ℕ)
    (hnoise : normInf (centered (phase (ofInt (qs.take ℓ).prod s) ct -
      ofInt (qs.take ℓ).prod ⟨fun i => (((qs.take ℓ).prod / t * (m.coeff i).val : ℕ) : ℤ)⟩)) ≤ B)
    (hB : decLowOK? t qs ℓ B = true) (i : Fin N) :
    (((bfvDecryptLow A t qs ℓ s ct).coeff i : ℕ) : ZMod t) = m.coeff i ∧
      (bfvDecryptLow A t qs ℓ s ct).coeff i < t := sorry

/-! ## Pins -/

/-- **The margin refuses every large `t`**: `decLowOK?` implies `t < 2⁵¹`. In particular every
`t ≥ 2⁵³` (where `double(t)` need not be `t`) is refused, at every noise bound. -/
theorem decLowOK?_t_lt (t : ℕ) (qs : List ℕ) (ℓ B : ℕ) (hq : 1 ≤ qs.headD 0)
    (h : decLowOK? t qs ℓ B = true) : t < 2 ^ 51 := sorry

/-- The limbs of `lowMargin_needed`: `2⁵⁹ − 55` and `2⁵⁹ − 99`. -/
def qsPin : List ℕ := [2 ^ 59 - 55, 2 ^ 59 - 99]

/-- **The margin cannot be dropped.** `t = 2`, level 1 of the two limbs `qsPin`, message `0`,
phase `x = (q₀ − 5)/4` (its noise is `x` itself): the textbook condition `decOK` accepts the
noise, textbook rounding gives `0`, the transcription with exact arithmetic gives `0`, and with
the conforming arithmetic `Challenge.BFVDecrypt.advD` (which rounds every contracted `a·b + c`
up by `1 + u`) it gives `1`. `decLowOK?` refuses this noise bound. -/
theorem lowMargin_needed :
    decLowParamsOK? 2 qsPin 1 = true ∧
      Challenge.BFV.decOK 2 (2 ^ 59 - 55) ((2 ^ 59 - 55 - 5) / 4) = true ∧
      roundDiv (2 * ((2 ^ 59 - 55 - 5) / 4 : ℕ)) (2 ^ 59 - 55) = 0 ∧
      decLow1 Spec.Float.exact 2 qsPin [(2 ^ 59 - 55 - 5) / 4] = 0 ∧
      decLow1 Challenge.BFVDecrypt.advD.base 2 qsPin [(2 ^ 59 - 55 - 5) / 4] = 1 ∧
      decLowOK? 2 qsPin 1 ((2 ^ 59 - 55 - 5) / 4) = false := sorry

-- Parameters with `t = 18014398510661633 ≈ 2⁵⁴` and four 60-bit limbs. The parameters themselves
-- pass `decLowParamsOK?`; the margin refuses every level even at noise 0 (the transcription
-- reproduces recorded outputs of the library's routine bit for bit: `FHE/Float/RNELow.lean`).
#guard decLowParamsOK? 18014398510661633
  [1152921504606748673, 1152921504606683137, 1152921504606584833, 1152921504605962241] 3
#guard [1, 2, 3].all fun ℓ => !decLowOK? 18014398510661633
  [1152921504606748673, 1152921504606683137, 1152921504606584833, 1152921504605962241] ℓ 0
-- OpenFHE's default-like parameters (three 60-bit limbs, `t = 65537`): after `Compress` to one
-- or two limbs, a noise bound of 99% of the textbook threshold
-- `E = (Q_ℓ/2 − (Q_ℓ mod t)(t − 1))/t` at that level is accepted.
#guard decLowOK? 65537 [1152921504606830593, 1152921504606791681, 1152921504606748673] 1
  ((1152921504606830593 / 2 - 1152921504606830593 % 65537 * 65536) / 65537 * 99 / 100)
#guard decLowOK? 65537 [1152921504606830593, 1152921504606791681, 1152921504606748673] 2
  ((1152921504606830593 * 1152921504606791681 / 2 -
    1152921504606830593 * 1152921504606791681 % 65537 * 65536) / 65537 * 99 / 100)
-- At `t ≈ 2⁵⁰` (two limbs left) the binary64 step costs most of the threshold: 12% of it is
-- accepted, 13% is refused.
#guard decLowOK? 1125899906826241 [1152921504606830593, 1152921504606791681, 1152921504606748673] 2
  ((1152921504606830593 * 1152921504606791681 / 2 - 1152921504606830593 * 1152921504606791681 %
    1125899906826241 * 1125899906826240) / 1125899906826241 * 12 / 100)
#guard !decLowOK? 1125899906826241 [1152921504606830593, 1152921504606791681, 1152921504606748673] 2
  ((1152921504606830593 * 1152921504606791681 / 2 - 1152921504606830593 * 1152921504606791681 %
    1125899906826241 * 1125899906826240) / 1125899906826241 * 13 / 100)

end Challenge.BFVDecryptLow
