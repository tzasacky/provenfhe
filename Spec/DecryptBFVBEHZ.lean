import Spec.DecryptBFVLow

/-!
# Spec.DecryptBFVBEHZ — OpenFHE's integer BFV decryption under BEHZ, transcribed   (TRUSTED)

OpenFHE v1.6.1 decrypts a BFV ciphertext that has all its limbs, under the multiplication
technique `BEHZ`, with the integer overload
`DCRTPolyImpl::ScaleAndRound(moduliQ, t, tgamma, tgammaQHatModq, tgammaQHatModqPrecon,
negInvqModtgamma, negInvqModtgammaPrecon)` (`P:249-252`, `D:1651-1696`): with `γ = 2²⁶` it
accumulates, modulo `t·γ`, the words `[[xᵢ·tγ·(Q/qᵢ)⁻¹]_{qᵢ}·(−qᵢ⁻¹)]_{tγ}`, then rounds by `γ`
(`s + (s & (γ − 1))`, `>> 26`). This file transcribes that computation for one coefficient
(`behz1`) with its tables (`C:844-873`), for a ciphertext (`bfvDecryptBEHZ`), and the side
condition and margin (`behzParamsOK?`, `decBEHZOK?`) of `Challenge/BFVDecryptBEHZ.lean`.

Source: upstream OpenFHE v1.6.1, commit `b59e1f291965f14fbee5172cd83a20f5b856204f`.
`NATIVEINT == 64`, `HAVE_INT128`, `NATIVEINT_DO_CHECKS == false`.
`P` = `src/pke/lib/scheme/bfvrns/bfvrns-pke.cpp`,
`C` = `src/pke/lib/scheme/bfvrns/bfvrns-cryptoparameters.cpp`,
`D` = `src/core/include/lattice/hal/default/dcrtpoly-impl.h`,
`U` = `src/core/include/math/hal/intnat/ubintnat.h`,
`R` = `src/pke/include/schemerns/rns-cryptoparameters.h`.

## What is transcribed and what is not

* *Transcribed*, with every machine-word operation wrapping modulo `2⁶⁴`: `tgamma =
  NativeInteger(t.ConvertToInt() * m_gamma)` (`C:844`, a `uint64_t` product), `m_gamma = 1 << 26`
  (`R:2014`); `PrepModMulConst` (`U:1234-1238`, `DivD(b, 0, m)`); `ModMulFastConst`
  (`U:1248-1253`, Shoup's multiplication with the signed 64-bit fix-up
  `yprime = (int64)(a·b − q·m)`, `yprime ≥ 0 ? yprime : yprime + m`, transcribed as written, not
  modelled as `a·b mod m`: `Challenge.BFVDecryptBEHZ.modMulFastConst_spec` proves that equality
  under its conditions, which `behzParamsOK?` guarantees); `ModAddFastEq` (`U:842-848`); `operator+=`
  (`AddEqFast`, wrapping); `>> 26` (`RShift`, `U:1389-1391`); the loop `D:1666-1680` and
  `D:1682-1685`; the returned values are not reduced (they can equal `t`).
* *Tables* (`C:849-873`): `negInvqModtgamma[i] = ((tgamma − 1)·qᵢ⁻¹ mod tgamma) mod tgamma` and
  `tgammaQHatInvModq[i] = ((((Q/qᵢ)⁻¹ mod qᵢ)·γ mod qᵢ)·t) mod qᵢ`, with the big-integer
  `ModInverse` exact (`Spec.DecryptBFV.invMod`; the library throws if the inverse does not
  exist, the side condition excludes that).
* *Not transcribed*: `DecryptCore`, the NTT (`bfvDecryptBEHZ` starts from the canonical residues
  of the exact phase, as `Spec.DecryptBFV.bfvDecryptLib`).
-/

namespace Spec.DecryptBFVBEHZ
open Spec.Float Spec.DecryptBFV Spec.DecryptBFVLow Spec.Scheme NPoly

/-- `m_gamma = 1 << 26` (`R:2014`). -/
def gamma : ℕ := 2 ^ 26

/-- `tgamma = NativeInteger(t.ConvertToInt() * m_gamma)` (`C:844`): the 64-bit product, wrapping. -/
def tgamma (t : ℕ) : ℕ := mulFast t gamma

/-- `PrepModMulConst(b, m)` (`U:1234-1238`): `DivD(b, 0, m)`, i.e. `⌊b·2⁶⁴/m⌋` (for `b < m`). -/
def prepModMulConst (b m : ℕ) : ℕ := divD b 0 m

/-- `a.ModMulFastConst(b, m, bInv)` (`U:1248-1253`): `q = MultDHi(a, bInv) + 1`;
`yprime = static_cast<int64_t>(a·b − q·m)` (64-bit wrapping products and difference); the result
is `yprime` if `yprime ≥ 0` (bit 63 clear), else `yprime + m` (as `uint64_t`, wrapping). -/
def modMulFastConst (a b m bInv : ℕ) : ℕ :=
  let q := addFast (multDHi a bInv) 1
  let y := subFast (mulFast a b) (mulFast q m)
  if y < 2 ^ 63 then y else addFast y m

/-- `s.ModAddFastEq(b, m)` (`U:842-848`): `s += b` (wrapping), then `s −= m` if `s ≥ m`. -/
def modAddFastEq (s b m : ℕ) : ℕ :=
  let r := addFast s b
  if r ≥ m then subFast r m else r

/-- `m_negInvqModtgamma[i]` (`C:851-857`): `((tgamma − 1)·ModInverse(qᵢ, tgamma)) mod tgamma`. -/
def negInvqModtgamma (t q : ℕ) : ℕ :=
  (subFast (tgamma t) 1 * invMod q (tgamma t)) % tgamma t

/-- `m_tgammaQHatInvModq[i]` (`C:863-872`): `((((Q/qᵢ)⁻¹ mod qᵢ)·γ) mod qᵢ · t) mod qᵢ`. -/
def tgammaQHatInvModq (t : ℕ) (qs : List ℕ) (q : ℕ) : ℕ :=
  (invMod (qs.prod / q) q * gamma % q * t) % q

/-- **One coefficient** (`D:1663-1686`) from the residues `xs` (`xᵢ < qᵢ`): `s = 0`; for each limb
`s.ModAddFastEq(xᵢ.ModMulFastConst(tgammaQHatModq[i], qᵢ, …).ModMulFastConst(negInvqModtgamma[i],
tgamma, …), tgamma)`; then `s += s & (γ − 1)` and the result `s >> 26`. -/
def behz1 (t : ℕ) (qs xs : List ℕ) : ℕ :=
  let tg := tgamma t
  let s := (List.range xs.length).foldl (fun s i =>
      let qi := qs.getD i 0
      let b1 := tgammaQHatInvModq t qs qi
      let b2 := negInvqModtgamma t qi
      let y := modMulFastConst (xs.getD i 0) b1 qi (prepModMulConst b1 qi)
      modAddFastEq s (modMulFastConst y b2 tg (prepModMulConst b2 tg)) tg) 0
  rshift (addFast s (s &&& (gamma - 1))) 26

/-- **The library's BEHZ decryption** of `ct` (all limbs, `Q = qs.prod`) under `s`: the native
coefficients of the returned `NativePoly` (`D:1688-1695`; unreduced). -/
def bfvDecryptBEHZ (t : ℕ) (qs : List ℕ) {N : ℕ} (s : IntPoly N) (ct : List (Poly qs.prod N)) :
    NPoly ℕ N :=
  ⟨fun i => behz1 t qs (residues qs ((phase (ofInt qs.prod s) ct).coeff i).val)⟩

/-- **The parameters for which the statements are made**: `2 ≤ t`; `t·γ < 2⁶³` (the product
`tgamma` does not wrap and is a valid modulus for the signed fix-up of `ModMulFastConst`; this
refuses `t ≥ 2³⁷`); at least one limb; every limb odd, at least `3`, below `2⁶⁰` and
coprime to `t`; the limbs pairwise coprime. -/
def behzParamsOK? (t : ℕ) (qs : List ℕ) : Bool :=
  decide (2 ≤ t) && decide (t * gamma < 2 ^ 63) && decide (1 ≤ qs.length) &&
  qs.all (fun q => decide (3 ≤ q) && decide (q % 2 = 1) && decide (q < 2 ^ 60) &&
    decide (Nat.Coprime q t)) &&
  decide (qs.Pairwise Nat.Coprime)

/-- **The margin condition** for noise bound `B` (with `Q = qs.prod`, `L` limbs,
`V = t·B + (Q mod t)·(t − 1)` the bound on the invariant noise): `2·γ·V + 2·L·Q < γ·Q`, i.e.
`V/Q + L/γ < 1/2`: the fractional sum `Σ yᵢ/qᵢ ∈ [0, L)` that BEHZ drops costs `L/γ` of the
rounding interval. -/
def decBEHZOK? (t : ℕ) (qs : List ℕ) (B : ℕ) : Bool :=
  let Q := qs.prod
  decide (2 * gamma * (t * B + Q % t * (t - 1)) + 2 * qs.length * Q < gamma * Q)

end Spec.DecryptBFVBEHZ
