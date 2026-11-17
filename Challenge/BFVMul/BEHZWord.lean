import Challenge.BFVMul.BEHZ
import Challenge.BFVMul.Float

/-!
# Challenge.BFVMul.BEHZWord — the machine-word precondition of OpenFHE's BEHZ multiplication   (LOCKED definitions and statements; proofs in `Validation/BFVMul/BEHZWord.lean`)

`Challenge.BFVMul.behzMul` transcribes OpenFHE's BEHZ multiplication with exact integers; its
side condition `behzAuxOK?` makes the *transcription* meet the `mul` contract. The library
computes the transcription only if its 64-bit word arithmetic does, and that needs more. This file
states the extra condition, `behzWordOK?`, which `Challenge.CertifyBFV.certifyBFV?` checks next to
`behzAuxOK?` at every BEHZ `mul` and `square`, and proves the part of it that bounds the
Shenoy–Kumaresan correction.

Source: upstream OpenFHE v1.6.1, commit `b59e1f291965f14fbee5172cd83a20f5b856204f`;
`dcrtpoly-impl.h` is `src/core/include/lattice/hal/default/dcrtpoly-impl.h`, `ubintnat.h` is
`src/core/include/math/hal/intnat/ubintnat.h`. `NATIVEINT == 64` with `HAVE_INT128` only.

**The word step.** `FastBaseConvSK` (`dcrtpoly-impl.h:1869-1953`) computes the
Shenoy–Kumaresan correction `α ∈ [0, msk)` (`:1897-1911`) and, for each ciphertext modulus `q`,
moves `α − msk` into `[0, q)` when `α > ⌊msk/2⌋` by
`alphaskBModqj.ModSubFast(moduliBsk[sizeBskm1], moduliQ[j])` (`:1936-1937`). `ModSubFast`
(`ubintnat.h:940-943`) computes `a − b + (a < b ? q : 0)` in `uint64_t` and is documented for
operands below the modulus; here `b = msk` and `a = α` are residues modulo `msk`, not modulo `q`.
With `αc = α − msk` the centred correction (`BEHZ.skAlpha1`), the model's arithmetic is exact
only when `αc ≥ −q`: the transcription takes the centred integer `αc`, and the word computed by
`ModSubFast` equals `αc + q` exactly in that case. The size of `|αc|` depends on `msk`
(`bfvrns-cryptoparameters.cpp:686-695`) through `αc = (Σⱼ zⱼ·B̂ⱼ − F)/B`, about `−F/B`, with `F`
the fast floor of the tensor product (up to about `t·N·Q/2`).

**The condition** (`behzWordOK? t N qs bs msk mt`):

* `αc ≥ −q` for every `q ∈ qs`, in the worst case: for every `q ∈ qs`,
  `t·N·Q·(m̃ + 2(k−1))² + 2k·m̃² ≤ m̃²·B·2q`. This is the size condition of `behzAuxOK?` with
  `msk − 1 − 2m` replaced by `2q`: under it every fast floor has `|F| ≤ q·B`, and since
  `B·αc = Σⱼ zⱼ·B̂ⱼ − F ≥ −F`, `αc ≥ −q` (`behz_sk_alpha_ge`, proved). With OpenFHE's bases
  (`B` and `Q` of the same size) it says roughly `t·N ≤ 2·q_min`.
* `m̃ < b` for every `b ∈ bs ++ [msk]`: the centred Montgomery remainder `r` is moved into `[0, b)`
  as `r + b − m̃` (`dcrtpoly-impl.h:1791-1793`).
* `floatBasisOK qs` and `floatBasisOK (bs ++ [msk])`: at most 128 moduli per basis, each below
  `2⁶⁰` (OpenFHE's `MAX_MODULUS_SIZE64`, `basicint.h:40`, which its Barrett (`ModMul` with `mu`)
  and Shoup (`ModMulFastConst`, `ubintnat.h:1248-1252`, signed result) routines assume; the
  enlargement loop can push `msk` past it). With it the unreduced 128-bit sums
  `result += Mul128(…)` / `aq += Mul128(…)` (`:1781-1785`, `:1848-1852`, `:1921-1925`) of at
  most 128 products of two words below `2⁶⁰` cannot wrap (the bound of
  `Challenge.BFVMul.acc_no_overflow`).

**What is proved and what is argued.** Proved (`behz_sk_alpha_ge`): under `behzAuxOK?` and
`behzWordOK?`, for every two-component operands and every coefficient of every component the
transcription's `FastBaseConvSK` reads, the centred correction is at least `−q` for every
`q ∈ qs`; `sk1_alpha` says that this `α` is the one `BEHZ.sk1` uses. Argued, not proved: that
`ModSubFast`, `ModMulFastConst`, Barrett reduction, `BarrettUint128ModUint64` and the NTT compute
the residues the transcription takes, given these word bounds (the same status as the integer
steps of the HPS family, `Challenge/BFVMul/Float.lean`). The condition is sufficient, not
necessary: it is a worst case over all operands with the coefficient bounds of the lifts. For
parameters outside it the proof says nothing, and `certifyBFV?` refuses the certificate.
-/

namespace Challenge.BFVMul
open Spec NPoly Scheme

variable {N : ℕ}

namespace BEHZ

/-- The centred Shenoy–Kumaresan correction of `BEHZ.sk1`: `α = [(Σⱼ zⱼ·B̂ⱼ − x_sk)·B⁻¹]_{msk}`,
read as `α − msk` when `α > ⌊msk/2⌋` (`dcrtpoly-impl.h:1897-1911`, `:1936`). -/
def skAlpha1 (bs : List ℕ) (msk : ℕ) (xb : List ℤ) (xsk : ℤ) : ℤ :=
  let z := HPS.digits bs xb
  let α := (convSum bs z msk % msk - xsk) * HPS.invMod bs.prod msk % msk
  if ((msk / 2 : ℕ) : ℤ) < α then α - msk else α

end BEHZ

/-- **The machine-word side condition of OpenFHE's BEHZ multiplication** (module docstring):
both bases pass `floatBasisOK`, `m̃` is below every modulus of `bs ++ [msk]`, and for every
`q ∈ qs`, `t·N·Q·(m̃ + 2(k−1))² + 2k·m̃² ≤ m̃²·B·2q` (the Shenoy–Kumaresan correction is at least
`−q`: the condition under which the model's arithmetic at `dcrtpoly-impl.h:1937` is exact). -/
def behzWordOK? (t N : ℕ) (qs bs : List ℕ) (msk mt : ℕ) : Bool :=
  floatBasisOK qs && floatBasisOK (bs ++ [msk]) &&
  (bs ++ [msk]).all (fun b => decide (mt < b)) &&
  qs.all fun q =>
    decide (t * N * qs.prod * (mt + 2 * (qs.length - 1)) ^ 2 + 2 * qs.length * mt ^ 2 ≤
      mt ^ 2 * bs.prod * (2 * q))

/-- `BEHZ.sk1` subtracts `skAlpha1 · B`: the correction of the statement below is the one the
transcription of `FastBaseConvSK` uses. -/
theorem sk1_alpha (bs : List ℕ) (msk : ℕ) (xb : List ℤ) (xsk : ℤ) (q : ℕ) :
    BEHZ.sk1 bs msk xb xsk q =
      (BEHZ.convSum bs (HPS.digits bs xb) q - BEHZ.skAlpha1 bs msk xb xsk * ((bs.prod % q : ℕ) : ℤ))
        % q := sorry

/-- **Under `behzAuxOK?` and `behzWordOK?` the Shenoy–Kumaresan correction is at least `−q`**
for every ciphertext modulus `q`, at every coefficient of every component that `behzMul` passes
to `BEHZ.convSK` (the fast floor of the limb-wise tensor product of the extended operands): the
precondition under which `ModSubFast` at `dcrtpoly-impl.h:1937` computes `α − msk + q` without
wrapping. -/
theorem behz_sk_alpha_ge (t : ℕ) (qs bs : List ℕ) (msk mt : ℕ)
    (haux : behzAuxOK? t N qs bs msk mt = true) (hword : behzWordOK? t N qs bs msk mt = true)
    (c d : List (IntPoly N)) (hc : c.length = 2) (hd : d.length = 2) :
    ∀ x ∈ HPS.tensor (qs ++ (bs ++ [msk]))
        (c.map fun a => BEHZ.extend qs (bs ++ [msk]) mt (HPS.toLimbs qs a))
        (d.map fun a => BEHZ.extend qs (bs ++ [msk]) mt (HPS.toLimbs qs a)),
      ∀ (i : Fin N), ∀ q ∈ qs,
        -(q : ℤ) ≤ BEHZ.skAlpha1 bs msk
          (HPS.residues ((BEHZ.floorq t qs (bs ++ [msk]) x).take bs.length) i)
          (((BEHZ.floorq t qs (bs ++ [msk]) x).getD bs.length 0).coeff i) := sorry

/-! ## Checks

`N = 4`, `qs = [7, 11]` (`Q = 77`), `bs = [13, 17]` (`B = 221`), `m̃ = 2`, so the left-hand side
of both size conditions is `t·4·77·4² + 2·2·2² = 4928·t + 16`. With `t = 2`, `msk = 19` both hold
(`9 872 ≤ 2²·221·14 = 12 376`, and `≤ 2²·221·2·7 = 12 376` for `q = 7`). With `t = 5` and the
larger `msk = 53` the size condition of `behzAuxOK?` holds (`24 656 ≤ 2²·221·48 = 42 432`) but the
word condition does not (`24 656 > 12 376`): the larger `msk` makes the transcription exact, not
the library's words. -/

#guard behzAuxOK? 2 4 [7, 11] [13, 17] 19 2 && behzWordOK? 2 4 [7, 11] [13, 17] 19 2
#guard behzAuxOK? 5 4 [7, 11] [13, 17] 53 2 && !behzWordOK? 5 4 [7, 11] [13, 17] 53 2
-- `m̃` not below an auxiliary modulus (`m̃ = 16 > 13`), and a modulus above `2⁶⁰`.
#guard !behzWordOK? 1 4 [7, 11] [13, 17] 19 16
#guard !behzWordOK? 1 4 [7, 11] [13, 17] (2 ^ 60 + 1) 2

end Challenge.BFVMul
