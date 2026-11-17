import Spec.DecryptBFVBEHZ
import Challenge.BFVDecryptLow

/-!
# Challenge.BFVDecryptBEHZ — OpenFHE's BEHZ decryption is textbook decryption under a computed margin   (LOCKED definitions and statements; proofs in `Validation/BFVDecryptBEHZ*.lean`)

`Spec.DecryptBFVBEHZ` transcribes OpenFHE v1.6.1's integer BFV decryption under `BEHZ` at the full
level (`DCRTPolyImpl::ScaleAndRound(moduliQ, t, tgamma, …)`), with its wrapping 64-bit products and
the signed fix-up of `ModMulFastConst`. The statements:

* **Shoup's multiplication** (`modMulFastConst_spec`): for `b < m < 2⁶³`, `a < 2⁶⁴`,
  `ModMulFastConst(a, b, m, PrepModMulConst(b, m)) = a·b mod m` (the transcription is literal; this
  is where `t·γ < 2⁶³` is needed).
* **Exactness** (`behz1_exact`): for every phase `x ∈ [0, Q)` and every integer `k` with
  `2γ·|t·x − Q·k| + 2·L·Q < γ·Q`, the routine returns `c ≤ t` with `c ≡ k (mod t)`. No floating
  point is involved; the `L/γ` term is the fractional sum `Σ yᵢ/qᵢ ∈ [0, L)` that BEHZ drops.
* **The main theorem** (`behz1_correct`, `bfvDecryptBEHZ_correct`): under `behzParamsOK?` and
  `decBEHZOK? t qs B`, with the noise of `BFVEncrypts` at most `B`, every native coefficient `c`
  satisfies `c ≡ mᵢ (mod t)` and `c ≤ t` (`c = t` occurs).
* **Pins**: `behzParamsOK?_t_lt` (`t < 2³⁷`: the side condition `t·γ < 2⁶³` on the 64-bit `tgamma`);
  `behzMargin_needed` (two limbs, `t = 2`: a noise that the textbook condition accepts and the
  transcribed routine does not decrypt correctly; `decBEHZOK?` refuses it).

**What is NOT shown.** `DecryptCore`, the NTT, the big-integer table arithmetic (`ModInverse`) are
modelled, not verified; BEHZ below the top level is the low-limb path of
`Challenge.BFVDecryptLow` (one limb only: `Spec.DecryptBFVLow` docstring).
-/

namespace Challenge.BFVDecryptBEHZ
open Spec Spec.Float Spec.DecryptBFV Spec.DecryptBFVLow Spec.DecryptBFVBEHZ Spec.Scheme NPoly

/-- **`ModMulFastConst` with its precomputation is the modular product** for a modulus below
`2⁶³` (where the signed fix-up is correct), `b < m`, and any 64-bit `a`. -/
theorem modMulFastConst_spec (a b m : ℕ) (ha : a < 2 ^ 64) (hb : b < m) (hm : 2 ≤ m)
    (hm' : m < 2 ^ 63) : modMulFastConst a b m (prepModMulConst b m) = a * b % m := sorry

/-- **The routine rounds exactly up to the dropped fraction**: for every `x ∈ [0, Q)` and every
integer `k` with `2γ·|t·x − Q·k| + 2·L·Q < γ·Q`, `behz1` returns `c ≤ t` with `c ≡ k (mod t)`. -/
theorem behz1_exact (t : ℕ) (qs : List ℕ) (hp : behzParamsOK? t qs = true) (x : ℕ)
    (hx : x < qs.prod) (k : ℤ)
    (hk : 2 * gamma * |(t : ℤ) * x - qs.prod * k| + 2 * qs.length * qs.prod < gamma * qs.prod) :
    ((behz1 t qs (residues qs x) : ℕ) : ZMod t) = (k : ZMod t) ∧ behz1 t qs (residues qs x) ≤ t :=
  sorry

/-- **One coefficient.** If the phase `x ∈ [0, Q)` is within `B` (centred) of `⌊Q/t⌋·m` modulo `Q`
and `decBEHZOK? t qs B`, the library returns `c ≤ t` with `c ≡ m (mod t)`. -/
theorem behz1_correct (t : ℕ) (qs : List ℕ) (hp : behzParamsOK? t qs = true) (B : ℕ)
    (hB : decBEHZOK? t qs B = true) (x m : ℕ) (hm : m < t) (hx : x < qs.prod)
    (hnoise : (((x : ℤ) - (qs.prod / t * m : ℕ) : ℤ) : ZMod qs.prod).valMinAbs.natAbs ≤ B) :
    ((behz1 t qs (residues qs x) : ℕ) : ZMod t) = (m : ZMod t) ∧ behz1 t qs (residues qs x) ≤ t :=
  sorry

/-- **OpenFHE's BFV decryption under BEHZ (full level) returns the encrypted message** when the
noise clause of `BFVEncrypts` holds at `B` and `decBEHZOK? t qs B`: every native coefficient `c`
satisfies `c ≡ mᵢ (mod t)` and `c ≤ t`. -/
theorem bfvDecryptBEHZ_correct (t : ℕ) (qs : List ℕ) (hp : behzParamsOK? t qs = true) {N : ℕ}
    (s : IntPoly N) (ct : List (Poly qs.prod N)) (m : Poly t N) (B : ℕ)
    (hnoise : normInf (centered (phase (ofInt qs.prod s) ct -
      ofInt qs.prod ⟨fun i => ((qs.prod / t * (m.coeff i).val : ℕ) : ℤ)⟩)) ≤ B)
    (hB : decBEHZOK? t qs B = true) (i : Fin N) :
    (((bfvDecryptBEHZ t qs s ct).coeff i : ℕ) : ZMod t) = m.coeff i ∧
      (bfvDecryptBEHZ t qs s ct).coeff i ≤ t := sorry

/-! ## Pins -/

/-- **The 64-bit overflow of `tgamma` is refused**: `behzParamsOK?` implies `t < 2³⁷`. -/
theorem behzParamsOK?_t_lt (t : ℕ) (qs : List ℕ) (h : behzParamsOK? t qs = true) : t < 2 ^ 37 :=
  sorry

/-- The limbs of `behzMargin_needed`. -/
def qsPinB : List ℕ := [2 ^ 59 - 55, 2 ^ 59 - 99]

/-- **The margin cannot be dropped.** `t = 2`, the two limbs `qsPinB`, message `0`, noise
`−B` with `B = (Q/2 − Q mod 2)/2 − 1` (the largest the textbook condition accepts): textbook
rounding gives `0`, the routine returns `1`; `decBEHZOK?` refuses `B`. -/
theorem behzMargin_needed :
    behzParamsOK? 2 qsPinB = true ∧
      Challenge.BFV.decOK 2 qsPinB.prod ((qsPinB.prod / 2 - qsPinB.prod % 2) / 2 - 1) = true ∧
      roundDiv (2 * -(((qsPinB.prod / 2 - qsPinB.prod % 2) / 2 - 1 : ℕ) : ℤ)) qsPinB.prod = 0 ∧
      behz1 2 qsPinB (residues qsPinB
        (qsPinB.prod - ((qsPinB.prod / 2 - qsPinB.prod % 2) / 2 - 1))) = 1 ∧
      decBEHZOK? 2 qsPinB ((qsPinB.prod / 2 - qsPinB.prod % 2) / 2 - 1) = false := sorry

-- OpenFHE-like parameters (`t = 65537`, three 60-bit limbs): 99.99% of the textbook threshold is
-- accepted. At `t = 137438822401 < 2³⁷` (`t·γ` just below `2⁶³`) the parameters pass; at
-- `t = 206158430209` (`t·γ ≈ 1.5·2⁶³`) they are refused.
#guard behzParamsOK? 65537 [1152921504606830593, 1152921504606791681, 1152921504606748673]
#guard decBEHZOK? 65537 [1152921504606830593, 1152921504606791681, 1152921504606748673]
  ((1152921504606830593 * 1152921504606791681 * 1152921504606748673 / 2 -
    1152921504606830593 * 1152921504606791681 * 1152921504606748673 % 65537 * 65536) / 65537 *
    9999 / 10000)
#guard behzParamsOK? 137438822401
  [1152921504606830593, 1152921504606791681, 1152921504606748673, 1152921504606683137]
#guard !behzParamsOK? 206158430209
  [1152921504606830593, 1152921504606791681, 1152921504606748673, 1152921504606683137]

end Challenge.BFVDecryptBEHZ
