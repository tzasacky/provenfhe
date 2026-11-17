import Spec.DecryptBFVLib
import Challenge.BFVDecrypt
import Challenge.BFVDecryptLow
import Challenge.BFVDecryptBEHZ

/-!
# Challenge.BFVDecryptLib — the library's decryption of every output, all three routines   (LOCKED definitions and statements; proofs in `Validation/BFVDecryptLib.lean`)

`decryptLibExtOK?` extends `Challenge.BFVDecrypt.decryptLibOK?` (HPS family, full level only) to
every routine `PKEBFVRNS::Decrypt` runs (`Spec.DecryptBFVLib`): for each output, at its own level
`ℓ` with its own bound `B` from the certificate,

* `ℓ = L`, HPS family: `decParamsOK?` and `decLibOK?` (`Challenge.BFVDecrypt`);
* `ℓ = L`, `BEHZ`: `behzParamsOK?` and `decBEHZOK?` (`Challenge.BFVDecryptBEHZ`);
* `ℓ < L`: `decLowParamsOK?` and `decLowOK?` (`Challenge.BFVDecryptLow`), and under `BEHZ` only
  `ℓ = 1` (the drop table is empty under `BEHZ`).

The technique must be declared (`InputBFV.mul`) and be one of OpenFHE's four. The corollary
`certifyBFV?_decryptsLibExt` concludes the library's decryption (`bfvDecryptOpenFHE`) of every
output. `decryptLibOK?` and `certifyBFV?_decryptsLib` are unchanged.
-/

namespace Challenge.BFVDecryptLib
open Spec Spec.Float Spec.DecryptBFV Spec.DecryptBFVLow Spec.DecryptBFVBEHZ Spec.DecryptBFVLib
  Spec.Scheme NPoly Source Correct Spec.CertifyBFV Challenge.CertifyBFV

/-- The routine family of a declared technique: `some false` for the HPS family, `some true` for
`BEHZ`, `none` otherwise (nothing declared, or the textbook algorithm, which OpenFHE does not
run). -/
def techLib? : Option Technique → Option Bool
  | some (.hps _) => some false
  | some (.poverq _) => some false
  | some (.leveled _) => some false
  | some (.behz ..) => some true
  | _ => none

/-- One output at level `ℓ` with bound `B` is covered by a proved routine. -/
def outputLibOK? (behz : Bool) (t : ℕ) (qs : List ℕ) (ℓ B : ℕ) : Bool :=
  if ℓ = qs.length then
    if behz then behzParamsOK? t qs && decBEHZOK? t qs B
    else decParamsOK? t qs && decLibOK? t qs B
  else decLowParamsOK? t qs ℓ && decLowOK? t qs ℓ B && (!behz || ℓ == 1)

/-- **The library's decryption is certified for every output**: the technique is OpenFHE's,
and every output, at its level (`Spec.Decrypt.outputLevel?`) and with its bound in `c.outputs`,
passes `outputLibOK?`. Depends only on `x.P`, `x.prog`, `x.mul` and `c.outputs`. -/
def decryptLibExtOK? (x : InputBFV) (c : CertificateBFV) : Bool :=
  match techLib? x.mul with
  | none => false
  | some behz => x.prog.outputs.all fun o =>
      match Decrypt.outputLevel? x.P.src x.prog o, c.outputs.lookup o with
      | some ℓ, some B => outputLibOK? behz x.P.src.t x.P.src.qs ℓ B
      | _, _ => false

/-- **One output.** A BFV value under `s` with exact message `m` that `Encrypts` with noise at
most `B`, at a level that passes `outputLibOK?`, is decrypted by the library's routine (every
conforming arithmetic) to native coefficients `c ≤ t` with `c ≡ mᵢ (mod t)`. -/
theorem output_decryptLibExt (P : FullParams) (hk : P.src.kind = .bfv) (A : ArithD)
    (hA : ConformsD A) (behz : Bool) (s : IntPoly P.src.N) (B : ℕ) (v : Val P.src)
    (ct : List (IntPoly P.src.N)) (m : Poly P.src.t P.src.N) (hmsg : v.msg = .exact m)
    (hkey : v.key = 1) (he : Encrypts P s B v ct)
    (hok : outputLibOK? behz P.src.t P.src.qs v.level B = true) (i : Fin P.src.N) :
    (((bfvDecryptOpenFHE A behz P.src.t P.src.qs v.level s ct).coeff i : ℕ) : ZMod P.src.t) =
        m.coeff i ∧
      (bfvDecryptOpenFHE A behz P.src.t P.src.qs v.level s ct).coeff i ≤ P.src.t := sorry

/-- **The BFV certificate, with the library's decryption by whichever routine it runs.** If
`certifyBFV? x = some c` and `decryptLibExtOK? x c`, then with `behz` the routine family of the
declared technique, for every conforming arithmetic, secret, messages and inputs within their
bounds, at the end of every run within the budgets `c.budget`, every output's LIBRARY decryption
with `s` at the output's level has native coefficients `c ≤ t` congruent to the message
`Source.eval` computes. -/
theorem certifyBFV?_decryptsLibExt (x : InputBFV) (c : CertificateBFV) (h : certifyBFV? x = some c)
    (hd : decryptLibExtOK? x c = true) (behz : Bool) (hb : techLib? x.mul = some behz) (A : ArithD)
    (hA : ConformsD A) (s : IntPoly x.P.src.N) (msgs : Var → Msg x.P.src.t x.P.src.N)
    (cts : Var → List (IntPoly x.P.src.N)) (hin : TraceBFV.InputsOK x.P s x.prog msgs cts) :
    ∃ ρ, Source.eval x.P.src x.prog msgs = some ρ ∧
      ∀ σ, TraceBFV.RunAt x.P c.budget s 0 x.prog.body (initEnv x.P.src x.prog msgs)
          (Trace.initCt x.P x.prog cts) σ →
        ∀ o ∈ x.prog.outputs, ∃ v ct m, ρ o = some v ∧ σ o = some ct ∧ v.msg = .exact m ∧
          ∀ i, (((bfvDecryptOpenFHE A behz x.P.src.t x.P.src.qs v.level s ct).coeff i : ℕ) :
                  ZMod x.P.src.t) = m.coeff i ∧
            (bfvDecryptOpenFHE A behz x.P.src.t x.P.src.qs v.level s ct).coeff i ≤ x.P.src.t :=
  sorry

/-- **The extension contains the old check**: a certified program whose outputs pass
`Challenge.BFVDecrypt.decryptLibOK?` (HPS family, full level) passes `decryptLibExtOK?`, so
switching to the new check refuses nothing the old one accepted. -/
theorem decryptLibOK?_ext (x : InputBFV) (c : CertificateBFV) (h : certifyBFV? x = some c)
    (hd : Challenge.BFVDecrypt.decryptLibOK? x c = true) : decryptLibExtOK? x c = true := sorry

-- Discrimination: BEHZ with a multi-limb output below the top level is refused (empty drop
-- table), one limb is not refused for that reason; nothing declared is refused.
#guard !outputLibOK? true 65537 [1152921504606830593, 1152921504606791681, 1152921504606748673] 2
  0
#guard outputLibOK? true 65537 [1152921504606830593, 1152921504606791681, 1152921504606748673] 1
  0
#guard outputLibOK? false 65537 [1152921504606830593, 1152921504606791681, 1152921504606748673] 2
  0
#guard techLib? none = none && techLib? (some .textbook) = none

end Challenge.BFVDecryptLib
