import Spec.Scaling
import Challenge.Certify.Defs
import Challenge.CertifyBFV.Defs
import Challenge.BFVEncrypt.Defs
import Challenge.BFVDecrypt
import Challenge.BFVDecryptLib

/-!
# Challenge.Fast.Defs — what "the fast path is the locked one" means   (LOCKED definitions)

`fhe_check` gets its verdict from `Challenge.Certify.certify?` (BGV), which runs the reference
analyzer `Challenge.Headline.refAnalyze`, and from `Challenge.CertifyBFV.certifyBFV?` (BFV), which
runs `Challenge.BFV.refAnalyzeBFVAt`. Those definitions are written to be read: their environments are
functions, a lookup costs time linear in the number of earlier instructions, and the analysis is
quadratic in the program length. The tool runs faster functions instead (search trees, one pass
over the body). This file says what those functions must satisfy for nothing else in the trust
story to change: they are **equal** to the locked ones on every input, not merely sound.

The predicates are over an arbitrary function; `Challenge/Fast.lean` applies them to the
definition holes `FHE.Holes.analyzeFast`, `certifyFast`, `analyzeBFVFast`, `certifyBFVFast` and
`certifyBFVFreshFast`,
and `Validation/Fast.lean`, `Validation/FastBFV.lean` prove them. A CERTIFIED verdict computed by
the fast path is therefore a value `certify? x = some c` (`certifyBFV? x = some c`), and every
statement of `Challenge.Certify` (`Challenge.CertifyBFV`) applies to it unchanged.

This file imports trusted code and locked definitions only.
-/

namespace Challenge.Fast
open Spec Spec.Source Spec.Certify Challenge.Headline Challenge.Certify

/-- The type of a BGV certificate decision: the decoded data ↦ a certificate, or `none`. -/
abbrev Certifier : Type := Input → Option Certificate

/-- `analyze` returns what the reference analyzer returns, on every input: the same bound, and
`none` exactly when the reference rejects. -/
def AnalyzerEqRef (analyze : NoiseAnalyzer) : Prop :=
  ∀ (P : FullParams) (E : Trace.Budget) (prog : Source.Program),
    analyze P E prog = refAnalyze P E prog

/-- `c` returns what `certify?` returns, on every input: the same certificate (parameters,
budget, kind of input noise, bounds of every output), and `none` exactly when `certify?`
refuses. -/
def CertifierEqRef (c : Certifier) : Prop := ∀ x : Input, c x = certify? x

/-- The type of a BFV certificate decision: the decoded data ↦ a certificate, or `none`. -/
abbrev CertifierBFV : Type := Spec.CertifyBFV.InputBFV → Option Spec.CertifyBFV.CertificateBFV

/-- `analyze` returns what the BFV reference analyzer with one budget per instruction returns,
on every input (`Challenge.BFV.refAnalyzeBFVAt`, which `certifyBFV?` runs; at a constant budget
it is `refAnalyzeBFV`: `Challenge.BFV.refAnalyzeBFVAt_const`). -/
def AnalyzerBFVEqRef (analyze : Challenge.BFV.NoiseAnalyzerBFVAt) : Prop :=
  ∀ (P : FullParams) (E : ℕ → TraceBFV.Budget) (prog : Source.Program),
    analyze P E prog = Challenge.BFV.refAnalyzeBFVAt P E prog

/-- `c` returns what `certifyBFV?` returns, on every input: the same certificate (budget, bounds
of every output, multiplication levels, recorded assumptions), and `none` exactly when
`certifyBFV?` refuses. -/
def CertifierBFVEqRef (c : CertifierBFV) : Prop :=
  ∀ x : Spec.CertifyBFV.InputBFV, c x = Challenge.CertifyBFV.certifyBFV? x

/-- The type of the check of the library's BFV decryption on a certificate. -/
abbrev DecryptLibCheck : Type :=
  Spec.CertifyBFV.InputBFV → Spec.CertifyBFV.CertificateBFV → Bool

/-- `f` returns what `Challenge.BFVDecrypt.decryptLibOK?` returns, on every input. -/
def DecryptLibEqRef (f : DecryptLibCheck) : Prop :=
  ∀ (x : Spec.CertifyBFV.InputBFV) (c : Spec.CertifyBFV.CertificateBFV),
    f x c = Challenge.BFVDecrypt.decryptLibOK? x c

/-- `f` returns what `Challenge.BFVDecryptLib.decryptLibExtOK?` returns, on every input. -/
def DecryptLibExtEqRef (f : DecryptLibCheck) : Prop :=
  ∀ (x : Spec.CertifyBFV.InputBFV) (c : Spec.CertifyBFV.CertificateBFV),
    f x c = Challenge.BFVDecryptLib.decryptLibExtOK? x c

/-- The type of a BFV fresh-encryption certificate decision. -/
abbrev CertifierBFVFresh : Type :=
  Spec.CertifyBFV.InputBFV → Spec.EncryptBFV.FreshModeBFV → Option Spec.EncryptBFV.FreshCertBFV

/-- `c` returns what `Challenge.BFVEncrypt.certifyBFVFresh?` returns, on every input and mode. -/
def CertifierBFVFreshEqRef (c : CertifierBFVFresh) : Prop :=
  ∀ (x : Spec.CertifyBFV.InputBFV) (m : Spec.EncryptBFV.FreshModeBFV),
    c x m = Challenge.BFVEncrypt.certifyBFVFresh? x m

/-- The type of the user-level scaling check (`Spec.Scaling.scaleOK?`). -/
abbrev ScaleCheck : Type := Params → Source.Program → Spec.Scaling.ScaleData → Bool

/-- `f` returns what `Spec.Scaling.scaleOK?` returns, on every input: the check that the factor
`Decrypt` hands to `Decode` equals the factor the program's plain semantics asks for, at every
output (the user-level decryption check `fhe_check` runs on every OpenFHE BGV program with scaling
data). -/
def ScaleOKEqRef (f : ScaleCheck) : Prop :=
  ∀ (P : Params) (prog : Source.Program) (sd : Spec.Scaling.ScaleData),
    f P prog sd = Spec.Scaling.scaleOK? P prog sd

end Challenge.Fast
