import Challenge.Headline.Defs
import FHE.Noise.Analyze
import Challenge.Fast.Defs
import FHE.Noise.Fast
import FHE.Noise.FastBFV
import FHE.Noise.FastScaling
import Challenge.Fast.ProfileDefs
import FHE.Noise.FastProfile

/-!
# FHE.Holes — the definition holes of the headline theorems   (UNTRUSTED, audited)

`Challenge/Headline.lean` states the headline theorems about the first function defined
here. The hole is filled: `analyze` is
`FHE.Noise.analyze`, which is *defined as* the reference analyzer
`Challenge.Headline.refAnalyze` (so the tightness headline `analyze_tight` holds trivially
today). The headline theorems about them are proved in `Validation/Headline/`.

`Challenge/Fast.lean` states that the fast path of `fhe_check` is the locked decision: the holes
`analyzeFast` and `certifyFast` (`FHE/Noise/Fast.lean`) are **equal**, on every input, to
`Challenge.Headline.refAnalyze` and `Challenge.Certify.certify?`, and `analyzeBFVFast`,
`certifyBFVFast` (`FHE/Noise/FastBFV.lean`) to `Challenge.BFV.refAnalyzeBFVAt` and
`Challenge.CertifyBFV.certifyBFV?`, and `certifyBFVFreshFast` to
`Challenge.BFVEncrypt.certifyBFVFresh?`, and `scaleOKFast` (`FHE/Noise/FastScaling.lean`) to
`Spec.Scaling.scaleOK?`. Proved in `Validation/Fast.lean`, `Validation/FastBFV.lean`,
`Validation/FastScaling.lean`.

`Challenge/Fast/Profile.lean` states the same of the profile mode (`fhe_check --profile`): the
holes `certifyProfileFast`, `certifyBFVProfileFast`, `coversBFVFast` and `coversBFVAtFast`
(`FHE/Noise/FastProfile.lean`) are equal to `Challenge.Profile.certifyProfile?`,
`certifyBFVProfile?`, `coversBFV?` and `coversBFVAt?`. Proved in `Validation/FastProfile.lean`.

Rules for this file and for everything it imports from outside `Spec/` and `Challenge/` (they are
what makes "the checker is a program" checkable; see `docs/SPEC.md` §4):

* The types of the holes are fixed (`Challenge.Headline.NoiseAnalyzer`, `Challenge.Fast.Certifier`, `Challenge.BFV.NoiseAnalyzerBFVAt`,
  `Challenge.Fast.CertifierBFV`, `Challenge.Fast.CertifierBFVFresh`, `Challenge.Fast.DecryptLibCheck`,
  `Challenge.Fast.ProfileDecision`, `Challenge.Fast.ProfileDecisionBFV`, `Challenge.Fast.CoverageBFV`,
  `Challenge.Fast.CoverageBFVAt`).
* All must be compiled, total functions. This file and its untrusted imports obey the same
  banned-construct list as `Spec/` (`scripts/check-spec.sh` step 2): nothing marked as not
  computable, no replacement of compiled code, no foreign functions, no escape from the
  termination or totality checks, no hidden bodies, no assumptions. (A function defined by
  classical choice on the truth of the conclusion would satisfy soundness and tell nobody
  anything.)
* No syntax extensions of any kind, and no instances on types from `Spec/` or
  `Challenge/`: this file is imported by `Challenge/Headline.lean`, and must not be able to change
  how a locked statement is read.
* It must not import `Challenge.Headline`, `Challenge.Fast`, `Challenge.Fast.Profile` or anything from `Validation/`. Proofs about these
  functions live elsewhere.
-/

namespace FHE.Holes

/-- HOLE (H6): the noise analyzer. -/
def analyze : Challenge.Headline.NoiseAnalyzer := FHE.Noise.analyze

/-- HOLE (fast path): the BGV analyzer `fhe_check` runs; equal to
`Challenge.Headline.refAnalyze` (`Challenge.Fast.analyzeFast_eq`). -/
def analyzeFast : Challenge.Headline.NoiseAnalyzer := FHE.Noise.Fast.analyze

/-- HOLE (fast path): the BGV certificate decision `fhe_check` runs; equal to
`Challenge.Certify.certify?` (`Challenge.Fast.certifyFast_eq`). -/
def certifyFast : Challenge.Fast.Certifier := FHE.Noise.Fast.certify

/-- HOLE (fast path): the BFV analyzer `fhe_check` runs; equal to
`Challenge.BFV.refAnalyzeBFVAt` (`Challenge.Fast.analyzeBFVFast_eq`). -/
def analyzeBFVFast : Challenge.BFV.NoiseAnalyzerBFVAt := FHE.Noise.FastBFV.analyze

/-- HOLE (fast path): the BFV certificate decision `fhe_check` runs; equal to
`Challenge.CertifyBFV.certifyBFV?` (`Challenge.Fast.certifyBFVFast_eq`). -/
def certifyBFVFast : Challenge.Fast.CertifierBFV := FHE.Noise.FastBFV.certify

/-- HOLE (fast path): the BFV fresh-encryption decision `fhe_check` runs; equal to
`Challenge.BFVEncrypt.certifyBFVFresh?` (`Challenge.Fast.certifyBFVFreshFast_eq`). -/
def certifyBFVFreshFast : Challenge.Fast.CertifierBFVFresh := FHE.Noise.FastBFV.certifyFresh

/-- HOLE (fast path): the check of the library's BFV decryption `fhe_check` runs; equal to
`Challenge.BFVDecrypt.decryptLibOK?` (`Challenge.Fast.decryptLibFast_eq`). -/
def decryptLibFast : Challenge.Fast.DecryptLibCheck := FHE.Noise.FastBFV.decryptLibOK

/-- HOLE (fast path): the check of the library's BFV decryption by every routine `fhe_check`
runs; equal to `Challenge.BFVDecryptLib.decryptLibExtOK?` (`Challenge.Fast.decryptLibExtFast_eq`). -/
def decryptLibExtFast : Challenge.Fast.DecryptLibCheck := FHE.Noise.FastBFV.decryptLibExtOK

/-- HOLE (fast path): the user-level scaling check `fhe_check` runs on every OpenFHE BGV program
with scaling data; equal to `Spec.Scaling.scaleOK?` (`Challenge.Fast.scaleOKFast_eq`). -/
def scaleOKFast : Challenge.Fast.ScaleCheck := FHE.Noise.FastScaling.scaleOK

/-- HOLE (profile mode): the BGV profile decision `fhe_check --profile` runs; equal to
`Challenge.Profile.certifyProfile?` (`Challenge.Fast.certifyProfileFast_eq`). -/
def certifyProfileFast : Challenge.Fast.ProfileDecision := FHE.Noise.FastProfile.certifyProfile

/-- HOLE (profile mode): the BFV profile decision `fhe_check --profile` runs; equal to
`Challenge.Profile.certifyBFVProfile?` (`Challenge.Fast.certifyBFVProfileFast_eq`). -/
def certifyBFVProfileFast : Challenge.Fast.ProfileDecisionBFV :=
  FHE.Noise.FastProfile.certifyBFVProfile

/-- HOLE (profile mode): the conservative BFV coverage check; equal to
`Challenge.Profile.coversBFV?` (`Challenge.Fast.coversBFVFast_eq`). -/
def coversBFVFast : Challenge.Fast.CoverageBFV := FHE.Noise.FastProfile.coversBFV

/-- HOLE (profile mode): the level-exact BFV coverage check; equal to
`Challenge.Profile.coversBFVAt?` (`Challenge.Fast.coversBFVAtFast_eq`). -/
def coversBFVAtFast : Challenge.Fast.CoverageBFVAt := FHE.Noise.FastProfile.coversBFVAt

end FHE.Holes
