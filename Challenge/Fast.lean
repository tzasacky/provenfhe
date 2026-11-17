import Challenge.Fast.Defs
import FHE.Holes

/-!
# Challenge.Fast — the fast path of `fhe_check` is the locked decision   (LOCKED statements)

`Challenge/Fast/Defs.lean` defines the predicates; this file applies them to the definition holes
`FHE.Holes.analyzeFast`, `certifyFast` (`FHE/Noise/Fast.lean`), `analyzeBFVFast` and
`certifyBFVFast`, `certifyBFVFreshFast`, `decryptLibFast`, `decryptLibExtFast` (`FHE/Noise/FastBFV.lean`) and `scaleOKFast` (`FHE/Noise/FastScaling.lean`): the reference analyses with their environments in
search trees, the body run once. It does nothing else: every
statement below is a locked predicate applied to a hole (checked by `scripts/PinStatus.lean`).

All eight are equalities on all inputs. So the tool's verdict, computed with the fast functions,
is the value of the locked `Challenge.Certify.certify?` (`Challenge.CertifyBFV.certifyBFV?`), and
the statements of `Challenge.Certify` and `Challenge.CertifyBFV` (`certify? x = some c → …`) are
about it.
-/

namespace Challenge.Fast

/-- Compiled alias: does not build unless `FHE.Holes.analyzeFast` is computable. -/
def analyzeFastCompiled : Challenge.Headline.NoiseAnalyzer := FHE.Holes.analyzeFast

/-- Compiled alias: does not build unless `FHE.Holes.certifyFast` is computable. -/
def certifyFastCompiled : Certifier := FHE.Holes.certifyFast

/-- The fast BGV analyzer returns exactly what `Challenge.Headline.refAnalyze` returns. -/
theorem analyzeFast_eq : AnalyzerEqRef FHE.Holes.analyzeFast := sorry

/-- The fast BGV certificate decision returns exactly what `Challenge.Certify.certify?` returns,
in every mode (worst case, fresh encryptions, fresh encryptions in `ℓ₂`). -/
theorem certifyFast_eq : CertifierEqRef FHE.Holes.certifyFast := sorry

/-- Compiled alias: does not build unless `FHE.Holes.analyzeBFVFast` is computable. -/
def analyzeBFVFastCompiled : Challenge.BFV.NoiseAnalyzerBFVAt := FHE.Holes.analyzeBFVFast

/-- Compiled alias: does not build unless `FHE.Holes.certifyBFVFast` is computable. -/
def certifyBFVFastCompiled : CertifierBFV := FHE.Holes.certifyBFVFast

/-- The fast BFV analyzer returns exactly what `Challenge.BFV.refAnalyzeBFVAt` returns. -/
theorem analyzeBFVFast_eq : AnalyzerBFVEqRef FHE.Holes.analyzeBFVFast := sorry

/-- The fast BFV certificate decision returns exactly what
`Challenge.CertifyBFV.certifyBFV?` returns, for every technique and method. -/
theorem certifyBFVFast_eq : CertifierBFVEqRef FHE.Holes.certifyBFVFast := sorry

/-- Compiled alias: does not build unless `FHE.Holes.certifyBFVFreshFast` is computable. -/
def certifyBFVFreshFastCompiled : CertifierBFVFresh := FHE.Holes.certifyBFVFreshFast

/-- The fast BFV fresh-encryption decision returns exactly what
`Challenge.BFVEncrypt.certifyBFVFresh?` returns, in every mode. -/
theorem certifyBFVFreshFast_eq : CertifierBFVFreshEqRef FHE.Holes.certifyBFVFreshFast := sorry

/-- Compiled alias: does not build unless `FHE.Holes.decryptLibFast` is computable. -/
def decryptLibFastCompiled : DecryptLibCheck := FHE.Holes.decryptLibFast

/-- The fast check of the library's BFV decryption returns exactly what
`Challenge.BFVDecrypt.decryptLibOK?` returns. -/
theorem decryptLibFast_eq : DecryptLibEqRef FHE.Holes.decryptLibFast := sorry

/-- Compiled alias: does not build unless `FHE.Holes.decryptLibExtFast` is computable. -/
def decryptLibExtFastCompiled : DecryptLibCheck := FHE.Holes.decryptLibExtFast

/-- The fast check of the library's BFV decryption by every routine returns exactly what
`Challenge.BFVDecryptLib.decryptLibExtOK?` returns. -/
theorem decryptLibExtFast_eq : DecryptLibExtEqRef FHE.Holes.decryptLibExtFast := sorry

/-- Compiled alias: does not build unless `FHE.Holes.scaleOKFast` is computable. -/
def scaleOKFastCompiled : ScaleCheck := FHE.Holes.scaleOKFast

/-- The fast user-level scaling check returns exactly what `Spec.Scaling.scaleOK?` returns. -/
theorem scaleOKFast_eq : ScaleOKEqRef FHE.Holes.scaleOKFast := sorry

end Challenge.Fast
