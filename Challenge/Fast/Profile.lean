import Challenge.Fast.ProfileDefs
import FHE.Holes

/-!
# Challenge.Fast.Profile — the profile mode of `fhe_check` is the locked decision   (LOCKED statements)

`Challenge/Fast/ProfileDefs.lean` defines the predicates; this file applies them to the
definition holes `FHE.Holes.certifyProfileFast`, `certifyBFVProfileFast`, `coversBFVFast` and
`coversBFVAtFast` (`FHE/Noise/FastProfile.lean`): the profile decisions and the BFV coverage
checks with their environments in search trees, the body run once. It does nothing else: every
statement below is a locked predicate applied to a hole (checked by `scripts/PinStatus.lean`).

All four are equalities on all inputs, at every budget. So the verdict of
`fhe_check --profile FILE`, computed with the fast functions at the declared budget `E`, is the
value of the locked `Challenge.Profile.certifyProfile? P E prog sw`
(`Challenge.Profile.certifyBFVProfile? P E prog`), and the statements of `Challenge.Profile`
(`certifyProfile?_sound`, `certifyBFVProfile?_sound`, …) are about it; the coverage line it
prints is the value of `Challenge.Profile.coversBFV?` and `Challenge.Profile.coversBFVAt?`, and
their realizability corollaries (`Challenge.Profile`, `Challenge.Profile.Tool`) are about it.
-/

namespace Challenge.Fast

/-- Compiled alias: does not build unless `FHE.Holes.certifyProfileFast` is computable. -/
def certifyProfileFastCompiled : ProfileDecision := FHE.Holes.certifyProfileFast

/-- The fast BGV profile decision returns exactly what `Challenge.Profile.certifyProfile?`
returns, at every budget. -/
theorem certifyProfileFast_eq : ProfileEqRef FHE.Holes.certifyProfileFast := sorry

/-- Compiled alias: does not build unless `FHE.Holes.certifyBFVProfileFast` is computable. -/
def certifyBFVProfileFastCompiled : ProfileDecisionBFV := FHE.Holes.certifyBFVProfileFast

/-- The fast BFV profile decision returns exactly what `Challenge.Profile.certifyBFVProfile?`
returns, at every per-instruction budget. -/
theorem certifyBFVProfileFast_eq : ProfileBFVEqRef FHE.Holes.certifyBFVProfileFast := sorry

/-- Compiled alias: does not build unless `FHE.Holes.coversBFVFast` is computable. -/
def coversBFVFastCompiled : CoverageBFV := FHE.Holes.coversBFVFast

/-- The fast conservative BFV coverage check returns exactly what `Challenge.Profile.coversBFV?`
returns. -/
theorem coversBFVFast_eq : CoversBFVEqRef FHE.Holes.coversBFVFast := sorry

/-- Compiled alias: does not build unless `FHE.Holes.coversBFVAtFast` is computable. -/
def coversBFVAtFastCompiled : CoverageBFVAt := FHE.Holes.coversBFVAtFast

/-- The fast level-exact BFV coverage check returns exactly what
`Challenge.Profile.coversBFVAt?` returns. -/
theorem coversBFVAtFast_eq : CoversBFVAtEqRef FHE.Holes.coversBFVAtFast := sorry

end Challenge.Fast
