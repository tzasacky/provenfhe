import Challenge.Headline.Defs
import FHE.Holes

/-!
# Challenge.Headline — the headline theorem   (LOCKED statements; proofs in `Validation/`)

What each statement means is defined in `Challenge/Headline/Defs.lean`, which depends on trusted
code only. This file applies those predicates to the definition hole `FHE.Holes.analyze`, and
does nothing else: every statement below is a locked predicate applied to a constant, with
no notation, so nothing the hole module declares can change what is being claimed.

**Headline (H6, BGV).** `analyze_sound`, with `analyze_tight`, `analyze_accepts_addMul` and
`analyze_rejects_nonBGV` (nothing outside the theorem's scope is accepted).

A headline is established only when its soundness pin and all of its acceptance pins are proved
about the same hole, and the hole passes the computability audit (`FHE/Holes.lean`). Soundness
alone is satisfied by a checker that rejects everything.

`analyzeCompiled` makes this file fail to build if the hole is not a compiled function.
-/

namespace Challenge.Headline

/-- Compiled alias: does not build unless `FHE.Holes.analyze` is computable. -/
def analyzeCompiled : NoiseAnalyzer := FHE.Holes.analyze

/-! ## Headline: noise (BGV) -/

theorem analyze_sound : NoiseSoundBGV FHE.Holes.analyze := sorry

theorem analyze_tight : NoiseTightBGV FHE.Holes.analyze := sorry

theorem analyze_accepts_addMul : NoiseAcceptsAddMul FHE.Holes.analyze := sorry

theorem analyze_rejects_nonBGV : NoiseRejectsNonBGV FHE.Holes.analyze := sorry

end Challenge.Headline
