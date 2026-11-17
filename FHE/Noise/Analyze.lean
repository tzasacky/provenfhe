import Challenge.Headline.Defs

/-!
# FHE.Noise.Analyze — the BGV noise analyzer   (UNTRUSTED, audited as part of the hole)

The analyzer is the textbook worst-case analysis of `Challenge.Headline.refAnalyze`: it tracks a
bound on the centred phase of every variable and rejects as soon as one reaches `Q/2`.
Soundness against every backend meeting the `Spec.Trace` contracts is proved in
`Validation/Headline/Noise.lean`.
-/

namespace FHE.Noise

/-- The certified BGV noise analyzer. -/
def analyze : Challenge.Headline.NoiseAnalyzer := Challenge.Headline.refAnalyze

end FHE.Noise
