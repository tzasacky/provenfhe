import Challenge.Budget
import Validation.Headline.Noise

/-!
# Validation.Headline.NoiseCertified — the noise headline at the certified budget

Proof of `Challenge.Budget.certified_sound`: an instance of the soundness of the reference
analysis (`Validation.Headline.NoiseAux.refAnalyze_sound`) at `Spec.Budget.certified P lay`.
-/

namespace Validation.Budget
open Spec NPoly Scheme Source Correct Spec.Budget Challenge.Headline

theorem certified_sound (P : FullParams) (lay : KSLayout) (prog : Source.Program) (B : ℕ)
    (hP : SchemeParamsOK P) (hk : P.src.kind = .bgv)
    (h : refAnalyze P (certified P lay) prog = some B)
    (s : IntPoly P.src.N) (msgs : Var → Msg P.src.t P.src.N)
    (cts : Var → List (IntPoly P.src.N)) (hin : InputsOK P s prog msgs cts)
    (hb : Trace.BoundsOK P s prog msgs cts) :
    ∃ ρ, Source.eval P.src prog msgs = some ρ ∧
      ∀ σ, Trace.Run P (certified P lay) s prog.body (initEnv P.src prog msgs)
          (Trace.initCt P prog cts) σ →
        ∀ o ∈ prog.outputs, ∃ v ct, ρ o = some v ∧ σ o = some ct ∧ Encrypts P s B v ct :=
  -- literally the noise headline at `E = certified P lay` (`FHE.Holes.analyze` is `refAnalyze`)
  Validation.Headline.analyze_sound P (certified P lay) prog B hP hk h s msgs cts hin hb

end Validation.Budget
