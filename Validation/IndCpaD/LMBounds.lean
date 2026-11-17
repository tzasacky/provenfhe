import Challenge.IndCpaD.LMBounds
import Validation.IndCpaD.LMBFV

/-!
# Validation.IndCpaD.LMBounds — proofs of the pins of `Challenge.IndCpaD.LMBounds`

By kernel evaluation.
-/

namespace Validation.IndCpaDLM
open Spec NPoly Scheme Source Spec.IndCpaD Spec.IndCpaDProfile Spec.IndCpaDLM
  Challenge.IndCpaDProfile Challenge.IndCpaDLM

theorem lm_bounds_kernel :
    admSeal (mkSeal gapQuery.1 gapQuery.2.1 gapQuery.2.2) = true ∧
      admLM mkSeal admSeal gapG gapQuery [("a", true)] = true := by
  decide +kernel

theorem lm_bounds_bfv_kernel :
    admBFVSeal (mkBFVSeal gapQueryBFV.1 gapQueryBFV.2.1 gapQueryBFV.2.2) = false ∧
      admLM mkBFVSeal admBFVSeal gapGBFV gapQueryBFV [("a", true)] = false := by
  decide +kernel

example := (@lm_bounds_kernel : type_of% @Challenge.IndCpaDLM.lm_bounds_kernel)
example := (@lm_bounds_bfv_kernel : type_of% @Challenge.IndCpaDLM.lm_bounds_bfv_kernel)

end Validation.IndCpaDLM
