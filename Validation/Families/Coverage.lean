import Challenge.Families.Coverage

/-!
# Validation.Families.Coverage — proofs of the pins of `Challenge.Families.Coverage`

Both coverage instances are closed computations, checked by the kernel (`decide +kernel`).
-/

namespace Validation.Families
open Spec Spec.Source Challenge.BFV Challenge.BFVMul Challenge.Profile Challenge.Families

theorem sealBFV_covers :
    coversBFV? sealBFV sealLayout 1 8 sealProg.body
      (fun _ => BudgetBFV.certifiedApprox sealBFV sealLayout 1 8 0) = true := by
  decide +kernel

theorem lattigoBFV_covers :
    coversBFV? lattigoBFV (Challenge.Instances.Lattigo.layout lattigoBFV) 0 65537
      (squareChain 12 7).body
      (fun _ => BudgetBFV.certifiedApprox lattigoBFV
        (Challenge.Instances.Lattigo.layout lattigoBFV) 0 65537 0) = true := by
  decide +kernel

end Validation.Families
