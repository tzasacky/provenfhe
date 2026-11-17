import Challenge.BFVMul

/-!
# Validation.BFVMul.Params — acceptance with the budgets of the RNS multiplications

Proofs of `Challenge.BFVMul.refAnalyzeBFV_accepts_seal_behz` and
`refAnalyzeBFV_accepts_seal_poverq`, by kernel evaluation of the locked analyzer.
-/

namespace Validation.BFVMul
open Spec NPoly Scheme Source Correct Challenge.BFV Challenge.BFVMul

theorem refAnalyzeBFV_accepts_seal_behz_eq :
    refAnalyzeBFV sealBFV (sealBudget sealBEHZ) sealProg
      = some 1487107268619559764005097146872301164369 := by
  decide +kernel

theorem refAnalyzeBFV_accepts_seal_behz :
    sealBEHZ.ok = true ∧
    ∃ B, refAnalyzeBFV sealBFV (sealBudget sealBEHZ) sealProg = some B ∧ B ≤ 2 ^ 131 :=
  ⟨by decide +kernel, _, refAnalyzeBFV_accepts_seal_behz_eq, by norm_num⟩

theorem refAnalyzeBFV_accepts_seal_poverq_eq :
    refAnalyzeBFV sealBFV (sealBudget sealPOverQ) sealProg
      = some 6936443845196500763689501953860571305809 := by
  decide +kernel

theorem refAnalyzeBFV_accepts_seal_poverq :
    sealPOverQ.ok = true ∧
    ∃ B, refAnalyzeBFV sealBFV (sealBudget sealPOverQ) sealProg = some B ∧ B ≤ 2 ^ 133 :=
  ⟨by decide +kernel, _, refAnalyzeBFV_accepts_seal_poverq_eq, by norm_num⟩

end Validation.BFVMul
