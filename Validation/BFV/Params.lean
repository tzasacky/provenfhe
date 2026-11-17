import Challenge.BFV
import Validation.ParamsCheck
import Validation.Budget.Basic

/-!
# Validation.BFV.Params — the instance `sealBFV` (N = 8192, 174-bit modulus), acceptance, and the budget comparison

Proofs of `Challenge.BFV.sealBFV_ok`, `refAnalyzeBFV_accepts_seal` (kernel evaluation of the
locked checkers) and `ksBoundAt_le_ksBudget` (the instance of
`Validation.Budget.ksBoundAt_le_ksBudget` at `BudgetBFV.unitPlain P`).
-/

namespace Validation.BFV
open Spec NPoly Scheme Source Correct Challenge.BFV

theorem sealBFV_ok : SchemeParamsOK sealBFV :=
  Validation.Params.schemeParamsOK?_sound _ (by decide +kernel)

theorem refAnalyzeBFV_accepts_seal_eq :
    refAnalyzeBFV sealBFV (BudgetBFV.certified sealBFV (Budget.uniformLayout 1)) sealProg
      = some 1487107268480789873794743232688495311414 := by
  decide +kernel

theorem refAnalyzeBFV_accepts_seal :
    ∃ B, refAnalyzeBFV sealBFV (BudgetBFV.certified sealBFV (Budget.uniformLayout 1)) sealProg
      = some B ∧ B ≤ 2 ^ 131 :=
  ⟨_, refAnalyzeBFV_accepts_seal_eq, by norm_num⟩

theorem ksBoundAt_le_ksBudget (P : FullParams) (lay : Budget.KSLayout) (ℓ : ℕ) (h1 : 1 ≤ ℓ)
    (hℓ : ℓ ≤ P.src.qs.length) : BudgetBFV.ksBoundAt P lay ℓ ≤ BudgetBFV.ksBudget P lay :=
  Validation.Budget.ksBoundAt_le_ksBudget (BudgetBFV.unitPlain P) lay ℓ h1 hℓ

end Validation.BFV
