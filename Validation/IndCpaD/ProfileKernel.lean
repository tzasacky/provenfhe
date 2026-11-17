import Challenge.IndCpaD.ProfileKernel

/-!
# Validation.IndCpaD.ProfileKernel — proof of the pin of `Challenge.IndCpaD.ProfileKernel`

A closed computation checked by the kernel (`decide +kernel`).
-/

namespace Validation.IndCpaDProfile
open Challenge.IndCpaD Challenge.IndCpaDProfile Spec.IndCpaDBFV

theorem sealCirc_kernel :
    freshDecOK sealSetting = true ∧ admissible sealCirc = true ∧
      admBFV (dataOf sealSetting) (profOf sealSetting) sealCirc = true ∧
      admBFV (dataOf sealSetting) sealTextbookProfile sealCirc = true := by
  decide +kernel

theorem classes_reject_kernel :
    admBFV (dataOf sealSetting) sealTextbookProfile
        ⟨{ sealCirc.prog with
            body := sealCirc.prog.body ++ [.mul "q" "o" "o", .relin "q" "q", .mul "q" "q" "q",
              .relin "q" "q", .mul "q" "q" "q", .relin "q" "q", .mul "q" "q" "q", .relin "q" "q"],
            outputs := ["q"] }, [], ["a", "b"], fun _ => 0⟩ = false ∧
      admBGV bgvSealData bgvSealProfile
        ({ inputs := [⟨"a", 2, 4, 1, 1⟩, ⟨"b", 2, 4, 1, 1⟩],
           body := [.mul "c" "a" "b", .mul "c" "c" "a", .mul "c" "c" "b"], outputs := ["c"] },
          ["a", "b"], fun _ => 0) = false ∧
      ksClass bgvKSSealData bgvKSLayout [3] bgvKSSealProfile bgvKSSealCirc = false := by
  decide +kernel

example := (@classes_reject_kernel : type_of% @Challenge.IndCpaDProfile.classes_reject_kernel)
example := (@sealCirc_kernel : type_of% @Challenge.IndCpaDProfile.sealCirc_kernel)

end Validation.IndCpaDProfile
