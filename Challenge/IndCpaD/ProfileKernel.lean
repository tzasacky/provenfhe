import Challenge.IndCpaD.ProfileInstances
import Challenge.IndCpaD.ProfileBGVKS

/-!
# Challenge.IndCpaD.ProfileKernel — a realistic BFV member of the classes, kernel-checked   (LOCKED statements; proofs in `Validation/IndCpaD/ProfileKernel.lean`)

`Challenge.IndCpaD.ProfileInstances` shows by compiled `#guard` that `sealCirc` (two fresh
inputs and a plaintext at `sealSetting`: `N = 2¹³`, four 43–44-bit limbs, `t = 65537`, one
special prime, HPS declared; a product, its relinearization, a rotation by 5 and a plaintext
addition) is in the classes. This file states it as a closed fact checked by the kernel
(`decide +kernel`): a fresh encryption decrypts at the setting, and the circuit is in the
tool's class, in the library-free profile class at the tool's profile, and in the profile class at the
directly given textbook profile. (The BGV counterpart, with relinearization, rotation and modulus
switching, is `Challenge.IndCpaD.ProfileBGVKS.ksClass_bgvKSSeal`.)
-/

namespace Challenge.IndCpaDProfile
open Challenge.IndCpaD Spec.IndCpaDBFV

/-- **`sealCirc` is in every class at `N = 2¹³`, kernel-checked** (module docstring). -/
theorem sealCirc_kernel :
    freshDecOK sealSetting = true ∧ admissible sealCirc = true ∧
      admBFV (dataOf sealSetting) (profOf sealSetting) sealCirc = true ∧
      admBFV (dataOf sealSetting) sealTextbookProfile sealCirc = true := sorry

/-- **Discrimination, kernel-checked**: at `N = 2¹³`, the BFV circuit followed by four more
products and relinearizations is outside the profile class at the textbook profile; three
successive BGV products of fresh encryptions are outside the BGV profile class; and the BGV
circuit with a rotation by 5 is outside the key-switching evaluator's class when the public key
carries rotation keys for `g = 3` only. -/
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
      ksClass bgvKSSealData bgvKSLayout [3] bgvKSSealProfile bgvKSSealCirc = false := sorry

end Challenge.IndCpaDProfile
