import Challenge.BFVMul.HPS

/-!
# FHE.BFV.MulHPSExample — `hpsMul` evaluated by the kernel at tiny parameters

`N = 2`, `t = 2`, ciphertext basis `qs = [3, 5]` (`Q = 15`, `Δ = ⌊Q/t⌋ = 7`), auxiliary basis
`ps = [7, 8]` (`P = 56`), secret `s = 1 − X`. Two ciphertexts with nonzero noise:

* `exC = (−7, 4 + 11X)` encrypts `m₁ = 1 + X` (phase `Δ·m₁ + 1`),
* `exD = (−15 + 17X, 13 + 2X)` encrypts `m₂ = X` (phase `Δ·m₂ − X`).

Every statement below is closed by `decide +kernel`: the proposition's `Decidable` instance is
evaluated to `true` by the Lean kernel itself (no compiler, no native code; the `+kernel` option
only skips the elaborator's own pre-evaluation, which does not unfold the well-founded recursion
inside `ZMod`'s inverse). The statements: the side condition holds; the inputs are BFV
encryptions with noise at most `1`; the limb-level `hpsMul` returns a specific list; that list
decrypts (`Spec.Scheme.bfvDecrypt`, three components) to the product `m₁·m₂ = 1 + X` in
`Z_2[X]/(X²+1)`; the same for the square (`m₁² = 0`); and the outputs agree with the textbook
`bfvMul` modulo `Q`.
-/

namespace FHE.BFV.MulHPSExample
open Spec NPoly Scheme Challenge.BFV Challenge.BFVMul

/-- Equality of coefficient vectors is decidable. -/
instance {R : Type} [DecidableEq R] {N : ℕ} : DecidableEq (NPoly R N) := fun a b =>
  decidable_of_iff (a.coeff = b.coeff) ⟨fun h => NPoly.ext h, fun h => h ▸ rfl⟩

/-- The secret `1 − X`. -/
def exS : IntPoly 2 := ⟨![1, -1]⟩
/-- `m₁ = 1 + X`. -/
def exM₁ : Poly 2 2 := ⟨![1, 1]⟩
/-- `m₂ = X`. -/
def exM₂ : Poly 2 2 := ⟨![0, 1]⟩
/-- An encryption of `m₁`: `c₀ + s·c₁ = 7·m₁ + 1 (mod 15)`. -/
def exC : List (IntPoly 2) := [⟨![-7, 0]⟩, ⟨![4, 11]⟩]
/-- An encryption of `m₂`: `d₀ + s·d₁ = 7·m₂ − X (mod 15)`. -/
def exD : List (IntPoly 2) := [⟨![-15, 17]⟩, ⟨![13, 2]⟩]

theorem ex_auxOK : hpsAuxOK? 2 2 [3, 5] [7, 8] = true := by decide +kernel

theorem exC_encrypts : BFVEncrypts 2 1 exS (exC.map (ofInt 15)) exM₁ := by
  unfold BFVEncrypts; decide +kernel

theorem exD_encrypts : BFVEncrypts 2 1 exS (exD.map (ofInt 15)) exM₂ := by
  unfold BFVEncrypts; decide +kernel

/-- The limb-level product, as a specific list. -/
theorem ex_hpsMul :
    hpsMul 2 [3, 5] [7, 8] exC exD = [⟨![0, 13]⟩, ⟨![3, 14]⟩, ⟨![0, 2]⟩] := by decide +kernel

/-- The product ciphertext decrypts to `m₁·m₂`. -/
theorem ex_hpsMul_decrypts :
    bfvDecrypt 2 exS ((hpsMul 2 [3, 5] [7, 8] exC exD).map (ofInt 15)) = exM₁ * exM₂ := by
  decide +kernel

/-- `m₁·m₂ = 1 + X` in `Z_2[X]/(X²+1)`. -/
theorem ex_product : exM₁ * exM₂ = ⟨![1, 1]⟩ := by decide +kernel

/-- The limb-level square, as a specific list. -/
theorem ex_hpsSquare :
    hpsMul 2 [3, 5] [7, 8] exC exC = [⟨![7, 0]⟩, ⟨![8, 7]⟩, ⟨![0, 11]⟩] := by decide +kernel

/-- The squared ciphertext decrypts to `m₁² = 0`. -/
theorem ex_hpsSquare_decrypts :
    bfvDecrypt 2 exS ((hpsMul 2 [3, 5] [7, 8] exC exC).map (ofInt 15)) = exM₁ * exM₁ := by
  decide +kernel

/-- Agreement with the textbook multiplication modulo `Q` (an instance of
`FHE.BFV.MulHPS.hpsMul_congr_bfvMul`, here by evaluation). -/
theorem ex_hpsMul_congr :
    (hpsMul 2 [3, 5] [7, 8] exC exD).map (ofInt 15) = (bfvMul 2 15 exC exD).map (ofInt 15) := by
  decide +kernel

/-- With the too-small auxiliary basis `ps = [7]` the side condition fails and the square is
not congruent to the textbook one. -/
theorem ex_small_aux :
    hpsAuxOK? 2 2 [3, 5] [7] = false ∧
      (hpsMul 2 [3, 5] [7] exC exC).map (ofInt 15) ≠ (bfvMul 2 15 exC exC).map (ofInt 15) := by
  decide +kernel

end FHE.BFV.MulHPSExample
