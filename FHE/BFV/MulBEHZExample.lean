import Challenge.BFVMul.BEHZ

/-!
# FHE.BFV.MulBEHZExample — `behzMul` evaluated by the kernel at tiny parameters

`N = 2`, `t = 2`, ciphertext basis `qs = [3, 5]` (`Q = 15`, `Δ = ⌊Q/t⌋ = 7`), auxiliary basis
`bs = [7]`, `msk = 23`, `m̃ = 4`, secret `s = 1 − X`. Two ciphertexts with nonzero noise:

* `exC = (3 + 11X, 12 + 8X)` encrypts `m₁ = 1 + X` (phase `Δ·m₁ + 1`),
* `exD = (14 + 8X, 2)` encrypts `m₂ = X` (phase `Δ·m₂ + 1 − X`).

Every statement below is closed by `decide +kernel`: the proposition's `Decidable` instance is
evaluated to `true` by the Lean kernel itself (no compiler, no native code; the `+kernel` option
only skips the elaborator's own pre-evaluation, which does not unfold the well-founded recursion
inside `ZMod`'s inverse). The statements: the side condition holds; the inputs are BFV
encryptions with noise at most `1`; the limb-level `behzMul` returns a specific list; that list
decrypts (`Spec.Scheme.bfvDecrypt`, three components) to the product `m₁·m₂ = 1 + X` in
`Z_2[X]/(X²+1)`; the same for the square (`m₁² = 0`); and with `msk = 1` the side condition
fails and the result changes.

The outputs agree with the Python model of the OpenFHE routines
(`harness/bfv-rns/rnsbfv.py`, `mul_behz`) on the same inputs. They are *not* congruent to the
textbook `bfvMul`: BEHZ multiplies other representatives of the operands and floors instead of
rounding (`ex_behzMul_ne_textbook`); it meets the same contract with a larger budget
(`Validation.BFVMul.stepOK_mul_behz`).
-/

namespace FHE.BFV.MulBEHZExample
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
def exC : List (IntPoly 2) := [⟨![3, 11]⟩, ⟨![12, 8]⟩]
/-- An encryption of `m₂`: `d₀ + s·d₁ = 7·m₂ + 1 − X (mod 15)`. -/
def exD : List (IntPoly 2) := [⟨![14, 8]⟩, ⟨![2, 0]⟩]

theorem ex_auxOK : behzAuxOK? 2 2 [3, 5] [7] 23 4 = true := by decide +kernel

theorem exC_encrypts : BFVEncrypts 2 1 exS (exC.map (ofInt 15)) exM₁ := by
  unfold BFVEncrypts; decide +kernel

theorem exD_encrypts : BFVEncrypts 2 1 exS (exD.map (ofInt 15)) exM₂ := by
  unfold BFVEncrypts; decide +kernel

/-- The limb-level product, as a specific list. -/
theorem ex_behzMul :
    behzMul 2 [3, 5] [7] 23 4 exC exD = [⟨![3, 3]⟩, ⟨![7, 9]⟩, ⟨![14, 1]⟩] := by decide +kernel

/-- The product ciphertext decrypts to `m₁·m₂`. -/
theorem ex_behzMul_decrypts :
    bfvDecrypt 2 exS ((behzMul 2 [3, 5] [7] 23 4 exC exD).map (ofInt 15)) = exM₁ * exM₂ := by
  decide +kernel

/-- `m₁·m₂ = 1 + X` in `Z_2[X]/(X²+1)`. -/
theorem ex_product : exM₁ * exM₂ = ⟨![1, 1]⟩ := by decide +kernel

/-- The limb-level square, as a specific list. -/
theorem ex_behzSquare :
    behzMul 2 [3, 5] [7] 23 4 exC exC = [⟨![13, 11]⟩, ⟨![5, 9]⟩, ⟨![7, 8]⟩] := by decide +kernel

/-- The squared ciphertext decrypts to `m₁² = 0`. -/
theorem ex_behzSquare_decrypts :
    bfvDecrypt 2 exS ((behzMul 2 [3, 5] [7] 23 4 exC exC).map (ofInt 15)) = exM₁ * exM₁ := by
  decide +kernel

/-- BEHZ does not compute the textbook product modulo `Q` (other lifts, floor instead of
rounding); it meets the same contract with the slacks of `Spec.BudgetBFV.behzSlack`. -/
theorem ex_behzMul_ne_textbook :
    (behzMul 2 [3, 5] [7] 23 4 exC exD).map (ofInt 15) ≠ (bfvMul 2 15 exC exD).map (ofInt 15) := by
  decide +kernel

/-- With the too-small `msk = 1` (no Shenoy–Kumaresan correction at all) the side condition
fails and the product is a different list modulo `Q`. (At these parameters every `msk ≥ 11`
coprime to the other moduli happens to give the right result; `Challenge/BFVMul/BEHZ.lean` has a
`#guard` with a wrong result at `Q = 77`, `msk = 5`.) -/
theorem ex_small_aux :
    behzAuxOK? 2 2 [3, 5] [7] 1 4 = false ∧
      (behzMul 2 [3, 5] [7] 1 4 exC exD).map (ofInt 15) ≠
        (behzMul 2 [3, 5] [7] 23 4 exC exD).map (ofInt 15) := by
  decide +kernel

end FHE.BFV.MulBEHZExample
