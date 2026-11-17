import Challenge.BFVMul.POverQ

/-!
# FHE.BFV.MulPOverQExample — `poverqMul` evaluated by the kernel at tiny parameters

`N = 2`, `t = 2`, ciphertext basis `qs = [11, 13]` (`Q = 143`, `Δ = ⌊Q/t⌋ = 71`), auxiliary basis
`ps = [15, 16]` (`P = 240`), secret `s = 1 − X`. Two ciphertexts with nonzero noise:

* `exC = (−69 + 10X, 40 + 101X)` encrypts `m₁ = 1 + X` (phase `Δ·m₁ + 1`),
* `exD = (−90 + 6X, 13 + 77X)` encrypts `m₂ = X` (phase `Δ·m₂ − X`).

Every statement below is closed by `decide +kernel`: the proposition's `Decidable` instance is
evaluated to `true` by the Lean kernel itself (no compiler, no native code; the `+kernel` option
only skips the elaborator's own pre-evaluation, which does not unfold the well-founded recursion
inside `ZMod`'s inverse). The statements: the side condition holds; the inputs are BFV
encryptions with noise at most `1`; the limb-level `poverqMul` returns a specific list; that list
decrypts (`Spec.Scheme.bfvDecrypt`, three components) to the product `m₁·m₂ = 1 + X` in
`Z_2[X]/(X²+1)`; the same for the product of `exC` with itself (`m₁² = 0`). Unlike `hpsMul`, the
result is *not* the textbook `bfvMul` modulo `Q` (`ex_poverqMul_ne_bfvMul`): the fast conversion
of the second operand moves it, within the slack `Spec.BudgetBFV.poverqSlack 2 2 143 240 2 0 0`
(`e = 3`, `rho = 11`). With the too-small auxiliary basis `ps = [3]` (still accepted by
`poverqAuxOK?`; slack `e = 191`, `rho = 764`) both results decrypt wrongly.
-/

namespace FHE.BFV.MulPOverQExample
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
/-- An encryption of `m₁`: `c₀ + s·c₁ = 71·m₁ + 1 (mod 143)`. -/
def exC : List (IntPoly 2) := [⟨![-69, 10]⟩, ⟨![40, 101]⟩]
/-- An encryption of `m₂`: `d₀ + s·d₁ = 71·m₂ − X (mod 143)`. -/
def exD : List (IntPoly 2) := [⟨![-90, 6]⟩, ⟨![13, 77]⟩]

theorem ex_auxOK : poverqAuxOK? 2 2 [11, 13] [15, 16] = true := by decide +kernel

theorem ex_slack : BudgetBFV.poverqSlack 2 2 143 240 2 0 0 = ⟨3, 11, true⟩ := by decide +kernel

theorem exC_encrypts : BFVEncrypts 2 1 exS (exC.map (ofInt 143)) exM₁ := by
  unfold BFVEncrypts; decide +kernel

theorem exD_encrypts : BFVEncrypts 2 1 exS (exD.map (ofInt 143)) exM₂ := by
  unfold BFVEncrypts; decide +kernel

/-- The limb-level product, as a specific list. -/
theorem ex_poverqMul :
    poverqMul 2 [11, 13] [15, 16] exC exD = [⟨![90, 1]⟩, ⟨![30, 37]⟩, ⟨![112, 99]⟩] := by
  decide +kernel

/-- The product ciphertext decrypts to `m₁·m₂`. -/
theorem ex_poverqMul_decrypts :
    bfvDecrypt 2 exS ((poverqMul 2 [11, 13] [15, 16] exC exD).map (ofInt 143)) = exM₁ * exM₂ := by
  decide +kernel

/-- `m₁·m₂ = 1 + X` in `Z_2[X]/(X²+1)`. -/
theorem ex_product : exM₁ * exM₂ = ⟨![1, 1]⟩ := by decide +kernel

/-- The limb-level product of `exC` with itself, as a specific list. -/
theorem ex_poverqSquare :
    poverqMul 2 [11, 13] [15, 16] exC exC = [⟨![65, 123]⟩, ⟨![78, 92]⟩, ⟨![141, 96]⟩] := by
  decide +kernel

/-- It decrypts to `m₁² = 0`. -/
theorem ex_poverqSquare_decrypts :
    bfvDecrypt 2 exS ((poverqMul 2 [11, 13] [15, 16] exC exC).map (ofInt 143)) = exM₁ * exM₁ := by
  decide +kernel

/-- The result is not the textbook product modulo `Q`: the textbook `bfvMul` gives
`(−52 + 2X, 30 + 38X, −31 − 45X)`, which differs in the coefficient of `X` of the first two
components. -/
theorem ex_poverqMul_ne_bfvMul :
    bfvMul 2 143 exC exD = [⟨![-52, 2]⟩, ⟨![30, 38]⟩, ⟨![-31, -45]⟩] ∧
      (poverqMul 2 [11, 13] [15, 16] exC exD).map (ofInt 143) ≠
        (bfvMul 2 143 exC exD).map (ofInt 143) := by
  decide +kernel

/-- With the auxiliary basis `ps = [3]` the side condition still holds (the slack is then
`e = 191`, `rho = 764`, far beyond what `Q = 143` tolerates) and the product decrypts wrongly. -/
theorem ex_small_aux :
    poverqAuxOK? 2 2 [11, 13] [3] = true ∧
      BudgetBFV.poverqSlack 2 2 143 3 2 0 0 = ⟨191, 764, false⟩ ∧
      bfvDecrypt 2 exS ((poverqMul 2 [11, 13] [3] exC exD).map (ofInt 143)) ≠ exM₁ * exM₂ := by
  decide +kernel

/-! ### The leveled variant

`qs = [11, 13, 17]` (`Q = 2431`, `Δ = 1215`), `ps = [15, 16, 19]`, one limb dropped internally
(`Q_l = 143`, `P_l = 240`, `D = 17`); same secret and messages. -/

/-- An encryption of `m₁` modulo `2431`: phase `1215·m₁ + 1`. -/
def exC' : List (IntPoly 2) := [⟨![-1485, -86]⟩, ⟨![700, 2001]⟩]
/-- An encryption of `m₂` modulo `2431`: phase `1215·m₂ − X`. -/
def exD' : List (IntPoly 2) := [⟨![-2290, -450]⟩, ⟨![313, 1977]⟩]

theorem ex_leveledAuxOK : leveledAuxOK? 2 2 [11, 13, 17] [15, 16, 19] 1 = true := by
  decide +kernel

theorem ex_leveledSlack :
    BudgetBFV.leveledSlack 2 2 2431 143 240 3 0 0 0 = ⟨61, 330, true⟩ := by decide +kernel

theorem exC'_encrypts : BFVEncrypts 2 1 exS (exC'.map (ofInt 2431)) exM₁ := by
  unfold BFVEncrypts; decide +kernel

theorem exD'_encrypts : BFVEncrypts 2 1 exS (exD'.map (ofInt 2431)) exM₂ := by
  unfold BFVEncrypts; decide +kernel

/-- The limb-level leveled product, as a specific list (every coefficient a multiple of
`D = 17`). -/
theorem ex_leveledMul :
    leveledMul 2 [11, 13, 17] [15, 16, 19] 1 exC' exD' =
      [⟨![85, 2074]⟩, ⟨![170, 1751]⟩, ⟨![34, 2057]⟩] := by
  decide +kernel

/-- It decrypts to `m₁·m₂`. -/
theorem ex_leveledMul_decrypts :
    bfvDecrypt 2 exS ((leveledMul 2 [11, 13, 17] [15, 16, 19] 1 exC' exD').map (ofInt 2431)) =
      exM₁ * exM₂ := by
  decide +kernel

/-- With no limb dropped, `leveledMul` is `poverqMul`. -/
theorem ex_leveledMul_drop0 :
    leveledMul 2 [11, 13, 17] [15, 16, 19] 0 exC' exD' =
      poverqMul 2 [11, 13, 17] [15, 16, 19] exC' exD' := by
  decide +kernel

end FHE.BFV.MulPOverQExample
