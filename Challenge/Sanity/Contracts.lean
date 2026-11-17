import Spec.TraceBFV

/-!
# Challenge.Sanity.Contracts — the exact contracts leave no freedom   (LOCKED statements; proofs in `Validation/Sanity/Contracts.lean`)

A contract that some output meets for no reason, or that two very different outputs both meet,
would make "every run" say less than it seems. For the operations that are exact on phases
(everything but key switching, modulus switching, and for BFV the products and the plaintext
additions), any two outputs meeting the contract have the same phase at the destination's level
and key, and leave every other variable as it was: the contract determines the result up to the
choice of representative ciphertext, so a wrong phase violates it.
-/

namespace Challenge.Sanity
open Spec NPoly Scheme Source Correct

/-- **BGV: the exact contracts determine the phase.** -/
theorem stepOK_exact_phase (P : FullParams) (E : Trace.Budget) (s : IntPoly P.src.N)
    (ρ ρ' : Env P.src) (σ σ₁ σ₂ : Trace.CtEnv P) (i : Instr)
    (hex : ∀ d a, i ≠ .relin d a ∧ i ≠ .keySwitch d a ∧ i ≠ .modSwitch d a)
    (h₁ : Trace.StepOK P E s ρ ρ' σ σ₁ i) (h₂ : Trace.StepOK P E s ρ ρ' σ σ₂ i) :
    ∃ v ct₁ ct₂, ρ' (Trace.dst i) = some v ∧ σ₁ = σ.set (Trace.dst i) ct₁ ∧
      σ₂ = σ.set (Trace.dst i) ct₂ ∧
      Trace.phaseAt P (P.src.modulus v.level) v.key s ct₁ =
        Trace.phaseAt P (P.src.modulus v.level) v.key s ct₂ := sorry

/-- **BFV: the exact contracts determine the phase** (the products, the plaintext additions,
key switching and modulus switching excluded). -/
theorem stepOK_exact_phase_bfv (P : FullParams) (E : TraceBFV.Budget) (s : IntPoly P.src.N)
    (ρ ρ' : Env P.src) (σ σ₁ σ₂ : Trace.CtEnv P) (i : Instr)
    (hex : ∀ d a b, i ≠ .relin d a ∧ i ≠ .keySwitch d a ∧ i ≠ .modSwitch d a ∧
      i ≠ .mul d a b ∧ i ≠ .square d a ∧ i ≠ .addPlain d a b ∧ i ≠ .subPlain d a b)
    (h₁ : TraceBFV.StepOK P E s ρ ρ' σ σ₁ i) (h₂ : TraceBFV.StepOK P E s ρ ρ' σ σ₂ i) :
    ∃ v ct₁ ct₂, ρ' (Trace.dst i) = some v ∧ σ₁ = σ.set (Trace.dst i) ct₁ ∧
      σ₂ = σ.set (Trace.dst i) ct₂ ∧
      Trace.phaseAt P (P.src.modulus v.level) v.key s ct₁ =
        Trace.phaseAt P (P.src.modulus v.level) v.key s ct₂ := sorry

end Challenge.Sanity
