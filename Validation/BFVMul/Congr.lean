import Spec.TraceBFV

/-!
# Validation.BFVMul.Congr — a BFV step contract reads the stored ciphertext modulo `Q` only

`Spec.TraceBFV.StepOK` constrains the ciphertext a step stores through its phase modulo the
modulus `Q` of the result's level, and through its number of components. So two candidate results
whose components agree modulo `Q` meet the same contracts (`stepOK_congr`, for every
instruction; `stepOK_mul_congr` and `stepOK_square_congr` are the instances used to transfer the
contract from the textbook multiplication to an RNS variant that computes the same residues).
-/

namespace Validation.BFVMul
open Spec NPoly Scheme Source Correct

variable {P : FullParams}

theorem ctEnv_set_inj (σ : Trace.CtEnv P) (d : Var) (c c' : List (IntPoly P.src.N))
    (h : σ.set d c = σ.set d c') : c = c' := by
  have := congrFun h d
  simpa [Trace.CtEnv.set] using this

/-- The phase modulo `Q` depends on the components modulo `Q` only. -/
theorem phaseAt_congr (Q key : ℕ) (s : IntPoly P.src.N) (ct ct' : List (IntPoly P.src.N))
    (h : ct.map (ofInt Q) = ct'.map (ofInt Q)) :
    Trace.phaseAt P Q key s ct = Trace.phaseAt P Q key s ct' := by
  unfold Trace.phaseAt
  rw [h]

/-- **A step contract depends on the stored ciphertext only through its components modulo the
modulus of the result's level.** Every instruction. -/
theorem stepOK_congr (E : TraceBFV.Budget) (s : IntPoly P.src.N) (ρ ρ' : Env P.src)
    (σ : Trace.CtEnv P) (i : Instr) (ct ct' : List (IntPoly P.src.N))
    (h : ∀ v, ρ' (Trace.dst i) = some v →
      ct.map (ofInt (P.src.modulus v.level)) = ct'.map (ofInt (P.src.modulus v.level)))
    (H : TraceBFV.StepOK P E s ρ ρ' σ (σ.set (Trace.dst i) ct) i) :
    TraceBFV.StepOK P E s ρ ρ' σ (σ.set (Trace.dst i) ct') i := by
  obtain ⟨v, ct0, hv, hlen, hσ, body⟩ := H
  have h0 := ctEnv_set_inj _ _ _ _ hσ
  subst h0
  refine ⟨v, ct', hv, ?_, rfl, ?_⟩
  · rw [← hlen]
    have := congrArg List.length (h v hv)
    simpa using this.symm
  · have hp := phaseAt_congr (P := P) (P.src.modulus v.level) v.key s _ _ (h v hv)
    dsimp only at body ⊢
    rw [← hp]
    exact body

/-- `stepOK_congr` for `mul`: if `ct` meets the `mul` contract and `ct'` has the same components
modulo the modulus of the result's level, `ct'` meets it. -/
theorem stepOK_mul_congr (E : TraceBFV.Budget) (s : IntPoly P.src.N) (ρ ρ' : Env P.src)
    (σ : Trace.CtEnv P) (d a b : Var) (ct ct' : List (IntPoly P.src.N))
    (h : ∀ v, ρ' d = some v →
      ct.map (ofInt (P.src.modulus v.level)) = ct'.map (ofInt (P.src.modulus v.level)))
    (H : TraceBFV.StepOK P E s ρ ρ' σ (σ.set d ct) (.mul d a b)) :
    TraceBFV.StepOK P E s ρ ρ' σ (σ.set d ct') (.mul d a b) :=
  stepOK_congr E s ρ ρ' σ (.mul d a b) ct ct' h H

/-- `stepOK_congr` for `square`. -/
theorem stepOK_square_congr (E : TraceBFV.Budget) (s : IntPoly P.src.N) (ρ ρ' : Env P.src)
    (σ : Trace.CtEnv P) (d a : Var) (ct ct' : List (IntPoly P.src.N))
    (h : ∀ v, ρ' d = some v →
      ct.map (ofInt (P.src.modulus v.level)) = ct'.map (ofInt (P.src.modulus v.level)))
    (H : TraceBFV.StepOK P E s ρ ρ' σ (σ.set d ct) (.square d a)) :
    TraceBFV.StepOK P E s ρ ρ' σ (σ.set d ct') (.square d a) :=
  stepOK_congr E s ρ ρ' σ (.square d a) ct ct' h H

end Validation.BFVMul
