import Challenge.Sanity.Contracts

/-!
# Validation.Sanity.Contracts — proofs of the pins of `Challenge.Sanity.Contracts`

Case analysis on the instruction: in each exact clause the operands are read from the same
environments, so the two right-hand sides are the same term.
-/

namespace Validation.Sanity
open Spec NPoly Scheme Source Correct

theorem stepOK_exact_phase (P : FullParams) (E : Trace.Budget) (s : IntPoly P.src.N)
    (ρ ρ' : Env P.src) (σ σ₁ σ₂ : Trace.CtEnv P) (i : Instr)
    (hex : ∀ d a, i ≠ .relin d a ∧ i ≠ .keySwitch d a ∧ i ≠ .modSwitch d a)
    (h₁ : Trace.StepOK P E s ρ ρ' σ σ₁ i) (h₂ : Trace.StepOK P E s ρ ρ' σ σ₂ i) :
    ∃ v ct₁ ct₂, ρ' (Trace.dst i) = some v ∧ σ₁ = σ.set (Trace.dst i) ct₁ ∧
      σ₂ = σ.set (Trace.dst i) ct₂ ∧
      Trace.phaseAt P (P.src.modulus v.level) v.key s ct₁ =
        Trace.phaseAt P (P.src.modulus v.level) v.key s ct₂ := by
  obtain ⟨v, c1, hv1, -, hs1, h1⟩ := h₁
  obtain ⟨v2, c2, hv2, -, hs2, h2⟩ := h₂
  rw [hv1] at hv2; obtain rfl := Option.some.inj hv2
  refine ⟨v, c1, c2, hv1, hs1, hs2, ?_⟩
  cases i
  case relin d a => exact absurd rfl (hex d a).1
  case keySwitch d a => exact absurd rfl (hex d a).2.1
  case modSwitch d a => exact absurd rfl (hex d a).2.2
  all_goals dsimp only at h1 h2
  all_goals first
    | (obtain ⟨x, y, ca, cb, hx, hy, ha, hb, e1⟩ := h1
       obtain ⟨x', y', ca', cb', hx', hy', ha', hb', e2⟩ := h2
       rw [hx] at hx'; rw [hy] at hy'; rw [ha] at ha'; rw [hb] at hb'
       obtain rfl := Option.some.inj hx'; obtain rfl := Option.some.inj hy'
       obtain rfl := Option.some.inj ha'; obtain rfl := Option.some.inj hb'
       rw [e1, e2])
    | (obtain ⟨x, ca, hx, ha, e1⟩ := h1
       obtain ⟨x', ca', hx', ha', e2⟩ := h2
       rw [hx] at hx'; rw [ha] at ha'
       obtain rfl := Option.some.inj hx'; obtain rfl := Option.some.inj ha'
       rw [e1, e2])

theorem stepOK_exact_phase_bfv (P : FullParams) (E : TraceBFV.Budget) (s : IntPoly P.src.N)
    (ρ ρ' : Env P.src) (σ σ₁ σ₂ : Trace.CtEnv P) (i : Instr)
    (hex : ∀ d a b, i ≠ .relin d a ∧ i ≠ .keySwitch d a ∧ i ≠ .modSwitch d a ∧
      i ≠ .mul d a b ∧ i ≠ .square d a ∧ i ≠ .addPlain d a b ∧ i ≠ .subPlain d a b)
    (h₁ : TraceBFV.StepOK P E s ρ ρ' σ σ₁ i) (h₂ : TraceBFV.StepOK P E s ρ ρ' σ σ₂ i) :
    ∃ v ct₁ ct₂, ρ' (Trace.dst i) = some v ∧ σ₁ = σ.set (Trace.dst i) ct₁ ∧
      σ₂ = σ.set (Trace.dst i) ct₂ ∧
      Trace.phaseAt P (P.src.modulus v.level) v.key s ct₁ =
        Trace.phaseAt P (P.src.modulus v.level) v.key s ct₂ := by
  obtain ⟨v, c1, hv1, -, hs1, h1⟩ := h₁
  obtain ⟨v2, c2, hv2, -, hs2, h2⟩ := h₂
  rw [hv1] at hv2; obtain rfl := Option.some.inj hv2
  refine ⟨v, c1, c2, hv1, hs1, hs2, ?_⟩
  cases i
  case relin d a => exact absurd rfl (hex d a a).1
  case keySwitch d a => exact absurd rfl (hex d a a).2.1
  case modSwitch d a => exact absurd rfl (hex d a a).2.2.1
  case mul d a b => exact absurd rfl (hex d a b).2.2.2.1
  case square d a => exact absurd rfl (hex d a a).2.2.2.2.1
  case addPlain d a b => exact absurd rfl (hex d a b).2.2.2.2.2.1
  case subPlain d a b => exact absurd rfl (hex d a b).2.2.2.2.2.2
  case dropLimbs => exact h1.elim
  all_goals dsimp only at h1 h2
  all_goals first
    | (obtain ⟨x, y, ca, cb, hx, hy, ha, hb, e1⟩ := h1
       obtain ⟨x', y', ca', cb', hx', hy', ha', hb', e2⟩ := h2
       rw [hx] at hx'; rw [hy] at hy'; rw [ha] at ha'; rw [hb] at hb'
       obtain rfl := Option.some.inj hx'; obtain rfl := Option.some.inj hy'
       obtain rfl := Option.some.inj ha'; obtain rfl := Option.some.inj hb'
       rw [e1, e2])
    | (obtain ⟨x, ca, hx, ha, e1⟩ := h1
       obtain ⟨x', ca', hx', ha', e2⟩ := h2
       rw [hx] at hx'; rw [ha] at ha'
       obtain rfl := Option.some.inj hx'; obtain rfl := Option.some.inj ha'
       rw [e1, e2])

example := (@stepOK_exact_phase : type_of% @Challenge.Sanity.stepOK_exact_phase)
example := (@stepOK_exact_phase_bfv : type_of% @Challenge.Sanity.stepOK_exact_phase_bfv)

end Validation.Sanity
