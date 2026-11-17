import Challenge.BFV
import FHE.BFV.KeySwitch

/-!
# Validation.BFV.KeySwitch — BFV `relin` and `keySwitch` are realizable within `BudgetBFV.ksBoundAt`

Proofs of the pins `Challenge.BFV.relin_realizable` and `Challenge.BFV.keySwitch_realizable`.
The function is plain RNS hybrid key switching on the digits of the layout
(`FHE.BFV.layoutKSPlain`: centred representatives, plain rounding in ModDown);
`FHE.BFV.layoutKSPlain_spec` is its contract under `SchemeParamsOK` and `SpecialOK`.
-/

namespace Validation.BFV
open Spec NPoly Scheme Source Correct

/-- **Relinearization within `BudgetBFV.ksBoundAt`.** -/
theorem relin_realizable (P : FullParams) (lay : Budget.KSLayout)
    (hP : SchemeParamsOK P) (hS : Budget.SpecialOK P) (ℓ : ℕ)
    (hℓ : ℓ ≤ P.src.qs.length) (hlay : lay.okAt ℓ = true) :
    ∃ f : List (IntPoly P.src.N) → List (IntPoly P.src.N × IntPoly P.src.N) →
        List (IntPoly P.src.N),
      ∀ (E : TraceBFV.Budget), BudgetBFV.ksBoundAt P lay ℓ ≤ E.keySwitch →
      ∀ (s : IntPoly P.src.N), SecretOK P.secretBound s →
      ∀ (keys : List (IntPoly P.src.N × IntPoly P.src.N)),
        Budget.GadgetKeysOK P lay ℓ .square s keys →
      ∀ (ρ ρ' : Env P.src) (σ : Trace.CtEnv P) (d a : Var) (x : Val P.src)
        (ca : List (IntPoly P.src.N)),
        step P.src ρ (.relin d a) = some ρ' → ρ a = some x → σ a = some ca → x.level = ℓ →
        ca.length = x.parts →
        TraceBFV.StepOK P E s ρ ρ' σ (σ.set d (f ca keys)) (.relin d a) := by
  have : NeZero P.src.N := ⟨by obtain ⟨k, hk'⟩ := hP.N_pow2; rw [hk']; positivity⟩
  refine ⟨fun ca keys => match ca with
    | [c0, c1, c2] =>
      [c0 + (FHE.BFV.layoutKSPlain P hP hS lay ℓ hℓ hlay c2 keys).1,
       c1 + (FHE.BFV.layoutKSPlain P hP hS lay ℓ hℓ hlay c2 keys).2]
    | _ => [], ?_⟩
  intro E hE s hs keys hkeys ρ ρ' σ d a x ca hstep hx hca hl hlen
  simp only [step, hx, guard] at hstep
  by_cases hg : x.parts = 3 ∧ x.key = 1
  swap
  · simp [hg] at hstep
  simp [hg] at hstep
  subst hstep
  rw [hg.1] at hlen
  obtain ⟨c0, c1, c2, rfl⟩ : ∃ c0 c1 c2, ca = [c0, c1, c2] := by
    match ca, hlen with
    | [c0, c1, c2], _ => exact ⟨_, _, _, rfl⟩
  subst hl
  obtain ⟨e, he, hb⟩ :=
    FHE.BFV.layoutKSPlain_spec P hP hS lay _ hℓ hlay s hs .square keys hkeys c2
  refine ⟨{ x with parts := 2 },
    [c0 + (FHE.BFV.layoutKSPlain P hP hS lay x.level hℓ hlay c2 keys).1,
     c1 + (FHE.BFV.layoutKSPlain P hP hS lay x.level hℓ hlay c2 keys).2], ?_, rfl, rfl, ?_⟩
  · simp [Env.set, Trace.dst, hg.2]
  refine ⟨x, [c0, c1, c2], e, hx, hca, hb.trans hE, ?_⟩
  simp only [Trace.phaseAt, hg.2, FHE.KeySwitch.automorph_one, List.map, phase,
    Validation.Scheme.ofInt_add, KeyTarget.eval] at he ⊢
  rw [Validation.Scheme.ofInt_mul] at he
  linear_combination he

/-- **Key switching within `BudgetBFV.ksBoundAt`.** The operand is under `σ_g(s)`, `g` its
recorded key; the keys are valid for the target `σ_g(s)`. The function is fixed before `g` is. -/
theorem keySwitch_realizable (P : FullParams) (lay : Budget.KSLayout)
    (hP : SchemeParamsOK P) (hS : Budget.SpecialOK P) (ℓ : ℕ)
    (hℓ : ℓ ≤ P.src.qs.length) (hlay : lay.okAt ℓ = true) :
    ∃ f : List (IntPoly P.src.N) → List (IntPoly P.src.N × IntPoly P.src.N) →
        List (IntPoly P.src.N),
      ∀ (E : TraceBFV.Budget), BudgetBFV.ksBoundAt P lay ℓ ≤ E.keySwitch →
      ∀ (s : IntPoly P.src.N), SecretOK P.secretBound s →
      ∀ (ρ ρ' : Env P.src) (σ : Trace.CtEnv P) (d a : Var) (x : Val P.src)
        (ca : List (IntPoly P.src.N)),
        step P.src ρ (.keySwitch d a) = some ρ' → ρ a = some x → σ a = some ca → x.level = ℓ →
        ca.length = x.parts →
      ∀ (keys : List (IntPoly P.src.N × IntPoly P.src.N)),
        Budget.GadgetKeysOK P lay ℓ (.galois x.key) s keys →
        TraceBFV.StepOK P E s ρ ρ' σ (σ.set d (f ca keys)) (.keySwitch d a) := by
  have : NeZero P.src.N := ⟨by obtain ⟨k, hk'⟩ := hP.N_pow2; rw [hk']; positivity⟩
  refine ⟨fun ca keys => match ca with
    | [c0, c1] =>
      [c0 + (FHE.BFV.layoutKSPlain P hP hS lay ℓ hℓ hlay c1 keys).1,
       (FHE.BFV.layoutKSPlain P hP hS lay ℓ hℓ hlay c1 keys).2]
    | _ => [], ?_⟩
  intro E hE s hs ρ ρ' σ d a x ca hstep hx hca hl hlen keys hkeys
  simp only [step, hx, guard] at hstep
  by_cases hg : x.parts = 2
  swap
  · simp [hg] at hstep
  simp [hg] at hstep
  subst hstep
  rw [hg] at hlen
  obtain ⟨c0, c1, rfl⟩ : ∃ c0 c1, ca = [c0, c1] := by
    match ca, hlen with
    | [c0, c1], _ => exact ⟨_, _, rfl⟩
  subst hl
  obtain ⟨e, he, hb⟩ :=
    FHE.BFV.layoutKSPlain_spec P hP hS lay _ hℓ hlay s hs (.galois x.key) keys hkeys c1
  refine ⟨{ x with key := 1 },
    [c0 + (FHE.BFV.layoutKSPlain P hP hS lay x.level hℓ hlay c1 keys).1,
     (FHE.BFV.layoutKSPlain P hP hS lay x.level hℓ hlay c1 keys).2], ?_, ?_, rfl, ?_⟩
  · simp [Env.set, Trace.dst, hg]
  · simp [hg]
  refine ⟨x, [c0, c1], e, hx, hca, hb.trans hE, ?_⟩
  simp only [Trace.phaseAt, FHE.KeySwitch.automorph_one, List.map, phase,
    Validation.Scheme.ofInt_add, KeyTarget.eval] at he ⊢
  linear_combination he

example := (@relin_realizable : type_of% @Challenge.BFV.relin_realizable)
example := (@keySwitch_realizable : type_of% @Challenge.BFV.keySwitch_realizable)

end Validation.BFV
