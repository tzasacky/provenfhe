import Challenge.Budget
import FHE.KeySwitch.Layout

/-!
# Validation.Budget.KeySwitch — `relin` and `keySwitch` are realizable within `ksBoundAt`

Proofs of the pins `Challenge.Budget.relin_realizable` and `Challenge.Budget.keySwitch_realizable`.
The function is RNS hybrid key switching on the digits of the layout
(`FHE.KeySwitch.layoutKS`: centred representatives, or the OpenFHE canonical variant when
`lay.canonical`); `FHE.KeySwitch.layoutKS_spec` is its contract under `SchemeParamsOK` and
`SpecialOK`.
-/

namespace Validation.Budget
open Spec NPoly Scheme Source Correct Spec.Budget Challenge.Headline

/-- **Relinearization within `ksBoundAt`.** -/
theorem relin_realizable (P : FullParams) (lay : KSLayout) (hk : P.src.kind = .bgv)
    (hP : SchemeParamsOK P) (hS : SpecialOK P) (ℓ : ℕ) (h1 : 1 ≤ ℓ) (hℓ : ℓ ≤ P.src.qs.length)
    (hlay : lay.okAt ℓ = true) :
    ∃ f : List (IntPoly P.src.N) → List (IntPoly P.src.N × IntPoly P.src.N) →
        List (IntPoly P.src.N),
      ∀ (E : Trace.Budget), ksBoundAt P lay ℓ ≤ E.keySwitch →
      ∀ (s : IntPoly P.src.N), SecretOK P.secretBound s →
      ∀ (keys : List (IntPoly P.src.N × IntPoly P.src.N)), GadgetKeysOK P lay ℓ .square s keys →
      ∀ (ρ ρ' : Env P.src) (σ : Trace.CtEnv P) (d a : Var) (x : Val P.src)
        (ca : List (IntPoly P.src.N)),
        step P.src ρ (.relin d a) = some ρ' → ρ a = some x → σ a = some ca → x.level = ℓ →
        ca.length = x.parts →
        Trace.StepOK P E s ρ ρ' σ (σ.set d (f ca keys)) (.relin d a) := by
  have : NeZero P.src.N := ⟨by obtain ⟨k, hk'⟩ := hP.N_pow2; rw [hk']; positivity⟩
  refine ⟨fun ca keys => match ca with
    | [c0, c1, c2] =>
      [c0 + (FHE.KeySwitch.layoutKS P hP hS lay ℓ hℓ hlay c2 keys).1,
       c1 + (FHE.KeySwitch.layoutKS P hP hS lay ℓ hℓ hlay c2 keys).2]
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
  obtain ⟨e, he, hdvd, hb⟩ :=
    FHE.KeySwitch.layoutKS_spec P hP hS hk lay _ hℓ hlay s hs .square keys hkeys c2
  refine ⟨{ x with parts := 2 },
    [c0 + (FHE.KeySwitch.layoutKS P hP hS lay x.level hℓ hlay c2 keys).1,
     c1 + (FHE.KeySwitch.layoutKS P hP hS lay x.level hℓ hlay c2 keys).2], ?_, rfl, rfl, ?_⟩
  · simp [Env.set, Trace.dst, hg.2]
  refine ⟨x, [c0, c1, c2], e, hx, hca, hb.trans hE, hdvd, ?_⟩
  simp only [Trace.phaseAt, hg.2, FHE.KeySwitch.automorph_one, List.map, phase,
    Validation.Scheme.ofInt_add, KeyTarget.eval] at he ⊢
  rw [Validation.Scheme.ofInt_mul] at he
  linear_combination he

/-- **Key switching within `ksBoundAt`.** The operand is under `σ_g(s)`, `g` its recorded key;
the keys are valid for the target `σ_g(s)`. The function is fixed before `g` is. -/
theorem keySwitch_realizable (P : FullParams) (lay : KSLayout) (hk : P.src.kind = .bgv)
    (hP : SchemeParamsOK P) (hS : SpecialOK P) (ℓ : ℕ) (h1 : 1 ≤ ℓ) (hℓ : ℓ ≤ P.src.qs.length)
    (hlay : lay.okAt ℓ = true) :
    ∃ f : List (IntPoly P.src.N) → List (IntPoly P.src.N × IntPoly P.src.N) →
        List (IntPoly P.src.N),
      ∀ (E : Trace.Budget), ksBoundAt P lay ℓ ≤ E.keySwitch →
      ∀ (s : IntPoly P.src.N), SecretOK P.secretBound s →
      ∀ (ρ ρ' : Env P.src) (σ : Trace.CtEnv P) (d a : Var) (x : Val P.src)
        (ca : List (IntPoly P.src.N)),
        step P.src ρ (.keySwitch d a) = some ρ' → ρ a = some x → σ a = some ca → x.level = ℓ →
        ca.length = x.parts →
      ∀ (keys : List (IntPoly P.src.N × IntPoly P.src.N)),
        GadgetKeysOK P lay ℓ (.galois x.key) s keys →
        Trace.StepOK P E s ρ ρ' σ (σ.set d (f ca keys)) (.keySwitch d a) := by
  have : NeZero P.src.N := ⟨by obtain ⟨k, hk'⟩ := hP.N_pow2; rw [hk']; positivity⟩
  refine ⟨fun ca keys => match ca with
    | [c0, c1] =>
      [c0 + (FHE.KeySwitch.layoutKS P hP hS lay ℓ hℓ hlay c1 keys).1,
       (FHE.KeySwitch.layoutKS P hP hS lay ℓ hℓ hlay c1 keys).2]
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
  obtain ⟨e, he, hdvd, hb⟩ :=
    FHE.KeySwitch.layoutKS_spec P hP hS hk lay _ hℓ hlay s hs (.galois x.key) keys hkeys c1
  refine ⟨{ x with key := 1 },
    [c0 + (FHE.KeySwitch.layoutKS P hP hS lay x.level hℓ hlay c1 keys).1,
     (FHE.KeySwitch.layoutKS P hP hS lay x.level hℓ hlay c1 keys).2], ?_, ?_, rfl, ?_⟩
  · simp [Env.set, Trace.dst, hg]
  · simp [hg]
  refine ⟨x, [c0, c1], e, hx, hca, hb.trans hE, hdvd, ?_⟩
  simp only [Trace.phaseAt, FHE.KeySwitch.automorph_one, List.map, phase,
    Validation.Scheme.ofInt_add, KeyTarget.eval] at he ⊢
  linear_combination he

end Validation.Budget
