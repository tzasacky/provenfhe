import Challenge.Instances.Lattigo
import Validation.Profile
import Validation.Budget.Restrict

/-!
# Validation.Instances.Lattigo — proofs of the pins of `Challenge.Instances.Lattigo`

The coverage and acceptance facts are closed computations, checked by the kernel. The
achievability corollaries read `instanceOK?` through a definitional `have` (no locked definition is unfolded by
name) and instantiate `Validation.Budget.relin_realizable_top`, `keySwitch_realizable_top` and
`modSwitch_realizable_parts` at the Lattigo profile, through `Validation.Profile.coversBGV?_facts`.
-/

namespace Validation.Instances.Lattigo
open Spec NPoly Scheme Source Correct Challenge.Profile Challenge.Instances.Lattigo

/-! ## 1. Coverage -/

theorem small_instanceOK : instanceOK? small = true := by
  decide +kernel

theorem exampleLogN14_instanceOK : instanceOK? exampleLogN14 = true := by
  decide +kernel

/-! ## 2. Achievability -/

/-- What `instanceOK?` gives: the coverage facts and the key-size condition. -/
theorem instanceOK?_facts {P : FullParams} (h : instanceOK? P = true) :
    coversBGV? P (layout P) maxParts (profile P) = true ∧ Certify.keysRestrict? P = true := by
  have h' : (coversBGV? P (layout P) maxParts (profile P) && Certify.keysRestrict? P) = true := h
  simpa only [Bool.and_eq_true] using h'

/-- The layout of `layout P` restricts from the top level to every level. -/
theorem layout_restricts (P : FullParams) (ℓ : ℕ) (h1 : 1 ≤ ℓ) (hℓ : ℓ ≤ P.src.qs.length) :
    Budget.restrictsTo (layout P) P.src.qs.length ℓ = true := by
  have hu : layout P = Budget.uniformLayout (max 1 P.store.special.length) := rfl
  rw [hu]
  exact Validation.Budget.layoutOK?_restricts P _
    (Validation.Budget.layoutOK?_uniform P _ false) ℓ h1 hℓ

theorem relin_meets (P : FullParams) (h : instanceOK? P = true) (ℓ : ℕ) (h1 : 1 ≤ ℓ)
    (hℓ : ℓ ≤ P.src.qs.length) :
    ∃ f : List (IntPoly P.src.N) → List (IntPoly P.src.N × IntPoly P.src.N) →
        List (IntPoly P.src.N),
      ∀ (s : IntPoly P.src.N), SecretOK P.secretBound s →
      ∀ (keys : List (IntPoly P.src.N × IntPoly P.src.N)),
        Budget.GadgetKeysOK P (layout P) P.src.qs.length .square s keys →
      ∀ (ρ ρ' : Env P.src) (σ : Trace.CtEnv P) (d a : Var) (x : Val P.src)
        (ca : List (IntPoly P.src.N)),
        step P.src ρ (.relin d a) = some ρ' → ρ a = some x → σ a = some ca → x.level = ℓ →
        ca.length = x.parts →
        Trace.StepOK P (profile P) s ρ ρ' σ
          (σ.set d (f ca (keys.take ((layout P).sizes ℓ).length))) (.relin d a) := by
  obtain ⟨hc, hr⟩ := instanceOK?_facts h
  obtain ⟨hP, hk, hS, hl, -⟩ := Validation.Profile.coversBGV?_facts hc
  obtain ⟨-, hb⟩ := hl ℓ h1 hℓ
  obtain ⟨f, hf⟩ := Validation.Budget.relin_realizable_top P (layout P) hk hP hS ℓ h1 hℓ
    (layout_restricts P ℓ h1 hℓ) (Validation.Budget.keysRestrict?_level P hr hP ℓ h1 hℓ)
  exact ⟨f, hf (profile P) hb⟩

theorem keySwitch_meets (P : FullParams) (h : instanceOK? P = true) (ℓ : ℕ) (h1 : 1 ≤ ℓ)
    (hℓ : ℓ ≤ P.src.qs.length) :
    ∃ f : List (IntPoly P.src.N) → List (IntPoly P.src.N × IntPoly P.src.N) →
        List (IntPoly P.src.N),
      ∀ (s : IntPoly P.src.N), SecretOK P.secretBound s →
      ∀ (ρ ρ' : Env P.src) (σ : Trace.CtEnv P) (d a : Var) (x : Val P.src)
        (ca : List (IntPoly P.src.N)),
        step P.src ρ (.keySwitch d a) = some ρ' → ρ a = some x → σ a = some ca → x.level = ℓ →
        ca.length = x.parts →
      ∀ (keys : List (IntPoly P.src.N × IntPoly P.src.N)),
        Budget.GadgetKeysOK P (layout P) P.src.qs.length (.galois x.key) s keys →
        Trace.StepOK P (profile P) s ρ ρ' σ
          (σ.set d (f ca (keys.take ((layout P).sizes ℓ).length))) (.keySwitch d a) := by
  obtain ⟨hc, hr⟩ := instanceOK?_facts h
  obtain ⟨hP, hk, hS, hl, -⟩ := Validation.Profile.coversBGV?_facts hc
  obtain ⟨-, hb⟩ := hl ℓ h1 hℓ
  obtain ⟨f, hf⟩ := Validation.Budget.keySwitch_realizable_top P (layout P) hk hP hS ℓ h1 hℓ
    (layout_restricts P ℓ h1 hℓ) (Validation.Budget.keysRestrict?_level P hr hP ℓ h1 hℓ)
  exact ⟨f, hf (profile P) hb⟩

theorem modSwitch_meets (P : FullParams) (h : instanceOK? P = true) (ℓ k : ℕ) (hk1 : 1 ≤ k)
    (hk : k ≤ maxParts) :
    ∃ f : List (IntPoly P.src.N) → List (IntPoly P.src.N),
      ∀ (s : IntPoly P.src.N), SecretOK P.secretBound s →
      ∀ (ρ ρ' : Env P.src) (σ : Trace.CtEnv P) (d a : Var) (x : Val P.src)
        (ca : List (IntPoly P.src.N)),
        step P.src ρ (.modSwitch d a) = some ρ' → ρ a = some x → σ a = some ca → x.level = ℓ →
        x.parts = k → ca.length = k →
        Trace.StepOK P (profile P) s ρ ρ' σ (σ.set d (f ca)) (.modSwitch d a) :=
  Validation.Profile.coversBGV?_modSwitch P (layout P) maxParts (profile P)
    (instanceOK?_facts h).1 ℓ k hk1 hk

/-! ## 3. Certificates at the profile -/

theorem exampleLogN14_accepts :
    (certifyProfile? exampleLogN14 (profile exampleLogN14) (chain 12 4) false).isSome = true ∧
      certifyProfile? exampleLogN14 (profile exampleLogN14) (chain 12 5) false = none := by
  decide +kernel

theorem small_accepts :
    (certifyProfile? small (profile small) (chain 4 3) false).isSome = true ∧
      (certifyProfile? small (profile small) smallProg false).isSome = true := by
  decide +kernel

example := (@small_instanceOK : type_of% @Challenge.Instances.Lattigo.small_instanceOK)
example := (@exampleLogN14_instanceOK :
  type_of% @Challenge.Instances.Lattigo.exampleLogN14_instanceOK)
example := (@relin_meets : type_of% @Challenge.Instances.Lattigo.relin_meets)
example := (@keySwitch_meets : type_of% @Challenge.Instances.Lattigo.keySwitch_meets)
example := (@modSwitch_meets : type_of% @Challenge.Instances.Lattigo.modSwitch_meets)
example := (@exampleLogN14_accepts : type_of% @Challenge.Instances.Lattigo.exampleLogN14_accepts)
example := (@small_accepts : type_of% @Challenge.Instances.Lattigo.small_accepts)

end Validation.Instances.Lattigo
