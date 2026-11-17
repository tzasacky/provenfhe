import Challenge.Realize
import FHE.Realize.KeySwitch
import FHE.Realize.Harness
import FHE.KeySwitch.Order
import Validation.Certify

/-!
# Validation.Realize — proofs of `Challenge.Realize`

The transcription of `Challenge.Realize.OpenFHE` is the library's OpenFHE key switching
(`FHE.Realize.KeySwitch.ksOpenFHE_ofInt`: at the `Spec` modulus it is `FHE.KeySwitch.layoutKS`
with canonical representatives), so the contract follows from `FHE.KeySwitch.layoutKS_spec`, as in
`Validation.Budget.KeySwitch`. The rotation: `FHE.Realize.rotateOpenFHE161_spec` (`FHE/Realize/Harness.lean`).
-/

namespace Validation.Realize
open Spec NPoly Scheme Source Correct Spec.Budget Spec.Certify Challenge.Certify Challenge.Realize

/-! ## Helpers -/

/-- `innerKey` depends on the key components of the digits of the level only. -/
theorem innerKey_congr (P : FullParams) (lay : KSLayout) (ℓ : ℕ) (d : IntPoly P.src.N)
    (k k' : ℕ → IntPoly P.src.N) (h : ∀ j : Fin (lay.sizes ℓ).length, k j = k' j) :
    innerKey P lay ℓ d k = innerKey P lay ℓ d k' := by
  unfold innerKey
  congr 2
  funext j
  rw [h j]

theorem getD_take {N : ℕ} (keys : List (IntPoly N × IntPoly N)) (n : ℕ) (j : Fin n) :
    (keys.take n).getD j (0, 0) = keys.getD j (0, 0) := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_take, j.isLt]

/-- The transcription reads only the keys of the digits of the level. -/
theorem ksOpenFHE_take (P : FullParams) (lay : KSLayout) (ℓ : ℕ) (d : IntPoly P.src.N)
    (keys : List (IntPoly P.src.N × IntPoly P.src.N)) :
    ksOpenFHE P lay ℓ d (keys.take (lay.sizes ℓ).length) = ksOpenFHE P lay ℓ d keys := by
  unfold ksOpenFHE
  congr 2
  · exact innerKey_congr P lay ℓ d _ _ fun j => by rw [getD_take]
  · exact innerKey_congr P lay ℓ d _ _ fun j => by rw [getD_take]

theorem relinOpenFHE_take (P : FullParams) (lay : KSLayout) (ℓ : ℕ) (ca : List (IntPoly P.src.N))
    (keys : List (IntPoly P.src.N × IntPoly P.src.N)) :
    relinOpenFHE P lay ℓ ca (keys.take (lay.sizes ℓ).length) = relinOpenFHE P lay ℓ ca keys := by
  rcases ca with _ | ⟨c0, _ | ⟨c1, _ | ⟨c2, _ | ⟨c3, rest⟩⟩⟩⟩
  · rfl
  · rfl
  · rfl
  · show [_, _] = [_, _]
    rw [ksOpenFHE_take]
  · rfl

theorem keySwitchOpenFHE_take (P : FullParams) (lay : KSLayout) (ℓ : ℕ)
    (ca : List (IntPoly P.src.N)) (keys : List (IntPoly P.src.N × IntPoly P.src.N)) :
    keySwitchOpenFHE P lay ℓ ca (keys.take (lay.sizes ℓ).length) =
      keySwitchOpenFHE P lay ℓ ca keys := by
  rcases ca with _ | ⟨c0, _ | ⟨c1, _ | ⟨c2, rest⟩⟩⟩
  · rfl
  · rfl
  · show [_, _] = [_, _]
    rw [ksOpenFHE_take]
  · rfl

theorem neZero_N (P : FullParams) (hP : SchemeParamsOK P) : NeZero P.src.N :=
  ⟨by obtain ⟨k, hk'⟩ := hP.N_pow2; rw [hk']; positivity⟩

/-! ## At one level -/

theorem relinOpenFHE_stepOK (P : FullParams) (lay : KSLayout) (hk : P.src.kind = .bgv)
    (hP : SchemeParamsOK P) (hS : SpecialOK P) (hc : lay.canonical = true) (ℓ : ℕ)
    (hℓ : ℓ ≤ P.src.qs.length) (hlay : lay.okAt ℓ = true)
    (E : Trace.Budget) (hE : ksBoundAt P lay ℓ ≤ E.keySwitch)
    (s : IntPoly P.src.N) (hs : SecretOK P.secretBound s)
    (keys : List (IntPoly P.src.N × IntPoly P.src.N)) (hkeys : GadgetKeysOK P lay ℓ .square s keys)
    (ρ ρ' : Env P.src) (σ : Trace.CtEnv P) (d a : Var) (x : Val P.src)
    (ca : List (IntPoly P.src.N))
    (hstep : step P.src ρ (.relin d a) = some ρ') (hx : ρ a = some x) (hca : σ a = some ca)
    (hl : x.level = ℓ) (hlen : ca.length = x.parts) :
    Trace.StepOK P E s ρ ρ' σ (σ.set d (relinOpenFHE P lay ℓ ca keys)) (.relin d a) := by
  have := neZero_N P hP
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
    FHE.Realize.ksOpenFHE_spec P hP hS lay _ hℓ hlay hk hc s hs .square keys hkeys c2
  refine ⟨{ x with parts := 2 },
    [c0 + (ksOpenFHE P lay x.level c2 keys).1, c1 + (ksOpenFHE P lay x.level c2 keys).2], ?_, rfl,
    rfl, ?_⟩
  · simp [Env.set, Trace.dst, hg.2]
  refine ⟨x, [c0, c1, c2], e, hx, hca, hb.trans hE, hdvd, ?_⟩
  simp only [Trace.phaseAt, hg.2, FHE.KeySwitch.automorph_one, List.map, phase,
    Validation.Scheme.ofInt_add, KeyTarget.eval] at he ⊢
  rw [Validation.Scheme.ofInt_mul] at he
  linear_combination he

theorem keySwitchOpenFHE_stepOK (P : FullParams) (lay : KSLayout) (hk : P.src.kind = .bgv)
    (hP : SchemeParamsOK P) (hS : SpecialOK P) (hc : lay.canonical = true) (ℓ : ℕ)
    (hℓ : ℓ ≤ P.src.qs.length) (hlay : lay.okAt ℓ = true)
    (E : Trace.Budget) (hE : ksBoundAt P lay ℓ ≤ E.keySwitch)
    (s : IntPoly P.src.N) (hs : SecretOK P.secretBound s)
    (ρ ρ' : Env P.src) (σ : Trace.CtEnv P) (d a : Var) (x : Val P.src)
    (ca : List (IntPoly P.src.N))
    (hstep : step P.src ρ (.keySwitch d a) = some ρ') (hx : ρ a = some x) (hca : σ a = some ca)
    (hl : x.level = ℓ) (hlen : ca.length = x.parts)
    (keys : List (IntPoly P.src.N × IntPoly P.src.N))
    (hkeys : GadgetKeysOK P lay ℓ (.galois x.key) s keys) :
    Trace.StepOK P E s ρ ρ' σ (σ.set d (keySwitchOpenFHE P lay ℓ ca keys)) (.keySwitch d a) := by
  have := neZero_N P hP
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
    FHE.Realize.ksOpenFHE_spec P hP hS lay _ hℓ hlay hk hc s hs (.galois x.key) keys hkeys c1
  refine ⟨{ x with key := 1 },
    [c0 + (ksOpenFHE P lay x.level c1 keys).1, (ksOpenFHE P lay x.level c1 keys).2], ?_, ?_, rfl,
    ?_⟩
  · simp [Env.set, Trace.dst, hg]
  · simp [hg]
  refine ⟨x, [c0, c1], e, hx, hca, hb.trans hE, hdvd, ?_⟩
  simp only [Trace.phaseAt, FHE.KeySwitch.automorph_one, List.map, phase,
    Validation.Scheme.ofInt_add, KeyTarget.eval] at he ⊢
  linear_combination he

theorem rotKeySecret_exists (N : ℕ) (hN : ∃ k, N = 2 ^ k) (g : ℕ) (hg : g % 2 = 1)
    (s : IntPoly N) : ∃ s' : IntPoly N, automorph g s' = s ∧ normInf s' = normInf s := by
  obtain ⟨k, rfl⟩ := hN
  have h2 : 1 < 2 * 2 ^ k := by have := Nat.one_le_two_pow (n := k); omega
  have hcop : Nat.Coprime g (2 * 2 ^ k) := by
    rw [← pow_succ']
    exact Nat.Coprime.pow_right _ ((Nat.coprime_comm.mp (Nat.prime_two.coprime_iff_not_dvd.mpr
      (by omega))))
  obtain ⟨h, -, hh⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop h2
  have hodd : h % 2 = 1 := by
    have h' : g * h % 2 = 1 := by
      have := Nat.mod_mod_of_dvd (g * h) (dvd_mul_right 2 (2 ^ k))
      rw [← this, hh]
    rw [Nat.mul_mod, hg, one_mul, Nat.mod_mod] at h'
    exact h'
  refine ⟨automorph h s, ?_, ?_⟩
  · rw [Validation.Source.automorph_automorph hg, ← Validation.Source.automorph_mod,
      mul_comm h g, hh, FHE.KeySwitch.automorph_one]
  · have h1 := FHE.KeySwitch.normInf_automorph_le ⟨k, rfl⟩ hodd s
    have h3 : normInf s ≤ normInf (automorph h s) := by
      have e : automorph g (automorph h s) = s := by
        rw [Validation.Source.automorph_automorph hg, ← Validation.Source.automorph_mod,
          mul_comm h g, hh, FHE.KeySwitch.automorph_one]
      calc normInf s = normInf (automorph g (automorph h s)) := by rw [e]
        _ ≤ normInf (automorph h s) := FHE.KeySwitch.normInf_automorph_le ⟨k, rfl⟩ hg _
    exact le_antisymm h1 h3

/-- For odd `g` and `N` a power of two, `σ_g` has an inverse `σ_h` (`h` odd). -/
theorem exists_automorph_inv {N : ℕ} (hN : ∃ k, N = 2 ^ k) {g : ℕ} (hg : g % 2 = 1) :
    ∃ h, h % 2 = 1 ∧ ∀ a : IntPoly N, automorph h (automorph g a) = a := by
  obtain ⟨k, rfl⟩ := hN
  have h2 : 1 < 2 * 2 ^ k := by have := Nat.one_le_two_pow (n := k); omega
  have hcop : Nat.Coprime g (2 * 2 ^ k) := by
    rw [← pow_succ']
    exact Nat.Coprime.pow_right _ ((Nat.coprime_comm.mp (Nat.prime_two.coprime_iff_not_dvd.mpr
      (by omega))))
  obtain ⟨h, -, hh⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop h2
  have hodd : h % 2 = 1 := by
    have h' : g * h % 2 = 1 := by
      have := Nat.mod_mod_of_dvd (g * h) (dvd_mul_right 2 (2 ^ k))
      rw [← this, hh]
    rw [Nat.mul_mod, hg, one_mul, Nat.mod_mod] at h'
    exact h'
  refine ⟨h, hodd, fun a => ?_⟩
  rw [Validation.Source.automorph_automorph hodd, ← Validation.Source.automorph_mod, hh,
    FHE.KeySwitch.automorph_one]

/-- If `σ_g(s') = s` (odd `g`, `N` a power of two), then `‖s'‖∞ ≤ ‖s‖∞`. -/
theorem normInf_le_of_automorph_eq {N : ℕ} (hN : ∃ k, N = 2 ^ k) {g : ℕ} (hg : g % 2 = 1)
    {s s' : IntPoly N} (h : automorph g s' = s) : normInf s' ≤ normInf s := by
  obtain ⟨h', hodd, hinv⟩ := exists_automorph_inv hN hg
  calc normInf s' = normInf (automorph h' s) := by rw [← h, hinv]
    _ ≤ normInf s := FHE.KeySwitch.normInf_automorph_le hN hodd s

theorem rotateOpenFHE161_run (P : FullParams) (lay : KSLayout) (hk : P.src.kind = .bgv)
    (hP : SchemeParamsOK P) (hS : SpecialOK P) (hc : lay.canonical = true) (ℓ : ℕ)
    (hℓ : ℓ ≤ P.src.qs.length) (hlay : lay.okAt ℓ = true)
    (E : Trace.Budget) (hE : ksBoundAt P lay ℓ ≤ E.keySwitch)
    (s : IntPoly P.src.N) (hs : SecretOK P.secretBound s)
    (ρ : Env P.src) (σ : Trace.CtEnv P) (d m a : Var) (g : ℕ) (hg : g % 2 = 1) (x : Val P.src)
    (ca : List (IntPoly P.src.N)) (hx : ρ a = some x) (hca : σ a = some ca)
    (hl : x.level = ℓ) (hkey : x.key = 1) (hparts : x.parts = 2) (hlen : ca.length = 2)
    (s' : IntPoly P.src.N) (hs' : automorph g s' = s)
    (keys : List (IntPoly P.src.N × IntPoly P.src.N))
    (hkeys : GadgetKeysOK P lay ℓ (.galois g) s' keys) :
    Trace.Run P E s [.automorph m a g, .keySwitch d m] ρ σ
      ((σ.set m (ca.map (automorph g))).set d (rotateOpenFHE161 P lay ℓ g ca keys)) := by
  have := neZero_N P hP
  obtain ⟨c0, c1, rfl⟩ : ∃ c0 c1, ca = [c0, c1] := by
    match ca, hlen with
    | [c0, c1], _ => exact ⟨_, _, rfl⟩
  subst hl
  set v1 : Val P.src := { x with msg := x.msg.lift₁ (automorph g),
                                 key := (x.key * g) % (2 * P.src.N) } with hv1
  have hstep1 : step P.src ρ (.automorph m a g) = some (ρ.set m v1) := by
    simp [step, hx, hg, hv1]
  have hρ1 : (ρ.set m v1) m = some v1 := by simp [Env.set]
  have hstep2 : step P.src (ρ.set m v1) (.keySwitch d m) =
      some ((ρ.set m v1).set d { v1 with key := 1 }) := by
    have hp : v1.parts = 2 := hparts
    simp only [step, hρ1, guard, Option.bind_eq_bind, Option.bind_some, hp, ite_true]
    rfl
  have hσ1 : (σ.set m ([c0, c1].map (automorph g))) m = some ([c0, c1].map (automorph g)) := by
    simp [Trace.CtEnv.set]
  have hs'b : normInf s' ≤ P.secretBound := (normInf_le_of_automorph_eq hP.N_pow2 hg hs').trans hs
  obtain ⟨e, he, hdvd, hb⟩ := FHE.Realize.rotateOpenFHE161_spec P hP hS lay x.level hℓ hlay hk hc
    s' hs'b (.galois g) keys hkeys g hg c0 c1
  refine ⟨ρ.set m v1, σ.set m ([c0, c1].map (automorph g)), hstep1, ?_, ?_⟩
  · exact Validation.Trace.stepOK_automorph_textbook P E s ρ _ σ m a g x [c0, c1] hstep1 hx hca
      (by simp [hparts])
  refine ⟨_, _, hstep2, ?_, rfl⟩
  rw [FHE.Realize.rotateOpenFHE161_pair]
  refine ⟨{ v1 with key := 1 }, _, ?_, ?_, rfl, ?_⟩
  · simp [Env.set, Trace.dst]
  · simp [hv1, hparts]
  refine ⟨v1, [c0, c1].map (automorph g), e, hρ1, hσ1, hb.trans hE, hdvd, ?_⟩
  have hk1 : automorph v1.key s = automorph g s := by
    rw [hv1]; dsimp only; rw [hkey, one_mul, Validation.Source.automorph_mod]
  simp only [KeyTarget.eval, hs'] at he
  simp only [Trace.phaseAt, FHE.KeySwitch.automorph_one, List.map, phase, hk1]
  linear_combination he

/-! ## At the budget of a certificate -/

theorem certified_ksBoundAt (x : Input) (c : Certificate) (h : certify? x = some c) (ℓ : ℕ)
    (h1 : 1 ≤ ℓ) (hL : ℓ ≤ c.params.src.qs.length) :
    ksBoundAt c.params x.lay ℓ ≤ c.budget.keySwitch := by
  rw [(Validation.Certify.certify?_spec x c h).1]
  exact Validation.Budget.ksBoundAt_le_ksBudget c.params x.lay ℓ h1 hL

theorem certify?_relinOpenFHE (x : Input) (c : Certificate) (h : certify? x = some c)
    (hc : x.lay.canonical = true)
    (s : IntPoly c.params.src.N) (hs : SecretOK c.params.secretBound s)
    (keys : List (IntPoly c.params.src.N × IntPoly c.params.src.N))
    (hkeys : GadgetKeysOK c.params x.lay c.params.src.qs.length .square s keys)
    (ρ ρ' : Env c.params.src) (σ : Trace.CtEnv c.params) (d a : Var) (v : Val c.params.src)
    (ca : List (IntPoly c.params.src.N))
    (hstep : step c.params.src ρ (.relin d a) = some ρ') (hv : ρ a = some v)
    (hca : σ a = some ca) (h1 : 1 ≤ v.level) (hL : v.level ≤ c.params.src.qs.length)
    (hlen : ca.length = v.parts) :
    Trace.StepOK c.params c.budget s ρ ρ' σ
      (σ.set d (relinOpenFHE c.params x.lay v.level ca keys)) (.relin d a) := by
  obtain ⟨hP, hk, hS, hlay⟩ := Validation.Certify.certify?_paramsOK x c h
  obtain ⟨-, hrest⟩ := Validation.Certify.certify?_keys_restrict x c h v.level h1 hL
  have := relinOpenFHE_stepOK c.params x.lay hk hP hS hc v.level hL (hlay v.level h1 hL).1
    c.budget (certified_ksBoundAt x c h v.level h1 hL) s hs _ (hrest .square s keys hkeys)
    ρ ρ' σ d a v ca hstep hv hca rfl hlen
  rwa [relinOpenFHE_take] at this

theorem certify?_keySwitchOpenFHE (x : Input) (c : Certificate) (h : certify? x = some c)
    (hc : x.lay.canonical = true)
    (s : IntPoly c.params.src.N) (hs : SecretOK c.params.secretBound s)
    (ρ ρ' : Env c.params.src) (σ : Trace.CtEnv c.params) (d a : Var) (v : Val c.params.src)
    (ca : List (IntPoly c.params.src.N))
    (hstep : step c.params.src ρ (.keySwitch d a) = some ρ') (hv : ρ a = some v)
    (hca : σ a = some ca) (h1 : 1 ≤ v.level) (hL : v.level ≤ c.params.src.qs.length)
    (hlen : ca.length = v.parts)
    (keys : List (IntPoly c.params.src.N × IntPoly c.params.src.N))
    (hkeys : GadgetKeysOK c.params x.lay c.params.src.qs.length (.galois v.key) s keys) :
    Trace.StepOK c.params c.budget s ρ ρ' σ
      (σ.set d (keySwitchOpenFHE c.params x.lay v.level ca keys)) (.keySwitch d a) := by
  obtain ⟨hP, hk, hS, hlay⟩ := Validation.Certify.certify?_paramsOK x c h
  obtain ⟨-, hrest⟩ := Validation.Certify.certify?_keys_restrict x c h v.level h1 hL
  have := keySwitchOpenFHE_stepOK c.params x.lay hk hP hS hc v.level hL (hlay v.level h1 hL).1
    c.budget (certified_ksBoundAt x c h v.level h1 hL) s hs ρ ρ' σ d a v ca hstep hv hca rfl hlen
    _ (hrest (.galois v.key) s keys hkeys)
  rwa [keySwitchOpenFHE_take] at this

theorem rotateOpenFHE161_take (P : FullParams) (lay : KSLayout) (ℓ g : ℕ)
    (ca : List (IntPoly P.src.N)) (keys : List (IntPoly P.src.N × IntPoly P.src.N)) :
    rotateOpenFHE161 P lay ℓ g ca (keys.take (lay.sizes ℓ).length) =
      rotateOpenFHE161 P lay ℓ g ca keys := by
  rcases ca with _ | ⟨c0, _ | ⟨c1, _ | ⟨c2, rest⟩⟩⟩
  · rfl
  · rfl
  · show [_, _] = [_, _]
    rw [innerKey_congr P lay ℓ c1 (fun j => ((keys.take (lay.sizes ℓ).length).getD j (0, 0)).1)
        (fun j => (keys.getD j (0, 0)).1) fun j => by rw [getD_take],
      innerKey_congr P lay ℓ c1 (fun j => ((keys.take (lay.sizes ℓ).length).getD j (0, 0)).2)
        (fun j => (keys.getD j (0, 0)).2) fun j => by rw [getD_take]]
  · rfl

theorem certify?_rotateOpenFHE161 (x : Input) (c : Certificate) (h : certify? x = some c)
    (hc : x.lay.canonical = true)
    (s : IntPoly c.params.src.N) (hs : SecretOK c.params.secretBound s)
    (ρ : Env c.params.src) (σ : Trace.CtEnv c.params) (d m a : Var) (g : ℕ) (hg : g % 2 = 1)
    (v : Val c.params.src) (ca : List (IntPoly c.params.src.N)) (hv : ρ a = some v)
    (hca : σ a = some ca) (h1 : 1 ≤ v.level) (hL : v.level ≤ c.params.src.qs.length)
    (hkey : v.key = 1) (hparts : v.parts = 2) (hlen : ca.length = 2)
    (s' : IntPoly c.params.src.N) (hs' : automorph g s' = s)
    (keys : List (IntPoly c.params.src.N × IntPoly c.params.src.N))
    (hkeys : GadgetKeysOK c.params x.lay c.params.src.qs.length (.galois g) s' keys) :
    Trace.Run c.params c.budget s [.automorph m a g, .keySwitch d m] ρ σ
      ((σ.set m (ca.map (automorph g))).set d
        (rotateOpenFHE161 c.params x.lay v.level g ca keys)) := by
  obtain ⟨hP, hk, hS, hlay⟩ := Validation.Certify.certify?_paramsOK x c h
  obtain ⟨-, hrest⟩ := Validation.Certify.certify?_keys_restrict x c h v.level h1 hL
  have := rotateOpenFHE161_run c.params x.lay hk hP hS hc v.level hL (hlay v.level h1 hL).1
    c.budget (certified_ksBoundAt x c h v.level h1 hL) s hs ρ σ d m a g hg v ca hv hca rfl hkey
    hparts hlen s' hs' _ (hrest (.galois g) s' keys hkeys)
  rwa [rotateOpenFHE161_take] at this

theorem certify?_modSwitch (x : Input) (c : Certificate) (h : certify? x = some c)
    (s : IntPoly c.params.src.N) (hs : SecretOK c.params.secretBound s)
    (ρ ρ' : Env c.params.src) (σ : Trace.CtEnv c.params) (d a : Var) (v : Val c.params.src)
    (ca : List (IntPoly c.params.src.N))
    (hstep : step c.params.src ρ (.modSwitch d a) = some ρ') (hv : ρ a = some v)
    (hca : σ a = some ca) (hlen : ca.length = v.parts) :
    Trace.StepOK c.params c.budget s ρ ρ' σ
      (σ.set d (ca.map (Challenge.Source.bgvModSwitchComp c.params.src.t
        c.params.src.qs[v.level - 1]!))) (.modSwitch d a) := by
  obtain ⟨hP, hk, -, -⟩ := Validation.Certify.certify?_paramsOK x c h
  refine Validation.Trace.stepOK_modSwitch_textbook_parts c.params hk hP c.budget s hs ρ ρ' σ d a
    v ca ?_ hstep hv hca hlen
  rw [(Validation.Certify.certify?_spec x c h).1, Validation.Budget.certified_modSwitchAt]

example := (@relinOpenFHE_stepOK : type_of% @Challenge.Realize.relinOpenFHE_stepOK)
example := (@keySwitchOpenFHE_stepOK : type_of% @Challenge.Realize.keySwitchOpenFHE_stepOK)
example := (@rotateOpenFHE161_run : type_of% @Challenge.Realize.rotateOpenFHE161_run)
example := (@rotKeySecret_exists : type_of% @Challenge.Realize.rotKeySecret_exists)
example := (@certify?_relinOpenFHE : type_of% @Challenge.Realize.certify?_relinOpenFHE)
example := (@certify?_keySwitchOpenFHE : type_of% @Challenge.Realize.certify?_keySwitchOpenFHE)
example := (@certify?_rotateOpenFHE161 : type_of% @Challenge.Realize.certify?_rotateOpenFHE161)
example := (@certify?_modSwitch : type_of% @Challenge.Realize.certify?_modSwitch)

end Validation.Realize
