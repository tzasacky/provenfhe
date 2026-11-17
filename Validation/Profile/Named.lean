import Challenge.Profile.Named
import Validation.Profile.Tool
import Validation.Realize
import Validation.RealizeBFV
import Validation.Trace

/-!
# Validation.Profile.Named — proofs of the pins of `Challenge.Profile.Named`

The checks are read by the existing decompositions (`Validation.Profile.coversBGV?_facts`,
`coversBFV?_facts`, `coversBFVAt?_facts`, `need_run`); the named statements are then
`Validation.RealizeBFV.relinBFV_stepOK`, `keySwitchBFV_stepOK`,
`Validation.Realize.relinOpenFHE_stepOK`, `keySwitchOpenFHE_stepOK` and
`Validation.Trace.stepOK_modSwitch_textbook_parts`, with the budget hypothesis from the check.
No locked definition is unfolded by name.
-/

namespace Validation.ProfileNamed
open Spec NPoly Scheme Source Correct Challenge.Profile Challenge.CertifyBFV Challenge.BFV
  Challenge.RealizeBFV Challenge.Realize

theorem coversBGV?_side (P : FullParams) (lay : Budget.KSLayout) (K : ℕ) (E : Trace.Budget)
    (hc : coversBGV? P lay K E = true) :
    SchemeParamsOK P ∧ P.src.kind = .bgv ∧ Budget.SpecialOK P ∧
      ∀ ℓ, 1 ≤ ℓ → ℓ ≤ P.src.qs.length → lay.okAt ℓ = true := by
  obtain ⟨hP, hk, hS, hl, -⟩ := Validation.Profile.coversBGV?_facts hc
  exact ⟨hP, hk, hS, fun ℓ h1 hℓ => (hl ℓ h1 hℓ).1⟩

theorem coversBGV?_ksBound (P : FullParams) (lay : Budget.KSLayout) (K : ℕ) (E : Trace.Budget)
    (hc : coversBGV? P lay K E = true) (ℓ : ℕ) (h1 : 1 ≤ ℓ) (hℓ : ℓ ≤ P.src.qs.length) :
    Budget.ksBoundAt P lay ℓ ≤ E.keySwitch :=
  ((Validation.Profile.coversBGV?_facts hc).2.2.2.1 ℓ h1 hℓ).2

theorem coversBGV?_msBudget (P : FullParams) (lay : Budget.KSLayout) (K : ℕ) (E : Trace.Budget)
    (hc : coversBGV? P lay K E = true) (k : ℕ) (h1 : 1 ≤ k) (hk : k ≤ K) :
    Budget.msBudgetAt P k ≤ E.modSwitchAt k :=
  (Validation.Profile.coversBGV?_facts hc).2.2.2.2 k h1 hk

theorem coversBFV?_side (P : FullParams) (lay : Budget.KSLayout) (U r : ℕ) (body : List Instr)
    (E : ℕ → TraceBFV.Budget) (hc : coversBFV? P lay U r body E = true) :
    SchemeParamsOK P ∧ Budget.SpecialOK P ∧
      ∀ ℓ, 1 ≤ ℓ → ℓ ≤ P.src.qs.length → lay.okAt ℓ = true := by
  obtain ⟨hP, hS, hl, -⟩ := Validation.Profile.coversBFV?_facts hc
  exact ⟨hP, hS, hl⟩

theorem coversBFV?_ksBound (P : FullParams) (lay : Budget.KSLayout) (U r : ℕ) (body : List Instr)
    (E : ℕ → TraceBFV.Budget) (hc : coversBFV? P lay U r body E = true) (k : ℕ) (d a : Var)
    (hk : body[k]? = some (.relin d a) ∨ body[k]? = some (.keySwitch d a))
    (ℓ : ℕ) (h1 : 1 ≤ ℓ) (hℓ : ℓ ≤ P.src.qs.length) :
    BudgetBFV.ksBoundAt P lay ℓ ≤ (E k).keySwitch := by
  obtain ⟨-, -, -, hn⟩ := Validation.Profile.coversBFV?_facts hc
  have hks : ksCoversBFV P lay (E k).keySwitch = true := by
    rcases hk with hk | hk
    · exact hn k _ hk
    · exact hn k _ hk
  exact Validation.Profile.ksCoversBFV_at hks ℓ h1 hℓ

theorem coversBFVAt?_side (P : FullParams) (lay : Budget.KSLayout) (U r : ℕ) (prog : Program)
    (E : ℕ → TraceBFV.Budget) (hc : coversBFVAt? P lay U r prog E = true) :
    SchemeParamsOK P ∧ P.src.kind = .bfv ∧ Budget.SpecialOK P ∧
      ∀ ℓ, 1 ≤ ℓ → ℓ ≤ P.src.qs.length → lay.okAt ℓ = true := by
  obtain ⟨hP, hk, hS, hl, -⟩ := Validation.Profile.coversBFVAt?_facts hc
  exact ⟨hP, hk, hS, hl⟩

open Validation.BFV.SoundAux in
theorem coversBFVAt?_ksBound (P : FullParams) (lay : Budget.KSLayout) (U r : ℕ) (prog : Program)
    (E : ℕ → TraceBFV.Budget) (hc : coversBFVAt? P lay U r prog E = true)
    (msgs : Var → Msg P.src.t P.src.N) (pre post : List Instr) (d a : Var) (ρ : Env P.src)
    (hbody : prog.body = pre ++ .relin d a :: post ∨ prog.body = pre ++ .keySwitch d a :: post)
    (hρ : pre.foldlM (step P.src) (initEnv P.src prog msgs) = some ρ)
    (x : Val P.src) (hx : ρ a = some x) :
    BudgetBFV.ksBoundAt P lay x.level ≤ (E pre.length).keySwitch := by
  have hn : decide (BudgetBFV.ksBoundAt P lay (levelOf (zenv ρ) a) ≤ (E pre.length).keySwitch)
      = true := by
    rcases hbody with hbody | hbody
    · exact Validation.Profile.need_run hc hbody hρ
    · exact Validation.Profile.need_run hc hbody hρ
  rw [Validation.CertifyBFV.levelOf_zenv, Validation.CertifyBFV.levelOf_some hx,
    decide_eq_true_eq] at hn
  exact hn

theorem coversBFV?_relinBFV (P : FullParams) (lay : Budget.KSLayout) (U r : ℕ) (body : List Instr)
    (E : ℕ → TraceBFV.Budget) (hc : coversBFV? P lay U r body E = true)
    (hdecl : ksDeclOK? P lay = true) (k : ℕ) (d a : Var) (hk : body[k]? = some (.relin d a))
    (s : IntPoly P.src.N) (hs : SecretOK P.secretBound s)
    (ρ ρ' : Env P.src) (σ : Trace.CtEnv P) (x : Val P.src) (ca : List (IntPoly P.src.N))
    (hstep : step P.src ρ (.relin d a) = some ρ') (hx : ρ a = some x) (hca : σ a = some ca)
    (h1 : 1 ≤ x.level) (hL : x.level ≤ P.src.qs.length) (hlen : ca.length = x.parts)
    (keys : List (IntPoly P.src.N × IntPoly P.src.N))
    (hkeys : Budget.GadgetKeysOK P lay x.level .square s keys) :
    TraceBFV.StepOK P (E k) s ρ ρ' σ (σ.set d (relinBFV P lay x.level ca keys)) (.relin d a) := by
  obtain ⟨hP, hS, hl⟩ := coversBFV?_side P lay U r body E hc
  exact Validation.RealizeBFV.relinBFV_stepOK P lay hP hS hdecl x.level h1 hL (hl _ h1 hL) (E k)
    (coversBFV?_ksBound P lay U r body E hc k d a (Or.inl hk) x.level h1 hL) s hs keys hkeys
    ρ ρ' σ d a x ca hstep hx hca rfl hlen

theorem coversBFV?_keySwitchBFV (P : FullParams) (lay : Budget.KSLayout) (U r : ℕ)
    (body : List Instr) (E : ℕ → TraceBFV.Budget) (hc : coversBFV? P lay U r body E = true)
    (hdecl : ksDeclOK? P lay = true) (k : ℕ) (d a : Var) (hk : body[k]? = some (.keySwitch d a))
    (s : IntPoly P.src.N) (hs : SecretOK P.secretBound s)
    (ρ ρ' : Env P.src) (σ : Trace.CtEnv P) (x : Val P.src) (ca : List (IntPoly P.src.N))
    (hstep : step P.src ρ (.keySwitch d a) = some ρ') (hx : ρ a = some x) (hca : σ a = some ca)
    (h1 : 1 ≤ x.level) (hL : x.level ≤ P.src.qs.length) (hlen : ca.length = x.parts)
    (keys : List (IntPoly P.src.N × IntPoly P.src.N))
    (hkeys : Budget.GadgetKeysOK P lay x.level (.galois x.key) s keys) :
    TraceBFV.StepOK P (E k) s ρ ρ' σ (σ.set d (keySwitchBFV P lay x.level ca keys))
      (.keySwitch d a) := by
  obtain ⟨hP, hS, hl⟩ := coversBFV?_side P lay U r body E hc
  exact Validation.RealizeBFV.keySwitchBFV_stepOK P lay hP hS hdecl x.level h1 hL (hl _ h1 hL)
    (E k) (coversBFV?_ksBound P lay U r body E hc k d a (Or.inr hk) x.level h1 hL) s hs
    ρ ρ' σ d a x ca hstep hx hca rfl hlen keys hkeys

theorem coversBFVAt?_relinBFV (P : FullParams) (lay : Budget.KSLayout) (U r : ℕ) (prog : Program)
    (E : ℕ → TraceBFV.Budget) (hc : coversBFVAt? P lay U r prog E = true)
    (hdecl : ksDeclOK? P lay = true)
    (msgs : Var → Msg P.src.t P.src.N) (pre post : List Instr) (d a : Var) (ρ ρ' : Env P.src)
    (hbody : prog.body = pre ++ .relin d a :: post)
    (hρ : pre.foldlM (step P.src) (initEnv P.src prog msgs) = some ρ)
    (s : IntPoly P.src.N) (hs : SecretOK P.secretBound s)
    (σ : Trace.CtEnv P) (x : Val P.src) (ca : List (IntPoly P.src.N))
    (hstep : step P.src ρ (.relin d a) = some ρ') (hx : ρ a = some x) (hca : σ a = some ca)
    (h1 : 1 ≤ x.level) (hL : x.level ≤ P.src.qs.length) (hlen : ca.length = x.parts)
    (keys : List (IntPoly P.src.N × IntPoly P.src.N))
    (hkeys : Budget.GadgetKeysOK P lay x.level .square s keys) :
    TraceBFV.StepOK P (E pre.length) s ρ ρ' σ (σ.set d (relinBFV P lay x.level ca keys))
      (.relin d a) := by
  obtain ⟨hP, -, hS, hl⟩ := coversBFVAt?_side P lay U r prog E hc
  exact Validation.RealizeBFV.relinBFV_stepOK P lay hP hS hdecl x.level h1 hL (hl _ h1 hL)
    (E pre.length)
    (coversBFVAt?_ksBound P lay U r prog E hc msgs pre post d a ρ (Or.inl hbody) hρ x hx)
    s hs keys hkeys ρ ρ' σ d a x ca hstep hx hca rfl hlen

theorem coversBFVAt?_keySwitchBFV (P : FullParams) (lay : Budget.KSLayout) (U r : ℕ)
    (prog : Program) (E : ℕ → TraceBFV.Budget) (hc : coversBFVAt? P lay U r prog E = true)
    (hdecl : ksDeclOK? P lay = true)
    (msgs : Var → Msg P.src.t P.src.N) (pre post : List Instr) (d a : Var) (ρ ρ' : Env P.src)
    (hbody : prog.body = pre ++ .keySwitch d a :: post)
    (hρ : pre.foldlM (step P.src) (initEnv P.src prog msgs) = some ρ)
    (s : IntPoly P.src.N) (hs : SecretOK P.secretBound s)
    (σ : Trace.CtEnv P) (x : Val P.src) (ca : List (IntPoly P.src.N))
    (hstep : step P.src ρ (.keySwitch d a) = some ρ') (hx : ρ a = some x) (hca : σ a = some ca)
    (h1 : 1 ≤ x.level) (hL : x.level ≤ P.src.qs.length) (hlen : ca.length = x.parts)
    (keys : List (IntPoly P.src.N × IntPoly P.src.N))
    (hkeys : Budget.GadgetKeysOK P lay x.level (.galois x.key) s keys) :
    TraceBFV.StepOK P (E pre.length) s ρ ρ' σ (σ.set d (keySwitchBFV P lay x.level ca keys))
      (.keySwitch d a) := by
  obtain ⟨hP, -, hS, hl⟩ := coversBFVAt?_side P lay U r prog E hc
  exact Validation.RealizeBFV.keySwitchBFV_stepOK P lay hP hS hdecl x.level h1 hL (hl _ h1 hL)
    (E pre.length)
    (coversBFVAt?_ksBound P lay U r prog E hc msgs pre post d a ρ (Or.inr hbody) hρ x hx)
    s hs ρ ρ' σ d a x ca hstep hx hca rfl hlen keys hkeys

theorem coversBGV?_relinOpenFHE (P : FullParams) (lay : Budget.KSLayout) (K : ℕ)
    (E : Trace.Budget) (hc : coversBGV? P lay K E = true) (hcan : lay.canonical = true)
    (s : IntPoly P.src.N) (hs : SecretOK P.secretBound s)
    (ρ ρ' : Env P.src) (σ : Trace.CtEnv P) (d a : Var) (x : Val P.src)
    (ca : List (IntPoly P.src.N))
    (hstep : step P.src ρ (.relin d a) = some ρ') (hx : ρ a = some x) (hca : σ a = some ca)
    (h1 : 1 ≤ x.level) (hL : x.level ≤ P.src.qs.length) (hlen : ca.length = x.parts)
    (keys : List (IntPoly P.src.N × IntPoly P.src.N))
    (hkeys : Budget.GadgetKeysOK P lay x.level .square s keys) :
    Trace.StepOK P E s ρ ρ' σ (σ.set d (relinOpenFHE P lay x.level ca keys)) (.relin d a) := by
  obtain ⟨hP, hk, hS, hl⟩ := coversBGV?_side P lay K E hc
  exact Validation.Realize.relinOpenFHE_stepOK P lay hk hP hS hcan x.level hL (hl _ h1 hL) E
    (coversBGV?_ksBound P lay K E hc x.level h1 hL) s hs keys hkeys ρ ρ' σ d a x ca hstep hx hca
    rfl hlen

theorem coversBGV?_keySwitchOpenFHE (P : FullParams) (lay : Budget.KSLayout) (K : ℕ)
    (E : Trace.Budget) (hc : coversBGV? P lay K E = true) (hcan : lay.canonical = true)
    (s : IntPoly P.src.N) (hs : SecretOK P.secretBound s)
    (ρ ρ' : Env P.src) (σ : Trace.CtEnv P) (d a : Var) (x : Val P.src)
    (ca : List (IntPoly P.src.N))
    (hstep : step P.src ρ (.keySwitch d a) = some ρ') (hx : ρ a = some x) (hca : σ a = some ca)
    (h1 : 1 ≤ x.level) (hL : x.level ≤ P.src.qs.length) (hlen : ca.length = x.parts)
    (keys : List (IntPoly P.src.N × IntPoly P.src.N))
    (hkeys : Budget.GadgetKeysOK P lay x.level (.galois x.key) s keys) :
    Trace.StepOK P E s ρ ρ' σ (σ.set d (keySwitchOpenFHE P lay x.level ca keys))
      (.keySwitch d a) := by
  obtain ⟨hP, hk, hS, hl⟩ := coversBGV?_side P lay K E hc
  exact Validation.Realize.keySwitchOpenFHE_stepOK P lay hk hP hS hcan x.level hL (hl _ h1 hL) E
    (coversBGV?_ksBound P lay K E hc x.level h1 hL) s hs ρ ρ' σ d a x ca hstep hx hca rfl hlen
    keys hkeys

theorem coversBGV?_modSwitchTextbook (P : FullParams) (lay : Budget.KSLayout) (K : ℕ)
    (E : Trace.Budget) (hc : coversBGV? P lay K E = true)
    (s : IntPoly P.src.N) (hs : SecretOK P.secretBound s)
    (ρ ρ' : Env P.src) (σ : Trace.CtEnv P) (d a : Var) (x : Val P.src)
    (ca : List (IntPoly P.src.N))
    (hstep : step P.src ρ (.modSwitch d a) = some ρ') (hx : ρ a = some x) (hca : σ a = some ca)
    (hlen : ca.length = x.parts) (hpK : x.parts ≤ K) :
    Trace.StepOK P E s ρ ρ' σ
      (σ.set d (ca.map (Challenge.Source.bgvModSwitchComp P.src.t P.src.qs[x.level - 1]!)))
      (.modSwitch d a) := by
  obtain ⟨hP, hk, -, -⟩ := coversBGV?_side P lay K E hc
  have hE : Budget.msBudgetAt P x.parts ≤ E.modSwitchAt x.parts := by
    rcases Nat.eq_zero_or_pos x.parts with h0 | hp
    · rw [h0]
      simp [Budget.msBudgetAt]
    · exact coversBGV?_msBudget P lay K E hc x.parts hp hpK
  exact Validation.Trace.stepOK_modSwitch_textbook_parts P hk hP E s hs ρ ρ' σ d a x ca
    hE hstep hx hca hlen

example := (@coversBGV?_side : type_of% @Challenge.ProfileNamed.coversBGV?_side)
example := (@coversBGV?_ksBound : type_of% @Challenge.ProfileNamed.coversBGV?_ksBound)
example := (@coversBGV?_msBudget : type_of% @Challenge.ProfileNamed.coversBGV?_msBudget)
example := (@coversBFV?_side : type_of% @Challenge.ProfileNamed.coversBFV?_side)
example := (@coversBFV?_ksBound : type_of% @Challenge.ProfileNamed.coversBFV?_ksBound)
example := (@coversBFVAt?_side : type_of% @Challenge.ProfileNamed.coversBFVAt?_side)
example := (@coversBFVAt?_ksBound : type_of% @Challenge.ProfileNamed.coversBFVAt?_ksBound)
example := (@coversBFV?_relinBFV : type_of% @Challenge.ProfileNamed.coversBFV?_relinBFV)
example := (@coversBFV?_keySwitchBFV : type_of% @Challenge.ProfileNamed.coversBFV?_keySwitchBFV)
example := (@coversBFVAt?_relinBFV : type_of% @Challenge.ProfileNamed.coversBFVAt?_relinBFV)
example := (@coversBFVAt?_keySwitchBFV :
  type_of% @Challenge.ProfileNamed.coversBFVAt?_keySwitchBFV)
example := (@coversBGV?_relinOpenFHE : type_of% @Challenge.ProfileNamed.coversBGV?_relinOpenFHE)
example := (@coversBGV?_keySwitchOpenFHE :
  type_of% @Challenge.ProfileNamed.coversBGV?_keySwitchOpenFHE)
example := (@coversBGV?_modSwitchTextbook :
  type_of% @Challenge.ProfileNamed.coversBGV?_modSwitchTextbook)

end Validation.ProfileNamed
