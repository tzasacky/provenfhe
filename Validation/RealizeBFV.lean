import Challenge.RealizeBFV
import FHE.Realize.BFV
import FHE.BFV.KSLeveled
import Validation.Realize
import Validation.Budget.Restrict
import Validation.BFVMul.Ops

/-!
# Validation.RealizeBFV — proofs of `Challenge.RealizeBFV`

The contract of the transcription is `FHE.RealizeBFV.ksBFV_spec` (HYBRID: the BGV library
function `keySwitchBGVOpenFHE` at `t = 1`; BV: the integer core `ks_core` with `P = 1`); the step
statements read it in `Spec.TraceBFV.StepOK` as `Validation.BFV.relin_realizable` does for the
idealised algorithm. The rotation: the key switch for `(s', σ_g(s') = s)` followed by `σ_g`, whose
phase under `s` is `σ_g` of the operand's phase plus `σ_g(e)` (`FHE.KeySwitch.phaseAt_map_automorph`).
-/

namespace Validation.RealizeBFV
open Spec NPoly Scheme Source Correct Challenge.BFVMul Challenge.RealizeBFV

theorem neZero_N (P : FullParams) (hP : SchemeParamsOK P) : NeZero P.src.N :=
  ⟨by obtain ⟨k, hk'⟩ := hP.N_pow2; rw [hk']; positivity⟩

theorem ksBFV_coreOK (P : FullParams) (lay : Budget.KSLayout) (hP : SchemeParamsOK P)
    (hS : Budget.SpecialOK P) (hdecl : ksDeclOK? P lay = true) (ℓ : ℕ) (h1 : 1 ≤ ℓ)
    (hℓ : ℓ ≤ P.src.qs.length) (hlay : lay.okAt ℓ = true)
    (s : IntPoly P.src.N) (hs : SecretOK P.secretBound s) (tgt : KeyTarget)
    (keys : List (IntPoly P.src.N × IntPoly P.src.N))
    (hkeys : Budget.GadgetKeysOK P lay ℓ tgt s keys) :
    KSCoreOK (P.src.modulus ℓ) (BudgetBFV.ksBoundAt P lay ℓ) s (tgt.eval s)
      (fun d => ksBFV P lay ℓ d keys) := by
  have := neZero_N P hP
  refine (FHE.BFV.KSLeveled.KSCoreOK_def _ _ _ _ _).mpr fun d => ?_
  obtain ⟨e, he, hb⟩ := FHE.RealizeBFV.ksBFV_spec P hP hS lay ℓ hℓ hlay hdecl h1 s hs tgt keys
    hkeys d
  exact ⟨e, hb, he⟩

/-- `ksBV` reads the first `ℓ` keys only. -/
theorem ksBV_take (P : FullParams) (ℓ : ℕ) (d : IntPoly P.src.N)
    (keys : List (IntPoly P.src.N × IntPoly P.src.N)) :
    ksBV P ℓ d (keys.take ℓ) = ksBV P ℓ d keys := by
  unfold ksBV
  congr 2 <;> (congr 1; funext i; rw [Validation.Realize.getD_take])

/-- `ksBFV` at level `ℓ` reads only the keys of the digits of the level. -/
theorem ksBFV_take (P : FullParams) (lay : Budget.KSLayout) (hdecl : ksDeclOK? P lay = true)
    (ℓ : ℕ) (h1 : 1 ≤ ℓ) (hℓ : ℓ ≤ P.src.qs.length) (d : IntPoly P.src.N)
    (keys : List (IntPoly P.src.N × IntPoly P.src.N)) :
    ksBFV P lay ℓ d (keys.take (lay.sizes ℓ).length) = ksBFV P lay ℓ d keys := by
  obtain ⟨hbv, -⟩ := FHE.RealizeBFV.ksDeclOK_at P lay ℓ hℓ hdecl h1
  unfold ksBFV
  by_cases hsp : P.store.special = []
  · rw [if_pos hsp, if_pos hsp, hbv hsp, List.length_replicate, ksBV_take]
  · rw [if_neg hsp, if_neg hsp]
    exact Validation.Realize.ksOpenFHE_take (BudgetBFV.unitPlain P) lay ℓ d keys

theorem ksBFV_coreOK_top (P : FullParams) (lay : Budget.KSLayout) (hP : SchemeParamsOK P)
    (hk : P.src.kind = .bfv) (hS : Budget.SpecialOK P) (hdecl : ksDeclOK? P lay = true)
    (ℓ : ℕ) (h1 : 1 ≤ ℓ) (hℓ : ℓ ≤ P.src.qs.length)
    (hlay : Budget.restrictsTo lay P.src.qs.length ℓ = true)
    (s : IntPoly P.src.N) (hs : SecretOK P.secretBound s) (tgt : KeyTarget)
    (keys : List (IntPoly P.src.N × IntPoly P.src.N))
    (hkeys : Budget.GadgetKeysOK P lay P.src.qs.length tgt s keys) :
    KSCoreOK (P.src.modulus ℓ) (BudgetBFV.ksBoundAt P lay ℓ) s (tgt.eval s)
      (fun d => ksBFV P lay ℓ d keys) := by
  have hlay' : lay.okAt ℓ = true := Validation.Budget.restrictsTo_okAt lay _ ℓ hℓ hlay
  have hkeys' := Validation.Budget.gadgetKeys_restrict P lay tgt hP ℓ hℓ hlay
    (fun h => by rw [hk] at h; cases h) s keys hkeys
  have h := ksBFV_coreOK P lay hP hS hdecl ℓ h1 hℓ hlay' s hs tgt _ hkeys'
  simpa only [ksBFV_take P lay hdecl ℓ h1 hℓ] using h

theorem relinBFV_stepOK (P : FullParams) (lay : Budget.KSLayout) (hP : SchemeParamsOK P)
    (hS : Budget.SpecialOK P) (hdecl : ksDeclOK? P lay = true) (ℓ : ℕ) (h1 : 1 ≤ ℓ)
    (hℓ : ℓ ≤ P.src.qs.length) (hlay : lay.okAt ℓ = true)
    (E : TraceBFV.Budget) (hE : BudgetBFV.ksBoundAt P lay ℓ ≤ E.keySwitch)
    (s : IntPoly P.src.N) (hs : SecretOK P.secretBound s)
    (keys : List (IntPoly P.src.N × IntPoly P.src.N))
    (hkeys : Budget.GadgetKeysOK P lay ℓ .square s keys)
    (ρ ρ' : Env P.src) (σ : Trace.CtEnv P) (d a : Var) (x : Val P.src)
    (ca : List (IntPoly P.src.N))
    (hstep : step P.src ρ (.relin d a) = some ρ') (hx : ρ a = some x) (hca : σ a = some ca)
    (hl : x.level = ℓ) (hlen : ca.length = x.parts) :
    TraceBFV.StepOK P E s ρ ρ' σ (σ.set d (relinBFV P lay ℓ ca keys)) (.relin d a) := by
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
  obtain ⟨e, he, hb⟩ :=
    FHE.RealizeBFV.ksBFV_spec P hP hS lay _ hℓ hlay hdecl h1 s hs .square keys hkeys c2
  refine ⟨{ x with parts := 2 },
    [c0 + (ksBFV P lay x.level c2 keys).1, c1 + (ksBFV P lay x.level c2 keys).2], ?_, rfl,
    rfl, ?_⟩
  · simp [Env.set, Trace.dst, hg.2]
  refine ⟨x, [c0, c1, c2], e, hx, hca, hb.trans hE, ?_⟩
  simp only [Trace.phaseAt, hg.2, FHE.KeySwitch.automorph_one, List.map, phase,
    Validation.Scheme.ofInt_add, KeyTarget.eval] at he ⊢
  rw [Validation.Scheme.ofInt_mul] at he
  linear_combination he

theorem keySwitchBFV_stepOK (P : FullParams) (lay : Budget.KSLayout) (hP : SchemeParamsOK P)
    (hS : Budget.SpecialOK P) (hdecl : ksDeclOK? P lay = true) (ℓ : ℕ) (h1 : 1 ≤ ℓ)
    (hℓ : ℓ ≤ P.src.qs.length) (hlay : lay.okAt ℓ = true)
    (E : TraceBFV.Budget) (hE : BudgetBFV.ksBoundAt P lay ℓ ≤ E.keySwitch)
    (s : IntPoly P.src.N) (hs : SecretOK P.secretBound s)
    (ρ ρ' : Env P.src) (σ : Trace.CtEnv P) (d a : Var) (x : Val P.src)
    (ca : List (IntPoly P.src.N))
    (hstep : step P.src ρ (.keySwitch d a) = some ρ') (hx : ρ a = some x) (hca : σ a = some ca)
    (hl : x.level = ℓ) (hlen : ca.length = x.parts)
    (keys : List (IntPoly P.src.N × IntPoly P.src.N))
    (hkeys : Budget.GadgetKeysOK P lay ℓ (.galois x.key) s keys) :
    TraceBFV.StepOK P E s ρ ρ' σ (σ.set d (keySwitchBFV P lay ℓ ca keys)) (.keySwitch d a) := by
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
  obtain ⟨e, he, hb⟩ :=
    FHE.RealizeBFV.ksBFV_spec P hP hS lay _ hℓ hlay hdecl h1 s hs (.galois x.key) keys hkeys c1
  refine ⟨{ x with key := 1 },
    [c0 + (ksBFV P lay x.level c1 keys).1, (ksBFV P lay x.level c1 keys).2], ?_, ?_, rfl, ?_⟩
  · simp [Env.set, Trace.dst, hg]
  · simp [hg]
  refine ⟨x, [c0, c1], e, hx, hca, hb.trans hE, ?_⟩
  simp only [Trace.phaseAt, FHE.KeySwitch.automorph_one, List.map, phase,
    Validation.Scheme.ofInt_add, KeyTarget.eval] at he ⊢
  linear_combination he

/-! ## Rotation: key switch, then `σ_g` -/

/-- **A BFV `keySwitch` step whose phase error is `σ_g(e)`.** -/
theorem keySwitch_stepOK_of_automorph_error (P : FullParams) (hP : SchemeParamsOK P)
    (E : TraceBFV.Budget) (s : IntPoly P.src.N) {ρ ρ' : Env P.src} {σ : Trace.CtEnv P}
    {d a : Var} {x : Val P.src}
    (hstep : step P.src ρ (.keySwitch d a) = some ρ') (hx : ρ a = some x)
    {ca : List (IntPoly P.src.N)} (hca : σ a = some ca)
    {g : ℕ} (hg : g % 2 = 1) (e : IntPoly P.src.N) (he : normInf e ≤ E.keySwitch)
    {ct : List (IntPoly P.src.N)} (hlen : ct.length = 2)
    (hphase : Trace.phaseAt P (P.src.modulus x.level) 1 s ct =
      Trace.phaseAt P (P.src.modulus x.level) x.key s ca +
        automorph g (ofInt (P.src.modulus x.level) e)) :
    TraceBFV.StepOK P E s ρ ρ' σ (σ.set d ct) (.keySwitch d a) := by
  simp only [step, hx, guard] at hstep
  by_cases h2 : x.parts = 2
  swap
  · simp [h2] at hstep
  simp [h2] at hstep
  subst hstep
  refine ⟨{ x with key := 1 }, ct, ?_, ?_, rfl, ?_⟩
  · simp [Env.set, Trace.dst, h2]
  · exact hlen.trans h2.symm
  refine ⟨x, ca, automorph g e, hx, hca,
    (FHE.KeySwitch.normInf_automorph_le hP.N_pow2 hg e).trans he, ?_⟩
  rw [Validation.Scheme.ofInt_automorph]
  exact hphase

/-- The phase under `s` of `σ_g` of a two-component ciphertext whose phase under `s'`
(`σ_g(s') = s`) is `y`: `σ_g(y)`. -/
theorem phase_automorph_pair {N : ℕ} (Q : ℕ) {g : ℕ} (hg : g % 2 = 1) (s s' : IntPoly N)
    (hs' : automorph g s' = s) (y0 y1 : IntPoly N) :
    ofInt Q (automorph g y0) + ofInt Q (automorph g y1) * ofInt Q s =
      automorph g (ofInt Q y0 + ofInt Q y1 * ofInt Q s') := by
  rw [← hs', Validation.Scheme.ofInt_automorph, Validation.Scheme.ofInt_automorph,
    Validation.Scheme.ofInt_automorph, Validation.Source.automorph_add,
    Validation.Source.automorph_mul hg]

theorem rotateBFV_run (P : FullParams) (lay : Budget.KSLayout) (hP : SchemeParamsOK P)
    (hS : Budget.SpecialOK P) (hdecl : ksDeclOK? P lay = true) (ℓ : ℕ) (h1 : 1 ≤ ℓ)
    (hℓ : ℓ ≤ P.src.qs.length) (hlay : lay.okAt ℓ = true)
    (E : TraceBFV.Budget) (hE : BudgetBFV.ksBoundAt P lay ℓ ≤ E.keySwitch)
    (s : IntPoly P.src.N) (hs : SecretOK P.secretBound s)
    (ρ : Env P.src) (σ : Trace.CtEnv P) (d m a : Var) (g : ℕ) (hg : g % 2 = 1) (x : Val P.src)
    (ca : List (IntPoly P.src.N)) (hx : ρ a = some x) (hca : σ a = some ca)
    (hl : x.level = ℓ) (hkey : x.key = 1) (hparts : x.parts = 2) (hlen : ca.length = 2)
    (s' : IntPoly P.src.N) (hs' : automorph g s' = s)
    (keys : List (IntPoly P.src.N × IntPoly P.src.N))
    (hkeys : Budget.GadgetKeysOK P lay ℓ (.galois g) s' keys) :
    TraceBFV.Run P E s [.automorph m a g, .keySwitch d m] ρ σ
      ((σ.set m (ca.map (automorph g))).set d (rotateBFV P lay ℓ g ca keys)) := by
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
  have hs'b : normInf s' ≤ P.secretBound :=
    (Validation.Realize.normInf_le_of_automorph_eq hP.N_pow2 hg hs').trans hs
  obtain ⟨e, he, hb⟩ := FHE.RealizeBFV.ksBFV_spec P hP hS lay x.level hℓ hlay hdecl h1 s' hs'b
    (.galois g) keys hkeys c1
  refine ⟨ρ.set m v1, σ.set m ([c0, c1].map (automorph g)), hstep1, ?_, ?_⟩
  · exact Validation.BFVMul.stepOK_automorph_textbook P hP E s ρ _ σ m a g x [c0, c1] hstep1 hx
      hca (by simp [hparts])
  refine ⟨_, _, hstep2, ?_, rfl⟩
  refine keySwitch_stepOK_of_automorph_error P hP E s hstep2 hρ1 hσ1 hg e (hb.trans hE)
    rfl ?_
  have h1' : Trace.phaseAt P (P.src.modulus v1.level) v1.key s ([c0, c1].map (automorph g)) =
      automorph g (Trace.phaseAt P (P.src.modulus x.level) x.key s [c0, c1]) :=
    FHE.KeySwitch.phaseAt_map_automorph P _ x.key s hg [c0, c1]
  rw [h1']
  change Trace.phaseAt P (P.src.modulus x.level) 1 s (rotateBFV P lay x.level g [c0, c1] keys) = _
  simp only [KeyTarget.eval, hs'] at he
  have hrot : Trace.phaseAt P (P.src.modulus x.level) 1 s (rotateBFV P lay x.level g [c0, c1] keys)
      = automorph g (ofInt (P.src.modulus x.level) (c0 + (ksBFV P lay x.level c1 keys).1) +
          ofInt (P.src.modulus x.level) (ksBFV P lay x.level c1 keys).2 *
            ofInt (P.src.modulus x.level) s') := by
    rw [← phase_automorph_pair _ hg s s' hs']
    show Trace.phaseAt P (P.src.modulus x.level) 1 s
      [automorph g (c0 + (ksBFV P lay x.level c1 keys).1),
        automorph g (ksBFV P lay x.level c1 keys).2] = _
    simp only [List.map, Trace.phaseAt, FHE.KeySwitch.automorph_one, phase]
    ring
  rw [hrot, ← Validation.Source.automorph_add]
  congr 1
  simp only [Trace.phaseAt, hkey, FHE.KeySwitch.automorph_one, List.map, phase,
    Validation.Scheme.ofInt_add] at he ⊢
  linear_combination he

example := (@ksBFV_coreOK : type_of% @Challenge.RealizeBFV.ksBFV_coreOK)
example := (@ksBFV_coreOK_top : type_of% @Challenge.RealizeBFV.ksBFV_coreOK_top)
example := (@relinBFV_stepOK : type_of% @Challenge.RealizeBFV.relinBFV_stepOK)
example := (@keySwitchBFV_stepOK : type_of% @Challenge.RealizeBFV.keySwitchBFV_stepOK)
example := (@rotateBFV_run : type_of% @Challenge.RealizeBFV.rotateBFV_run)

end Validation.RealizeBFV
