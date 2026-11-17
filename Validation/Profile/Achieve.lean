import Challenge.Profile.Achieve
import Validation.Profile.Named
import Validation.IndCpaD.ProfileBGVKS
import Validation.IndCpaD.LMBFV

/-!
# Validation.Profile.Achieve — proofs of the pins of `Challenge.Profile.Achieve`

The class conditions of the evaluators (`Challenge.IndCpaDProfile.ksNeed`,
`Challenge.IndCpaDLM.bfvNeedAt`) are derived from the coverage checks along the run, with the
explicit hypotheses for the Galois elements and the numbers of components: `ksNeed_of` (BGV, by
induction over the body, the level of each operand inside the chain by the `Levels` invariant,
which the declarations start), and inside `bfv_run_at` (BFV, in lockstep with the replay of
`coversBFVAt?`, `needAux`). The runs are then `Validation.IndCpaDProfile.ks_run` and
`Validation.IndCpaDLM.bfv_step` step by step; decryption is the profile soundness
(`certifyProfile?_sound`, `certifyBFVProfile?_sound`) applied to that run. No locked definition is
unfolded by name: they are read through `show`, `change` and existing `rfl` equations.
-/

namespace Validation.ProfileAchieve
open Spec NPoly Scheme Source Correct Challenge.Profile Challenge.CertifyBFV Challenge.BFV
  Challenge.RealizeBFV Challenge.Realize Challenge.IndCpaDProfile Challenge.IndCpaDLM
  Challenge.ProfileAchieve
open Validation.Budget.RunAux (Shape shape_step Levels levels_step)
open Validation.BFV.SoundAux (zenv zv)

/-! ## BFV: the run is the interpreter's -/

theorem bfvRun_eq_irun (D : Spec.IndCpaDProfile.AbsScheme) (lay : Budget.KSLayout)
    (rk : D.PK → ℕ → List (IntPoly D.P.src.N × IntPoly D.P.src.N))
    (gk : D.PK → ℕ → ℕ → List (IntPoly D.P.src.N × IntPoly D.P.src.N)) (pk : D.PK)
    (body : List Instr) (ρ : Env D.P.src) (σ : Trace.CtEnv D.Pe) :
    irun D (bfvStepFn D lay rk gk) pk body ρ σ = bfvRun D.Pe lay (rk pk) (gk pk) body ρ σ := by
  induction body generalizing ρ σ with
  | nil => rfl
  | cons i is ih =>
    show (step D.P.src ρ i).bind (fun ρ' => (bfvStep D.Pe lay (rk pk) (gk pk) ρ σ i).bind
        fun σ' => irun D (bfvStepFn D lay rk gk) pk is ρ' σ') =
      (step D.P.src ρ i).bind (fun ρ' => (bfvStep D.Pe lay (rk pk) (gk pk) ρ σ i).bind
        fun σ' => bfvRun D.Pe lay (rk pk) (gk pk) is ρ' σ')
    exact congrArg _ (funext fun ρ' => congrArg _ (funext fun σ' => ih ρ' σ'))

/-! ## BGV -/

section BGV
variable {P : FullParams} {lay : Budget.KSLayout} {K : ℕ} {E : Trace.Budget} {rots : List ℕ}

/-- `ksSide` from the coverage check and the explicit layout conditions. -/
theorem ksSide_of (hc : coversBGV? P lay K E = true) (hcan : lay.canonical = true)
    (hlo : Spec.Certify.layoutOK? P lay = true) (hkr : Spec.Certify.keysRestrict? P = true) :
    ksSide P lay = true := by
  have hc' : (schemeParamsOK? P && decide (P.src.kind = .bgv) && Budget.specialOK? P &&
      (List.range P.src.qs.length).all (fun j =>
        lay.okAt (j + 1) && decide (Budget.ksBoundAt P lay (j + 1) ≤ E.keySwitch)) &&
      (List.range K).all fun j =>
        decide (Budget.msBudgetAt P (j + 1) ≤ E.modSwitchAt (j + 1))) = true := hc
  simp only [Bool.and_eq_true] at hc'
  change (Budget.specialOK? P && Spec.Certify.layoutOK? P lay && Spec.Certify.keysRestrict? P &&
    lay.canonical) = true
  simp [hc'.1.1.2, hlo, hkr, hcan]

/-- **The class condition `ksNeed` from the coverage check** along a run. -/
theorem ksNeed_of (hk : P.src.kind = .bgv) (hc : coversBGV? P lay K E = true) :
    ∀ (body : List Instr) (ρ : Env P.src), Levels P ρ →
      (∀ (pre post : List Instr) (d a : Var) (ρ' : Env P.src) (x : Val P.src),
        body = pre ++ .keySwitch d a :: post →
        pre.foldlM (step P.src) ρ = some ρ' → ρ' a = some x → x.key ∈ rots) →
      (∀ (pre post : List Instr) (d a : Var) (ρ' : Env P.src) (x : Val P.src),
        body = pre ++ .modSwitch d a :: post →
        pre.foldlM (step P.src) ρ = some ρ' → ρ' a = some x → x.parts ≤ K) →
      ksNeed P lay rots E body (zenv ρ) = true
  | [], _, _, _, _ => rfl
  | i :: is, ρ, hlv, hrot, hms => by
    have hz := (Validation.IndCpaDProfile.step_zenv_bgv hk (Validation.IndCpaD.allExact_all ρ) i).1
    show (ksNeedAt P lay rots E (zenv ρ) i &&
      (step P.src (zenv ρ) i).elim true (ksNeed P lay rots E is)) = true
    rw [hz, Bool.and_eq_true]
    refine ⟨?_, ?_⟩
    · cases i
      case relin d a =>
        show ((zenv ρ a).elim true fun x =>
          decide (Budget.ksBoundAt P lay x.level ≤ E.keySwitch)) = true
        rcases hx : ρ a with _ | x
        · simp [zenv, hx]
        · have hz' : zenv ρ a = some (zv x) := by simp [zenv, hx]
          rw [hz']
          obtain ⟨h1, hL⟩ := hlv a x hx
          exact decide_eq_true
            (Validation.ProfileNamed.coversBGV?_ksBound P lay K E hc x.level h1 hL)
      case keySwitch d a =>
        show ((zenv ρ a).elim true fun x =>
          decide (Budget.ksBoundAt P lay x.level ≤ E.keySwitch) && decide (x.key ∈ rots)) = true
        rcases hx : ρ a with _ | x
        · simp [zenv, hx]
        · have hz' : zenv ρ a = some (zv x) := by simp [zenv, hx]
          rw [hz']
          obtain ⟨h1, hL⟩ := hlv a x hx
          exact (Bool.and_eq_true _ _).mpr
            ⟨decide_eq_true (Validation.ProfileNamed.coversBGV?_ksBound P lay K E hc x.level h1 hL),
              decide_eq_true (hrot [] is d a ρ x rfl rfl hx)⟩
      case modSwitch d a =>
        show ((zenv ρ a).elim true fun x =>
          decide (Budget.msBudgetAt P x.parts ≤ E.modSwitchAt x.parts)) = true
        rcases hx : ρ a with _ | x
        · simp [zenv, hx]
        · have hz' : zenv ρ a = some (zv x) := by simp [zenv, hx]
          rw [hz']
          show decide (Budget.msBudgetAt P x.parts ≤ E.modSwitchAt x.parts) = true
          apply decide_eq_true
          rcases Nat.eq_zero_or_pos x.parts with h0 | hp
          · rw [h0]
            simp [Budget.msBudgetAt]
          · exact Validation.ProfileNamed.coversBGV?_msBudget P lay K E hc x.parts hp
              (hms [] is d a ρ x rfl rfl hx)
      all_goals rfl
    · rcases hs : step P.src ρ i with _ | ρ'
      · rfl
      · show ksNeed P lay rots E is (zenv ρ') = true
        exact ksNeed_of hk hc is ρ' (levels_step hlv hs)
          (fun pre post d a ρ'' x hb hf hx => hrot (i :: pre) post d a ρ'' x
            (by rw [hb]; rfl) (by rw [List.foldlM_cons, hs]; exact hf) hx)
          (fun pre post d a ρ'' x hb hf hx => hms (i :: pre) post d a ρ'' x
            (by rw [hb]; rfl) (by rw [List.foldlM_cons, hs]; exact hf) hx)

end BGV

theorem achieve_bgv (P : FullParams) (E : Trace.Budget) (prog : Program) (sw : Bool) (B : ℕ)
    (outs : List (Var × ℕ)) (h : certifyProfile? P E prog sw = some (B, outs))
    (lay : Budget.KSLayout) (K : ℕ) (hc : coversBGV? P lay K E = true)
    (hcan : lay.canonical = true) (hlo : Spec.Certify.layoutOK? P lay = true)
    (hkr : Spec.Certify.keysRestrict? P = true) (rots : List ℕ)
    (s : IntPoly P.src.N) (hs : SecretOK P.secretBound s)
    (rk : List (IntPoly P.src.N × IntPoly P.src.N))
    (hrk : Budget.GadgetKeysOK P lay P.src.qs.length .square s rk)
    (gk : ℕ → List (IntPoly P.src.N × IntPoly P.src.N))
    (hgk : ∀ g ∈ rots, Budget.GadgetKeysOK P lay P.src.qs.length (.galois g) s (gk g))
    (msgs : Var → Msg P.src.t P.src.N) (cts : Var → List (IntPoly P.src.N))
    (hin : InputsOK P s prog msgs cts) (hb : Trace.BoundsOK P s prog msgs cts)
    (hrot : ∀ (pre post : List Instr) (d a : Var) (ρ : Env P.src) (x : Val P.src),
      prog.body = pre ++ .keySwitch d a :: post →
      pre.foldlM (step P.src) (initEnv P.src prog msgs) = some ρ → ρ a = some x → x.key ∈ rots)
    (hms : ∀ (pre post : List Instr) (d a : Var) (ρ : Env P.src) (x : Val P.src),
      prog.body = pre ++ .modSwitch d a :: post →
      pre.foldlM (step P.src) (initEnv P.src prog msgs) = some ρ → ρ a = some x → x.parts ≤ K) :
    ∃ σf, ksRun P lay rk gk prog.body (initEnv P.src prog fun _ => .exact 0)
        (Trace.initCt P prog cts) = some σf ∧
      Trace.Run P E s prog.body (initEnv P.src prog msgs) (Trace.initCt P prog cts) σf ∧
      ∃ ρ, Source.eval P.src prog msgs = some ρ ∧
        ∀ o ∈ prog.outputs, ∃ v ct m b, ρ o = some v ∧ σf o = some ct ∧
          outs.lookup o = some b ∧ Encrypts P s b v ct ∧ v.msg = .exact m ∧ v.key = 1 ∧
          bgvDecrypt P.src.t s (ct.map (ofInt (P.src.modulus v.level))) = m := by
  obtain ⟨hP, hk, -, -⟩ := Validation.Profile.certifyProfile?_some h
  obtain ⟨ρ, hρ, hall⟩ :=
    Validation.Profile.certifyProfile?_sound P E prog sw B outs h s msgs cts hin hb
  have hρ' := hρ
  simp only [Source.eval, Option.bind_eq_bind, Option.pure_def] at hρ'
  obtain ⟨hdecl, hρ'⟩ := Validation.Trace.guard_bind_eq_some hρ'
  obtain ⟨-, hρ'⟩ := Validation.Trace.guard_bind_eq_some hρ'
  obtain ⟨ρf, hbody, -⟩ := Option.bind_eq_some_iff.mp hρ'
  have hsh : Shape P (initEnv P.src prog msgs) (Trace.initCt P prog cts) := by
    intro x v hv
    simp only [initEnv, Option.map_eq_some_iff] at hv
    obtain ⟨d, hd, rfl⟩ := hv
    exact ⟨_, by simp [Trace.initCt, hd], (hin x d hd).1⟩
  have hlv : Levels P (initEnv P.src prog msgs) := by
    intro x v hv
    simp only [initEnv, Option.map_eq_some_iff] at hv
    obtain ⟨d, hd, rfl⟩ := hv
    have hok := List.all_eq_true.mp hdecl d (List.mem_of_find?_eq_some hd)
    simp only [Decl.ok, decide_eq_true_eq] at hok
    exact ⟨hok.2.1, hok.2.2.1⟩
  have hz0 : zenv (initEnv P.src prog msgs) = initEnv P.src prog fun _ => .exact 0 := by
    funext x; simp only [zenv, initEnv, Option.map_map]; rfl
  have hneed := ksNeed_of (rots := rots) hk hc prog.body _ hlv hrot hms
  obtain ⟨σf, hf, hrun⟩ := Validation.IndCpaDProfile.ks_run (P := P) (lay := lay) (rots := rots)
    (E := E) (s := s) (rk := rk) (gk := gk) hk hP (ksSide_of hc hcan hlo hkr) hs hrk hgk
    prog.body _ ρf _ hsh hlv hneed hbody
  rw [hz0] at hf
  refine ⟨σf, hf, hrun, ρ, hρ, fun o ho => ?_⟩
  obtain ⟨v, ct, m, b, h1, h2, h3, h4, h5, h6, h7, -⟩ := hall σf hrun o ho
  exact ⟨v, ct, m, b, h1, h2, h3, h4, h5, h6, h7⟩

/-! ## BFV -/

section BFV
variable {P : FullParams} {lay : Budget.KSLayout} {U r : ℕ} {E : ℕ → TraceBFV.Budget}
  {rots : List ℕ} {s : IntPoly P.src.N} {rk : ℕ → List (IntPoly P.src.N × IntPoly P.src.N)}
  {gk : ℕ → ℕ → List (IntPoly P.src.N × IntPoly P.src.N)}

/-- **The evaluator's run** is a run within `E`, from the replay condition of `coversBFVAt?`. -/
theorem bfv_run_at (hk : P.src.kind = .bfv) (hP : SchemeParamsOK P)
    (hside : bfvSide P lay = true) (hs : SecretOK P.secretBound s)
    (hkeys : ∀ ℓ, 1 ≤ ℓ → ℓ ≤ P.src.qs.length →
      Budget.GadgetKeysOK P lay ℓ .square s (rk ℓ) ∧
      ∀ g ∈ rots, Budget.GadgetKeysOK P lay ℓ (.galois g) s (gk g ℓ)) (hr : 1 ≤ r) :
    ∀ (body : List Instr) (n : ℕ) (ρ ρf : Env P.src) (σ : Trace.CtEnv P),
      Shape P ρ σ → Levels P ρ → needAux P lay U r E n body (zenv ρ) = true →
      (∀ (pre post : List Instr) (d a : Var) (ρ' : Env P.src) (x : Val P.src),
        body = pre ++ .keySwitch d a :: post →
        pre.foldlM (step P.src) ρ = some ρ' → ρ' a = some x → x.key ∈ rots) →
      (∀ (pre post : List Instr) (d a b : Var) (ρ' : Env P.src) (x y : Val P.src),
        body = pre ++ .mul d a b :: post →
        pre.foldlM (step P.src) ρ = some ρ' → ρ' a = some x → ρ' b = some y →
        x.parts = 2 ∧ y.parts = 2) →
      (∀ (pre post : List Instr) (d a : Var) (ρ' : Env P.src) (x : Val P.src),
        body = pre ++ .square d a :: post →
        pre.foldlM (step P.src) ρ = some ρ' → ρ' a = some x → x.parts = 2) →
      (∀ (pre post : List Instr) (d a : Var) (ρ' : Env P.src) (x : Val P.src),
        body = pre ++ .modSwitch d a :: post →
        pre.foldlM (step P.src) ρ = some ρ' → ρ' a = some x → x.parts = 2) →
      body.foldlM (step P.src) ρ = some ρf →
      ∃ σf, bfvRun P lay rk gk body (zenv ρ) σ = some σf ∧ TraceBFV.RunAt P E s n body ρ σ σf
  | [], _, _, _, σ, _, _, _, _, _, _, _, _ => ⟨σ, rfl, rfl⟩
  | i :: is, n, ρ, ρf, σ, hsh, hlv, hneed, hrot, hmul, hsq, hms, h => by
    simp only [List.foldlM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨ρ', hstep, hrest⟩ := h
    have hz := (Validation.BFV.SoundAux.step_zenv hk (Validation.IndCpaD.allExact_all ρ) i).1
    rw [hstep, Option.map_some] at hz
    rw [Validation.Profile.needAux_cons, hz, Bool.and_eq_true] at hneed
    have hn2 : needAux P lay U r E (n + 1) is (zenv ρ') = true := hneed.2
    have hn1 := hneed.1
    have hb : bfvNeedAt P lay rots (E n) (zenv ρ) i = true := by
      cases i
      case mul d a b =>
        have hn : (decide (BudgetBFV.mulLiftApprox P U ≤ (E n).mulLift) &&
            decide (BudgetBFV.mulRoundApprox P r ≤ (E n).mulRound)) = true := hn1
        simp only [Bool.and_eq_true, BudgetBFV.mulLiftApprox, BudgetBFV.mulRoundApprox] at hn
        show ((zenv ρ a).elim true fun x => (zenv ρ b).elim true fun y =>
          decide (BudgetBFV.mulLift P ≤ (E n).mulLift) &&
            decide (BudgetBFV.mulRound P ≤ (E n).mulRound) &&
            decide (x.parts = 2) && decide (y.parts = 2)) = true
        rcases hx : ρ a with _ | x
        · simp [zenv, hx]
        rcases hy : ρ b with _ | y
        · simp [zenv, hx, hy]
        have hzx : zenv ρ a = some (zv x) := by simp [zenv, hx]
        have hzy : zenv ρ b = some (zv y) := by simp [zenv, hy]
        rw [hzx, hzy]
        obtain ⟨h2x, h2y⟩ := hmul [] is d a b ρ x y rfl rfl hx hy
        show (decide (BudgetBFV.mulLift P ≤ (E n).mulLift) &&
          decide (BudgetBFV.mulRound P ≤ (E n).mulRound) &&
          decide (x.parts = 2) && decide (y.parts = 2)) = true
        simp only [Bool.and_eq_true, decide_eq_true_eq]
        exact ⟨⟨⟨(Nat.le_add_right _ _).trans (of_decide_eq_true hn.1),
          (Nat.le_mul_of_pos_left _ hr).trans (of_decide_eq_true hn.2)⟩, h2x⟩, h2y⟩
      case square d a =>
        have hn : (decide (BudgetBFV.mulLiftApprox P U ≤ (E n).mulLift) &&
            decide (BudgetBFV.mulRoundApprox P r ≤ (E n).mulRound)) = true := hn1
        simp only [Bool.and_eq_true, BudgetBFV.mulLiftApprox, BudgetBFV.mulRoundApprox] at hn
        show ((zenv ρ a).elim true fun x =>
          decide (BudgetBFV.mulLift P ≤ (E n).mulLift) &&
            decide (BudgetBFV.mulRound P ≤ (E n).mulRound) && decide (x.parts = 2)) = true
        rcases hx : ρ a with _ | x
        · simp [zenv, hx]
        have hzx : zenv ρ a = some (zv x) := by simp [zenv, hx]
        rw [hzx]
        have h2x := hsq [] is d a ρ x rfl rfl hx
        show (decide (BudgetBFV.mulLift P ≤ (E n).mulLift) &&
          decide (BudgetBFV.mulRound P ≤ (E n).mulRound) && decide (x.parts = 2)) = true
        simp only [Bool.and_eq_true, decide_eq_true_eq]
        exact ⟨⟨(Nat.le_add_right _ _).trans (of_decide_eq_true hn.1), (Nat.le_mul_of_pos_left _ hr).trans (of_decide_eq_true hn.2)⟩, h2x⟩
      case relin d a =>
        have hn : decide (BudgetBFV.ksBoundAt P lay (levelOf (zenv ρ) a) ≤ (E n).keySwitch)
          = true := hn1
        show ((zenv ρ a).elim true fun x =>
          decide (BudgetBFV.ksBoundAt P lay x.level ≤ (E n).keySwitch)) = true
        rcases hx : ρ a with _ | x
        · simp [zenv, hx]
        have hzx : zenv ρ a = some (zv x) := by simp [zenv, hx]
        rw [hzx]
        rw [Validation.CertifyBFV.levelOf_zenv, Validation.CertifyBFV.levelOf_some hx] at hn
        exact hn
      case keySwitch d a =>
        have hn : decide (BudgetBFV.ksBoundAt P lay (levelOf (zenv ρ) a) ≤ (E n).keySwitch)
          = true := hn1
        show ((zenv ρ a).elim true fun x =>
          decide (BudgetBFV.ksBoundAt P lay x.level ≤ (E n).keySwitch) &&
            decide (x.key ∈ rots)) = true
        rcases hx : ρ a with _ | x
        · simp [zenv, hx]
        have hzx : zenv ρ a = some (zv x) := by simp [zenv, hx]
        rw [hzx]
        rw [Validation.CertifyBFV.levelOf_zenv, Validation.CertifyBFV.levelOf_some hx] at hn
        exact (Bool.and_eq_true _ _).mpr ⟨hn, decide_eq_true (hrot [] is d a ρ x rfl rfl hx)⟩
      case modSwitch d a =>
        have hn : decide (BudgetBFV.msBudget P ≤ (E n).modSwitch) = true := hn1
        show ((zenv ρ a).elim true fun x =>
          decide (BudgetBFV.msBudget P ≤ (E n).modSwitch) && decide (x.parts = 2)) = true
        rcases hx : ρ a with _ | x
        · simp [zenv, hx]
        have hzx : zenv ρ a = some (zv x) := by simp [zenv, hx]
        rw [hzx]
        exact (Bool.and_eq_true _ _).mpr ⟨hn, decide_eq_true (hms [] is d a ρ x rfl rfl hx)⟩
      all_goals rfl
    obtain ⟨σ', he, hok⟩ := Validation.IndCpaDLM.bfv_step (P := P) (lay := lay) (rots := rots)
      (E := E n) (s := s) (rk := rk) (gk := gk) hk hP hside hs hkeys i hsh hlv hb hstep
    have shift : ∀ {pre post : List Instr} {j : Instr}, is = pre ++ j :: post →
        i :: is = (i :: pre) ++ j :: post := fun hb' => by rw [hb']; rfl
    have shiftF : ∀ {pre : List Instr} {ρ'' : Env P.src},
        pre.foldlM (step P.src) ρ' = some ρ'' → (i :: pre).foldlM (step P.src) ρ = some ρ'' :=
      fun hf => by rw [List.foldlM_cons, hstep]; exact hf
    obtain ⟨σf, hf, hrun⟩ := bfv_run_at hk hP hside hs hkeys hr is (n + 1) ρ' ρf σ'
      (Validation.IndCpaDLM.shape_step_bfv hsh hstep hok) (levels_step hlv hstep) hn2
      (fun pre post d a ρ'' x hb' hf hx => hrot (i :: pre) post d a ρ'' x (shift hb') (shiftF hf) hx)
      (fun pre post d a b ρ'' x y hb' hf hx hy =>
        hmul (i :: pre) post d a b ρ'' x y (shift hb') (shiftF hf) hx hy)
      (fun pre post d a ρ'' x hb' hf hx => hsq (i :: pre) post d a ρ'' x (shift hb') (shiftF hf) hx)
      (fun pre post d a ρ'' x hb' hf hx => hms (i :: pre) post d a ρ'' x (shift hb') (shiftF hf) hx)
      hrest
    refine ⟨σf, ?_, ρ', σ', hstep, hok, hrun⟩
    show (step P.src (zenv ρ) i).bind (fun ρ0' => (bfvStep P lay rk gk (zenv ρ) σ i).bind
      fun σ' => bfvRun P lay rk gk is ρ0' σ') = _
    rw [hz, Option.bind_some, he, Option.bind_some]
    exact hf

end BFV

theorem achieve_bfv (P : FullParams) (E : ℕ → TraceBFV.Budget) (prog : Program) (B : ℕ)
    (outs : List (Var × ℕ)) (h : certifyBFVProfile? P E prog = some (B, outs))
    (lay : Budget.KSLayout) (U r : ℕ) (hc : coversBFVAt? P lay U r prog E = true) (hr : 1 ≤ r)
    (hdecl : ksDeclOK? P lay = true) (rots : List ℕ)
    (s : IntPoly P.src.N) (hs : SecretOK P.secretBound s)
    (rk : ℕ → List (IntPoly P.src.N × IntPoly P.src.N))
    (gk : ℕ → ℕ → List (IntPoly P.src.N × IntPoly P.src.N))
    (hkeys : ∀ ℓ, 1 ≤ ℓ → ℓ ≤ P.src.qs.length →
      Budget.GadgetKeysOK P lay ℓ .square s (rk ℓ) ∧
      ∀ g ∈ rots, Budget.GadgetKeysOK P lay ℓ (.galois g) s (gk g ℓ))
    (msgs : Var → Msg P.src.t P.src.N) (cts : Var → List (IntPoly P.src.N))
    (hin : TraceBFV.InputsOK P s prog msgs cts)
    (hrot : ∀ (pre post : List Instr) (d a : Var) (ρ : Env P.src) (x : Val P.src),
      prog.body = pre ++ .keySwitch d a :: post →
      pre.foldlM (step P.src) (initEnv P.src prog msgs) = some ρ → ρ a = some x → x.key ∈ rots)
    (hmul : ∀ (pre post : List Instr) (d a b : Var) (ρ : Env P.src) (x y : Val P.src),
      prog.body = pre ++ .mul d a b :: post →
      pre.foldlM (step P.src) (initEnv P.src prog msgs) = some ρ → ρ a = some x → ρ b = some y →
      x.parts = 2 ∧ y.parts = 2)
    (hsq : ∀ (pre post : List Instr) (d a : Var) (ρ : Env P.src) (x : Val P.src),
      prog.body = pre ++ .square d a :: post →
      pre.foldlM (step P.src) (initEnv P.src prog msgs) = some ρ → ρ a = some x → x.parts = 2)
    (hms : ∀ (pre post : List Instr) (d a : Var) (ρ : Env P.src) (x : Val P.src),
      prog.body = pre ++ .modSwitch d a :: post →
      pre.foldlM (step P.src) (initEnv P.src prog msgs) = some ρ → ρ a = some x → x.parts = 2) :
    ∃ σf, bfvRun P lay rk gk prog.body (initEnv P.src prog fun _ => .exact 0)
        (Trace.initCt P prog cts) = some σf ∧
      TraceBFV.RunAt P E s 0 prog.body (initEnv P.src prog msgs) (Trace.initCt P prog cts) σf ∧
      ∃ ρ, Source.eval P.src prog msgs = some ρ ∧
        ∀ o ∈ prog.outputs, ∃ v ct m b, ρ o = some v ∧ σf o = some ct ∧
          outs.lookup o = some b ∧ Encrypts P s b v ct ∧ v.msg = .exact m ∧ v.key = 1 ∧
          bfvDecrypt P.src.t s (ct.map (ofInt (P.src.modulus v.level))) = m := by
  obtain ⟨hP, hk, -⟩ := Validation.Profile.certifyBFVProfile?_some h
  obtain ⟨ρ, hρ, hall⟩ :=
    Validation.Profile.certifyBFVProfile?_sound P E prog B outs h s msgs cts hin
  have hρ' := hρ
  simp only [Source.eval, Option.bind_eq_bind, Option.pure_def] at hρ'
  obtain ⟨hdecl', hρ'⟩ := Validation.Trace.guard_bind_eq_some hρ'
  obtain ⟨-, hρ'⟩ := Validation.Trace.guard_bind_eq_some hρ'
  obtain ⟨ρf, hbody, -⟩ := Option.bind_eq_some_iff.mp hρ'
  have hsh : Shape P (initEnv P.src prog msgs) (Trace.initCt P prog cts) := by
    intro x v hv
    simp only [initEnv, Option.map_eq_some_iff] at hv
    obtain ⟨d, hd, rfl⟩ := hv
    have h1 := hin x d hd
    refine ⟨cts x, by simp [Trace.initCt, hd], ?_⟩
    split_ifs at h1
    · exact h1.1
    · exact h1.1
  have hlv : Levels P (initEnv P.src prog msgs) := by
    intro x v hv
    simp only [initEnv, Option.map_eq_some_iff] at hv
    obtain ⟨d, hd, rfl⟩ := hv
    have hok := List.all_eq_true.mp hdecl' d (List.mem_of_find?_eq_some hd)
    simp only [Decl.ok, decide_eq_true_eq] at hok
    exact ⟨hok.2.1, hok.2.2.1⟩
  have hz0 : zenv (initEnv P.src prog msgs) = initEnv P.src prog fun _ => .exact 0 := by
    funext x; simp only [zenv, initEnv, Option.map_map]; rfl
  have hc' := hc
  rw [Validation.Profile.coversBFVAt?_eq] at hc'
  simp only [Bool.and_eq_true] at hc'
  obtain ⟨⟨⟨⟨-, -⟩, hsp⟩, hall'⟩, hneed⟩ := hc'
  have hside : bfvSide P lay = true := by
    change (Budget.specialOK? P && ksDeclOK? P lay &&
      (List.range P.src.qs.length).all fun j => lay.okAt (j + 1)) = true
    simp [hsp, hdecl, hall']
  rw [← hz0] at hneed
  obtain ⟨σf, hf, hrun⟩ := bfv_run_at (U := U) (E := E) (rots := rots) (rk := rk) (gk := gk)
    hk hP hside hs hkeys hr prog.body 0 _ ρf _ hsh hlv hneed hrot hmul hsq hms hbody
  rw [hz0] at hf
  exact ⟨σf, hf, hrun, ρ, hρ, hall σf hrun⟩

example := (@bfvRun_eq_irun : type_of% @Challenge.ProfileAchieve.bfvRun_eq_irun)
example := (@achieve_bgv : type_of% @Challenge.ProfileAchieve.achieve_bgv)
example := (@achieve_bfv : type_of% @Challenge.ProfileAchieve.achieve_bfv)

end Validation.ProfileAchieve
