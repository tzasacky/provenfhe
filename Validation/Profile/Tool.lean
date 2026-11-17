import Challenge.Profile.Tool
import Validation.Profile
import Validation.IndCpaD.Levels

/-!
# Validation.Profile.Tool — proofs of the pins of `Challenge.Profile.Tool`

The tools' decisions are decomposed by the existing lemmas (`Validation.Certify.certify?_checked`,
`checked?_some`, `Validation.CertifyBFV.certifyBFV?_some`, `checks`); every guard of the profile
functions is one of their checks. The level-exact coverage of the computed BFV budget is an
induction along the replay that computes it (`budgetsAux`), with one fact per instruction
(`need_stepBudget`). The realizability corollaries read `needAt` at the position of the
instruction in a run on any messages: the zero-message replay reaches `zenv ρ`
(`Validation.IndCpaD.foldlM_zenv`), which has the same levels. No locked definition is unfolded
by name: they are read through `change`, `show` and local `rfl` equations.
-/

namespace Validation.Profile
open Spec NPoly Scheme Source Correct Challenge.Headline Challenge.Certify Challenge.CertifyBFV
  Challenge.BFV Challenge.BFVMul Challenge.Profile Spec.Certify Spec.CertifyBFV

/-! ## BGV -/

theorem certify?_profile (x : Input) (c : Certificate) (h : certify? x = some c) :
    certifyProfile? c.params c.budget x.prog x.switched = some (c.bound, c.outputs) := by
  obtain ⟨hE, hch⟩ := Validation.Certify.certify?_checked h
  obtain ⟨h1, -, -, hout, hB, ho, -, hI⟩ := Validation.Certify.checked?_some hch
  obtain ⟨-, hk, -⟩ := Validation.Certify.certify?_paramsOK x c h
  rw [hE]
  change (do
    guard (schemeParamsOK? c.params)
    guard (c.params.src.kind = .bgv)
    guard (!x.prog.outputs.isEmpty)
    guard (Challenge.Certify.inputsMsgOK? c.params x.prog)
    let B ← refAnalyze c.params (Spec.Budget.certified c.params x.lay) x.prog
    let outs ← x.prog.outputs.mapM fun o =>
      (outputBound? c.params (Spec.Budget.certified c.params x.lay) x.prog x.switched o).map
        fun b => (o, b)
    pure (B, outs)) = some (c.bound, c.outputs)
  have he : x.prog.outputs.isEmpty = false := by
    cases hl : x.prog.outputs with
    | nil => exact absurd hl hout
    | cons _ _ => rfl
  simp [guard, h1, hk, he, hI, hB, ho]

theorem certify?_covers (x : Input) (c : Certificate) (h : certify? x = some c) (K : ℕ) :
    coversBGV? c.params x.lay K c.budget = true := by
  obtain ⟨hE, hch⟩ := Validation.Certify.certify?_checked h
  obtain ⟨h1, h2, -⟩ := Validation.Certify.checked?_some hch
  obtain ⟨-, hk, -, hlay⟩ := Validation.Certify.certify?_paramsOK x c h
  change (schemeParamsOK? c.params && decide (c.params.src.kind = .bgv) &&
    Spec.Budget.specialOK? c.params &&
    (List.range c.params.src.qs.length).all (fun j =>
      x.lay.okAt (j + 1) &&
        decide (Spec.Budget.ksBoundAt c.params x.lay (j + 1) ≤ c.budget.keySwitch)) &&
    (List.range K).all fun j =>
      decide (Spec.Budget.msBudgetAt c.params (j + 1) ≤ c.budget.modSwitchAt (j + 1))) = true
  rw [hE]
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range]
  refine ⟨⟨⟨⟨h1, hk⟩, h2⟩, fun j hj => ⟨(hlay (j + 1) (by omega) (by omega)).1, ?_⟩⟩,
    fun j _ => ?_⟩
  · exact Validation.Budget.ksBoundAt_le_ksBudget c.params x.lay (j + 1) (by omega) (by omega)
  · rw [Validation.Budget.certified_modSwitchAt]

/-! ## BFV: profile acceptance -/

theorem certifyBFV?_profile (x : InputBFV) (c : CertificateBFV) (h : certifyBFV? x = some c) :
    certifyBFVProfile? x.P c.budget x.prog = some (c.bound, c.outputs) := by
  have hc := Validation.CertifyBFV.checks h
  obtain ⟨-, B, outs, hB, hU, ho, rfl⟩ := Validation.CertifyBFV.certifyBFV?_some h
  have hdec : inputsDecOK x.P x.prog = true := by
    change (x.prog.inputs.all fun d => decide (d.parts = 1) || !d.ok x.P.src ||
      decOK x.P.src.t (x.P.src.modulus d.level) (TraceBFV.inputBound x.P x.prog d)) = true
    apply List.all_eq_true.mpr
    intro d hd
    by_cases hp : d.parts = 1
    · simp [hp]
    · by_cases hok : d.ok x.P.src = true
      · simp [hp, hok, hc.inputs d hd hp hok]
      · simp [hp, hok]
  have he : x.prog.outputs.isEmpty = false := by
    cases hl : x.prog.outputs with
    | nil => exact absurd hl hc.outs
    | cons _ _ => rfl
  change (do
    guard (schemeParamsOK? x.P)
    guard (x.P.src.kind = .bfv)
    guard (!x.prog.outputs.isEmpty)
    guard (inputsDecOK x.P x.prog)
    guard (Challenge.CertifyBFV.plainBoundsOK x.P x.prog)
    guard (x.P.src.t - 1 ≤ x.P.src.qs.headD 0 / 2)
    let B ← refAnalyzeBFVAt x.P (budgetBFV x) x.prog
    guard (Encrypt.outputsUnderS? x.P.src x.prog)
    let outs ← x.prog.outputs.mapM fun o =>
      (refAnalyzeBFVAt x.P (budgetBFV x) { x.prog with outputs := [o] }).map fun b => (o, b)
    pure (B, outs)) = some (B, outs)
  have hen : x.P.src.t ≤ x.P.src.qs.head?.getD 0 / 2 + 1 := by
    have h := hc.encode.1
    simp only [List.headD_eq_head?_getD] at h
    omega
  simp [guard, hc.params, hc.kind, he, hdec, hc.plain, hen, hB, hU, ho]

/-! ## BFV: the level-exact check -/

theorem needAux_cons (P : FullParams) (lay : Budget.KSLayout) (U r : ℕ) (E : ℕ → TraceBFV.Budget)
    (n : ℕ) (i : Instr) (is : List Instr) (ρ : Env P.src) :
    needAux P lay U r E n (i :: is) ρ =
      (needAt P lay U r (E n) ρ i &&
        match step P.src ρ i with
        | some ρ' => needAux P lay U r E (n + 1) is ρ'
        | none => true) := rfl

theorem coversBFVAt?_eq (P : FullParams) (lay : Budget.KSLayout) (U r : ℕ) (prog : Program)
    (E : ℕ → TraceBFV.Budget) :
    coversBFVAt? P lay U r prog E =
      (schemeParamsOK? P && decide (P.src.kind = .bfv) && Budget.specialOK? P &&
        (List.range P.src.qs.length).all (fun j => lay.okAt (j + 1)) &&
        needAux P lay U r E 0 prog.body (initEnv P.src prog fun _ => .exact 0)) := rfl

/-- What the computed budget of one instruction gives the textbook family. -/
theorem need_stepBudget (x : InputBFV) (ρ : Env x.P.src) (dr : ℕ) (i : Instr) :
    needAt x.P x.lay 0 1 (stepBudget x ρ dr i) ρ i = true := by
  have hL : BudgetBFV.mulLiftApprox x.P 0 ≤ (stepBudget x ρ dr i).mulLift := by
    have e : BudgetBFV.mulLiftApprox x.P 0 = BudgetBFV.mulLift x.P := by
      simp [BudgetBFV.mulLiftApprox]
    rw [e]
    exact le_max_left _ _
  have hR : BudgetBFV.mulRoundApprox x.P 1 ≤ (stepBudget x ρ dr i).mulRound :=
    Nat.mul_le_mul_right _ (le_max_left 1 _)
  have hM : BudgetBFV.msBudget x.P ≤ (stepBudget x ρ dr i).modSwitch := le_refl _
  cases i with
  | mul d a b => exact (Bool.and_eq_true _ _).mpr ⟨decide_eq_true hL, decide_eq_true hR⟩
  | square d a => exact (Bool.and_eq_true _ _).mpr ⟨decide_eq_true hL, decide_eq_true hR⟩
  | relin d a => exact decide_eq_true (Validation.CertifyBFV.ksBoundAt_le_ksAt x _ dr _)
  | keySwitch d a => exact decide_eq_true (Validation.CertifyBFV.ksBoundAt_le_ksAt x _ dr _)
  | modSwitch d a => exact decide_eq_true hM
  | _ => rfl

theorem needAux_of_budgets (x : InputBFV) (E : ℕ → TraceBFV.Budget) :
    ∀ (body : List Instr) (ds : List ℕ) (ρ : Env x.P.src) (n : ℕ),
      (∀ j b, (budgetsAux x body ds ρ)[j]? = some b → E (n + j) = b) →
      needAux x.P x.lay 0 1 E n body ρ = true
  | [], _, _, _, _ => rfl
  | i :: is, ds, ρ, n, hb => by
    rw [needAux_cons]
    have h0 : E n = stepBudget x ρ (ds.headD 0) i := by
      have := hb 0 (stepBudget x ρ (ds.headD 0) i) (by rw [Validation.CertifyBFV.budgetsAux_cons]; rfl)
      simpa using this
    rw [h0, need_stepBudget, Bool.true_and]
    rcases hs : step x.P.src ρ i with _ | ρ'
    · rfl
    · apply needAux_of_budgets x E is ds.tail ρ' (n + 1)
      intro j b hj
      have e : budgetsAux x (i :: is) ds ρ =
          stepBudget x ρ (ds.headD 0) i :: budgetsAux x is ds.tail ρ' := by
        rw [Validation.CertifyBFV.budgetsAux_cons, hs]
      have := hb (j + 1) b (by rw [e]; simpa using hj)
      rwa [show n + (j + 1) = n + 1 + j by omega] at this

theorem certifyBFV?_coversAt (x : InputBFV) (c : CertificateBFV) (h : certifyBFV? x = some c) :
    coversBFVAt? x.P x.lay 0 1 x.prog c.budget = true := by
  have hc := Validation.CertifyBFV.checks h
  obtain ⟨-, -, -, hlay, -⟩ := Validation.CertifyBFV.certifyBFV?_paramsOK x c h
  obtain ⟨-, B, outs, -, -, -, rfl⟩ := Validation.CertifyBFV.certifyBFV?_some h
  rw [coversBFVAt?_eq]
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range]
  refine ⟨⟨⟨⟨hc.params, hc.kind⟩, hc.special⟩, fun j hj => (hlay (j + 1) (by omega) (by omega)).1⟩,
    ?_⟩
  apply needAux_of_budgets x _ x.prog.body (dropsOf x) _ 0
  intro j b hj
  show budgetFn (budgetsBFV x).toArray (0 + j) = b
  rw [Validation.CertifyBFV.budgetFn_toArray, Nat.zero_add]
  show ((budgetsAux x x.prog.body (dropsOf x) (initEnv x.P.src x.prog fun _ => .exact 0))[j]?).getD _ = b
  rw [hj]; rfl

/-! ## Realizability under the level-exact check -/

theorem coversBFVAt?_facts {P : FullParams} {lay : Budget.KSLayout} {U r : ℕ} {prog : Program}
    {E : ℕ → TraceBFV.Budget} (hc : coversBFVAt? P lay U r prog E = true) :
    SchemeParamsOK P ∧ P.src.kind = .bfv ∧ Budget.SpecialOK P ∧
      (∀ ℓ, 1 ≤ ℓ → ℓ ≤ P.src.qs.length → lay.okAt ℓ = true) ∧
      needAux P lay U r E 0 prog.body (initEnv P.src prog fun _ => .exact 0) = true := by
  rw [coversBFVAt?_eq] at hc
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at hc
  obtain ⟨⟨⟨⟨h1, hk⟩, h2⟩, h3⟩, h4⟩ := hc
  refine ⟨Validation.Params.schemeParamsOK?_sound P h1, hk,
    Validation.Budget.specialOK?_sound P h2, fun ℓ hℓ1 hℓ => ?_, h4⟩
  have := h3 (ℓ - 1) (by omega)
  rwa [Nat.sub_add_cancel hℓ1] at this

theorem needAux_at {P : FullParams} {lay : Budget.KSLayout} {U r : ℕ} {E : ℕ → TraceBFV.Budget}
    (i : Instr) (post : List Instr) :
    ∀ (pre : List Instr) (n : ℕ) (ρ0 ρ : Env P.src),
      needAux P lay U r E n (pre ++ i :: post) ρ0 = true →
      pre.foldlM (step P.src) ρ0 = some ρ →
      needAt P lay U r (E (n + pre.length)) ρ i = true
  | [], n, ρ0, ρ, h, hf => by
    cases (Option.some.inj hf : ρ0 = ρ)
    rw [List.nil_append, needAux_cons] at h
    exact ((Bool.and_eq_true _ _).mp h).1
  | j :: pre, n, ρ0, ρ, h, hf => by
    rw [List.foldlM_cons] at hf
    obtain ⟨ρ1, h1, hf⟩ := Option.bind_eq_some_iff.mp hf
    rw [List.cons_append, needAux_cons, h1] at h
    have := needAux_at i post pre (n + 1) ρ1 ρ ((Bool.and_eq_true _ _).mp h).2 hf
    rwa [show n + 1 + pre.length = n + (j :: pre).length by simp; omega] at this

open Validation.BFV.SoundAux in
theorem need_run {P : FullParams} {lay : Budget.KSLayout} {U r : ℕ} {prog : Program}
    {E : ℕ → TraceBFV.Budget} (hc : coversBFVAt? P lay U r prog E = true)
    {msgs : Var → Msg P.src.t P.src.N} {pre post : List Instr} {i : Instr} {ρ : Env P.src}
    (hbody : prog.body = pre ++ i :: post)
    (hρ : pre.foldlM (step P.src) (initEnv P.src prog msgs) = some ρ) :
    needAt P lay U r (E pre.length) (zenv ρ) i = true := by
  obtain ⟨-, hk, -, -, hn⟩ := coversBFVAt?_facts hc
  have hz0 : zenv (initEnv P.src prog msgs) = initEnv P.src prog fun _ => .exact 0 := by
    funext y; simp only [zenv, initEnv, Option.map_map]; rfl
  have hz := Validation.IndCpaD.foldlM_zenv hk pre (initEnv P.src prog msgs)
  rw [hρ, hz0] at hz
  rw [hbody] at hn
  have := needAux_at i post pre 0 _ _ hn hz
  rwa [Nat.zero_add] at this

theorem coversBFVAt?_mul (P : FullParams) (lay : Budget.KSLayout) (U r : ℕ) (prog : Program)
    (E : ℕ → TraceBFV.Budget) (hc : coversBFVAt? P lay U r prog E = true)
    (msgs : Var → Msg P.src.t P.src.N) (pre post : List Instr) (d a b : Var) (ρ ρ' : Env P.src)
    (hbody : prog.body = pre ++ .mul d a b :: post)
    (hρ : pre.foldlM (step P.src) (initEnv P.src prog msgs) = some ρ)
    (s : IntPoly P.src.N) (hs : SecretOK P.secretBound s)
    (σ : Trace.CtEnv P) (x y : Val P.src) (ca cb : List (IntPoly P.src.N))
    (hstep : step P.src ρ (.mul d a b) = some ρ') (hx : ρ a = some x) (hy : ρ b = some y)
    (ha : σ a = some ca) (hb : σ b = some cb)
    (hla : ca.length = 2) (hlb : cb.length = 2) (h2x : x.parts = 2) (h2y : y.parts = 2)
    (hℓ : 1 ≤ x.level) (hℓL : x.level ≤ P.src.qs.length)
    (ua ub X out : List (IntPoly P.src.N))
    (hua : ua.length = 2) (hub : ub.length = 2) (hX : X.length = 3)
    (hUa : ∀ u ∈ ua, normInf u ≤ U) (hUb : ∀ u ∈ ub, normInf u ≤ U)
    (hround : ∀ (j : ℕ) (i : Fin P.src.N),
      2 * |(P.src.modulus x.level : ℤ) * (X.getD j 0).coeff i -
          (P.src.t : ℤ) * ((Challenge.Source.tensor (approxLift (P.src.modulus x.level) ca ua)
            (approxLift (P.src.modulus x.level) cb ub)).getD j 0).coeff i|
        ≤ (P.src.modulus x.level : ℤ) * r)
    (hout : out.map (ofInt (P.src.modulus x.level)) = X.map (ofInt (P.src.modulus x.level))) :
    TraceBFV.StepOK P (E pre.length) s ρ ρ' σ (σ.set d out) (.mul d a b) := by
  obtain ⟨hP, -⟩ := coversBFVAt?_facts hc
  have hn : (decide (BudgetBFV.mulLiftApprox P U ≤ (E pre.length).mulLift) &&
      decide (BudgetBFV.mulRoundApprox P r ≤ (E pre.length).mulRound)) = true :=
    need_run hc hbody hρ
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hn
  exact Validation.BFVMul.stepOK_mul_approx P hP U r (E pre.length) hn.1 hn.2 s hs ρ ρ' σ d a b x
    y ca cb hstep hx hy ha hb hla hlb h2x h2y hℓ hℓL ua ub X out hua hub hX hUa hUb hround hout

theorem coversBFVAt?_square (P : FullParams) (lay : Budget.KSLayout) (U r : ℕ) (prog : Program)
    (E : ℕ → TraceBFV.Budget) (hc : coversBFVAt? P lay U r prog E = true)
    (msgs : Var → Msg P.src.t P.src.N) (pre post : List Instr) (d a : Var) (ρ ρ' : Env P.src)
    (hbody : prog.body = pre ++ .square d a :: post)
    (hρ : pre.foldlM (step P.src) (initEnv P.src prog msgs) = some ρ)
    (s : IntPoly P.src.N) (hs : SecretOK P.secretBound s)
    (σ : Trace.CtEnv P) (x : Val P.src) (ca : List (IntPoly P.src.N))
    (hstep : step P.src ρ (.square d a) = some ρ') (hx : ρ a = some x)
    (ha : σ a = some ca) (hla : ca.length = 2) (h2x : x.parts = 2)
    (hℓ : 1 ≤ x.level) (hℓL : x.level ≤ P.src.qs.length)
    (ua X out : List (IntPoly P.src.N))
    (hua : ua.length = 2) (hX : X.length = 3) (hUa : ∀ u ∈ ua, normInf u ≤ U)
    (hround : ∀ (j : ℕ) (i : Fin P.src.N),
      2 * |(P.src.modulus x.level : ℤ) * (X.getD j 0).coeff i -
          (P.src.t : ℤ) * ((Challenge.Source.tensor (approxLift (P.src.modulus x.level) ca ua)
            (approxLift (P.src.modulus x.level) ca ua)).getD j 0).coeff i|
        ≤ (P.src.modulus x.level : ℤ) * r)
    (hout : out.map (ofInt (P.src.modulus x.level)) = X.map (ofInt (P.src.modulus x.level))) :
    TraceBFV.StepOK P (E pre.length) s ρ ρ' σ (σ.set d out) (.square d a) := by
  obtain ⟨hP, -⟩ := coversBFVAt?_facts hc
  have hn : (decide (BudgetBFV.mulLiftApprox P U ≤ (E pre.length).mulLift) &&
      decide (BudgetBFV.mulRoundApprox P r ≤ (E pre.length).mulRound)) = true :=
    need_run hc hbody hρ
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hn
  exact Validation.BFVMul.stepOK_square_approx P hP U r (E pre.length) hn.1 hn.2 s hs ρ ρ' σ d a
    x ca hstep hx ha hla h2x hℓ hℓL ua X out hua hX hUa hround hout

open Validation.BFV.SoundAux in
theorem coversBFVAt?_relin (P : FullParams) (lay : Budget.KSLayout) (U r : ℕ) (prog : Program)
    (E : ℕ → TraceBFV.Budget) (hc : coversBFVAt? P lay U r prog E = true) (ℓ : ℕ)
    (h1 : 1 ≤ ℓ) (hℓ : ℓ ≤ P.src.qs.length) :
    ∃ f : List (IntPoly P.src.N) → List (IntPoly P.src.N × IntPoly P.src.N) →
        List (IntPoly P.src.N),
      ∀ (msgs : Var → Msg P.src.t P.src.N) (pre post : List Instr) (d a : Var) (ρ : Env P.src),
        prog.body = pre ++ .relin d a :: post →
        pre.foldlM (step P.src) (initEnv P.src prog msgs) = some ρ →
      ∀ (s : IntPoly P.src.N), SecretOK P.secretBound s →
      ∀ (keys : List (IntPoly P.src.N × IntPoly P.src.N)),
        Budget.GadgetKeysOK P lay ℓ .square s keys →
      ∀ (ρ' : Env P.src) (σ : Trace.CtEnv P) (x : Val P.src) (ca : List (IntPoly P.src.N)),
        step P.src ρ (.relin d a) = some ρ' → ρ a = some x → σ a = some ca → x.level = ℓ →
        ca.length = x.parts →
        TraceBFV.StepOK P (E pre.length) s ρ ρ' σ (σ.set d (f ca keys)) (.relin d a) := by
  obtain ⟨hP, -, hS, hlay, -⟩ := coversBFVAt?_facts hc
  obtain ⟨f, hf⟩ := Validation.BFV.relin_realizable P lay hP hS ℓ hℓ (hlay ℓ h1 hℓ)
  refine ⟨f, fun msgs pre post d a ρ hbody hρ s hs keys hkeys ρ' σ x ca e1 e2 e3 e4 e5 => ?_⟩
  have hn : decide (BudgetBFV.ksBoundAt P lay (levelOf (zenv ρ) a) ≤ (E pre.length).keySwitch)
      = true := need_run hc hbody hρ
  rw [Validation.CertifyBFV.levelOf_zenv, Validation.CertifyBFV.levelOf_some e2, e4,
    decide_eq_true_eq] at hn
  exact hf (E pre.length) hn s hs keys hkeys ρ ρ' σ d a x ca e1 e2 e3 e4 e5

open Validation.BFV.SoundAux in
theorem coversBFVAt?_keySwitch (P : FullParams) (lay : Budget.KSLayout) (U r : ℕ)
    (prog : Program) (E : ℕ → TraceBFV.Budget) (hc : coversBFVAt? P lay U r prog E = true)
    (ℓ : ℕ) (h1 : 1 ≤ ℓ) (hℓ : ℓ ≤ P.src.qs.length) :
    ∃ f : List (IntPoly P.src.N) → List (IntPoly P.src.N × IntPoly P.src.N) →
        List (IntPoly P.src.N),
      ∀ (msgs : Var → Msg P.src.t P.src.N) (pre post : List Instr) (d a : Var) (ρ : Env P.src),
        prog.body = pre ++ .keySwitch d a :: post →
        pre.foldlM (step P.src) (initEnv P.src prog msgs) = some ρ →
      ∀ (s : IntPoly P.src.N), SecretOK P.secretBound s →
      ∀ (ρ' : Env P.src) (σ : Trace.CtEnv P) (x : Val P.src) (ca : List (IntPoly P.src.N)),
        step P.src ρ (.keySwitch d a) = some ρ' → ρ a = some x → σ a = some ca → x.level = ℓ →
        ca.length = x.parts →
      ∀ (keys : List (IntPoly P.src.N × IntPoly P.src.N)),
        Budget.GadgetKeysOK P lay ℓ (.galois x.key) s keys →
        TraceBFV.StepOK P (E pre.length) s ρ ρ' σ (σ.set d (f ca keys)) (.keySwitch d a) := by
  obtain ⟨hP, -, hS, hlay, -⟩ := coversBFVAt?_facts hc
  obtain ⟨f, hf⟩ := Validation.BFV.keySwitch_realizable P lay hP hS ℓ hℓ (hlay ℓ h1 hℓ)
  refine ⟨f, fun msgs pre post d a ρ hbody hρ s hs ρ' σ x ca e1 e2 e3 e4 e5 keys hkeys => ?_⟩
  have hn : decide (BudgetBFV.ksBoundAt P lay (levelOf (zenv ρ) a) ≤ (E pre.length).keySwitch)
      = true := need_run hc hbody hρ
  rw [Validation.CertifyBFV.levelOf_zenv, Validation.CertifyBFV.levelOf_some e2, e4,
    decide_eq_true_eq] at hn
  exact hf (E pre.length) hn s hs ρ ρ' σ d a x ca e1 e2 e3 e4 e5 keys hkeys

theorem coversBFVAt?_modSwitch (P : FullParams) (lay : Budget.KSLayout) (U r : ℕ)
    (prog : Program) (E : ℕ → TraceBFV.Budget) (hc : coversBFVAt? P lay U r prog E = true)
    (msgs : Var → Msg P.src.t P.src.N) (pre post : List Instr) (d a : Var) (ρ ρ' : Env P.src)
    (hbody : prog.body = pre ++ .modSwitch d a :: post)
    (hρ : pre.foldlM (step P.src) (initEnv P.src prog msgs) = some ρ)
    (s : IntPoly P.src.N) (hs : SecretOK P.secretBound s)
    (σ : Trace.CtEnv P) (x : Val P.src) (ca : List (IntPoly P.src.N))
    (hstep : step P.src ρ (.modSwitch d a) = some ρ') (hx : ρ a = some x)
    (ha : σ a = some ca) (hℓL : x.level ≤ P.src.qs.length) (h2 : x.parts = 2)
    (hla : ca.length = 2) :
    TraceBFV.StepOK P (E pre.length) s ρ ρ' σ
      (σ.set d (ca.map (bfvModSwitchComp P.src.qs[x.level - 1]!))) (.modSwitch d a) := by
  obtain ⟨hP, -⟩ := coversBFVAt?_facts hc
  have hn : decide (BudgetBFV.msBudget P ≤ (E pre.length).modSwitch) = true := need_run hc hbody hρ
  exact Validation.BFV.stepOK_modSwitch_textbook P hP (E pre.length) (decide_eq_true_eq.mp hn) s
    hs ρ ρ' σ d a x ca hstep hx ha hℓL h2 hla

example := (@certify?_profile : type_of% @Challenge.Profile.certify?_profile)
example := (@certify?_covers : type_of% @Challenge.Profile.certify?_covers)
example := (@certifyBFV?_profile : type_of% @Challenge.Profile.certifyBFV?_profile)
example := (@certifyBFV?_coversAt : type_of% @Challenge.Profile.certifyBFV?_coversAt)
example := (@coversBFVAt?_mul : type_of% @Challenge.Profile.coversBFVAt?_mul)
example := (@coversBFVAt?_square : type_of% @Challenge.Profile.coversBFVAt?_square)
example := (@coversBFVAt?_relin : type_of% @Challenge.Profile.coversBFVAt?_relin)
example := (@coversBFVAt?_keySwitch : type_of% @Challenge.Profile.coversBFVAt?_keySwitch)
example := (@coversBFVAt?_modSwitch : type_of% @Challenge.Profile.coversBFVAt?_modSwitch)

end Validation.Profile
