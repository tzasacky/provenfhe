import Validation.Budget.Restrict
import Challenge.CertifyBFV
import Validation.BFVMul.Float
import Validation.BFVMul.FloatSums
import Validation.BFVMul.KSLeveled
import Validation.Certify
import Validation.BFVMul.Cert
import Validation.BFVMul.HPS
import Validation.BFVMul.BEHZ
import Validation.BFVMul.POverQ
import Validation.BFVMul.Ops
import Validation.BFV.Textbook
import Validation.BFV.Sound
import Validation.BFV.Domain
import Validation.BFV.PerInstr

/-!
# Validation.CertifyBFV — proofs of the pins of `Challenge.CertifyBFV`

The budget of a certificate is one budget per instruction. The bridge (`at_facts`): if
`certifyBFV? x = some c` and `i` is instruction `n` of the program with the environment `ρ` in
front of it (`AtInstr`), then `c.budget n` is `stepBudget` at the level of the operand in `ρ` and
`stepChecks` passed there (the replay on all-zero messages reaches the zeroed `ρ`, which has the
same levels: `Validation.BFV.SoundAux.step_zenv`). Everything else is obtained from the existing
proofs: `Validation.BFVMul.certifiedAt_decrypts` and `Validation.BFV.refAnalyzeBFVAt_sound` for
soundness, and the realizability pins of `Validation.BFV` and `Validation.BFVMul` with their
hypotheses read off `stepBudget` and `stepChecks`.

`Challenge.*` definitions are unfolded through local `rfl` lemmas (and `cases` on the input).
-/

namespace Validation.CertifyBFV
open Spec NPoly Scheme Source Correct Spec.BudgetBFV Challenge.BFV Challenge.BFVMul
open Spec.CertifyBFV Challenge.CertifyBFV

/-! ## Unfolding `certifyBFV?` -/

theorem certifyBFV?_some {x : InputBFV} {c : CertificateBFV} (h : certifyBFV? x = some c) :
    checksOK x = true ∧ ∃ B outs, refAnalyzeBFVAt x.P (budgetBFV x) x.prog = some B ∧
      Encrypt.outputsUnderS? x.P.src x.prog = true ∧
      x.prog.outputs.mapM (fun o =>
        (refAnalyzeBFVAt x.P (budgetBFV x) { x.prog with outputs := [o] }).map fun b => (o, b)) =
          some outs ∧
      c = ⟨budgetBFV x, B, outs, mulLevels x.P.src x.prog, assumptionsOf x⟩ := by
  unfold certifyBFV? at h
  simp only [Option.bind_eq_bind, Option.pure_def] at h
  obtain ⟨h1, h⟩ := Validation.Trace.guard_bind_eq_some h
  obtain ⟨B, hB, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨h2, h⟩ := Validation.Trace.guard_bind_eq_some h
  obtain ⟨outs, ho, h⟩ := Option.bind_eq_some_iff.mp h
  cases h
  exact ⟨h1, B, outs, hB, h2, ho, rfl⟩

/-- The parts of `checksOK` the proofs use. -/
structure Checks (x : InputBFV) : Prop where
  params : schemeParamsOK? x.P = true
  kind : x.P.src.kind = .bfv
  special : Budget.specialOK? x.P = true
  layout : Spec.Certify.layoutOK? x.P x.lay = true
  outs : x.prog.outputs ≠ []
  inputs : ∀ d ∈ x.prog.inputs, d.parts ≠ 1 → d.ok x.P.src = true →
    decOK x.P.src.t (x.P.src.modulus d.level) (TraceBFV.inputBound x.P x.prog d) = true
  mulDecl : (x.mul.isSome || !x.prog.body.any isMul) = true
  encode : x.P.src.t - 1 ≤ x.P.src.qs.headD 0 / 2 ∧ ∀ q ∈ x.P.src.qs, x.P.src.t ≤ q
  ksDecl : Challenge.RealizeBFV.ksDeclOK? x.P x.lay = true
  aux : checksAux x x.prog.body (dropsOf x) (initEnv x.P.src x.prog fun _ => .exact 0) = true
  plain : plainBoundsOK x.P x.prog = true

theorem band {a b : Bool} (h : (a && b) = true) : a = true ∧ b = true := by
  cases a <;> cases b <;> simp_all

theorem checks_of {x : InputBFV} (h : checksOK x = true) : Checks x := by
  unfold checksOK at h
  obtain ⟨h, h12⟩ := band h
  obtain ⟨h, hKs⟩ := band h
  obtain ⟨h, hEnc⟩ := band h
  obtain ⟨h, -⟩ := band h
  obtain ⟨h, -⟩ := band h
  obtain ⟨h, -⟩ := band h
  obtain ⟨h, -⟩ := band h
  obtain ⟨h, h7⟩ := band h
  obtain ⟨h, hPl⟩ := band h
  obtain ⟨h, h6⟩ := band h
  obtain ⟨h, h5⟩ := band h
  obtain ⟨h, h4⟩ := band h
  obtain ⟨h, h3⟩ := band h
  obtain ⟨h1, h2⟩ := band h
  refine ⟨h1, by simpa using h2, h3, h4, by simpa using h5, fun d hd hp hok => ?_, h7,
    by simpa using hEnc, hKs, h12, hPl⟩
  have := List.all_eq_true.mp h6 d hd
  simpa [hp, hok] using this

theorem checks {x : InputBFV} {c : CertificateBFV} (h : certifyBFV? x = some c) : Checks x :=
  checks_of (certifyBFV?_some h).1

/-! ## The budget and the checks of one instruction, as functions of the operand's level -/

theorem levelOf_def {Pr : Params} (ρ : Env Pr) (a : Var) :
    levelOf ρ a = ((ρ a).map (·.level)).getD 0 := rfl

theorem levelOf_some {Pr : Params} {ρ : Env Pr} {a : Var} {xa : Val Pr} (hx : ρ a = some xa) :
    levelOf ρ a = xa.level := by
  rw [levelOf_def, hx]; rfl

open Validation.BFV.SoundAux in
theorem levelOf_zenv {Pr : Params} (ρ : Env Pr) (a : Var) :
    levelOf (zenv ρ) a = levelOf ρ a := by
  rw [levelOf_def, levelOf_def]
  simp only [zenv]
  cases ρ a <;> rfl

/-- `stepBudget`, as a function of the level of the operand. -/
def bud (x : InputBFV) (ℓ dr : ℕ) (i : Instr) : TraceBFV.Budget :=
  budgetOf
    (match i with
      | .relin .. => ksAt x ℓ dr (x.P.src.N * x.P.secretBound * x.P.secretBound)
      | .keySwitch .. => ksAt x ℓ dr x.P.secretBound
      | _ => 0)
    (msBudget x.P) (max (mulLift x.P) (mulLiftNormAt x.P ℓ (slackOf x ℓ dr i).e))
    (mulRoundApprox x.P (max 1 (slackOf x ℓ dr i).rho))
    (plainAddAt x ℓ)

theorem stepBudget_eq (x : InputBFV) (ρ : Env x.P.src) (dr : ℕ) (i : Instr) :
    stepBudget x ρ dr i = bud x (levelOf ρ (operand i)) dr i := rfl

/-- `stepChecks`, as a function of the level of the operand. -/
def chk (x : InputBFV) (ℓ dr : ℕ) (i : Instr) : Bool :=
  (match x.mul with
    | some m =>
      !isMul i || (decide (1 ≤ ℓ) && decide (ℓ ≤ x.P.src.qs.length) &&
        (slackAt x.P x.floatTol ℓ dr m).1.ok && (slackAt x.P x.floatTol ℓ dr m).2)
    | none => true) &&
  (match x.mul with
    | some (.leveled _) =>
      !isKS i || decide (ℓ ≠ x.P.src.qs.length) ||
        (decide (dr < ℓ) && floatAuxOK? (x.P.src.qs.take ℓ) [])
    | _ => true) &&
  (match x.mul with
    | some (.leveled _) =>
      decide (dr = 0) || (decide (ℓ = x.P.src.qs.length) && (isMul i || isKS i))
    | _ => true)

theorem stepChecks_eq (x : InputBFV) (ρ : Env x.P.src) (dr : ℕ) (i : Instr) :
    stepChecks x ρ dr i = chk x (levelOf ρ (operand i)) dr i := rfl

theorem budgetsAux_cons (x : InputBFV) (i : Instr) (is : List Instr) (ds : List ℕ)
    (ρ : Env x.P.src) :
    budgetsAux x (i :: is) ds ρ =
      stepBudget x ρ (ds.headD 0) i ::
        match step x.P.src ρ i with
        | some ρ' => budgetsAux x is ds.tail ρ'
        | none => [] := rfl

theorem checksAux_cons (x : InputBFV) (i : Instr) (is : List Instr) (ds : List ℕ)
    (ρ : Env x.P.src) :
    checksAux x (i :: is) ds ρ =
      (stepChecks x ρ (ds.headD 0) i &&
        match step x.P.src ρ i with
        | some ρ' => checksAux x is ds.tail ρ'
        | none => true) := rfl

theorem budgetsBFV_def (x : InputBFV) :
    budgetsBFV x =
      budgetsAux x x.prog.body (dropsOf x) (initEnv x.P.src x.prog fun _ => .exact 0) := rfl

theorem headD_eq (ds : List ℕ) : ds.headD 0 = ds.getD 0 0 := by cases ds <;> rfl

theorem tail_getD (ds : List ℕ) (n : ℕ) : ds.tail.getD n 0 = ds.getD (n + 1) 0 := by
  cases ds <;> simp

/-- The replay reaches instruction `pre.length` with the environment `Source.step` gives. -/
theorem aux_at (x : InputBFV) (i : Instr) (post : List Instr) :
    ∀ (pre : List Instr) (ds : List ℕ) (ρ0 ρ' : Env x.P.src),
      pre.foldlM (step x.P.src) ρ0 = some ρ' →
      (budgetsAux x (pre ++ i :: post) ds ρ0)[pre.length]? =
          some (stepBudget x ρ' (ds.getD pre.length 0) i) ∧
        (checksAux x (pre ++ i :: post) ds ρ0 = true →
          stepChecks x ρ' (ds.getD pre.length 0) i = true)
  | [], ds, ρ0, ρ', h => by
    cases (Option.some.inj h : ρ0 = ρ')
    rw [List.nil_append, budgetsAux_cons, checksAux_cons, headD_eq]
    exact ⟨rfl, fun hc => (band hc).1⟩
  | j :: pre, ds, ρ0, ρ', h => by
    rw [List.foldlM_cons] at h
    obtain ⟨ρ1, h1, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨ih1, ih2⟩ := aux_at x i post pre ds.tail ρ1 ρ' h
    rw [tail_getD] at ih1 ih2
    rw [List.cons_append, budgetsAux_cons, checksAux_cons, h1]
    refine ⟨?_, fun hc => ih2 (band hc).2⟩
    rw [List.length_cons, List.getElem?_cons_succ]
    exact ih1

theorem budgetFn_toArray (l : List TraceBFV.Budget) (n : ℕ) :
    budgetFn l.toArray n = l[n]?.getD (budgetOf 0 0 0 0 0) := by
  show l.toArray.getD n _ = _
  simp [Array.getD_eq_getD_getElem?]

open Validation.BFV Validation.BFV.SoundAux in
/-- Inputs within their bounds have exact messages. -/
theorem allExact_init {P : FullParams} (hk : P.src.kind = .bfv) {prog : Program}
    {s : IntPoly P.src.N} {msgs : Var → Msg P.src.t P.src.N}
    {cts : Var → List (IntPoly P.src.N)} (hin : TraceBFV.InputsOK P s prog msgs cts) :
    AllExact (initEnv P.src prog msgs) := by
  intro y v hv
  simp only [initEnv, Option.map_eq_some_iff] at hv
  obtain ⟨d, hd, rfl⟩ := hv
  have hn : d.name = y := by simpa using List.find?_some hd
  subst hn
  have he := hin _ d hd
  by_cases hp : d.parts = 1
  · simp only [hp, ↓reduceIte] at he
    obtain ⟨m, hm, -⟩ := plain_elim he
    exact ⟨m, hm⟩
  · simp only [hp, ↓reduceIte] at he
    obtain ⟨m, hm, -⟩ := enc_elim hk he
    exact ⟨m, hm⟩

open Validation.BFV.SoundAux in
/-- **The bridge.** The budget of instruction `n` is `stepBudget` at the level its operand has
in every run, and `stepChecks` passed there. -/
theorem at_facts {x : InputBFV} {c : CertificateBFV} (h : certifyBFV? x = some c)
    {s : IntPoly x.P.src.N} {msgs : Var → Msg x.P.src.t x.P.src.N}
    {cts : Var → List (IntPoly x.P.src.N)} (hin : TraceBFV.InputsOK x.P s x.prog msgs cts)
    {n : ℕ} {i : Instr} {ρ : Env x.P.src} (hat : AtInstr x msgs n i ρ) :
    c.budget n = bud x (levelOf ρ (operand i)) ((dropsOf x).getD n 0) i ∧
      chk x (levelOf ρ (operand i)) ((dropsOf x).getD n 0) i = true := by
  obtain ⟨hc, B, outs, -, -, -, rfl⟩ := certifyBFV?_some h
  have hk := (checks_of hc).kind
  obtain ⟨pre, post, hbody, rfl, hρ⟩ := hat
  have hz0 : zenv (initEnv x.P.src x.prog msgs) = initEnv x.P.src x.prog fun _ => .exact 0 := by
    funext y; simp only [zenv, initEnv, Option.map_map]; rfl
  have hfold := Validation.BFVMul.Cert.foldlM_zenv hk pre _ (allExact_init hk hin)
  rw [hρ, hz0, Option.map_some] at hfold
  obtain ⟨h1, h2⟩ := aux_at x i post pre (dropsOf x) _ _ hfold
  have h2 := h2 (by rw [← hbody]; exact (checks_of hc).aux)
  rw [stepBudget_eq, levelOf_zenv] at h1
  rw [stepChecks_eq, levelOf_zenv] at h2
  refine ⟨?_, h2⟩
  show budgetFn (budgetsBFV x).toArray pre.length = _
  rw [budgetFn_toArray, budgetsBFV_def, hbody, h1]
  rfl

theorem dropsOf_leveled {x : InputBFV} {Ps : List ℕ} (hm : x.mul = some (.leveled Ps)) :
    dropsOf x = x.drops := by
  rcases x with ⟨P, lay, prog, mul, ft, pa, ms, drops⟩
  cases hm
  rfl

theorem slackOf_mul {x : InputBFV} {m : Technique} (hm : x.mul = some m) {i : Instr}
    (hi : isMul i = true) (ℓ dr : ℕ) :
    slackOf x ℓ dr i = (slackAt x.P x.floatTol ℓ dr m).1 := by
  rcases x with ⟨P, lay, prog, mul, ft, pa, ms, drops⟩
  cases hm
  exact ite_eq_left hi

theorem chk_mul {x : InputBFV} {m : Technique} (hm : x.mul = some m) {i : Instr}
    (hi : isMul i = true) {ℓ dr : ℕ} (hc : chk x ℓ dr i = true) :
    1 ≤ ℓ ∧ ℓ ≤ x.P.src.qs.length ∧ (slackAt x.P x.floatTol ℓ dr m).1.ok = true ∧
      (slackAt x.P x.floatTol ℓ dr m).2 = true := by
  rcases x with ⟨P, lay, prog, mul, ft, pa, ms, drops⟩
  cases hm
  have h1 : (!isMul i || (decide (1 ≤ ℓ) && decide (ℓ ≤ P.src.qs.length) &&
      (slackAt P ft ℓ dr m).1.ok && (slackAt P ft ℓ dr m).2)) = true := (band (band hc).1).1
  rw [hi] at h1
  have h2 : (decide (1 ≤ ℓ) && decide (ℓ ≤ P.src.qs.length) &&
      (slackAt P ft ℓ dr m).1.ok && (slackAt P ft ℓ dr m).2) = true := h1
  obtain ⟨h2, h6⟩ := band h2
  obtain ⟨h2, h5⟩ := band h2
  obtain ⟨h3, h4⟩ := band h2
  exact ⟨of_decide_eq_true h3, of_decide_eq_true h4, h5, h6⟩

theorem chk_ks {x : InputBFV} {Ps : List ℕ} (hm : x.mul = some (.leveled Ps)) {i : Instr}
    (hi : isKS i = true) {ℓ dr : ℕ} (hc : chk x ℓ dr i = true) (htop : ℓ = x.P.src.qs.length) :
    dr < ℓ ∧ floatAuxOK? (x.P.src.qs.take ℓ) [] = true := by
  rcases x with ⟨P, lay, prog, mul, ft, pa, ms, drops⟩
  cases hm
  have h1 : (!isKS i || decide (ℓ ≠ P.src.qs.length) ||
      (decide (dr < ℓ) && floatAuxOK? (P.src.qs.take ℓ) [])) = true := (band (band hc).1).2
  have hd : decide (ℓ ≠ P.src.qs.length) = false := by simpa using htop
  rw [hi, hd] at h1
  have h2 : (decide (dr < ℓ) && floatAuxOK? (P.src.qs.take ℓ) []) = true := h1
  exact ⟨of_decide_eq_true (band h2).1, (band h2).2⟩

theorem ksBoundAt_le_ksAt (x : InputBFV) (ℓ dr btgt : ℕ) :
    ksBoundAt x.P x.lay ℓ ≤ ksAt x ℓ dr btgt := by
  rcases x with ⟨P, lay, prog, mul, ft, pa, ms, drops⟩
  rcases mul with _ | m
  · exact le_refl _
  · cases m
    case leveled Ps =>
      show _ ≤ (if ℓ = P.src.qs.length ∧ dr ≠ 0 then max _ _ else _)
      split
      · exact le_max_left _ _
      · exact le_refl _
    all_goals exact le_refl _

theorem ksAt_leveled {x : InputBFV} {Ps : List ℕ} (hm : x.mul = some (.leveled Ps))
    (ℓ dr btgt : ℕ) :
    ksAt x ℓ dr btgt =
      if ℓ = x.P.src.qs.length ∧ dr ≠ 0 then
        max (ksBoundAt x.P x.lay ℓ)
          (ksLeveled x.P.src.N (x.P.src.modulus ℓ / x.P.src.modulus (ℓ - dr))
            (ksBoundAt x.P x.lay (ℓ - dr)) btgt
            (doubleSr ((x.P.src.qs.take ℓ).drop (ℓ - dr))))
      else ksBoundAt x.P x.lay ℓ := by
  rcases x with ⟨P, lay, prog, mul, ft, pa, ms, drops⟩
  cases hm
  rfl

/-- What a certificate gives at a `mul` or `square`: the level is a level of the chain, the
slack of the declared technique there passed its checks, and the multiplication numbers of the
instruction's budget cover it. -/
theorem mul_facts {x : InputBFV} {c : CertificateBFV} (h : certifyBFV? x = some c)
    {s : IntPoly x.P.src.N} {msgs : Var → Msg x.P.src.t x.P.src.N}
    {cts : Var → List (IntPoly x.P.src.N)} (hin : TraceBFV.InputsOK x.P s x.prog msgs cts)
    {m : Technique} (hm : x.mul = some m)
    {n : ℕ} {i : Instr} {ρ : Env x.P.src} (hat : AtInstr x msgs n i ρ) (hi : isMul i = true)
    {xa : Val x.P.src} (hx : ρ (operand i) = some xa) :
    1 ≤ xa.level ∧ xa.level ≤ x.P.src.qs.length ∧
      (slackAt x.P x.floatTol xa.level ((dropsOf x).getD n 0) m).1.ok = true ∧
      (slackAt x.P x.floatTol xa.level ((dropsOf x).getD n 0) m).2 = true ∧
      mulLiftNormAt x.P xa.level (slackAt x.P x.floatTol xa.level ((dropsOf x).getD n 0) m).1.e ≤
        (c.budget n).mulLift ∧
      mulRoundApprox x.P (slackAt x.P x.floatTol xa.level ((dropsOf x).getD n 0) m).1.rho ≤
        (c.budget n).mulRound := by
  obtain ⟨hb, hc⟩ := at_facts h hin hat
  rw [levelOf_some hx] at hb hc
  rw [hb]
  have hsl := slackOf_mul hm hi xa.level ((dropsOf x).getD n 0)
  obtain ⟨h1, h2, h3, h4⟩ := chk_mul hm hi hc
  refine ⟨h1, h2, h3, h4, ?_, ?_⟩
  · show _ ≤ max (mulLift x.P)
      (mulLiftNormAt x.P xa.level (slackOf x xa.level ((dropsOf x).getD n 0) i).e)
    rw [hsl]; exact le_max_right _ _
  · show _ ≤ mulRoundApprox x.P (max 1 (slackOf x xa.level ((dropsOf x).getD n 0) i).rho)
    rw [hsl]; exact Nat.mul_le_mul_right _ (le_max_right _ _)

/-! ## The levels of the multiplications -/

/-- The levels `mulLevelsAux` records at one instruction (a copy, for the `rfl` equation below). -/
def lv (Pr : Params) (i : Instr) (ρ : Env Pr) : List ℕ :=
  match i with
  | .mul _ a _ | .square _ a => ((ρ a).map (·.level)).toList
  | _ => []

theorem mulLevelsAux_cons (Pr : Params) (i : Instr) (is : List Instr) (ρ : Env Pr) :
    mulLevelsAux Pr (i :: is) ρ =
      match step Pr ρ i with
      | some ρ' => lv Pr i ρ ++ mulLevelsAux Pr is ρ'
      | none => lv Pr i ρ := by
  cases i <;> rfl

theorem mulLevels_eq (Pr : Params) (prog : Program) :
    mulLevels Pr prog =
      (mulLevelsAux Pr prog.body (initEnv Pr prog fun _ => .exact 0)).eraseDups := rfl

open Validation.BFV.SoundAux in
theorem mem_mulLevelsAux {Pr : Params} (hk : Pr.kind = .bfv) (i : Instr) (post : List Instr)
    (a : Var) (xa : Val Pr) (hi : (∃ d b, i = .mul d a b) ∨ ∃ d, i = .square d a) :
    ∀ (pre : List Instr) (ρ0 ρ : Env Pr), AllExact ρ0 → pre.foldlM (step Pr) ρ0 = some ρ →
      ρ a = some xa → xa.level ∈ mulLevelsAux Pr (pre ++ i :: post) (zenv ρ0)
  | [], ρ0, ρ, _, hρ, hx => by
    cases (Option.some.inj hρ : ρ0 = ρ)
    have hlv : xa.level ∈ lv Pr i (zenv ρ0) := by
      rcases hi with ⟨d, b, rfl⟩ | ⟨d, rfl⟩ <;> simp [lv, zenv, hx, zv]
    rw [List.nil_append, mulLevelsAux_cons]
    split
    · exact List.mem_append_left _ hlv
    · exact hlv
  | j :: pre, ρ0, ρ, h0, hρ, hx => by
    rw [List.foldlM_cons] at hρ
    obtain ⟨ρ1, h1, hρ⟩ := Option.bind_eq_some_iff.mp hρ
    obtain ⟨hz, hex⟩ := step_zenv hk h0 j
    rw [List.cons_append, mulLevelsAux_cons, hz, h1]
    exact List.mem_append_right _
      (mem_mulLevelsAux hk i post a xa hi pre ρ1 ρ (hex ρ1 h1) hρ hx)

theorem lv_mem {Pr : Params} {i : Instr} {ρ : Env Pr} {ℓ : ℕ} (h : ℓ ∈ lv Pr i ρ) :
    isMul i = true ∧ ∃ xa, ρ (operand i) = some xa ∧ xa.level = ℓ := by
  cases i
  case mul d a b =>
    rcases hx : ρ a with _ | xa
    · simp [lv, hx] at h
    · simp [lv, hx] at h
      exact ⟨rfl, xa, hx, h.symm⟩
  case square d a =>
    rcases hx : ρ a with _ | xa
    · simp [lv, hx] at h
    · simp [lv, hx] at h
      exact ⟨rfl, xa, hx, h.symm⟩
  all_goals exact absurd h List.not_mem_nil

theorem mulLevelsAux_ok (x : InputBFV) : ∀ (body : List Instr) (ds : List ℕ) (ρ : Env x.P.src),
    checksAux x body ds ρ = true → (∀ i ∈ body, isMul i = true → ∃ m, x.mul = some m) →
    ∀ ℓ ∈ mulLevelsAux x.P.src body ρ, 1 ≤ ℓ ∧ ℓ ≤ x.P.src.qs.length
  | [], _, _, _, _, ℓ, hℓ => absurd hℓ List.not_mem_nil
  | i :: is, ds, ρ, hc, hmul, ℓ, hℓ => by
    rw [checksAux_cons] at hc
    obtain ⟨hc1, hc2⟩ := band hc
    rw [mulLevelsAux_cons] at hℓ
    have hhere : ∀ ℓ ∈ lv x.P.src i ρ, 1 ≤ ℓ ∧ ℓ ≤ x.P.src.qs.length := by
      intro ℓ hℓ
      obtain ⟨hi, xa, hx, rfl⟩ := lv_mem hℓ
      obtain ⟨m, hm⟩ := hmul i List.mem_cons_self hi
      rw [stepChecks_eq, levelOf_some hx] at hc1
      obtain ⟨h1, h2, -⟩ := chk_mul hm hi hc1
      exact ⟨h1, h2⟩
    rcases hs : step x.P.src ρ i with _ | ρ'
    · rw [hs] at hℓ
      exact hhere ℓ hℓ
    · rw [hs] at hℓ hc2
      rcases List.mem_append.mp hℓ with h | h
      · exact hhere ℓ h
      · exact mulLevelsAux_ok x is ds.tail ρ' hc2
          (fun i hi => hmul i (List.mem_cons_of_mem _ hi)) ℓ h

/-! ## What the certificate contains -/

theorem certifyBFV?_spec (x : InputBFV) (c : CertificateBFV) (h : certifyBFV? x = some c) :
    checksOK x = true ∧ c.budget = budgetBFV x ∧ c.mulLevels = mulLevels x.P.src x.prog ∧
    c.assumed = assumptionsOf x ∧
    refAnalyzeBFVAt x.P c.budget x.prog = some c.bound ∧
    Encrypt.outputsUnderS? x.P.src x.prog = true ∧
    x.prog.outputs ≠ [] ∧ c.outputs.map Prod.fst = x.prog.outputs ∧
    ∀ o ∈ x.prog.outputs, ∃ B, c.outputs.lookup o = some B ∧
      refAnalyzeBFVAt x.P c.budget { x.prog with outputs := [o] } = some B := by
  obtain ⟨hc, B, outs, hB, hU, ho, rfl⟩ := certifyBFV?_some h
  obtain ⟨hfst, hl⟩ := Validation.Certify.mapM_pair _ _ ho
  refine ⟨hc, rfl, rfl, rfl, hB, hU, (checks_of hc).outs, hfst, fun o hoo => ?_⟩
  obtain ⟨b, hb, hlk⟩ := hl o hoo
  exact ⟨b, hlk, hb⟩

theorem certifyBFV?_paramsOK (x : InputBFV) (c : CertificateBFV) (h : certifyBFV? x = some c) :
    SchemeParamsOK x.P ∧ x.P.src.kind = .bfv ∧ Budget.SpecialOK x.P ∧
    (∀ ℓ, 1 ≤ ℓ → ℓ ≤ x.P.src.qs.length → x.lay.okAt ℓ = true ∧
      Budget.restrictsTo x.lay x.P.src.qs.length ℓ = true) ∧
    (∀ ℓ ∈ c.mulLevels, 1 ≤ ℓ ∧ ℓ ≤ x.P.src.qs.length) := by
  have hc := checks h
  obtain ⟨-, -, hML, -⟩ := certifyBFV?_spec x c h
  refine ⟨Validation.Params.schemeParamsOK?_sound _ hc.params, hc.kind,
    Validation.Budget.specialOK?_sound _ hc.special, fun ℓ hℓ1 hℓ => ?_, fun ℓ hℓ => ?_⟩
  · have hr := Validation.Budget.layoutOK?_restricts x.P x.lay hc.layout ℓ hℓ1 hℓ
    exact ⟨Validation.Budget.restrictsTo_okAt x.lay _ ℓ hℓ hr, hr⟩
  · rw [hML, mulLevels_eq, List.mem_eraseDups] at hℓ
    refine mulLevelsAux_ok x _ _ _ hc.aux (fun i hi him => ?_) ℓ hℓ
    have h7 := hc.mulDecl
    rcases hmm : x.mul with _ | m
    · have hany : x.prog.body.any isMul = true := List.any_eq_true.mpr ⟨i, hi, him⟩
      rw [hmm, hany] at h7
      exact absurd h7 (by decide)
    · exact ⟨m, rfl⟩

theorem certifyBFV?_inputs (x : InputBFV) (c : CertificateBFV) (h : certifyBFV? x = some c)
    (d : Decl) (hd : d ∈ x.prog.inputs) (hp : d.parts ≠ 1) (hok : d.ok x.P.src = true) :
    decOK x.P.src.t (x.P.src.modulus d.level) (TraceBFV.inputBound x.P x.prog d) = true :=
  (checks h).inputs d hd hp hok

theorem certifyBFV?_budget (x : InputBFV) (c : CertificateBFV) (h : certifyBFV? x = some c)
    (s : IntPoly x.P.src.N) (msgs : Var → Msg x.P.src.t x.P.src.N)
    (cts : Var → List (IntPoly x.P.src.N)) (hin : TraceBFV.InputsOK x.P s x.prog msgs cts)
    (n : ℕ) (i : Instr) (ρ : Env x.P.src) (hat : AtInstr x msgs n i ρ) :
    (c.budget n).modSwitch = msBudget x.P ∧
    mulLift x.P ≤ (c.budget n).mulLift ∧ mulRound x.P ≤ (c.budget n).mulRound ∧
    (∀ d a xa, i = .relin d a ∨ i = .keySwitch d a → ρ a = some xa →
      ksBoundAt x.P x.lay xa.level ≤ (c.budget n).keySwitch) ∧
    (∀ d a p xa, i = .addPlain d a p ∨ i = .subPlain d a p → ρ a = some xa →
      (c.budget n).plainAdd = plainAddAt x xa.level) := by
  obtain ⟨hb, -⟩ := at_facts h hin hat
  rw [hb]
  refine ⟨rfl, le_max_left _ _, ?_, ?_, ?_⟩
  · show mulRound x.P ≤ max 1 _ * mulRound x.P
    exact Nat.le_mul_of_pos_left _ (lt_of_lt_of_le Nat.one_pos (le_max_left _ _))
  · rintro d a xa (rfl | rfl) hx
    · have e : levelOf ρ (operand (.relin d a)) = xa.level := levelOf_some hx
      rw [e]; exact ksBoundAt_le_ksAt x _ _ _
    · have e : levelOf ρ (operand (.keySwitch d a)) = xa.level := levelOf_some hx
      rw [e]; exact ksBoundAt_le_ksAt x _ _ _
  · rintro d a p xa (rfl | rfl) hx
    · have e : levelOf ρ (operand (.addPlain d a p)) = xa.level := levelOf_some hx
      rw [e]; rfl
    · have e : levelOf ρ (operand (.subPlain d a p)) = xa.level := levelOf_some hx
      rw [e]; rfl

/-! ## What "certified" means for the outputs -/

theorem certifyBFV?_decrypts (x : InputBFV) (c : CertificateBFV) (h : certifyBFV? x = some c)
    (s : IntPoly x.P.src.N) (msgs : Var → Msg x.P.src.t x.P.src.N)
    (cts : Var → List (IntPoly x.P.src.N)) (hin : TraceBFV.InputsOK x.P s x.prog msgs cts) :
    OutputsDecryptAt x.P c.budget x.prog s msgs cts := by
  obtain ⟨hP, hk, -, -, -⟩ := certifyBFV?_paramsOK x c h
  obtain ⟨-, -, -, -, hB, hU, -⟩ := certifyBFV?_spec x c h
  exact Validation.BFVMul.certifiedAt_decrypts x.P c.budget x.prog c.bound hP hk hB hU s msgs cts
    hin

theorem certifyBFV?_sound (x : InputBFV) (c : CertificateBFV) (h : certifyBFV? x = some c)
    (s : IntPoly x.P.src.N) (msgs : Var → Msg x.P.src.t x.P.src.N)
    (cts : Var → List (IntPoly x.P.src.N)) (hin : TraceBFV.InputsOK x.P s x.prog msgs cts) :
    OutputsCertifiedBFV x.P c.budget x.prog c.outputs s msgs cts := by
  obtain ⟨hP, hk, -, -, -⟩ := certifyBFV?_paramsOK x c h
  obtain ⟨-, -, -, -, -, -, -, -, hout⟩ := certifyBFV?_spec x c h
  obtain ⟨ρ, hev, hrun⟩ := certifyBFV?_decrypts x c h s msgs cts hin
  refine ⟨ρ, hev, fun σ hσ o ho => ?_⟩
  obtain ⟨v, ct, m, hv, hct, hm, hkey, hd⟩ := hrun σ hσ o ho
  obtain ⟨b, hlk, hbo⟩ := hout o ho
  have hin' : TraceBFV.InputsOK x.P s { x.prog with outputs := [o] } msgs cts := hin
  obtain ⟨ρ1, hev1, hrun1⟩ :=
    Validation.BFV.refAnalyzeBFVAt_sound x.P c.budget _ b hP hk hbo s msgs cts hin'
  have f0 : x.prog.body.foldlM (step x.P.src) (initEnv x.P.src x.prog msgs) = some ρ :=
    Validation.Certify.eval_body hev
  have f1 : x.prog.body.foldlM (step x.P.src) (initEnv x.P.src x.prog msgs) = some ρ1 :=
    Validation.Certify.eval_body (prog := { x.prog with outputs := [o] }) hev1
  have e1 : ρ1 = ρ := Option.some.inj (f1.symm.trans f0)
  subst e1
  obtain ⟨v', ct', hv', hct', henc⟩ := hrun1 σ hσ o (List.mem_singleton.mpr rfl)
  have ev : v' = v := Option.some.inj (hv'.symm.trans hv)
  have ec : ct' = ct := Option.some.inj (hct'.symm.trans hct)
  subst ev; subst ec
  exact ⟨v', ct', m, b, hv, hct, hlk, henc, hm, hkey, hd⟩

/-! ## Level coverage -/

open Validation.BFV.SoundAux in
theorem certifyBFV?_mulLevels (x : InputBFV) (c : CertificateBFV) (h : certifyBFV? x = some c)
    (s : IntPoly x.P.src.N) (msgs : Var → Msg x.P.src.t x.P.src.N)
    (cts : Var → List (IntPoly x.P.src.N)) (hin : TraceBFV.InputsOK x.P s x.prog msgs cts)
    (pre post : List Instr) (i : Instr) (hbody : x.prog.body = pre ++ i :: post)
    (ρ : Env x.P.src)
    (hρ : pre.foldlM (step x.P.src) (initEnv x.P.src x.prog msgs) = some ρ)
    (a : Var) (xa : Val x.P.src) (hi : (∃ d b, i = .mul d a b) ∨ ∃ d, i = .square d a)
    (hx : ρ a = some xa) :
    xa.level ∈ c.mulLevels := by
  obtain ⟨-, hk, -⟩ := certifyBFV?_paramsOK x c h
  obtain ⟨-, -, hML, -⟩ := certifyBFV?_spec x c h
  have hz0 : zenv (initEnv x.P.src x.prog msgs) = initEnv x.P.src x.prog fun _ => .exact 0 := by
    funext y; simp only [zenv, initEnv, Option.map_map]; rfl
  rw [hML, mulLevels_eq, List.mem_eraseDups, hbody, ← hz0]
  exact mem_mulLevelsAux hk i post a xa hi pre _ ρ (allExact_init hk hin) hρ hx

/-! ## Realizability: the textbook algorithm -/

theorem certifyBFV?_textbook_mul (x : InputBFV) (c : CertificateBFV) (h : certifyBFV? x = some c)
    (s : IntPoly x.P.src.N) (hs : SecretOK x.P.secretBound s)
    (msgs : Var → Msg x.P.src.t x.P.src.N) (cts : Var → List (IntPoly x.P.src.N))
    (hin : TraceBFV.InputsOK x.P s x.prog msgs cts) (n : ℕ) (d a b : Var)
    (ρ ρ' : Env x.P.src) (hat : AtInstr x msgs n (.mul d a b) ρ)
    (σ : Trace.CtEnv x.P) (xa xb : Val x.P.src) (ca cb : List (IntPoly x.P.src.N))
    (hstep : step x.P.src ρ (.mul d a b) = some ρ') (hx : ρ a = some xa) (hy : ρ b = some xb)
    (ha : σ a = some ca) (hb : σ b = some cb)
    (hla : ca.length = 2) (hlb : cb.length = 2) (h2x : xa.parts = 2) (h2y : xb.parts = 2) :
    TraceBFV.StepOK x.P (c.budget n) s ρ ρ' σ
      (σ.set d (bfvMul x.P.src.t (x.P.src.modulus xa.level) ca cb)) (.mul d a b) := by
  obtain ⟨hP, -⟩ := certifyBFV?_paramsOK x c h
  obtain ⟨-, hL, hR, -⟩ := certifyBFV?_budget x c h s msgs cts hin n _ ρ hat
  exact Validation.BFV.stepOK_mul_textbook x.P hP (c.budget n) hL hR s hs ρ ρ' σ d a b xa xb ca cb
    hstep hx hy ha hb hla hlb h2x h2y

theorem certifyBFV?_textbook_square (x : InputBFV) (c : CertificateBFV)
    (h : certifyBFV? x = some c)
    (s : IntPoly x.P.src.N) (hs : SecretOK x.P.secretBound s)
    (msgs : Var → Msg x.P.src.t x.P.src.N) (cts : Var → List (IntPoly x.P.src.N))
    (hin : TraceBFV.InputsOK x.P s x.prog msgs cts) (n : ℕ) (d a : Var)
    (ρ ρ' : Env x.P.src) (hat : AtInstr x msgs n (.square d a) ρ)
    (σ : Trace.CtEnv x.P) (xa : Val x.P.src) (ca : List (IntPoly x.P.src.N))
    (hstep : step x.P.src ρ (.square d a) = some ρ') (hx : ρ a = some xa)
    (ha : σ a = some ca) (hla : ca.length = 2) (h2x : xa.parts = 2) :
    TraceBFV.StepOK x.P (c.budget n) s ρ ρ' σ
      (σ.set d (bfvMul x.P.src.t (x.P.src.modulus xa.level) ca ca)) (.square d a) := by
  obtain ⟨hP, -⟩ := certifyBFV?_paramsOK x c h
  obtain ⟨-, hL, hR, -⟩ := certifyBFV?_budget x c h s msgs cts hin n _ ρ hat
  exact Validation.BFV.stepOK_square_textbook x.P hP (c.budget n) hL hR s hs ρ ρ' σ d a xa ca
    hstep hx ha hla h2x

/-! ## Run existence -/

section RunExists
open Validation.BFV Validation.BFV.SoundAux Validation.BFV.PerInstrAux
open Validation.Budget.RunAux (Shape Levels levels_step gadgetKeys_exist)
variable {P : FullParams}

/-- What the textbook realization of instruction `i` in front of `ρ` needs of its budget. -/
def GoodB (P : FullParams) (lay : Budget.KSLayout) (En : TraceBFV.Budget) (i : Instr)
    (ρ : Env P.src) : Prop :=
  msBudget P ≤ En.modSwitch ∧ mulLift P ≤ En.mulLift ∧ mulRound P ≤ En.mulRound ∧
    ∀ d a xa, i = .relin d a ∨ i = .keySwitch d a → ρ a = some xa →
      ksBoundAt P lay xa.level ≤ En.keySwitch

theorem step_existsAt (lay : Budget.KSLayout) (hk : P.src.kind = .bfv) (hP : SchemeParamsOK P)
    (hS : Budget.SpecialOK P)
    (hlay : ∀ ℓ, 1 ≤ ℓ → ℓ ≤ P.src.qs.length → lay.okAt ℓ = true)
    (En : TraceBFV.Budget) (s : IntPoly P.src.N) (hs : SecretOK P.secretBound s)
    {ρ ρ' : Env P.src} {σ : Trace.CtEnv P} (i : Instr) (hg : GoodB P lay En i ρ)
    (hsh : Shape P ρ σ) (hlv : Levels P ρ) (hstep : step P.src ρ i = some ρ')
    (hdom : domainOK ρ i = true) :
    ∃ σ', TraceBFV.StepOK P En s ρ ρ' σ σ' i := by
  obtain ⟨hEm, hEl, hEr, hEk⟩ := hg
  cases i with
  | relin d a =>
    rcases hx : ρ a with _ | x
    · simp [step, hx] at hstep
    obtain ⟨ca, ha, hla⟩ := hsh a x hx
    obtain ⟨h1, hL⟩ := hlv a x hx
    obtain ⟨f, hf⟩ := Validation.BFV.relin_realizable P lay hP hS x.level hL (hlay _ h1 hL)
    obtain ⟨keys, hkeys⟩ := gadgetKeys_exist P lay x.level .square s
    exact ⟨_, hf En (hEk d a x (Or.inl rfl) hx) s hs keys hkeys ρ ρ' σ d a x ca hstep hx ha rfl
      hla⟩
  | keySwitch d a =>
    rcases hx : ρ a with _ | x
    · simp [step, hx] at hstep
    obtain ⟨ca, ha, hla⟩ := hsh a x hx
    obtain ⟨h1, hL⟩ := hlv a x hx
    obtain ⟨f, hf⟩ := Validation.BFV.keySwitch_realizable P lay hP hS x.level hL (hlay _ h1 hL)
    obtain ⟨keys, hkeys⟩ := gadgetKeys_exist P lay x.level (.galois x.key) s
    exact ⟨_, hf En (hEk d a x (Or.inr rfl) hx) s hs ρ ρ' σ d a x ca hstep hx ha rfl hla keys
      hkeys⟩
  | _ =>
    obtain ⟨σ', hok⟩ := step_exists lay hk hP hS hlay
      ⟨max En.keySwitch (ksBudget P lay), En.modSwitch, En.mulLift, En.mulRound, En.plainAdd⟩
      (le_max_right _ _) hEm hEl hEr s hs _ hsh hlv hstep hdom
    exact ⟨σ', hok⟩

theorem run_existsAt (lay : Budget.KSLayout) (hk : P.src.kind = .bfv) (hP : SchemeParamsOK P)
    (hS : Budget.SpecialOK P)
    (hlay : ∀ ℓ, 1 ≤ ℓ → ℓ ≤ P.src.qs.length → lay.okAt ℓ = true)
    (E E' : ℕ → TraceBFV.Budget) (s : IntPoly P.src.N) (hs : SecretOK P.secretBound s) :
    ∀ (body : List Instr) (n : ℕ) (ρ : Env P.src)
    (σ : Trace.CtEnv P) (β : Var → Option TraceBFV.Bnd)
    (r : Env P.src × (Var → Option TraceBFV.Bnd)),
    AllExact ρ → Shape P ρ σ → Levels P ρ → refRunBFVAt P E' n body (zenv ρ) β = some r →
    (∀ pre i post ρj, body = pre ++ i :: post → pre.foldlM (step P.src) ρ = some ρj →
      GoodB P lay (E (n + pre.length)) i ρj) →
    ∃ σf, TraceBFV.RunAt P E s n body ρ σ σf
  | [], _, _, σ, _, _, _, _, _, _, _ => ⟨σ, rfl⟩
  | i :: is, n, ρ, σ, β, r, hρ, hsh, hlv, h, hg => by
    obtain ⟨ρz', vz, b, h1, -, -, -, h5, hdom⟩ := refRunAt_cons_some P h
    obtain ⟨hz, hex⟩ := step_zenv hk hρ i
    rw [hz] at h1
    obtain ⟨ρ', hstep, rfl⟩ := Option.map_eq_some_iff.mp h1
    rw [domainOK_zenv] at hdom
    obtain ⟨σ', hok⟩ := step_existsAt lay hk hP hS hlay (E n) s hs i (hg [] i is ρ rfl rfl)
      hsh hlv hstep hdom
    obtain ⟨σf, hrun⟩ := run_existsAt lay hk hP hS hlay E E' s hs is (n + 1) ρ' σ' _ r
      (hex ρ' hstep) (shape_step hsh hstep hok) (levels_step hlv hstep) h5
      (fun pre j post ρj hb hf => by
        have := hg (i :: pre) j post ρj (by rw [hb]; rfl)
          (by rw [List.foldlM_cons, hstep]; exact hf)
        rwa [List.length_cons, show n + (pre.length + 1) = n + 1 + pre.length by omega] at this)
    exact ⟨σf, ρ', σ', hstep, hok, hrun⟩

end RunExists

open Validation.BFV Validation.BFV.SoundAux Validation.BFV.PerInstrAux in
theorem certifyBFV?_textbook_run_exists (x : InputBFV) (c : CertificateBFV)
    (h : certifyBFV? x = some c)
    (s : IntPoly x.P.src.N) (hs : SecretOK x.P.secretBound s)
    (msgs : Var → Msg x.P.src.t x.P.src.N) (cts : Var → List (IntPoly x.P.src.N))
    (hin : TraceBFV.InputsOK x.P s x.prog msgs cts) :
    ∃ σ, TraceBFV.RunAt x.P c.budget s 0 x.prog.body (initEnv x.P.src x.prog msgs)
      (Trace.initCt x.P x.prog cts) σ := by
  obtain ⟨hP, -, hS, hlay, -⟩ := certifyBFV?_paramsOK x c h
  obtain ⟨-, -, -, -, hB, -⟩ := certifyBFV?_spec x c h
  obtain ⟨hk, hdecl, ρz, βf, hrun, -⟩ := refAnalyzeAt_some hB
  have hfind : ∀ y d, x.prog.inputs.find? (·.name = y) = some d →
      (cts y).length = d.parts := by
    intro y d hd
    have hn : d.name = y := by simpa using List.find?_some hd
    have he := hin y d hd
    by_cases hp : d.parts = 1
    · simp only [hp, ↓reduceIte] at he
      exact he.1
    · simp only [hp, ↓reduceIte] at he
      obtain ⟨m, hm, hl, -⟩ := enc_elim hk he
      exact hl
  have hz0 : zenv (initEnv x.P.src x.prog msgs) = initEnv x.P.src x.prog fun _ => .exact 0 := by
    funext y; simp only [zenv, initEnv, Option.map_map]; rfl
  rw [← hz0] at hrun
  refine run_existsAt x.lay hk hP hS (fun ℓ h1 h2 => (hlay ℓ h1 h2).1) c.budget c.budget s hs
    x.prog.body 0 _ _ _ _ (allExact_init hk hin) ?_ ?_ hrun ?_
  · intro y v hv
    simp only [initEnv, Option.map_eq_some_iff] at hv
    obtain ⟨d, hd, rfl⟩ := hv
    exact ⟨cts y, by simp [Trace.initCt, hd], hfind y d hd⟩
  · intro y v hv
    simp only [initEnv, Option.map_eq_some_iff] at hv
    obtain ⟨d, hd, rfl⟩ := hv
    have hok := List.all_eq_true.mp hdecl d (List.mem_of_find?_eq_some hd)
    simp only [Decl.ok, decide_eq_true_eq] at hok
    exact ⟨hok.2.1, hok.2.2.1⟩
  · intro pre i post ρj hb hf
    obtain ⟨e1, e2, e3, e4, -⟩ :=
      certifyBFV?_budget x c h s msgs cts hin pre.length i ρj ⟨pre, post, hb, rfl, hf⟩
    rw [Nat.zero_add]
    exact ⟨le_of_eq e1.symm, e2, e3, e4⟩

/-! ## The slack of each technique -/

theorem slackAt_hps_false (P : FullParams) (ℓ dr : ℕ) (R : List ℕ) :
    slackAt P false ℓ dr (.hps R) = ((⟨0, 1, true⟩ : Slack), decide (ℓ = P.src.qs.length) &&
      decide (1 ≤ R.length) && hpsAuxOK? P.src.t P.src.N (P.src.qs.take ℓ) R) := rfl

theorem slackAt_hps_true (P : FullParams) (ℓ dr : ℕ) (R : List ℕ) :
    slackAt P true ℓ dr (.hps R) =
      (hpsSlack P.src.t P.src.N (P.src.modulus ℓ) R.prod (doubleSw ℓ) (doubleSw R.length)
          (doubleSr (P.src.qs.take ℓ)),
        decide (ℓ = P.src.qs.length) && decide (1 ≤ R.length) && basisOK (P.src.qs.take ℓ) R &&
          floatAuxOK? (P.src.qs.take ℓ) R) := rfl

theorem slackAt_behz (P : FullParams) (ft : Bool) (ℓ dr : ℕ) (B : List ℕ) (msk mt : ℕ) :
    slackAt P ft ℓ dr (.behz B msk mt) =
      (behzSlack P.src.t P.src.N (P.src.modulus ℓ) B.prod msk ℓ B.length mt,
        decide (ℓ = P.src.qs.length) && decide (1 ≤ B.length) &&
          basisOK (P.src.qs.take ℓ) (B ++ [msk]) &&
          behzAuxOK? P.src.t P.src.N (P.src.qs.take ℓ) B msk mt &&
          behzWordOK? P.src.t P.src.N (P.src.qs.take ℓ) B msk mt) := rfl

theorem slackAt_poverq (P : FullParams) (ft : Bool) (ℓ dr : ℕ) (Ps : List ℕ) :
    slackAt P ft ℓ dr (.poverq Ps) = poverqAt P ft ℓ Ps := rfl

theorem slackAt_leveled (P : FullParams) (ft : Bool) (ℓ dr : ℕ) (Ps : List ℕ) :
    slackAt P ft ℓ dr (.leveled Ps) =
      if ℓ = P.src.qs.length ∧ dr ≠ 0 then leveledAt P ft Ps dr else poverqAt P ft ℓ Ps := rfl

/-! ## Realizability: the idealised exact algorithms and BEHZ -/

theorem certifyBFV?_hps_mul (x : InputBFV) (c : CertificateBFV) (h : certifyBFV? x = some c)
    (R : List ℕ) (hm : x.mul = some (.hps R)) (hf : x.floatTol = false)
    (s : IntPoly x.P.src.N) (hs : SecretOK x.P.secretBound s)
    (msgs : Var → Msg x.P.src.t x.P.src.N) (cts : Var → List (IntPoly x.P.src.N))
    (hin : TraceBFV.InputsOK x.P s x.prog msgs cts) (n : ℕ) (d a b : Var)
    (ρ ρ' : Env x.P.src) (hat : AtInstr x msgs n (.mul d a b) ρ)
    (σ : Trace.CtEnv x.P) (xa xb : Val x.P.src) (ca cb : List (IntPoly x.P.src.N))
    (hstep : step x.P.src ρ (.mul d a b) = some ρ') (hx : ρ a = some xa) (hy : ρ b = some xb)
    (ha : σ a = some ca) (hb : σ b = some cb)
    (hla : ca.length = 2) (hlb : cb.length = 2) (h2x : xa.parts = 2) (h2y : xb.parts = 2) :
    TraceBFV.StepOK x.P (c.budget n) s ρ ρ' σ
      (σ.set d (hpsMul x.P.src.t (x.P.src.qs.take xa.level) R ca cb)) (.mul d a b) := by
  obtain ⟨hP, -⟩ := certifyBFV?_paramsOK x c h
  obtain ⟨-, hL, hR, -⟩ := certifyBFV?_budget x c h s msgs cts hin n _ ρ hat
  obtain ⟨hℓ1, hℓL, -, h2, -, -⟩ := mul_facts h hin hm hat (i := .mul d a b) rfl hx
  rw [hf, slackAt_hps_false] at h2
  exact Validation.BFVMul.stepOK_mul_hps x.P hP (c.budget n) hL hR s hs ρ ρ' σ d a b xa xb ca cb R
    hstep hx hy ha hb hla hlb h2x h2y hℓ1 hℓL (band h2).2

theorem certifyBFV?_hps_square (x : InputBFV) (c : CertificateBFV) (h : certifyBFV? x = some c)
    (R : List ℕ) (hm : x.mul = some (.hps R)) (hf : x.floatTol = false)
    (s : IntPoly x.P.src.N) (hs : SecretOK x.P.secretBound s)
    (msgs : Var → Msg x.P.src.t x.P.src.N) (cts : Var → List (IntPoly x.P.src.N))
    (hin : TraceBFV.InputsOK x.P s x.prog msgs cts) (n : ℕ) (d a : Var)
    (ρ ρ' : Env x.P.src) (hat : AtInstr x msgs n (.square d a) ρ)
    (σ : Trace.CtEnv x.P) (xa : Val x.P.src) (ca : List (IntPoly x.P.src.N))
    (hstep : step x.P.src ρ (.square d a) = some ρ') (hx : ρ a = some xa)
    (ha : σ a = some ca) (hla : ca.length = 2) (h2x : xa.parts = 2) :
    TraceBFV.StepOK x.P (c.budget n) s ρ ρ' σ
      (σ.set d (hpsMul x.P.src.t (x.P.src.qs.take xa.level) R ca ca)) (.square d a) := by
  obtain ⟨hP, -⟩ := certifyBFV?_paramsOK x c h
  obtain ⟨-, hL, hR, -⟩ := certifyBFV?_budget x c h s msgs cts hin n _ ρ hat
  obtain ⟨hℓ1, hℓL, -, h2, -, -⟩ := mul_facts h hin hm hat (i := .square d a) rfl hx
  rw [hf, slackAt_hps_false] at h2
  exact Validation.BFVMul.stepOK_square_hps x.P hP (c.budget n) hL hR s hs ρ ρ' σ d a xa ca R
    hstep hx ha hla h2x hℓ1 hℓL (band h2).2

theorem certifyBFV?_behz_mul (x : InputBFV) (c : CertificateBFV) (h : certifyBFV? x = some c)
    (B : List ℕ) (msk mt : ℕ) (hm : x.mul = some (.behz B msk mt))
    (s : IntPoly x.P.src.N) (hs : SecretOK x.P.secretBound s)
    (msgs : Var → Msg x.P.src.t x.P.src.N) (cts : Var → List (IntPoly x.P.src.N))
    (hin : TraceBFV.InputsOK x.P s x.prog msgs cts) (n : ℕ) (d a b : Var)
    (ρ ρ' : Env x.P.src) (hat : AtInstr x msgs n (.mul d a b) ρ)
    (σ : Trace.CtEnv x.P) (xa xb : Val x.P.src) (ca cb : List (IntPoly x.P.src.N))
    (hstep : step x.P.src ρ (.mul d a b) = some ρ') (hx : ρ a = some xa) (hy : ρ b = some xb)
    (ha : σ a = some ca) (hb : σ b = some cb)
    (hla : ca.length = 2) (hlb : cb.length = 2) (h2x : xa.parts = 2) (h2y : xb.parts = 2) :
    TraceBFV.StepOK x.P (c.budget n) s ρ ρ' σ
      (σ.set d (behzMul x.P.src.t (x.P.src.qs.take xa.level) B msk mt ca cb)) (.mul d a b) := by
  obtain ⟨hP, -⟩ := certifyBFV?_paramsOK x c h
  obtain ⟨hℓ1, hℓL, -, h2, hL, hR⟩ := mul_facts h hin hm hat (i := .mul d a b) rfl hx
  rw [slackAt_behz] at h2 hL hR
  exact Validation.BFVMul.stepOK_mul_behz x.P hP (c.budget n) s hs ρ ρ' σ d a b xa xb ca cb B msk
    mt hL hR hstep hx hy ha hb hla hlb h2x h2y hℓ1 hℓL (band (band h2).1).2

theorem certifyBFV?_behz_square (x : InputBFV) (c : CertificateBFV) (h : certifyBFV? x = some c)
    (B : List ℕ) (msk mt : ℕ) (hm : x.mul = some (.behz B msk mt))
    (s : IntPoly x.P.src.N) (hs : SecretOK x.P.secretBound s)
    (msgs : Var → Msg x.P.src.t x.P.src.N) (cts : Var → List (IntPoly x.P.src.N))
    (hin : TraceBFV.InputsOK x.P s x.prog msgs cts) (n : ℕ) (d a : Var)
    (ρ ρ' : Env x.P.src) (hat : AtInstr x msgs n (.square d a) ρ)
    (σ : Trace.CtEnv x.P) (xa : Val x.P.src) (ca : List (IntPoly x.P.src.N))
    (hstep : step x.P.src ρ (.square d a) = some ρ') (hx : ρ a = some xa)
    (ha : σ a = some ca) (hla : ca.length = 2) (h2x : xa.parts = 2) :
    TraceBFV.StepOK x.P (c.budget n) s ρ ρ' σ
      (σ.set d (behzMul x.P.src.t (x.P.src.qs.take xa.level) B msk mt ca ca)) (.square d a) := by
  obtain ⟨hP, -⟩ := certifyBFV?_paramsOK x c h
  obtain ⟨hℓ1, hℓL, -, h2, hL, hR⟩ := mul_facts h hin hm hat (i := .square d a) rfl hx
  rw [slackAt_behz] at h2 hL hR
  exact Validation.BFVMul.stepOK_square_behz x.P hP (c.budget n) s hs ρ ρ' σ d a xa ca B msk mt
    hL hR hstep hx ha hla h2x hℓ1 hℓL (band (band h2).1).2

/-- Idealised exact P-over-Q at a level whose slack is `poverqAt … false`. -/
theorem poverq_exact (P : FullParams) (hP : SchemeParamsOK P) (E : TraceBFV.Budget)
    (Ps : List ℕ)
    (s : IntPoly P.src.N) (hs : SecretOK P.secretBound s) (d a b : Var)
    (ρ ρ' : Env P.src)
    (σ : Trace.CtEnv P) (xa xb : Val P.src) (ca cb : List (IntPoly P.src.N))
    (hstep : step P.src ρ (.mul d a b) = some ρ') (hx : ρ a = some xa) (hy : ρ b = some xb)
    (ha : σ a = some ca) (hb : σ b = some cb)
    (hla : ca.length = 2) (hlb : cb.length = 2) (h2x : xa.parts = 2) (h2y : xb.parts = 2)
    (hℓ1 : 1 ≤ xa.level) (hℓL : xa.level ≤ P.src.qs.length)
    (h2 : (poverqAt P false xa.level Ps).2 = true)
    (hL : mulLiftNormAt P xa.level (poverqAt P false xa.level Ps).1.e ≤ E.mulLift)
    (hR : mulRoundApprox P (poverqAt P false xa.level Ps).1.rho ≤ E.mulRound) :
    TraceBFV.StepOK P E s ρ ρ' σ
      (σ.set d (poverqMul P.src.t (P.src.qs.take xa.level) (Ps.take xa.level) ca cb))
      (.mul d a b) := by
  have h2'' : (decide (xa.level ≤ Ps.length) && basisOK (P.src.qs.take xa.level) (Ps.take xa.level)
      && poverqAuxOK? P.src.t P.src.N (P.src.qs.take xa.level) (Ps.take xa.level)
      && (!false || floatAuxOK? (P.src.qs.take xa.level) (Ps.take xa.level))) = true :=
    h2
  have h2' := (band h2'').1
  exact Validation.BFVMul.stepOK_mul_poverq P hP E s hs ρ ρ' σ d a b xa xb ca cb
    (Ps.take xa.level) hL hR hstep hx hy ha hb hla hlb h2x h2y hℓ1 hℓL (band h2').2

theorem certifyBFV?_poverq_mul (x : InputBFV) (c : CertificateBFV) (h : certifyBFV? x = some c)
    (Ps : List ℕ) (hm : x.mul = some (.poverq Ps)) (hf : x.floatTol = false)
    (s : IntPoly x.P.src.N) (hs : SecretOK x.P.secretBound s)
    (msgs : Var → Msg x.P.src.t x.P.src.N) (cts : Var → List (IntPoly x.P.src.N))
    (hin : TraceBFV.InputsOK x.P s x.prog msgs cts) (n : ℕ) (d a b : Var)
    (ρ ρ' : Env x.P.src) (hat : AtInstr x msgs n (.mul d a b) ρ)
    (σ : Trace.CtEnv x.P) (xa xb : Val x.P.src) (ca cb : List (IntPoly x.P.src.N))
    (hstep : step x.P.src ρ (.mul d a b) = some ρ') (hx : ρ a = some xa) (hy : ρ b = some xb)
    (ha : σ a = some ca) (hb : σ b = some cb)
    (hla : ca.length = 2) (hlb : cb.length = 2) (h2x : xa.parts = 2) (h2y : xb.parts = 2) :
    TraceBFV.StepOK x.P (c.budget n) s ρ ρ' σ
      (σ.set d (poverqMul x.P.src.t (x.P.src.qs.take xa.level) (Ps.take xa.level) ca cb))
      (.mul d a b) := by
  obtain ⟨hP, -⟩ := certifyBFV?_paramsOK x c h
  obtain ⟨hℓ1, hℓL, -, h2, hL, hR⟩ := mul_facts h hin hm hat (i := .mul d a b) rfl hx
  rw [hf, slackAt_poverq] at h2 hL hR
  exact poverq_exact x.P hP (c.budget n) Ps s hs d a b ρ ρ' σ xa xb ca cb hstep hx hy ha hb hla hlb
    h2x h2y hℓ1 hℓL h2 hL hR

theorem certifyBFV?_leveled_mul (x : InputBFV) (c : CertificateBFV) (h : certifyBFV? x = some c)
    (Ps : List ℕ) (hm : x.mul = some (.leveled Ps)) (hf : x.floatTol = false)
    (s : IntPoly x.P.src.N) (hs : SecretOK x.P.secretBound s)
    (msgs : Var → Msg x.P.src.t x.P.src.N) (cts : Var → List (IntPoly x.P.src.N))
    (hin : TraceBFV.InputsOK x.P s x.prog msgs cts) (n : ℕ) (d a b : Var)
    (ρ ρ' : Env x.P.src) (hat : AtInstr x msgs n (.mul d a b) ρ)
    (σ : Trace.CtEnv x.P) (xa xb : Val x.P.src) (ca cb : List (IntPoly x.P.src.N))
    (hstep : step x.P.src ρ (.mul d a b) = some ρ') (hx : ρ a = some xa) (hy : ρ b = some xb)
    (ha : σ a = some ca) (hb : σ b = some cb)
    (hla : ca.length = 2) (hlb : cb.length = 2) (h2x : xa.parts = 2) (h2y : xb.parts = 2) :
    TraceBFV.StepOK x.P (c.budget n) s ρ ρ' σ
      (σ.set d
        (if xa.level = x.P.src.qs.length ∧ x.drops.getD n 0 ≠ 0 then
          leveledMul x.P.src.t (x.P.src.qs.take xa.level) Ps (x.drops.getD n 0) ca cb
        else poverqMul x.P.src.t (x.P.src.qs.take xa.level) (Ps.take xa.level) ca cb))
      (.mul d a b) := by
  obtain ⟨hP, -⟩ := certifyBFV?_paramsOK x c h
  obtain ⟨hℓ1, hℓL, -, h2, hL, hR⟩ := mul_facts h hin hm hat (i := .mul d a b) rfl hx
  rw [dropsOf_leveled hm, hf, slackAt_leveled] at h2 hL hR
  by_cases hcnd : xa.level = x.P.src.qs.length ∧ x.drops.getD n 0 ≠ 0
  · rw [ite_eq_left hcnd] at h2 hL hR ⊢
    have htop := hcnd.1
    have h2'' : (decide (x.drops.getD n 0 < xa.level) &&
        decide (xa.level - x.drops.getD n 0 ≤ Ps.length) &&
        basisOK (x.P.src.qs.take xa.level) (Ps.take (xa.level - x.drops.getD n 0)) &&
        leveledAuxOK? x.P.src.t x.P.src.N (x.P.src.qs.take xa.level) Ps (x.drops.getD n 0) &&
        (!false || floatAuxOK? (x.P.src.qs.take xa.level)
          (Ps.take (xa.level - x.drops.getD n 0)))) = true := by
      rw [htop]; exact h2
    have h2' := (band h2'').1
    have hL' : mulLiftNormAt x.P xa.level
        (leveledSlack x.P.src.t x.P.src.N (x.P.src.modulus xa.level)
          (x.P.src.modulus (xa.level - x.drops.getD n 0))
          (Ps.take (xa.level - x.drops.getD n 0)).prod xa.level 0 0 0).e
          ≤ (c.budget n).mulLift := by
      rw [htop] at hL ⊢; exact hL
    have hR' : mulRoundApprox x.P
        (leveledSlack x.P.src.t x.P.src.N (x.P.src.modulus xa.level)
          (x.P.src.modulus (xa.level - x.drops.getD n 0))
          (Ps.take (xa.level - x.drops.getD n 0)).prod xa.level 0 0 0).rho
          ≤ (c.budget n).mulRound := by
      rw [htop]; exact hR
    exact Validation.BFVMul.stepOK_mul_leveled x.P hP (c.budget n) s hs ρ ρ' σ d a b xa xb ca cb
      Ps (x.drops.getD n 0) hL' hR' hstep hx hy ha hb hla hlb h2x h2y hℓ1 hℓL (band h2').2
  · rw [ite_eq_right hcnd] at h2 hL hR ⊢
    exact poverq_exact x.P hP (c.budget n) Ps s hs d a b ρ ρ' σ xa xb ca cb hstep hx hy ha hb hla
      hlb h2x h2y hℓ1 hℓL h2 hL hR

/-! ## Realizability of the library's floating-point multiplication -/

theorem certifyBFV?_hps_mul_float (x : InputBFV) (c : CertificateBFV)
    (h : certifyBFV? x = some c) (R : List ℕ) (hm : x.mul = some (.hps R))
    (hft : x.floatTol = true) (A : Spec.Float.Arith) (hA : Spec.Float.Conforms A)
    (s : IntPoly x.P.src.N) (hs : SecretOK x.P.secretBound s)
    (msgs : Var → Msg x.P.src.t x.P.src.N) (cts : Var → List (IntPoly x.P.src.N))
    (hin : TraceBFV.InputsOK x.P s x.prog msgs cts) (n : ℕ) (d a b : Var)
    (ρ ρ' : Env x.P.src) (hat : AtInstr x msgs n (.mul d a b) ρ)
    (σ : Trace.CtEnv x.P) (xa xb : Val x.P.src) (ca cb : List (IntPoly x.P.src.N))
    (hstep : step x.P.src ρ (.mul d a b) = some ρ') (hx : ρ a = some xa) (hy : ρ b = some xb)
    (ha : σ a = some ca) (hb : σ b = some cb)
    (hla : ca.length = 2) (hlb : cb.length = 2) (h2x : xa.parts = 2) (h2y : xb.parts = 2) :
    TraceBFV.StepOK x.P (c.budget n) s ρ ρ' σ
      (σ.set d (Fl.hpsMul (Fl.floatSums A) x.P.src.t (x.P.src.qs.take xa.level) R ca cb))
      (.mul d a b) := by
  obtain ⟨hP, -⟩ := certifyBFV?_paramsOK x c h
  obtain ⟨hℓ1, hℓL, hok, h2, hL, hR⟩ := mul_facts h hin hm hat (i := .mul d a b) rfl hx
  rw [hft, slackAt_hps_true] at hok h2 hL hR
  exact Validation.BFVMul.stepOK_mul_hps_float x.P A hA hP (c.budget n) s hs ρ ρ' σ d a b xa xb ca
    cb R hL hR hok hstep hx hy ha hb hla hlb h2x h2y hℓ1 hℓL (band h2).2

theorem certifyBFV?_hps_square_float (x : InputBFV) (c : CertificateBFV)
    (h : certifyBFV? x = some c) (R : List ℕ) (hm : x.mul = some (.hps R))
    (hft : x.floatTol = true) (A : Spec.Float.Arith) (hA : Spec.Float.Conforms A)
    (s : IntPoly x.P.src.N) (hs : SecretOK x.P.secretBound s)
    (msgs : Var → Msg x.P.src.t x.P.src.N) (cts : Var → List (IntPoly x.P.src.N))
    (hin : TraceBFV.InputsOK x.P s x.prog msgs cts) (n : ℕ) (d a : Var)
    (ρ ρ' : Env x.P.src) (hat : AtInstr x msgs n (.square d a) ρ)
    (σ : Trace.CtEnv x.P) (xa : Val x.P.src) (ca : List (IntPoly x.P.src.N))
    (hstep : step x.P.src ρ (.square d a) = some ρ') (hx : ρ a = some xa)
    (ha : σ a = some ca) (hla : ca.length = 2) (h2x : xa.parts = 2) :
    TraceBFV.StepOK x.P (c.budget n) s ρ ρ' σ
      (σ.set d (Fl.hpsMul (Fl.floatSums A) x.P.src.t (x.P.src.qs.take xa.level) R ca ca))
      (.square d a) := by
  obtain ⟨hP, -⟩ := certifyBFV?_paramsOK x c h
  obtain ⟨hℓ1, hℓL, hok, h2, hL, hR⟩ := mul_facts h hin hm hat (i := .square d a) rfl hx
  rw [hft, slackAt_hps_true] at hok h2 hL hR
  exact Validation.BFVMul.stepOK_square_hps_float x.P A hA hP (c.budget n) s hs ρ ρ' σ d a xa ca
    R hL hR hok hstep hx ha hla h2x hℓ1 hℓL (band h2).2

/-- The library's P-over-Q multiplication at a level whose slack is `poverqAt … true`. -/
theorem poverq_float (P : FullParams) (A : Spec.Float.Arith) (hA : Spec.Float.Conforms A)
    (hP : SchemeParamsOK P) (E : TraceBFV.Budget) (Ps : List ℕ)
    (s : IntPoly P.src.N) (hs : SecretOK P.secretBound s) (d a b : Var)
    (ρ ρ' : Env P.src)
    (σ : Trace.CtEnv P) (xa xb : Val P.src) (ca cb : List (IntPoly P.src.N))
    (hstep : step P.src ρ (.mul d a b) = some ρ') (hx : ρ a = some xa) (hy : ρ b = some xb)
    (ha : σ a = some ca) (hb : σ b = some cb)
    (hla : ca.length = 2) (hlb : cb.length = 2) (h2x : xa.parts = 2) (h2y : xb.parts = 2)
    (hℓ1 : 1 ≤ xa.level) (hℓL : xa.level ≤ P.src.qs.length)
    (h2 : (poverqAt P true xa.level Ps).2 = true)
    (hL : mulLiftNormAt P xa.level (poverqAt P true xa.level Ps).1.e ≤ E.mulLift)
    (hR : mulRoundApprox P (poverqAt P true xa.level Ps).1.rho ≤ E.mulRound) :
    TraceBFV.StepOK P E s ρ ρ' σ
      (σ.set d (Fl.poverqMul (Fl.floatSums A) P.src.t (P.src.qs.take xa.level)
        (Ps.take xa.level) ca cb))
      (.mul d a b) := by
  have h2' : (decide (xa.level ≤ Ps.length) && basisOK (P.src.qs.take xa.level) (Ps.take xa.level)
      && poverqAuxOK? P.src.t P.src.N (P.src.qs.take xa.level) (Ps.take xa.level)
      && (!true || floatAuxOK? (P.src.qs.take xa.level) (Ps.take xa.level))) = true :=
    h2
  have haux : floatAuxOK? (P.src.qs.take xa.level) (Ps.take xa.level) = true := (band h2').2
  have hlenP : (Ps.take xa.level).length ≤ xa.level := by
    rw [List.length_take]; exact Nat.min_le_left _ _
  exact Validation.BFVMul.stepOK_mul_poverq_float P A hA hP E s hs ρ ρ' σ d a b xa xb
    ca cb (Ps.take xa.level) hL hR hstep hx hy ha hb hla hlb h2x h2y hℓ1 hℓL hlenP haux

theorem certifyBFV?_poverq_mul_float (x : InputBFV) (c : CertificateBFV)
    (h : certifyBFV? x = some c) (Ps : List ℕ) (hm : x.mul = some (.poverq Ps))
    (hft : x.floatTol = true) (A : Spec.Float.Arith) (hA : Spec.Float.Conforms A)
    (s : IntPoly x.P.src.N) (hs : SecretOK x.P.secretBound s)
    (msgs : Var → Msg x.P.src.t x.P.src.N) (cts : Var → List (IntPoly x.P.src.N))
    (hin : TraceBFV.InputsOK x.P s x.prog msgs cts) (n : ℕ) (d a b : Var)
    (ρ ρ' : Env x.P.src) (hat : AtInstr x msgs n (.mul d a b) ρ)
    (σ : Trace.CtEnv x.P) (xa xb : Val x.P.src) (ca cb : List (IntPoly x.P.src.N))
    (hstep : step x.P.src ρ (.mul d a b) = some ρ') (hx : ρ a = some xa) (hy : ρ b = some xb)
    (ha : σ a = some ca) (hb : σ b = some cb)
    (hla : ca.length = 2) (hlb : cb.length = 2) (h2x : xa.parts = 2) (h2y : xb.parts = 2) :
    TraceBFV.StepOK x.P (c.budget n) s ρ ρ' σ
      (σ.set d (Fl.poverqMul (Fl.floatSums A) x.P.src.t (x.P.src.qs.take xa.level)
        (Ps.take xa.level) ca cb))
      (.mul d a b) := by
  obtain ⟨hP, -⟩ := certifyBFV?_paramsOK x c h
  obtain ⟨hℓ1, hℓL, -, h2, hL, hR⟩ := mul_facts h hin hm hat (i := .mul d a b) rfl hx
  rw [hft, slackAt_poverq] at h2 hL hR
  exact poverq_float x.P A hA hP (c.budget n) Ps s hs d a b ρ ρ' σ xa xb ca cb hstep hx hy ha hb
    hla hlb h2x h2y hℓ1 hℓL h2 hL hR

theorem certifyBFV?_leveled_mul_float (x : InputBFV) (c : CertificateBFV)
    (h : certifyBFV? x = some c) (Ps : List ℕ) (hm : x.mul = some (.leveled Ps))
    (hft : x.floatTol = true) (A : Spec.Float.Arith) (hA : Spec.Float.Conforms A)
    (s : IntPoly x.P.src.N) (hs : SecretOK x.P.secretBound s)
    (msgs : Var → Msg x.P.src.t x.P.src.N) (cts : Var → List (IntPoly x.P.src.N))
    (hin : TraceBFV.InputsOK x.P s x.prog msgs cts) (n : ℕ) (d a b : Var)
    (ρ ρ' : Env x.P.src) (hat : AtInstr x msgs n (.mul d a b) ρ)
    (σ : Trace.CtEnv x.P) (xa xb : Val x.P.src) (ca cb : List (IntPoly x.P.src.N))
    (hstep : step x.P.src ρ (.mul d a b) = some ρ') (hx : ρ a = some xa) (hy : ρ b = some xb)
    (ha : σ a = some ca) (hb : σ b = some cb)
    (hla : ca.length = 2) (hlb : cb.length = 2) (h2x : xa.parts = 2) (h2y : xb.parts = 2) :
    TraceBFV.StepOK x.P (c.budget n) s ρ ρ' σ
      (σ.set d
        (if xa.level = x.P.src.qs.length ∧ x.drops.getD n 0 ≠ 0 then
          Fl.leveledMul (Fl.floatSums A) x.P.src.t (x.P.src.qs.take xa.level) Ps
            (x.drops.getD n 0) ca cb
        else Fl.poverqMul (Fl.floatSums A) x.P.src.t (x.P.src.qs.take xa.level)
          (Ps.take xa.level) ca cb))
      (.mul d a b) := by
  obtain ⟨hP, -⟩ := certifyBFV?_paramsOK x c h
  obtain ⟨hℓ1, hℓL, -, h2, hL, hR⟩ := mul_facts h hin hm hat (i := .mul d a b) rfl hx
  rw [dropsOf_leveled hm, hft, slackAt_leveled] at h2 hL hR
  by_cases hcnd : xa.level = x.P.src.qs.length ∧ x.drops.getD n 0 ≠ 0
  · rw [ite_eq_left hcnd] at h2 hL hR ⊢
    have htop := hcnd.1
    have htk : x.P.src.qs.take xa.level = x.P.src.qs := by rw [htop, List.take_length]
    have h2' : (decide (x.drops.getD n 0 < xa.level) &&
        decide (xa.level - x.drops.getD n 0 ≤ Ps.length) &&
        basisOK (x.P.src.qs.take xa.level) (Ps.take (xa.level - x.drops.getD n 0)) &&
        leveledAuxOK? x.P.src.t x.P.src.N (x.P.src.qs.take xa.level) Ps (x.drops.getD n 0) &&
        (!true || floatAuxOK? (x.P.src.qs.take xa.level)
          (Ps.take (xa.level - x.drops.getD n 0)))) = true := by
      rw [htop]; exact h2
    have haux : floatAuxOK? (x.P.src.qs.take xa.level)
        (Ps.take (xa.level - x.drops.getD n 0)) = true := (band h2').2
    have hL' : mulLiftNormAt x.P xa.level
        (leveledSlack x.P.src.t x.P.src.N (x.P.src.modulus xa.level)
          (x.P.src.modulus (xa.level - x.drops.getD n 0))
          (Ps.take (xa.level - x.drops.getD n 0)).prod xa.level
          (doubleSw xa.level)
          (doubleSr ((x.P.src.qs.take xa.level).drop (xa.level - x.drops.getD n 0)))
          (doubleSr (Ps.take (xa.level - x.drops.getD n 0)))).e ≤ (c.budget n).mulLift := by
      rw [htk]; rw [htop] at hL ⊢; exact hL
    have hR' : mulRoundApprox x.P
        (leveledSlack x.P.src.t x.P.src.N (x.P.src.modulus xa.level)
          (x.P.src.modulus (xa.level - x.drops.getD n 0))
          (Ps.take (xa.level - x.drops.getD n 0)).prod xa.level
          (doubleSw xa.level)
          (doubleSr ((x.P.src.qs.take xa.level).drop (xa.level - x.drops.getD n 0)))
          (doubleSr (Ps.take (xa.level - x.drops.getD n 0)))).rho ≤ (c.budget n).mulRound := by
      rw [htk, htop]; exact hR
    exact Validation.BFVMul.stepOK_mul_leveled_float x.P A hA hP (c.budget n) s hs ρ ρ' σ d a b xa
      xb ca cb Ps (x.drops.getD n 0) hL' hR' hstep hx hy ha hb hla hlb h2x h2y hℓ1 hℓL haux
  · rw [ite_eq_right hcnd] at h2 hL hR ⊢
    exact poverq_float x.P A hA hP (c.budget n) Ps s hs d a b ρ ρ' σ xa xb ca cb hstep hx hy ha hb
      hla hlb h2x h2y hℓ1 hℓL h2 hL hR

/-! ## Realizability of the library's key switch under `HPSPOVERQLEVELED` -/

/-- What a certificate gives at a `relin` or `keySwitch` of a top-level operand under
`HPSPOVERQLEVELED`: the declared drop is below the level, the ciphertext basis passes
`floatAuxOK?`, and the key-switching number of the instruction's budget covers the drop. -/
theorem ks_facts {x : InputBFV} {c : CertificateBFV} (h : certifyBFV? x = some c)
    {Ps : List ℕ} (hm : x.mul = some (.leveled Ps))
    {s : IntPoly x.P.src.N} {msgs : Var → Msg x.P.src.t x.P.src.N}
    {cts : Var → List (IntPoly x.P.src.N)} (hin : TraceBFV.InputsOK x.P s x.prog msgs cts)
    {n : ℕ} {i : Instr} {ρ : Env x.P.src} (hat : AtInstr x msgs n i ρ) (hi : isKS i = true)
    {xa : Val x.P.src} (hx : ρ (operand i) = some xa) (htop : xa.level = x.P.src.qs.length)
    (btgt : ℕ) (hks : ∀ ℓ dr, (bud x ℓ dr i).keySwitch = ksAt x ℓ dr btgt) :
    x.drops.getD n 0 < xa.level ∧ floatAuxOK? (x.P.src.qs.take xa.level) [] = true ∧
      (if x.drops.getD n 0 = 0 then ksBoundAt x.P x.lay (xa.level - x.drops.getD n 0) else
        ksLeveled x.P.src.N
          (x.P.src.modulus xa.level / x.P.src.modulus (xa.level - x.drops.getD n 0))
          (ksBoundAt x.P x.lay (xa.level - x.drops.getD n 0)) btgt
          (doubleSr ((x.P.src.qs.take xa.level).drop (xa.level - x.drops.getD n 0)))) ≤
        (c.budget n).keySwitch := by
  obtain ⟨hb, hc⟩ := at_facts h hin hat
  rw [levelOf_some hx, dropsOf_leveled hm] at hb hc
  obtain ⟨hdrop, haux⟩ := chk_ks hm hi hc htop
  refine ⟨hdrop, haux, ?_⟩
  rw [hb, hks, ksAt_leveled hm]
  by_cases h0 : x.drops.getD n 0 = 0
  · rw [ite_eq_left h0, ite_eq_right (fun hh => hh.2 h0), h0, Nat.sub_zero]
  · rw [ite_eq_right h0, ite_eq_left ⟨htop, h0⟩]; exact le_max_right _ _

theorem certifyBFV?_leveled_relin (x : InputBFV) (c : CertificateBFV)
    (h : certifyBFV? x = some c) (Ps : List ℕ) (hm : x.mul = some (.leveled Ps))
    (A : Spec.Float.Arith) (hA : Spec.Float.Conforms A) (n : ℕ) :
    ∃ core : IntPoly x.P.src.N → List (IntPoly x.P.src.N × IntPoly x.P.src.N) →
        IntPoly x.P.src.N × IntPoly x.P.src.N,
      ∀ (s : IntPoly x.P.src.N), SecretOK x.P.secretBound s →
      ∀ (keys : List (IntPoly x.P.src.N × IntPoly x.P.src.N)),
        Budget.GadgetKeysOK x.P x.lay x.P.src.qs.length .square s keys →
      ∀ (msgs : Var → Msg x.P.src.t x.P.src.N) (cts : Var → List (IntPoly x.P.src.N)),
        TraceBFV.InputsOK x.P s x.prog msgs cts →
      ∀ (d a : Var) (ρ ρ' : Env x.P.src), AtInstr x msgs n (.relin d a) ρ →
      ∀ (σ : Trace.CtEnv x.P) (xa : Val x.P.src) (ca : List (IntPoly x.P.src.N)),
        step x.P.src ρ (.relin d a) = some ρ' → ρ a = some xa → σ a = some ca →
        ca.length = 3 → xa.level = x.P.src.qs.length →
        TraceBFV.StepOK x.P (c.budget n) s ρ ρ' σ
          (σ.set d (Fl.leveledKS (Fl.floatSums A) (x.P.src.qs.take xa.level) (x.drops.getD n 0)
            (fun c2 => core c2
              (keys.take (x.lay.sizes (xa.level - x.drops.getD n 0)).length)) ca))
          (.relin d a) := by
  obtain ⟨hP, hk, hS, hlay, -⟩ := certifyBFV?_paramsOK x c h
  by_cases hr : Budget.restrictsTo x.lay x.P.src.qs.length
      (x.P.src.qs.length - x.drops.getD n 0) = true
  · obtain ⟨core, hcore⟩ := Validation.BFVMul.ksCore_realizable x.P x.lay hP hk hS _
      (Nat.sub_le _ _) hr
    refine ⟨core, ?_⟩
    intro s hs keys hkeys msgs cts hin d a ρ ρ' hat σ xa ca hstep hx ha hla htop
    obtain ⟨hdrop, haux, hE⟩ := ks_facts h hm hin hat (i := .relin d a) rfl hx htop
      (x.P.src.N * x.P.secretBound * x.P.secretBound) (fun _ _ => rfl)
    have hco := hcore s hs .square keys hkeys
    rw [← htop] at hco
    exact Validation.BFVMul.stepOK_relin_leveled_tol x.P (Fl.floatSums A)
      (Validation.BFVMul.floatSums_ok A hA) hP (c.budget n) s hs ρ ρ' σ d a xa ca
      (x.drops.getD n 0) (ksBoundAt x.P x.lay (xa.level - x.drops.getD n 0)) _ hco hE hstep hx ha
      hla (le_of_eq htop) hdrop haux
  · refine ⟨fun _ _ => (0, 0), ?_⟩
    intro s hs keys hkeys msgs cts hin d a ρ ρ' hat σ xa ca hstep hx ha hla htop
    obtain ⟨hdrop, -, -⟩ := ks_facts h hm hin hat (i := .relin d a) rfl hx htop
      (x.P.src.N * x.P.secretBound * x.P.secretBound) (fun _ _ => rfl)
    exact absurd (hlay _ (by omega) (Nat.sub_le _ _)).2 hr

theorem certifyBFV?_leveled_keySwitch (x : InputBFV) (c : CertificateBFV)
    (h : certifyBFV? x = some c) (Ps : List ℕ) (hm : x.mul = some (.leveled Ps))
    (A : Spec.Float.Arith) (hA : Spec.Float.Conforms A) (n : ℕ) :
    ∃ core : IntPoly x.P.src.N → List (IntPoly x.P.src.N × IntPoly x.P.src.N) →
        IntPoly x.P.src.N × IntPoly x.P.src.N,
      ∀ (s : IntPoly x.P.src.N), SecretOK x.P.secretBound s →
      ∀ (msgs : Var → Msg x.P.src.t x.P.src.N) (cts : Var → List (IntPoly x.P.src.N)),
        TraceBFV.InputsOK x.P s x.prog msgs cts →
      ∀ (d a : Var) (ρ ρ' : Env x.P.src), AtInstr x msgs n (.keySwitch d a) ρ →
      ∀ (σ : Trace.CtEnv x.P) (xa : Val x.P.src) (ca : List (IntPoly x.P.src.N)),
        step x.P.src ρ (.keySwitch d a) = some ρ' → ρ a = some xa → σ a = some ca →
        ca.length = 2 → xa.level = x.P.src.qs.length →
      ∀ (keys : List (IntPoly x.P.src.N × IntPoly x.P.src.N)),
        Budget.GadgetKeysOK x.P x.lay x.P.src.qs.length (.galois xa.key) s keys →
        TraceBFV.StepOK x.P (c.budget n) s ρ ρ' σ
          (σ.set d (Fl.leveledKS (Fl.floatSums A) (x.P.src.qs.take xa.level) (x.drops.getD n 0)
            (fun c1 => core c1
              (keys.take (x.lay.sizes (xa.level - x.drops.getD n 0)).length)) ca))
          (.keySwitch d a) := by
  obtain ⟨hP, hk, hS, hlay, -⟩ := certifyBFV?_paramsOK x c h
  obtain ⟨-, -, -, -, hB, -⟩ := certifyBFV?_spec x c h
  obtain ⟨-, hdecl, -⟩ := Validation.BFV.PerInstrAux.refAnalyzeAt_some hB
  by_cases hr : Budget.restrictsTo x.lay x.P.src.qs.length
      (x.P.src.qs.length - x.drops.getD n 0) = true
  · obtain ⟨core, hcore⟩ := Validation.BFVMul.ksCore_realizable x.P x.lay hP hk hS _
      (Nat.sub_le _ _) hr
    refine ⟨core, ?_⟩
    intro s hs msgs cts hin d a ρ ρ' hat σ xa ca hstep hx ha hla htop keys hkeys
    obtain ⟨hdrop, haux, hE⟩ := ks_facts h hm hin hat (i := .keySwitch d a) rfl hx htop
      x.P.secretBound (fun _ _ => rfl)
    have hodd : xa.key % 2 = 1 := by
      obtain ⟨pre, post, -, -, hρ⟩ := hat
      exact Validation.BFVMul.run_key_odd x.P.src x.prog msgs hdecl pre ρ hρ a xa hx
    have hco := hcore s hs (.galois xa.key) keys hkeys
    rw [← htop] at hco
    exact Validation.BFVMul.stepOK_keySwitch_leveled_tol x.P (Fl.floatSums A)
      (Validation.BFVMul.floatSums_ok A hA) hP (c.budget n) s hs ρ ρ' σ d a xa ca
      (x.drops.getD n 0) (ksBoundAt x.P x.lay (xa.level - x.drops.getD n 0)) _ hco hE hstep hx ha
      hla hodd (le_of_eq htop) hdrop haux
  · refine ⟨fun _ _ => (0, 0), ?_⟩
    intro s hs msgs cts hin d a ρ ρ' hat σ xa ca hstep hx ha hla htop keys hkeys
    obtain ⟨hdrop, -, -⟩ := ks_facts h hm hin hat (i := .keySwitch d a) rfl hx htop
      x.P.secretBound (fun _ _ => rfl)
    exact absurd (hlay _ (by omega) (Nat.sub_le _ _)).2 hr

/-! ## The assumptions -/

theorem certifyBFV?_leveled_relin_drop0 (x : InputBFV) (c : CertificateBFV)
    (h : certifyBFV? x = some c) (Ps : List ℕ) (hm : x.mul = some (.leveled Ps))
    (A : Spec.Float.Arith) (n : ℕ) (h0 : x.drops.getD n 0 = 0) :
    ∃ core : IntPoly x.P.src.N → List (IntPoly x.P.src.N × IntPoly x.P.src.N) →
        IntPoly x.P.src.N × IntPoly x.P.src.N,
      ∀ (s : IntPoly x.P.src.N), SecretOK x.P.secretBound s →
      ∀ (keys : List (IntPoly x.P.src.N × IntPoly x.P.src.N)),
        Budget.GadgetKeysOK x.P x.lay x.P.src.qs.length .square s keys →
      ∀ (msgs : Var → Msg x.P.src.t x.P.src.N) (cts : Var → List (IntPoly x.P.src.N)),
        TraceBFV.InputsOK x.P s x.prog msgs cts →
      ∀ (d a : Var) (ρ ρ' : Env x.P.src), AtInstr x msgs n (.relin d a) ρ →
      ∀ (σ : Trace.CtEnv x.P) (xa : Val x.P.src) (ca : List (IntPoly x.P.src.N)),
        step x.P.src ρ (.relin d a) = some ρ' → ρ a = some xa → σ a = some ca →
        ca.length = 3 → xa.level = x.P.src.qs.length →
        TraceBFV.StepOK x.P (c.budget n) s ρ ρ' σ
          (σ.set d (Fl.leveledKS (Fl.floatSums A) (x.P.src.qs.take xa.level) 0
            (fun c2 => core c2 (keys.take (x.lay.sizes xa.level).length)) ca))
          (.relin d a) := by
  obtain ⟨core, hcore⟩ := certifyBFV?_leveled_relin x c h Ps hm Spec.Float.exact
    Validation.BFVMul.exact_conforms n
  refine ⟨core, ?_⟩
  intro s hs keys hkeys msgs cts hin d a ρ ρ' hat σ xa ca hstep hx ha hla htop
  have := hcore s hs keys hkeys msgs cts hin d a ρ ρ' hat σ xa ca hstep hx ha hla htop
  rw [h0, Nat.sub_zero] at this
  rwa [Validation.BFVMul.leveledKS_drop_zero A Spec.Float.exact]

theorem certifyBFV?_leveled_keySwitch_drop0 (x : InputBFV) (c : CertificateBFV)
    (h : certifyBFV? x = some c) (Ps : List ℕ) (hm : x.mul = some (.leveled Ps))
    (A : Spec.Float.Arith) (n : ℕ) (h0 : x.drops.getD n 0 = 0) :
    ∃ core : IntPoly x.P.src.N → List (IntPoly x.P.src.N × IntPoly x.P.src.N) →
        IntPoly x.P.src.N × IntPoly x.P.src.N,
      ∀ (s : IntPoly x.P.src.N), SecretOK x.P.secretBound s →
      ∀ (msgs : Var → Msg x.P.src.t x.P.src.N) (cts : Var → List (IntPoly x.P.src.N)),
        TraceBFV.InputsOK x.P s x.prog msgs cts →
      ∀ (d a : Var) (ρ ρ' : Env x.P.src), AtInstr x msgs n (.keySwitch d a) ρ →
      ∀ (σ : Trace.CtEnv x.P) (xa : Val x.P.src) (ca : List (IntPoly x.P.src.N)),
        step x.P.src ρ (.keySwitch d a) = some ρ' → ρ a = some xa → σ a = some ca →
        ca.length = 2 → xa.level = x.P.src.qs.length →
      ∀ (keys : List (IntPoly x.P.src.N × IntPoly x.P.src.N)),
        Budget.GadgetKeysOK x.P x.lay x.P.src.qs.length (.galois xa.key) s keys →
        TraceBFV.StepOK x.P (c.budget n) s ρ ρ' σ
          (σ.set d (Fl.leveledKS (Fl.floatSums A) (x.P.src.qs.take xa.level) 0
            (fun c1 => core c1 (keys.take (x.lay.sizes xa.level).length)) ca))
          (.keySwitch d a) := by
  obtain ⟨core, hcore⟩ := certifyBFV?_leveled_keySwitch x c h Ps hm Spec.Float.exact
    Validation.BFVMul.exact_conforms n
  refine ⟨core, ?_⟩
  intro s hs msgs cts hin d a ρ ρ' hat σ xa ca hstep hx ha hla htop keys hkeys
  have := hcore s hs msgs cts hin d a ρ ρ' hat σ xa ca hstep hx ha hla htop keys hkeys
  rw [h0, Nat.sub_zero] at this
  rwa [Validation.BFVMul.leveledKS_drop_zero A Spec.Float.exact]

theorem ksDropped_iff (x : InputBFV) :
    ksDropped x = true ↔
      ∃ n i, x.prog.body[n]? = some i ∧ isKS i = true ∧ x.drops.getD n 0 ≠ 0 := by
  have hdef : ksDropped x = (List.range x.prog.body.length).any fun n =>
      (x.prog.body[n]?.map isKS).getD false && x.drops.getD n 0 != 0 := rfl
  rw [hdef, List.any_eq_true]
  constructor
  · rintro ⟨n, hn, hb⟩
    have hn' : n < x.prog.body.length := List.mem_range.mp hn
    rw [Bool.and_eq_true] at hb
    refine ⟨n, x.prog.body[n], List.getElem?_eq_getElem hn', ?_, ?_⟩
    · simpa [List.getElem?_eq_getElem hn'] using hb.1
    · simpa using hb.2
  · rintro ⟨n, i, hi, hks, hd⟩
    have hn' : n < x.prog.body.length := (List.getElem?_eq_some_iff.mp hi).1
    refine ⟨n, List.mem_range.mpr hn', ?_⟩
    rw [Bool.and_eq_true]
    exact ⟨by simp [hi, hks], by simpa using hd⟩

/-- `assumptionsOf`, as a function of its pieces (so that it can be computed on in this module). -/
def asm (m : Option Technique) (ft mults ks top : Bool) : List AssumptionBFV :=
  (match m with
  | some (.hps _) | some (.poverq _) => if mults then [if ft then .binary64 else .idealised] else []
  | some (.leveled _) => (if mults || ks then [if ft then .binary64 else .idealised] else []) ++
      (if top then [.declaredDrops] else [])
  | _ => []) ++
  (match m with
  | some (.hps _) | some (.poverq _) | some (.leveled _) | some (.behz ..) => [.binary64Dec]
  | _ => [])

theorem assumptionsOf_eq (x : InputBFV) :
    assumptionsOf x = asm x.mul x.floatTol (!(mulLevels x.P.src x.prog).isEmpty)
      (ksDropped x) ((opLevels x.P.src x.prog).contains x.P.src.qs.length) := by
  rcases x with ⟨P, lay, prog, mul, ft, pa, ms, drops⟩
  rcases mul with _ | t
  · rfl
  · cases t <;> rfl

theorem certifyBFV?_assumed (x : InputBFV) (c : CertificateBFV) (h : certifyBFV? x = some c) :
    (AssumptionBFV.binary64 ∈ c.assumed ↔
      x.floatTol = true ∧
        ((c.mulLevels ≠ [] ∧
            ((∃ R, x.mul = some (.hps R)) ∨ (∃ Ps, x.mul = some (.poverq Ps)) ∨
              ∃ Ps, x.mul = some (.leveled Ps))) ∨
          ((∃ n i, x.prog.body[n]? = some i ∧ isKS i = true ∧ x.drops.getD n 0 ≠ 0) ∧
            ∃ Ps, x.mul = some (.leveled Ps)))) ∧
    (AssumptionBFV.idealised ∈ c.assumed ↔
      x.floatTol = false ∧
        ((c.mulLevels ≠ [] ∧
            ((∃ R, x.mul = some (.hps R)) ∨ (∃ Ps, x.mul = some (.poverq Ps)) ∨
              ∃ Ps, x.mul = some (.leveled Ps))) ∨
          ((∃ n i, x.prog.body[n]? = some i ∧ isKS i = true ∧ x.drops.getD n 0 ≠ 0) ∧
            ∃ Ps, x.mul = some (.leveled Ps)))) ∧
    (AssumptionBFV.declaredDrops ∈ c.assumed ↔
      (∃ Ps, x.mul = some (.leveled Ps)) ∧ x.P.src.qs.length ∈ opLevels x.P.src x.prog) ∧
    (AssumptionBFV.binary64Dec ∈ c.assumed ↔ x.mul ≠ none ∧ x.mul ≠ some .textbook) ∧
    ¬ (AssumptionBFV.binary64 ∈ c.assumed ∧ AssumptionBFV.idealised ∈ c.assumed) := by
  obtain ⟨-, -, hML, hA, -⟩ := certifyBFV?_spec x c h
  rw [hA, hML, assumptionsOf_eq, ← ksDropped_iff]
  have hmem : (x.P.src.qs.length ∈ opLevels x.P.src x.prog) ↔
      (opLevels x.P.src x.prog).contains x.P.src.qs.length = true := by simp
  rw [hmem]
  generalize (opLevels x.P.src x.prog).contains x.P.src.qs.length = top
  generalize ksDropped x = ks
  generalize mulLevels x.P.src x.prog = ml
  rcases x.mul with _ | m
  · simp [asm]
  · cases m <;> cases hft : x.floatTol <;> cases ks <;> cases ml <;> cases top <;> simp [asm]

/-! ## Discrimination -/

theorem certifyBFV?_accepts_behz :
    (certifyBFV? (tinyIn mulProg (some behzTech) true)).map (·.assumed) = some [.binary64Dec] := by
  decide +kernel

theorem certifyBFV?_accepts_hps :
    (certifyBFV? (tinyIn mulProg (some (.hps hpsAux)) false)).map (·.assumed) =
      some [.idealised, .binary64Dec] := by
  decide +kernel

theorem certifyBFV?_accepts_hps_binary64 :
    (certifyBFV? (tinyIn mulProg (some (.hps hpsAux)) true)).map (·.assumed) =
      some [.binary64, .binary64Dec] := by
  decide +kernel

theorem certifyBFV?_rejects_packedWindow :
    (certifyBFV? (addAtT 32769)).isSome = true ∧ (certifyBFV? (addAtT 32771)).isSome = false := by
  constructor <;> decide +kernel

theorem certifyBFV?_encodeOK (x : InputBFV) (c : CertificateBFV) (h : certifyBFV? x = some c) :
    x.P.src.t - 1 ≤ x.P.src.qs.headD 0 / 2 ∧ ∀ q ∈ x.P.src.qs, x.P.src.t ≤ q :=
  (checks h).encode

theorem certifyBFV?_rejects_badAux :
    (certifyBFV? (tinyIn mulProg (some (.hps hpsAuxSmall)) false)).isSome = false := by
  decide +kernel

theorem certifyBFV?_rejects_badLayout :
    (certifyBFV? ⟨tinyBFV, badLayout, mulProg, some .textbook, false, none, true, []⟩).isSome =
      false := by
  decide +kernel

theorem certifyBFV?_rejects_rotatedKey :
    (certifyBFV? (tinyIn
      { inputs := [⟨"a", 2, 2, 1, 1⟩], body := [.automorph "o" "a" 3], outputs := ["o"] }
      none false)).isSome = false := by
  decide +kernel

theorem certifyBFV?_rejects_overflow :
    (certifyBFV? (tinyIn
      { inputs := [⟨"a", 2, 2, 1, 1⟩],
        body := [.square "c" "a", .square "c" "c", .square "c" "c", .square "c" "c"],
        outputs := ["c"] } (some .textbook) false)).isSome = false := by
  decide +kernel

theorem certifyBFV?_rejects_square_poverq :
    (certifyBFV? (tinyIn
      { inputs := [⟨"a", 2, 2, 1, 1⟩], body := [.square "c" "a", .relin "c" "c"],
        outputs := ["c"] } (some (.poverq [1000003, 1000033])) false)).isSome = false := by
  decide +kernel

example := (@certifyBFV?_spec :
  type_of% @Challenge.CertifyBFV.certifyBFV?_spec)
example := (@certifyBFV?_paramsOK :
  type_of% @Challenge.CertifyBFV.certifyBFV?_paramsOK)
example := (@certifyBFV?_inputs :
  type_of% @Challenge.CertifyBFV.certifyBFV?_inputs)
example := (@certifyBFV?_budget :
  type_of% @Challenge.CertifyBFV.certifyBFV?_budget)
example := (@certifyBFV?_sound :
  type_of% @Challenge.CertifyBFV.certifyBFV?_sound)
example := (@certifyBFV?_decrypts :
  type_of% @Challenge.CertifyBFV.certifyBFV?_decrypts)
example := (@certifyBFV?_mulLevels :
  type_of% @Challenge.CertifyBFV.certifyBFV?_mulLevels)
example := (@certifyBFV?_textbook_mul :
  type_of% @Challenge.CertifyBFV.certifyBFV?_textbook_mul)
example := (@certifyBFV?_textbook_square :
  type_of% @Challenge.CertifyBFV.certifyBFV?_textbook_square)
example := (@certifyBFV?_hps_mul :
  type_of% @Challenge.CertifyBFV.certifyBFV?_hps_mul)
example := (@certifyBFV?_hps_square :
  type_of% @Challenge.CertifyBFV.certifyBFV?_hps_square)
example := (@certifyBFV?_behz_mul :
  type_of% @Challenge.CertifyBFV.certifyBFV?_behz_mul)
example := (@certifyBFV?_behz_square :
  type_of% @Challenge.CertifyBFV.certifyBFV?_behz_square)
example := (@certifyBFV?_poverq_mul :
  type_of% @Challenge.CertifyBFV.certifyBFV?_poverq_mul)
example := (@certifyBFV?_leveled_mul :
  type_of% @Challenge.CertifyBFV.certifyBFV?_leveled_mul)
example := (@certifyBFV?_textbook_run_exists :
  type_of% @Challenge.CertifyBFV.certifyBFV?_textbook_run_exists)
example := (@certifyBFV?_hps_mul_float :
  type_of% @Challenge.CertifyBFV.certifyBFV?_hps_mul_float)
example := (@certifyBFV?_hps_square_float :
  type_of% @Challenge.CertifyBFV.certifyBFV?_hps_square_float)
example := (@certifyBFV?_poverq_mul_float :
  type_of% @Challenge.CertifyBFV.certifyBFV?_poverq_mul_float)
example := (@certifyBFV?_leveled_mul_float :
  type_of% @Challenge.CertifyBFV.certifyBFV?_leveled_mul_float)
example := (@certifyBFV?_leveled_relin :
  type_of% @Challenge.CertifyBFV.certifyBFV?_leveled_relin)
example := (@certifyBFV?_leveled_keySwitch :
  type_of% @Challenge.CertifyBFV.certifyBFV?_leveled_keySwitch)
example := (@certifyBFV?_leveled_relin_drop0 :
  type_of% @Challenge.CertifyBFV.certifyBFV?_leveled_relin_drop0)
example := (@certifyBFV?_leveled_keySwitch_drop0 :
  type_of% @Challenge.CertifyBFV.certifyBFV?_leveled_keySwitch_drop0)
example := (@certifyBFV?_assumed :
  type_of% @Challenge.CertifyBFV.certifyBFV?_assumed)
example := (@certifyBFV?_accepts_behz :
  type_of% @Challenge.CertifyBFV.certifyBFV?_accepts_behz)
example := (@certifyBFV?_accepts_hps :
  type_of% @Challenge.CertifyBFV.certifyBFV?_accepts_hps)
example := (@certifyBFV?_accepts_hps_binary64 :
  type_of% @Challenge.CertifyBFV.certifyBFV?_accepts_hps_binary64)
example := (@certifyBFV?_rejects_badAux :
  type_of% @Challenge.CertifyBFV.certifyBFV?_rejects_badAux)
example := (@certifyBFV?_rejects_badLayout :
  type_of% @Challenge.CertifyBFV.certifyBFV?_rejects_badLayout)
example := (@certifyBFV?_rejects_rotatedKey :
  type_of% @Challenge.CertifyBFV.certifyBFV?_rejects_rotatedKey)
example := (@certifyBFV?_rejects_overflow :
  type_of% @Challenge.CertifyBFV.certifyBFV?_rejects_overflow)
example := (@certifyBFV?_rejects_square_poverq :
  type_of% @Challenge.CertifyBFV.certifyBFV?_rejects_square_poverq)

end Validation.CertifyBFV
