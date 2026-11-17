import Challenge.Profile
import Validation.Certify
import Validation.CertifyBFV
import Validation.ParamsRange
import Validation.IndCpaD.Inputs

/-!
# Validation.Profile — proofs of the pins of `Challenge.Profile`

Soundness at a profile is the soundness of the computed-budget certificates with the budget left
as a variable: `Validation.Certify.core` (BGV) and `certifiedAt_decrypts` with
`refAnalyzeBFVAt_sound` (BFV). The budget order is proved by cases on the instruction. The
coverage corollaries instantiate the realizability pins at `E k`. No locked definition is
unfolded by name: the decisions are read through `change` (no equation lemma of a `Challenge`
definition is generated in this module).
-/

namespace Validation.Profile
open Spec NPoly Scheme Source Correct Challenge.Headline Challenge.Certify Challenge.CertifyBFV
  Challenge.BFV Challenge.BFVMul Challenge.Profile Spec.Encrypt

/-! ## Soundness -/

theorem certifyProfile?_some {P : FullParams} {E : Trace.Budget} {prog : Program} {sw : Bool}
    {B : ℕ} {outs : List (Var × ℕ)} (h : certifyProfile? P E prog sw = some (B, outs)) :
    SchemeParamsOK P ∧ P.src.kind = .bgv ∧ refAnalyze P E prog = some B ∧
      prog.outputs.mapM (fun o => (outputBound? P E prog sw o).map fun b => (o, b)) =
        some outs := by
  change (do
    guard (schemeParamsOK? P)
    guard (P.src.kind = .bgv)
    guard (!prog.outputs.isEmpty)
    guard (Challenge.Certify.inputsMsgOK? P prog)
    let B ← refAnalyze P E prog
    let outs ← prog.outputs.mapM fun o => (outputBound? P E prog sw o).map fun b => (o, b)
    pure (B, outs)) = some (B, outs) at h
  simp only [Option.bind_eq_bind, Option.pure_def] at h
  obtain ⟨h1, h⟩ := Validation.Trace.guard_bind_eq_some h
  obtain ⟨hk, h⟩ := Validation.Trace.guard_bind_eq_some h
  obtain ⟨-, h⟩ := Validation.Trace.guard_bind_eq_some h
  obtain ⟨-, h⟩ := Validation.Trace.guard_bind_eq_some h
  obtain ⟨B', hB, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨outs', ho, h⟩ := Option.bind_eq_some_iff.mp h
  cases h
  exact ⟨Validation.Params.schemeParamsOK?_sound P h1, hk, hB, ho⟩

/-- The input check of `certifyProfile?`. -/
theorem certifyProfile?_inputsMsgOK {P : FullParams} {E : Trace.Budget} {prog : Program}
    {sw : Bool} {B : ℕ} {outs : List (Var × ℕ)} (h : certifyProfile? P E prog sw = some (B, outs)) :
    Challenge.Certify.inputsMsgOK? P prog = true := by
  change (do
    guard (schemeParamsOK? P)
    guard (P.src.kind = .bgv)
    guard (!prog.outputs.isEmpty)
    guard (Challenge.Certify.inputsMsgOK? P prog)
    let B ← refAnalyze P E prog
    let outs ← prog.outputs.mapM fun o => (outputBound? P E prog sw o).map fun b => (o, b)
    pure (B, outs)) = some (B, outs) at h
  simp only [Option.bind_eq_bind, Option.pure_def] at h
  obtain ⟨-, h⟩ := Validation.Trace.guard_bind_eq_some h
  obtain ⟨-, h⟩ := Validation.Trace.guard_bind_eq_some h
  obtain ⟨-, h⟩ := Validation.Trace.guard_bind_eq_some h
  obtain ⟨hI, -⟩ := Validation.Trace.guard_bind_eq_some h
  exact hI

theorem certifyProfile?_sound (P : FullParams) (E : Trace.Budget) (prog : Program) (sw : Bool)
    (B : ℕ) (outs : List (Var × ℕ)) (h : certifyProfile? P E prog sw = some (B, outs))
    (s : IntPoly P.src.N) (msgs : Var → Msg P.src.t P.src.N)
    (cts : Var → List (IntPoly P.src.N)) (hin : InputsOK P s prog msgs cts)
    (hb : Trace.BoundsOK P s prog msgs cts) :
    OutputsCertified P E prog sw outs s msgs cts := by
  obtain ⟨hP, hk, hB, ho⟩ := certifyProfile?_some h
  obtain ⟨-, hlk⟩ := Validation.Certify.mapM_pair _ _ ho
  exact Validation.Certify.core P E prog sw outs hP hk B hB
    (fun o ho' => by
      obtain ⟨b, hg, hl⟩ := hlk o ho'
      obtain ⟨hr, hc⟩ := Validation.Certify.outputBound?_some hg
      exact ⟨b, hl, hr, hc⟩) s msgs cts hin hb

theorem certifyBFVProfile?_some {P : FullParams} {E : ℕ → TraceBFV.Budget} {prog : Program}
    {B : ℕ} {outs : List (Var × ℕ)} (h : certifyBFVProfile? P E prog = some (B, outs)) :
    SchemeParamsOK P ∧ P.src.kind = .bfv ∧ inputsDecOK P prog = true ∧
      P.src.t - 1 ≤ P.src.qs.headD 0 / 2 ∧ refAnalyzeBFVAt P E prog = some B ∧
      Encrypt.outputsUnderS? P.src prog = true ∧
      prog.outputs.mapM (fun o =>
        (refAnalyzeBFVAt P E { prog with outputs := [o] }).map fun b => (o, b)) = some outs := by
  change (do
    guard (schemeParamsOK? P)
    guard (P.src.kind = .bfv)
    guard (!prog.outputs.isEmpty)
    guard (inputsDecOK P prog)
    guard (Challenge.CertifyBFV.plainBoundsOK P prog)
    guard (P.src.t - 1 ≤ P.src.qs.headD 0 / 2)
    let B ← refAnalyzeBFVAt P E prog
    guard (Encrypt.outputsUnderS? P.src prog)
    let outs ← prog.outputs.mapM fun o =>
      (refAnalyzeBFVAt P E { prog with outputs := [o] }).map fun b => (o, b)
    pure (B, outs)) = some (B, outs) at h
  simp only [Option.bind_eq_bind, Option.pure_def] at h
  obtain ⟨h1, h⟩ := Validation.Trace.guard_bind_eq_some h
  obtain ⟨hk, h⟩ := Validation.Trace.guard_bind_eq_some h
  obtain ⟨-, h⟩ := Validation.Trace.guard_bind_eq_some h
  obtain ⟨hd, h⟩ := Validation.Trace.guard_bind_eq_some h
  obtain ⟨-, h⟩ := Validation.Trace.guard_bind_eq_some h
  obtain ⟨he, h⟩ := Validation.Trace.guard_bind_eq_some h
  obtain ⟨B', hB, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨hU, h⟩ := Validation.Trace.guard_bind_eq_some h
  obtain ⟨outs', ho, h⟩ := Option.bind_eq_some_iff.mp h
  cases h
  exact ⟨Validation.Params.schemeParamsOK?_sound P h1, hk, hd, he, hB, hU, ho⟩

/-- The plaintext-bound check of `certifyBFVProfile?`. -/
theorem certifyBFVProfile?_plain {P : FullParams} {E : ℕ → TraceBFV.Budget} {prog : Program}
    {B : ℕ} {outs : List (Var × ℕ)} (h : certifyBFVProfile? P E prog = some (B, outs)) :
    Challenge.CertifyBFV.plainBoundsOK P prog = true := by
  change (do
    guard (schemeParamsOK? P)
    guard (P.src.kind = .bfv)
    guard (!prog.outputs.isEmpty)
    guard (inputsDecOK P prog)
    guard (Challenge.CertifyBFV.plainBoundsOK P prog)
    guard (P.src.t - 1 ≤ P.src.qs.headD 0 / 2)
    let B ← refAnalyzeBFVAt P E prog
    guard (Encrypt.outputsUnderS? P.src prog)
    let outs ← prog.outputs.mapM fun o =>
      (refAnalyzeBFVAt P E { prog with outputs := [o] }).map fun b => (o, b)
    pure (B, outs)) = some (B, outs) at h
  simp only [Option.bind_eq_bind, Option.pure_def] at h
  obtain ⟨-, h⟩ := Validation.Trace.guard_bind_eq_some h
  obtain ⟨-, h⟩ := Validation.Trace.guard_bind_eq_some h
  obtain ⟨-, h⟩ := Validation.Trace.guard_bind_eq_some h
  obtain ⟨-, h⟩ := Validation.Trace.guard_bind_eq_some h
  obtain ⟨hp, -⟩ := Validation.Trace.guard_bind_eq_some h
  exact hp

theorem certifyBFVProfile?_sound (P : FullParams) (E : ℕ → TraceBFV.Budget) (prog : Program)
    (B : ℕ) (outs : List (Var × ℕ)) (h : certifyBFVProfile? P E prog = some (B, outs))
    (s : IntPoly P.src.N) (msgs : Var → Msg P.src.t P.src.N)
    (cts : Var → List (IntPoly P.src.N)) (hin : TraceBFV.InputsOK P s prog msgs cts) :
    OutputsCertifiedBFV P E prog outs s msgs cts := by
  obtain ⟨hP, hk, -, -, hB, hU, ho⟩ := certifyBFVProfile?_some h
  obtain ⟨-, hlk⟩ := Validation.Certify.mapM_pair _ _ ho
  obtain ⟨ρ, hev, hrun⟩ :=
    Validation.BFVMul.certifiedAt_decrypts P E prog B hP hk hB hU s msgs cts hin
  refine ⟨ρ, hev, fun σ hσ o ho' => ?_⟩
  obtain ⟨v, ct, m, hv, hct, hm, hkey, hd⟩ := hrun σ hσ o ho'
  obtain ⟨b, hbo, hl⟩ := hlk o ho'
  have hin' : TraceBFV.InputsOK P s { prog with outputs := [o] } msgs cts := hin
  obtain ⟨ρ1, hev1, hrun1⟩ :=
    Validation.BFV.refAnalyzeBFVAt_sound P E _ b hP hk hbo s msgs cts hin'
  have f0 := Validation.Certify.eval_body hev
  have f1 := Validation.Certify.eval_body (prog := { prog with outputs := [o] }) hev1
  have e1 : ρ1 = ρ := Option.some.inj (f1.symm.trans f0)
  subst e1
  obtain ⟨v', ct', hv', hct', henc⟩ := hrun1 σ hσ o (List.mem_singleton.mpr rfl)
  have ev : v' = v := Option.some.inj (hv'.symm.trans hv)
  have ec : ct' = ct := Option.some.inj (hct'.symm.trans hct)
  subst ev; subst ec
  exact ⟨v', ct', m, b, hv, hct, hl, henc, hm, hkey, hd⟩

/-- `decOK`, unfolded (local `rfl` equation). -/
theorem decOK_eq (t Q B : ℕ) : decOK t Q B = decide (2 * (t * B + Q % t * (t - 1)) < Q) := rfl

/-- The input clause, at one input ciphertext. -/
theorem inputsDecOK_at {P : FullParams} {prog : Program} (h : inputsDecOK P prog = true)
    (d : Decl) (hd : d ∈ prog.inputs) (hp : d.parts ≠ 1) (hok : d.ok P.src = true) :
    decOK P.src.t (P.src.modulus d.level) (TraceBFV.inputBound P prog d) = true := by
  have h' : (prog.inputs.all fun d => decide (d.parts = 1) || !d.ok P.src ||
      decOK P.src.t (P.src.modulus d.level) (TraceBFV.inputBound P prog d)) = true := h
  have := List.all_eq_true.mp h' d hd
  simpa [hp, hok] using this

theorem certifyBFVProfile?_inputs (P : FullParams) (E : ℕ → TraceBFV.Budget) (prog : Program)
    (B : ℕ) (outs : List (Var × ℕ)) (h : certifyBFVProfile? P E prog = some (B, outs))
    (d : Decl) (hd : d ∈ prog.inputs) (hp : d.parts ≠ 1) :
    decOK P.src.t (P.src.modulus d.level) (TraceBFV.inputBound P prog d) = true := by
  obtain ⟨-, -, hdec, -, hB, -⟩ := certifyBFVProfile?_some h
  obtain ⟨-, hdecl, -⟩ := Validation.BFV.PerInstrAux.refAnalyzeAt_some hB
  exact inputsDecOK_at hdec d hd hp (List.all_eq_true.mp hdecl d hd)

/-! ## The inputs exist -/

theorem decOK_zero {t Q B : ℕ} (h : decOK t Q B = true) : decOK t Q 0 = true := by
  rw [decOK_eq, decide_eq_true_eq] at h ⊢
  refine Nat.lt_of_le_of_lt (Nat.mul_le_mul_left 2 (Nat.add_le_add_right ?_ _)) h
  simp

theorem encrypts_mono_bfv {P : FullParams} (hk : P.src.kind = .bfv) {s : IntPoly P.src.N}
    {b b' : ℕ} {v : Val P.src} {ct : List (IntPoly P.src.N)} {m : Poly P.src.t P.src.N}
    (hm : v.msg = .exact m) (h : Encrypts P s b v ct) (hbb : b ≤ b') : Encrypts P s b' v ct := by
  obtain ⟨hl, h2⟩ := h
  refine ⟨hl, ?_⟩
  revert h2
  simp only [hk, hm]
  exact fun h => ⟨h.1, h.2.trans hbb⟩

theorem certifyBFVProfile?_inputs_exist (P : FullParams) (E : ℕ → TraceBFV.Budget)
    (prog : Program) (B : ℕ) (outs : List (Var × ℕ))
    (h : certifyBFVProfile? P E prog = some (B, outs))
    (hpt : ∀ d ∈ prog.inputs, d.parts = 1 → P.src.t - 1 ≤ TraceBFV.inputBound P prog d)
    (s : IntPoly P.src.N) (m : Var → Poly P.src.t P.src.N) :
    ∃ cts, TraceBFV.InputsOK P s prog (fun x => .exact (m x)) cts := by
  classical
  obtain ⟨hP, hk, hdec, henc, hB, -⟩ := certifyBFVProfile?_some h
  obtain ⟨-, hdecl, -⟩ := Validation.BFV.PerInstrAux.refAnalyzeAt_some hB
  have ht : 0 < P.src.t := by have := hP.plaintext.1; omega
  have hex : ∀ x, ∃ ct, ∀ d, prog.inputs.find? (·.name = x) = some d →
      if d.parts = 1 then
        TraceBFV.PlainOK P s (TraceBFV.inputBound P prog d)
          (inputVal P (fun x => .exact (m x)) d) ct
      else Encrypts P s (TraceBFV.inputBound P prog d) (inputVal P (fun x => .exact (m x)) d) ct := by
    intro x
    rcases hf : prog.inputs.find? (·.name = x) with _ | d
    · exact ⟨[], fun d h => by rw [hf] at h; cases h⟩
    have hmem := List.mem_of_find?_eq_some hf
    have hok := List.all_eq_true.mp hdecl d hmem
    have hok' := hok
    simp only [Decl.ok, decide_eq_true_eq] at hok'
    have hmsg : (inputVal P (fun x => .exact (m x)) d).msg = .exact (m d.name) := rfl
    by_cases hp : d.parts = 1
    · refine ⟨[liftMsg (m d.name)], fun d' hd' => ?_⟩
      cases hd'.symm.trans hf
      simp only [hp, ↓reduceIte]
      have hQ : P.src.t - 1 ≤ P.src.modulus d.level / 2 := by
        have := Validation.IndCpaD.headD_le_modulus P.src d.level hok'.2.1
          (fun q hq => (hP.prime q hq).pos)
        exact henc.trans (Nat.div_le_div_right this)
      exact Validation.IndCpaD.plainOK_liftMsg P s _ _ (m d.name) hp hmsg ht hQ (hpt d hmem hp)
    · have hdo := inputsDecOK_at hdec d hmem hp hok
      obtain ⟨ct, hct⟩ := Validation.BFV.bfv_inputs_exist P hk ht s
        (inputVal P (fun x => .exact (m x)) d) (m d.name) hmsg hok'.1 (decOK_zero hdo)
      refine ⟨ct, fun d' hd' => ?_⟩
      cases hd'.symm.trans hf
      simp only [hp, ↓reduceIte]
      exact encrypts_mono_bfv hk hmsg hct (Nat.zero_le _)
  choose cts hcts using hex
  exact ⟨cts, fun x d hd => hcts x d hd⟩

theorem certifyProfile?_inputs_exist (P : FullParams) (E : Trace.Budget) (prog : Program)
    (sw : Bool) (B : ℕ) (outs : List (Var × ℕ)) (h : certifyProfile? P E prog sw = some (B, outs))
    (hbd : prog.bounds = [])
    (h2 : ∀ d ∈ prog.inputs, d.parts = 2 ∧ P.src.t < P.src.modulus d.level)
    (s : IntPoly P.src.N) (m : Var → Poly P.src.t P.src.N) :
    ∃ cts, InputsOK P s prog (fun x => .exact (m x)) cts ∧
      Trace.BoundsOK P s prog (fun x => .exact (m x)) cts := by
  classical
  obtain ⟨hP, hk, -⟩ := certifyProfile?_some h
  have hex : ∀ x, ∃ ct, ∀ d, prog.inputs.find? (·.name = x) = some d →
      Encrypts P s P.inputNoise (inputVal P (fun x => .exact (m x)) d) ct := by
    intro x
    rcases hf : prog.inputs.find? (·.name = x) with _ | d
    · exact ⟨[], fun d h => by rw [hf] at h; cases h⟩
    obtain ⟨hp2, hQ⟩ := h2 d (List.mem_of_find?_eq_some hf)
    obtain ⟨ct, hct⟩ := Validation.Params.bgv_inputs_exist P hP hk s
      (inputVal P (fun x => .exact (m x)) d) (m d.name) rfl hp2 hQ
    exact ⟨ct, fun d' hd' => by cases hd'.symm.trans hf; exact hct⟩
  choose cts hcts using hex
  refine ⟨cts, fun x d hd => hcts x d hd, fun x d b _ hb => ?_⟩
  simp [Program.boundOf, hbd] at hb

/-! ## Budget order -/

theorem stepOK_mono (P : FullParams) (E E' : Trace.Budget) (hE : BudgetLEBGV E E')
    (s : IntPoly P.src.N) (ρ ρ' : Env P.src) (σ σ' : Trace.CtEnv P) (i : Instr)
    (h : Trace.StepOK P E s ρ ρ' σ σ' i) : Trace.StepOK P E' s ρ ρ' σ σ' i := by
  obtain ⟨hks, hms⟩ := hE
  obtain ⟨v, ct, h1, h2, h3, h4⟩ := h
  refine ⟨v, ct, h1, h2, h3, ?_⟩
  cases i with
  | relin d a =>
    obtain ⟨x, ca, e, hx, ha, he, hd, hφ⟩ := h4
    exact ⟨x, ca, e, hx, ha, he.trans hks, hd, hφ⟩
  | keySwitch d a =>
    obtain ⟨x, ca, e, hx, ha, he, hd, hφ⟩ := h4
    exact ⟨x, ca, e, hx, ha, he.trans hks, hd, hφ⟩
  | modSwitch d a =>
    obtain ⟨x, ca, δ, q, hx, ha, hq, hδ, hd, hdv, hφ⟩ := h4
    exact ⟨x, ca, δ, q, hx, ha, hq, hδ.trans (Nat.mul_le_mul_left q (hms _)), hd, hdv, hφ⟩
  | _ => exact h4

theorem run_mono (P : FullParams) (E E' : Trace.Budget) (hE : BudgetLEBGV E E')
    (s : IntPoly P.src.N) (body : List Instr) (ρ : Env P.src) (σ σf : Trace.CtEnv P)
    (h : Trace.Run P E s body ρ σ σf) : Trace.Run P E' s body ρ σ σf := by
  induction body generalizing ρ σ with
  | nil => exact h
  | cons i is ih =>
    obtain ⟨ρ', σ', hs, hok, hr⟩ := h
    exact ⟨ρ', σ', hs, stepOK_mono P E E' hE s ρ ρ' σ σ' i hok, ih ρ' σ' hr⟩

theorem outputsCertified_mono (P : FullParams) (E E' : Trace.Budget) (hE : BudgetLEBGV E E')
    (prog : Program) (sw : Bool) (bounds : List (Var × ℕ)) (s : IntPoly P.src.N)
    (msgs : Var → Msg P.src.t P.src.N) (cts : Var → List (IntPoly P.src.N))
    (h : OutputsCertified P E' prog sw bounds s msgs cts) :
    OutputsCertified P E prog sw bounds s msgs cts := by
  obtain ⟨ρ, hev, hall⟩ := h
  exact ⟨ρ, hev, fun σ hσ => hall σ (run_mono P E E' hE s _ _ _ σ hσ)⟩

theorem stepOK_mono_bfv (P : FullParams) (E E' : TraceBFV.Budget) (hE : BudgetLEBFV E E')
    (s : IntPoly P.src.N) (ρ ρ' : Env P.src) (σ σ' : Trace.CtEnv P) (i : Instr)
    (h : TraceBFV.StepOK P E s ρ ρ' σ σ' i) : TraceBFV.StepOK P E' s ρ ρ' σ σ' i := by
  obtain ⟨hks, hms, hml, hmr, hpa⟩ := hE
  obtain ⟨v, ct, h1, h2, h3, h4⟩ := h
  refine ⟨v, ct, h1, h2, h3, ?_⟩
  cases i with
  | addPlain d a p =>
    obtain ⟨x, y, ca, cb, δ, hx, hy, ha, hb, hδ, hφ⟩ := h4
    exact ⟨x, y, ca, cb, δ, hx, hy, ha, hb, hδ.trans hpa, hφ⟩
  | subPlain d a p =>
    obtain ⟨x, y, ca, cb, δ, hx, hy, ha, hb, hδ, hφ⟩ := h4
    exact ⟨x, y, ca, cb, δ, hx, hy, ha, hb, hδ.trans hpa, hφ⟩
  | mul d a b =>
    obtain ⟨x, y, ca, cb, ka, kb, X, D, hx, hy, ha, hb, hka, hkb, hD, hX, hφ⟩ := h4
    exact ⟨x, y, ca, cb, ka, kb, X, D, hx, hy, ha, hb, hka.trans hml, hkb.trans hml,
      hD.trans (Nat.mul_le_mul_left _ hmr), hX, hφ⟩
  | square d a =>
    obtain ⟨x, ca, ka, X, D, hx, ha, hka, hD, hX, hφ⟩ := h4
    exact ⟨x, ca, ka, X, D, hx, ha, hka.trans hml, hD.trans (Nat.mul_le_mul_left _ hmr), hX, hφ⟩
  | relin d a =>
    obtain ⟨x, ca, e, hx, ha, he, hφ⟩ := h4
    exact ⟨x, ca, e, hx, ha, he.trans hks, hφ⟩
  | keySwitch d a =>
    obtain ⟨x, ca, e, hx, ha, he, hφ⟩ := h4
    exact ⟨x, ca, e, hx, ha, he.trans hks, hφ⟩
  | modSwitch d a =>
    obtain ⟨x, ca, δ, q, hx, ha, hq, hδ, hdv, hφ⟩ := h4
    exact ⟨x, ca, δ, q, hx, ha, hq, hδ.trans (Nat.mul_le_mul_left q hms), hdv, hφ⟩
  | _ => exact h4

theorem runAt_mono (P : FullParams) (E E' : ℕ → TraceBFV.Budget)
    (hE : ∀ k, BudgetLEBFV (E k) (E' k)) (s : IntPoly P.src.N) (n : ℕ) (body : List Instr)
    (ρ : Env P.src) (σ σf : Trace.CtEnv P) (h : TraceBFV.RunAt P E s n body ρ σ σf) :
    TraceBFV.RunAt P E' s n body ρ σ σf := by
  induction body generalizing n ρ σ with
  | nil => exact h
  | cons i is ih =>
    obtain ⟨ρ', σ', hs, hok, hr⟩ := h
    exact ⟨ρ', σ', hs, stepOK_mono_bfv P (E n) (E' n) (hE n) s ρ ρ' σ σ' i hok,
      ih (n + 1) ρ' σ' hr⟩

theorem outputsCertifiedBFV_mono (P : FullParams) (E E' : ℕ → TraceBFV.Budget)
    (hE : ∀ k, BudgetLEBFV (E k) (E' k)) (prog : Program) (bounds : List (Var × ℕ))
    (s : IntPoly P.src.N) (msgs : Var → Msg P.src.t P.src.N)
    (cts : Var → List (IntPoly P.src.N))
    (h : OutputsCertifiedBFV P E' prog bounds s msgs cts) :
    OutputsCertifiedBFV P E prog bounds s msgs cts := by
  obtain ⟨ρ, hev, hall⟩ := h
  exact ⟨ρ, hev, fun σ hσ => hall σ (runAt_mono P E E' hE s 0 _ _ _ σ hσ)⟩

/-! ## Coverage -/

/-- What the coverage check asks of the budget `Ek` at one instruction (a copy of the body of
`coversBFV?`, equal to it by `rfl`). -/
def needBFV (P : FullParams) (lay : Budget.KSLayout) (U r : ℕ) (Ek : TraceBFV.Budget) :
    Option Instr → Bool
  | some (.mul ..) | some (.square ..) =>
    decide (BudgetBFV.mulLiftApprox P U ≤ Ek.mulLift) &&
      decide (BudgetBFV.mulRoundApprox P r ≤ Ek.mulRound)
  | some (.relin ..) | some (.keySwitch ..) => ksCoversBFV P lay Ek.keySwitch
  | some (.modSwitch ..) => decide (BudgetBFV.msBudget P ≤ Ek.modSwitch)
  | _ => true

theorem coversBFV?_eq (P : FullParams) (lay : Budget.KSLayout) (U r : ℕ) (body : List Instr)
    (E : ℕ → TraceBFV.Budget) :
    coversBFV? P lay U r body E =
      (schemeParamsOK? P && Budget.specialOK? P &&
        (List.range P.src.qs.length).all (fun j => lay.okAt (j + 1)) &&
        (List.range body.length).all fun k => needBFV P lay U r (E k) body[k]?) := rfl

theorem coversBFV?_facts {P : FullParams} {lay : Budget.KSLayout} {U r : ℕ} {body : List Instr}
    {E : ℕ → TraceBFV.Budget} (hc : coversBFV? P lay U r body E = true) :
    SchemeParamsOK P ∧ Budget.SpecialOK P ∧
      (∀ ℓ, 1 ≤ ℓ → ℓ ≤ P.src.qs.length → lay.okAt ℓ = true) ∧
      ∀ k i, body[k]? = some i → needBFV P lay U r (E k) (some i) = true := by
  rw [coversBFV?_eq] at hc
  obtain ⟨hc, h4⟩ := (Bool.and_eq_true _ _).mp hc
  obtain ⟨hc, h3⟩ := (Bool.and_eq_true _ _).mp hc
  obtain ⟨h1, h2⟩ := (Bool.and_eq_true _ _).mp hc
  refine ⟨Validation.Params.schemeParamsOK?_sound P h1, Validation.Budget.specialOK?_sound P h2,
    fun ℓ hℓ1 hℓ => ?_, fun k i hk => ?_⟩
  · have := List.all_eq_true.mp h3 (ℓ - 1) (List.mem_range.mpr (by omega))
    rwa [Nat.sub_add_cancel hℓ1] at this
  · have hlt : k < body.length := by
      by_contra hn
      rw [List.getElem?_eq_none (by omega)] at hk
      cases hk
    have := List.all_eq_true.mp h4 k (List.mem_range.mpr hlt)
    rwa [hk] at this

theorem ksCoversBFV_at {P : FullParams} {lay : Budget.KSLayout} {b : ℕ}
    (h : ksCoversBFV P lay b = true) (ℓ : ℕ) (h1 : 1 ≤ ℓ) (hℓ : ℓ ≤ P.src.qs.length) :
    BudgetBFV.ksBoundAt P lay ℓ ≤ b := by
  have h' : ((List.range P.src.qs.length).all fun j =>
      decide (BudgetBFV.ksBoundAt P lay (j + 1) ≤ b)) = true := h
  have := List.all_eq_true.mp h' (ℓ - 1) (List.mem_range.mpr (by omega))
  rw [Nat.sub_add_cancel h1, decide_eq_true_eq] at this
  exact this

theorem need_mul {P : FullParams} {lay : Budget.KSLayout} {U r : ℕ} {Ek : TraceBFV.Budget}
    {i : Instr} (hi : (∃ d a b, i = .mul d a b) ∨ ∃ d a, i = .square d a)
    (h : needBFV P lay U r Ek (some i) = true) :
    BudgetBFV.mulLiftApprox P U ≤ Ek.mulLift ∧ BudgetBFV.mulRoundApprox P r ≤ Ek.mulRound := by
  have h' : (decide (BudgetBFV.mulLiftApprox P U ≤ Ek.mulLift) &&
      decide (BudgetBFV.mulRoundApprox P r ≤ Ek.mulRound)) = true := by
    rcases hi with ⟨d, a, b, rfl⟩ | ⟨d, a, rfl⟩ <;> exact h
  simpa only [Bool.and_eq_true, decide_eq_true_eq] using h'

theorem coversBFV?_mul (P : FullParams) (lay : Budget.KSLayout) (U r : ℕ) (body : List Instr)
    (E : ℕ → TraceBFV.Budget) (hc : coversBFV? P lay U r body E = true) (k : ℕ) (d a b : Var)
    (hk : body[k]? = some (.mul d a b))
    (s : IntPoly P.src.N) (hs : SecretOK P.secretBound s) (ρ ρ' : Env P.src)
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
    TraceBFV.StepOK P (E k) s ρ ρ' σ (σ.set d out) (.mul d a b) := by
  obtain ⟨hP, -, -, hn⟩ := coversBFV?_facts hc
  obtain ⟨hL, hR⟩ := need_mul (Or.inl ⟨d, a, b, rfl⟩) (hn k _ hk)
  exact Validation.BFVMul.stepOK_mul_approx P hP U r (E k) hL hR s hs ρ ρ' σ d a b x y ca cb
    hstep hx hy ha hb hla hlb h2x h2y hℓ hℓL ua ub X out hua hub hX hUa hUb hround hout

theorem coversBFV?_square (P : FullParams) (lay : Budget.KSLayout) (U r : ℕ) (body : List Instr)
    (E : ℕ → TraceBFV.Budget) (hc : coversBFV? P lay U r body E = true) (k : ℕ) (d a : Var)
    (hk : body[k]? = some (.square d a))
    (s : IntPoly P.src.N) (hs : SecretOK P.secretBound s) (ρ ρ' : Env P.src)
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
    TraceBFV.StepOK P (E k) s ρ ρ' σ (σ.set d out) (.square d a) := by
  obtain ⟨hP, -, -, hn⟩ := coversBFV?_facts hc
  obtain ⟨hL, hR⟩ := need_mul (Or.inr ⟨d, a, rfl⟩) (hn k _ hk)
  exact Validation.BFVMul.stepOK_square_approx P hP U r (E k) hL hR s hs ρ ρ' σ d a x ca
    hstep hx ha hla h2x hℓ hℓL ua X out hua hX hUa hround hout

theorem coversBFV?_relin (P : FullParams) (lay : Budget.KSLayout) (U r : ℕ) (body : List Instr)
    (E : ℕ → TraceBFV.Budget) (hc : coversBFV? P lay U r body E = true) (ℓ : ℕ) (h1 : 1 ≤ ℓ)
    (hℓ : ℓ ≤ P.src.qs.length) :
    ∃ f : List (IntPoly P.src.N) → List (IntPoly P.src.N × IntPoly P.src.N) →
        List (IntPoly P.src.N),
      ∀ (k : ℕ) (d a : Var), body[k]? = some (.relin d a) →
      ∀ (s : IntPoly P.src.N), SecretOK P.secretBound s →
      ∀ (keys : List (IntPoly P.src.N × IntPoly P.src.N)),
        Budget.GadgetKeysOK P lay ℓ .square s keys →
      ∀ (ρ ρ' : Env P.src) (σ : Trace.CtEnv P) (x : Val P.src) (ca : List (IntPoly P.src.N)),
        step P.src ρ (.relin d a) = some ρ' → ρ a = some x → σ a = some ca → x.level = ℓ →
        ca.length = x.parts →
        TraceBFV.StepOK P (E k) s ρ ρ' σ (σ.set d (f ca keys)) (.relin d a) := by
  obtain ⟨hP, hS, hlay, hn⟩ := coversBFV?_facts hc
  obtain ⟨f, hf⟩ := Validation.BFV.relin_realizable P lay hP hS ℓ hℓ (hlay ℓ h1 hℓ)
  refine ⟨f, fun k d a hk s hs keys hkeys ρ ρ' σ x ca e1 e2 e3 e4 e5 => ?_⟩
  have hks : ksCoversBFV P lay (E k).keySwitch = true := hn k _ hk
  exact hf (E k) (ksCoversBFV_at hks ℓ h1 hℓ) s hs keys hkeys ρ ρ' σ d a x ca e1 e2 e3 e4 e5

theorem coversBFV?_keySwitch (P : FullParams) (lay : Budget.KSLayout) (U r : ℕ)
    (body : List Instr) (E : ℕ → TraceBFV.Budget) (hc : coversBFV? P lay U r body E = true)
    (ℓ : ℕ) (h1 : 1 ≤ ℓ) (hℓ : ℓ ≤ P.src.qs.length) :
    ∃ f : List (IntPoly P.src.N) → List (IntPoly P.src.N × IntPoly P.src.N) →
        List (IntPoly P.src.N),
      ∀ (k : ℕ) (d a : Var), body[k]? = some (.keySwitch d a) →
      ∀ (s : IntPoly P.src.N), SecretOK P.secretBound s →
      ∀ (ρ ρ' : Env P.src) (σ : Trace.CtEnv P) (x : Val P.src) (ca : List (IntPoly P.src.N)),
        step P.src ρ (.keySwitch d a) = some ρ' → ρ a = some x → σ a = some ca → x.level = ℓ →
        ca.length = x.parts →
      ∀ (keys : List (IntPoly P.src.N × IntPoly P.src.N)),
        Budget.GadgetKeysOK P lay ℓ (.galois x.key) s keys →
        TraceBFV.StepOK P (E k) s ρ ρ' σ (σ.set d (f ca keys)) (.keySwitch d a) := by
  obtain ⟨hP, hS, hlay, hn⟩ := coversBFV?_facts hc
  obtain ⟨f, hf⟩ := Validation.BFV.keySwitch_realizable P lay hP hS ℓ hℓ (hlay ℓ h1 hℓ)
  refine ⟨f, fun k d a hk s hs ρ ρ' σ x ca e1 e2 e3 e4 e5 keys hkeys => ?_⟩
  have hks : ksCoversBFV P lay (E k).keySwitch = true := hn k _ hk
  exact hf (E k) (ksCoversBFV_at hks ℓ h1 hℓ) s hs ρ ρ' σ d a x ca e1 e2 e3 e4 e5 keys hkeys

theorem coversBFV?_modSwitch (P : FullParams) (lay : Budget.KSLayout) (U r : ℕ)
    (body : List Instr) (E : ℕ → TraceBFV.Budget) (hc : coversBFV? P lay U r body E = true)
    (k : ℕ) (d a : Var) (hk : body[k]? = some (.modSwitch d a))
    (s : IntPoly P.src.N) (hs : SecretOK P.secretBound s) (ρ ρ' : Env P.src)
    (σ : Trace.CtEnv P) (x : Val P.src) (ca : List (IntPoly P.src.N))
    (hstep : step P.src ρ (.modSwitch d a) = some ρ') (hx : ρ a = some x)
    (ha : σ a = some ca) (hℓL : x.level ≤ P.src.qs.length) (h2 : x.parts = 2)
    (hla : ca.length = 2) :
    TraceBFV.StepOK P (E k) s ρ ρ' σ
      (σ.set d (ca.map (bfvModSwitchComp P.src.qs[x.level - 1]!))) (.modSwitch d a) := by
  obtain ⟨hP, -, -, hn⟩ := coversBFV?_facts hc
  have hm : decide (BudgetBFV.msBudget P ≤ (E k).modSwitch) = true := hn k _ hk
  exact Validation.BFV.stepOK_modSwitch_textbook P hP (E k) (decide_eq_true_eq.mp hm) s hs ρ ρ' σ
    d a x ca hstep hx ha hℓL h2 hla

/-! ## Coverage (BGV) -/

theorem coversBGV?_facts {P : FullParams} {lay : Budget.KSLayout} {K : ℕ} {E : Trace.Budget}
    (hc : coversBGV? P lay K E = true) :
    SchemeParamsOK P ∧ P.src.kind = .bgv ∧ Budget.SpecialOK P ∧
      (∀ ℓ, 1 ≤ ℓ → ℓ ≤ P.src.qs.length →
        lay.okAt ℓ = true ∧ Budget.ksBoundAt P lay ℓ ≤ E.keySwitch) ∧
      ∀ k, 1 ≤ k → k ≤ K → Budget.msBudgetAt P k ≤ E.modSwitchAt k := by
  have hc' : (schemeParamsOK? P && decide (P.src.kind = .bgv) && Budget.specialOK? P &&
      (List.range P.src.qs.length).all (fun j =>
        lay.okAt (j + 1) && decide (Budget.ksBoundAt P lay (j + 1) ≤ E.keySwitch)) &&
      (List.range K).all fun j =>
        decide (Budget.msBudgetAt P (j + 1) ≤ E.modSwitchAt (j + 1))) = true := hc
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at hc'
  obtain ⟨⟨⟨⟨h1, hk⟩, h2⟩, h3⟩, h4⟩ := hc'
  refine ⟨Validation.Params.schemeParamsOK?_sound P h1, hk,
    Validation.Budget.specialOK?_sound P h2, fun ℓ hℓ1 hℓ => ?_, fun k hk1 hkK => ?_⟩
  · have := h3 (ℓ - 1) (by omega)
    rwa [Nat.sub_add_cancel hℓ1] at this
  · have := h4 (k - 1) (by omega)
    rwa [Nat.sub_add_cancel hk1] at this

theorem coversBGV?_relin (P : FullParams) (lay : Budget.KSLayout) (K : ℕ) (E : Trace.Budget)
    (hc : coversBGV? P lay K E = true) (ℓ : ℕ) (h1 : 1 ≤ ℓ) (hℓ : ℓ ≤ P.src.qs.length) :
    ∃ f : List (IntPoly P.src.N) → List (IntPoly P.src.N × IntPoly P.src.N) →
        List (IntPoly P.src.N),
      ∀ (s : IntPoly P.src.N), SecretOK P.secretBound s →
      ∀ (keys : List (IntPoly P.src.N × IntPoly P.src.N)),
        Budget.GadgetKeysOK P lay ℓ .square s keys →
      ∀ (ρ ρ' : Env P.src) (σ : Trace.CtEnv P) (d a : Var) (x : Val P.src)
        (ca : List (IntPoly P.src.N)),
        step P.src ρ (.relin d a) = some ρ' → ρ a = some x → σ a = some ca → x.level = ℓ →
        ca.length = x.parts →
        Trace.StepOK P E s ρ ρ' σ (σ.set d (f ca keys)) (.relin d a) := by
  obtain ⟨hP, hk, hS, hl, -⟩ := coversBGV?_facts hc
  obtain ⟨hlay, hb⟩ := hl ℓ h1 hℓ
  obtain ⟨f, hf⟩ := Validation.Budget.relin_realizable P lay hk hP hS ℓ h1 hℓ hlay
  exact ⟨f, hf E hb⟩

theorem coversBGV?_keySwitch (P : FullParams) (lay : Budget.KSLayout) (K : ℕ) (E : Trace.Budget)
    (hc : coversBGV? P lay K E = true) (ℓ : ℕ) (h1 : 1 ≤ ℓ) (hℓ : ℓ ≤ P.src.qs.length) :
    ∃ f : List (IntPoly P.src.N) → List (IntPoly P.src.N × IntPoly P.src.N) →
        List (IntPoly P.src.N),
      ∀ (s : IntPoly P.src.N), SecretOK P.secretBound s →
      ∀ (ρ ρ' : Env P.src) (σ : Trace.CtEnv P) (d a : Var) (x : Val P.src)
        (ca : List (IntPoly P.src.N)),
        step P.src ρ (.keySwitch d a) = some ρ' → ρ a = some x → σ a = some ca → x.level = ℓ →
        ca.length = x.parts →
      ∀ (keys : List (IntPoly P.src.N × IntPoly P.src.N)),
        Budget.GadgetKeysOK P lay ℓ (.galois x.key) s keys →
        Trace.StepOK P E s ρ ρ' σ (σ.set d (f ca keys)) (.keySwitch d a) := by
  obtain ⟨hP, hk, hS, hl, -⟩ := coversBGV?_facts hc
  obtain ⟨hlay, hb⟩ := hl ℓ h1 hℓ
  obtain ⟨f, hf⟩ := Validation.Budget.keySwitch_realizable P lay hk hP hS ℓ h1 hℓ hlay
  exact ⟨f, hf E hb⟩

theorem coversBGV?_modSwitch (P : FullParams) (lay : Budget.KSLayout) (K : ℕ) (E : Trace.Budget)
    (hc : coversBGV? P lay K E = true) (ℓ k : ℕ) (hk1 : 1 ≤ k) (hkK : k ≤ K) :
    ∃ f : List (IntPoly P.src.N) → List (IntPoly P.src.N),
      ∀ (s : IntPoly P.src.N), SecretOK P.secretBound s →
      ∀ (ρ ρ' : Env P.src) (σ : Trace.CtEnv P) (d a : Var) (x : Val P.src)
        (ca : List (IntPoly P.src.N)),
        step P.src ρ (.modSwitch d a) = some ρ' → ρ a = some x → σ a = some ca → x.level = ℓ →
        x.parts = k → ca.length = k →
        Trace.StepOK P E s ρ ρ' σ (σ.set d (f ca)) (.modSwitch d a) := by
  obtain ⟨hP, hk, -, -, hms⟩ := coversBGV?_facts hc
  obtain ⟨f, hf⟩ := Validation.Budget.modSwitch_realizable_parts P hk hP ℓ k
  exact ⟨f, hf E (hms k hk1 hkK)⟩

/-! ## Instances -/

theorem tiny_accepts :
    (certifyBFVProfile? tinyBFV tinyProfile tinyProg).isSome = true ∧
      coversBFV? tinyBFV (Budget.uniformLayout 1) 0 1 tinyProg.body tinyProfile = true ∧
      coversBFV? tinyBFV (Budget.uniformLayout 1) 0 1 tinyProg.body
        (fun _ => ⟨0, 0, 0, 0, 0⟩) = false := by
  decide +kernel

example := (@certifyProfile?_sound : type_of% @Challenge.Profile.certifyProfile?_sound)
example := (@certifyBFVProfile?_sound : type_of% @Challenge.Profile.certifyBFVProfile?_sound)
example := (@certifyBFVProfile?_inputs : type_of% @Challenge.Profile.certifyBFVProfile?_inputs)
example := (@certifyBFVProfile?_inputs_exist :
  type_of% @Challenge.Profile.certifyBFVProfile?_inputs_exist)
example := (@certifyProfile?_inputs_exist :
  type_of% @Challenge.Profile.certifyProfile?_inputs_exist)
example := (@stepOK_mono : type_of% @Challenge.Profile.stepOK_mono)
example := (@run_mono : type_of% @Challenge.Profile.run_mono)
example := (@outputsCertified_mono : type_of% @Challenge.Profile.outputsCertified_mono)
example := (@stepOK_mono_bfv : type_of% @Challenge.Profile.stepOK_mono_bfv)
example := (@runAt_mono : type_of% @Challenge.Profile.runAt_mono)
example := (@outputsCertifiedBFV_mono : type_of% @Challenge.Profile.outputsCertifiedBFV_mono)
example := (@coversBFV?_mul : type_of% @Challenge.Profile.coversBFV?_mul)
example := (@coversBFV?_square : type_of% @Challenge.Profile.coversBFV?_square)
example := (@coversBFV?_relin : type_of% @Challenge.Profile.coversBFV?_relin)
example := (@coversBFV?_keySwitch : type_of% @Challenge.Profile.coversBFV?_keySwitch)
example := (@coversBFV?_modSwitch : type_of% @Challenge.Profile.coversBFV?_modSwitch)
example := (@coversBGV?_relin : type_of% @Challenge.Profile.coversBGV?_relin)
example := (@coversBGV?_keySwitch : type_of% @Challenge.Profile.coversBGV?_keySwitch)
example := (@coversBGV?_modSwitch : type_of% @Challenge.Profile.coversBGV?_modSwitch)
example := (@tiny_accepts : type_of% @Challenge.Profile.tiny_accepts)

end Validation.Profile
