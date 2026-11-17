import Challenge.Scaling
import Validation.Certify

/-!
# Validation.Scaling — proofs of the pins of `Challenge.Scaling`

The invariant `eval_scaled` is an induction over the body: every variable `Source.step` defines
holds `phi •` its plain message, because each rule of `Spec.Scaling.facStep` moves exactly the
scalar `Source.step` puts on the message (`q⁻¹` at a switch, `c` at an adjustment) into `phi`, and
the plain semantics takes the rest. The headline composes it with
`Validation.Certify.certify?_sound` and cancels the decode factor.
-/

namespace Validation.Scaling
open Spec NPoly Scheme Source Correct Spec.Scaling Spec.Decrypt Spec.Certify Spec.Budget
open Challenge.Certify Challenge.Scaling Validation.Ring

/-! ## Scalars on `NPoly` -/

section Smul
variable {R : Type} [CommRing R] {N : ℕ}

theorem smul_add'' (c : R) (a b : NPoly R N) : c • (a + b) = c • a + c • b := by
  ext i; simp [mul_add]

theorem smul_sub'' (c : R) (a b : NPoly R N) : c • (a - b) = c • a - c • b := by
  ext i; simp [mul_sub]

theorem smul_smul'' (c d : R) (a : NPoly R N) : c • (d • a) = (c * d) • a := by
  ext i; simp [mul_assoc]

theorem one_smul'' (a : NPoly R N) : (1 : R) • a = a := by
  ext i; simp

theorem smul_comm'' (c d : R) (a : NPoly R N) : c • (d • a) = d • (c • a) := by
  ext i; simp [mul_left_comm]

theorem smul_mul_smul'' (c d : R) (a b : NPoly R N) : (c • a) * (d • b) = (c * d) • (a * b) := by
  ext k
  simp only [coeff_mul', coeff_smul', Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> ring

theorem automorph_smul'' (g : ℕ) (c : R) (a : NPoly R N) :
    automorph g (c • a) = c • automorph g a := by
  ext k
  simp only [coeff_automorph', coeff_smul', Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> ring

end Smul

/-! ## The invariant -/

theorem opt_failure {α : Type} : (failure : Option α) = none := rfl

section Inv
variable {P : Params}

/-- Every defined variable holds `phi •` its plain message, at the tracked level. -/
def Inv (ρ : Env P) (F : Var → Option (Fac P.t)) (μ : Var → Poly P.t P.N) : Prop :=
  ∀ y v, ρ y = some v → ∃ x, F y = some x ∧ v.msg = .exact (x.phi • μ y) ∧ v.level = x.level

theorem inv_set {ρ : Env P} {F : Var → Option (Fac P.t)} {μ : Var → Poly P.t P.N}
    (h : Inv ρ F μ) (d : Var) (v : Val P) (x : Fac P.t) (m : Poly P.t P.N)
    (hm : v.msg = .exact (x.phi • m)) (hl : v.level = x.level) :
    Inv (ρ.set d v) (upd F d (some x)) (upd μ d m) := by
  intro y w hw
  by_cases hy : y = d
  · subst hy
    simp only [Env.set, ite_true, Option.some.injEq] at hw
    subst hw
    exact ⟨x, by simp [upd], by simp [upd, hm], hl⟩
  · simp only [Env.set, hy, ite_false] at hw
    obtain ⟨x', h1, h2, h3⟩ := h y w hw
    exact ⟨x', by simp [upd, hy, h1], by simp [upd, hy, h2], h3⟩

theorem inv_step (hk : P.kind = .bgv) {ρ ρ' : Env P} {F F' : Var → Option (Fac P.t)}
    {μ : Var → Poly P.t P.N} (tr adj : Bool) (h : Inv ρ F μ) (i : Instr)
    (hs : step P ρ i = some ρ') (hf : facStep P tr adj F i = some F') :
    Inv ρ' F' (plainInstr adj μ i) := by
  cases i with
  | add d a b | sub d a b | addPlain d a b | subPlain d a b =>
    rcases h1 : ρ a with _ | va
    · simp [step, h1] at hs
    rcases h2 : ρ b with _ | vb
    · simp [step, h1, h2] at hs
    obtain ⟨xa, ha, hma, hla⟩ := h a va h1
    obtain ⟨xb, hb, hmb, hlb⟩ := h b vb h2
    simp only [facStep, ha, hb, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
      guard] at hf
    split_ifs at hf with hphi
    all_goals try simp only [opt_failure, Option.bind_none, Option.bind_some, Option.some.injEq,
      reduceCtorEq] at hf
    subst hf
    simp only [step, h1, h2, hma, hmb, Msg.lift₂, Option.bind_eq_bind, Option.bind_some,
      Option.pure_def, guard] at hs
    split_ifs at hs
    all_goals try simp only [opt_failure, Option.bind_none, Option.bind_some, Option.some.injEq,
      reduceCtorEq] at hs
    subst hs
    refine inv_set h d _ xa _ ?_ hla
    simp only [plainInstr, Msg.exact.injEq]
    first
    | rw [smul_add'', hphi]
    | rw [smul_sub'', hphi]
  | mul d a b | mulPlain d a b =>
    rcases h1 : ρ a with _ | va
    · simp [step, h1] at hs
    rcases h2 : ρ b with _ | vb
    · simp [step, h1, h2] at hs
    obtain ⟨xa, ha, hma, hla⟩ := h a va h1
    obtain ⟨xb, hb, hmb, hlb⟩ := h b vb h2
    simp only [facStep, ha, hb, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
      Option.some.injEq] at hf
    subst hf
    simp only [step, h1, h2, hma, hmb, Msg.lift₂, Option.bind_eq_bind, Option.bind_some,
      Option.pure_def, guard] at hs
    split_ifs at hs
    all_goals try simp only [opt_failure, Option.bind_none, Option.bind_some, Option.some.injEq,
      reduceCtorEq] at hs
    subst hs
    refine inv_set h d _ _ _ ?_ hla
    simp only [plainInstr, Msg.exact.injEq, smul_mul_smul'']
  | square d a =>
    rcases h1 : ρ a with _ | va
    · simp [step, h1] at hs
    obtain ⟨xa, ha, hma, hla⟩ := h a va h1
    simp only [facStep, ha, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
      Option.some.injEq] at hf
    subst hf
    simp only [step, h1, hma, Msg.lift₂, Option.bind_eq_bind, Option.bind_some,
      Option.pure_def, guard] at hs
    split_ifs at hs
    all_goals try simp only [opt_failure, Option.bind_none, Option.bind_some, Option.some.injEq,
      reduceCtorEq] at hs
    subst hs
    refine inv_set h d _ _ _ ?_ hla
    simp only [plainInstr, Msg.exact.injEq, smul_mul_smul'']
  | mulConst d a c =>
    rcases h1 : ρ a with _ | va
    · simp [step, h1] at hs
    obtain ⟨xa, ha, hma, hla⟩ := h a va h1
    simp only [facStep, ha, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
      Option.some.injEq] at hf
    subst hf
    simp only [step, h1, hma, Msg.lift₁, Option.bind_eq_bind, Option.bind_some,
      Option.pure_def, Option.some.injEq] at hs
    subst hs
    cases adj
    · refine inv_set h d _ _ _ ?_ hla
      simp only [plainInstr, Msg.exact.injEq, Bool.false_eq_true, ite_false]
      exact smul_comm'' _ _ _
    · refine inv_set h d _ _ _ ?_ hla
      simp only [plainInstr, Msg.exact.injEq, ite_true, smul_smul'']
  | modSwitch d a =>
    rcases h1 : ρ a with _ | va
    · simp [step, h1] at hs
    obtain ⟨xa, ha, hma, hla⟩ := h a va h1
    simp only [step, h1, hma, Msg.lift₁, hk, Option.bind_eq_bind, Option.bind_some,
      Option.pure_def, guard] at hs
    split_ifs at hs with h2
    all_goals try simp only [opt_failure, Option.bind_none, Option.bind_some, reduceCtorEq] at hs
    rcases hq : P.qs[va.level - 1]? with _ | q
    · simp [hq] at hs
    simp only [hq, Option.bind_some, Option.some.injEq] at hs
    subst hs
    simp only [facStep, ha, ← hla, h2, hq, Option.bind_eq_bind, Option.bind_some,
      Option.pure_def, guard, ite_true, Option.some.injEq] at hf
    subst hf
    refine inv_set h d _ _ _ ?_ (by simp [hla])
    simp only [plainInstr, Msg.exact.injEq, smul_smul'']
  | dropLimbs d a k =>
    rcases h1 : ρ a with _ | va
    · simp [step, h1] at hs
    obtain ⟨xa, ha, hma, hla⟩ := h a va h1
    simp only [facStep, ha, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
      Option.some.injEq] at hf
    subst hf
    simp only [step, h1, Option.bind_eq_bind, Option.bind_some, Option.pure_def, guard] at hs
    split_ifs at hs
    all_goals try simp only [opt_failure, Option.bind_none, Option.bind_some, Option.some.injEq,
      reduceCtorEq] at hs
    subst hs
    exact inv_set h d _ _ _ hma (by simp [hla])
  | automorph d a g =>
    rcases h1 : ρ a with _ | va
    · simp [step, h1] at hs
    obtain ⟨xa, ha, hma, hla⟩ := h a va h1
    simp only [facStep, ha, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
      Option.some.injEq] at hf
    subst hf
    simp only [step, h1, hma, Msg.lift₁, Option.bind_eq_bind, Option.bind_some,
      Option.pure_def, guard] at hs
    split_ifs at hs
    all_goals try simp only [opt_failure, Option.bind_none, Option.bind_some, Option.some.injEq,
      reduceCtorEq] at hs
    subst hs
    refine inv_set h d _ _ _ ?_ hla
    simp only [plainInstr, Msg.exact.injEq, automorph_smul'']
  | copy d a | toEval d a | toCoeff d a =>
    rcases h1 : ρ a with _ | va
    · simp [step, h1] at hs
    obtain ⟨xa, ha, hma, hla⟩ := h a va h1
    simp only [facStep, ha, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
      Option.some.injEq] at hf
    subst hf
    simp only [step, h1, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
      Option.some.injEq] at hs
    subst hs
    exact inv_set h d _ _ _ hma hla
  | relin d a | keySwitch d a =>
    rcases h1 : ρ a with _ | va
    · simp [step, h1] at hs
    obtain ⟨xa, ha, hma, hla⟩ := h a va h1
    simp only [facStep, ha, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
      Option.some.injEq] at hf
    subst hf
    simp only [step, h1, Option.bind_eq_bind, Option.bind_some, Option.pure_def, guard] at hs
    split_ifs at hs
    all_goals try simp only [opt_failure, Option.bind_none, Option.bind_some, Option.some.injEq,
      reduceCtorEq] at hs
    subst hs
    exact inv_set h d _ _ _ hma hla

theorem inv_run (hk : P.kind = .bgv) (tr : Bool) : ∀ (body : List Instr) (ms : List Bool)
    (ρ ρ' : Env P) (F F' : Var → Option (Fac P.t)) (μ : Var → Poly P.t P.N),
    Inv ρ F μ → body.foldlM (step P) ρ = some ρ' → facRun P tr body ms F = some F' →
    Inv ρ' F' (plainRun body ms μ)
  | [], _, ρ, ρ', F, F', μ, h, hs, hf => by
    simp only [List.foldlM_nil, Option.pure_def, Option.some.injEq] at hs
    simp only [facRun, Option.some.injEq] at hf
    subst hs hf
    exact h
  | i :: is, ms, ρ, ρ', F, F', μ, h, hs, hf => by
    simp only [List.foldlM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff] at hs
    obtain ⟨ρ1, hs1, hs2⟩ := hs
    simp only [facRun, Option.bind_eq_bind, Option.bind_eq_some_iff] at hf
    obtain ⟨F1, hf1, hf2⟩ := hf
    exact inv_run hk tr is ms.tail ρ1 ρ' F1 F' _ (inv_step hk tr _ h i hs1 hf1) hs2 hf2

end Inv

/-! ## The pins -/

theorem eval_scaled (P : Params) (prog : Program) (sd : ScaleData) (F : Var → Option (Fac P.t))
    (hF : factors? P prog sd = some F) (u : Var → Poly P.t P.N) (ρ : Env P)
    (hρ : eval P prog (scaledMsgs P sd u) = some ρ) (y : Var) (v : Val P) (hy : ρ y = some v) :
    ∃ x, F y = some x ∧ v.msg = .exact (x.phi • plainEval prog sd.marks u y) ∧
      v.level = x.level := by
  simp only [factors?, Option.bind_eq_bind, Option.bind_eq_some_iff, guard,
    Option.pure_def] at hF
  obtain ⟨_, hk0, _, _, hrun⟩ := hF
  have hk : P.kind = .bgv := by
    by_contra hc; simp [hc] at hk0
  simp only [eval, Option.bind_eq_bind, Option.bind_eq_some_iff, guard, Option.pure_def] at hρ
  obtain ⟨_, _, _, _, ρ', h3, _, _, h5⟩ := hρ
  simp only [Option.some.injEq] at h5
  subst h5
  have h0 : Inv (initEnv P prog (scaledMsgs P sd u)) (facInit P prog sd) u := by
    intro z w hw
    simp only [initEnv, Option.map_eq_some_iff] at hw
    obtain ⟨d, hd, rfl⟩ := hw
    exact ⟨⟨inputFactor P sd z, inputFactor P sd z, d.level⟩,
      by simp [facInit, hd], rfl, rfl⟩
  exact inv_run hk sd.tracks prog.body sd.marks _ _ _ F u h0 h3 hrun y v hy

theorem certify?_src (x : Input) (c : Certificate) (h : certify? x = some c) :
    c.params.src = x.P.src := by
  rcases hm : x.mode with _ | ⟨fresh, Bp, Bk, Bu, B1, B2, mn, md, κ⟩ |
    ⟨fresh, Bp, E2, S2, Vu, V1, V2, mn, md, κ⟩
  · rw [(Validation.Certify.certify?_worstCase x c h hm).1]
  · rw [(Validation.Certify.certify?_fresh x c h _ _ _ _ _ _ _ _ _ hm).2.2.1]
  · rw [(Validation.Certify.certify?_freshL2 x c h _ _ _ _ _ _ _ _ _ _ hm).2.2.1]

theorem certify?_user (x : Input) (c : Certificate) (h : certify? x = some c)
    (hsw : x.switched = true) (sd : ScaleData) (hsc : scaleOK? c.params.src x.prog sd = true)
    (s : IntPoly c.params.src.N) (u : Var → Poly c.params.src.t c.params.src.N)
    (cts : Var → List (IntPoly c.params.src.N))
    (hin : InputsOK c.params s x.prog (scaledMsgs c.params.src sd u) cts)
    (hb : Trace.BoundsOK c.params s x.prog (scaledMsgs c.params.src sd u) cts) :
    ∀ σ, Trace.Run c.params c.budget s x.prog.body
        (initEnv c.params.src x.prog (scaledMsgs c.params.src sd u))
        (Trace.initCt c.params x.prog cts) σ →
      ∀ o ∈ x.prog.outputs, ∃ ct dF ℓ, σ o = some ct ∧
        decodeAt? c.params.src x.prog sd o = some (dF, ℓ) ∧
        userDecrypt c.params.src dF ℓ s ct = plainEval x.prog sd.marks u o := by
  intro σ hσ o ho
  obtain ⟨ρ, hev, hrun⟩ := Validation.Certify.certify?_sound x c h s _ cts hin hb
  obtain ⟨v, ct, m, B, hv, hct, _, _, hm, _, _, hsw'⟩ := hrun σ hσ o ho
  have hdec := hsw' hsw
  rcases hF : factors? c.params.src x.prog sd with _ | F
  · simp [scaleOK?, hF] at hsc
  simp only [scaleOK?, hF] at hsc
  have hall := List.all_eq_true.mp hsc o ho
  obtain ⟨xo, hxo, hmo, hlo⟩ := eval_scaled c.params.src x.prog sd F hF u ρ hev o v hv
  rw [hxo] at hall
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hall
  obtain ⟨hd1, hd2⟩ := hall
  refine ⟨ct, decodeFactor c.params.src sd.tracks xo, xo.level, hct,
    by simp [decodeAt?, hF, hxo], ?_⟩
  rw [hm] at hmo
  simp only [Msg.exact.injEq] at hmo
  unfold userDecrypt
  rw [← hlo, hdec, hmo, smul_smul'', smul_smul'', hlo, mul_assoc,
    mul_comm (decScale _ _) xo.phi, ← hd1, mul_comm, hd2, one_smul'']

/-! ## Closed pins -/

theorem adjProg_accepted :
    (certify? (tinyInput adjProg true .worstCase)).isSome = true ∧
    scaleOK? Spec.FullParams.tinyBGV.src adjProg adjSD = true ∧
    decodeNat Spec.FullParams.tinyBGV.src adjProg adjSD "o" = some (13, 1) := by
  decide +kernel

theorem addMismatch_rejected :
    scaleOK? Spec.FullParams.tinyBGV.src addMismatchProg ⟨[("a", 13), ("b", 13)], [], true⟩ =
      false := by
  decide +kernel

theorem mulPlain_factor_rejected :
    scaleOK? Spec.FullParams.tinyBGV.src mulPlainProg ⟨[("a", 13), ("p", 2)], [], true⟩ =
      false := by
  decide +kernel

theorem untracked_switch_rejected :
    scaleOK? Spec.FullParams.tinyBGV.src Challenge.Headline.mulSwitchProg
      ⟨[("a", 1), ("b", 1)], [], false⟩ = false := by
  decide +kernel

theorem nonUnit_rejected :
    scaleOK? Spec.FullParams.tinyBGV.src copyProg ⟨[("a", 17)], [], true⟩ = false := by
  decide +kernel

theorem adjProg_decodeAt :
    decodeAt? Spec.FullParams.tinyBGV.src adjProg adjSD "o" = some (13, 1) := by
  decide +kernel

theorem zmod17_fix : ∀ z : ZMod 17, (13 : ZMod 17)⁻¹ * z = z → z = 0 := by
  decide +kernel

theorem adjProg_raw_ne_plain (s : IntPoly Spec.FullParams.tinyBGV.src.N)
    (u : Var → Poly Spec.FullParams.tinyBGV.src.t Spec.FullParams.tinyBGV.src.N)
    (cts : Var → List (IntPoly Spec.FullParams.tinyBGV.src.N))
    (hin : InputsOK Spec.FullParams.tinyBGV s adjProg
      (scaledMsgs Spec.FullParams.tinyBGV.src adjSD u) cts)
    (hb : Trace.BoundsOK Spec.FullParams.tinyBGV s adjProg
      (scaledMsgs Spec.FullParams.tinyBGV.src adjSD u) cts)
    (σ : Trace.CtEnv Spec.FullParams.tinyBGV)
    (hσ : Trace.Run Spec.FullParams.tinyBGV
      (certified Spec.FullParams.tinyBGV (uniformLayout 1)) s adjProg.body
      (initEnv Spec.FullParams.tinyBGV.src adjProg (scaledMsgs Spec.FullParams.tinyBGV.src adjSD u))
      (Trace.initCt Spec.FullParams.tinyBGV adjProg cts) σ)
    (hne : plainEval adjProg adjSD.marks u "o" ≠ 0) :
    ∃ ct, σ "o" = some ct ∧
      userDecrypt Spec.FullParams.tinyBGV.src 13 1 s ct = plainEval adjProg adjSD.marks u "o" ∧
      bgvDecryptSwitched Spec.FullParams.tinyBGV.src.t (Spec.FullParams.tinyBGV.src.qs.take 1) s
          (ct.map (ofInt (Spec.FullParams.tinyBGV.src.qs.take 1).prod)) ≠
        plainEval adjProg adjSD.marks u "o" := by
  have hsome : (certify? (tinyInput adjProg true .worstCase)).isSome = true := adjProg_accepted.1
  obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp hsome
  have hp : c.params = Spec.FullParams.tinyBGV :=
    (Validation.Certify.certify?_worstCase _ c hc rfl).1
  have hbud : c.budget = certified c.params (uniformLayout 1) :=
    (Validation.Certify.certify?_spec _ c hc).1
  obtain ⟨params, budget, used, eps, drift, bound, outputs⟩ := c
  simp only at hp hbud
  subst hp hbud
  have hsc : scaleOK? Spec.FullParams.tinyBGV.src adjProg adjSD = true := adjProg_accepted.2.1
  obtain ⟨ct, dF, ℓ, hct, hdl, huser⟩ :=
    certify?_user (tinyInput adjProg true .worstCase) _ hc rfl adjSD hsc s u cts hin hb σ hσ "o"
      (show "o" ∈ ["o"] from List.mem_singleton.mpr rfl)
  change decodeAt? Spec.FullParams.tinyBGV.src adjProg adjSD "o" = some (dF, ℓ) at hdl
  rw [adjProg_decodeAt, Option.some.injEq, Prod.mk.injEq] at hdl
  obtain ⟨rfl, rfl⟩ := hdl
  change userDecrypt Spec.FullParams.tinyBGV.src 13 1 s ct = plainEval adjProg adjSD.marks u "o"
    at huser
  refine ⟨ct, hct, huser, fun heq => hne ?_⟩
  unfold userDecrypt at huser
  rw [heq] at huser
  ext i
  have hi := congrArg (fun p => p.coeff i) huser
  simp only [coeff_smul'] at hi
  exact zmod17_fix _ hi

end Validation.Scaling
