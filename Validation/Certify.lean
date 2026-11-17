import Challenge.Certify
import Validation.FreshNoise.Basic
import Validation.FreshNoise.L2
import Validation.Budget.RunExists
import Validation.ParamsCheck
import Validation.Budget.Restrict

/-!
# Validation.Certify — proofs of the pins of `Challenge.Certify`

Everything is obtained from the existing proofs: `refAnalyze_sound` and
`outputsDecrypt_of_encrypts` applied to each one-output program (runs do not depend on the
outputs), `fresh_inputsOK` for the fresh-encryption mode, and one union bound over the fresh
inputs for the single bad event.
-/

namespace Validation.Certify
open Spec NPoly Scheme Source Correct Spec.Budget Spec.Encrypt Spec.Certify Challenge.Headline
open Challenge.FreshNoise Challenge.FreshNoiseL2 Challenge.Certify MeasureTheory
open ProbabilityTheory
open Validation.Trace Validation.Headline.NoiseAux

/-! ## Unfolding `certify?` -/

theorem checked?_some {P : FullParams} {lay : KSLayout} {prog : Program} {sw : Bool} {B : ℕ}
    {outs : List (Var × ℕ)} (h : checked? P lay prog sw = some (B, outs)) :
    schemeParamsOK? P = true ∧ specialOK? P = true ∧ layoutOK? P lay = true ∧
      prog.outputs ≠ [] ∧ refAnalyze P (certified P lay) prog = some B ∧
      prog.outputs.mapM (fun o =>
        (outputBound? P (certified P lay) prog sw o).map fun b => (o, b)) = some outs ∧
      keysRestrict? P = true ∧ inputsMsgOK? P prog = true := by
  unfold checked? at h
  simp only [Option.bind_eq_bind, Option.pure_def] at h
  obtain ⟨h1, h⟩ := guard_bind_eq_some h
  obtain ⟨h2, h⟩ := guard_bind_eq_some h
  obtain ⟨h3, h⟩ := guard_bind_eq_some h
  obtain ⟨hk, h⟩ := guard_bind_eq_some h
  obtain ⟨h4, h⟩ := guard_bind_eq_some h
  obtain ⟨hI, h⟩ := guard_bind_eq_some h
  obtain ⟨B', hB, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨outs', ho, h⟩ := Option.bind_eq_some_iff.mp h
  cases h
  exact ⟨h1, h2, h3, by simpa using h4, hB, ho, hk, hI⟩

theorem outputBound?_some {P : FullParams} {E : Trace.Budget} {prog : Program} {sw : Bool}
    {o : Var} {b : ℕ} (h : outputBound? P E prog sw o = some b) :
    refAnalyze P E { prog with outputs := [o] } = some b ∧
      certOK? P { prog with outputs := [o] } b sw = true := by
  unfold outputBound? at h
  simp only [Option.bind_eq_bind, Option.pure_def] at h
  obtain ⟨b', hb, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨hc, h⟩ := guard_bind_eq_some h
  cases h
  exact ⟨hb, hc⟩

/-- A list built by `mapM` of `o ↦ (o, g o)`: its first components, and `lookup`. -/
theorem mapM_pair {g : Var → Option ℕ} : ∀ (l : List Var) (outs : List (Var × ℕ)),
    l.mapM (fun o => (g o).map fun b => (o, b)) = some outs →
      outs.map Prod.fst = l ∧ ∀ o ∈ l, ∃ b, g o = some b ∧ outs.lookup o = some b
  | [], outs, h => by
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h
    subst h; simp
  | y :: l, outs, h => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq, Option.map_eq_some_iff] at h
    obtain ⟨_, ⟨b, hb, rfl⟩, outs', ho, rfl⟩ := h
    obtain ⟨ih1, ih2⟩ := mapM_pair l outs' ho
    refine ⟨by simp [ih1], fun o ho' => ?_⟩
    by_cases hoy : o = y
    · subst hoy
      exact ⟨b, hb, by simp [List.lookup]⟩
    · rcases List.mem_cons.mp ho' with rfl | ho'
      · exact absurd rfl hoy
      · obtain ⟨b', hb', hl⟩ := ih2 o ho'
        refine ⟨b', hb', ?_⟩
        have : (o == y) = false := by simpa using hoy
        simp [List.lookup, this, hl]

/-- The bound of one output is at most the bound of the whole program. -/
theorem single_le {P : FullParams} {E : Trace.Budget} {prog : Program} {B b : ℕ} {o : Var}
    (ho : o ∈ prog.outputs) (hB : refAnalyze P E prog = some B)
    (hb : refAnalyze P E { prog with outputs := [o] } = some b) : b ≤ B := by
  obtain ⟨-, -, ρz, β, hrun, -, bs, hbs, rfl⟩ := refAnalyze_some hB
  obtain ⟨-, -, ρz', β', hrun', -, bs', hbs', rfl⟩ := refAnalyze_some hb
  have e : (ρz', β') = (ρz, β) := Option.some.inj (hrun'.symm.trans hrun)
  cases e
  obtain ⟨b1, hb1, hβ⟩ := mapM_some β prog.outputs bs hbs o ho
  simp only [List.mapM_cons, List.mapM_nil, hβ, Option.bind_eq_bind, Option.bind_some,
    Option.pure_def, Option.some.injEq] at hbs'
  subst hbs'
  simp only [List.foldl_cons, List.foldl_nil, Nat.zero_max]
  exact le_foldl_max 0 hb1

theorem certify?_centred (x : Input) (c : Certificate) (h : certify? x = some c) :
    x.msMethod = .centred := by
  by_cases hc : x.msMethod = .centred
  · exact hc
  · unfold certify? at h
    rw [ite_eq_left hc] at h
    cases h

theorem certify?_worstCase (x : Input) (c : Certificate) (h : certify? x = some c)
    (hm : x.mode = .worstCase) : c.params = x.P ∧ c.used = .declared := by
  have hc := certify?_centred x c h
  unfold certify? at h
  rw [ite_eq_right (not_not.mpr hc)] at h
  simp only [hm, Option.bind_eq_bind, Option.pure_def] at h
  obtain ⟨⟨B, outs⟩, -, h⟩ := Option.bind_eq_some_iff.mp h
  cases h
  exact ⟨rfl, rfl⟩

/-- The fresh mode, unfolded: the guards, and the certificate in terms of `freshEps`. -/
theorem certify?_fresh_raw (x : Input) (c : Certificate) (h : certify? x = some c)
    (fresh : List Var) (Bp Bk Bu B1 B2 mn md κ : ℕ)
    (hm : x.mode = .fresh fresh Bp Bk Bu B1 B2 mn md κ) :
    0 < varProxy x.P.src.N x.P.secretBound Bk Bu B1 B2 ∧ 0 < md ∧
    ∃ ε used drift, freshEps x.P fresh.length Bk Bu B1 B2 mn md κ = (ε, used, drift) ∧
      freshOK? { x.P with inputNoise := freshNoise x.P.src.t Bp ε } x.prog fresh = true ∧
      ∃ B outs,
        checked? { x.P with inputNoise := freshNoise x.P.src.t Bp ε } x.lay x.prog x.switched =
          some (B, outs) ∧
        c = ⟨{ x.P with inputNoise := freshNoise x.P.src.t Bp ε },
          certified { x.P with inputNoise := freshNoise x.P.src.t Bp ε } x.lay, used, ε, drift,
          B, outs⟩ := by
  have hc := certify?_centred x c h
  unfold certify? at h
  rw [ite_eq_right (not_not.mpr hc)] at h
  simp only [hm, Option.bind_eq_bind, Option.pure_def] at h
  obtain ⟨hV, h⟩ := guard_bind_eq_some h
  obtain ⟨hmd, h⟩ := guard_bind_eq_some h
  generalize hfe : freshEps x.P fresh.length Bk Bu B1 B2 mn md κ = r at h
  obtain ⟨ε, used, drift⟩ := r
  dsimp only at h
  obtain ⟨hf, h⟩ := guard_bind_eq_some h
  obtain ⟨⟨B, outs⟩, hch, h⟩ := Option.bind_eq_some_iff.mp h
  cases h
  exact ⟨hV, hmd, ε, used, drift, rfl, hf, B, outs, hch, rfl⟩

/-- The `ℓ₂` mode, unfolded. -/
theorem certify?_freshL2_raw (x : Input) (c : Certificate) (h : certify? x = some c)
    (fresh : List Var) (Bp E2 S2 Vu V1 V2 mn md κ : ℕ)
    (hm : x.mode = .freshL2 fresh Bp E2 S2 Vu V1 V2 mn md κ) :
    0 < varProxyL2 E2 S2 Vu V1 V2 ∧ 0 < md ∧
    ∃ P' : FullParams, P' = { x.P with
        inputNoise := freshNoise x.P.src.t Bp
          (epsFor (varProxyL2 E2 S2 Vu V1 V2) (fresh.length * (2 * x.P.src.N)) κ +
            meanDrift (E2 + 1 + S2) mn md) } ∧
      freshOK? P' x.prog fresh = true ∧
      ∃ B outs, checked? P' x.lay x.prog x.switched = some (B, outs) ∧
        c = ⟨P', certified P' x.lay, .freshKappaL2,
          epsFor (varProxyL2 E2 S2 Vu V1 V2) (fresh.length * (2 * x.P.src.N)) κ +
            meanDrift (E2 + 1 + S2) mn md, meanDrift (E2 + 1 + S2) mn md, B, outs⟩ := by
  have hc := certify?_centred x c h
  unfold certify? at h
  rw [ite_eq_right (not_not.mpr hc)] at h
  simp only [hm, Option.bind_eq_bind, Option.pure_def] at h
  obtain ⟨hV, h⟩ := guard_bind_eq_some h
  obtain ⟨hmd, h⟩ := guard_bind_eq_some h
  obtain ⟨hf, h⟩ := guard_bind_eq_some h
  obtain ⟨⟨B, outs⟩, hch, h⟩ := Option.bind_eq_some_iff.mp h
  cases h
  exact ⟨hV, hmd, _, rfl, hf, B, outs, hch, rfl⟩

theorem certify?_checked {x : Input} {c : Certificate} (h : certify? x = some c) :
    c.budget = certified c.params x.lay ∧
      checked? c.params x.lay x.prog x.switched = some (c.bound, c.outputs) := by
  cases hm : x.mode with
  | worstCase =>
    have hc := certify?_centred x c h
    unfold certify? at h
    rw [ite_eq_right (not_not.mpr hc)] at h
    simp only [hm, Option.bind_eq_bind, Option.pure_def] at h
    obtain ⟨⟨B, outs⟩, hch, h⟩ := Option.bind_eq_some_iff.mp h
    cases h
    exact ⟨rfl, hch⟩
  | fresh fresh Bp Bk Bu B1 B2 mn md κ =>
    obtain ⟨-, -, ε, used, drift, -, -, B, outs, hch, rfl⟩ :=
      certify?_fresh_raw x c h fresh Bp Bk Bu B1 B2 mn md κ hm
    exact ⟨rfl, hch⟩
  | freshL2 fresh Bp E2 S2 Vu V1 V2 mn md κ =>
    obtain ⟨-, -, P', -, -, B, outs, hch, rfl⟩ :=
      certify?_freshL2_raw x c h fresh Bp E2 S2 Vu V1 V2 mn md κ hm
    exact ⟨rfl, hch⟩

theorem certify?_fresh (x : Input) (c : Certificate) (h : certify? x = some c)
    (fresh : List Var) (Bp Bk Bu B1 B2 mn md κ : ℕ)
    (hm : x.mode = .fresh fresh Bp Bk Bu B1 B2 mn md κ) :
    0 < varProxy x.P.src.N x.P.secretBound Bk Bu B1 B2 ∧ 0 < md ∧
    c.params = { x.P with inputNoise := freshNoise x.P.src.t Bp c.eps } ∧
    freshOK? c.params x.prog fresh = true ∧
    ((c.used = .freshKappa ∧
        c.drift = meanDrift (x.P.src.N * Bk + 1 + x.P.src.N * x.P.secretBound) mn md ∧
        c.eps = epsFor (varProxy x.P.src.N x.P.secretBound Bk Bu B1 B2)
          (fresh.length * (2 * x.P.src.N)) κ + c.drift ∧
        c.eps < worstError x.P.src.N x.P.secretBound Bk Bu B1 B2) ∨
      (c.used = .freshWorst ∧ c.drift = 0 ∧
        c.eps = worstError x.P.src.N x.P.secretBound Bk Bu B1 B2 ∧
        worstError x.P.src.N x.P.secretBound Bk Bu B1 B2 ≤
          epsFor (varProxy x.P.src.N x.P.secretBound Bk Bu B1 B2)
            (fresh.length * (2 * x.P.src.N)) κ +
          meanDrift (x.P.src.N * Bk + 1 + x.P.src.N * x.P.secretBound) mn md)) := by
  obtain ⟨hV, hmd, ε, used, drift, hfe, hf, B, outs, -, rfl⟩ :=
    certify?_fresh_raw x c h fresh Bp Bk Bu B1 B2 mn md κ hm
  refine ⟨hV, hmd, rfl, hf, ?_⟩
  unfold freshEps freshDrift at hfe
  dsimp only at hfe ⊢
  split at hfe
  · next hle =>
    cases hfe
    exact Or.inr ⟨rfl, rfl, rfl, hle⟩
  · next hle =>
    cases hfe
    exact Or.inl ⟨rfl, rfl, rfl, Nat.lt_of_not_le hle⟩

theorem certified_inputNoise (P : FullParams) (lay : KSLayout) (n : ℕ) :
    certified { P with inputNoise := n } lay = certified P lay := rfl

theorem certify?_spec (x : Input) (c : Certificate) (h : certify? x = some c) :
    c.budget = certified c.params x.lay ∧
    schemeParamsOK? c.params = true ∧ specialOK? c.params = true ∧
    layoutOK? c.params x.lay = true ∧
    refAnalyze c.params c.budget x.prog = some c.bound ∧
    x.prog.outputs ≠ [] ∧ c.outputs.map Prod.fst = x.prog.outputs ∧
    ∀ o ∈ x.prog.outputs, ∃ B, c.outputs.lookup o = some B ∧ B ≤ c.bound ∧
      refAnalyze c.params c.budget { x.prog with outputs := [o] } = some B ∧
      certOK? c.params { x.prog with outputs := [o] } B x.switched = true := by
  obtain ⟨hE, hch⟩ := certify?_checked h
  obtain ⟨h1, h2, h3, h4, hB, ho, -⟩ := checked?_some hch
  obtain ⟨hfst, hl⟩ := mapM_pair _ _ ho
  rw [hE]
  refine ⟨rfl, h1, h2, h3, hB, h4, hfst, fun o hoo => ?_⟩
  obtain ⟨b, hb, hlk⟩ := hl o hoo
  obtain ⟨hb1, hb2⟩ := outputBound?_some hb
  exact ⟨b, hlk, single_le hoo hB hb1, hb1, hb2⟩

/-! ## Non-vacuity -/

theorem certify?_paramsOK (x : Input) (c : Certificate) (h : certify? x = some c) :
    SchemeParamsOK c.params ∧ c.params.src.kind = .bgv ∧ SpecialOK c.params ∧
      ∀ ℓ, 1 ≤ ℓ → ℓ ≤ c.params.src.qs.length →
        x.lay.okAt ℓ = true ∧ restrictsTo x.lay c.params.src.qs.length ℓ = true := by
  obtain ⟨hE, h1, h2, h3, hB, -⟩ := certify?_spec x c h
  refine ⟨Validation.Params.schemeParamsOK?_sound _ h1, (refAnalyze_some hB).1,
    Validation.Budget.specialOK?_sound _ h2, fun ℓ hℓ1 hℓ => ?_⟩
  have hr := Validation.Budget.layoutOK?_restricts c.params x.lay h3 ℓ hℓ1 hℓ
  exact ⟨Validation.Budget.restrictsTo_okAt x.lay _ ℓ hℓ hr, hr⟩

theorem certify?_keys_restrict (x : Input) (c : Certificate) (h : certify? x = some c)
    (ℓ : ℕ) (h1 : 1 ≤ ℓ) (hℓ : ℓ ≤ c.params.src.qs.length) :
    2 * (c.params.keyNoise / c.params.src.t * c.params.src.t) <
        c.params.src.modulus ℓ * specialProd c.params ∧
    ∀ (tgt : KeyTarget) (s : IntPoly c.params.src.N)
      (keys : List (IntPoly c.params.src.N × IntPoly c.params.src.N)),
      GadgetKeysOK c.params x.lay c.params.src.qs.length tgt s keys →
      GadgetKeysOK c.params x.lay ℓ tgt s (keys.take (x.lay.sizes ℓ).length) := by
  obtain ⟨hP, -, -, hlay⟩ := certify?_paramsOK x c h
  obtain ⟨-, hch⟩ := certify?_checked h
  have hk := (checked?_some hch).2.2.2.2.2.2.1
  have hsz := Validation.Budget.keysRestrict?_level c.params hk hP ℓ h1 hℓ
  exact ⟨hsz, fun tgt s keys hkeys =>
    Validation.Budget.gadgetKeys_restrict c.params x.lay tgt hP ℓ hℓ (hlay ℓ h1 hℓ).2
      (fun _ => hsz) s keys hkeys⟩

theorem certified_run_exists (x : Input) (c : Certificate) (h : certify? x = some c)
    (s : IntPoly c.params.src.N) (hs : SecretOK c.params.secretBound s)
    (msgs : Var → Msg c.params.src.t c.params.src.N)
    (cts : Var → List (IntPoly c.params.src.N)) (hin : InputsOK c.params s x.prog msgs cts) :
    ∃ σ, Trace.Run c.params c.budget s x.prog.body (initEnv c.params.src x.prog msgs)
      (Trace.initCt c.params x.prog cts) σ := by
  obtain ⟨hP, hk, hS, hlay⟩ := certify?_paramsOK x c h
  obtain ⟨hE, -, -, -, hB, -⟩ := certify?_spec x c h
  rw [hE] at hB ⊢
  exact Validation.Budget.certified_run_exists c.params x.lay x.prog c.bound hP hk hS
    (fun ℓ a b => (hlay ℓ a b).1) hB s hs
    msgs cts hin

/-! ## The deterministic core -/

/-- The environment `eval` returns is the result of folding `step` over the body. -/
theorem eval_body {Pr : Params} {prog : Program} {msgs : Var → Msg Pr.t Pr.N} {ρ : Env Pr}
    (h : eval Pr prog msgs = some ρ) :
    prog.body.foldlM (step Pr) (initEnv Pr prog msgs) = some ρ := by
  simp only [eval, Option.bind_eq_bind, Option.pure_def] at h
  obtain ⟨-, h⟩ := guard_bind_eq_some h
  obtain ⟨-, h⟩ := guard_bind_eq_some h
  obtain ⟨ρf, hbody, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨-, h⟩ := guard_bind_eq_some h
  cases h
  exact hbody

/-- **Per-output analysis, joint conclusion.** If the reference analysis accepts the program,
and each output passes the one-output analysis and `certOK?` with the bound `bounds` lists for
it, then for all inputs within the input noise every output of every run decrypts and has noise
at most its own bound. -/
theorem core (P : FullParams) (E : Trace.Budget) (prog : Program) (sw : Bool)
    (bounds : List (Var × ℕ)) (hP : SchemeParamsOK P) (hk : P.src.kind = .bgv) (B : ℕ)
    (hB : refAnalyze P E prog = some B)
    (hout : ∀ o ∈ prog.outputs, ∃ b, bounds.lookup o = some b ∧
      refAnalyze P E { prog with outputs := [o] } = some b ∧
      certOK? P { prog with outputs := [o] } b sw = true)
    (s : IntPoly P.src.N) (msgs : Var → Msg P.src.t P.src.N)
    (cts : Var → List (IntPoly P.src.N)) (hin : InputsOK P s prog msgs cts)
    (hb : Trace.BoundsOK P s prog msgs cts) :
    OutputsCertified P E prog sw bounds s msgs cts := by
  obtain ⟨ρ, hev, -⟩ := refAnalyze_sound P E prog B hP hk hB s msgs cts hin hb
  refine ⟨ρ, hev, fun σ hσ o ho => ?_⟩
  obtain ⟨b, hlk, hbo, hco⟩ := hout o ho
  have hin' : InputsOK P s { prog with outputs := [o] } msgs cts := hin
  have hb' : Trace.BoundsOK P s { prog with outputs := [o] } msgs cts := hb
  have henc := refAnalyze_sound P E { prog with outputs := [o] } b hP hk hbo s msgs cts hin' hb'
  have hdec := Validation.FreshNoise.outputsDecrypt_of_encrypts P E { prog with outputs := [o] } b
    sw hP hk hco s msgs cts henc
  obtain ⟨ρ1, hev1, hrun1⟩ := henc
  obtain ⟨ρ2, hev2, hrun2⟩ := hdec
  have f0 : prog.body.foldlM (step P.src) (initEnv P.src prog msgs) = some ρ := eval_body hev
  have f1 : prog.body.foldlM (step P.src) (initEnv P.src prog msgs) = some ρ1 :=
    eval_body (prog := { prog with outputs := [o] }) hev1
  have f2 : prog.body.foldlM (step P.src) (initEnv P.src prog msgs) = some ρ2 :=
    eval_body (prog := { prog with outputs := [o] }) hev2
  have e1 : ρ1 = ρ := Option.some.inj (f1.symm.trans f0)
  have e2 : ρ2 = ρ := Option.some.inj (f2.symm.trans f0)
  subst e1; subst e2
  obtain ⟨v, ct, hv, hct, hE⟩ := hrun1 σ hσ o (List.mem_singleton.mpr rfl)
  obtain ⟨v', ct', m, hv', hct', hm, hkey, hd, hsw⟩ := hrun2 σ hσ o (List.mem_singleton.mpr rfl)
  have ev : v' = v := Option.some.inj (hv'.symm.trans hv)
  have ec : ct' = ct := Option.some.inj (hct'.symm.trans hct)
  subst ev; subst ec
  exact ⟨v', ct', m, b, hv, hct, hlk, hE, hm, hkey, hd, hsw⟩

theorem outputsCertified_decrypts (P : FullParams) (E : Trace.Budget) (prog : Program)
    (switched : Bool) (bounds : List (Var × ℕ)) (s : IntPoly P.src.N)
    (msgs : Var → Msg P.src.t P.src.N) (cts : Var → List (IntPoly P.src.N))
    (h : OutputsCertified P E prog switched bounds s msgs cts) :
    OutputsDecrypt P E prog switched s msgs cts := by
  obtain ⟨ρ, hev, hrun⟩ := h
  refine ⟨ρ, hev, fun σ hσ o ho => ?_⟩
  obtain ⟨v, ct, m, B, hv, hct, -, -, hm, hkey, hd, hsw⟩ := hrun σ hσ o ho
  exact ⟨v, ct, m, hv, hct, hm, hkey, hd, hsw⟩

theorem certified_sound (x : Input) (c : Certificate) (h : certify? x = some c)
    (s : IntPoly c.params.src.N) (msgs : Var → Msg c.params.src.t c.params.src.N)
    (cts : Var → List (IntPoly c.params.src.N)) (hin : InputsOK c.params s x.prog msgs cts)
    (hb : Trace.BoundsOK c.params s x.prog msgs cts) :
    OutputsCertified c.params c.budget x.prog x.switched c.outputs s msgs cts := by
  obtain ⟨hP, hk, -, -⟩ := certify?_paramsOK x c h
  obtain ⟨-, -, -, -, hB, -, -, hout⟩ := certify?_spec x c h
  exact core c.params c.budget x.prog x.switched c.outputs hP hk c.bound hB
    (fun o ho => by
      obtain ⟨b, h1, -, h2, h3⟩ := hout o ho
      exact ⟨b, h1, h2, h3⟩) s msgs cts hin hb

theorem certify?_sound (x : Input) (c : Certificate) (h : certify? x = some c)
    (s : IntPoly c.params.src.N) (msgs : Var → Msg c.params.src.t c.params.src.N)
    (cts : Var → List (IntPoly c.params.src.N)) (hin : InputsOK c.params s x.prog msgs cts)
    (hb : Trace.BoundsOK c.params s x.prog msgs cts) :
    OutputsCertified c.params c.budget x.prog x.switched c.outputs s msgs cts :=
  certified_sound x c h s msgs cts hin hb

theorem certify?_decrypts (x : Input) (c : Certificate) (h : certify? x = some c)
    (s : IntPoly c.params.src.N) (msgs : Var → Msg c.params.src.t c.params.src.N)
    (cts : Var → List (IntPoly c.params.src.N)) (hin : InputsOK c.params s x.prog msgs cts)
    (hb : Trace.BoundsOK c.params s x.prog msgs cts) :
    OutputsDecrypt c.params c.budget x.prog x.switched s msgs cts :=
  outputsCertified_decrypts _ _ _ _ _ _ _ _ (certified_sound x c h s msgs cts hin hb)

theorem worst_certified (x : Input) (c : Certificate) (h : certify? x = some c)
    (hm : x.mode = .worstCase)
    (s : IntPoly x.P.src.N) (msgs : Var → Msg x.P.src.t x.P.src.N)
    (cts : Var → List (IntPoly x.P.src.N)) (hin : InputsOK x.P s x.prog msgs cts)
    (hb : Trace.BoundsOK x.P s x.prog msgs cts) :
    OutputsCertified x.P (certified x.P x.lay) x.prog x.switched c.outputs s msgs cts := by
  obtain ⟨hp, -⟩ := certify?_worstCase x c h hm
  have hE := (certify?_spec x c h).1
  have key := certified_sound x c h
  rw [hE] at key
  revert key
  rw [hp]
  exact fun key => key s msgs cts hin hb

/-! ## The fresh-encryption mode -/

/-- The deterministic core of the fresh mode: if the error of every fresh encryption is at most
`c.eps`, the inputs are within the analysed input noise. -/
theorem fresh_inputs (x : Input) (c : Certificate) (h : certify? x = some c)
    (fresh : List Var) (Bp Bk Bu B1 B2 mn md κ : ℕ)
    (hm : x.mode = .fresh fresh Bp Bk Bu B1 B2 mn md κ)
    (s e b a : IntPoly c.params.src.N)
    (hpk : PublicKeyOK c.params.src.t (c.params.src.modulus c.params.src.qs.length) s e b a)
    (u e₁ e₂ : Var → IntPoly c.params.src.N)
    (hgood : ∀ y ∈ fresh, normInf (freshError s e (u y) (e₁ y) (e₂ y)) ≤ c.eps)
    (p : Var → IntPoly c.params.src.N)
    (m : Var → Poly c.params.src.t c.params.src.N) (cts : Var → List (IntPoly c.params.src.N))
    (hin : FreshInputs c.params x.prog fresh Bp s b a u e₁ e₂ p m cts) :
    InputsOK c.params s x.prog (fun y => .exact (m y)) cts ∧
      Trace.BoundsOK c.params s x.prog (fun y => .exact (m y)) cts := by
  obtain ⟨hP, hk, -, -⟩ := certify?_paramsOK x c h
  obtain ⟨-, -, hpar, hf, -⟩ := certify?_fresh x c h fresh Bp Bk Bu B1 B2 mn md κ hm
  have hnoise : freshNoise c.params.src.t Bp c.eps ≤ c.params.inputNoise := by
    rw [hpar]
  have hb := Validation.FreshNoise.fresh_boundsOK c.params x.prog fresh hf Bp s b a u e₁ e₂ p m cts hin
  exact ⟨Validation.FreshNoise.fresh_inputsOK c.params x.prog Bp c.eps hP hk hnoise fresh hf s e b a
    hpk u e₁ e₂ hgood p m cts hin.1 hb, hb⟩

theorem fresh_run_exists (x : Input) (c : Certificate) (h : certify? x = some c)
    (fresh : List Var) (Bp Bk Bu B1 B2 mn md κ : ℕ)
    (hm : x.mode = .fresh fresh Bp Bk Bu B1 B2 mn md κ)
    (s e b a : IntPoly c.params.src.N) (hs : SecretOK c.params.secretBound s)
    (hpk : PublicKeyOK c.params.src.t (c.params.src.modulus c.params.src.qs.length) s e b a)
    (u e₁ e₂ : Var → IntPoly c.params.src.N)
    (hgood : ∀ y ∈ fresh, normInf (freshError s e (u y) (e₁ y) (e₂ y)) ≤ c.eps)
    (p : Var → IntPoly c.params.src.N)
    (m : Var → Poly c.params.src.t c.params.src.N) (cts : Var → List (IntPoly c.params.src.N))
    (hin : FreshInputs c.params x.prog fresh Bp s b a u e₁ e₂ p m cts) :
    ∃ σ, Trace.Run c.params c.budget s x.prog.body
      (initEnv c.params.src x.prog fun y => .exact (m y)) (Trace.initCt c.params x.prog cts) σ :=
  certified_run_exists x c h s hs _ cts
    (fresh_inputs x c h fresh Bp Bk Bu B1 B2 mn md κ hm s e b a hpk u e₁ e₂ hgood p m cts hin).1

/-- The fresh mode, deterministically: errors at most `c.eps` give the conclusion. -/
theorem fresh_core (x : Input) (c : Certificate) (h : certify? x = some c)
    (fresh : List Var) (Bp Bk Bu B1 B2 mn md κ : ℕ)
    (hm : x.mode = .fresh fresh Bp Bk Bu B1 B2 mn md κ)
    (s e b a : IntPoly c.params.src.N)
    (hpk : PublicKeyOK c.params.src.t (c.params.src.modulus c.params.src.qs.length) s e b a)
    (u e₁ e₂ : Var → IntPoly c.params.src.N)
    (hgood : ∀ y ∈ fresh, normInf (freshError s e (u y) (e₁ y) (e₂ y)) ≤ c.eps)
    (p : Var → IntPoly c.params.src.N)
    (m : Var → Poly c.params.src.t c.params.src.N) (cts : Var → List (IntPoly c.params.src.N))
    (hin : FreshInputs c.params x.prog fresh Bp s b a u e₁ e₂ p m cts) :
    OutputsCertified c.params c.budget x.prog x.switched c.outputs s (fun y => .exact (m y))
      cts := by
  obtain ⟨h1, h2⟩ := fresh_inputs x c h fresh Bp Bk Bu B1 B2 mn md κ hm s e b a hpk u e₁ e₂ hgood p m cts hin
  exact certified_sound x c h s _ cts h1 h2

/-- The sizes in the analysed parameters are the declared ones. -/
theorem fresh_params_eq (x : Input) (c : Certificate) (h : certify? x = some c)
    (fresh : List Var) (Bp Bk Bu B1 B2 mn md κ : ℕ)
    (hm : x.mode = .fresh fresh Bp Bk Bu B1 B2 mn md κ) :
    x.P.src.N = c.params.src.N ∧ x.P.secretBound = c.params.secretBound := by
  obtain ⟨-, -, hpar, -, -⟩ := certify?_fresh x c h fresh Bp Bk Bu B1 B2 mn md κ hm
  rw [hpar]
  exact ⟨rfl, rfl⟩

theorem fresh_worst_certified (x : Input) (c : Certificate) (h : certify? x = some c)
    (fresh : List Var) (Bp Bk Bu B1 B2 mn md κ : ℕ)
    (hm : x.mode = .fresh fresh Bp Bk Bu B1 B2 mn md κ)
    (hu : c.used = .freshWorst)
    (s e b a : IntPoly c.params.src.N) (hs : SecretOK c.params.secretBound s)
    (he : normInf e ≤ Bk)
    (hpk : PublicKeyOK c.params.src.t (c.params.src.modulus c.params.src.qs.length) s e b a)
    (u e₁ e₂ : Var → IntPoly c.params.src.N)
    (hrand : ∀ y ∈ fresh, normInf (u y) ≤ Bu ∧ normInf (e₁ y) ≤ B1 ∧ normInf (e₂ y) ≤ B2)
    (p : Var → IntPoly c.params.src.N)
    (m : Var → Poly c.params.src.t c.params.src.N) (cts : Var → List (IntPoly c.params.src.N))
    (hin : FreshInputs c.params x.prog fresh Bp s b a u e₁ e₂ p m cts) :
    OutputsCertified c.params c.budget x.prog x.switched c.outputs s (fun y => .exact (m y))
      cts := by
  obtain ⟨hN, hsB⟩ := fresh_params_eq x c h fresh Bp Bk Bu B1 B2 mn md κ hm
  obtain ⟨-, -, -, -, hcase⟩ := certify?_fresh x c h fresh Bp Bk Bu B1 B2 mn md κ hm
  have heps : c.eps = worstError c.params.src.N c.params.secretBound Bk Bu B1 B2 := by
    rcases hcase with ⟨hk', -, -, -⟩ | ⟨-, -, he', -⟩
    · rw [hu] at hk'; exact absurd hk' (by decide)
    · rw [he', hN, hsB]
  refine fresh_core x c h fresh Bp Bk Bu B1 B2 mn md κ hm s e b a hpk u e₁ e₂ (fun y hy => ?_) p m cts hin
  rw [heps]
  exact Validation.FreshNoise.freshError_worst s e (u y) (e₁ y) (e₂ y) c.params.secretBound
    Bk Bu B1 B2 hs he (hrand y hy).1 (hrand y hy).2.1 (hrand y hy).2.2

/-- A property that holds almost surely for each element of a list holds almost surely for all. -/
theorem ae_list {Ω ι : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (p : ι → Ω → Prop) :
    ∀ l : List ι, (∀ y ∈ l, ∀ᵐ ω ∂μ, p y ω) → ∀ᵐ ω ∂μ, ∀ y ∈ l, p y ω
  | [], _ => Filter.Eventually.of_forall (by simp)
  | y :: l, h => by
    have h1 := h y List.mem_cons_self
    have h2 := ae_list μ p l fun z hz => h z (List.mem_cons_of_mem _ hz)
    filter_upwards [h1, h2] with ω a1 a2 z hz
    rcases List.mem_cons.mp hz with rfl | hz
    · exact a1
    · exact a2 z hz

/-- Under `SamplerOK` the randomness is almost surely within its bounds. -/
theorem sampler_bounds {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (Bu B1 B2 : ℕ)
    (mn md : ℕ)
    (u e₁ e₂ : Ω → IntPoly N) (h : SamplerOK μ Bu B1 B2 mn md u e₁ e₂) :
    ∀ᵐ ω ∂μ, normInf (u ω) ≤ Bu ∧ normInf (e₁ ω) ≤ B1 ∧ normInf (e₂ ω) ≤ B2 := by
  have hall : ∀ᵐ ω ∂μ, ∀ j, |coords u e₁ e₂ j ω| ≤ (coordBound N Bu B1 B2 j : ℤ) :=
    ae_all_iff.mpr h.bound
  filter_upwards [hall] with ω hω
  refine ⟨?_, ?_, ?_⟩
  · exact (Validation.Scheme.normInf_le_iff _ _).mpr fun i => hω (.inl i)
  · exact (Validation.Scheme.normInf_le_iff _ _).mpr fun i => hω (.inr (.inl i))
  · exact (Validation.Scheme.normInf_le_iff _ _).mpr fun i => hω (.inr (.inr i))

theorem fresh_kappa_certified (x : Input) (c : Certificate) (h : certify? x = some c)
    (fresh : List Var) (Bp Bk Bu B1 B2 mn md κ : ℕ)
    (hm : x.mode = .fresh fresh Bp Bk Bu B1 B2 mn md κ)
    (s e b a : IntPoly c.params.src.N) (hs : SecretOK c.params.secretBound s)
    (he : normInf e ≤ Bk)
    (hpk : PublicKeyOK c.params.src.t (c.params.src.modulus c.params.src.qs.length) s e b a)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (u e₁ e₂ : Var → Ω → IntPoly c.params.src.N)
    (hsamp : ∀ y ∈ fresh, SamplerOK μ Bu B1 B2 mn md (u y) (e₁ y) (e₂ y)) :
    μ.real {ω | CertifiedFails c.params c.budget x.prog x.switched c.outputs fresh Bp s b a
      u e₁ e₂ ω} ≤ (2 : ℝ)⁻¹ ^ κ := by
  obtain ⟨hN, hsB⟩ := fresh_params_eq x c h fresh Bp Bk Bu B1 B2 mn md κ hm
  obtain ⟨hV, hmd, -, -, hcase⟩ := certify?_fresh x c h fresh Bp Bk Bu B1 B2 mn md κ hm
  obtain ⟨hP, -, -, -⟩ := certify?_paramsOK x c h
  rw [hN, hsB] at hV hcase
  -- the one bad event: the error of some fresh encryption exceeds `c.eps`
  have hsub : {ω | CertifiedFails c.params c.budget x.prog x.switched c.outputs fresh Bp s b a
      u e₁ e₂ ω} ⊆
      ⋃ y ∈ fresh, {ω | ¬ normInf (freshError s e (u y ω) (e₁ y ω) (e₂ y ω)) ≤ c.eps} := by
    intro ω hω
    by_contra hne
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq, not_exists, not_not] at hne
    obtain ⟨p, m, cts, hin, hno⟩ := hω
    exact hno (fresh_core x c h fresh Bp Bk Bu B1 B2 mn md κ hm s e b a hpk (fun y => u y ω)
      (fun y => e₁ y ω) (fun y => e₂ y ω) hne p m cts hin)
  rcases hcase with ⟨-, hdr, heps, -⟩ | ⟨-, -, heps, -⟩
  · -- high-probability bound: the tail bound for each fresh input, and a union bound
    have hN0 : 0 < c.params.src.N := by
      obtain ⟨k, hk'⟩ := hP.N_pow2
      rw [hk']; exact Nat.pos_of_ne_zero (by positivity)
    have hD := Validation.FreshNoise.meanDrift_spec
      (c.params.src.N * Bk + 1 + c.params.src.N * c.params.secretBound) mn md hmd
    rw [← hdr] at hD
    have hsub2 : (⋃ y ∈ fresh,
        {ω | ¬ normInf (freshError s e (u y ω) (e₁ y ω) (e₂ y ω)) ≤ c.eps}) ⊆
        ⋃ y ∈ fresh,
          {ω | ((epsFor (varProxy c.params.src.N c.params.secretBound Bk Bu B1 B2)
              (fresh.length * (2 * c.params.src.N)) κ : ℕ) : ℝ) + (mn : ℝ) / md *
              ((c.params.src.N * Bk + 1 + c.params.src.N * c.params.secretBound : ℕ) : ℝ) ≤
            (normInf (freshError s e (u y ω) (e₁ y ω) (e₂ y ω)) : ℝ)} := by
      refine Set.iUnion₂_mono fun y _ ω hω => ?_
      have h1 : c.eps ≤ normInf (freshError s e (u y ω) (e₁ y ω) (e₂ y ω)) :=
        (Nat.lt_of_not_le hω).le
      rw [heps] at h1
      have h2 : ((epsFor (varProxy c.params.src.N c.params.secretBound Bk Bu B1 B2)
          (fresh.length * (2 * c.params.src.N)) κ : ℕ) : ℝ) + (c.drift : ℝ) ≤
          (normInf (freshError s e (u y ω) (e₁ y ω) (e₂ y ω)) : ℝ) := by exact_mod_cast h1
      show (_ : ℝ) ≤ _
      linarith
    have h1 := Validation.FreshNoise.measureReal_biUnion_list_le μ _ _ fresh fun y hy =>
        Validation.FreshNoise.freshError_tail μ hN0 s e c.params.secretBound Bk Bu B1 B2 mn md
          hs he (u y) (e₁ y) (e₂ y) (hsamp y hy)
          ((epsFor (varProxy c.params.src.N c.params.secretBound Bk Bu B1 B2)
              (fresh.length * (2 * c.params.src.N)) κ : ℕ) : ℝ) (Nat.cast_nonneg _)
    have h2 := Validation.FreshNoise.epsFor_spec
      (varProxy c.params.src.N c.params.secretBound Bk Bu B1 B2)
      (fresh.length * (2 * c.params.src.N)) κ hV
    push_cast at h2
    refine (measureReal_mono (hsub.trans hsub2) (measure_ne_top μ _)).trans (h1.trans ?_)
    refine le_trans (le_of_eq ?_) h2
    ring
  · -- worst case: the bad event is a null set
    have hae : ∀ᵐ ω ∂μ, ∀ y ∈ fresh,
        normInf (u y ω) ≤ Bu ∧ normInf (e₁ y ω) ≤ B1 ∧ normInf (e₂ y ω) ≤ B2 :=
      ae_list μ _ fresh fun y hy => sampler_bounds μ Bu B1 B2 mn md (u y) (e₁ y) (e₂ y) (hsamp y hy)
    have hnull : μ {ω | CertifiedFails c.params c.budget x.prog x.switched c.outputs fresh Bp s b a
        u e₁ e₂ ω} = 0 := by
      refine measure_mono_null hsub ?_
      rw [measure_eq_zero_iff_ae_notMem]
      filter_upwards [hae] with ω hω hmem
      simp only [Set.mem_iUnion, Set.mem_ofPred_eq] at hmem
      obtain ⟨y, hy, hbad⟩ := hmem
      refine hbad ?_
      rw [heps]
      exact Validation.FreshNoise.freshError_worst s e (u y ω) (e₁ y ω) (e₂ y ω)
        c.params.secretBound Bk Bu B1 B2 hs he (hω y hy).1 (hω y hy).2.1 (hω y hy).2.2
    rw [Measure.real, hnull]
    simp only [ENNReal.toReal_zero]
    positivity

theorem fresh_kappa_decrypts (x : Input) (c : Certificate) (h : certify? x = some c)
    (fresh : List Var) (Bp Bk Bu B1 B2 mn md κ : ℕ)
    (hm : x.mode = .fresh fresh Bp Bk Bu B1 B2 mn md κ)
    (s e b a : IntPoly c.params.src.N) (hs : SecretOK c.params.secretBound s)
    (he : normInf e ≤ Bk)
    (hpk : PublicKeyOK c.params.src.t (c.params.src.modulus c.params.src.qs.length) s e b a)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (u e₁ e₂ : Var → Ω → IntPoly c.params.src.N)
    (hsamp : ∀ y ∈ fresh, SamplerOK μ Bu B1 B2 mn md (u y) (e₁ y) (e₂ y)) :
    μ.real {ω | DecryptFails c.params c.budget x.prog x.switched fresh Bp s b a u e₁ e₂ ω} ≤
      (2 : ℝ)⁻¹ ^ κ := by
  have hsub : {ω | DecryptFails c.params c.budget x.prog x.switched fresh Bp s b a u e₁ e₂ ω} ⊆
      {ω | CertifiedFails c.params c.budget x.prog x.switched c.outputs fresh Bp s b a
        u e₁ e₂ ω} := by
    rintro ω ⟨p, m, cts, hin, hno⟩
    exact ⟨p, m, cts, hin, fun hc =>
      hno (outputsCertified_decrypts c.params c.budget x.prog x.switched c.outputs s _ cts hc)⟩
  exact (measureReal_mono hsub (measure_ne_top μ _)).trans
    (fresh_kappa_certified x c h fresh Bp Bk Bu B1 B2 mn md κ hm s e b a hs he hpk μ u e₁ e₂ hsamp)

/-! ## The fresh-encryption mode described in `ℓ₂` -/

theorem certify?_freshL2 (x : Input) (c : Certificate) (h : certify? x = some c)
    (fresh : List Var) (Bp E2 S2 Vu V1 V2 mn md κ : ℕ)
    (hm : x.mode = .freshL2 fresh Bp E2 S2 Vu V1 V2 mn md κ) :
    0 < varProxyL2 E2 S2 Vu V1 V2 ∧ 0 < md ∧
    c.params = { x.P with inputNoise := freshNoise x.P.src.t Bp c.eps } ∧
    freshOK? c.params x.prog fresh = true ∧ c.used = .freshKappaL2 ∧
    c.drift = meanDrift (E2 + 1 + S2) mn md ∧
    c.eps = epsFor (varProxyL2 E2 S2 Vu V1 V2) (fresh.length * (2 * x.P.src.N)) κ + c.drift := by
  obtain ⟨hV, hmd, P', rfl, hf, B, outs, -, rfl⟩ :=
    certify?_freshL2_raw x c h fresh Bp E2 S2 Vu V1 V2 mn md κ hm
  exact ⟨hV, hmd, rfl, hf, rfl, rfl, rfl⟩

/-- The deterministic core in the `ℓ₂` mode. -/
theorem fresh_l2_inputs (x : Input) (c : Certificate) (h : certify? x = some c)
    (fresh : List Var) (Bp E2 S2 Vu V1 V2 mn md κ : ℕ)
    (hm : x.mode = .freshL2 fresh Bp E2 S2 Vu V1 V2 mn md κ)
    (s e b a : IntPoly c.params.src.N)
    (hpk : PublicKeyOK c.params.src.t (c.params.src.modulus c.params.src.qs.length) s e b a)
    (u e₁ e₂ : Var → IntPoly c.params.src.N)
    (hgood : ∀ y ∈ fresh, normInf (freshError s e (u y) (e₁ y) (e₂ y)) ≤ c.eps)
    (p : Var → IntPoly c.params.src.N)
    (m : Var → Poly c.params.src.t c.params.src.N) (cts : Var → List (IntPoly c.params.src.N))
    (hin : FreshInputs c.params x.prog fresh Bp s b a u e₁ e₂ p m cts) :
    InputsOK c.params s x.prog (fun y => .exact (m y)) cts ∧
      Trace.BoundsOK c.params s x.prog (fun y => .exact (m y)) cts := by
  obtain ⟨hP, hk, -, -⟩ := certify?_paramsOK x c h
  obtain ⟨-, -, hpar, hf, -, -, -⟩ := certify?_freshL2 x c h fresh Bp E2 S2 Vu V1 V2 mn md κ hm
  have hnoise : freshNoise c.params.src.t Bp c.eps ≤ c.params.inputNoise := by
    rw [hpar]
  have hb := Validation.FreshNoise.fresh_boundsOK c.params x.prog fresh hf Bp s b a u e₁ e₂ p m cts hin
  exact ⟨Validation.FreshNoise.fresh_inputsOK c.params x.prog Bp c.eps hP hk hnoise fresh hf s e b a
    hpk u e₁ e₂ hgood p m cts hin.1 hb, hb⟩

theorem fresh_l2_run_exists (x : Input) (c : Certificate) (h : certify? x = some c)
    (fresh : List Var) (Bp E2 S2 Vu V1 V2 mn md κ : ℕ)
    (hm : x.mode = .freshL2 fresh Bp E2 S2 Vu V1 V2 mn md κ)
    (s e b a : IntPoly c.params.src.N) (hs : SecretOK c.params.secretBound s)
    (hpk : PublicKeyOK c.params.src.t (c.params.src.modulus c.params.src.qs.length) s e b a)
    (u e₁ e₂ : Var → IntPoly c.params.src.N)
    (hgood : ∀ y ∈ fresh, normInf (freshError s e (u y) (e₁ y) (e₂ y)) ≤ c.eps)
    (p : Var → IntPoly c.params.src.N)
    (m : Var → Poly c.params.src.t c.params.src.N) (cts : Var → List (IntPoly c.params.src.N))
    (hin : FreshInputs c.params x.prog fresh Bp s b a u e₁ e₂ p m cts) :
    ∃ σ, Trace.Run c.params c.budget s x.prog.body
      (initEnv c.params.src x.prog fun y => .exact (m y)) (Trace.initCt c.params x.prog cts) σ :=
  certified_run_exists x c h s hs _ cts
    (fresh_l2_inputs x c h fresh Bp E2 S2 Vu V1 V2 mn md κ hm s e b a hpk u e₁ e₂ hgood p m cts hin).1

theorem fresh_l2_certified (x : Input) (c : Certificate) (h : certify? x = some c)
    (fresh : List Var) (Bp E2 S2 Vu V1 V2 mn md κ : ℕ)
    (hm : x.mode = .freshL2 fresh Bp E2 S2 Vu V1 V2 mn md κ)
    (s e b a : IntPoly c.params.src.N) (hs : normSq s ≤ S2) (he : normSq e ≤ E2)
    (hpk : PublicKeyOK c.params.src.t (c.params.src.modulus c.params.src.qs.length) s e b a)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (u e₁ e₂ : Var → Ω → IntPoly c.params.src.N)
    (hsamp : ∀ y ∈ fresh, SubGaussSamplerOK μ Vu V1 V2 mn md (u y) (e₁ y) (e₂ y)) :
    μ.real {ω | CertifiedFails c.params c.budget x.prog x.switched c.outputs fresh Bp s b a
      u e₁ e₂ ω} ≤ (2 : ℝ)⁻¹ ^ κ := by
  obtain ⟨hV, hmd, hpar, -, -, hdr, heps⟩ :=
    certify?_freshL2 x c h fresh Bp E2 S2 Vu V1 V2 mn md κ hm
  obtain ⟨hP, -, -, -⟩ := certify?_paramsOK x c h
  have hN : x.P.src.N = c.params.src.N := by rw [hpar]
  rw [hN] at heps
  have hN0 : 0 < c.params.src.N := by
    obtain ⟨k, hk'⟩ := hP.N_pow2
    rw [hk']; exact Nat.pos_of_ne_zero (by positivity)
  have hD := Validation.FreshNoise.meanDrift_spec (E2 + 1 + S2) mn md hmd
  rw [← hdr] at hD
  have hsub : {ω | CertifiedFails c.params c.budget x.prog x.switched c.outputs fresh Bp s b a
      u e₁ e₂ ω} ⊆
      ⋃ y ∈ fresh,
        {ω | ((epsFor (varProxyL2 E2 S2 Vu V1 V2)
              (fresh.length * (2 * c.params.src.N)) κ : ℕ) : ℝ) + (mn : ℝ) / md *
              ((E2 + 1 + S2 : ℕ) : ℝ) ≤
          (normInf (freshError s e (u y ω) (e₁ y ω) (e₂ y ω)) : ℝ)} := by
    intro ω hω
    by_contra hne
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq, not_exists, not_le] at hne
    obtain ⟨p, m, cts, hin, hno⟩ := hω
    have hgood : ∀ y ∈ fresh,
        normInf (freshError s e (u y ω) (e₁ y ω) (e₂ y ω)) ≤ c.eps := by
      intro y hy
      have h3 := hne y hy
      by_contra hgt
      have h1 : c.eps ≤ normInf (freshError s e (u y ω) (e₁ y ω) (e₂ y ω)) :=
        (Nat.lt_of_not_le hgt).le
      rw [heps] at h1
      have h2 : ((epsFor (varProxyL2 E2 S2 Vu V1 V2)
          (fresh.length * (2 * c.params.src.N)) κ : ℕ) : ℝ) + (c.drift : ℝ) ≤
          (normInf (freshError s e (u y ω) (e₁ y ω) (e₂ y ω)) : ℝ) := by exact_mod_cast h1
      linarith
    obtain ⟨h1, h2⟩ := fresh_l2_inputs x c h fresh Bp E2 S2 Vu V1 V2 mn md κ hm s e b a hpk
      (fun y => u y ω) (fun y => e₁ y ω) (fun y => e₂ y ω) hgood p m cts hin
    exact hno (certified_sound x c h s _ cts h1 h2)
  have h1 := Validation.FreshNoise.measureReal_biUnion_list_le μ _ _ fresh fun y hy =>
      Validation.FreshNoiseL2.freshError_tail_l2 μ hN0 s e E2 S2 Vu V1 V2 mn md hs he
        (u y) (e₁ y) (e₂ y) (hsamp y hy)
        ((epsFor (varProxyL2 E2 S2 Vu V1 V2)
            (fresh.length * (2 * c.params.src.N)) κ : ℕ) : ℝ) (Nat.cast_nonneg _)
  have h2 := Validation.FreshNoise.epsFor_spec (varProxyL2 E2 S2 Vu V1 V2)
    (fresh.length * (2 * c.params.src.N)) κ hV
  push_cast at h2
  refine (measureReal_mono hsub (measure_ne_top μ _)).trans (h1.trans ?_)
  refine le_trans (le_of_eq ?_) h2
  ring

theorem fresh_l2_decrypts (x : Input) (c : Certificate) (h : certify? x = some c)
    (fresh : List Var) (Bp E2 S2 Vu V1 V2 mn md κ : ℕ)
    (hm : x.mode = .freshL2 fresh Bp E2 S2 Vu V1 V2 mn md κ)
    (s e b a : IntPoly c.params.src.N) (hs : normSq s ≤ S2) (he : normSq e ≤ E2)
    (hpk : PublicKeyOK c.params.src.t (c.params.src.modulus c.params.src.qs.length) s e b a)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (u e₁ e₂ : Var → Ω → IntPoly c.params.src.N)
    (hsamp : ∀ y ∈ fresh, SubGaussSamplerOK μ Vu V1 V2 mn md (u y) (e₁ y) (e₂ y)) :
    μ.real {ω | DecryptFails c.params c.budget x.prog x.switched fresh Bp s b a u e₁ e₂ ω} ≤
      (2 : ℝ)⁻¹ ^ κ := by
  have hsub : {ω | DecryptFails c.params c.budget x.prog x.switched fresh Bp s b a u e₁ e₂ ω} ⊆
      {ω | CertifiedFails c.params c.budget x.prog x.switched c.outputs fresh Bp s b a
        u e₁ e₂ ω} := by
    rintro ω ⟨p, m, cts, hin, hno⟩
    exact ⟨p, m, cts, hin, fun hc =>
      hno (outputsCertified_decrypts c.params c.budget x.prog x.switched c.outputs s _ cts hc)⟩
  exact (measureReal_mono hsub (measure_ne_top μ _)).trans
    (fresh_l2_certified x c h fresh Bp E2 S2 Vu V1 V2 mn md κ hm s e b a hs he hpk μ u e₁ e₂ hsamp)

theorem certify?_accepts_threeOut_l2 :
    (certify? (tinyInput threeOutProg true (.freshL2 ["a", "b"] 16 4 4 1 1 1 0 1 1))).map
        (fun c => (c.used, c.outputs)) =
      some (.freshKappaL2, [("c", 304), ("d", 109144576), ("e", 181)]) := by
  decide +kernel

/-! ## Closed pins (kernel evaluation) -/

theorem certify?_accepts_runDemo :
    (certify? (tinyInput Challenge.Budget.runDemoProg true .worstCase)).isSome = true := by
  decide +kernel

theorem certify?_accepts_threeOut :
    (certify? (tinyInput threeOutProg true (.fresh ["a", "b"] 16 1 1 1 1 0 1 1))).map
        (fun c => (c.used, c.outputs)) =
      some (.freshKappa, [("c", 304), ("d", 109144576), ("e", 181)]) := by
  decide +kernel

theorem certify?_rejects_badSpecial :
    (certify? ⟨badSpecialParams, uniformLayout 1, Challenge.Budget.runDemoProg, false,
      .worstCase, .centred⟩).isSome = false := by
  decide +kernel

theorem certify?_rejects_badLayout :
    (certify? ⟨Spec.FullParams.tinyBGV, badLayout, Challenge.Budget.runDemoProg, false,
      .worstCase, .centred⟩).isSome = false := by
  decide +kernel

theorem certify?_rejects_varProxy_zero :
    (certify? (tinyInput Challenge.Budget.runDemoProg false
      (.fresh ["a", "b"] 16 0 0 0 0 0 1 128))).isSome = false := by
  decide +kernel

theorem certify?_rejects_rotatedKey :
    (certify? (tinyInput
      { inputs := [⟨"a", 2, 2, 1, 1⟩], body := [.automorph "o" "a" 5], outputs := ["o"] }
      false .worstCase)).isSome = false := by
  decide +kernel

theorem certify?_rejects_switched :
    (certify? ⟨{ Spec.FullParams.tinyBGV with inputNoise := 25765000000 }, uniformLayout 1,
      { inputs := [⟨"a", 2, 2, 1, 1⟩], body := [.copy "o" "a"], outputs := ["o"] }, true,
      .worstCase, .centred⟩).isSome = false := by
  decide +kernel

theorem certify?_rejects_nonCentred :
    (certify? ⟨Spec.FullParams.tinyBGV, uniformLayout 1, Challenge.Budget.runDemoProg, true,
      .worstCase, .canonical⟩).isSome = false ∧
    (certify? ⟨Spec.FullParams.tinyBGV, uniformLayout 1, Challenge.Budget.runDemoProg, true,
      .worstCase, .other⟩).isSome = false := ⟨rfl, rfl⟩

theorem certify?_rejects_evenSpecial :
    (certify? ⟨evenSpecialParams, uniformLayout 1, Challenge.Budget.runDemoProg, false,
      .worstCase, .centred⟩).isSome = false := by
  decide +kernel

theorem certify?_rejects_nonRestricting :
    (certify? ⟨Challenge.Budget.restrictBadParams, Challenge.Budget.restrictBadLayout,
      restrictProg, false, .worstCase, .centred⟩).isSome = false ∧
    (∀ ℓ, 1 ≤ ℓ → ℓ ≤ 3 → Challenge.Budget.restrictBadLayout.okAt ℓ = true) ∧
    (certify? ⟨Challenge.Budget.restrictBadParams, uniformLayout 1, restrictProg, false,
      .worstCase, .centred⟩).isSome = true := by
  refine ⟨by decide +kernel, fun ℓ h1 h3 => ?_, by decide +kernel⟩
  interval_cases ℓ <;> decide +kernel

theorem certify?_rejects_keySize :
    (certify? ⟨Challenge.Budget.restrictSizeParams, uniformLayout 1, restrictSizeProg, false,
      .worstCase, .centred⟩).isSome = false := by
  decide +kernel

theorem layoutOK?_uniform (P : FullParams) (α : ℕ) (c : Bool) :
    layoutOK? P (uniformLayout α c) = true :=
  Validation.Budget.layoutOK?_uniform P α c

theorem certify?_accepts_drift :
    (certify? (tinyInput threeOutProg true (.freshL2 ["a", "b"] 16 4 4 1 1 1 1 100 128))).map
        (fun c => (c.used, c.eps, c.drift)) =
      some (.freshKappaL2, epsFor 9 16 128 + 1, 1) := by
  decide +kernel

theorem certify?_rejects_overflow :
    (certify? (tinyInput
      { inputs := [⟨"a", 2, 2, 1, 1⟩],
        body := [.square "c" "a", .square "c" "c", .square "c" "c", .square "c" "c"],
        outputs := ["c"] } false .worstCase)).isSome = false := by
  decide +kernel

end Validation.Certify
