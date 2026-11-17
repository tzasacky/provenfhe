import Challenge.IndCpaD.ProfileBGV
import Validation.IndCpaD.Profile

/-!
# Validation.IndCpaD.ProfileBGV — proofs of the pins of `Challenge.IndCpaD.ProfileBGV`

As `Validation.IndCpaD.Profile`, with the BGV profile certificate
(`Validation.Profile.certifyProfile?_sound`), the BGV input hypotheses (`Spec.Correct.InputsOK`:
every input, the stored plaintext operands included, within the input noise; `Trace.BoundsOK`:
within its declared bound), and the levels of `Source.eval` shown message independent for BGV
too (a modulus switch multiplies the zero message by `q⁻¹`, which keeps it zero).
-/

namespace Validation.IndCpaDProfile
open Spec NPoly Scheme Source Spec.Encrypt Spec.IndCpaDProfile Challenge.IndCpaDProfile
open Challenge.Profile (certifyProfile?)

variable {D : AbsScheme}

/-! ## The levels do not depend on the messages (BGV) -/

section Zero
open Validation.BFV.SoundAux Validation.Ring Validation.Scheme Validation.Source
variable {Pr : Params}

theorem step_zenv_bgv (hk : Pr.kind = .bgv) {ρ : Env Pr} (hρ : AllExact ρ) (i : Instr) :
    step Pr (zenv ρ) i = (step Pr ρ i).map zenv ∧ ∀ ρ', step Pr ρ i = some ρ' → AllExact ρ' := by
  cases i with
  | add d a b | sub d a b | mul d a b | addPlain d a b | subPlain d a b | mulPlain d a b =>
    rcases h1 : ρ a with _ | x
    · simp [step, zenv, h1]
    rcases h2 : ρ b with _ | y
    · simp [step, zenv, h1, h2]
    obtain ⟨m, hm⟩ := hρ a x h1
    obtain ⟨m', hm'⟩ := hρ b y h2
    simp only [step, zenv, h1, h2, zv, hm, hm', Msg.lift₂, hk, Option.map_some, Option.bind_eq_bind,
      Option.bind_some, Option.pure_def, guard]
    refine ⟨?_, ?_⟩
    · split_ifs <;> simp [zenv_set, zv, npoly_zero_add, npoly_zero_sub, npoly_zero_mul]
    · intro ρ' h; split_ifs at h <;> simp at h
      all_goals (subst h; exact allExact_set hρ _ _ _ rfl)
  | square d a | mulConst d a _ | copy d a | toEval d a | toCoeff d a | relin d a | keySwitch d a
  | automorph d a _ | modSwitch d a | dropLimbs d a _ =>
    rcases h1 : ρ a with _ | x
    · simp [step, zenv, h1]
    obtain ⟨m, hm⟩ := hρ a x h1
    rcases hq : Pr.qs[x.level - 1]? with _ | q
    all_goals simp only [step, zenv, h1, zv, hm, hq, Msg.lift₂, Msg.lift₁, hk, Option.map_some,
      Option.bind_eq_bind, Option.bind_some, Option.bind_none, Option.pure_def, guard]
    all_goals refine ⟨?_, ?_⟩
    all_goals first
    | (try split_ifs
       all_goals simp [zenv_set, zv, npoly_zero_mul, npoly_smul_zero, automorph_zero]
       done)
    | (intro ρ' h
       try split_ifs at h
       all_goals simp at h
       all_goals (subst h; first | exact allExact_set hρ _ _ _ rfl | exact allExact_set hρ _ _ _ hm))

theorem foldlM_zenv_bgv (hk : Pr.kind = .bgv) :
    ∀ (body : List Instr) (ρ : Env Pr),
      body.foldlM (step Pr) (zenv ρ) = (body.foldlM (step Pr) ρ).map zenv := by
  intro body
  induction body with
  | nil => intro ρ; rfl
  | cons i is ih =>
    intro ρ
    obtain ⟨hz, -⟩ := step_zenv_bgv hk (Validation.IndCpaD.allExact_all ρ) i
    simp only [List.foldlM_cons, Option.bind_eq_bind]
    rw [hz]
    rcases step Pr ρ i with _ | ρ'
    · rfl
    · simp only [Option.map_some, Option.bind_some]; exact ih ρ'

end Zero

theorem level_eq_bgv {Pr : Params} (hk : Pr.kind = .bgv) (prog : Program)
    (msgs : Var → Msg Pr.t Pr.N) (ρ : Env Pr) (h : Source.eval Pr prog msgs = some ρ)
    (o : Var) (v : Val Pr) (hv : ρ o = some v) :
    ((Source.eval Pr prog (fun _ => .exact 0) >>= fun ρ => ρ o).map (·.level)).getD 0 =
      v.level := by
  open Validation.BFV.SoundAux in
  have hz0 : zenv (initEnv Pr prog msgs) = initEnv Pr prog fun _ => .exact 0 := by
    funext x; simp only [zenv, initEnv, Option.map_map]; rfl
  have hf := foldlM_zenv_bgv hk prog.body (initEnv Pr prog msgs)
  rw [hz0] at hf
  have hfits : ∀ (msgs : Var → Msg Pr.t Pr.N),
      (prog.inputs.all fun dcl => (msgs dcl.name).fits Pr.kind) = true := by
    intro msgs; rw [List.all_eq_true]; intro dcl _
    cases msgs dcl.name; rw [hk]; rfl
  have hf1 := hfits msgs
  have hf0 := hfits (fun _ => .exact 0)
  by_cases hdecl : (prog.inputs.all fun dcl => dcl.ok Pr) = true
  swap
  · simp [Source.eval, guard, hdecl] at h
  rcases hρ : prog.body.foldlM (step Pr) (initEnv Pr prog msgs) with _ | ρf
  · simp [Source.eval, guard, hdecl, hf1, hρ] at h
  rw [hρ] at hf
  by_cases hout : ∀ x ∈ prog.outputs, (ρf x).isSome = true
  swap
  · simp [Source.eval, guard, hdecl, hf1, hρ, hout] at h
  simp [Source.eval, guard, hdecl, hf1, hρ] at h
  rw [ite_eq_left_of_eq_true _ _ (eq_true hout)] at h
  simp only [Option.bind_some, Option.some.injEq] at h
  subst h
  simp [Source.eval, guard, hdecl, hf0, hf, Validation.BFV.SoundAux.zenv]
  rw [ite_eq_left_of_eq_true _ _ (eq_true hout)]
  simp [Validation.BFV.SoundAux.zenv, hv, Validation.BFV.SoundAux.zv]

/-! ## The inputs -/

/-- A BGV encryption under `σ_k(s)` is `Encrypts` of the value. -/
theorem encrypts_of_bgv (P : FullParams) (hk : P.src.kind = .bgv) (s : IntPoly P.src.N) (B : ℕ)
    (m : Poly P.src.t P.src.N) (p l k : ℕ) (sc : ℚ) (ct : List (IntPoly P.src.N))
    (hl : ct.length = p)
    (h : BGVEncrypts P.src.t B (automorph k s) (ct.map (ofInt (P.src.modulus l))) m) :
    Correct.Encrypts P s B ⟨.exact m, p, l, k, sc⟩ ct := by
  unfold Correct.Encrypts
  refine ⟨hl, ?_⟩
  simp only [hk]
  exact h

/-- `admBGV`, read (by `change`). -/
theorem admBGV_some {prof : D.Circ → Trace.Budget} {C : D.Circ}
    (h : admBGV D prof C = true) :
    ∃ B outs, certifyProfile? D.Pe (prof C) (D.prog C) false = some (B, outs) ∧
      D.inputsFit C = true ∧
      ∀ d ∈ (D.prog C).inputs, d.name ∉ D.fresh C → D.P.src.t - 1 ≤ D.eps := by
  change ((certifyProfile? D.Pe (prof C) (D.prog C) false).isSome && D.inputsFit C &&
    (D.prog C).inputs.all fun d => decide (d.name ∈ D.fresh C) ||
      decide (D.P.src.t - 1 ≤ D.eps)) = true at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  obtain ⟨⟨B, outs⟩, hc⟩ := Option.isSome_iff_exists.mp h1
  refine ⟨B, outs, hc, h2, fun d hd hn => ?_⟩
  have := List.all_eq_true.mp h3 d hd
  simpa [hn] using this

/-- **The inputs of an admissible circuit meet the BGV input hypotheses.** -/
theorem inputsOK_bgv (hkind : D.P.src.kind = .bgv) (henc : D.EncOKBGV) (C : D.Circ)
    (ht : 0 < D.P.src.t) (hfit : D.inputsFit C = true)
    (hpe : ∀ d ∈ (D.prog C).inputs, d.name ∉ D.fresh C → D.P.src.t - 1 ≤ D.eps)
    (pk : D.PK) (sk : D.SK)
    (hk : D.KeysOK pk sk) (ins : List (Poly D.P.src.t D.P.src.N × D.ER))
    (hins : ∀ p ∈ ins, D.GoodE pk sk p.2) (hlen : ins.length = (D.fresh C).length) :
    Correct.InputsOK D.Pe (D.sec sk) (D.prog C)
        (fun x => .exact (D.msg C (ins.map Prod.fst) x))
        (D.cts C (ins.map fun p => D.enc pk p.1 p.2)) ∧
      Trace.BoundsOK D.Pe (D.sec sk) (D.prog C)
        (fun x => .exact (D.msg C (ins.map Prod.fst) x))
        (D.cts C (ins.map fun p => D.enc pk p.1 p.2)) := by
  have hk' : D.Pe.src.kind = .bgv := hkind
  -- one input, at any bound `b` that is at least `eps` (fresh) or `t − 1` (plaintext)
  have key : ∀ x d b, (D.prog C).inputs.find? (·.name = x) = some d →
      (x ∈ D.fresh C → D.eps ≤ b) → (x ∉ D.fresh C → D.P.src.t - 1 ≤ b) →
      Correct.Encrypts D.Pe (D.sec sk) b
        (Correct.inputVal D.Pe (fun x => .exact (D.msg C (ins.map Prod.fst) x)) d)
        (D.cts C (ins.map fun p => D.enc pk p.1 p.2) x) := by
    intro x d b hd hbf hbp
    have hn : d.name = x := by simpa using List.find?_some hd
    have hmem : d ∈ (D.prog C).inputs := List.mem_of_find?_eq_some hd
    obtain ⟨hfr, hcn⟩ := fit_at hfit hmem
    simp only [Correct.inputVal]
    by_cases hx : x ∈ D.fresh C
    · obtain ⟨hp, hkey, hlv, -⟩ := hfr (hn ▸ hx)
      obtain ⟨i, hi, hm, hct⟩ := fresh_index C pk ins hlen x hx
      obtain ⟨-, hl2, he⟩ := henc pk sk hk ins[i].1 ins[i].2 (hins _ (List.getElem_mem hi))
      rw [hn, hm, hct, hp, hkey, hlv]
      refine encrypts_of_bgv D.Pe hk' (D.sec sk) b ins[i].1 2 D.lvl 1 d.scale _ hl2 ?_
      rw [FHE.KeySwitch.automorph_one]
      exact ⟨he.1, he.2.trans (hbf hx)⟩
    · obtain ⟨hp1, hQ, -⟩ := hcn (hn ▸ hx)
      obtain ⟨hm, hct⟩ :=
        const_index C (ins.map Prod.fst) (ins.map fun p => D.enc pk p.1 p.2) x hx
      have hpl := Validation.IndCpaD.plainOK_liftMsg D.Pe (D.sec sk) b
        (Correct.inputVal D.Pe (fun x => .exact (D.msg C (ins.map Prod.fst) x)) d) (D.pt C x)
        hp1 (by simp only [Correct.inputVal]; rw [hn, hm]) ht hQ (hbp hx)
      obtain ⟨hl1, m', hm', hbe⟩ := hpl
      simp only [Correct.inputVal] at hm' hl1 hbe
      rw [hn, hm] at hm'
      cases hm'
      rw [hn, hm, hct]
      exact encrypts_of_bgv D.Pe hk' (D.sec sk) b _ d.parts d.level d.key d.scale _ hl1 hbe
  refine ⟨fun x d hd => key x d _ hd (fun _ => le_rfl) (fun hx => ?_), fun x d b hd hb => ?_⟩
  · have hn : d.name = x := by simpa using List.find?_some hd
    exact hpe d (List.mem_of_find?_eq_some hd) (hn ▸ hx)
  · have hn : d.name = x := by simpa using List.find?_some hd
    have hmem : d ∈ (D.prog C).inputs := List.mem_of_find?_eq_some hd
    obtain ⟨hfr, hcn⟩ := fit_at hfit hmem
    refine key x d b hd (fun hx => ?_) (fun hx => (hcn (hn ▸ hx)).2.2 b (hn ▸ hb))
    obtain ⟨-, -, -, hbd⟩ := hfr (hn ▸ hx)
    rw [hn, hb] at hbd
    cases hbd

/-! ## The locked statements -/

theorem correct_bgv (D : AbsScheme) (henc : D.EncOKBGV) (prof : D.Circ → Trace.Budget)
    (adm : D.Circ → Bool) (hadm : ∀ C, adm C = true → admBGV D prof C = true)
    (ev : D.PK → D.Circ → List (ℕ × List (IntPoly D.P.src.N)) →
      List (ℕ × List (IntPoly D.P.src.N)))
    (hev : EvalMeetsBGV D prof adm ev) : Spec.IndCpaD.Correct (schemeBGV D ev adm) where
  fresh pk sk hk m r hr := by
    obtain ⟨hl, -, he⟩ := henc pk sk hk m r hr
    change bgvDecrypt D.P.src.t (D.sec sk)
      ((D.enc pk m r).2.map (ofInt (D.P.src.modulus (D.enc pk m r).1))) = m
    rw [hl]
    exact he.1
  eval pk sk hk C hC ins hins := by
    change (if (ins.map fun p => D.enc pk p.1 p.2).length = (D.fresh C).length
        then ev pk C (ins.map fun p => D.enc pk p.1 p.2) else []).map (D.decBGV sk) =
      D.sem C (ins.map Prod.fst)
    obtain ⟨B, outs, hcert, hfit, hpe⟩ := admBGV_some (hadm C hC)
    by_cases hlen : ins.length = (D.fresh C).length
    · obtain ⟨hP, hkind, -⟩ := Validation.Profile.certifyProfile?_some hcert
      have ht : 0 < D.P.src.t := by have := hP.plaintext.1; exact lt_of_lt_of_le (by norm_num) this
      obtain ⟨hin, hbd⟩ := inputsOK_bgv hkind henc C ht hfit hpe pk sk hk ins hins hlen
      obtain ⟨σ, hσ, hevq⟩ := hev pk sk hk C hC ins hins hlen
      obtain ⟨ρ, hρ, hout⟩ := Validation.Profile.certifyProfile?_sound D.Pe (prof C) (D.prog C)
        false B outs hcert (D.sec sk) _ _ hin hbd
      simp only [List.length_map, hlen, ite_true]
      rw [hevq]
      simp only [AbsScheme.sem, List.length_map, hlen, ite_true]
      erw [List.map_map]
      change Source.eval D.P.src (D.prog C) _ = some ρ at hρ
      erw [hρ]
      dsimp only
      apply List.map_congr_left
      intro o ho
      obtain ⟨v, ct, m, B', hv, hct, -, -, hm, -, hd, -⟩ := hout σ hσ o ho
      simp only [Function.comp, hv, hct, hm]
      unfold AbsScheme.decBGV
      rw [show D.outLevel C o = v.level from level_eq_bgv hkind _ _ ρ hρ o v hv]
      exact hd
    · simp only [AbsScheme.sem, List.length_map, hlen, ite_false]
      rfl

theorem bgv_prob_eq (D : AbsScheme) (henc : D.EncOKBGV) (prof : D.Circ → Trace.Budget)
    (adm : D.Circ → Bool) (hadm : ∀ C, adm C = true → admBGV D prof C = true)
    (ev : D.PK → D.Circ → List (ℕ × List (IntPoly D.P.src.N)) →
      List (ℕ × List (IntPoly D.P.src.N)))
    (hev : EvalMeetsBGV D prof adm ev) [DecidableEq (Poly D.P.src.t D.P.src.N)]
    {Ω Coins : Type} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    (pk : Ω → D.PK) (sk : Ω → D.SK) (tape : Ω → ℕ → D.ER) (coins : Ω → Coins)
    (A : Coins → D.PK → Spec.IndCpaD.Adv (schemeBGV D ev adm) Bool) (b : Bool)
    (hgood : ∀ᵐ ω ∂μ, D.KeysOK (pk ω) (sk ω) ∧ ∀ i, D.GoodE (pk ω) (sk ω) (tape ω i)) :
    μ {ω | Spec.IndCpaD.gameD (S := schemeBGV D ev adm) b (pk ω) (sk ω) (tape ω)
        (A (coins ω) (pk ω)) 0 [] = true} =
      μ {ω | Spec.IndCpaD.gameCPA (S := schemeBGV D ev adm) b (pk ω) (tape ω)
        (Spec.IndCpaD.reduction (S := schemeBGV D ev adm) A (coins ω) (pk ω)) 0 = true} :=
  Validation.IndCpaD.prob_eq (schemeBGV D ev adm)
    (correct_bgv D henc prof adm hadm ev hev) μ pk sk tape coins A b hgood

theorem bgv_prob_le (D : AbsScheme) (henc : D.EncOKBGV) (prof : D.Circ → Trace.Budget)
    (adm : D.Circ → Bool) (hadm : ∀ C, adm C = true → admBGV D prof C = true)
    (ev : D.PK → D.Circ → List (ℕ × List (IntPoly D.P.src.N)) →
      List (ℕ × List (IntPoly D.P.src.N)))
    (hev : EvalMeetsBGV D prof adm ev) [DecidableEq (Poly D.P.src.t D.P.src.N)]
    {Ω Coins : Type} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    (pk : Ω → D.PK) (sk : Ω → D.SK) (tape : Ω → ℕ → D.ER) (coins : Ω → Coins)
    (A : Coins → D.PK → Spec.IndCpaD.Adv (schemeBGV D ev adm) Bool) (b : Bool) (q : ℕ)
    (hq : ∀ r p, Spec.IndCpaD.Bounded (A r p) q) :
    μ {ω | Spec.IndCpaD.gameD (S := schemeBGV D ev adm) b (pk ω) (sk ω) (tape ω)
        (A (coins ω) (pk ω)) 0 [] = true} ≤
        μ {ω | Spec.IndCpaD.gameCPA (S := schemeBGV D ev adm) b (pk ω) (tape ω)
          (Spec.IndCpaD.reduction (S := schemeBGV D ev adm) A (coins ω) (pk ω)) 0 = true} +
          μ {ω | ¬ (D.KeysOK (pk ω) (sk ω) ∧ ∀ i < q, D.GoodE (pk ω) (sk ω) (tape ω i))} ∧
      μ {ω | Spec.IndCpaD.gameCPA (S := schemeBGV D ev adm) b (pk ω) (tape ω)
          (Spec.IndCpaD.reduction (S := schemeBGV D ev adm) A (coins ω) (pk ω)) 0 = true} ≤
        μ {ω | Spec.IndCpaD.gameD (S := schemeBGV D ev adm) b (pk ω) (sk ω) (tape ω)
          (A (coins ω) (pk ω)) 0 [] = true} +
          μ {ω | ¬ (D.KeysOK (pk ω) (sk ω) ∧ ∀ i < q, D.GoodE (pk ω) (sk ω) (tape ω i))} :=
  Validation.IndCpaD.prob_le (schemeBGV D ev adm)
    (correct_bgv D henc prof adm hadm ev hev) μ pk sk tape coins A b q hq

example := (@correct_bgv : type_of% @Challenge.IndCpaDProfile.correct_bgv)
example := (@bgv_prob_eq : type_of% @Challenge.IndCpaDProfile.bgv_prob_eq)
example := (@bgv_prob_le : type_of% @Challenge.IndCpaDProfile.bgv_prob_le)

end Validation.IndCpaDProfile
