import Challenge.IndCpaD.ProfileInstances
import Validation.IndCpaD.Profile
import Validation.IndCpaD.Textbook
import Validation.Profile.Tool

/-!
# Validation.IndCpaD.ProfileInstances — proofs of the pins of `Challenge.IndCpaD.ProfileInstances`

The tool's class is inside the profile class: the tool's certificate at the analysed input noise
gives the profile certificate at the computed budget (`Validation.Profile.certifyBFV?_profile`),
and that input noise is `eps` because every fresh input is at the top level (so the maximum in
`freshInputNoise` is over equal numbers). The OpenFHE-shaped statements follow from the
library-free ones by transferring `Correct` across the two descriptions of the same scheme: the
fields agree by definition except the message-level semantics, whose two definitions use
different matchers and are proved equal by cases. No locked definition is unfolded by name:
`profOf` is read through a local `rfl` equation, `admBFV` through `change`.
-/

namespace Validation.IndCpaDProfile
open Spec NPoly Scheme Source Spec.IndCpaDProfile Spec.IndCpaDBFV Spec.EncryptBFV Spec.Encrypt
  Spec.CertifyBFV Challenge.BFVEncrypt Challenge.IndCpaD Challenge.IndCpaDProfile
open Challenge.Profile (certifyBFVProfile?)

variable {St : Setting}

/-- `profOf`, unfolded (a local `rfl` equation). -/
theorem profOf_eq (St : Setting) (C : Circ St) : profOf St C =
    match certifyBFVFresh? C.input (.worst C.fresh St.Bk St.Bu St.B1 St.B2) with
    | some fc => fc.cert.budget
    | none => fun _ => ⟨0, 0, 0, 0, 0⟩ := rfl

theorem profOf_some (C : Circ St) (fc : FreshCertBFV)
    (h : certifyBFVFresh? C.input (.worst C.fresh St.Bk St.Bu St.B1 St.B2) = some fc) :
    profOf St C = fc.cert.budget := by
  rw [profOf_eq, h]

theorem foldl_max_const (c : ℕ) : ∀ (L : List ℕ) (a : ℕ), a ≤ c → (∀ x ∈ L, x = c) →
    L ≠ [] → L.foldl max a = c
  | [], _, _, _, h => absurd rfl h
  | x :: xs, a, ha, hL, _ => by
    have hx : x = c := hL x (by simp)
    rw [List.foldl_cons, hx, Nat.max_eq_right ha]
    rcases xs with _ | ⟨y, ys⟩
    · rfl
    · exact foldl_max_const c (y :: ys) c le_rfl (fun z hz => hL z (by simp [hz])) (by simp)

/-- The facts the tool's acceptance gives about the inputs. -/
theorem tool_facts (C : Circ St) (fc : FreshCertBFV)
    (h : certifyBFVFresh? C.input (.worst C.fresh St.Bk St.Bu St.B1 St.B2) = some fc)
    (hx : C.extraOK = true) :
    fc.params.inputNoise =
        freshInputNoise St.base.P C.prog C.fresh
          (worstError St.base.P.src.N St.base.P.secretBound St.Bk St.Bu St.B1 St.B2) ∧
      C.fresh ≠ [] ∧ (∀ x ∈ C.fresh, ∃ d ∈ C.prog.inputs, d.name = x) ∧
      ∀ d ∈ C.prog.inputs,
        (d.name ∈ C.fresh → d.parts = 2 ∧ d.key = 1 ∧ C.prog.boundOf d.name = none ∧
          d.level = top St) ∧
        (d.name ∉ C.fresh → d.parts = 1 ∧
          St.base.P.src.t - 1 ≤ St.base.P.src.modulus d.level / 2 ∧
          ∀ b, C.prog.boundOf d.name = some b → St.base.P.src.t - 1 ≤ b) := by
  obtain ⟨hpar, hfr, hc⟩ := Validation.BFVEncrypt.certifyBFVFresh?_spec _ _ fc h
  obtain ⟨heps, -, -⟩ := Validation.BFVEncrypt.certifyBFVFresh?_worst_eps _ fc _ _ _ _ _ h
  have henc := Validation.CertifyBFV.certifyBFV?_encodeOK _ _ hc
  obtain ⟨hPok, -⟩ := Validation.CertifyBFV.certifyBFV?_paramsOK _ _ hc
  obtain ⟨-, -, -, -, hra, -⟩ := Validation.CertifyBFV.certifyBFV?_spec _ _ hc
  obtain ⟨-, hallok, -⟩ := Validation.BFV.PerInstrAux.refAnalyzeAt_some hra
  obtain ⟨hne, hdecl, hspec⟩ := Validation.BFVEncrypt.freshOKBFV?_spec _ _ hfr
  have hx1 := (Bool.and_eq_true _ _).mp hx |>.1
  obtain ⟨params, cert, used, eps, drift⟩ := fc
  simp only at hpar heps henc hPok hallok
  subst hpar
  refine ⟨by rw [heps]; rfl, hne, hdecl, fun d hd => ⟨fun hn => ?_, fun hn => ?_⟩⟩
  · obtain ⟨hp, hk, hb⟩ := (hspec d hd).1 hn
    have hlev := List.all_eq_true.mp hx1 d hd
    simp only [hn, ↓reduceIte, beq_iff_eq] at hlev
    exact ⟨hp, hk, hb, hlev⟩
  · have hp1 := (hspec d hd).2 hn
    have hok := List.all_eq_true.mp hallok d hd
    have hlv : 1 ≤ d.level := by
      simp only [Decl.ok, decide_eq_true_eq] at hok; exact hok.2.1
    have h2t : 2 ≤ St.base.P.src.t := hPok.plaintext.1
    have henc1 : St.base.P.src.t - 1 ≤ St.base.P.src.qs.headD 0 / 2 := henc.1
    have henc2 : ∀ q ∈ St.base.P.src.qs, St.base.P.src.t ≤ q := henc.2
    have hQ : St.base.P.src.t - 1 ≤ St.base.P.src.modulus d.level / 2 :=
      henc1.trans (Nat.div_le_div_right
        (Validation.IndCpaD.headD_le_modulus _ _ hlv fun q hq => by have := henc2 q hq; omega))
    refine ⟨hp1, hQ, fun b hb => ?_⟩
    have hb' := List.all_eq_true.mp hx1 d hd
    simp only [hn, ↓reduceIte, hb] at hb'
    simpa using hb'

/-- The analysed input noise is `eps`. -/
theorem eps_eq (C : Circ St) (fc : FreshCertBFV)
    (h : certifyBFVFresh? C.input (.worst C.fresh St.Bk St.Bu St.B1 St.B2) = some fc)
    (hx : C.extraOK = true) : fc.params.inputNoise = (dataOf St).eps := by
  obtain ⟨hn, hne, hdecl, hin⟩ := tool_facts C fc h hx
  rw [hn]
  show _ = _ + encodeDev St.base.P.src.t (Qtop St)
  unfold freshInputNoise
  congr 1
  apply foldl_max_const _ _ 0 (Nat.zero_le _)
  · intro y hy
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hy
    obtain ⟨hd1, hd2⟩ := List.mem_filter.mp hd
    have hlev := ((hin d hd1).1 (by simpa using hd2)).2.2.2
    rw [hlev]; rfl
  · obtain ⟨x, hxm⟩ := List.exists_mem_of_ne_nil _ hne
    obtain ⟨d, hd, hdn⟩ := hdecl x hxm
    intro hnil
    have : d ∈ C.prog.inputs.filter fun d => d.name ∈ C.fresh :=
      List.mem_filter.mpr ⟨hd, by simpa [hdn] using hxm⟩
    rw [List.map_eq_nil_iff] at hnil
    rw [hnil] at this
    simp at this

/-- The tool's inputs have the shape of the profile class. -/
theorem fit_of_tool (C : Circ St) (fc : FreshCertBFV)
    (h : certifyBFVFresh? C.input (.worst C.fresh St.Bk St.Bu St.B1 St.B2) = some fc)
    (hx : C.extraOK = true) : (dataOf St).inputsFit C = true := by
  obtain ⟨-, -, -, hin⟩ := tool_facts C fc h hx
  unfold AbsScheme.inputsFit
  rw [List.all_eq_true]
  intro d hd
  have hd' : d ∈ C.prog.inputs := hd
  by_cases hn : d.name ∈ C.fresh
  · have hn' : d.name ∈ (dataOf St).fresh C := hn
    obtain ⟨hp, hk, hb, hl⟩ := (hin d hd').1 hn
    rw [ite_eq_left_of_eq_true _ _ (eq_true hn')]
    simp only [Bool.and_eq_true, beq_iff_eq, Option.isNone_iff_eq_none]
    exact ⟨⟨⟨hp, hk⟩, hl⟩, hb⟩
  · have hn' : d.name ∉ (dataOf St).fresh C := hn
    obtain ⟨hp, hQ, hb⟩ := (hin d hd').2 hn
    rw [ite_eq_right_of_eq_false _ _ (eq_false hn')]
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
    refine ⟨⟨hp, hQ⟩, ?_⟩
    have e : ((dataOf St).prog C).boundOf d.name = C.prog.boundOf d.name := rfl
    rw [e]
    rcases hbo : C.prog.boundOf d.name with _ | b
    · rfl
    · exact decide_eq_true (hb b hbo)

/-! ## The two descriptions of the same scheme -/

theorem msg_eq (C : Circ St) (ms : List (Poly St.base.P.src.t St.base.P.src.N)) (x : Var) :
    (dataOf St).msg C ms x = C.msg ms x := by
  unfold AbsScheme.msg Circ.msg
  split
  · rename_i i hi
    have hi' : C.fresh.idxOf? x = some i := hi
    rw [hi']; rfl
  · rename_i hi
    have hi' : C.fresh.idxOf? x = none := hi
    rw [hi']; rfl

theorem cts_eq (C : Circ St) (cs : List (CT (St := St))) (x : Var) :
    (dataOf St).cts C cs x = C.cts cs x := by
  unfold AbsScheme.cts Circ.cts
  split
  · rename_i i hi
    have hi' : C.fresh.idxOf? x = some i := hi
    rw [hi']; rfl
  · rename_i hi
    have hi' : C.fresh.idxOf? x = none := hi
    rw [hi']; rfl

theorem sem_eq (C : Circ St) (ms : List (Poly St.base.P.src.t St.base.P.src.N)) :
    (dataOf St).sem C ms = Spec.IndCpaDBFV.sem C ms := by
  have hm : (fun x => Msg.exact ((dataOf St).msg C ms x)) = fun x => .exact (C.msg ms x) :=
    funext fun x => congrArg Msg.exact (msg_eq C ms x)
  unfold AbsScheme.sem Spec.IndCpaDBFV.sem
  rw [hm]
  split_ifs with h1 h2 h2
  · split
    · rename_i ρ hρ
      have hρ' : Source.eval St.base.P.src C.prog (fun x => .exact (C.msg ms x)) = some ρ := hρ
      rw [hρ']
      apply List.map_congr_left
      intro o _
      rcases hv : ρ o with _ | ⟨⟨m⟩, p, l, k, sc⟩
      · rfl
      · rfl
    · rename_i hρ
      have hρ' : Source.eval St.base.P.src C.prog (fun x => .exact (C.msg ms x)) = none := hρ
      rw [hρ']; rfl
  all_goals first | rfl | exact absurd h1 h2 | exact absurd h2 h1

/-- **`Correct` transfers** from the library-free description to `schemeWith St ev`. -/
theorem correct_transfer (St : Setting)
    (ev : PK (St := St) → Circ St → List (CT (St := St)) → List (CT (St := St)))
    (h : Spec.IndCpaD.Correct (schemeBFV (dataOf St) ev admissible)) :
    Spec.IndCpaD.Correct (schemeWith St ev) where
  fresh := h.fresh
  eval pk sk hk C hC ins hins := by
    have := h.eval pk sk hk C hC ins hins
    change _ = Spec.IndCpaDBFV.sem C (ins.map Prod.fst)
    rw [← sem_eq]
    exact this

/-! ## The locked statements -/

theorem admissible_profile (St : Setting) (C : Circ St) (h : admissible C = true) :
    admBFV (dataOf St) (profOf St) C = true := by
  rcases hfc : certifyBFVFresh? C.input (.worst C.fresh St.Bk St.Bu St.B1 St.B2) with _ | fc
  · exact (Validation.IndCpaD.admissible_none C hfc h).elim
  have hx := ((Bool.and_eq_true _ _).mp (Validation.IndCpaD.admissible_some C fc hfc h)).2
  have hcert := Validation.IndCpaD.analysed_cert C fc hfc
  have hpr := Validation.Profile.certifyBFV?_profile _ _ hcert
  have heps := eps_eq C fc hfc hx
  change ((certifyBFVProfile? (dataOf St).Pe (profOf St C) C.prog).isSome &&
    (dataOf St).inputsFit C) = true
  rw [profOf_some C fc hfc, fit_of_tool C fc hfc hx, Bool.and_true]
  have e : (dataOf St).Pe = (Validation.IndCpaD.analysed C fc.params.inputNoise).P := by
    rw [heps]; rfl
  rw [e]
  change (certifyBFVProfile? (Validation.IndCpaD.analysed C fc.params.inputNoise).P
    fc.cert.budget (Validation.IndCpaD.analysed C fc.params.inputNoise).prog).isSome = true
  rw [hpr]; rfl

theorem encOK_dataOf (St : Setting) (hSt : freshDecOK St = true) : (dataOf St).EncOKBFV := by
  intro pk sk hk m r hr
  rw [Validation.IndCpaD.freshDecOK_eq] at hSt
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hSt
  obtain ⟨ht, hdec⟩ := hSt
  obtain ⟨hs, he, hpk, -⟩ := hk
  have hε := Validation.FreshNoise.freshError_worst sk.s sk.e r.1 r.2.1 r.2.2
    St.base.P.secretBound St.Bk St.Bu St.B1 St.B2 hs he hr.1 hr.2.1 hr.2.2
  exact ⟨rfl, rfl, Validation.BFVEncrypt.encryptBFV_encrypts St.base.P.src.t (Qtop St) _ ht sk.s
    sk.e pk.b pk.a r.1 r.2.1 r.2.2 m hpk hε hdec⟩

theorem evalMeets_dataOf (St : Setting)
    (ev : PK (St := St) → Circ St → List (CT (St := St)) → List (CT (St := St)))
    (hev : EvalMeets St ev) : EvalMeetsBFV (dataOf St) (profOf St) admissible ev := by
  intro pk sk hk C hC ins hins hlen
  rcases hfc : certifyBFVFresh? C.input (.worst C.fresh St.Bk St.Bu St.B1 St.B2) with _ | fc
  · exact (Validation.IndCpaD.admissible_none C hfc hC).elim
  have hx := ((Bool.and_eq_true _ _).mp (Validation.IndCpaD.admissible_some C fc hfc hC)).2
  obtain ⟨σ, hσ, hevq⟩ := hev pk sk hk C hC fc hfc hx ins hins hlen
  refine ⟨σ, ?_, hevq⟩
  rw [profOf_some C fc hfc]
  have hm : (fun x => Msg.exact ((dataOf St).msg C (ins.map Prod.fst) x)) =
      fun x => .exact (C.msg (ins.map Prod.fst) x) := funext fun x => congrArg Msg.exact (msg_eq C _ x)
  have hc : (dataOf St).cts C (ins.map fun p => (dataOf St).enc pk p.1 p.2) =
      C.cts (ins.map fun p => enc pk p.1 p.2) := funext fun x => cts_eq C _ x
  rw [hm, hc]
  rw [eps_eq C fc hfc hx] at hσ
  exact hσ

theorem correct_via_profile (St : Setting) (hSt : freshDecOK St = true)
    (hA : Spec.Float.Conforms St.A) : Spec.IndCpaD.Correct (scheme St) :=
  correct_transfer St (libEval St)
    (correct_bfv (dataOf St) (encOK_dataOf St hSt) (profOf St) admissible
      (admissible_profile St) (libEval St)
      (evalMeets_dataOf St _ (Validation.IndCpaD.libEval_meets St hA)))

theorem correct_textEval_via_profile (St : Setting) (hSt : freshDecOK St = true)
    (hnl : ∀ Ps, St.base.mul ≠ some (.leveled Ps)) :
    Spec.IndCpaD.Correct (schemeWith St (textEval St)) :=
  correct_transfer St (textEval St)
    (correct_bfv (dataOf St) (encOK_dataOf St hSt) (profOf St) admissible
      (admissible_profile St) (textEval St)
      (evalMeets_dataOf St _ (Validation.IndCpaD.textEval_meets St hnl)))

theorem bfv_prob_eq_via_profile (St : Setting) (hSt : freshDecOK St = true)
    (hA : Spec.Float.Conforms St.A)
    {Ω Coins : Type} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    (pk : Ω → PK (St := St)) (sk : Ω → SK (St := St)) (tape : Ω → ℕ → ER (St := St))
    (coins : Ω → Coins) (A : Coins → PK (St := St) → Spec.IndCpaD.Adv (scheme St) Bool) (b : Bool)
    (hgood : ∀ᵐ ω ∂μ, KeysOK (pk ω) (sk ω) ∧ ∀ i, GoodE (pk ω) (sk ω) (tape ω i)) :
    μ {ω | Spec.IndCpaD.gameD (S := scheme St) b (pk ω) (sk ω) (tape ω) (A (coins ω) (pk ω)) 0 []
        = true} =
      μ {ω | Spec.IndCpaD.gameCPA (S := scheme St) b (pk ω) (tape ω)
        (Spec.IndCpaD.reduction (S := scheme St) A (coins ω) (pk ω)) 0 = true} :=
  Validation.IndCpaD.prob_eq (scheme St) (correct_via_profile St hSt hA) μ pk sk tape coins A b
    hgood

theorem bfv_prob_le_via_profile (St : Setting) (hSt : freshDecOK St = true)
    (hA : Spec.Float.Conforms St.A)
    {Ω Coins : Type} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    (pk : Ω → PK (St := St)) (sk : Ω → SK (St := St)) (tape : Ω → ℕ → ER (St := St))
    (coins : Ω → Coins) (A : Coins → PK (St := St) → Spec.IndCpaD.Adv (scheme St) Bool) (b : Bool)
    (q : ℕ) (hq : ∀ r p, Spec.IndCpaD.Bounded (A r p) q) :
    μ {ω | Spec.IndCpaD.gameD (S := scheme St) b (pk ω) (sk ω) (tape ω) (A (coins ω) (pk ω)) 0 []
        = true} ≤
        μ {ω | Spec.IndCpaD.gameCPA (S := scheme St) b (pk ω) (tape ω)
          (Spec.IndCpaD.reduction (S := scheme St) A (coins ω) (pk ω)) 0 = true} +
          μ {ω | ¬ (KeysOK (pk ω) (sk ω) ∧ ∀ i < q, GoodE (pk ω) (sk ω) (tape ω i))} ∧
      μ {ω | Spec.IndCpaD.gameCPA (S := scheme St) b (pk ω) (tape ω)
          (Spec.IndCpaD.reduction (S := scheme St) A (coins ω) (pk ω)) 0 = true} ≤
        μ {ω | Spec.IndCpaD.gameD (S := scheme St) b (pk ω) (sk ω) (tape ω) (A (coins ω) (pk ω))
          0 [] = true} +
          μ {ω | ¬ (KeysOK (pk ω) (sk ω) ∧ ∀ i < q, GoodE (pk ω) (sk ω) (tape ω i))} :=
  Validation.IndCpaD.prob_le (scheme St) (correct_via_profile St hSt hA) μ pk sk tape coins A b q
    hq

theorem admBFV_tiny : admBFV (dataOf tinySetting) (profOf tinySetting) tinyCirc = true ∧
    (dataOf tinySetting).EncOKBFV :=
  ⟨admissible_profile _ _ Validation.IndCpaD.admissible_tiny.2,
    encOK_dataOf _ Validation.IndCpaD.admissible_tiny.1⟩

example := (@admissible_profile : type_of% @Challenge.IndCpaDProfile.admissible_profile)
example := (@encOK_dataOf : type_of% @Challenge.IndCpaDProfile.encOK_dataOf)
example := (@evalMeets_dataOf : type_of% @Challenge.IndCpaDProfile.evalMeets_dataOf)
example := (@correct_via_profile : type_of% @Challenge.IndCpaDProfile.correct_via_profile)
example := (@correct_textEval_via_profile :
  type_of% @Challenge.IndCpaDProfile.correct_textEval_via_profile)
example := (@bfv_prob_eq_via_profile : type_of% @Challenge.IndCpaDProfile.bfv_prob_eq_via_profile)
example := (@bfv_prob_le_via_profile : type_of% @Challenge.IndCpaDProfile.bfv_prob_le_via_profile)
example := (@admBFV_tiny : type_of% @Challenge.IndCpaDProfile.admBFV_tiny)

end Validation.IndCpaDProfile
