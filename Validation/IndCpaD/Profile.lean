import Challenge.IndCpaD.Profile
import Validation.IndCpaD.Abstract
import Validation.IndCpaD.Levels
import Validation.Profile

/-!
# Validation.IndCpaD.Profile — proofs of the pins of `Challenge.IndCpaD.Profile`

`correct_bfv` is the proof of `Validation.IndCpaD.correct_of_meets` with the tool's certificate
replaced by the profile certificate (`Validation.Profile.certifyBFVProfile?_sound`), the modelled
encryption by the hypothesis `EncOK` (which gives `InputsOK` for the fresh inputs, and fresh
decryption directly: `BFVEncrypts` contains it), and the library's circuit type by the abstract
one. No locked definition is unfolded by name: `admBFV` is read through `change`.
-/

namespace Validation.IndCpaDProfile
open Spec NPoly Scheme Source Spec.Encrypt Spec.IndCpaDProfile Challenge.IndCpaDProfile
open Challenge.Profile (certifyBFVProfile?)

variable {D : AbsScheme}

/-! ## Generic facts about the abstract data -/

/-- The levels of `Source.eval` do not depend on the messages (BFV). -/
theorem level_eq_bfv {Pr : Params} (hk : Pr.kind = .bfv) (prog : Program)
    (msgs : Var → Msg Pr.t Pr.N) (ρ : Env Pr) (h : Source.eval Pr prog msgs = some ρ)
    (o : Var) (v : Val Pr) (hv : ρ o = some v) :
    ((Source.eval Pr prog (fun _ => .exact 0) >>= fun ρ => ρ o).map (·.level)).getD 0 =
      v.level := by
  open Validation.BFV.SoundAux in
  have hz0 : zenv (initEnv Pr prog msgs) = initEnv Pr prog fun _ => .exact 0 := by
    funext x; simp only [zenv, initEnv, Option.map_map]; rfl
  open Validation.BFV.SoundAux in
  have hf := Validation.IndCpaD.foldlM_zenv hk prog.body (initEnv Pr prog msgs)
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

/-- The fresh name `x` at index `i`: its message and ciphertext. -/
theorem fresh_index (C : D.Circ) (pk : D.PK)
    (ins : List (Poly D.P.src.t D.P.src.N × D.ER)) (hlen : ins.length = (D.fresh C).length)
    (x : Var) (hx : x ∈ D.fresh C) :
    ∃ i, ∃ hi : i < ins.length,
      D.msg C (ins.map Prod.fst) x = ins[i].1 ∧
      D.cts C (ins.map fun p => D.enc pk p.1 p.2) x = (D.enc pk ins[i].1 ins[i].2).2 := by
  obtain ⟨i, hi⟩ := Option.isSome_iff_exists.mp (List.isSome_idxOf?.mpr hx)
  obtain ⟨hlt, -⟩ := List.idxOf?_eq_some_iff.mp hi
  have hlt' : i < ins.length := hlen ▸ hlt
  refine ⟨i, hlt', ?_, ?_⟩
  · simp only [AbsScheme.msg, hi, List.getElem?_map, List.getElem?_eq_getElem hlt',
      Option.map_some, Option.getD_some]
  · simp only [AbsScheme.cts, hi, List.getElem?_map, List.getElem?_eq_getElem hlt',
      Option.map_some, Option.getD_some]

/-- A non-fresh name: its message is the constant, its ciphertext the stored `liftMsg`. -/
theorem const_index (C : D.Circ) (ms : List (Poly D.P.src.t D.P.src.N))
    (cs : List (ℕ × List (IntPoly D.P.src.N))) (x : Var) (hx : x ∉ D.fresh C) :
    D.msg C ms x = D.pt C x ∧ D.cts C cs x = [liftMsg (D.pt C x)] := by
  have hnone : (D.fresh C).idxOf? x = none := List.idxOf?_eq_none_iff.mpr hx
  exact ⟨by simp only [AbsScheme.msg, hnone], by simp only [AbsScheme.cts, hnone]⟩

/-- `inputsFit`, read at one declaration. -/
theorem fit_at {C : D.Circ} (hfit : D.inputsFit C = true) {d : Decl} (hd : d ∈ (D.prog C).inputs) :
    (d.name ∈ D.fresh C → d.parts = 2 ∧ d.key = 1 ∧ d.level = D.lvl ∧
        (D.prog C).boundOf d.name = none) ∧
      (d.name ∉ D.fresh C → d.parts = 1 ∧ D.P.src.t - 1 ≤ D.P.src.modulus d.level / 2 ∧
        ∀ b, (D.prog C).boundOf d.name = some b → D.P.src.t - 1 ≤ b) := by
  have h := List.all_eq_true.mp hfit d hd
  refine ⟨fun hx => ?_, fun hx => ?_⟩
  · simp only [hx, ↓reduceIte, Bool.and_eq_true, beq_iff_eq, Option.isNone_iff_eq_none] at h
    exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩
  · simp only [hx, ↓reduceIte, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
    refine ⟨h.1.1, h.1.2, fun b hb => ?_⟩
    have h2 := h.2
    rw [hb] at h2
    simpa using h2

/-- `Encrypts` reads the parameters only through `P.src` (but through a matcher that takes `P`,
hence the case split), and the value not through its scale; it is monotone in the bound. -/
theorem encrypts_Pe (D : AbsScheme) (s : IntPoly D.P.src.N) (B B' : ℕ) (hB : B ≤ B')
    (m : Poly D.P.src.t D.P.src.N) (p l k : ℕ) (sc sc' : ℚ) (ct : List (IntPoly D.P.src.N))
    (h : Correct.Encrypts D.P s B ⟨.exact m, p, l, k, sc⟩ ct) :
    Correct.Encrypts D.Pe s B' ⟨.exact m, p, l, k, sc'⟩ ct := by
  unfold Correct.Encrypts at h ⊢
  obtain ⟨hl, h⟩ := h
  refine ⟨hl, ?_⟩
  have e : D.Pe.src.kind = D.P.src.kind := rfl
  revert h
  rw [e]
  cases D.P.src.kind with
  | bgv => exact fun h => ⟨h.1, h.2.trans hB⟩
  | bfv => exact fun h => ⟨h.1, h.2.trans hB⟩

/-- **The inputs of an admissible circuit meet `InputsOK`** (BFV): the fresh inputs by `EncOK`,
the constants as stored `liftMsg` plaintexts. -/
theorem inputsOK_fit (hkind : D.P.src.kind = .bfv) (henc : D.EncOKBFV) (C : D.Circ)
    (ht : 0 < D.P.src.t) (hfit : D.inputsFit C = true) (pk : D.PK) (sk : D.SK)
    (hk : D.KeysOK pk sk) (ins : List (Poly D.P.src.t D.P.src.N × D.ER))
    (hins : ∀ p ∈ ins, D.GoodE pk sk p.2) (hlen : ins.length = (D.fresh C).length) :
    TraceBFV.InputsOK D.Pe (D.sec sk) (D.prog C)
      (fun x => .exact (D.msg C (ins.map Prod.fst) x))
      (D.cts C (ins.map fun p => D.enc pk p.1 p.2)) := by
  intro x d hd
  have hn : d.name = x := by simpa using List.find?_some hd
  have hmem : d ∈ (D.prog C).inputs := List.mem_of_find?_eq_some hd
  obtain ⟨hfr, hcn⟩ := fit_at hfit hmem
  by_cases hx : x ∈ D.fresh C
  · obtain ⟨hp, hkey, hlv, hbd⟩ := hfr (hn ▸ hx)
    obtain ⟨i, hi, hm, hct⟩ := fresh_index C pk ins hlen x hx
    have hp1 : ¬ d.parts = 1 := by omega
    simp only [hp1, ↓reduceIte]
    obtain ⟨-, hl2, he⟩ := henc pk sk hk ins[i].1 ins[i].2 (hins _ (List.getElem_mem hi))
    have hb : TraceBFV.inputBound D.Pe (D.prog C) d = D.eps := by
      simp only [TraceBFV.inputBound, hbd, hp1, ↓reduceIte, Option.getD_none]
    rw [hb, hct]
    simp only [Correct.inputVal]
    rw [hn, hm, hp, hkey, hlv]
    refine encrypts_Pe D (D.sec sk) D.eps D.eps le_rfl ins[i].1 2 D.lvl 1 0 d.scale _ ⟨hl2, ?_⟩
    simp only [hkind]
    rw [FHE.KeySwitch.automorph_one]
    exact he
  · obtain ⟨hp1, hQ, hbd⟩ := hcn (hn ▸ hx)
    obtain ⟨hm, hct⟩ := const_index C (ins.map Prod.fst) (ins.map fun p => D.enc pk p.1 p.2) x hx
    simp only [hp1, ↓reduceIte]
    rw [hct]
    have hb : D.P.src.t - 1 ≤ TraceBFV.inputBound D.Pe (D.prog C) d := by
      unfold TraceBFV.inputBound
      rcases hbo : (D.prog C).boundOf d.name with _ | b
      · simp only [hp1, ↓reduceIte, Option.getD_none]; exact le_rfl
      · exact hbd b hbo
    exact Validation.IndCpaD.plainOK_liftMsg D.Pe (D.sec sk) _ _ (D.pt C x) hp1
      (by simp only [Correct.inputVal]; rw [hn, hm]) ht hQ hb

/-- The accepting branch of `admBFV` (by `change`). -/
theorem admBFV_some {prof : D.Circ → ℕ → TraceBFV.Budget} {C : D.Circ}
    (h : admBFV D prof C = true) :
    ∃ B outs, certifyBFVProfile? D.Pe (prof C) (D.prog C) = some (B, outs) ∧
      D.inputsFit C = true := by
  change ((certifyBFVProfile? D.Pe (prof C) (D.prog C)).isSome && D.inputsFit C) = true at h
  rw [Bool.and_eq_true] at h
  obtain ⟨⟨B, outs⟩, hc⟩ := Option.isSome_iff_exists.mp h.1
  exact ⟨B, outs, hc, h.2⟩

/-! ## The locked statements -/

theorem correct_bfv (D : AbsScheme) (henc : D.EncOKBFV)
    (prof : D.Circ → ℕ → TraceBFV.Budget) (adm : D.Circ → Bool)
    (hadm : ∀ C, adm C = true → admBFV D prof C = true)
    (ev : D.PK → D.Circ → List (ℕ × List (IntPoly D.P.src.N)) →
      List (ℕ × List (IntPoly D.P.src.N)))
    (hev : EvalMeetsBFV D prof adm ev) : Spec.IndCpaD.Correct (schemeBFV D ev adm) where
  fresh pk sk hk m r hr := by
    obtain ⟨hl, -, he⟩ := henc pk sk hk m r hr
    change bfvDecrypt D.P.src.t (D.sec sk)
      ((D.enc pk m r).2.map (ofInt (D.P.src.modulus (D.enc pk m r).1))) = m
    rw [hl]
    exact he.1
  eval pk sk hk C hC ins hins := by
    change (if (ins.map fun p => D.enc pk p.1 p.2).length = (D.fresh C).length
        then ev pk C (ins.map fun p => D.enc pk p.1 p.2) else []).map (D.decBFV sk) =
      D.sem C (ins.map Prod.fst)
    obtain ⟨B, outs, hcert, hfit⟩ := admBFV_some (hadm C hC)
    by_cases hlen : ins.length = (D.fresh C).length
    · obtain ⟨hP, hkind, -⟩ := Validation.Profile.certifyBFVProfile?_some hcert
      have ht : 0 < D.P.src.t := by have := hP.plaintext.1; exact lt_of_lt_of_le (by norm_num) this
      have hin := inputsOK_fit hkind henc C ht hfit pk sk hk ins hins hlen
      obtain ⟨σ, hσ, hevq⟩ := hev pk sk hk C hC ins hins hlen
      obtain ⟨ρ, hρ, hout⟩ := Validation.Profile.certifyBFVProfile?_sound D.Pe (prof C) (D.prog C)
        B outs hcert (D.sec sk) _ _ hin
      simp only [List.length_map, hlen, ite_true]
      rw [hevq]
      simp only [AbsScheme.sem, List.length_map, hlen, ite_true]
      erw [List.map_map]
      change Source.eval D.P.src (D.prog C) _ = some ρ at hρ
      erw [hρ]
      dsimp only
      apply List.map_congr_left
      intro o ho
      obtain ⟨v, ct, m, B', hv, hct, -, -, hm, -, hd⟩ := hout σ hσ o ho
      simp only [Function.comp, hv, hct, hm]
      unfold AbsScheme.decBFV
      rw [show D.outLevel C o = v.level from level_eq_bfv hkind _ _ ρ hρ o v hv]
      exact hd
    · simp only [AbsScheme.sem, List.length_map, hlen, ite_false]
      rfl

theorem bfv_prob_eq (D : AbsScheme) (henc : D.EncOKBFV)
    (prof : D.Circ → ℕ → TraceBFV.Budget) (adm : D.Circ → Bool)
    (hadm : ∀ C, adm C = true → admBFV D prof C = true)
    (ev : D.PK → D.Circ → List (ℕ × List (IntPoly D.P.src.N)) →
      List (ℕ × List (IntPoly D.P.src.N)))
    (hev : EvalMeetsBFV D prof adm ev) [DecidableEq (Poly D.P.src.t D.P.src.N)]
    {Ω Coins : Type} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    (pk : Ω → D.PK) (sk : Ω → D.SK) (tape : Ω → ℕ → D.ER) (coins : Ω → Coins)
    (A : Coins → D.PK → Spec.IndCpaD.Adv (schemeBFV D ev adm) Bool) (b : Bool)
    (hgood : ∀ᵐ ω ∂μ, D.KeysOK (pk ω) (sk ω) ∧ ∀ i, D.GoodE (pk ω) (sk ω) (tape ω i)) :
    μ {ω | Spec.IndCpaD.gameD (S := schemeBFV D ev adm) b (pk ω) (sk ω) (tape ω)
        (A (coins ω) (pk ω)) 0 [] = true} =
      μ {ω | Spec.IndCpaD.gameCPA (S := schemeBFV D ev adm) b (pk ω) (tape ω)
        (Spec.IndCpaD.reduction (S := schemeBFV D ev adm) A (coins ω) (pk ω)) 0 = true} :=
  Validation.IndCpaD.prob_eq (schemeBFV D ev adm)
    (correct_bfv D henc prof adm hadm ev hev) μ pk sk tape coins A b hgood

theorem bfv_prob_le (D : AbsScheme) (henc : D.EncOKBFV)
    (prof : D.Circ → ℕ → TraceBFV.Budget) (adm : D.Circ → Bool)
    (hadm : ∀ C, adm C = true → admBFV D prof C = true)
    (ev : D.PK → D.Circ → List (ℕ × List (IntPoly D.P.src.N)) →
      List (ℕ × List (IntPoly D.P.src.N)))
    (hev : EvalMeetsBFV D prof adm ev) [DecidableEq (Poly D.P.src.t D.P.src.N)]
    {Ω Coins : Type} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    (pk : Ω → D.PK) (sk : Ω → D.SK) (tape : Ω → ℕ → D.ER) (coins : Ω → Coins)
    (A : Coins → D.PK → Spec.IndCpaD.Adv (schemeBFV D ev adm) Bool) (b : Bool) (q : ℕ)
    (hq : ∀ r p, Spec.IndCpaD.Bounded (A r p) q) :
    μ {ω | Spec.IndCpaD.gameD (S := schemeBFV D ev adm) b (pk ω) (sk ω) (tape ω)
        (A (coins ω) (pk ω)) 0 [] = true} ≤
        μ {ω | Spec.IndCpaD.gameCPA (S := schemeBFV D ev adm) b (pk ω) (tape ω)
          (Spec.IndCpaD.reduction (S := schemeBFV D ev adm) A (coins ω) (pk ω)) 0 = true} +
          μ {ω | ¬ (D.KeysOK (pk ω) (sk ω) ∧ ∀ i < q, D.GoodE (pk ω) (sk ω) (tape ω i))} ∧
      μ {ω | Spec.IndCpaD.gameCPA (S := schemeBFV D ev adm) b (pk ω) (tape ω)
          (Spec.IndCpaD.reduction (S := schemeBFV D ev adm) A (coins ω) (pk ω)) 0 = true} ≤
        μ {ω | Spec.IndCpaD.gameD (S := schemeBFV D ev adm) b (pk ω) (sk ω) (tape ω)
          (A (coins ω) (pk ω)) 0 [] = true} +
          μ {ω | ¬ (D.KeysOK (pk ω) (sk ω) ∧ ∀ i < q, D.GoodE (pk ω) (sk ω) (tape ω i))} :=
  Validation.IndCpaD.prob_le (schemeBFV D ev adm)
    (correct_bfv D henc prof adm hadm ev hev) μ pk sk tape coins A b q hq

example := (@correct_bfv : type_of% @Challenge.IndCpaDProfile.correct_bfv)
example := (@bfv_prob_eq : type_of% @Challenge.IndCpaDProfile.bfv_prob_eq)
example := (@bfv_prob_le : type_of% @Challenge.IndCpaDProfile.bfv_prob_le)

end Validation.IndCpaDProfile
