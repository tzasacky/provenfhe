import Validation.IndCpaD.LMBasic
import Validation.IndCpaD.Abstract
import Validation.IndCpaD.ProfileAdv

/-!
# Validation.IndCpaD.LM — proofs of the generic pins of `Challenge.IndCpaD.LM`

The invariant of the real game (`Inv`): there are good fresh inputs `fins` for the fresh
entries of the global program `G`, the message run and the interpreter's run of `G.body` from
them succeed (`ρf`, `σf`), every entry decrypts to its selected message, and every linked entry's
name is a variable of `G` holding, in `ρf`, its selected message and, in `σf`, its ciphertext.

An evaluation query `C` on entries: the interpreter's run of `C` alone on the entries'
ciphertexts is extended by the run of the inlined program `G.body ++ C.body` on the fresh
inputs (both environments at the start of `C.body` extend `C`'s initial environments: the
entries' values by the invariant and the admissibility check on declarations, the constants by
construction), so on `C`'s outputs the two coincide (`LMBasic`); the fresh-only correctness of
the scheme on the inlined program (in the class by the admissibility check) gives that they
decrypt to what `C` computes on the entries' selected messages. Old entries are untouched: `C`
writes only new names.
-/

namespace Validation.IndCpaDLM
open Spec NPoly Scheme Source Spec.Encrypt Spec.IndCpaD Spec.IndCpaDProfile Spec.IndCpaDLM
  Challenge.IndCpaDLM MeasureTheory
open Validation.BFV.SoundAux (zenv zv)

/-! ## Messages and ciphertexts of a circuit, by its fresh names and constants -/

section Fill
variable {D : AbsScheme}

/-- The message of input `x` (as `AbsScheme.msg`). -/
def fmsg (f : List Var) (c : Var → M D) (ms : List (M D)) (x : Var) : M D :=
  match f.idxOf? x with
  | some i => ms[i]?.getD 0
  | none => c x

/-- The ciphertext of input `x` (as `AbsScheme.cts`). -/
def fcts (f : List Var) (c : Var → M D) (cs : List (CT D)) (x : Var) :
    List (IntPoly D.P.src.N) :=
  match f.idxOf? x with
  | some i => (cs[i]?.map (·.2)).getD []
  | none => [liftMsg (c x)]

theorem msg_mk (mk : Program → List Var → (Var → M D) → D.Circ)
    (hmk : ∀ p f c, D.prog (mk p f c) = p ∧ D.fresh (mk p f c) = f ∧ D.pt (mk p f c) = c)
    (p : Program) (f : List Var) (c : Var → M D) (ms : List (M D)) (x : Var) :
    D.msg (mk p f c) ms x = fmsg f c ms x := by
  unfold AbsScheme.msg fmsg
  rw [(hmk p f c).2.1, (hmk p f c).2.2]
  cases f.idxOf? x <;> rfl

theorem cts_mk (mk : Program → List Var → (Var → M D) → D.Circ)
    (hmk : ∀ p f c, D.prog (mk p f c) = p ∧ D.fresh (mk p f c) = f ∧ D.pt (mk p f c) = c)
    (p : Program) (f : List Var) (c : Var → M D) (cs : List (CT D)) (x : Var) :
    D.cts (mk p f c) cs x = fcts f c cs x := by
  unfold AbsScheme.cts fcts
  rw [(hmk p f c).2.1, (hmk p f c).2.2]
  cases f.idxOf? x <;> rfl

theorem fmsg_none {f : List Var} {c : Var → M D} {ms : List (M D)} {x : Var} (hx : x ∉ f) :
    fmsg f c ms x = c x := by
  have : f.idxOf? x = none := List.idxOf?_eq_none_iff.mpr hx
  simp only [fmsg, this]

theorem fcts_none {f : List Var} {c : Var → M D} {cs : List (CT D)} {x : Var} (hx : x ∉ f) :
    fcts f c cs x = [liftMsg (c x)] := by
  have : f.idxOf? x = none := List.idxOf?_eq_none_iff.mpr hx
  simp only [fcts, this]

theorem idxOf_append_mem {l r : List Var} {y : Var} (hy : y ∈ l) :
    (l ++ r).idxOf? y = l.idxOf? y := by
  obtain ⟨i, hi⟩ := Option.isSome_iff_exists.mp (List.isSome_idxOf?.mpr hy)
  rw [hi]
  obtain ⟨hlt, hget, hbef⟩ := List.idxOf?_eq_some_iff.mp hi
  refine List.idxOf?_eq_some_iff.mpr ⟨by simp; omega, ?_, ?_⟩
  · rw [List.getElem_append_left hlt]; exact hget
  · intro j hj
    have := hbef j hj
    rwa [List.getElem_append_left (by omega)]

theorem idxOf_append_single {l : List Var} {x y : Var} (hy : y ∉ l) (hxy : y = x) :
    (l ++ [x]).idxOf? y = some l.length := by
  subst hxy
  refine List.idxOf?_eq_some_iff.mpr ⟨by simp, by simp, ?_⟩
  intro j hj
  rw [List.getElem_append_left hj]
  intro h
  exact hy (h ▸ List.getElem_mem hj)

theorem idxOf_append_ne {l : List Var} {x y : Var} (hy : y ∉ l) (hxy : y ≠ x) :
    (l ++ [x]).idxOf? y = none :=
  List.idxOf?_eq_none_iff.mpr (by simp [hy, hxy])

end Fill

/-! ## Initial environments -/

theorem initEnv_ext {Pr : Params} (p p' : Program) (more : List Decl)
    (hin : p'.inputs = p.inputs ++ more) (m m' : Var → Msg Pr.t Pr.N)
    (hm : ∀ x d, p.inputs.find? (·.name = x) = some d → m x = m' x) :
    Validation.IndCpaDLM.Ext (initEnv Pr p m) (initEnv Pr p' m') := by
  intro x v hx
  simp only [initEnv, Option.map_eq_some_iff] at hx ⊢
  obtain ⟨d, hd, rfl⟩ := hx
  refine ⟨d, ?_, by rw [hm x d hd]⟩
  rw [hin, List.find?_append, hd]; rfl

theorem initCt_ext {P : FullParams} (p p' : Program) (more : List Decl)
    (hin : p'.inputs = p.inputs ++ more) (c c' : Var → List (IntPoly P.src.N))
    (hc : ∀ x d, p.inputs.find? (·.name = x) = some d → c x = c' x) :
    Validation.IndCpaDLM.Ext (Trace.initCt P p c) (Trace.initCt P p' c') := by
  intro x v hx
  simp only [Trace.initCt, Option.map_eq_some_iff] at hx ⊢
  obtain ⟨d, hd, rfl⟩ := hx
  refine ⟨d, ?_, by rw [hc x d hd]⟩
  rw [hin, List.find?_append, hd]; rfl

theorem initEnv_dom {Pr : Params} {P : FullParams} (p : Program) (m : Var → Msg Pr.t Pr.N)
    (c : Var → List (IntPoly P.src.N)) :
    ∀ x, (initEnv Pr p m x).isSome → (Trace.initCt P p c x).isSome := by
  intro x hx
  simp only [initEnv, Trace.initCt, Option.isSome_map] at hx ⊢
  exact hx

theorem find_name {l : List Decl} {x : Var} {d : Decl} (h : l.find? (·.name = x) = some d) :
    d.name = x ∧ d ∈ l := ⟨by simpa using List.find?_some h, List.mem_of_find?_eq_some h⟩

theorem find_none {l : List Decl} {x : Var} (h : x ∉ l.map (·.name)) :
    l.find? (·.name = x) = none := by
  rw [List.find?_eq_none]
  intro d hd hdx
  exact h (List.mem_map.mpr ⟨d, hd, by simpa using hdx⟩)

/-! ## `Source.eval`, in parts -/

theorem eval_parts {Pr : Params} {prog : Program} {m : Var → Msg Pr.t Pr.N} {ρ : Env Pr}
    (h : Source.eval Pr prog m = some ρ) :
    (prog.inputs.all fun d => d.ok Pr) = true ∧
      prog.body.foldlM (step Pr) (initEnv Pr prog m) = some ρ ∧
      ∀ o ∈ prog.outputs, (ρ o).isSome := by
  simp only [Source.eval, Option.bind_eq_bind, Option.pure_def] at h
  obtain ⟨h1, h⟩ := Validation.Trace.guard_bind_eq_some h
  obtain ⟨-, h⟩ := Validation.Trace.guard_bind_eq_some h
  obtain ⟨ρf, h2, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨h3, h⟩ := Validation.Trace.guard_bind_eq_some h
  cases h
  exact ⟨h1, h2, fun o ho => by simpa using List.all_eq_true.mp h3 o ho⟩

theorem eval_of_parts {Pr : Params} {prog : Program} {m : Var → Poly Pr.t Pr.N} {ρ : Env Pr}
    (h1 : (prog.inputs.all fun d => d.ok Pr) = true)
    (h2 : prog.body.foldlM (step Pr) (initEnv Pr prog fun x => .exact (m x)) = some ρ)
    (h3 : ∀ o ∈ prog.outputs, (ρ o).isSome) :
    Source.eval Pr prog (fun x => .exact (m x)) = some ρ := by
  have hf : (prog.inputs.all fun dcl => (Msg.exact (m dcl.name) : Msg Pr.t Pr.N).fits Pr.kind)
      = true := by
    rw [List.all_eq_true]; intro d _
    cases hk : Pr.kind <;> rfl
  have ho : (prog.outputs.all fun o => (ρ o).isSome) = true := List.all_eq_true.mpr h3
  simp [Source.eval, guard, h1, hf, h2]
  rw [ite_eq_left_of_eq_true _ _ (eq_true h3)]; rfl

/-- The message run succeeds where the zero-message replay does, and zeroes to it. -/
theorem foldl_of_zero {Pr : Params} (prog : Program) (m : Var → Msg Pr.t Pr.N) (ρz : Env Pr)
    (h : prog.body.foldlM (step Pr) (initEnv Pr prog fun _ => .exact 0) = some ρz) :
    ∃ ρ, prog.body.foldlM (step Pr) (initEnv Pr prog m) = some ρ ∧ zenv ρ = ρz := by
  have := foldl_zenv prog.body (initEnv Pr prog m)
  rw [zenv_initEnv, h] at this
  rcases h' : prog.body.foldlM (step Pr) (initEnv Pr prog m) with _ | ρ
  · rw [h'] at this; cases this
  · rw [h'] at this
    exact ⟨ρ, rfl, (Option.some.inj this).symm⟩

theorem zenv_apply {Pr : Params} (ρ : Env Pr) (x : Var) : zenv ρ x = (ρ x).map zv := rfl

/-! ## Zips -/

theorem zip4_index {α β γ δ : Type} :
    ∀ (as : List α) (ns : List β) (xs : List γ) (ys : List δ) (p : α × β × γ × δ),
      p ∈ as.zip (ns.zip (xs.zip ys)) →
      ∃ k : ℕ, as[k]? = some p.1 ∧ ns[k]? = some p.2.1 ∧ xs[k]? = some p.2.2.1 ∧
        ys[k]? = some p.2.2.2
  | [], _, _, _, _, hp => by simp at hp
  | _ :: _, [], _, _, _, hp => by simp at hp
  | _ :: _, _ :: _, [], _, _, hp => by simp at hp
  | _ :: _, _ :: _, _ :: _, [], _, hp => by simp at hp
  | a :: as, n :: ns, x :: xs, y :: ys, p, hp => by
    simp only [List.zip_cons_cons, List.mem_cons] at hp
    rcases hp with rfl | hp
    · exact ⟨0, rfl, rfl, rfl, rfl⟩
    · obtain ⟨k, h1, h2, h3, h4⟩ := zip4_index as ns xs ys p hp
      exact ⟨k + 1, h1, h2, h3, h4⟩


/-! ## The invariant of the real game -/

section Game
variable {D : AbsScheme} (mk : Program → List Var → (Var → M D) → D.Circ)
  (adm : D.Circ → Bool) (dec : D.SK → CT D → M D) (stepF : StepFn D)
  (b : Bool) (pk : D.PK) (sk : D.SK)

/-- The fresh ciphertexts. -/
def fencs (fins : List (M D × D.ER)) : List (CT D) := fins.map fun p => D.enc pk p.1 p.2

/-- **The invariant** (module docstring). -/
def Inv (T : List (LEntry D)) (G : Global D) : Prop :=
  ∃ fins : List (M D × D.ER), fins.length = G.fresh.length ∧ (∀ p ∈ fins, D.GoodE pk sk p.2) ∧
    (∀ x ∈ G.fresh, x ∈ G.names) ∧
    ∃ ρf σf,
      G.body.foldlM (step D.P.src)
        (initEnv D.P.src G.prog fun x => .exact (fmsg G.fresh G.pt (fins.map Prod.fst) x)) =
          some ρf ∧
      irun D stepF pk G.body (initEnv D.P.src G.prog fun _ => .exact 0)
        (Trace.initCt D.Pe G.prog (fcts G.fresh G.pt (fencs pk fins))) = some σf ∧
      (∀ e ∈ T, dec sk e.c = pick b e.m0 e.m1) ∧
      (∀ e ∈ T, e.linked = true → e.name ∈ G.names ∧
        (∃ v, ρf e.name = some v ∧ v.msg = .exact (pick b e.m0 e.m1)) ∧ σf e.name = some e.c.2)

theorem inv_empty : Inv dec stepF b pk sk [] (Global.empty D) :=
  ⟨[], rfl, by simp, by simp [Global.empty], _, _, rfl, rfl, by simp, by simp⟩

theorem fmsg_congr {f : List Var} {c c' : Var → M D} {ms : List (M D)} {y : Var}
    (h : c y = c' y) : fmsg f c ms y = fmsg f c' ms y := by
  unfold fmsg; rw [h]

theorem fcts_congr {f : List Var} {c c' : Var → M D} {cs : List (CT D)} {y : Var}
    (h : c y = c' y) : fcts f c cs y = fcts f c' cs y := by
  unfold fcts; rw [h]

theorem mem_names_input {G : Global D} {x : Var} (h : x ∈ G.inputs.map (·.name)) :
    x ∈ G.names := List.mem_append_left _ h

theorem mem_names_dst {G : Global D} {x : Var} (h : x ∈ G.body.map Trace.dst) :
    x ∈ G.names := List.mem_append_right _ h

theorem names_extend {G : Global D} {C : QCirc D} {x : Var} (h : x ∈ G.names) :
    x ∈ (G.extend C).names := by
  unfold Global.names at h ⊢
  simp only [Global.extend, List.map_append, List.mem_append] at h ⊢
  tauto

variable {mk adm dec stepF b pk sk}

/-- **The encryption oracle keeps the invariant.** -/
theorem inv_enc (hI : InterpOK D stepF)
    (hC : Correct (freshScheme D adm (interpEval D stepF) dec)) (hk : D.KeysOK pk sk)
    {T : List (LEntry D)} {G : Global D} (hT : Inv dec stepF b pk sk T G) (m0 m1 : M D)
    (x : Var) (r : D.ER) (hr : D.GoodE pk sk r) :
    Inv dec stepF b pk sk (T ++ [⟨m0, m1, D.enc pk (pick b m0 m1) r, x, decide (x ∉ G.names)⟩])
      (G.link x) := by
  obtain ⟨fins, hlen, hgood, hfr, ρf, σf, hρ, hσ, hdec, hlink⟩ := hT
  have hdec' : dec sk (D.enc pk (pick b m0 m1) r) = pick b m0 m1 := hC.fresh pk sk hk _ r hr
  by_cases hx : x ∈ G.names
  · have hG : G.link x = G := by unfold Global.link; rw [ite_eq_left_of_eq_true _ _ (eq_true hx)]
    rw [hG]
    refine ⟨fins, hlen, hgood, hfr, ρf, σf, hρ, hσ, ?_, ?_⟩
    · intro e he
      rcases List.mem_append.mp he with he | he
      · exact hdec e he
      · simp only [List.mem_singleton] at he; subst he; exact hdec'
    · intro e he hl
      rcases List.mem_append.mp he with he | he
      · exact hlink e he hl
      · simp only [List.mem_singleton] at he; subst he; simp [hx] at hl
  have hG : G.link x =
      { G with inputs := G.inputs ++ [freshDecl D x], fresh := G.fresh ++ [x] } := by
    unfold Global.link; rw [ite_eq_right_of_eq_false _ _ (eq_false hx)]
  rw [hG]
  have hxf : x ∉ G.fresh := fun h => hx (hfr x h)
  have hxin : x ∉ G.inputs.map (·.name) := fun h => hx (mem_names_input h)
  have hxd : x ∉ G.body.map Trace.dst := fun h => hx (mem_names_dst h)
  let fins' := fins ++ [(pick b m0 m1, r)]
  have hmsg : ∀ y, y ≠ x → fmsg (G.fresh ++ [x]) G.pt (fins'.map Prod.fst) y =
      fmsg G.fresh G.pt (fins.map Prod.fst) y := by
    intro y hyx
    by_cases hy : y ∈ G.fresh
    · unfold fmsg
      rw [idxOf_append_mem hy]
      obtain ⟨i, hi⟩ := Option.isSome_iff_exists.mp (List.isSome_idxOf?.mpr hy)
      rw [hi]
      have hlt : i < fins.length := hlen ▸ (List.idxOf?_eq_some_iff.mp hi).1
      simp only [fins', List.map_append]
      rw [List.getElem?_append_left (by simpa using hlt)]
    · rw [fmsg_none (by simp [hy, hyx]), fmsg_none hy]
  have hcts : ∀ y, y ≠ x → fcts (G.fresh ++ [x]) G.pt (fencs pk fins') y =
      fcts G.fresh G.pt (fencs pk fins) y := by
    intro y hyx
    by_cases hy : y ∈ G.fresh
    · unfold fcts
      rw [idxOf_append_mem hy]
      obtain ⟨i, hi⟩ := Option.isSome_iff_exists.mp (List.isSome_idxOf?.mpr hy)
      rw [hi]
      have hlt : i < fins.length := hlen ▸ (List.idxOf?_eq_some_iff.mp hi).1
      simp only [fencs, fins', List.map_append]
      rw [List.getElem?_append_left (by simpa using hlt)]
    · rw [fcts_none (by simp [hy, hyx]), fcts_none hy]
  have hne : ∀ y d, G.inputs.find? (·.name = y) = some d → y ≠ x := by
    intro y d hd hyx
    obtain ⟨hdn, hdm⟩ := find_name hd
    exact hxin (List.mem_map.mpr ⟨d, hdm, hdn.trans hyx⟩)
  have e1 := initEnv_ext (Pr := D.P.src) G.prog
    ({ G with inputs := G.inputs ++ [freshDecl D x], fresh := G.fresh ++ [x] } : Global D).prog
    [freshDecl D x] rfl _ (fun y => .exact (fmsg (G.fresh ++ [x]) G.pt (fins'.map Prod.fst) y))
    (fun y d hd => by rw [hmsg y (hne y d hd)])
  have e2 := initEnv_ext (Pr := D.P.src) G.prog
    ({ G with inputs := G.inputs ++ [freshDecl D x], fresh := G.fresh ++ [x] } : Global D).prog
    [freshDecl D x] rfl (fun _ => .exact 0) (fun _ => .exact 0) (fun _ _ _ => rfl)
  have e3 := initCt_ext (P := D.Pe) G.prog
    ({ G with inputs := G.inputs ++ [freshDecl D x], fresh := G.fresh ++ [x] } : Global D).prog
    [freshDecl D x] rfl _ (fcts (G.fresh ++ [x]) G.pt (fencs pk fins'))
    (fun y d hd => (hcts y (hne y d hd)).symm)
  obtain ⟨ρf', hρ', hρx⟩ := foldl_ext G.body _ _ ρf hρ e1
  obtain ⟨σf', hσ', hσx⟩ := irun_ext stepF hI pk G.body _ _ _ _ σf hσ e2 e3
  have hfindx : (G.inputs ++ [freshDecl D x]).find? (·.name = x) = some (freshDecl D x) := by
    rw [List.find?_append, find_none hxin]; simp [freshDecl]
  have hmx : fmsg (G.fresh ++ [x]) G.pt (fins'.map Prod.fst) x = pick b m0 m1 := by
    unfold fmsg
    rw [idxOf_append_single hxf rfl]
    simp [fins', hlen]
  have hcx : fcts (G.fresh ++ [x]) G.pt (fencs pk fins') x = (D.enc pk (pick b m0 m1) r).2 := by
    unfold fcts
    rw [idxOf_append_single hxf rfl]
    simp [fencs, fins', hlen]
  refine ⟨fins', by simp [fins', hlen], ?_, ?_, ρf', σf', hρ', hσ', ?_, ?_⟩
  · intro p hp
    rcases List.mem_append.mp hp with hp | hp
    · exact hgood p hp
    · simp only [List.mem_singleton] at hp; subst hp; exact hr
  · intro y hy
    rcases List.mem_append.mp hy with hy | hy
    · have := hfr y hy
      unfold Global.names at this ⊢
      simp only [List.map_append, List.mem_append] at this ⊢
      tauto
    · simp only [List.mem_singleton] at hy; subst hy
      unfold Global.names; simp [freshDecl]
  · intro e he
    rcases List.mem_append.mp he with he | he
    · exact hdec e he
    · simp only [List.mem_singleton] at he; subst he; exact hdec'
  · intro e he hl
    rcases List.mem_append.mp he with he | he
    · obtain ⟨hn, ⟨v, hv, hvm⟩, hσe⟩ := hlink e he hl
      refine ⟨?_, ⟨v, hρx _ _ hv, hvm⟩, hσx _ _ hσe⟩
      unfold Global.names at hn ⊢
      simp only [List.map_append, List.mem_append] at hn ⊢
      tauto
    · simp only [List.mem_singleton] at he; subst he
      refine ⟨by unfold Global.names; simp [freshDecl], ?_, ?_⟩
      · rw [foldl_nodst G.body _ ρf' hρ' x hxd]
        have : initEnv D.P.src ⟨G.inputs ++ [freshDecl D x], G.body, [], G.bounds⟩
            (fun y => Msg.exact (fmsg (G.fresh ++ [x]) G.pt (fins'.map Prod.fst) y)) x =
            some ⟨.exact (pick b m0 m1), 2, D.lvl, 1, 0⟩ := by
          simp only [initEnv, hfindx, Option.map_some, hmx]; rfl
        exact ⟨_, this, rfl⟩
      · rw [irun_nodst stepF hI pk G.body _ _ σf' hσ' x hxd]
        show Trace.initCt D.Pe ⟨G.inputs ++ [freshDecl D x], G.body, [], G.bounds⟩ _ x = _
        simp only [Trace.initCt, hfindx, Option.map_some, hcx]

theorem find_filter_eq {l : List Decl} {S : List Var} {y : Var} (hy : y ∉ S) :
    (l.filter fun d => decide (d.name ∉ S)).find? (·.name = y) = l.find? (·.name = y) := by
  rw [List.find?_filter]
  congr 1
  funext a
  by_cases h : a.name = y
  · subst h; simp [hy]
  · simp [h]

/-- **The evaluation oracle keeps the invariant.** -/
theorem inv_eval (hmk : ∀ p f c, D.prog (mk p f c) = p ∧ D.fresh (mk p f c) = f ∧ D.pt (mk p f c) = c)
    (hI : InterpOK D stepF)
    (hC : Correct (freshScheme D adm (interpEval D stepF) dec)) (hk : D.KeysOK pk sk)
    {T : List (LEntry D)} {G : Global D} (hT : Inv dec stepF b pk sk T G) (C : QCirc D)
    (idx : List ℕ) {outs : List (CT D)} {new : List (LEntry D)} {G' : Global D}
    (h : evalLM mk adm (interpEval D stepF) pk T G C idx = some (outs, new, G')) :
    Inv dec stepF b pk sk (T ++ new) G' := by
  obtain ⟨fins, hlen, hgood, hfr, ρf, σf, hρ, hσ, hdec, hlink⟩ := hT
  unfold evalLM at h
  split at h
  swap
  · cases h
  rename_i es hes
  split at h
  swap
  · cases h
  rename_i hadm
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨hout, hnew, hG'⟩ := h
  subst hG'
  have hesT : ∀ e ∈ es, e ∈ T := fun e he => by
    obtain ⟨j, hj⟩ := Validation.IndCpaD.mapM_mem hes e he
    exact List.mem_of_getElem? hj
  -- the admissibility check, read
  unfold admLM at hadm
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hadm
  obtain ⟨⟨⟨⟨⟨⟨a1, a2⟩, a3⟩, a4⟩, a5⟩, a6⟩, a7⟩ := hadm
  simp only [List.map_map, Function.comp_def] at a1
  have hlinked : ∀ e ∈ es, e.linked = true := fun e he =>
    List.all_eq_true.mp a2 (e.name, e.linked) (List.mem_map.mpr ⟨e, he, rfl⟩)
  have hnew_names : ∀ x ∈ constNames C ++ C.1.body.map Trace.dst, x ∉ G.names := fun x hx => by
    have := List.all_eq_true.mp a3 x hx; simpa using this
  -- the zero replay of `G` is the zeroed message run
  have hGz : G.body.foldlM (step D.P.src) (initEnv D.P.src G.prog fun _ => .exact 0) =
      some (zenv ρf) := by
    rw [← zenv_initEnv G.prog (fun x => .exact (fmsg G.fresh G.pt (fins.map Prod.fst) x)),
      foldl_zenv, hρ]; rfl
  have hmeta : ∀ d ∈ C.1.inputs, d.name ∈ C.2.1 → metaOK (zenv ρf) d = true := by
    have a5' := a5
    unfold Global.replay at a5'
    rw [hGz] at a5'
    intro d hd hdn
    have := List.all_eq_true.mp a5' d hd
    simpa [hdn] using this
  -- the global program after the query
  have hpt : ∀ y, y ∉ constNames C → (G.extend C).pt y = G.pt y := fun y hy => by
    show (if y ∈ constNames C then C.2.2 y else G.pt y) = G.pt y
    rw [ite_eq_right_of_eq_false _ _ (eq_false hy)]
  have hptC : ∀ y, y ∈ constNames C → (G.extend C).pt y = C.2.2 y := fun y hy => by
    show (if y ∈ constNames C then C.2.2 y else G.pt y) = C.2.2 y
    rw [ite_eq_left_of_eq_true _ _ (eq_true hy)]
  have hGin : ∀ y d, G.inputs.find? (·.name = y) = some d → y ∉ constNames C := by
    intro y d hd hy
    obtain ⟨hdn, hdm⟩ := find_name hd
    exact hnew_names y (List.mem_append_left _ hy)
      (mem_names_input (List.mem_map.mpr ⟨d, hdm, hdn⟩))
  have e1 := initEnv_ext (Pr := D.P.src) G.prog (G.extend C).prog
    (C.1.inputs.filter fun d => decide (d.name ∉ C.2.1)) rfl
    (fun y => .exact (fmsg G.fresh G.pt (fins.map Prod.fst) y))
    (fun y => .exact (fmsg G.fresh (G.extend C).pt (fins.map Prod.fst) y))
    (fun y d hd => by rw [fmsg_congr (hpt y (hGin y d hd)).symm])
  have e2 := initEnv_ext (Pr := D.P.src) G.prog (G.extend C).prog
    (C.1.inputs.filter fun d => decide (d.name ∉ C.2.1)) rfl (fun _ => .exact 0)
    (fun _ => .exact 0) (fun _ _ _ => rfl)
  have e3 := initCt_ext (P := D.Pe) G.prog (G.extend C).prog
    (C.1.inputs.filter fun d => decide (d.name ∉ C.2.1)) rfl
    (fcts G.fresh G.pt (fencs pk fins)) (fcts G.fresh (G.extend C).pt (fencs pk fins))
    (fun y d hd => fcts_congr (hpt y (hGin y d hd)).symm)
  obtain ⟨ρ1, hρ1, hρ1x⟩ := foldl_ext G.body _ _ ρf hρ e1
  obtain ⟨ρ1z, hρ1z, hρ1zx⟩ := foldl_ext G.body _ _ _ hGz e2
  obtain ⟨σ1, hσ1, hσ1x⟩ := irun_ext stepF hI pk G.body _ _ _ _ σf hσ e2 e3
  -- the query alone
  obtain ⟨ρCz, hCz⟩ := Option.isSome_iff_exists.mp a4
  obtain ⟨hCok, hCfold, hCout⟩ := eval_parts hCz
  let cs : List (CT D) := es.map (·.c)
  obtain ⟨σs, hσs, hσsd⟩ := irun_progress stepF hI pk C.1.body _ ρCz
    (Trace.initCt D.Pe C.1 (fcts C.2.1 C.2.2 cs)) hCfold (initEnv_dom _ _ _)
  let ms : List (M D) := es.map fun e => pick b e.m0 e.m1
  obtain ⟨ρCm, hCm, hCmz⟩ := foldl_of_zero C.1 (fun x => .exact (fmsg C.2.1 C.2.2 ms x)) ρCz hCfold
  -- the query's start, inside the inlined program
  have hlenes : es.length = C.2.1.length := by rw [a1]; simp
  have entry : ∀ y, y ∈ C.2.1 → ∃ e ∈ es, e.name = y ∧
      fmsg C.2.1 C.2.2 ms y = pick b e.m0 e.m1 ∧ fcts C.2.1 C.2.2 cs y = e.c.2 := by
    intro y hy
    obtain ⟨i, hi⟩ := Option.isSome_iff_exists.mp (List.isSome_idxOf?.mpr hy)
    obtain ⟨hlt, hget, -⟩ := List.idxOf?_eq_some_iff.mp hi
    have hlt' : i < es.length := hlenes ▸ hlt
    refine ⟨es[i], List.getElem_mem hlt', ?_, ?_, ?_⟩
    · have : C.2.1[i] = (es.map (·.name))[i]'(by simpa using hlt') := by simp only [a1]
      rw [hget] at this; simpa using this.symm
    · simp [fmsg, hi, ms, hlt']
    · simp [fcts, hi, cs, hlt']
  have constc : ∀ y d, C.1.inputs.find? (·.name = y) = some d → y ∉ C.2.1 →
      y ∈ constNames C := by
    intro y d hd hy
    obtain ⟨hdn, hdm⟩ := find_name hd
    unfold constNames
    exact List.mem_filter.mpr ⟨List.mem_map.mpr ⟨d, hdm, hdn⟩, by simpa using hy⟩
  have notG : ∀ y, y ∈ constNames C → y ∉ G.inputs.map (·.name) ∧ y ∉ G.body.map Trace.dst ∧
      y ∉ G.fresh := fun y hy => by
    have h1 := hnew_names y (List.mem_append_left _ hy)
    exact ⟨fun h => h1 (mem_names_input h), fun h => h1 (mem_names_dst h),
      fun h => h1 (hfr y h)⟩
  have findG' : ∀ y, y ∉ G.inputs.map (·.name) → y ∉ C.2.1 →
      (G.extend C).prog.inputs.find? (·.name = y) = C.1.inputs.find? (·.name = y) := by
    intro y h1 h2
    show (G.inputs ++ C.1.inputs.filter fun d => decide (d.name ∉ C.2.1)).find? _ = _
    rw [List.find?_append, find_none h1, find_filter_eq h2]; rfl
  have metaV : ∀ d ∈ C.1.inputs, d.name ∈ C.2.1 → ∀ v, ρf d.name = some v →
      v.parts = d.parts ∧ v.level = d.level ∧ v.key = d.key ∧ v.scale = d.scale := by
    intro d hd hdn v hv
    have := hmeta d hd hdn
    unfold metaOK at this
    rw [zenv_apply, hv] at this
    simp [zv] at this
    exact ⟨this.1.1.1, this.1.1.2, this.1.2, this.2⟩
  have Sz : Ext (initEnv D.P.src C.1 fun _ => .exact 0) ρ1z := by
    intro y w hy
    obtain ⟨d, hd, rfl⟩ := Option.map_eq_some_iff.mp hy
    obtain ⟨hdn, hdm⟩ := find_name hd
    by_cases hyC : y ∈ C.2.1
    · obtain ⟨e, he, hen, -, -⟩ := entry y hyC
      obtain ⟨-, ⟨v, hv, -⟩, -⟩ := hlink e (hesT e he) (hlinked e he)
      rw [hen] at hv
      obtain ⟨p1, p2, p3, p4⟩ := metaV d hdm (hdn ▸ hyC) v (hdn ▸ hv)
      apply hρ1zx
      rw [zenv_apply, hv]
      simp only [Option.map_some, zv, ← p1, ← p2, ← p3, ← p4]
    · obtain ⟨h1, h2, -⟩ := notG y (constc y d hd hyC)
      rw [foldl_nodst G.body _ ρ1z hρ1z y h2]
      simp only [initEnv, findG' y h1 hyC, hd, Option.map_some]
  have Sm : Ext (initEnv D.P.src C.1 fun x => .exact (fmsg C.2.1 C.2.2 ms x)) ρ1 := by
    intro y w hy
    obtain ⟨d, hd, rfl⟩ := Option.map_eq_some_iff.mp hy
    obtain ⟨hdn, hdm⟩ := find_name hd
    by_cases hyC : y ∈ C.2.1
    · obtain ⟨e, he, hen, hem, -⟩ := entry y hyC
      obtain ⟨-, ⟨v, hv, hvm⟩, -⟩ := hlink e (hesT e he) (hlinked e he)
      rw [hen] at hv
      obtain ⟨p1, p2, p3, p4⟩ := metaV d hdm (hdn ▸ hyC) v (hdn ▸ hv)
      apply hρ1x
      rw [hv]
      congr 1
      cases v
      simp only at hvm p1 p2 p3 p4
      subst hvm p1 p2 p3 p4
      simp only [hem]
    · have hc := constc y d hd hyC
      obtain ⟨h1, h2, h3⟩ := notG y hc
      rw [foldl_nodst G.body _ ρ1 hρ1 y h2]
      simp only [initEnv, findG' y h1 hyC, hd, Option.map_some, fmsg_none h3, fmsg_none hyC,
        hptC y hc]
  have Sc : Ext (Trace.initCt D.Pe C.1 (fcts C.2.1 C.2.2 cs)) σ1 := by
    intro y w hy
    obtain ⟨d, hd, rfl⟩ := Option.map_eq_some_iff.mp hy
    obtain ⟨hdn, hdm⟩ := find_name hd
    by_cases hyC : y ∈ C.2.1
    · obtain ⟨e, he, hen, -, hec⟩ := entry y hyC
      obtain ⟨-, -, hσe⟩ := hlink e (hesT e he) (hlinked e he)
      rw [hen] at hσe
      rw [hec]
      exact hσ1x _ _ hσe
    · have hc := constc y d hd hyC
      obtain ⟨h1, h2, h3⟩ := notG y hc
      rw [irun_nodst stepF hI pk G.body _ _ σ1 hσ1 y h2]
      simp only [Trace.initCt, findG' y h1 hyC, hd, Option.map_some, fcts_none h3, fcts_none hyC,
        hptC y hc]
  -- the inlined program's runs
  obtain ⟨ρ2z, hρ2z, hρ2zx⟩ := foldl_ext C.1.body _ _ ρCz hCfold Sz
  obtain ⟨ρ2, hρ2, hρ2x⟩ := foldl_ext C.1.body _ _ ρCm hCm Sm
  obtain ⟨σ2, hσ2, hσ2x⟩ := irun_ext stepF hI pk C.1.body _ _ _ _ σs hσs Sz Sc
  have hfold2 : (G.extend C).body.foldlM (step D.P.src) (initEnv D.P.src (G.extend C).prog
      fun x => .exact (fmsg G.fresh (G.extend C).pt (fins.map Prod.fst) x)) = some ρ2 := by
    show (G.body ++ C.1.body).foldlM _ _ = _
    rw [List.foldlM_append, hρ1]; exact hρ2
  have hfold2z : (G.body ++ C.1.body).foldlM (step D.P.src)
      (initEnv D.P.src (G.extend C).prog fun _ => .exact 0) = some ρ2z := by
    rw [List.foldlM_append, hρ1z]; exact hρ2z
  have hirun2 : irun D stepF pk (G.extend C).body
      (initEnv D.P.src (G.extend C).prog fun _ => .exact 0)
      (Trace.initCt D.Pe (G.extend C).prog (fcts G.fresh (G.extend C).pt (fencs pk fins))) =
        some σ2 := by
    show irun D stepF pk (G.body ++ C.1.body) _ _ = _
    rw [irun_append stepF pk G.body C.1.body _ _ _ _ hσ1 hρ1z]; exact hσ2
  -- the inlined program's evaluation and certificate
  obtain ⟨ρPz, hPz⟩ := Option.isSome_iff_exists.mp a6
  obtain ⟨hPok, hPfold, -⟩ := eval_parts hPz
  have ePz : ρPz = ρ2z := by
    have : (composite G C).body.foldlM (step D.P.src)
        (initEnv D.P.src (composite G C) fun _ => .exact 0) = some ρ2z := hfold2z
    exact Option.some.inj (hPfold.symm.trans this)
  have hCmout : ∀ o ∈ C.1.outputs, ∃ v, ρCm o = some v := by
    intro o ho
    obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp (hCout o ho)
    rw [← hCmz, zenv_apply] at hw
    obtain ⟨v, hv, -⟩ := Option.map_eq_some_iff.mp hw
    exact ⟨v, hv⟩
  have hPm : Source.eval D.P.src (composite G C)
      (fun x => .exact (fmsg G.fresh (G.extend C).pt (fins.map Prod.fst) x)) = some ρ2 := by
    refine eval_of_parts hPok hfold2 (fun o ho => ?_)
    obtain ⟨v, hv⟩ := hCmout o ho
    rw [hρ2x o v hv]; rfl
  have hCm' : Source.eval D.P.src C.1 (fun x => .exact (fmsg C.2.1 C.2.2 ms x)) = some ρCm := by
    refine eval_of_parts hCok hCm (fun o ho => ?_)
    obtain ⟨v, hv⟩ := hCmout o ho
    rw [hv]; rfl
  have hcor := hC.eval pk sk hk (mk (composite G C) G.fresh (G.extend C).pt) a7 fins hgood
  have hlen' : (fins.map fun p => D.enc pk p.1 p.2).length =
      (D.fresh (mk (composite G C) G.fresh (G.extend C).pt)).length := by
    rw [(hmk _ _ _).2.1]; simp [hlen]
  change (if (fins.map fun p => D.enc pk p.1 p.2).length =
      (D.fresh (mk (composite G C) G.fresh (G.extend C).pt)).length
    then interpEval D stepF pk (mk (composite G C) G.fresh (G.extend C).pt)
      (fins.map fun p => D.enc pk p.1 p.2) else []).map (dec sk) =
    D.sem (mk (composite G C) G.fresh (G.extend C).pt) (fins.map Prod.fst) at hcor
  rw [ite_eq_left_of_eq_true _ _ (eq_true hlen')] at hcor
  -- both evaluations, written out
  have evP : interpEval D stepF pk (mk (composite G C) G.fresh (G.extend C).pt)
      (fins.map fun p => D.enc pk p.1 p.2) =
      C.1.outputs.map fun o => (((ρ2z o).map (·.level)).getD 0, (σ2 o).getD []) := by
    show ((irun D stepF pk (D.prog (mk (composite G C) G.fresh (G.extend C).pt)).body
      (initEnv D.P.src (D.prog (mk (composite G C) G.fresh (G.extend C).pt)) fun _ => .exact 0)
      (Trace.initCt D.Pe (D.prog (mk (composite G C) G.fresh (G.extend C).pt))
        (D.cts (mk (composite G C) G.fresh (G.extend C).pt)
          (fins.map fun p => D.enc pk p.1 p.2)))).map
      fun σ => (D.prog (mk (composite G C) G.fresh (G.extend C).pt)).outputs.map fun o =>
        (D.outLevel (mk (composite G C) G.fresh (G.extend C).pt) o, (σ o).getD [])).getD [] = _
    have hc : D.cts (mk (composite G C) G.fresh (G.extend C).pt)
        (fins.map fun p => D.enc pk p.1 p.2) = fcts G.fresh (G.extend C).pt (fencs pk fins) :=
      funext fun x => cts_mk mk hmk _ _ _ _ x
    rw [hc]
    unfold AbsScheme.outLevel
    rw [(hmk _ _ _).1, hPz]
    have : irun D stepF pk (composite G C).body
        (initEnv D.P.src (composite G C) fun _ => .exact 0)
        (Trace.initCt D.Pe (composite G C) (fcts G.fresh (G.extend C).pt (fencs pk fins))) =
          some σ2 := hirun2
    rw [this, ePz]; rfl
  have evC : interpEval D stepF pk (mk C.1 C.2.1 C.2.2) cs =
      C.1.outputs.map fun o => (((ρCz o).map (·.level)).getD 0, (σs o).getD []) := by
    show ((irun D stepF pk (D.prog (mk C.1 C.2.1 C.2.2)).body
      (initEnv D.P.src (D.prog (mk C.1 C.2.1 C.2.2)) fun _ => .exact 0)
      (Trace.initCt D.Pe (D.prog (mk C.1 C.2.1 C.2.2)) (D.cts (mk C.1 C.2.1 C.2.2) cs))).map
      fun σ => (D.prog (mk C.1 C.2.1 C.2.2)).outputs.map fun o =>
        (D.outLevel (mk C.1 C.2.1 C.2.2) o, (σ o).getD [])).getD [] = _
    have hc : D.cts (mk C.1 C.2.1 C.2.2) cs = fcts C.2.1 C.2.2 cs :=
      funext fun x => cts_mk mk hmk _ _ _ _ x
    rw [hc]
    unfold AbsScheme.outLevel
    rw [(hmk _ _ _).1, hCz, hσs]; rfl
  have outs_eq : interpEval D stepF pk (mk C.1 C.2.1 C.2.2) cs =
      interpEval D stepF pk (mk (composite G C) G.fresh (G.extend C).pt)
        (fins.map fun p => D.enc pk p.1 p.2) := by
    rw [evC, evP]
    apply List.map_congr_left
    intro o ho
    obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp (hCout o ho)
    obtain ⟨ct, hct⟩ := Option.isSome_iff_exists.mp (hσsd o (by rw [hw]; rfl))
    rw [hw, hρ2zx o w hw, hct, hσ2x o ct hct]
  -- what the query computes on the selected messages
  let g : Var → M D := fun o => match ρCm o with
    | some v => (match v.msg with | .exact m => m)
    | none => 0
  have semC : D.sem (mk C.1 C.2.1 C.2.2) ms = C.1.outputs.map g := by
    unfold AbsScheme.sem
    rw [(hmk _ _ _).2.1, ite_eq_left_of_eq_true _ _ (eq_true (by simp [ms, hlenes]))]
    have hm : (fun x => Msg.exact (D.msg (mk C.1 C.2.1 C.2.2) ms x)) =
        fun x => .exact (fmsg C.2.1 C.2.2 ms x) := funext fun x => by rw [msg_mk mk hmk]
    rw [hm, (hmk _ _ _).1, hCm']
    show List.map _ C.1.outputs = _
    apply List.map_congr_left
    intro o _
    simp only [g]
    rcases ρCm o with _ | ⟨⟨m⟩, _, _, _, _⟩ <;> rfl
  have semP : D.sem (mk (composite G C) G.fresh (G.extend C).pt) (fins.map Prod.fst) =
      C.1.outputs.map g := by
    unfold AbsScheme.sem
    rw [(hmk _ _ _).2.1, ite_eq_left_of_eq_true _ _ (eq_true (by simp [hlen]))]
    have hm : (fun x => Msg.exact (D.msg (mk (composite G C) G.fresh (G.extend C).pt)
        (fins.map Prod.fst) x)) =
        fun x => .exact (fmsg G.fresh (G.extend C).pt (fins.map Prod.fst) x) :=
      funext fun x => by rw [msg_mk mk hmk]
    rw [hm, (hmk _ _ _).1, hPm]
    show List.map _ C.1.outputs = _
    apply List.map_congr_left
    intro o ho
    obtain ⟨v, hv⟩ := hCmout o ho
    rw [hρ2x o v hv]
    simp only [g, hv]
  have hpick : pick b (D.sem (mk C.1 C.2.1 C.2.2) (es.map (·.m0)))
      (D.sem (mk C.1 C.2.1 C.2.2) (es.map (·.m1))) = C.1.outputs.map g := by
    rw [← semC]; cases b <;> rfl
  have hdecs : (interpEval D stepF pk (mk C.1 C.2.1 C.2.2) cs).map (dec sk) =
      C.1.outputs.map g := by
    rw [outs_eq, hcor, semP]
  -- the new entries
  subst hout hnew
  refine ⟨fins, hlen, hgood, fun x hx => names_extend (hfr x hx), ρ2, σ2, hfold2, hirun2, ?_, ?_⟩
  · intro e he
    rcases List.mem_append.mp he with he | he
    · exact hdec e he
    · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp he
      obtain ⟨k, h1, -, h3, h4⟩ := zip4_index _ _ _ _ p hp
      have hd := congrArg (·[k]?) hdecs
      simp only [List.getElem?_map] at hd
      have hp' := congrArg (·[k]?) hpick
      cases b
      · simp only [pick, Bool.false_eq_true, ↓reduceIte] at hp' ⊢
        rw [h3, List.getElem?_map] at hp'
        rw [h1, Option.map_some] at hd
        exact Option.some.inj (hd.trans hp'.symm)
      · simp only [pick, ↓reduceIte] at hp' ⊢
        rw [h4, List.getElem?_map] at hp'
        rw [h1, Option.map_some] at hd
        exact Option.some.inj (hd.trans hp'.symm)
  · intro e he hl
    rcases List.mem_append.mp he with he | he
    · obtain ⟨hn, ⟨v, hv, hvm⟩, hσe⟩ := hlink e he hl
      have hnd : e.name ∉ C.1.body.map Trace.dst := fun h =>
        hnew_names _ (List.mem_append_right _ h) hn
      refine ⟨names_extend hn, ⟨v, ?_, hvm⟩, ?_⟩
      · rw [foldl_nodst C.1.body ρ1 ρ2 hρ2 _ hnd]; exact hρ1x _ _ hv
      · rw [irun_nodst stepF hI pk C.1.body ρ1z σ1 σ2 hσ2 _ hnd]; exact hσ1x _ _ hσe
    · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp he
      obtain ⟨k, h1, h2, h3, h4⟩ := zip4_index _ _ _ _ p hp
      have ho : p.2.1 ∈ C.1.outputs := List.mem_of_getElem? h2
      obtain ⟨v, hv⟩ := hCmout p.2.1 ho
      refine ⟨?_, ⟨v, hρ2x _ _ hv, ?_⟩, ?_⟩
      · -- the output is a name of the new global program
        rcases foldl_dom C.1.body _ ρCz hCfold p.2.1 (hCout p.2.1 ho) with hi | hi
        · obtain ⟨d, hdm, hdn⟩ : ∃ x ∈ C.1.inputs, x.name = p.2.1 := by
            simpa [initEnv] using hi
          by_cases hyC : p.2.1 ∈ C.2.1
          · obtain ⟨e, he, hen, -, -⟩ := entry _ hyC
            rw [← hen]; exact names_extend (hlink e (hesT e he) (hlinked e he)).1
          · unfold Global.names; simp only [Global.extend, List.map_append, List.mem_append]
            left; right
            exact List.mem_map.mpr ⟨d, List.mem_filter.mpr ⟨hdm, by simpa [hdn] using hyC⟩, hdn⟩
        · unfold Global.names; simp only [Global.extend, List.map_append, List.mem_append]
          right; right; exact hi
      · have hp' := congrArg (·[k]?) hpick
        simp only [List.getElem?_map, h2, Option.map_some] at hp'
        have hgv : g p.2.1 = (match v.msg with | .exact m => m) := by
          show (match ρCm p.2.1 with
            | some v => (match v.msg with | .exact m => m)
            | none => 0) = _
          rw [hv]
        rcases hvm : v.msg with ⟨m⟩
        rw [hvm] at hgv
        cases b
        · simp only [pick, Bool.false_eq_true, ↓reduceIte] at hp' ⊢; rw [h3] at hp'; rw [Option.some.inj hp', hgv]
        · simp only [pick, ↓reduceIte] at hp' ⊢; rw [h4] at hp'; rw [Option.some.inj hp', hgv]
      · rw [evC] at h1
        simp only [List.getElem?_map, h2, Option.map_some, Option.some.injEq] at h1
        obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp (hCout _ ho)
        obtain ⟨ct, hct⟩ := Option.isSome_iff_exists.mp (hσsd _ (by rw [hw]; rfl))
        rw [← h1, hct]
        exact hσ2x _ _ hct

end Game

section Sim
variable {D : AbsScheme} {mk : Program → List Var → (Var → M D) → D.Circ}
  {adm : D.Circ → Bool} {dec : D.SK → CT D → M D} {stepF : StepFn D} {b : Bool} {pk : D.PK}
  {sk : D.SK} [DecidableEq (M D)]

theorem decAns_eqLM {T : List (LEntry D)} {G : Global D} (hT : Inv dec stepF b pk sk T G)
    (j : ℕ) : decAnsLM dec sk T j = simAnsLM T j := by
  obtain ⟨-, -, -, -, -, -, -, -, hdec, -⟩ := hT
  unfold decAnsLM simAnsLM
  rcases he : T[j]? with _ | e
  · rfl
  · show (if e.m0 = e.m1 then some (dec sk e.c) else none) =
      (if e.m0 = e.m1 then some e.m0 else none)
    split_ifs with h
    · rw [hdec e (List.mem_of_getElem? he), h]; cases b <;> rfl
    · rfl

theorem simLM (hmk : ∀ p f c, D.prog (mk p f c) = p ∧ D.fresh (mk p f c) = f ∧ D.pt (mk p f c) = c)
    (hI : InterpOK D stepF) (hC : Correct (freshScheme D adm (interpEval D stepF) dec))
    (tape : ℕ → D.ER) (hk : D.KeysOK pk sk) :
    ∀ (A : LAdv D Bool) (n : ℕ) (T : List (LEntry D)) (G : Global D),
      Inv dec stepF b pk sk T G → TapeOKLM pk sk tape A n →
      gameLM mk adm (interpEval D stepF) dec b pk sk tape A n T G =
        gameCPA (S := freshScheme D adm (interpEval D stepF) dec) b pk tape
          (reduceLM mk adm (interpEval D stepF) dec pk A T G) n
  | .ret a, n, T, G, _, _ => rfl
  | .enc m0 m1 x k, n, T, G, hT, ht => by
    simp only [gameLM, reduceLM, gameCPA]
    exact simLM hmk hI hC tape hk (k _) (n + 1) _ _
      (inv_enc hI hC hk hT m0 m1 x (tape n) ht.1) (ht.2 _)
  | .eval C idx k, n, T, G, hT, ht => by
    simp only [gameLM, reduceLM]
    cases h : evalLM mk adm (interpEval D stepF) pk T G C idx with
    | none => exact simLM hmk hI hC tape hk (k none) n T G hT (ht _)
    | some r =>
      obtain ⟨outs, new, G'⟩ := r
      exact simLM hmk hI hC tape hk (k (some outs)) n _ _ (inv_eval hmk hI hC hk hT C idx h) (ht _)
  | .dec j k, n, T, G, hT, ht => by
    simp only [gameLM, reduceLM]
    rw [decAns_eqLM hT j]
    exact simLM hmk hI hC tape hk (k _) n T G hT (ht _)

end Sim

theorem tapeOKLM_all {D : AbsScheme} {pk : D.PK} {sk : D.SK} {tape : ℕ → D.ER}
    (h : ∀ i, D.GoodE pk sk (tape i)) : ∀ (A : LAdv D Bool) n, TapeOKLM pk sk tape A n := by
  intro A
  induction A with
  | ret a => intro n; trivial
  | enc m0 m1 x k ih => intro n; exact ⟨h n, fun c => ih c (n + 1)⟩
  | eval C idx k ih => intro n r; exact ih r n
  | dec j k ih => intro n r; exact ih r n

theorem tapeOKLM_of_bounded {D : AbsScheme} {pk : D.PK} {sk : D.SK} {tape : ℕ → D.ER} :
    ∀ {A : LAdv D Bool} {q : ℕ}, BoundedLM A q → ∀ n, (∀ i, n ≤ i → i < n + q →
      D.GoodE pk sk (tape i)) → TapeOKLM pk sk tape A n := by
  intro A q hb
  induction hb with
  | ret a q => intro n _; trivial
  | enc m0 m1 x k q _ ih =>
    intro n hg
    exact ⟨hg n le_rfl (by omega), fun c => ih c (n + 1) fun i h1 h2 => hg i (by omega) (by omega)⟩
  | eval C idx k q _ ih => intro n hg r; exact ih r n hg
  | dec j k q _ ih => intro n hg r; exact ih r n hg

/-! ## The locked statements -/

theorem gameLM_eq_gameCPA (D : AbsScheme)
    (mk : Program → List Var → (Var → M D) → D.Circ)
    (hmk : ∀ p f c, D.prog (mk p f c) = p ∧ D.fresh (mk p f c) = f ∧ D.pt (mk p f c) = c)
    (adm : D.Circ → Bool) (dec : D.SK → CT D → M D) (stepF : StepFn D) (hI : InterpOK D stepF)
    [DecidableEq (M D)] (hC : Correct (freshScheme D adm (interpEval D stepF) dec)) (b : Bool)
    (pk : D.PK) (sk : D.SK) (tape : ℕ → D.ER) (hk : D.KeysOK pk sk) (A : LAdv D Bool)
    (ht : TapeOKLM pk sk tape A 0) :
    gameLM mk adm (interpEval D stepF) dec b pk sk tape A 0 [] (Global.empty D) =
      gameCPA (S := freshScheme D adm (interpEval D stepF) dec) b pk tape
        (reduceLM mk adm (interpEval D stepF) dec pk A [] (Global.empty D)) 0 :=
  simLM hmk hI hC tape hk A 0 [] _ (inv_empty dec stepF b pk sk) ht

theorem probLM_eq (D : AbsScheme)
    (mk : Program → List Var → (Var → M D) → D.Circ)
    (hmk : ∀ p f c, D.prog (mk p f c) = p ∧ D.fresh (mk p f c) = f ∧ D.pt (mk p f c) = c)
    (adm : D.Circ → Bool) (dec : D.SK → CT D → M D) (stepF : StepFn D) (hI : InterpOK D stepF)
    [DecidableEq (M D)] (hC : Correct (freshScheme D adm (interpEval D stepF) dec))
    {Ω Coins : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    (pk : Ω → D.PK) (sk : Ω → D.SK) (tape : Ω → ℕ → D.ER) (coins : Ω → Coins)
    (A : Coins → D.PK → LAdv D Bool) (b : Bool)
    (hgood : ∀ᵐ ω ∂μ, D.KeysOK (pk ω) (sk ω) ∧ ∀ i, D.GoodE (pk ω) (sk ω) (tape ω i)) :
    μ {ω | gameLM mk adm (interpEval D stepF) dec b (pk ω) (sk ω) (tape ω) (A (coins ω) (pk ω))
        0 [] (Global.empty D) = true} =
      μ {ω | gameCPA (S := freshScheme D adm (interpEval D stepF) dec) b (pk ω) (tape ω)
        (reductionLM mk adm (interpEval D stepF) dec A (coins ω) (pk ω)) 0 = true} := by
  apply measure_congr
  rw [Filter.eventuallyEqSet_iff]
  filter_upwards [hgood] with ω hω
  rw [gameLM_eq_gameCPA D mk hmk adm dec stepF hI hC b (pk ω) (sk ω) (tape ω) hω.1 _
    (tapeOKLM_all hω.2 _ 0)]
  rfl

theorem probLM_le (D : AbsScheme)
    (mk : Program → List Var → (Var → M D) → D.Circ)
    (hmk : ∀ p f c, D.prog (mk p f c) = p ∧ D.fresh (mk p f c) = f ∧ D.pt (mk p f c) = c)
    (adm : D.Circ → Bool) (dec : D.SK → CT D → M D) (stepF : StepFn D) (hI : InterpOK D stepF)
    [DecidableEq (M D)] (hC : Correct (freshScheme D adm (interpEval D stepF) dec))
    {Ω Coins : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    (pk : Ω → D.PK) (sk : Ω → D.SK) (tape : Ω → ℕ → D.ER) (coins : Ω → Coins)
    (A : Coins → D.PK → LAdv D Bool) (b : Bool) (q : ℕ) (hq : ∀ r p, BoundedLM (A r p) q) :
    μ {ω | gameLM mk adm (interpEval D stepF) dec b (pk ω) (sk ω) (tape ω) (A (coins ω) (pk ω))
        0 [] (Global.empty D) = true} ≤
        μ {ω | gameCPA (S := freshScheme D adm (interpEval D stepF) dec) b (pk ω) (tape ω)
          (reductionLM mk adm (interpEval D stepF) dec A (coins ω) (pk ω)) 0 = true} +
          μ {ω | ¬ (D.KeysOK (pk ω) (sk ω) ∧ ∀ i < q, D.GoodE (pk ω) (sk ω) (tape ω i))} ∧
      μ {ω | gameCPA (S := freshScheme D adm (interpEval D stepF) dec) b (pk ω) (tape ω)
          (reductionLM mk adm (interpEval D stepF) dec A (coins ω) (pk ω)) 0 = true} ≤
        μ {ω | gameLM mk adm (interpEval D stepF) dec b (pk ω) (sk ω) (tape ω) (A (coins ω) (pk ω))
          0 [] (Global.empty D) = true} +
          μ {ω | ¬ (D.KeysOK (pk ω) (sk ω) ∧ ∀ i < q, D.GoodE (pk ω) (sk ω) (tape ω i))} := by
  have agree : ∀ ω, (D.KeysOK (pk ω) (sk ω) ∧ ∀ i < q, D.GoodE (pk ω) (sk ω) (tape ω i)) →
      gameLM mk adm (interpEval D stepF) dec b (pk ω) (sk ω) (tape ω) (A (coins ω) (pk ω))
        0 [] (Global.empty D) =
      gameCPA (S := freshScheme D adm (interpEval D stepF) dec) b (pk ω) (tape ω)
        (reductionLM mk adm (interpEval D stepF) dec A (coins ω) (pk ω)) 0 := fun ω hg =>
    gameLM_eq_gameCPA D mk hmk adm dec stepF hI hC b _ _ _ hg.1 _
      (tapeOKLM_of_bounded (hq _ _) 0 fun i _ hi => hg.2 i (by omega))
  constructor
  · refine le_trans (measure_mono ?_) (measure_union_le _ _)
    intro ω hω
    by_cases hg : D.KeysOK (pk ω) (sk ω) ∧ ∀ i < q, D.GoodE (pk ω) (sk ω) (tape ω i)
    · left
      simp only [Set.mem_ofPred_eq] at hω ⊢
      rw [← agree ω hg]; exact hω
    · right; exact hg
  · refine le_trans (measure_mono ?_) (measure_union_le _ _)
    intro ω hω
    by_cases hg : D.KeysOK (pk ω) (sk ω) ∧ ∀ i < q, D.GoodE (pk ω) (sk ω) (tape ω i)
    · left
      simp only [Set.mem_ofPred_eq] at hω ⊢
      rw [agree ω hg]; exact hω
    · right; exact hg

theorem advLM_le (D : AbsScheme)
    (mk : Program → List Var → (Var → M D) → D.Circ)
    (hmk : ∀ p f c, D.prog (mk p f c) = p ∧ D.fresh (mk p f c) = f ∧ D.pt (mk p f c) = c)
    (adm : D.Circ → Bool) (dec : D.SK → CT D → M D) (stepF : StepFn D) (hI : InterpOK D stepF)
    [DecidableEq (M D)] (hC : Correct (freshScheme D adm (interpEval D stepF) dec))
    {Ω Coins : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (pk : Ω → D.PK) (sk : Ω → D.SK) (tape : Ω → ℕ → D.ER) (coins : Ω → Coins)
    (A : Coins → D.PK → LAdv D Bool) (q : ℕ) (hq : ∀ r p, BoundedLM (A r p) q) :
    |(μ {ω | gameLM mk adm (interpEval D stepF) dec true (pk ω) (sk ω) (tape ω)
          (A (coins ω) (pk ω)) 0 [] (Global.empty D) = true}).toReal -
        (μ {ω | gameLM mk adm (interpEval D stepF) dec false (pk ω) (sk ω) (tape ω)
          (A (coins ω) (pk ω)) 0 [] (Global.empty D) = true}).toReal| ≤
      |(μ {ω | gameCPA (S := freshScheme D adm (interpEval D stepF) dec) true (pk ω) (tape ω)
          (reductionLM mk adm (interpEval D stepF) dec A (coins ω) (pk ω)) 0 = true}).toReal -
        (μ {ω | gameCPA (S := freshScheme D adm (interpEval D stepF) dec) false (pk ω) (tape ω)
          (reductionLM mk adm (interpEval D stepF) dec A (coins ω) (pk ω)) 0 = true}).toReal| +
      2 * (μ {ω | ¬ (D.KeysOK (pk ω) (sk ω) ∧ ∀ i < q, D.GoodE (pk ω) (sk ω) (tape ω i))}).toReal := by
  obtain ⟨h1, h1'⟩ := probLM_le D mk hmk adm dec stepF hI hC μ pk sk tape coins A true q hq
  obtain ⟨h0, h0'⟩ := probLM_le D mk hmk adm dec stepF hI hC μ pk sk tape coins A false q hq
  have r1 := Validation.IndCpaDProfile.toReal_le_add μ _ _ _ h1
  have r1' := Validation.IndCpaDProfile.toReal_le_add μ _ _ _ h1'
  have r0 := Validation.IndCpaDProfile.toReal_le_add μ _ _ _ h0
  have r0' := Validation.IndCpaDProfile.toReal_le_add μ _ _ _ h0'
  set x1 := (μ {ω | gameCPA (S := freshScheme D adm (interpEval D stepF) dec) true (pk ω) (tape ω)
          (reductionLM mk adm (interpEval D stepF) dec A (coins ω) (pk ω)) 0 = true}).toReal
  set x0 := (μ {ω | gameCPA (S := freshScheme D adm (interpEval D stepF) dec) false (pk ω) (tape ω)
          (reductionLM mk adm (interpEval D stepF) dec A (coins ω) (pk ω)) 0 = true}).toReal
  rw [abs_le]
  constructor <;> linarith [le_abs_self (x1 - x0), neg_abs_le (x1 - x0)]

example := (@gameLM_eq_gameCPA : type_of% @Challenge.IndCpaDLM.gameLM_eq_gameCPA)
example := (@probLM_eq : type_of% @Challenge.IndCpaDLM.probLM_eq)
example := (@probLM_le : type_of% @Challenge.IndCpaDLM.probLM_le)
example := (@advLM_le : type_of% @Challenge.IndCpaDLM.advLM_le)

end Validation.IndCpaDLM
