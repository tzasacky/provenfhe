import Validation.IndCpaD.RenameQuery
import Challenge.IndCpaD.LMEmbed

/-!
# Validation.IndCpaD.LMEmbed — a regular fresh-only adversary has a counterpart in the game with evaluation on earlier results

The counterpart `tr A` of a fresh-only adversary `A` keeps, per table index, `some n` for the
`n`-th encryption and `none` for a derived entry, the encryption counter and the query counter.
It names the `n`-th encryption `ename n`; it answers itself an evaluation query the fresh-only
oracle refuses (class refuses, or an index is not a fresh entry: `none`) or answers with no
output (wrong arity: `some []`); it forwards every other evaluation query on the same indices as
`renQ` (fresh inputs renamed to the selected entries' names, every other name `x` to `tname k x`);
it forwards decryption queries unchanged.

`sim`: the two games return the same result, by induction on the adversary with the invariant
`Inv` (the fresh-only table is the view of the table of `gameLM`; fresh entries are linked under
their `ename`, which is a fresh input of the global program; distinct fresh entries have distinct
names; every name of the global program is an `ename` of an earlier encryption or a `tname` of an
earlier query; the global program is reachable). The forwarded query is accepted by the agreement
statements (`admLM_fresh_*`) applied to the renamed query, which the class accepts by the
renaming lemmas; its outputs and messages are those of the original query (`interpEval_ren`,
`sem_ren`).
-/

namespace Validation.IndCpaDEmbed
open Spec NPoly Scheme Source Spec.IndCpaD Spec.IndCpaDProfile Spec.IndCpaDLM
open Validation.IndCpaDRen

variable {D : AbsScheme}

/-! ## Lists -/

theorem mapM_cons' {α β : Type} (f : α → Option β) (a : α) (l : List α) :
    (a :: l).mapM f = (f a).bind fun b => (l.mapM f).map (b :: ·) := by
  simp only [List.mapM_cons, Option.bind_eq_bind, Option.pure_def]
  cases f a <;> simp
  cases l.mapM f <;> rfl

theorem mapM_forall₂ {α β : Type} {f : α → Option β} :
    ∀ {l : List α} {bs : List β}, l.mapM f = some bs → List.Forall₂ (fun a b => f a = some b) l bs
  | [], bs, h => by
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h; subst h
    exact List.Forall₂.nil
  | a :: l, bs, h => by
    rw [mapM_cons'] at h
    obtain ⟨b, hb, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨bs', hbs, rfl⟩ := Option.map_eq_some_iff.mp h
    exact List.Forall₂.cons hb (mapM_forall₂ hbs)

theorem mapM_of_forall₂ {α β γ : Type} {f : α → Option β} {g : γ → β} :
    ∀ {l : List α} {cs : List γ}, List.Forall₂ (fun a c => f a = some (g c)) l cs →
      l.mapM f = some (cs.map g)
  | _, _, List.Forall₂.nil => rfl
  | _, _, List.Forall₂.cons h hs => by
    rw [mapM_cons', h, mapM_of_forall₂ hs]; rfl

theorem mapM_none {α β : Type} {f : α → Option β} :
    ∀ {l : List α} {a : α}, a ∈ l → f a = none → l.mapM f = none
  | [], _, ha, _ => by simp at ha
  | b :: l, a, ha, h => by
    rw [mapM_cons']
    rcases List.mem_cons.mp ha with rfl | ha
    · rw [h]; rfl
    · rw [mapM_none ha h]; cases f b <;> rfl

theorem mapM_none_mem {α β : Type} {f : α → Option β} :
    ∀ {l : List α}, l.mapM f = none → ∃ a ∈ l, f a = none
  | [], h => by simp at h
  | b :: l, h => by
    rw [mapM_cons'] at h
    rcases hb : f b with _ | x
    · exact ⟨b, List.mem_cons_self, hb⟩
    · rw [hb] at h
      rcases hl : l.mapM f with _ | xs
      · obtain ⟨a, ha, h'⟩ := mapM_none_mem hl
        exact ⟨a, List.mem_cons_of_mem _ ha, h'⟩
      · rw [hl] at h; cases h

theorem forall₂_split {α β γ : Type} {R : α → β → Prop} {S : α → γ → Prop} {T : β → γ → Prop}
    (h : ∀ a b, R a b → ∃ c, S a c ∧ T b c) :
    ∀ {l : List α} {bs : List β}, List.Forall₂ R l bs →
      ∃ cs, List.Forall₂ S l cs ∧ List.Forall₂ T bs cs
  | _, _, List.Forall₂.nil => ⟨[], List.Forall₂.nil, List.Forall₂.nil⟩
  | _, _, List.Forall₂.cons hxy hs => by
    obtain ⟨c, h1, h2⟩ := h _ _ hxy
    obtain ⟨cs, h3, h4⟩ := forall₂_split h hs
    exact ⟨c :: cs, List.Forall₂.cons h1 h3, List.Forall₂.cons h2 h4⟩

theorem forall₂_map_eq {α β δ : Type} {f : α → δ} {g : β → δ} :
    ∀ {l : List α} {bs : List β}, List.Forall₂ (fun a b => f a = g b) l bs → l.map f = bs.map g
  | _, _, List.Forall₂.nil => rfl
  | _, _, List.Forall₂.cons h hs => by
    simp only [List.map_cons, h, forall₂_map_eq hs]

theorem forall₂_mem_right {α β : Type} {R : α → β → Prop} :
    ∀ {l : List α} {bs : List β}, List.Forall₂ R l bs → ∀ b ∈ bs, ∃ a ∈ l, R a b
  | _, _, List.Forall₂.nil, _, hb => by simp at hb
  | _, _, @List.Forall₂.cons _ _ _ x y l bs hxy hs, b, hb => by
    rcases List.mem_cons.mp hb with rfl | hb
    · exact ⟨x, List.mem_cons_self, hxy⟩
    · obtain ⟨a, ha, h⟩ := forall₂_mem_right hs b hb
      exact ⟨a, List.mem_cons_of_mem _ ha, h⟩

theorem forall₂_nodup {α β : Type} {R : α → β → Prop}
    (hinj : ∀ a a' b, R a b → R a' b → a = a') :
    ∀ {l : List α} {bs : List β}, List.Forall₂ R l bs → l.Nodup → bs.Nodup
  | _, _, List.Forall₂.nil, _ => List.nodup_nil
  | _, _, @List.Forall₂.cons _ _ _ x y l bs hxy hs, hl => by
    obtain ⟨hx, hl⟩ := List.nodup_cons.mp hl
    refine List.nodup_cons.mpr ⟨fun hy => ?_, forall₂_nodup hinj hs hl⟩
    obtain ⟨a, ha, h⟩ := forall₂_mem_right hs y hy
    exact hx (hinj x a y hxy h ▸ ha)

theorem getElem?_append_one {α : Type} (l : List α) (a : α) (j : ℕ) :
    (l ++ [a])[j]? = if j < l.length then l[j]? else if j = l.length then some a else none := by
  split_ifs with h1 h2
  · exact List.getElem?_append_left h1
  · subst h2; simp
  · rw [List.getElem?_append_right (by omega)]
    have : j - l.length ≠ 0 := by omega
    obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero this
    rw [hm]; rfl

/-! ## The view of the table of `gameLM` -/

variable (adm : D.Circ → Bool) (ev : D.PK → D.Circ → List (CT D) → List (CT D))
  (dec : D.SK → CT D → M D)

/-- The fresh-only table that the table of `gameLM` and the translator's flags stand for. -/
def view (TL : List (LEntry D)) (L : List (Option ℕ)) : List (Entry (freshScheme D adm ev dec)) :=
  (TL.zip L).map fun p => ⟨p.1.m0, p.1.m1, p.1.c, p.2.isSome⟩

variable {adm ev dec}

theorem view_append {TL TL' : List (LEntry D)} {L L' : List (Option ℕ)}
    (h : TL.length = L.length) :
    view adm ev dec (TL ++ TL') (L ++ L') = view adm ev dec TL L ++ view adm ev dec TL' L' := by
  unfold view; rw [List.zip_append h, List.map_append]

theorem view_get : ∀ {TL : List (LEntry D)} {L : List (Option ℕ)}, TL.length = L.length →
    ∀ j : ℕ, (view adm ev dec TL L)[j]? =
      (TL[j]?).bind fun e => (L[j]?).map fun o =>
        (⟨e.m0, e.m1, e.c, o.isSome⟩ : Entry (freshScheme D adm ev dec))
  | [], [], _, j => by simp [view]
  | [], _ :: _, h, _ => by simp at h
  | _ :: _, [], h, _ => by simp at h
  | e :: TL, o :: L, h, 0 => rfl
  | e :: TL, o :: L, h, j + 1 => by
    have := view_get (TL := TL) (L := L) (by simpa using h) j
    simp only [view, List.zip_cons_cons, List.map_cons, List.getElem?_cons_succ] at this ⊢
    exact this

theorem freshAt_view_none {TL : List (LEntry D)} {L : List (Option ℕ)} (h : TL.length = L.length)
    {j : ℕ} (hj : (L[j]?).join = none) : freshAt (view adm ev dec TL L) j = none := by
  unfold freshAt
  rw [view_get h]
  rcases he : TL[j]? with _ | e
  · rfl
  · rcases hl : L[j]? with _ | o
    · rfl
    · rw [hl] at hj
      simp only [Option.join_some] at hj
      subst hj
      rfl

theorem freshAt_view_some {TL : List (LEntry D)} {L : List (Option ℕ)} (h : TL.length = L.length)
    {j n' : ℕ} {e : LEntry D} (hj : L[j]? = some (some n')) (he : TL[j]? = some e) :
    freshAt (view adm ev dec TL L) j = some ⟨e.m0, e.m1, e.c, true⟩ := by
  unfold freshAt
  rw [view_get h, he, hj]
  rfl

theorem decAns_view [DecidableEq (M D)] {TL : List (LEntry D)} {L : List (Option ℕ)}
    (h : TL.length = L.length) (sk : D.SK) (j : ℕ) :
    decAns (S := freshScheme D adm ev dec) sk (view adm ev dec TL L) j = decAnsLM dec sk TL j := by
  unfold decAns decAnsLM
  rw [view_get h]
  rcases he : TL[j]? with _ | e
  · rfl
  · have hj : j < L.length := by
      rw [← h]; exact (List.getElem?_eq_some_iff.mp he).1
    rw [List.getElem?_eq_getElem hj]
    rfl

/-! ## Lengths of what the evaluator and the semantics return -/

theorem interpEval_eq (stepF : Challenge.IndCpaDLM.StepFn D) (pk : D.PK) (C : D.Circ)
    (cs : List (CT D)) : Challenge.IndCpaDLM.interpEval D stepF pk C cs =
      ((Challenge.IndCpaDLM.irun D stepF pk (D.prog C).body
          (initEnv D.P.src (D.prog C) fun _ => .exact 0)
          (Trace.initCt D.Pe (D.prog C) (D.cts C cs))).map
        fun σ => (D.prog C).outputs.map fun o => (D.outLevel C o, (σ o).getD [])).getD [] := rfl

theorem interpEval_len (stepF : Challenge.IndCpaDLM.StepFn D) (pk : D.PK) (C : D.Circ)
    (cs : List (CT D)) :
    (Challenge.IndCpaDLM.interpEval D stepF pk C cs).length ≤ (D.prog C).outputs.length := by
  rw [interpEval_eq]
  generalize Challenge.IndCpaDLM.irun D stepF pk _ _ _ = o
  cases o <;> simp

theorem sem_len {C : D.Circ} (hz : (Source.eval D.P.src (D.prog C) fun _ => .exact 0).isSome)
    (ms : List (M D)) (hl : ms.length = (D.fresh C).length) :
    (D.sem C ms).length = (D.prog C).outputs.length := by
  obtain ⟨ρz, hρz⟩ := Option.isSome_iff_exists.mp hz
  obtain ⟨hok, hf, hout⟩ := Validation.IndCpaDLM.eval_parts hρz
  obtain ⟨ρm, hfm, hz'⟩ := Validation.IndCpaDLM.foldl_of_zero (D.prog C)
    (fun x => .exact (D.msg C ms x)) ρz hf
  have hem : Source.eval D.P.src (D.prog C) (fun x => .exact (D.msg C ms x)) = some ρm := by
    refine Validation.IndCpaDLM.eval_of_parts hok hfm fun o ho => ?_
    have := hout o ho
    rw [← hz', Validation.IndCpaDLM.zenv_apply] at this
    simpa using this
  unfold AbsScheme.sem
  rw [ite_eq_left_of_eq_true _ _ (eq_true hl), hem]
  simp

/-! ## The appended entries -/

theorem zip_len {α β γ δ ε : Type} (f : α × β × γ × δ → ε) :
    ∀ (outs : List α) (os : List β) (s0 : List γ) (s1 : List δ), outs.length ≤ os.length →
      outs.length ≤ s0.length → outs.length ≤ s1.length →
      ((outs.zip (os.zip (s0.zip s1))).map f).length = outs.length
  | [], _, _, _, _, _, _ => rfl
  | _ :: _, [], _, _, h, _, _ => by simp at h
  | _ :: _, _ :: _, [], _, _, h, _ => by simp at h
  | _ :: _, _ :: _, _ :: _, [], _, _, h => by simp at h
  | _ :: outs, _ :: os, _ :: s0, _ :: s1, h1, h2, h3 => by
    simp only [List.zip_cons_cons, List.map_cons, List.length_cons] at h1 h2 h3 ⊢
    rw [zip_len f outs os s0 s1 (by omega) (by omega) (by omega)]

theorem zip_view : ∀ (outs : List (CT D)) (os : List Var) (s0 s1 : List (M D)),
    outs.length ≤ os.length → outs.length ≤ s0.length → outs.length ≤ s1.length →
    view adm ev dec ((outs.zip (os.zip (s0.zip s1))).map
        fun p => (⟨p.2.2.1, p.2.2.2, p.1, p.2.1, true⟩ : LEntry D)) (outs.map fun _ => none) =
      (outs.zip (s0.zip s1)).map fun p => ⟨p.2.1, p.2.2, p.1, false⟩
  | [], _, _, _, _, _, _ => rfl
  | _ :: _, [], _, _, h, _, _ => by simp at h
  | _ :: _, _ :: _, [], _, _, h, _ => by simp at h
  | _ :: _, _ :: _, _ :: _, [], _, _, h => by simp at h
  | c :: outs, o :: os, a :: s0, b :: s1, h1, h2, h3 => by
    simp only [List.length_cons] at h1 h2 h3
    have := zip_view outs os s0 s1 (by omega) (by omega) (by omega)
    simp only [view, List.zip_cons_cons, List.map_cons] at this ⊢
    rw [this]; rfl

/-! ## Names -/

theorem names_def (G : Global D) : G.names = G.inputs.map (·.name) ++ G.body.map Trace.dst := rfl

theorem constNames_def (C : QCirc D) :
    constNames C = (C.1.inputs.map (·.name)).filter (· ∉ C.2.1) := rfl

theorem mem_link {G : Global D} {x y : Var} (h : x ∈ (G.link y).names) : x ∈ G.names ∨ x = y := by
  unfold Global.link at h
  split_ifs at h
  · exact Or.inl h
  · simp only [names_def, List.map_append, List.map_cons, List.map_nil, List.mem_append,
      List.mem_singleton] at h ⊢
    unfold freshDecl at h
    tauto

theorem mem_extend {G : Global D} {C : QCirc D} {x : Var} (h : x ∈ (G.extend C).names) :
    x ∈ G.names ∨ x ∈ constNames C ∨ x ∈ C.1.body.map Trace.dst := by
  simp only [names_def, Global.extend, List.map_append, List.mem_append, constNames_def,
    List.mem_filter, List.mem_map, decide_eq_true_eq] at h ⊢
  rcases h with (h | ⟨d, hd, rfl⟩) | h | h
  · exact Or.inl (Or.inl h)
  · obtain ⟨hd, hn⟩ := hd
    exact Or.inr (Or.inl ⟨⟨d, hd, rfl⟩, hn⟩)
  · exact Or.inl (Or.inr h)
  · exact Or.inr (Or.inr h)


/-! ## Renamed queries -/

theorem rmap_cases {C : D.Circ} {names : List Var} {q : ℕ} (h : NamesOK D C names) (x : Var) :
    (x ∈ D.fresh C ∧ rmap D C names q x ∈ names) ∨
      (x ∉ D.fresh C ∧ rmap D C names q x = tname q x) := by
  rcases hx : (D.fresh C).idxOf? x with _ | p
  · exact Or.inr ⟨List.idxOf?_eq_none_iff.mp hx, rmap_none hx⟩
  · obtain ⟨hp, e1, e2⟩ := rmap_some (k := q) h hx
    refine Or.inl ⟨e2 ▸ List.getElem_mem _, e1 ▸ List.getElem_mem _⟩

theorem tname_not_mem {C : D.Circ} {names : List Var} (h : NamesOK D C names) (q : ℕ) (y : Var) :
    tname q y ∉ names := fun hy => by
  obtain ⟨n, hn⟩ := h.ent _ hy
  exact ename_ne_tname n q y hn.symm

theorem fit_fresh {C : D.Circ} (hfit : D.inputsFit C = true) {d : Decl}
    (hd : d ∈ (D.prog C).inputs) (hf : d.name ∈ D.fresh C) :
    d.parts = 2 ∧ d.key = 1 ∧ d.level = D.lvl ∧ (D.prog C).boundOf d.name = none := by
  rw [Validation.IndCpaDLM.inputsFit_eq] at hfit
  have := List.all_eq_true.mp hfit d hd
  unfold Validation.IndCpaDLM.qFit at this
  simp only [decide_eq_true hf, ↓reduceIte, Bool.and_eq_true, beq_iff_eq,
    Option.isNone_iff_eq_none] at this
  exact ⟨this.1.1.1, this.1.1.2, this.1.2, this.2⟩

/-- Every name the renamed query introduces (constants and destinations) is a `tname q _`. -/
theorem new_tname {C : D.Circ} {names : List Var} {q : ℕ} (h : NamesOK D C names)
    (hdst : ∀ i ∈ (D.prog C).body, Trace.dst i ∉ D.fresh C) :
    ∀ x ∈ constNames (renQ D C names q) ++ (renQ D C names q).1.body.map Trace.dst,
      ∃ y, x = tname q y := by
  intro x hx
  rcases List.mem_append.mp hx with hx | hx
  · obtain ⟨hx, hxn⟩ := List.mem_filter.mp hx
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hx
    obtain ⟨d0, -, rfl⟩ := List.mem_map.mp hd
    simp only [decide_eq_true_eq] at hxn
    rcases rmap_cases (q := q) h d0.name with ⟨-, h2⟩ | ⟨-, h2⟩
    · exact absurd h2 hxn
    · exact ⟨d0.name, h2⟩
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
    obtain ⟨i0, hi0, rfl⟩ := List.mem_map.mp hi
    rw [dst_renI]
    rcases rmap_cases (q := q) h (Trace.dst i0) with ⟨h1, -⟩ | ⟨-, h2⟩
    · exact absurd h1 (hdst i0 hi0)
    · exact ⟨_, h2⟩

theorem decl_fresh {C : D.Circ} {names : List Var} {q : ℕ} (h : NamesOK D C names)
    (hfit : D.inputsFit C = true)
    (hsc : ∀ d ∈ (D.prog C).inputs, d.name ∈ D.fresh C → d.scale = 0) :
    ∀ d ∈ (renQ D C names q).1.inputs, d.name ∈ (renQ D C names q).2.1 →
      d = freshDecl D d.name := by
  intro d hd hn
  obtain ⟨d0, hd0, rfl⟩ := List.mem_map.mp hd
  rcases rmap_cases (q := q) h d0.name with ⟨h1, -⟩ | ⟨-, h2⟩
  · obtain ⟨hp, hk, hlv, -⟩ := fit_fresh hfit hd0 h1
    have hs := hsc d0 hd0 h1
    obtain ⟨nm, pa, lv, sc, ky⟩ := d0
    simp only at hp hk hlv hs
    subst hp hk hlv hs
    rfl
  · exact absurd (h2 ▸ hn) (tname_not_mem h q d0.name)

theorem bnd_fresh {C : D.Circ} {names : List Var} {q : ℕ} (h : NamesOK D C names) :
    ∀ x ∈ (renQ D C names q).2.1, (renQ D C names q).1.boundOf x = none := by
  intro x hx
  show ((((D.prog C).bounds.filter fun b => decide (b.1 ∉ D.fresh C)).map
      fun b => (rmap D C names q b.1, b.2)).find? (·.1 = x)).map (·.2) = none
  rw [List.find?_eq_none.mpr]
  · rfl
  intro b hb hbx
  obtain ⟨b0, hb0, rfl⟩ := List.mem_map.mp hb
  obtain ⟨-, hb0⟩ := List.mem_filter.mp hb0
  simp only [decide_eq_true_eq] at hb0 hbx
  rcases rmap_cases (q := q) h b0.1 with ⟨h1, -⟩ | ⟨-, h2⟩
  · exact hb0 h1
  · exact tname_not_mem h q b0.1 (h2 ▸ hbx ▸ hx)


/-! ## The translator -/

open Challenge.IndCpaDLM (StepFn InterpOK interpEval Reg RegQ)

variable (adm ev dec) in
/-- **The counterpart of a fresh-only adversary** (module docstring), with the flags `L` (per
table index: `some n` for the `n`-th encryption, `none` for a derived entry), the encryption
counter `n` and the query counter `q`. -/
noncomputable def tr : Adv (freshScheme D adm ev dec) Bool → List (Option ℕ) → ℕ → ℕ → LAdv D Bool
  | .ret a, _, _, _ => .ret a
  | .enc m0 m1 k, L, n, q => .enc m0 m1 (ename n) fun c => tr (k c) (L ++ [some n]) (n + 1) q
  | .eval C idx k, L, n, q =>
    if adm C = true then
      match idx.mapM (fun j => (L[j]?).join) with
      | some ns =>
        if ns.length = (D.fresh C).length then
          .eval (renQ D C (ns.map ename) q) idx fun r =>
            tr (k r) (L ++ (r.getD []).map fun _ => none) n (q + 1)
        else tr (k (some [])) L n q
      | none => tr (k none) L n q
    else tr (k none) L n q
  | .dec j k, L, n, q => .dec j fun r => tr (k r) L n q

section TrEq
variable {C : D.Circ} {idx : List ℕ} {k : Option (List (CT D)) → Adv (freshScheme D adm ev dec) Bool}
  {L : List (Option ℕ)} {n q : ℕ}

theorem tr_rej (h : adm C = false) :
    tr adm ev dec (.eval C idx k) L n q = tr adm ev dec (k none) L n q := by
  simp [tr, h]

theorem tr_notfresh (h : adm C = true) (hm : idx.mapM (fun j => (L[j]?).join) = none) :
    tr adm ev dec (.eval C idx k) L n q = tr adm ev dec (k none) L n q := by
  simp [tr, h, hm]

theorem tr_arity (h : adm C = true) {ns : List ℕ} (hm : idx.mapM (fun j => (L[j]?).join) = some ns)
    (har : ¬ ns.length = (D.fresh C).length) :
    tr adm ev dec (.eval C idx k) L n q = tr adm ev dec (k (some [])) L n q := by
  simp [tr, h, hm, har]

theorem tr_fwd (h : adm C = true) {ns : List ℕ} (hm : idx.mapM (fun j => (L[j]?).join) = some ns)
    (har : ns.length = (D.fresh C).length) :
    tr adm ev dec (.eval C idx k) L n q = .eval (renQ D C (ns.map ename) q) idx fun r =>
      tr adm ev dec (k r) (L ++ (r.getD []).map fun _ => none) n (q + 1) := by
  simp [tr, h, hm, har]

end TrEq

/-- The translator makes the same encryption queries. -/
theorem tr_bounded : ∀ {A : Adv (freshScheme D adm ev dec) Bool} {qe : ℕ}, Bounded A qe →
    ∀ L n q, BoundedLM (tr adm ev dec A L n q) qe
  | _, _, .ret a qe, L, n, q => BoundedLM.ret a qe
  | _, _, .enc m0 m1 k qe h, L, n, q =>
    BoundedLM.enc _ _ _ _ _ fun c => tr_bounded (h c) _ _ _
  | _, _, .eval C idx k qe h, L, n, q => by
    cases hc : adm C
    · rw [tr_rej hc]; exact tr_bounded (h _) _ _ _
    · rcases hm : idx.mapM (fun j => (L[j]?).join) with _ | ns
      · rw [tr_notfresh hc hm]; exact tr_bounded (h _) _ _ _
      · by_cases har : ns.length = (D.fresh C).length
        · rw [tr_fwd hc hm har]
          exact BoundedLM.eval _ _ _ _ fun r => tr_bounded (h r) _ _ _
        · rw [tr_arity hc hm har]; exact tr_bounded (h _) _ _ _
  | _, _, .dec j k qe h, L, n, q => BoundedLM.dec _ _ _ fun r => tr_bounded (h r) _ _ _

/-! ## The invariant -/

/-- **The invariant** (module docstring). -/
structure Inv (mk : Program → List Var → (Var → M D) → D.Circ) (adm : D.Circ → Bool)
    (ev : D.PK → D.Circ → List (CT D) → List (CT D)) (dec : D.SK → CT D → M D) (T : List (Entry (freshScheme D adm ev dec))) (TL : List (LEntry D))
    (L : List (Option ℕ)) (n q : ℕ) (G : Global D) : Prop where
  view : T = view adm ev dec TL L
  len : TL.length = L.length
  fr : ∀ j n' : ℕ, L[j]? = some (some n') → ∃ e : LEntry D, TL[j]? = some e ∧ e.name = ename n' ∧
    e.linked = true ∧ ename n' ∈ G.fresh ∧ n' < n
  dist : ∀ i j n' : ℕ, L[i]? = some (some n') → L[j]? = some (some n') → i = j
  names : ∀ x ∈ G.names, (∃ n' < n, x = ename n') ∨ ∃ k' < q, ∃ y, x = tname k' y
  reach : Reach mk adm G

theorem inv_empty (mk : Program → List Var → (Var → M D) → D.Circ) :
    Inv mk adm ev dec [] [] [] 0 0 (Global.empty D) :=
  ⟨rfl, rfl, fun _ _ h => by simp at h, fun _ _ _ h => by simp at h,
    fun x hx => by simp [names_def, Global.empty] at hx, Reach.empty⟩

theorem ename_not_mem {G : Global D} {n q : ℕ}
    (h : ∀ x ∈ G.names, (∃ n' < n, x = ename n') ∨ ∃ k' < q, ∃ y, x = tname k' y) :
    ename n ∉ G.names := fun hx => by
  rcases h _ hx with ⟨n', hn', he⟩ | ⟨k', -, y, he⟩
  · have := ename_inj he; omega
  · exact ename_ne_tname _ _ _ he

theorem tname_not_mem_G {G : Global D} {n q : ℕ}
    (h : ∀ x ∈ G.names, (∃ n' < n, x = ename n') ∨ ∃ k' < q, ∃ y, x = tname k' y) (y : Var) :
    tname q y ∉ G.names := fun hx => by
  rcases h _ hx with ⟨n', -, he⟩ | ⟨k', hk', y', he⟩
  · exact ename_ne_tname _ _ _ he.symm
  · have := (tname_inj he).1; omega

theorem inv_enc {mk : Program → List Var → (Var → M D) → D.Circ}
    {T : List (Entry (freshScheme D adm ev dec))} {TL : List (LEntry D)} {L : List (Option ℕ)}
    {n q : ℕ} {G : Global D} (I : Inv mk adm ev dec T TL L n q G) (m0 m1 : M D) (c : CT D) :
    Inv mk adm ev dec (T ++ [⟨m0, m1, c, true⟩])
      (TL ++ [⟨m0, m1, c, ename n, decide (ename n ∉ G.names)⟩]) (L ++ [some n]) (n + 1) q
      (G.link (ename n)) := by
  have hnot := ename_not_mem I.names
  have hlink : G.link (ename n) = (⟨G.inputs ++ [freshDecl D (ename n)], G.body,
      G.fresh ++ [ename n], G.pt, G.bounds⟩ : Global D) := by
    unfold Global.link; simp [hnot]
  have hfr : ∀ x, x ∈ G.fresh → x ∈ (G.link (ename n)).fresh := fun x hx => by
    rw [hlink]; exact List.mem_append_left _ hx
  refine ⟨?_, ?_, ?_, ?_, ?_, Reach.link G _ I.reach⟩
  · rw [I.view, view_append I.len]; rfl
  · simp [I.len]
  · intro j n' hj
    rw [getElem?_append_one] at hj
    split_ifs at hj with h1 h2
    · obtain ⟨e, he, h3, h4, h5, h6⟩ := I.fr j n' hj
      refine ⟨e, ?_, h3, h4, hfr _ h5, by omega⟩
      rw [List.getElem?_append_left (by rw [I.len]; exact h1)]; exact he
    · cases hj
      refine ⟨⟨m0, m1, c, ename n, decide (ename n ∉ G.names)⟩, ?_, rfl, decide_eq_true hnot,
        by rw [hlink]; simp, by omega⟩
      rw [getElem?_append_one]
      have : TL.length = j := by rw [I.len]; exact h2.symm
      simp [this]
  · intro i j n' hi hj
    rw [getElem?_append_one] at hi hj
    have hlt : ∀ i, L[i]? = some (some n') → n' < n := fun i h => (I.fr i n' h).choose_spec.2.2.2.2
    split_ifs at hi hj with h1 h2 h3 h4 h5 h6
    · exact I.dist i j n' hi hj
    · cases hj; have := hlt i hi; omega
    · cases hi; have := hlt j hj; omega
    · omega
  · intro x hx
    rcases mem_link hx with hx | rfl
    · rcases I.names x hx with ⟨n', h1, h2⟩ | h
      · exact Or.inl ⟨n', by omega, h2⟩
      · exact Or.inr h
    · exact Or.inl ⟨n, by omega, rfl⟩


theorem getElem?_append_none {L : List (Option ℕ)} {M : List (Option ℕ)} (hM : ∀ o ∈ M, o = none)
    {j n' : ℕ} (h : (L ++ M)[j]? = some (some n')) : L[j]? = some (some n') := by
  by_cases hj : j < L.length
  · rwa [List.getElem?_append_left hj] at h
  · rw [List.getElem?_append_right (by omega)] at h
    have := hM _ (List.mem_of_getElem? h)
    cases this

theorem inv_fwd {mk : Program → List Var → (Var → M D) → D.Circ}
    {T : List (Entry (freshScheme D adm ev dec))} {TL : List (LEntry D)} {L : List (Option ℕ)}
    {n q : ℕ} {G : Global D} (I : Inv mk adm ev dec T TL L n q G) {C' : QCirc D}
    {en : List (Var × Bool)} (hadm : admLM mk adm G C' en = true)
    (hnewq : ∀ x ∈ constNames C' ++ C'.1.body.map Trace.dst, ∃ y, x = tname q y)
    (outs : List (CT D)) (os : List Var) (s0 s1 : List (M D)) (h1 : outs.length ≤ os.length)
    (h2 : outs.length ≤ s0.length) (h3 : outs.length ≤ s1.length) :
    Inv mk adm ev dec (T ++ (outs.zip (s0.zip s1)).map fun p => ⟨p.2.1, p.2.2, p.1, false⟩)
      (TL ++ (outs.zip (os.zip (s0.zip s1))).map
        fun p => (⟨p.2.2.1, p.2.2.2, p.1, p.2.1, true⟩ : LEntry D))
      (L ++ outs.map fun _ => none) n (q + 1) (G.extend C') := by
  have hM : ∀ o ∈ outs.map (fun _ => (none : Option ℕ)), o = none := fun o ho => by
    obtain ⟨_, _, rfl⟩ := List.mem_map.mp ho; rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, Reach.extend G C' en I.reach hadm⟩
  · rw [I.view, view_append I.len, zip_view outs os s0 s1 h1 h2 h3]
  · rw [List.length_append, List.length_append, zip_len _ outs os s0 s1 h1 h2 h3, I.len,
      List.length_map]
  · intro j n' hj
    obtain ⟨e, he, h4, h5, h6, h7⟩ := I.fr j n' (getElem?_append_none hM hj)
    refine ⟨e, ?_, h4, h5, h6, h7⟩
    rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp he).1]; exact he
  · intro i j n' hi hj
    exact I.dist i j n' (getElem?_append_none hM hi) (getElem?_append_none hM hj)
  · intro x hx
    rcases mem_extend hx with hx | hx | hx
    · rcases I.names x hx with h | ⟨k', hk, y, h⟩
      · exact Or.inl h
      · exact Or.inr ⟨k', by omega, y, h⟩
    · obtain ⟨y, rfl⟩ := hnewq x (List.mem_append_left _ hx)
      exact Or.inr ⟨q, by omega, y, rfl⟩
    · obtain ⟨y, rfl⟩ := hnewq x (List.mem_append_right _ hx)
      exact Or.inr ⟨q, by omega, y, rfl⟩

/-! ## The simulation -/

theorem reg_eval {C : D.Circ} {idx : List ℕ}
    {k : Option (List (CT D)) → Adv (freshScheme D adm ev dec) Bool}
    (h : Reg D adm ev dec (.eval C idx k)) :
    (adm C = true → idx.length = (D.fresh C).length → RegQ D C idx) ∧
      ∀ r, Reg D adm ev dec (k r) := h


section Sim
variable (mk : Program → List Var → (Var → M D) → D.Circ)
  (hmk : ∀ p f c, D.prog (mk p f c) = p ∧ D.fresh (mk p f c) = f ∧ D.pt (mk p f c) = c)
  (adm : D.Circ → Bool) (stepF : StepFn D) (hI : InterpOK D stepF) (hR : RenameOK D stepF)
  (dec : D.SK → CT D → M D) [DecidableEq (M D)]
  (hren : ∀ r C0 C', CircRen D r C0 C' → adm C0 = true → adm C' = true)
  (hz : ∀ C, adm C = true → (Source.eval D.P.src (D.prog C) fun _ => .exact 0).isSome)
  (hfit : ∀ C, adm C = true → D.inputsFit C = true)
  (hagree : ∀ G, Reach mk adm G → ∀ (C : QCirc D) (en : List (Var × Bool)),
    C.2.1 = en.map (·.1) → en.all (·.2) = true → (∀ x ∈ C.2.1, x ∈ G.fresh) →
    (∀ x ∈ constNames C ++ C.1.body.map Trace.dst, x ∉ G.names) →
    (∀ d ∈ C.1.inputs, d.name ∈ C.2.1 → d = freshDecl D d.name) →
    (∀ x ∈ C.2.1, C.1.boundOf x = none) → admLM mk adm G C en = adm (mk C.1 C.2.1 C.2.2))
include hmk hI hR hren hz hfit hagree

/-- **The simulation**: the fresh-only game and `gameLM` against the translator return the same
bit, from any states related by the invariant. -/
theorem sim (b : Bool) (pk : D.PK) (sk : D.SK) (tape : ℕ → D.ER) :
    ∀ (A : Adv (freshScheme D adm (interpEval D stepF) dec) Bool),
      Reg D adm (interpEval D stepF) dec A →
      ∀ T TL L n q G, Inv mk adm (interpEval D stepF) dec T TL L n q G →
      gameD b pk sk tape A n T =
        gameLM mk adm (interpEval D stepF) dec b pk sk tape
          (tr adm (interpEval D stepF) dec A L n q) n TL G := by
  intro A
  induction A with
  | ret a => intro _ T TL L n q G _; rfl
  | enc m0 m1 k ih =>
    intro hA T TL L n q G I
    exact ih _ (hA _) _ _ _ _ _ _ (inv_enc I m0 m1 _)
  | dec j k ih =>
    intro hA T TL L n q G I
    simp only [gameD, gameLM, tr]
    rw [I.view, decAns_view I.len]
    exact ih _ (hA _) _ _ _ _ _ _ (I.view ▸ I)
  | eval C idx k ih =>
    intro hA T TL L n q G I
    obtain ⟨hreg, hk⟩ := reg_eval hA
    cases hc : adm C
    · have hstep : evalStep (S := freshScheme D adm (interpEval D stepF) dec) pk T C idx = none := by
        unfold evalStep; simp [hc]
      rw [tr_rej hc]
      simp only [gameD, hstep]
      exact ih _ (hk _) _ _ _ _ _ _ I
    rcases hm : idx.mapM (fun j => (L[j]?).join) with _ | ns
    · obtain ⟨j, hj, hjn⟩ := mapM_none_mem hm
      have hstep : evalStep (S := freshScheme D adm (interpEval D stepF) dec) pk T C idx = none := by
        unfold evalStep
        rw [mapM_none hj (I.view ▸ freshAt_view_none I.len hjn)]
        simp [hc]
      rw [tr_notfresh hc hm]
      simp only [gameD, hstep]
      exact ih _ (hk _) _ _ _ _ _ _ I
    have h2 := mapM_forall₂ hm
    obtain ⟨esL, hS, hT⟩ := forall₂_split
      (S := fun j (e : LEntry D) => TL[j]? = some e ∧
        freshAt T j = some (⟨e.m0, e.m1, e.c, true⟩ : Entry (freshScheme D adm (interpEval D stepF) dec)))
      (T := fun n' (e : LEntry D) => e.name = ename n' ∧ e.linked = true ∧ ename n' ∈ G.fresh)
      (fun j n' h => by
        have h' := Option.join_eq_some_iff.mp h
        obtain ⟨e, he, h3, h4, h5, -⟩ := I.fr j n' h'
        exact ⟨e, ⟨he, I.view ▸ freshAt_view_some I.len h' he⟩, h3, h4, h5⟩) h2
    have hmT : idx.mapM (fun j => TL[j]?) = some esL := by
      have := mapM_of_forall₂ (g := id) (hS.imp fun _ _ h => h.1)
      rwa [List.map_id] at this
    have hmF := mapM_of_forall₂ (hS.imp fun _ _ h => h.2)
    have hlen1 : idx.length = ns.length := h2.length_eq
    have hlen2 : idx.length = esL.length := hS.length_eq
    by_cases har : ns.length = (D.fresh C).length
    swap
    · have hstep : evalStep (S := freshScheme D adm (interpEval D stepF) dec) pk T C idx =
          some ([], []) := by
        unfold evalStep
        rw [hmF]
        have : ¬ esL.length = (D.fresh C).length := by omega
        simp [hc, this]
      rw [tr_arity hc hm har]
      simp only [gameD, hstep, List.append_nil]
      exact ih _ (hk _) _ _ _ _ _ _ I
    obtain ⟨hfn, hidx, hsc, hdst⟩ := hreg hc (by omega)
    have hnd : ns.Nodup := forall₂_nodup (fun a a' b h h' =>
      I.dist a a' b (Option.join_eq_some_iff.mp h) (Option.join_eq_some_iff.mp h')) h2 hidx
    have hN : NamesOK D C (ns.map ename) :=
      ⟨by rw [List.length_map, har], hnd.map fun _ _ h => ename_inj h, hfn,
        fun y hy => by obtain ⟨n', -, rfl⟩ := List.mem_map.mp hy; exact ⟨n', rfl⟩⟩
    have hnames : esL.map (·.name) = ns.map ename :=
      (forall₂_map_eq (hT.imp fun _ _ h => h.1.symm)).symm
    have hfrG : ∀ x ∈ ns.map ename, x ∈ G.fresh := by
      intro x hx
      rw [← hnames] at hx
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp hx
      obtain ⟨n', -, h3, -, h5⟩ := forall₂_mem_right hT e he
      exact h3 ▸ h5
    have hbf : ∀ d ∈ (D.prog C).inputs, d.name ∈ D.fresh C → (D.prog C).boundOf d.name = none :=
      fun d hd hf => (fit_fresh (hfit C hc) hd hf).2.2.2
    have hcirc := renQ_circRen (k := q) mk hmk hN hbf
    set C' := renQ D C (ns.map ename) q with hC'
    have hnewq := new_tname (q := q) hN hdst
    have hadm : admLM mk adm G C' (esL.map fun e => (e.name, e.linked)) = true := by
      rw [hagree G I.reach C' _ (by rw [List.map_map]; exact hnames.symm)
        (List.all_eq_true.mpr fun p hp => by
          obtain ⟨e, he, rfl⟩ := List.mem_map.mp hp
          exact (forall₂_mem_right hT e he).choose_spec.2.2.1)
        hfrG (fun x hx => by
          obtain ⟨y, rfl⟩ := hnewq x hx
          exact tname_not_mem_G I.names y)
        (decl_fresh hN (hfit C hc) hsc) (bnd_fresh hN)]
      exact hren _ _ _ hcirc hc
    have hzC := hz C hc
    have hev := interpEval_ren hI hR hcirc hzC pk
    have hsem := sem_ren hcirc hzC
    have hcs : (esL.map fun e => (⟨e.m0, e.m1, e.c, true⟩ :
        Entry (freshScheme D adm (interpEval D stepF) dec))).map (·.c) = esL.map (·.c) := by
      rw [List.map_map]; rfl
    have hm0 : (esL.map fun e => (⟨e.m0, e.m1, e.c, true⟩ :
        Entry (freshScheme D adm (interpEval D stepF) dec))).map (·.m0) = esL.map (·.m0) := by
      rw [List.map_map]; rfl
    have hm1 : (esL.map fun e => (⟨e.m0, e.m1, e.c, true⟩ :
        Entry (freshScheme D adm (interpEval D stepF) dec))).map (·.m1) = esL.map (·.m1) := by
      rw [List.map_map]; rfl
    have hlc : (esL.map (·.c)).length = (D.fresh C).length := by
      rw [List.length_map]; omega
    have hl0 : (esL.map (·.m0)).length = (D.fresh C).length := by
      rw [List.length_map]; omega
    have hl1 : (esL.map (·.m1)).length = (D.fresh C).length := by
      rw [List.length_map]; omega
    set outs := interpEval D stepF pk C (esL.map (·.c)) with houts
    set s0 := D.sem C (esL.map (·.m0)) with hs0
    set s1 := D.sem C (esL.map (·.m1)) with hs1
    have hstep : evalStep (S := freshScheme D adm (interpEval D stepF) dec) pk T C idx =
        some (outs, (outs.zip (s0.zip s1)).map fun p => ⟨p.2.1, p.2.2, p.1, false⟩) := by
      unfold evalStep
      rw [hmF]
      simp only [hc, ↓reduceIte, hcs, hm0, hm1, hlc]
      rfl
    have hLM : evalLM mk adm (interpEval D stepF) pk TL G C' idx =
        some (outs, (outs.zip (C'.1.outputs.zip (s0.zip s1))).map
          (fun p => (⟨p.2.2.1, p.2.2.2, p.1, p.2.1, true⟩ : LEntry D)), G.extend C') := by
      unfold evalLM
      rw [hmT]
      simp only [hadm, ↓reduceIte, hev, hsem]
      rfl
    rw [tr_fwd hc hm har]
    simp only [gameD, gameLM, hstep]
    rw [← hC', hLM]
    simp only [Option.getD_some]
    have hlo : outs.length ≤ (D.prog C).outputs.length := interpEval_len stepF pk C _
    have hls0 : s0.length = (D.prog C).outputs.length := sem_len hzC _ hl0
    have hls1 : s1.length = (D.prog C).outputs.length := sem_len hzC _ hl1
    have hlo' : C'.1.outputs.length = (D.prog C).outputs.length := List.length_map _
    exact ih _ (hk _) _ _ _ _ _ _ (inv_fwd I hadm hnewq outs C'.1.outputs s0 s1 (by omega) (by omega)
      (by omega))

omit hmk hI hR hren hz hfit hagree [DecidableEq (M D)] in
theorem inv_empty' : Inv mk adm (interpEval D stepF) dec [] [] [] 0 0 (Global.empty D) :=
  inv_empty mk

/-- **The embedding, generic form**: for a class kept by renaming, on which the oracle with
evaluation on earlier results agrees with the class on fresh entries, and an interpreter that is
local and kept by renaming. -/
theorem embed_core {Coins : Type}
    (A : Coins → D.PK → Adv (freshScheme D adm (interpEval D stepF) dec) Bool)
    (hA : ∀ c p, Reg D adm (interpEval D stepF) dec (A c p)) :
    ∃ A' : Coins → D.PK → LAdv D Bool, (∀ c p q, Bounded (A c p) q → BoundedLM (A' c p) q) ∧
      ∀ b pk sk tape c, gameD b pk sk tape (A c pk) 0 [] =
        gameLM mk adm (interpEval D stepF) dec b pk sk tape (A' c pk) 0 [] (Global.empty D) :=
  ⟨fun c p => tr adm (interpEval D stepF) dec (A c p) [] 0 0,
    fun _ _ _ h => tr_bounded h _ _ _,
    fun b pk sk tape c => sim mk hmk adm stepF hI hR dec hren hz hfit hagree b pk sk tape (A c pk)
      (hA c pk) [] [] [] 0 0 _ (inv_empty' mk adm stepF dec)⟩

end Sim

/-! ## The classes -/

open Challenge.IndCpaDProfile in
theorem exact_admBGV {E : Trace.Budget} {C : D.Circ} (h : exactClass D (fun _ => E) C = true) :
    admBGV D (fun _ => E) C = true := by
  have e : exactClass D (fun _ => E) C =
      (admBGV D (fun _ => E) C && Challenge.IndCpaDProfile.exactOnly (D.prog C).body) := rfl
  rw [e, Bool.and_eq_true] at h
  exact h.1

open Challenge.IndCpaDProfile in
theorem ks_admBGV {lay : Budget.KSLayout} {rots : List ℕ} {E : Trace.Budget} {C : D.Circ}
    (h : ksClass D lay rots (fun _ => E) C = true) : admBGV D (fun _ => E) C = true := by
  have e : ksClass D lay rots (fun _ => E) C = (admBGV D (fun _ => E) C &&
      Challenge.IndCpaDProfile.ksSide D.Pe lay && Challenge.IndCpaDProfile.ksNeed D.Pe lay rots E
        (D.prog C).body (initEnv D.P.src (D.prog C) fun _ => .exact 0)) := rfl
  rw [e, Bool.and_eq_true, Bool.and_eq_true] at h
  exact h.1.1

open Challenge.IndCpaDProfile in
theorem bfv_admBFV {lay : Budget.KSLayout} {rots : List ℕ} {E : TraceBFV.Budget} {C : D.Circ}
    (h : Challenge.IndCpaDLM.bfvClass D lay rots E C = true) :
    admBFV D (fun _ _ => E) C = true := by
  have e : Challenge.IndCpaDLM.bfvClass D lay rots E C = (admBFV D (fun _ _ => E) C &&
      Challenge.IndCpaDLM.bfvSide D.Pe lay && Challenge.IndCpaDLM.bfvNeed D.Pe lay rots E
        (D.prog C).body (initEnv D.P.src (D.prog C) fun _ => .exact 0)) := rfl
  rw [e, Bool.and_eq_true, Bool.and_eq_true] at h
  exact h.1.1

open Challenge.IndCpaDProfile in
theorem admBGV_fit {E : Trace.Budget} {C : D.Circ} (h : admBGV D (fun _ => E) C = true) :
    D.inputsFit C = true := by
  rw [Validation.IndCpaDLM.admBGV_eq, Bool.and_eq_true, Bool.and_eq_true] at h
  exact h.1.2

open Challenge.IndCpaDProfile in
theorem admBFV_fit {E : TraceBFV.Budget} {C : D.Circ} (h : admBFV D (fun _ _ => E) C = true) :
    D.inputsFit C = true := by
  rw [Validation.IndCpaDLM.admBFV_eq, Bool.and_eq_true] at h
  exact h.2

end Validation.IndCpaDEmbed

/-! ## The statements of `Challenge.IndCpaD.LMEmbed` -/

namespace Validation.IndCpaDLM
open Spec NPoly Scheme Source Spec.IndCpaD Spec.IndCpaDProfile Spec.IndCpaDLM
  Challenge.IndCpaDProfile MeasureTheory

theorem embed_exact (D : AbsScheme) (mk : Program → List Var → (Var → M D) → D.Circ)
    (hmk : ∀ p f c, D.prog (mk p f c) = p ∧ D.fresh (mk p f c) = f ∧ D.pt (mk p f c) = c)
    (E : Trace.Budget) (hfd : ∀ x, (freshDecl D x).ok D.P.src = true)
    (hmf : D.P.src.t < D.P.src.modulus D.lvl) (dec : D.SK → CT D → M D) [DecidableEq (M D)]
    {Coins : Type}
    (A : Coins → D.PK →
      Adv (freshScheme D (exactClass D fun _ => E)
        (Challenge.IndCpaDLM.interpEval D (Challenge.IndCpaDLM.exactStepFn D)) dec) Bool)
    (hA : ∀ c p, Challenge.IndCpaDLM.Reg D (exactClass D fun _ => E)
      (Challenge.IndCpaDLM.interpEval D (Challenge.IndCpaDLM.exactStepFn D)) dec (A c p)) :
    ∃ A' : Coins → D.PK → LAdv D Bool, (∀ c p q, Bounded (A c p) q → BoundedLM (A' c p) q) ∧
      ∀ b pk sk tape c, gameD b pk sk tape (A c pk) 0 [] =
        gameLM mk (exactClass D fun _ => E)
          (Challenge.IndCpaDLM.interpEval D (Challenge.IndCpaDLM.exactStepFn D)) dec b pk sk tape
          (A' c pk) 0 [] (Global.empty D) :=
  Validation.IndCpaDEmbed.embed_core mk hmk _ _ (Validation.IndCpaDLM.exactStep_interpOK D)
    (Validation.IndCpaDRen.exactStep_renameOK D) dec
    (fun _ _ _ h hc => Validation.IndCpaDRen.exactClass_ren E h hc)
    (fun _ hc => Validation.IndCpaDLM.admBGV_eval (Validation.IndCpaDEmbed.exact_admBGV hc))
    (fun _ hc => Validation.IndCpaDEmbed.admBGV_fit (Validation.IndCpaDEmbed.exact_admBGV hc))
    (fun G hG C en hen hl hfr hnew hdecl hbnd =>
      Validation.IndCpaDLM.admLM_fresh_exact D mk hmk E hfd hmf G hG C en hen hl hfr hnew hdecl
        hbnd) A hA

theorem embed_ks (D : AbsScheme) (mk : Program → List Var → (Var → M D) → D.Circ)
    (hmk : ∀ p f c, D.prog (mk p f c) = p ∧ D.fresh (mk p f c) = f ∧ D.pt (mk p f c) = c)
    (lay : Budget.KSLayout) (rots : List ℕ) (E : Trace.Budget)
    (rk : D.PK → List (IntPoly D.P.src.N × IntPoly D.P.src.N))
    (gk : D.PK → ℕ → List (IntPoly D.P.src.N × IntPoly D.P.src.N))
    (hfd : ∀ x, (freshDecl D x).ok D.P.src = true) (hmf : D.P.src.t < D.P.src.modulus D.lvl)
    (dec : D.SK → CT D → M D) [DecidableEq (M D)] {Coins : Type}
    (A : Coins → D.PK → Adv (freshScheme D (ksClass D lay rots fun _ => E)
      (Challenge.IndCpaDLM.interpEval D (Challenge.IndCpaDLM.ksStepFn D lay rk gk)) dec) Bool)
    (hA : ∀ c p, Challenge.IndCpaDLM.Reg D (ksClass D lay rots fun _ => E)
      (Challenge.IndCpaDLM.interpEval D (Challenge.IndCpaDLM.ksStepFn D lay rk gk)) dec
      (A c p)) :
    ∃ A' : Coins → D.PK → LAdv D Bool, (∀ c p q, Bounded (A c p) q → BoundedLM (A' c p) q) ∧
      ∀ b pk sk tape c, gameD b pk sk tape (A c pk) 0 [] =
        gameLM mk (ksClass D lay rots fun _ => E)
          (Challenge.IndCpaDLM.interpEval D (Challenge.IndCpaDLM.ksStepFn D lay rk gk)) dec b pk
          sk tape (A' c pk) 0 [] (Global.empty D) :=
  Validation.IndCpaDEmbed.embed_core mk hmk _ _ (Validation.IndCpaDLM.ksStep_interpOK D lay rk gk)
    (Validation.IndCpaDRen.ksStep_renameOK D lay rk gk) dec
    (fun _ _ _ h hc => Validation.IndCpaDRen.ksClass_ren lay rots E h hc)
    (fun _ hc => Validation.IndCpaDLM.admBGV_eval (Validation.IndCpaDEmbed.ks_admBGV hc))
    (fun _ hc => Validation.IndCpaDEmbed.admBGV_fit (Validation.IndCpaDEmbed.ks_admBGV hc))
    (fun G hG C en hen hl hfr hnew hdecl hbnd =>
      Validation.IndCpaDLM.admLM_fresh_ks D mk hmk lay rots E hfd hmf G hG C en hen hl hfr hnew
        hdecl hbnd) A hA

theorem embed_bfv (D : AbsScheme) (mk : Program → List Var → (Var → M D) → D.Circ)
    (hmk : ∀ p f c, D.prog (mk p f c) = p ∧ D.fresh (mk p f c) = f ∧ D.pt (mk p f c) = c)
    (lay : Budget.KSLayout) (rots : List ℕ) (E : TraceBFV.Budget)
    (rk : D.PK → ℕ → List (IntPoly D.P.src.N × IntPoly D.P.src.N))
    (gk : D.PK → ℕ → ℕ → List (IntPoly D.P.src.N × IntPoly D.P.src.N))
    (hfd : ∀ x, (freshDecl D x).ok D.P.src = true)
    (hdf : Challenge.BFV.decOK D.P.src.t (D.P.src.modulus D.lvl) D.eps = true)
    (dec : D.SK → CT D → M D) [DecidableEq (M D)] {Coins : Type}
    (A : Coins → D.PK → Adv (freshScheme D (Challenge.IndCpaDLM.bfvClass D lay rots E)
      (Challenge.IndCpaDLM.interpEval D (Challenge.IndCpaDLM.bfvStepFn D lay rk gk)) dec) Bool)
    (hA : ∀ c p, Challenge.IndCpaDLM.Reg D (Challenge.IndCpaDLM.bfvClass D lay rots E)
      (Challenge.IndCpaDLM.interpEval D (Challenge.IndCpaDLM.bfvStepFn D lay rk gk)) dec
      (A c p)) :
    ∃ A' : Coins → D.PK → LAdv D Bool, (∀ c p q, Bounded (A c p) q → BoundedLM (A' c p) q) ∧
      ∀ b pk sk tape c, gameD b pk sk tape (A c pk) 0 [] =
        gameLM mk (Challenge.IndCpaDLM.bfvClass D lay rots E)
          (Challenge.IndCpaDLM.interpEval D (Challenge.IndCpaDLM.bfvStepFn D lay rk gk)) dec b pk
          sk tape (A' c pk) 0 [] (Global.empty D) :=
  Validation.IndCpaDEmbed.embed_core mk hmk _ _ (Validation.IndCpaDLM.bfvStep_interpOK D lay rk gk)
    (Validation.IndCpaDRen.bfvStep_renameOK D lay rk gk) dec
    (fun _ _ _ h hc => Validation.IndCpaDRen.bfvClass_ren lay rots E h hc)
    (fun _ hc => Validation.IndCpaDLM.admBFV_eval (Validation.IndCpaDEmbed.bfv_admBFV hc))
    (fun _ hc => Validation.IndCpaDEmbed.admBFV_fit (Validation.IndCpaDEmbed.bfv_admBFV hc))
    (fun G hG C en hen hl hfr hnew hdecl hbnd =>
      Validation.IndCpaDLM.admLM_fresh_bfvClass D mk hmk lay rots E hfd hdf G hG C en hen hl hfr
        hnew hdecl hbnd) A hA

theorem embed_bgvSealExact [DecidableEq (M bgvSealData)] {Coins : Type}
    (A : Coins → bgvSealData.PK → Adv (freshScheme bgvSealData
      (exactClass bgvSealData bgvSealProfile)
      (Challenge.IndCpaDLM.interpEval bgvSealData (Challenge.IndCpaDLM.exactStepFn bgvSealData))
      bgvSealData.decBGV) Bool)
    (hA : ∀ c p, Challenge.IndCpaDLM.Reg bgvSealData (exactClass bgvSealData bgvSealProfile)
      (Challenge.IndCpaDLM.interpEval bgvSealData (Challenge.IndCpaDLM.exactStepFn bgvSealData))
      bgvSealData.decBGV (A c p)) :
    ∃ A' : Coins → bgvSealData.PK → LAdv bgvSealData Bool,
      (∀ c p q, Bounded (A c p) q → BoundedLM (A' c p) q) ∧
      ∀ b pk sk tape c, gameD b pk sk tape (A c pk) 0 [] =
        gameLM Challenge.IndCpaDLM.mkSealExact (exactClass bgvSealData bgvSealProfile)
          (Challenge.IndCpaDLM.interpEval bgvSealData (Challenge.IndCpaDLM.exactStepFn bgvSealData))
          bgvSealData.decBGV b pk sk tape (A' c pk) 0 [] (Global.empty bgvSealData) :=
  embed_exact bgvSealData Challenge.IndCpaDLM.mkSealExact (fun _ _ _ => ⟨rfl, rfl, rfl⟩)
    (Spec.Budget.certified bgvSeal (Spec.Budget.uniformLayout 1)) (fun _ => rfl) (by decide)
    bgvSealData.decBGV A hA

theorem embed_bgvKSSeal [DecidableEq (M bgvKSSealData)] {Coins : Type}
    (A : Coins → bgvKSSealData.PK →
      Adv (freshScheme bgvKSSealData Challenge.IndCpaDLM.admSeal Challenge.IndCpaDLM.evSeal
        bgvKSSealData.decBGV) Bool)
    (hA : ∀ c p, Challenge.IndCpaDLM.Reg bgvKSSealData Challenge.IndCpaDLM.admSeal
      Challenge.IndCpaDLM.evSeal bgvKSSealData.decBGV (A c p)) :
    ∃ A' : Coins → bgvKSSealData.PK → LAdv bgvKSSealData Bool,
      (∀ c p q, Bounded (A c p) q → BoundedLM (A' c p) q) ∧
      ∀ b pk sk tape c, gameD b pk sk tape (A c pk) 0 [] =
        gameLM Challenge.IndCpaDLM.mkSeal Challenge.IndCpaDLM.admSeal Challenge.IndCpaDLM.evSeal
          bgvKSSealData.decBGV b pk sk tape (A' c pk) 0 [] (Global.empty bgvKSSealData) :=
  embed_ks bgvKSSealData Challenge.IndCpaDLM.mkSeal Validation.IndCpaDLM.hmkSeal bgvKSLayout [5]
    (Spec.Budget.certified bgvKSSeal bgvKSLayout) (fun pk => pk.2.2.1) (fun pk => pk.2.2.2)
    (fun _ => rfl) (by decide) bgvKSSealData.decBGV A hA

theorem embed_bfvSeal [DecidableEq (M Challenge.IndCpaDLM.bfvSealData)] {Coins : Type}
    (A : Coins → Challenge.IndCpaDLM.bfvSealData.PK →
      Adv (freshScheme Challenge.IndCpaDLM.bfvSealData Challenge.IndCpaDLM.admBFVSeal
        Challenge.IndCpaDLM.evBFVSeal Challenge.IndCpaDLM.bfvSealData.decBFV) Bool)
    (hA : ∀ c p, Challenge.IndCpaDLM.Reg Challenge.IndCpaDLM.bfvSealData
      Challenge.IndCpaDLM.admBFVSeal Challenge.IndCpaDLM.evBFVSeal
      Challenge.IndCpaDLM.bfvSealData.decBFV (A c p)) :
    ∃ A' : Coins → Challenge.IndCpaDLM.bfvSealData.PK → LAdv Challenge.IndCpaDLM.bfvSealData Bool,
      (∀ c p q, Bounded (A c p) q → BoundedLM (A' c p) q) ∧
      ∀ b pk sk tape c, gameD b pk sk tape (A c pk) 0 [] =
        gameLM Challenge.IndCpaDLM.mkBFVSeal Challenge.IndCpaDLM.admBFVSeal
          Challenge.IndCpaDLM.evBFVSeal Challenge.IndCpaDLM.bfvSealData.decBFV b pk sk tape
          (A' c pk) 0 [] (Global.empty Challenge.IndCpaDLM.bfvSealData) :=
  embed_bfv Challenge.IndCpaDLM.bfvSealData Challenge.IndCpaDLM.mkBFVSeal
    Validation.IndCpaDLM.hmkBFVSeal Challenge.IndCpaDLM.bfvSealLayout [5]
    Challenge.IndCpaDLM.bfvSealBudget (fun pk => pk.2.2.1) (fun pk => pk.2.2.2) (fun _ => rfl)
    Validation.IndCpaDLM.lm_two_stage_bfv_kernel.1 Challenge.IndCpaDLM.bfvSealData.decBFV A hA

theorem embedProb_bgvSealExact [DecidableEq (M bgvSealData)] {Coins : Type}
    (A : Coins → bgvSealData.PK → Adv (freshScheme bgvSealData
      (exactClass bgvSealData bgvSealProfile)
      (Challenge.IndCpaDLM.interpEval bgvSealData (Challenge.IndCpaDLM.exactStepFn bgvSealData))
      bgvSealData.decBGV) Bool)
    (hA : ∀ c p, Challenge.IndCpaDLM.Reg bgvSealData (exactClass bgvSealData bgvSealProfile)
      (Challenge.IndCpaDLM.interpEval bgvSealData (Challenge.IndCpaDLM.exactStepFn bgvSealData))
      bgvSealData.decBGV (A c p)) :
    ∃ A' : Coins → bgvSealData.PK → LAdv bgvSealData Bool,
      (∀ c p q, Bounded (A c p) q → BoundedLM (A' c p) q) ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (pk : Ω → bgvSealData.PK)
        (sk : Ω → bgvSealData.SK) (tape : Ω → ℕ → bgvSealData.ER) (coins : Ω → Coins) (b : Bool),
        μ {ω | gameD b (pk ω) (sk ω) (tape ω) (A (coins ω) (pk ω)) 0 [] = true} =
          μ {ω | gameLM Challenge.IndCpaDLM.mkSealExact (exactClass bgvSealData bgvSealProfile)
            (Challenge.IndCpaDLM.interpEval bgvSealData
              (Challenge.IndCpaDLM.exactStepFn bgvSealData)) bgvSealData.decBGV b (pk ω) (sk ω)
            (tape ω) (A' (coins ω) (pk ω)) 0 [] (Global.empty bgvSealData) = true} := by
  obtain ⟨A', h1, h2⟩ := embed_bgvSealExact A hA
  exact ⟨A', h1, fun μ pk sk tape coins b => by simp only [h2]⟩

theorem embedProb_bgvKSSeal [DecidableEq (M bgvKSSealData)] {Coins : Type}
    (A : Coins → bgvKSSealData.PK →
      Adv (freshScheme bgvKSSealData Challenge.IndCpaDLM.admSeal Challenge.IndCpaDLM.evSeal
        bgvKSSealData.decBGV) Bool)
    (hA : ∀ c p, Challenge.IndCpaDLM.Reg bgvKSSealData Challenge.IndCpaDLM.admSeal
      Challenge.IndCpaDLM.evSeal bgvKSSealData.decBGV (A c p)) :
    ∃ A' : Coins → bgvKSSealData.PK → LAdv bgvKSSealData Bool,
      (∀ c p q, Bounded (A c p) q → BoundedLM (A' c p) q) ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (pk : Ω → bgvKSSealData.PK)
        (sk : Ω → bgvKSSealData.SK) (tape : Ω → ℕ → bgvKSSealData.ER) (coins : Ω → Coins)
        (b : Bool),
        μ {ω | gameD b (pk ω) (sk ω) (tape ω) (A (coins ω) (pk ω)) 0 [] = true} =
          μ {ω | gameLM Challenge.IndCpaDLM.mkSeal Challenge.IndCpaDLM.admSeal
            Challenge.IndCpaDLM.evSeal bgvKSSealData.decBGV b (pk ω) (sk ω) (tape ω)
            (A' (coins ω) (pk ω)) 0 [] (Global.empty bgvKSSealData) = true} := by
  obtain ⟨A', h1, h2⟩ := embed_bgvKSSeal A hA
  exact ⟨A', h1, fun μ pk sk tape coins b => by simp only [h2]⟩

theorem embedProb_bfvSeal [DecidableEq (M Challenge.IndCpaDLM.bfvSealData)] {Coins : Type}
    (A : Coins → Challenge.IndCpaDLM.bfvSealData.PK →
      Adv (freshScheme Challenge.IndCpaDLM.bfvSealData Challenge.IndCpaDLM.admBFVSeal
        Challenge.IndCpaDLM.evBFVSeal Challenge.IndCpaDLM.bfvSealData.decBFV) Bool)
    (hA : ∀ c p, Challenge.IndCpaDLM.Reg Challenge.IndCpaDLM.bfvSealData
      Challenge.IndCpaDLM.admBFVSeal Challenge.IndCpaDLM.evBFVSeal
      Challenge.IndCpaDLM.bfvSealData.decBFV (A c p)) :
    ∃ A' : Coins → Challenge.IndCpaDLM.bfvSealData.PK → LAdv Challenge.IndCpaDLM.bfvSealData Bool,
      (∀ c p q, Bounded (A c p) q → BoundedLM (A' c p) q) ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
        (pk : Ω → Challenge.IndCpaDLM.bfvSealData.PK) (sk : Ω → Challenge.IndCpaDLM.bfvSealData.SK)
        (tape : Ω → ℕ → Challenge.IndCpaDLM.bfvSealData.ER) (coins : Ω → Coins) (b : Bool),
        μ {ω | gameD b (pk ω) (sk ω) (tape ω) (A (coins ω) (pk ω)) 0 [] = true} =
          μ {ω | gameLM Challenge.IndCpaDLM.mkBFVSeal Challenge.IndCpaDLM.admBFVSeal
            Challenge.IndCpaDLM.evBFVSeal Challenge.IndCpaDLM.bfvSealData.decBFV b (pk ω) (sk ω)
            (tape ω) (A' (coins ω) (pk ω)) 0 [] (Global.empty Challenge.IndCpaDLM.bfvSealData)
              = true} := by
  obtain ⟨A', h1, h2⟩ := embed_bfvSeal A hA
  exact ⟨A', h1, fun μ pk sk tape coins b => by simp only [h2]⟩

example := (@embed_exact : type_of% @Challenge.IndCpaDLM.embed_exact)
example := (@embed_ks : type_of% @Challenge.IndCpaDLM.embed_ks)
example := (@embed_bfv : type_of% @Challenge.IndCpaDLM.embed_bfv)
example := (@embed_bgvSealExact : type_of% @Challenge.IndCpaDLM.embed_bgvSealExact)
example := (@embed_bgvKSSeal : type_of% @Challenge.IndCpaDLM.embed_bgvKSSeal)
example := (@embed_bfvSeal : type_of% @Challenge.IndCpaDLM.embed_bfvSeal)
example := (@embedProb_bgvSealExact : type_of% @Challenge.IndCpaDLM.embedProb_bgvSealExact)
example := (@embedProb_bgvKSSeal : type_of% @Challenge.IndCpaDLM.embedProb_bgvKSSeal)
example := (@embedProb_bfvSeal : type_of% @Challenge.IndCpaDLM.embedProb_bfvSeal)

end Validation.IndCpaDLM
