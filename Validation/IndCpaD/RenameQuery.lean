import Validation.IndCpaD.RenameClass

/-!
# Validation.IndCpaD.RenameQuery — renaming a fresh-only query to globally new names

The `n`-th encryption is named `ename n`; the names of the `k`-th evaluation query that are not
fresh inputs become `tname k x`; its fresh inputs become the names of the selected entries.
`renQ_circRen`: for a circuit of a class (fresh inputs well formed, no bound for them, distinct
fresh names, distinct entry names), the renamed query is a renaming of it (`CircRen`).
-/

namespace Validation.IndCpaDRen
open Spec NPoly Scheme Source Spec.IndCpaDProfile Spec.IndCpaDLM

/-- The name of the `n`-th encryption. -/
def ename (n : ℕ) : Var := String.ofList ('e' :: List.replicate n 'x')

/-- The name of the variable `x` of the `k`-th query. -/
def tname (k : ℕ) (x : Var) : Var := String.ofList ('q' :: (List.replicate k 'x' ++ '.' :: x.toList))

theorem replicate_dot {a b : List Char} : ∀ {k k' : ℕ},
    List.replicate k 'x' ++ '.' :: a = List.replicate k' 'x' ++ '.' :: b → k = k' ∧ a = b
  | 0, 0, h => by simpa using h
  | 0, _ + 1, h => by simp [List.replicate_succ] at h
  | _ + 1, 0, h => by simp [List.replicate_succ] at h
  | k + 1, k' + 1, h => by
    simp only [List.replicate_succ, List.cons_append, List.cons.injEq, true_and] at h
    obtain ⟨h1, h2⟩ := replicate_dot h
    exact ⟨by rw [h1], h2⟩

theorem ename_inj {n n' : ℕ} (h : ename n = ename n') : n = n' := by
  have := String.ofList_injective h
  simp only [List.cons.injEq, true_and] at this
  simpa using congrArg List.length this

theorem tname_inj {k k' : ℕ} {x y : Var} (h : tname k x = tname k' y) : k = k' ∧ x = y := by
  have := String.ofList_injective h
  simp only [List.cons.injEq, true_and] at this
  obtain ⟨h1, h2⟩ := replicate_dot this
  exact ⟨h1, String.ext h2⟩

theorem ename_ne_tname (n k : ℕ) (x : Var) : ename n ≠ tname k x := by
  intro h
  have := String.ofList_injective h
  simp at this

variable {D : AbsScheme}

/-- The renaming of the names of a query: fresh input `p` to `names[p]`, other names tagged. -/
def rmap (D : AbsScheme) (C : D.Circ) (names : List Var) (k : ℕ) (x : Var) : Var :=
  match (D.fresh C).idxOf? x with
  | some p => names.getD p ""
  | none => tname k x

/-- The renamed program. -/
def rprog (D : AbsScheme) (C : D.Circ) (names : List Var) (k : ℕ) : Program :=
  ⟨(D.prog C).inputs.map (renD (rmap D C names k)), (D.prog C).body.map (renI (rmap D C names k)),
    (D.prog C).outputs.map (rmap D C names k),
    ((D.prog C).bounds.filter fun b => decide (b.1 ∉ D.fresh C)).map
      fun b => (rmap D C names k b.1, b.2)⟩

open Classical in
/-- The renamed constants. -/
noncomputable def rpt (D : AbsScheme) (C : D.Circ) (names : List Var) (k : ℕ) (y : Var) :
    Poly D.P.src.t D.P.src.N :=
  if h : ∃ x, rmap D C names k x = y then D.pt C (Classical.choose h) else 0

/-- **The renamed query.** -/
noncomputable def renQ (D : AbsScheme) (C : D.Circ) (names : List Var) (k : ℕ) : QCirc D :=
  (rprog D C names k, names, rpt D C names k)

theorem idxOf_nodup {l : List Var} (hl : l.Nodup) {p : ℕ} (hp : p < l.length) :
    l.idxOf? l[p] = some p := by
  refine List.idxOf?_eq_some_iff.mpr ⟨hp, rfl, fun j hj h => ?_⟩
  have := (List.Nodup.getElem_inj_iff hl (i := j) (j := p) (hi := by omega) (hj := hp)).mp
    (by simpa using h)
  omega

/-- The conditions on the selected names. -/
structure NamesOK (D : AbsScheme) (C : D.Circ) (names : List Var) : Prop where
  len : names.length = (D.fresh C).length
  nodup : names.Nodup
  fresh : (D.fresh C).Nodup
  ent : ∀ y ∈ names, ∃ n, y = ename n

theorem rmap_fresh {C : D.Circ} {names : List Var} {k : ℕ} (h : NamesOK D C names) {p : ℕ}
    (hp : p < (D.fresh C).length) :
    rmap D C names k (D.fresh C)[p] = names[p]'(h.len ▸ hp) := by
  unfold rmap
  rw [idxOf_nodup h.fresh hp]
  simp [List.getD_eq_getElem?_getD, h.len ▸ hp]

theorem rmap_some {C : D.Circ} {names : List Var} {k : ℕ} (h : NamesOK D C names) {x : Var}
    {p : ℕ} (hx : (D.fresh C).idxOf? x = some p) :
    ∃ hp : p < names.length, rmap D C names k x = names[p] ∧ (D.fresh C)[p]'(h.len ▸ hp) = x := by
  obtain ⟨hp, hp2, -⟩ := List.idxOf?_eq_some_iff.mp hx
  have hp' : p < names.length := h.len ▸ hp
  refine ⟨hp', ?_, hp2⟩
  unfold rmap
  rw [hx]
  simp [List.getD_eq_getElem?_getD, hp']

theorem rmap_none {C : D.Circ} {names : List Var} {k : ℕ} {x : Var}
    (hx : (D.fresh C).idxOf? x = none) : rmap D C names k x = tname k x := by
  unfold rmap; rw [hx]

theorem rmap_inj {C : D.Circ} {names : List Var} {k : ℕ} (h : NamesOK D C names) :
    Function.Injective (rmap D C names k) := by
  intro x y hxy
  rcases hx : (D.fresh C).idxOf? x with _ | p <;> rcases hy : (D.fresh C).idxOf? y with _ | q
  · rw [rmap_none hx, rmap_none hy] at hxy; exact (tname_inj hxy).2
  · obtain ⟨hq, e2, -⟩ := rmap_some h hy
    rw [rmap_none hx, e2] at hxy
    obtain ⟨n, hn⟩ := h.ent _ (List.getElem_mem hq)
    exact absurd (hxy.trans hn).symm (ename_ne_tname n k x)
  · obtain ⟨hp, e1, -⟩ := rmap_some h hx
    rw [rmap_none hy, e1] at hxy
    obtain ⟨n, hn⟩ := h.ent _ (List.getElem_mem hp)
    exact absurd (hxy.symm.trans hn).symm (ename_ne_tname n k y)
  · obtain ⟨hp, e1, f1⟩ := rmap_some h hx
    obtain ⟨hq, e2, f2⟩ := rmap_some h hy
    rw [e1, e2] at hxy
    have := (List.Nodup.getElem_inj_iff h.nodup).mp hxy
    subst this
    rw [← f1, ← f2]

/-- **The renamed query is a renaming of the circuit**, for a circuit whose fresh inputs declare
no bound. -/
theorem renQ_circRen (mk : Program → List Var → (Var → M D) → D.Circ)
    (hmk : ∀ p f c, D.prog (mk p f c) = p ∧ D.fresh (mk p f c) = f ∧ D.pt (mk p f c) = c)
    {C : D.Circ} {names : List Var} {k : ℕ} (h : NamesOK D C names)
    (hbf : ∀ d ∈ (D.prog C).inputs, d.name ∈ D.fresh C → (D.prog C).boundOf d.name = none) :
    CircRen D (rmap D C names k) C (mk (renQ D C names k).1 (renQ D C names k).2.1
      (renQ D C names k).2.2) := by
  have hr := rmap_inj (k := k) h
  refine ⟨⟨hr, by rw [(hmk _ _ _).1]; rfl, by rw [(hmk _ _ _).1]; rfl,
    by rw [(hmk _ _ _).1]; rfl, fun d hd => ?_⟩, ?_, fun x => ?_⟩
  · rw [(hmk _ _ _).1]
    show (((((D.prog C).bounds.filter fun b => decide (b.1 ∉ D.fresh C)).map
      fun b : Var × ℕ => (rmap D C names k b.1, b.2)).find? (·.1 = rmap D C names k d.name)).map
        (·.2)) = _
    rw [List.find?_map]
    have e : ((fun b : Var × ℕ => decide (b.1 = rmap D C names k d.name)) ∘
        fun b : Var × ℕ => (rmap D C names k b.1, b.2)) = fun b : Var × ℕ =>
          decide (b.1 = d.name) := by
      funext b; simp [hr.eq_iff]
    rw [e, Option.map_map]
    by_cases hdf : d.name ∈ D.fresh C
    · rw [hbf d hd hdf, List.find?_eq_none.mpr]
      · rfl
      intro b hb hbe
      obtain ⟨-, hb2⟩ := List.mem_filter.mp hb
      simp only [decide_eq_true_eq] at hbe hb2
      exact hb2 (hbe ▸ hdf)
    · have e2 : ((D.prog C).bounds.filter fun b => decide (b.1 ∉ D.fresh C)).find?
            (fun b => decide (b.1 = d.name)) =
          (D.prog C).bounds.find? (fun b => decide (b.1 = d.name)) := by
        rw [List.find?_filter]
        congr 1
        funext b
        by_cases hb : b.1 = d.name
        · simp [hb, hdf]
        · simp [hb]
      rw [e2]
      rfl
  · rw [(hmk _ _ _).2.1]
    show names = _
    refine List.ext_getElem (by rw [List.length_map, h.len]) fun p h1 h2 => ?_
    rw [List.getElem_map]
    have hp : p < (D.fresh C).length := by rw [← h.len]; exact h1
    obtain ⟨_, e1, -⟩ := rmap_some (k := k) h (idxOf_nodup h.fresh hp)
    rw [e1]
  · rw [(hmk _ _ _).2.2]
    show rpt D C names k (rmap D C names k x) = _
    unfold rpt
    have hex : ∃ y, rmap D C names k y = rmap D C names k x := ⟨x, rfl⟩
    rw [dif_pos hex, hr (Classical.choose_spec hex)]

end Validation.IndCpaDRen
