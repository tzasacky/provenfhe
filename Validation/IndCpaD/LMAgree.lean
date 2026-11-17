import Validation.IndCpaD.Frame
import Validation.IndCpaD.LM
import Challenge.IndCpaD.LMAgree

/-!
# Validation.IndCpaD.LMAgree — a query on fresh entries is accepted exactly when the fresh-only class accepts it

For the certificate classes at a constant budget, a reachable global program `G` and a query `C`
on fresh entries that writes only new names, the inlined program `G.body ++ C.body` is in the
class exactly when `C` alone is (`Validation.IndCpaD.Frame`: the analyses are local; the inputs
of the inlined program are those of `G`, which passed the checks when they were inlined, and the
constants of `C` with the bounds `C` declares).
-/

namespace Validation.IndCpaDLM
open Spec NPoly Scheme Source Spec.IndCpaD Spec.IndCpaDProfile Spec.IndCpaDLM
  Challenge.IndCpaDProfile Challenge.Headline
open Validation.IndCpaDLM (Ext ext_refl ext_trans find_name find_none)
open Validation.IndCpaDFrame

variable {D : AbsScheme}

/-- The input-shape check of `AbsScheme.inputsFit` for one declaration, with its declared bound
and whether it is a fresh input. -/
def qFit (D : AbsScheme) (d : Decl) (bnd : Option ℕ) (fr : Bool) : Bool :=
  if fr then d.parts == 2 && d.key == 1 && d.level == D.lvl && bnd.isNone
  else
    d.parts == 1 && decide (D.P.src.t - 1 ≤ D.P.src.modulus d.level / 2) &&
      match bnd with
      | some b => decide (D.P.src.t - 1 ≤ b)
      | none => true

theorem inputsFit_eq (C : D.Circ) : D.inputsFit C =
    (D.prog C).inputs.all fun d =>
      qFit D d ((D.prog C).boundOf d.name) (decide (d.name ∈ D.fresh C)) := by
  unfold AbsScheme.inputsFit qFit
  congr 1; funext d
  by_cases h : d.name ∈ D.fresh C
  · rw [if_pos h, if_pos (by simpa using h)]
  · rw [if_neg h, if_neg (by simpa using h)]
    cases (D.prog C).boundOf d.name <;> rfl

/-- The input check of `Challenge.Certify.inputsMsgOK?` for one declaration, with its declared
bound. -/
def qMsg (D : AbsScheme) (d : Decl) (bnd : Option ℕ) : Bool :=
  decide (D.P.src.t < D.P.src.modulus d.level) && bnd.all fun b => decide (D.P.src.t / 2 ≤ b)

theorem inputsMsgOK_eq (prog : Program) :
    Challenge.Certify.inputsMsgOK? D.Pe prog =
      prog.inputs.all fun d => qMsg D d (prog.boundOf d.name) := rfl

theorem certifyProfile_msg {P : FullParams} {E : Trace.Budget} {prog : Program}
    {r : ℕ × List (Var × ℕ)} (h : Challenge.Profile.certifyProfile? P E prog false = some r) :
    Challenge.Certify.inputsMsgOK? P prog = true := by
  rw [Validation.IndCpaDFrame.certifyProfile_eq] at h
  by_contra hc
  simp [hc, guard] at h

/-! ## Names and declarations of the inlined program -/

theorem boundOf_eq (p : Program) (x : Var) :
    p.boundOf x = (p.bounds.find? (·.1 = x)).map (·.2) := rfl

theorem find_pairs_none {l : List (Var × ℕ)} {x : Var} (h : ∀ p ∈ l, p.1 ≠ x) :
    l.find? (·.1 = x) = none := by
  rw [List.find?_eq_none]; intro p hp; simpa using h p hp

theorem find_pairs_filter {l : List (Var × ℕ)} {S : List Var} {x : Var} (hx : x ∈ S) :
    (l.filter fun p => decide (p.1 ∈ S)).find? (·.1 = x) = l.find? (·.1 = x) := by
  rw [List.find?_filter]
  congr 1
  funext p
  by_cases h : p.1 = x
  · subst h; simp [hx]
  · simp [h]

/-- The declared bound of a name of `G` in the inlined program is its bound in `G`. -/
theorem boundOf_composite_G (G : Global D) (C : QCirc D) (hnew : ∀ y ∈ constNames C, y ∉ G.names)
    {x : Var} (hx : x ∈ G.names) : (composite G C).boundOf x = G.prog.boundOf x := by
  rw [boundOf_eq, boundOf_eq]
  show ((G.bounds ++ C.1.bounds.filter fun p => decide (p.1 ∈ constNames C)).find? _).map _ =
    (G.bounds.find? _).map _
  rw [List.find?_append]
  rcases hg : G.bounds.find? (·.1 = x) with _ | p
  · rw [hg, Option.none_or, List.find?_filter, List.find?_eq_none.mpr]
    · intro p _ hp
      simp only [decide_eq_true_eq] at hp
      exact hnew _ hp.1 (hp.2 ▸ hx)
  · rw [hg, Option.some_or]

/-- The declared bound of a constant of `C` in the inlined program is the one `C` declares. -/
theorem boundOf_composite_C (G : Global D) (C : QCirc D)
    (hb : ∀ p ∈ G.bounds, p.1 ∈ G.names) {y : Var} (hy : y ∈ constNames C) (hyG : y ∉ G.names) :
    (composite G C).boundOf y = C.1.boundOf y := by
  rw [boundOf_eq, boundOf_eq]
  show ((G.bounds ++ C.1.bounds.filter fun p => decide (p.1 ∈ constNames C)).find? _).map _ = _
  rw [List.find?_append, find_pairs_none (fun p hp h => hyG (by rw [← h]; exact hb p hp)),
    Option.none_or, find_pairs_filter hy]

theorem mem_constNames {C : QCirc D} {d : Decl} (hd : d ∈ C.1.inputs) (h : d.name ∉ C.2.1) :
    d.name ∈ constNames C :=
  List.mem_filter.mpr ⟨List.mem_map.mpr ⟨d, hd, rfl⟩, by simpa using h⟩

/-- **The per-input checks of the inlined program and of the query agree.** -/
theorem inputs_frame (G : Global D) (C : QCirc D) (q : Decl → Option ℕ → Bool → Bool)
    (hG : (G.inputs.all fun d => q d (G.prog.boundOf d.name) (decide (d.name ∈ G.fresh))) = true)
    (hq : ∀ x, q (freshDecl D x) none true = true)
    (hnew : ∀ y ∈ constNames C, y ∉ G.names) (hfr : ∀ x ∈ G.fresh, x ∈ G.names)
    (hb : ∀ p ∈ G.bounds, p.1 ∈ G.names)
    (hdecl : ∀ d ∈ C.1.inputs, d.name ∈ C.2.1 → d = freshDecl D d.name)
    (hbnd : ∀ x ∈ C.2.1, C.1.boundOf x = none) :
    ((composite G C).inputs.all fun d =>
        q d ((composite G C).boundOf d.name) (decide (d.name ∈ G.fresh))) =
      (C.1.inputs.all fun d => q d (C.1.boundOf d.name) (decide (d.name ∈ C.2.1))) := by
  have hc : ∀ d ∈ C.1.inputs, d.name ∉ C.2.1 →
      q d ((composite G C).boundOf d.name) (decide (d.name ∈ G.fresh)) =
        q d (C.1.boundOf d.name) (decide (d.name ∈ C.2.1)) := by
    intro d hd hn
    have hy := mem_constNames hd hn
    have hyG := hnew _ hy
    rw [boundOf_composite_C G C hb hy hyG]
    have h1 : d.name ∉ G.fresh := fun h => hyG (hfr _ h)
    simp [h1, hn]
  apply Bool.eq_iff_iff.mpr
  simp only [List.all_eq_true]
  constructor
  · intro h d hd
    by_cases hn : d.name ∈ C.2.1
    · rw [hdecl d hd hn, hbnd _ (by rw [hdecl d hd hn] at hn; exact hn)]
      have : (freshDecl D d.name).name = d.name := rfl
      simp only [this, hn, decide_true]
      exact hq _
    · rw [← hc d hd hn]
      exact h d (List.mem_append_right _ (List.mem_filter.mpr ⟨hd, by simpa using hn⟩))
  · intro h d hd
    rcases List.mem_append.mp hd with hd | hd
    · have hx : d.name ∈ G.names := List.mem_append_left _ (List.mem_map.mpr ⟨d, hd, rfl⟩)
      rw [boundOf_composite_G G C hnew hx]
      exact List.all_eq_true.mp hG d hd
    · obtain ⟨hd, hn⟩ := List.mem_filter.mp hd
      have hn' : d.name ∉ C.2.1 := by simpa using hn
      rw [hc d hd hn']
      exact h d hd

/-! ## The run of the global program inside the inlined program -/

section Run
variable (E : Trace.Budget)

/-- The initial environments of the inlined program extend those of `G`. -/
theorem rel_G_composite (G : Global D) (C : QCirc D) (hnew : ∀ y ∈ constNames C, y ∉ G.names)
    (os : List Var) :
    Rel (P := D.Pe) (initEnv D.P.src G.prog fun _ => .exact 0)
      (initEnv D.P.src { composite G C with outputs := os } fun _ => .exact 0)
      (beta0 D.Pe G.prog) (beta0 D.Pe { composite G C with outputs := os }) := by
  refine ⟨Validation.IndCpaDLM.initEnv_ext G.prog _ _ rfl _ _ fun _ _ _ => rfl, ?_,
    rel_init D.Pe G.prog⟩
  intro x v hx
  obtain ⟨d, hd, rfl⟩ := Option.map_eq_some_iff.mp hx
  obtain ⟨hdn, hdm⟩ := find_name hd
  have hxG : x ∈ G.names := List.mem_append_left _ (List.mem_map.mpr ⟨d, hdm, hdn⟩)
  have hb : ({ composite G C with outputs := os } : Program).boundOf x = G.prog.boundOf x :=
    boundOf_composite_G G C hnew hxG
  show ((G.inputs ++ C.1.inputs.filter fun d => decide (d.name ∉ C.2.1)).find? _).map _ = _
  have hd' : G.inputs.find? (·.name = x) = some d := hd
  rw [List.find?_append, hd', Option.some_or]
  simp only [Option.map_some, hb]

/-- The invariant of a reachable global program, for the BGV classes at the budget `E` with the
body check `X`. -/
def InvB (X : Program → Bool) (G : Global D) : Prop :=
  (∀ x ∈ G.fresh, x ∈ G.names ∧ x ∉ G.body.map Trace.dst ∧
    G.inputs.find? (·.name = x) = some (freshDecl D x)) ∧
  (∀ p ∈ G.bounds, p.1 ∈ G.names ∧ p.1 ∉ G.fresh) ∧
  (∃ ρg βg, refRun D.Pe E G.body (initEnv D.P.src G.prog fun _ => .exact 0) (beta0 D.Pe G.prog) =
    some (ρg, βg)) ∧
  (G.inputs.all fun d => d.ok D.P.src) = true ∧
  (G.inputs.all fun d => qFit D d (G.prog.boundOf d.name) (decide (d.name ∈ G.fresh))) = true ∧
  (G.inputs.all fun d => decide (d.name ∈ G.fresh) || decide (D.P.src.t - 1 ≤ D.eps)) = true ∧
  (G.inputs.all fun d => qMsg D d (G.prog.boundOf d.name)) = true ∧
  X G.prog = true

/-- **The run of `G.body` inside the inlined program** ends in environments that extend the
query's initial ones. -/
theorem grun {X : Program → Bool} {G : Global D} (hG : InvB E X G) (C : QCirc D)
    (hnew : ∀ y ∈ constNames C, y ∉ G.names) (hfr : ∀ x ∈ C.2.1, x ∈ G.fresh)
    (hdecl : ∀ d ∈ C.1.inputs, d.name ∈ C.2.1 → d = freshDecl D d.name)
    (hbnd : ∀ x ∈ C.2.1, C.1.boundOf x = none) (os : List Var) :
    ∃ ρg βg, refRun D.Pe E G.body
        (initEnv D.P.src { composite G C with outputs := os } fun _ => .exact 0)
        (beta0 D.Pe { composite G C with outputs := os }) = some (ρg, βg) ∧
      Ext (initEnv D.P.src C.1 fun _ => .exact 0) ρg ∧ Ext (beta0 D.Pe C.1) βg := by
  obtain ⟨hfresh, hbG, ⟨ρ0, β0, hrun⟩, -⟩ := hG
  have hfold := refRun_fold _ _ _ _ _ hrun
  rcases refRun_frame (E := E) G.body _ _ ρ0 _ _ hfold (rel_G_composite G C hnew os) with
    ⟨h1, -⟩ | ⟨β0', ρg, βg, h1, h2, hr⟩
  · rw [hrun] at h1; cases h1
  rw [hrun] at h1
  cases h1
  refine ⟨ρg, βg, h2, ?_, ?_⟩
  · intro y v hy
    obtain ⟨d, hd, rfl⟩ := Option.map_eq_some_iff.mp hy
    obtain ⟨hdn, hdm⟩ := find_name hd
    by_cases hyC : y ∈ C.2.1
    · obtain ⟨-, hnd, hfind⟩ := hfresh y (hfr y hyC)
      have hdf := hdecl d hdm (hdn ▸ hyC)
      apply hr.1
      rw [(refRun_nodst _ _ _ _ _ hrun y hnd).1]
      show (G.inputs.find? (·.name = y)).map _ = _
      rw [hfind, hdf]
      subst hdn; rfl
    · have hc := mem_constNames hdm (hdn ▸ hyC)
      rw [hdn] at hc
      have hyG := hnew y hc
      have hnd : y ∉ G.body.map Trace.dst := fun h => hyG (List.mem_append_right _ h)
      rw [(refRun_nodst _ _ _ _ _ h2 y hnd).1]
      show ((G.inputs ++ C.1.inputs.filter fun d => decide (d.name ∉ C.2.1)).find? _).map _ = _
      rw [List.find?_append, find_none (fun h => hyG (List.mem_append_left _ h)), Option.none_or,
        Validation.IndCpaDLM.find_filter_eq hyC, hd]
      rfl
  · intro y v hy
    obtain ⟨d, hd, rfl⟩ := Option.map_eq_some_iff.mp hy
    obtain ⟨hdn, hdm⟩ := find_name hd
    by_cases hyC : y ∈ C.2.1
    · obtain ⟨-, hnd, hfind⟩ := hfresh y (hfr y hyC)
      apply hr.2.1
      rw [(refRun_nodst _ _ _ _ _ hrun y hnd).2]
      have hb1 : C.1.boundOf y = none := hbnd y hyC
      have hb2 : G.prog.boundOf y = none := by
        rw [boundOf_eq, find_pairs_none]; rfl
        intro p hp hpy; exact (hbG p hp).2 (hpy ▸ hfr y hyC)
      show (G.inputs.find? (·.name = y)).map _ = _
      rw [hfind]
      simp only [Option.map_some, hb1, hb2]
    · have hc := mem_constNames hdm (hdn ▸ hyC)
      rw [hdn] at hc
      have hyG := hnew y hc
      have hnd : y ∉ G.body.map Trace.dst := fun h => hyG (List.mem_append_right _ h)
      rw [(refRun_nodst _ _ _ _ _ h2 y hnd).2]
      have hb : ({ composite G C with outputs := os } : Program).boundOf y = C.1.boundOf y :=
        boundOf_composite_C G C (fun p hp => (hbG p hp).1) hc hyG
      show ((G.inputs ++ C.1.inputs.filter fun d => decide (d.name ∉ C.2.1)).find? _).map _ = _
      rw [List.find?_append, find_none (fun h => hyG (List.mem_append_left _ h)), Option.none_or,
        Validation.IndCpaDLM.find_filter_eq hyC, hd]
      simp only [Option.map_some, hb]

/-! ## The body checks of the classes -/

/-- What the body check `X` of a class must satisfy: it does not read the outputs, it holds for
the empty body, it is kept by extending the inputs, and on a body `pre ++ S.body` whose `pre`
part passed it equals the check of `S` alone. -/
def XProp (P : FullParams) (X : Program → Bool) : Prop :=
  (∀ (prog : Program) os, X { prog with outputs := os } = X prog) ∧
  (∀ prog : Program, prog.body = [] → X prog = true) ∧
  (∀ K₀ K : Program, K.body = K₀.body →
    Ext (initEnv P.src K₀ fun _ => .exact 0) (initEnv P.src K fun _ => .exact 0) →
    (K₀.body.foldlM (step P.src) (initEnv P.src K₀ fun _ => .exact 0)).isSome →
    X K₀ = true → X K = true) ∧
  (∀ (K₀ K S : Program) (ρg : Env P.src), K.body = K₀.body ++ S.body →
    Ext (initEnv P.src K₀ fun _ => .exact 0) (initEnv P.src K fun _ => .exact 0) →
    (K₀.body.foldlM (step P.src) (initEnv P.src K₀ fun _ => .exact 0)).isSome →
    K₀.body.foldlM (step P.src) (initEnv P.src K fun _ => .exact 0) = some ρg →
    Ext (initEnv P.src S fun _ => .exact 0) ρg →
    (S.body.foldlM (step P.src) (initEnv P.src S fun _ => .exact 0)).isSome →
    X K₀ = true → X K = X S)

theorem xprop_true (P : FullParams) : XProp P fun _ => true :=
  ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ _ _ _ _ => rfl, fun _ _ _ _ _ _ _ _ _ _ _ => rfl⟩

theorem exactOnly_eq (b : List Instr) :
    Challenge.IndCpaDProfile.exactOnly b = b.all Challenge.IndCpaDProfile.exactInstr := rfl

theorem xprop_exact (P : FullParams) :
    XProp P fun p => Challenge.IndCpaDProfile.exactOnly p.body := by
  refine ⟨fun _ _ => rfl, fun p h => ?_, fun K₀ K h _ _ hx => ?_,
    fun K₀ K S ρg h _ _ _ _ _ hx => ?_⟩ <;> dsimp only at *
  · rw [h]; rfl
  · rw [h]; exact hx
  · rw [exactOnly_eq] at hx ⊢
    rw [h, List.all_append, hx, Bool.true_and, exactOnly_eq]

theorem xprop_ks (P : FullParams) (lay : Budget.KSLayout) (rots : List ℕ) (E : Trace.Budget) :
    XProp P fun p => Challenge.IndCpaDProfile.ksNeed P lay rots E p.body
      (initEnv P.src p fun _ => .exact 0) := by
  have hl := ksNeedAt_local P lay rots E
  refine ⟨fun _ _ => rfl, fun p h => ?_, fun K₀ K h he hf hx => ?_,
    fun K₀ K S ρg h he hf hg hS hSf hx => ?_⟩ <;> dsimp only at *
  · rw [h]; rfl
  · obtain ⟨ρf, hρf⟩ := Option.isSome_iff_exists.mp hf
    rw [ksNeed_eq] at hx ⊢
    rw [h, ← needFold_frame hl _ _ _ ρf hρf he]; exact hx
  · obtain ⟨ρf, hρf⟩ := Option.isSome_iff_exists.mp hf
    obtain ⟨ρS, hρS⟩ := Option.isSome_iff_exists.mp hSf
    rw [ksNeed_eq] at hx ⊢
    rw [ksNeed_eq, h, needFold_append _ _ _ _ _ hg, ← needFold_frame hl _ _ _ ρf hρf he, hx,
      Bool.true_and, ← needFold_frame hl _ _ _ ρS hρS hS]

/-! ## Agreement, BGV -/

theorem admBGV_eq (E : Trace.Budget) (C : D.Circ) :
    admBGV D (fun _ => E) C =
      ((Challenge.Profile.certifyProfile? D.Pe E (D.prog C) false).isSome && D.inputsFit C &&
        (D.prog C).inputs.all fun d =>
          decide (d.name ∈ D.fresh C) || decide (D.P.src.t - 1 ≤ D.eps)) := rfl

theorem admBGV_eval {E : Trace.Budget} {C : D.Circ} (h : admBGV D (fun _ => E) C = true) :
    (Source.eval D.P.src (D.prog C) fun _ => .exact 0).isSome := by
  rw [admBGV_eq] at h
  simp only [Bool.and_eq_true, Option.isSome_iff_exists] at h
  obtain ⟨⟨⟨r, hr⟩, -⟩, -⟩ := h
  obtain ⟨B, hB⟩ := certifyProfile_analyze hr
  exact refAnalyze_eval (P := D.Pe) hB

/-- **Agreement, BGV, any body check `X` with `XProp`.** -/
theorem agree_bgv (E : Trace.Budget) (X : Program → Bool) (hX : XProp D.P X)
    (mk : Program → List Var → (Var → M D) → D.Circ)
    (hmk : ∀ p f c, D.prog (mk p f c) = p ∧ D.fresh (mk p f c) = f ∧ D.pt (mk p f c) = c)
    (hfd : ∀ x, (freshDecl D x).ok D.P.src = true) (hmf : D.P.src.t < D.P.src.modulus D.lvl)
    {G : Global D} (hG : InvB E X G) (C : QCirc D) (en : List (Var × Bool))
    (hen : C.2.1 = en.map (·.1)) (hl : en.all (·.2) = true) (hfr : ∀ x ∈ C.2.1, x ∈ G.fresh)
    (hnew : ∀ x ∈ constNames C ++ C.1.body.map Trace.dst, x ∉ G.names)
    (hdecl : ∀ d ∈ C.1.inputs, d.name ∈ C.2.1 → d = freshDecl D d.name)
    (hbnd : ∀ x ∈ C.2.1, C.1.boundOf x = none) :
    admLM mk (fun C' => admBGV D (fun _ => E) C' && X (D.prog C')) G C en =
      (admBGV D (fun _ => E) (mk C.1 C.2.1 C.2.2) && X C.1) := by
  have hnewc : ∀ y ∈ constNames C, y ∉ G.names := fun y hy => hnew y (List.mem_append_left _ hy)
  have hG' := hG
  obtain ⟨hfresh, hbG, ⟨ρ0, β0, hrun⟩, hGok, hGfit, hGconst, hGmsg, hGX⟩ := hG'
  have hfrn : ∀ x ∈ G.fresh, x ∈ G.names := fun x hx => (hfresh x hx).1
  have hbn : ∀ p ∈ G.bounds, p.1 ∈ G.names := fun p hp => (hbG p hp).1
  obtain ⟨ρg, βg, hgr, he1, he2⟩ := grun E hG C hnewc hfr hdecl hbnd C.1.outputs
  have hfold0 := refRun_fold _ _ _ _ _ hrun
  have hfoldg := refRun_fold _ _ _ _ _ hgr
  have hok := inputs_frame G C (fun d _ _ => d.ok D.P.src) hGok (fun x => hfd x) hnewc hfrn hbn
    hdecl hbnd
  have hfit := inputs_frame G C (qFit D) hGfit (fun x => by simp [qFit, freshDecl]) hnewc hfrn
    hbn hdecl hbnd
  have hconst := inputs_frame G C
    (fun _ _ fr => fr || decide (D.P.src.t - 1 ≤ D.eps)) hGconst (fun x => rfl) hnewc hfrn hbn
    hdecl hbnd
  have hmsg0 := inputs_frame G C (fun d bnd _ => qMsg D d bnd) hGmsg
    (fun x => by simp [qMsg, freshDecl, hmf]) hnewc hfrn hbn hdecl hbnd
  have hmsg : Challenge.Certify.inputsMsgOK? D.Pe (composite G C) =
      Challenge.Certify.inputsMsgOK? D.Pe C.1 := by
    rw [inputsMsgOK_eq, inputsMsgOK_eq]; exact hmsg0
  -- the checks of `admLM` that hold
  have c1 : decide (C.2.1 = en.map (·.1)) = true := by simp [hen]
  have c3 : ((constNames C ++ C.1.body.map Trace.dst).all fun x => decide (x ∉ G.names)) = true :=
    List.all_eq_true.mpr fun x hx => by simpa using hnew x hx
  have c5 : G.replay.elim false (fun ρ => C.1.inputs.all fun d =>
      decide (d.name ∉ C.2.1) || metaOK ρ d) = true := by
    have : G.replay = some ρ0 := hfold0
    rw [this]
    show (C.1.inputs.all fun d => decide (d.name ∉ C.2.1) || metaOK ρ0 d) = true
    refine List.all_eq_true.mpr fun d hd => ?_
    by_cases hn : d.name ∈ C.2.1
    · obtain ⟨-, hnd, hfind⟩ := hfresh _ (hfr _ hn)
      have hv := Validation.IndCpaDLM.foldl_nodst _ _ _ hfold0 d.name hnd
      have hdf := hdecl d hd hn
      have : ρ0 d.name = some ⟨.exact 0, 2, D.lvl, 1, 0⟩ := by
        rw [hv]
        show (G.inputs.find? (·.name = d.name)).map _ = _
        rw [hfind]; rfl
      simp only [metaOK, this, Option.elim_some]
      rw [hdf]; simp [freshDecl]
    · simp [hn]
  unfold admLM
  rw [c1, hl, c3, c5]
  simp only [Bool.true_and, Bool.and_true]
  beta_reduce at hok hconst
  obtain ⟨-, -, -, hX4⟩ := hX
  by_cases h4 : (Source.eval D.P.src C.1 fun _ => .exact 0).isSome
  · have hcert := certifyProfile_frame (P := D.Pe) (E := E) (composite G C) C.1 G.body rfl rfl
      hok hmsg ρg βg hgr ⟨he1, he2⟩ h4
    obtain ⟨ρC, hρC⟩ := Option.isSome_iff_exists.mp h4
    obtain ⟨-, hCf, -⟩ := Validation.IndCpaDLM.eval_parts hρC
    have hXe : X (composite G C) = X C.1 :=
      hX4 G.prog (composite G C) C.1 ρg rfl (rel_G_composite G C hnewc C.1.outputs).1
        (by rw [show G.prog.body = G.body from rfl, hfold0]; rfl) hfoldg he1 (by rw [hCf]; rfl)
        hGX
    have hadm : admBGV D (fun _ => E) (mk (composite G C) G.fresh (G.extend C).pt) =
        admBGV D (fun _ => E) (mk C.1 C.2.1 C.2.2) := by
      rw [admBGV_eq, admBGV_eq, inputsFit_eq, inputsFit_eq, (hmk (composite G C) _ _).1,
        (hmk (composite G C) _ _).2.1, (hmk C.1 _ _).1, (hmk C.1 _ _).2.1, hcert, hfit, hconst]
    rw [h4, hadm, (hmk (composite G C) _ _).1, hXe, Bool.true_and]
    cases hS : admBGV D (fun _ => E) (mk C.1 C.2.1 C.2.2)
    · simp
    · have h6 := admBGV_eval (hadm.trans hS)
      rw [(hmk _ _ _).1] at h6
      rw [h6]; simp
  · have hS : admBGV D (fun _ => E) (mk C.1 C.2.1 C.2.2) = false := by
      by_contra h
      have h6 := admBGV_eval (Bool.eq_true_of_not_eq_false h)
      rw [(hmk _ _ _).1] at h6
      exact h4 h6
    rw [Bool.eq_false_iff.mpr h4, hS]; simp

/-! ## Reachable global programs satisfy the invariant -/

theorem rel_prefix (P : FullParams) (p p' : Program) (more : List Decl)
    (hin : p'.inputs = p.inputs ++ more) (hb : p'.bounds = p.bounds) :
    Rel (P := P) (initEnv P.src p fun _ => .exact 0) (initEnv P.src p' fun _ => .exact 0)
      (beta0 P p) (beta0 P p') := by
  refine ⟨Validation.IndCpaDLM.initEnv_ext p p' more hin _ _ fun _ _ _ => rfl, ?_, rel_init P p⟩
  intro x v hx
  obtain ⟨d, hd, rfl⟩ := Option.map_eq_some_iff.mp hx
  have hbo : p'.boundOf x = p.boundOf x := by rw [boundOf_eq, boundOf_eq, hb]
  show (p'.inputs.find? (·.name = x)).map _ = _
  rw [hin, List.find?_append, hd, Option.some_or]
  simp only [Option.map_some, hbo]

theorem reach_inv (E : Trace.Budget) (X : Program → Bool) (hX : XProp D.P X)
    (mk : Program → List Var → (Var → M D) → D.Circ)
    (hmk : ∀ p f c, D.prog (mk p f c) = p ∧ D.fresh (mk p f c) = f ∧ D.pt (mk p f c) = c)
    (hfd : ∀ x, (freshDecl D x).ok D.P.src = true) (hmf : D.P.src.t < D.P.src.modulus D.lvl)
    {G : Global D}
    (hR : Reach mk (fun C' => admBGV D (fun _ => E) C' && X (D.prog C')) G) : InvB E X G := by
  induction hR with
  | empty =>
    refine ⟨fun x hx => by simp [Global.empty] at hx, fun p hp => by simp [Global.empty] at hp,
      ⟨_, _, rfl⟩, rfl, rfl, rfl, rfl, hX.2.1 _ rfl⟩
  | link G x _ ih =>
    by_cases hx : x ∈ G.names
    · have : G.link x = G := by unfold Global.link; rw [if_pos hx]
      rw [this]; exact ih
    have hG' : G.link x =
        { G with inputs := G.inputs ++ [freshDecl D x], fresh := G.fresh ++ [x] } := by
      unfold Global.link; rw [if_neg hx]
    rw [hG']
    obtain ⟨hfresh, hbG, ⟨ρ0, β0, hrun⟩, hok, hfit, hconst, hmsgG, hXG⟩ := ih
    have hxin : x ∉ G.inputs.map (·.name) := fun h => hx (List.mem_append_left _ h)
    have hrel := rel_prefix D.Pe G.prog
      ({ G with inputs := G.inputs ++ [freshDecl D x], fresh := G.fresh ++ [x] } : Global D).prog
      [freshDecl D x] rfl rfl
    have hfold := refRun_fold _ _ _ _ _ hrun
    have hnm : ∀ d ∈ G.inputs, d.name ≠ x := fun d hd h =>
      hxin (List.mem_map.mpr ⟨d, hd, h⟩)
    have hbx : G.prog.boundOf x = none := by
      rw [boundOf_eq, find_pairs_none]; rfl
      intro p hp hpx; exact hx (hpx ▸ (hbG p hp).1)
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro y hy
      rcases List.mem_append.mp hy with hy | hy
      · obtain ⟨h1, h2, h3⟩ := hfresh y hy
        refine ⟨?_, h2, ?_⟩
        · unfold Global.names at h1 ⊢
          simp only [List.map_append, List.mem_append] at h1 ⊢; tauto
        · show (G.inputs ++ [freshDecl D x]).find? _ = _
          rw [List.find?_append, h3, Option.some_or]
      · simp only [List.mem_singleton] at hy; subst hy
        refine ⟨by unfold Global.names; simp [freshDecl], fun h => hx (List.mem_append_right _ h),
          ?_⟩
        show (G.inputs ++ [freshDecl D y]).find? _ = _
        rw [List.find?_append, find_none hxin, Option.none_or]; simp [freshDecl]
    · intro p hp
      obtain ⟨h1, h2⟩ := hbG p hp
      refine ⟨?_, ?_⟩
      · unfold Global.names at h1 ⊢
        simp only [List.map_append, List.mem_append] at h1 ⊢; tauto
      · simp only [List.mem_append, List.mem_singleton, not_or]
        exact ⟨h2, fun h => hx (h ▸ h1)⟩
    · rcases refRun_frame (E := E) G.body _ _ ρ0 _ _ hfold hrel with ⟨h1, -⟩ | ⟨-, ρ₂, β₂, -, h2, -⟩
      · rw [hrun] at h1; cases h1
      · exact ⟨ρ₂, β₂, h2⟩
    · show ((G.inputs ++ [freshDecl D x]).all fun d => d.ok D.P.src) = true
      rw [List.all_append, hok, Bool.true_and]; simp [hfd x]
    · show ((G.inputs ++ [freshDecl D x]).all fun d =>
        qFit D d (G.prog.boundOf d.name) (decide (d.name ∈ G.fresh ++ [x]))) = true
      rw [List.all_append, List.all_eq_true.mpr fun d hd => ?_, Bool.true_and]
      · simp [qFit, freshDecl, hbx]
      · have := List.all_eq_true.mp hfit d hd
        have h' : decide (d.name ∈ G.fresh ++ [x]) = decide (d.name ∈ G.fresh) := by
          simp [hnm d hd]
        rw [h']; exact this
    · show ((G.inputs ++ [freshDecl D x]).all fun d =>
        decide (d.name ∈ G.fresh ++ [x]) || decide (D.P.src.t - 1 ≤ D.eps)) = true
      rw [List.all_append, List.all_eq_true.mpr fun d hd => ?_, Bool.true_and]
      · simp [freshDecl]
      · have := List.all_eq_true.mp hconst d hd
        have h' : decide (d.name ∈ G.fresh ++ [x]) = decide (d.name ∈ G.fresh) := by
          simp [hnm d hd]
        rw [h']; exact this
    · show ((G.inputs ++ [freshDecl D x]).all fun d => qMsg D d (G.prog.boundOf d.name)) = true
      rw [List.all_append, hmsgG, Bool.true_and]
      simp [qMsg, freshDecl, hbx, hmf]
    · exact hX.2.2.1 G.prog _ rfl hrel.1 (by rw [show G.prog.body = G.body from rfl, hfold]; rfl)
        hXG
  | extend G C en _ hadm ih =>
    obtain ⟨hfresh, hbG, -, -, -, -, -, -⟩ := ih
    unfold admLM at hadm
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hadm
    obtain ⟨⟨⟨⟨⟨⟨-, -⟩, a3⟩, -⟩, -⟩, -⟩, ⟨a7, a8⟩⟩ := hadm
    have hnew : ∀ x ∈ constNames C ++ C.1.body.map Trace.dst, x ∉ G.names := fun x hx => by
      have := List.all_eq_true.mp a3 x hx; simpa using this
    rw [admBGV_eq, inputsFit_eq, (hmk _ _ _).1, (hmk _ _ _).2.1] at a7
    rw [(hmk _ _ _).1] at a8
    simp only [Bool.and_eq_true, Option.isSome_iff_exists] at a7
    obtain ⟨⟨⟨r, hr⟩, hfit⟩, hconst⟩ := a7
    obtain ⟨B, hB⟩ := certifyProfile_analyze hr
    have hok := refAnalyze_ok hB
    have hmsgN := certifyProfile_msg hr
    rw [inputsMsgOK_eq] at hmsgN
    obtain ⟨ρ, β, hrun⟩ := refAnalyze_run hB
    refine ⟨?_, ?_, ⟨ρ, β, hrun⟩, hok, hfit, hconst, hmsgN, ?_⟩
    · intro y hy
      obtain ⟨h1, h2, h3⟩ := hfresh y hy
      refine ⟨Validation.IndCpaDLM.names_extend h1, ?_, ?_⟩
      · show y ∉ (G.body ++ C.1.body).map Trace.dst
        rw [List.map_append]
        exact fun h => (List.mem_append.mp h).elim h2
          fun h' => hnew y (List.mem_append_right _ h') h1
      · show (G.inputs ++ _).find? _ = _
        rw [List.find?_append, h3, Option.some_or]
    · intro p hp
      rcases List.mem_append.mp hp with hp | hp
      · exact ⟨Validation.IndCpaDLM.names_extend (hbG p hp).1, (hbG p hp).2⟩
      · obtain ⟨-, hpc⟩ := List.mem_filter.mp hp
        have hpc' : p.1 ∈ constNames C := by simpa using hpc
        refine ⟨?_, fun h => hnew _ (List.mem_append_left _ hpc')
          ((hfresh _ h).1)⟩
        unfold constNames at hpc'
        obtain ⟨hm, hn⟩ := List.mem_filter.mp hpc'
        obtain ⟨d, hd, hdn⟩ := List.mem_map.mp hm
        unfold Global.names
        simp only [Global.extend, List.map_append, List.mem_append]
        left; right
        exact List.mem_map.mpr ⟨d, List.mem_filter.mpr ⟨hd, by rw [hdn]; exact hn⟩, hdn⟩
    · exact (hX.1 _ C.1.outputs).symm.trans a8

end Run

/-! ## The locked statements, BGV -/

theorem admLM_fresh_bgv (D : AbsScheme) (mk : Program → List Var → (Var → M D) → D.Circ)
    (hmk : ∀ p f c, D.prog (mk p f c) = p ∧ D.fresh (mk p f c) = f ∧ D.pt (mk p f c) = c)
    (E : Trace.Budget) (hfd : ∀ x, (freshDecl D x).ok D.P.src = true)
    (hmf : D.P.src.t < D.P.src.modulus D.lvl) (G : Global D)
    (hG : Reach mk (admBGV D fun _ => E) G) (C : QCirc D) (en : List (Var × Bool))
    (hen : C.2.1 = en.map (·.1)) (hl : en.all (·.2) = true) (hfr : ∀ x ∈ C.2.1, x ∈ G.fresh)
    (hnew : ∀ x ∈ constNames C ++ C.1.body.map Trace.dst, x ∉ G.names)
    (hdecl : ∀ d ∈ C.1.inputs, d.name ∈ C.2.1 → d = freshDecl D d.name)
    (hbnd : ∀ x ∈ C.2.1, C.1.boundOf x = none) :
    admLM mk (admBGV D fun _ => E) G C en = admBGV D (fun _ => E) (mk C.1 C.2.1 C.2.2) := by
  have hc : (admBGV D fun _ => E) = fun C' => admBGV D (fun _ => E) C' && (fun _ => true) (D.prog C') :=
    funext fun C' => (Bool.and_true _).symm
  rw [hc] at hG ⊢
  rw [agree_bgv E _ (xprop_true D.P) mk hmk hfd hmf (reach_inv E _ (xprop_true D.P) mk hmk hfd hmf hG) C en
    hen hl hfr hnew hdecl hbnd]

theorem admLM_fresh_exact (D : AbsScheme) (mk : Program → List Var → (Var → M D) → D.Circ)
    (hmk : ∀ p f c, D.prog (mk p f c) = p ∧ D.fresh (mk p f c) = f ∧ D.pt (mk p f c) = c)
    (E : Trace.Budget) (hfd : ∀ x, (freshDecl D x).ok D.P.src = true)
    (hmf : D.P.src.t < D.P.src.modulus D.lvl) (G : Global D)
    (hG : Reach mk (exactClass D fun _ => E) G) (C : QCirc D) (en : List (Var × Bool))
    (hen : C.2.1 = en.map (·.1)) (hl : en.all (·.2) = true) (hfr : ∀ x ∈ C.2.1, x ∈ G.fresh)
    (hnew : ∀ x ∈ constNames C ++ C.1.body.map Trace.dst, x ∉ G.names)
    (hdecl : ∀ d ∈ C.1.inputs, d.name ∈ C.2.1 → d = freshDecl D d.name)
    (hbnd : ∀ x ∈ C.2.1, C.1.boundOf x = none) :
    admLM mk (exactClass D fun _ => E) G C en = exactClass D (fun _ => E) (mk C.1 C.2.1 C.2.2) := by
  have hc : (exactClass D fun _ => E) = fun C' => admBGV D (fun _ => E) C' &&
      (fun p => Challenge.IndCpaDProfile.exactOnly p.body) (D.prog C') := rfl
  rw [hc] at hG ⊢
  rw [agree_bgv E _ (xprop_exact D.P) mk hmk hfd hmf (reach_inv E _ (xprop_exact D.P) mk hmk hfd hmf hG) C
    en hen hl hfr hnew hdecl hbnd]
  beta_reduce
  rw [(hmk _ _ _).1]

theorem admLM_fresh_ks (D : AbsScheme) (mk : Program → List Var → (Var → M D) → D.Circ)
    (hmk : ∀ p f c, D.prog (mk p f c) = p ∧ D.fresh (mk p f c) = f ∧ D.pt (mk p f c) = c)
    (lay : Budget.KSLayout) (rots : List ℕ) (E : Trace.Budget)
    (hfd : ∀ x, (freshDecl D x).ok D.P.src = true) (hmf : D.P.src.t < D.P.src.modulus D.lvl)
    (G : Global D)
    (hG : Reach mk (ksClass D lay rots fun _ => E) G) (C : QCirc D) (en : List (Var × Bool))
    (hen : C.2.1 = en.map (·.1)) (hl : en.all (·.2) = true) (hfr : ∀ x ∈ C.2.1, x ∈ G.fresh)
    (hnew : ∀ x ∈ constNames C ++ C.1.body.map Trace.dst, x ∉ G.names)
    (hdecl : ∀ d ∈ C.1.inputs, d.name ∈ C.2.1 → d = freshDecl D d.name)
    (hbnd : ∀ x ∈ C.2.1, C.1.boundOf x = none) :
    admLM mk (ksClass D lay rots fun _ => E) G C en =
      ksClass D lay rots (fun _ => E) (mk C.1 C.2.1 C.2.2) := by
  have hcls : ∀ C', ksClass D lay rots (fun _ => E) C' = (admBGV D (fun _ => E) C' &&
      Challenge.IndCpaDProfile.ksSide D.Pe lay && Challenge.IndCpaDProfile.ksNeed D.Pe lay rots E
        (D.prog C').body (initEnv D.P.src (D.prog C') fun _ => .exact 0)) := fun _ => rfl
  cases hside : Challenge.IndCpaDProfile.ksSide D.Pe lay
  · have hf : (ksClass D lay rots fun _ => E) = fun _ => false :=
      funext fun C' => by rw [hcls, hside]; simp
    rw [hf]
    unfold admLM; simp
  · have hc : (ksClass D lay rots fun _ => E) = fun C' => admBGV D (fun _ => E) C' &&
        (fun p => Challenge.IndCpaDProfile.ksNeed D.Pe lay rots E p.body
          (initEnv D.P.src p fun _ => .exact 0)) (D.prog C') :=
      funext fun C' => by rw [hcls, hside, Bool.and_true]
    rw [hc] at hG ⊢
    have hXk : XProp D.P fun p => Challenge.IndCpaDProfile.ksNeed D.Pe lay rots E p.body
        (initEnv D.P.src p fun _ => .exact 0) := xprop_ks D.Pe lay rots E
    rw [agree_bgv E _ hXk mk hmk hfd hmf (reach_inv E _ hXk mk hmk hfd hmf hG) C en hen hl hfr hnew hdecl
      hbnd]
    beta_reduce
    rw [(hmk _ _ _).1]

example := (@admLM_fresh_bgv : type_of% @Challenge.IndCpaDLM.admLM_fresh_bgv)
example := (@admLM_fresh_exact : type_of% @Challenge.IndCpaDLM.admLM_fresh_exact)
example := (@admLM_fresh_ks : type_of% @Challenge.IndCpaDLM.admLM_fresh_ks)

end Validation.IndCpaDLM
