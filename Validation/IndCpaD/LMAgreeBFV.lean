import Validation.IndCpaD.LMAgree
import Validation.IndCpaD.LMBFV

/-!
# Validation.IndCpaD.LMAgreeBFV — agreement on fresh entries for the BFV classes

The proof of `Validation.IndCpaD.LMAgree` for the BFV profile class (`certifyBFVProfile?` at a
constant per-instruction budget, `refRunBFV` by `refRunAt_const`) and for `bfvClass`.
-/

namespace Validation.IndCpaDLM
open Spec NPoly Scheme Source Spec.IndCpaD Spec.IndCpaDProfile Spec.IndCpaDLM
  Challenge.IndCpaDProfile Challenge.Headline Challenge.BFV
open Spec.TraceBFV (Bnd)
open Validation.IndCpaDLM (Ext ext_refl ext_trans find_name find_none)
open Validation.IndCpaDFrame

variable {D : AbsScheme}

/-- The decryption check of `Challenge.Profile.inputsDecOK` for one declaration, with its
declared bound. -/
def qDec (D : AbsScheme) (d : Decl) (bnd : Option ℕ) : Bool :=
  decide (d.parts = 1) || !d.ok D.P.src ||
    decOK D.P.src.t (D.P.src.modulus d.level)
      (bnd.getD (if d.parts = 1 then D.P.src.t - 1 else D.eps))

/-- The plaintext-bound check of `Challenge.CertifyBFV.plainBoundsOK` for one declaration. -/
def qPlain (D : AbsScheme) (d : Decl) (bnd : Option ℕ) : Bool :=
  decide (d.parts ≠ 1) ||
    decide (D.P.src.t / 2 ≤ bnd.getD (if d.parts = 1 then D.P.src.t - 1 else D.eps))

theorem plainBoundsOK_eq (prog : Program) :
    Challenge.CertifyBFV.plainBoundsOK D.Pe prog =
      prog.inputs.all fun d => qPlain D d (prog.boundOf d.name) := rfl

theorem certifyBFV_plain {P : FullParams} {E : TraceBFV.Budget} {prog : Program}
    {r : ℕ × List (Var × ℕ)} (h : Challenge.Profile.certifyBFVProfile? P (fun _ => E) prog = some r) :
    Challenge.CertifyBFV.plainBoundsOK P prog = true := by
  rw [certifyBFVProfile_eq] at h
  by_contra hc
  simp [hc, guard] at h

theorem inputsDecOK_eq (prog : Program) :
    Challenge.Profile.inputsDecOK D.Pe prog =
      prog.inputs.all fun d => qDec D d (prog.boundOf d.name) := rfl

theorem rel_prefixB (P : FullParams) (p p' : Program) (more : List Decl)
    (hin : p'.inputs = p.inputs ++ more) (hb : p'.bounds = p.bounds) :
    Rel (P := P) (initEnv P.src p fun _ => .exact 0) (initEnv P.src p' fun _ => .exact 0)
      (beta0B P p) (beta0B P p') := by
  refine ⟨Validation.IndCpaDLM.initEnv_ext p p' more hin _ _ fun _ _ _ => rfl, ?_, rel_initB P p⟩
  intro x v hx
  obtain ⟨d, hd, rfl⟩ := Option.map_eq_some_iff.mp hx
  have hbo : p'.boundOf d.name = p.boundOf d.name := by rw [boundOf_eq, boundOf_eq, hb]
  show (p'.inputs.find? (·.name = x)).map _ = _
  rw [hin, List.find?_append, hd, Option.some_or]
  simp only [Option.map_some, TraceBFV.inputBound, hbo]

section Run
variable (E : TraceBFV.Budget)


/-- The initial environments of the inlined program extend those of `G`. -/
theorem rel_G_compositeB (G : Global D) (C : QCirc D) (hnew : ∀ y ∈ constNames C, y ∉ G.names)
    (os : List Var) :
    Rel (P := D.Pe) (initEnv D.P.src G.prog fun _ => .exact 0)
      (initEnv D.P.src { composite G C with outputs := os } fun _ => .exact 0)
      (beta0B D.Pe G.prog) (beta0B D.Pe { composite G C with outputs := os }) := by
  refine ⟨Validation.IndCpaDLM.initEnv_ext G.prog _ _ rfl _ _ fun _ _ _ => rfl, ?_,
    rel_initB D.Pe G.prog⟩
  intro x v hx
  obtain ⟨d, hd, rfl⟩ := Option.map_eq_some_iff.mp hx
  obtain ⟨hdn, hdm⟩ := find_name hd
  have hxG : x ∈ G.names := List.mem_append_left _ (List.mem_map.mpr ⟨d, hdm, hdn⟩)
  have hb : ({ composite G C with outputs := os } : Program).boundOf d.name =
      G.prog.boundOf d.name := hdn ▸ boundOf_composite_G G C hnew hxG
  show ((G.inputs ++ C.1.inputs.filter fun d => decide (d.name ∉ C.2.1)).find? _).map _ = _
  have hd' : G.inputs.find? (·.name = x) = some d := hd
  rw [List.find?_append, hd', Option.some_or]
  simp only [Option.map_some, TraceBFV.inputBound, hb]

/-- The invariant of a reachable global program, for the BFV classes at the budget `E` with the
body check `X`. -/
def InvF (X : Program → Bool) (G : Global D) : Prop :=
  (∀ x ∈ G.fresh, x ∈ G.names ∧ x ∉ G.body.map Trace.dst ∧
    G.inputs.find? (·.name = x) = some (freshDecl D x)) ∧
  (∀ p ∈ G.bounds, p.1 ∈ G.names ∧ p.1 ∉ G.fresh) ∧
  (∃ ρg βg, refRunBFV D.Pe E G.body (initEnv D.P.src G.prog fun _ => .exact 0) (beta0B D.Pe G.prog) =
    some (ρg, βg)) ∧
  (G.inputs.all fun d => d.ok D.P.src) = true ∧
  (G.inputs.all fun d => qFit D d (G.prog.boundOf d.name) (decide (d.name ∈ G.fresh))) = true ∧
  (G.inputs.all fun d => qDec D d (G.prog.boundOf d.name)) = true ∧
  (G.inputs.all fun d => qPlain D d (G.prog.boundOf d.name)) = true ∧
  X G.prog = true

/-- **The run of `G.body` inside the inlined program** ends in environments that extend the
query's initial ones. -/
theorem grunB {X : Program → Bool} {G : Global D} (hG : InvF E X G) (C : QCirc D)
    (hnew : ∀ y ∈ constNames C, y ∉ G.names) (hfr : ∀ x ∈ C.2.1, x ∈ G.fresh)
    (hdecl : ∀ d ∈ C.1.inputs, d.name ∈ C.2.1 → d = freshDecl D d.name)
    (hbnd : ∀ x ∈ C.2.1, C.1.boundOf x = none) (os : List Var) :
    ∃ ρg βg, refRunBFV D.Pe E G.body
        (initEnv D.P.src { composite G C with outputs := os } fun _ => .exact 0)
        (beta0B D.Pe { composite G C with outputs := os }) = some (ρg, βg) ∧
      Ext (initEnv D.P.src C.1 fun _ => .exact 0) ρg ∧ Ext (beta0B D.Pe C.1) βg := by
  obtain ⟨hfresh, hbG, ⟨ρ0, β0, hrun⟩, -⟩ := hG
  have hfold := refRunBFV_fold _ _ _ _ _ hrun
  rcases refRunBFV_frame (E := E) G.body _ _ ρ0 _ _ hfold (rel_G_compositeB G C hnew os) with
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
      rw [(refRunBFV_nodst _ _ _ _ _ hrun y hnd).1]
      show (G.inputs.find? (·.name = y)).map _ = _
      rw [hfind, hdf]
      subst hdn; rfl
    · have hc := mem_constNames hdm (hdn ▸ hyC)
      rw [hdn] at hc
      have hyG := hnew y hc
      have hnd : y ∉ G.body.map Trace.dst := fun h => hyG (List.mem_append_right _ h)
      rw [(refRunBFV_nodst _ _ _ _ _ h2 y hnd).1]
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
      rw [(refRunBFV_nodst _ _ _ _ _ hrun y hnd).2]
      have hb1 : C.1.boundOf y = none := hbnd y hyC
      have hb2 : G.prog.boundOf y = none := by
        rw [boundOf_eq, find_pairs_none]; rfl
        intro p hp hpy; exact (hbG p hp).2 (hpy ▸ hfr y hyC)
      show (G.inputs.find? (·.name = y)).map _ = _
      rw [hfind]
      have hdf : d = freshDecl D y := hdn ▸ hdecl d hdm (hdn ▸ hyC)
      rw [hdf]
      simp [TraceBFV.inputBound, freshDecl, hb1, hb2]
    · have hc := mem_constNames hdm (hdn ▸ hyC)
      rw [hdn] at hc
      have hyG := hnew y hc
      have hnd : y ∉ G.body.map Trace.dst := fun h => hyG (List.mem_append_right _ h)
      rw [(refRunBFV_nodst _ _ _ _ _ h2 y hnd).2]
      have hb : ({ composite G C with outputs := os } : Program).boundOf y = C.1.boundOf y :=
        boundOf_composite_C G C (fun p hp => (hbG p hp).1) hc hyG
      show ((G.inputs ++ C.1.inputs.filter fun d => decide (d.name ∉ C.2.1)).find? _).map _ = _
      rw [List.find?_append, find_none (fun h => hyG (List.mem_append_left _ h)), Option.none_or,
        Validation.IndCpaDLM.find_filter_eq hyC, hd]
      subst hdn
      simp only [Option.map_some, TraceBFV.inputBound, hb]

/-! ## Agreement, BFV -/

theorem admBFV_eq (E : TraceBFV.Budget) (C : D.Circ) :
    admBFV D (fun _ _ => E) C =
      ((Challenge.Profile.certifyBFVProfile? D.Pe (fun _ => E) (D.prog C)).isSome &&
        D.inputsFit C) := rfl

theorem certifyBFV_analyze {P : FullParams} {E : TraceBFV.Budget} {prog : Program}
    {r : ℕ × List (Var × ℕ)} (h : Challenge.Profile.certifyBFVProfile? P (fun _ => E) prog = some r) :
    ∃ B, refAnalyzeBFVAt P (fun _ => E) prog = some B := by
  rw [certifyBFVProfile_eq] at h
  rcases hB : refAnalyzeBFVAt P (fun _ => E) prog with _ | B
  · simp [hB] at h
  · exact ⟨B, rfl⟩

theorem certifyBFV_dec {P : FullParams} {E : TraceBFV.Budget} {prog : Program}
    {r : ℕ × List (Var × ℕ)} (h : Challenge.Profile.certifyBFVProfile? P (fun _ => E) prog = some r) :
    Challenge.Profile.inputsDecOK P prog = true := by
  rw [certifyBFVProfile_eq] at h
  by_contra hc
  simp [hc, guard] at h

theorem admBFV_eval {E : TraceBFV.Budget} {C : D.Circ} (h : admBFV D (fun _ _ => E) C = true) :
    (Source.eval D.P.src (D.prog C) fun _ => .exact 0).isSome := by
  rw [admBFV_eq] at h
  simp only [Bool.and_eq_true, Option.isSome_iff_exists] at h
  obtain ⟨⟨r, hr⟩, -⟩ := h
  obtain ⟨B, hB⟩ := certifyBFV_analyze hr
  exact refAnalyzeBFV_eval (P := D.Pe) hB

/-- **Agreement, BFV, any body check `X` with `XProp`.** -/
theorem agree_bfv (E : TraceBFV.Budget) (X : Program → Bool) (hX : XProp D.P X)
    (mk : Program → List Var → (Var → M D) → D.Circ)
    (hmk : ∀ p f c, D.prog (mk p f c) = p ∧ D.fresh (mk p f c) = f ∧ D.pt (mk p f c) = c)
    (hfd : ∀ x, (freshDecl D x).ok D.P.src = true)
    (hdf : decOK D.P.src.t (D.P.src.modulus D.lvl) D.eps = true)
    {G : Global D} (hG : InvF E X G) (C : QCirc D) (en : List (Var × Bool))
    (hen : C.2.1 = en.map (·.1)) (hl : en.all (·.2) = true) (hfr : ∀ x ∈ C.2.1, x ∈ G.fresh)
    (hnew : ∀ x ∈ constNames C ++ C.1.body.map Trace.dst, x ∉ G.names)
    (hdecl : ∀ d ∈ C.1.inputs, d.name ∈ C.2.1 → d = freshDecl D d.name)
    (hbnd : ∀ x ∈ C.2.1, C.1.boundOf x = none) :
    admLM mk (fun C' => admBFV D (fun _ _ => E) C' && X (D.prog C')) G C en =
      (admBFV D (fun _ _ => E) (mk C.1 C.2.1 C.2.2) && X C.1) := by
  have hnewc : ∀ y ∈ constNames C, y ∉ G.names := fun y hy => hnew y (List.mem_append_left _ hy)
  have hG' := hG
  obtain ⟨hfresh, hbG, ⟨ρ0, β0, hrun⟩, hGok, hGfit, hGconst, hGpl, hGX⟩ := hG'
  have hfrn : ∀ x ∈ G.fresh, x ∈ G.names := fun x hx => (hfresh x hx).1
  have hbn : ∀ p ∈ G.bounds, p.1 ∈ G.names := fun p hp => (hbG p hp).1
  obtain ⟨ρg, βg, hgr, he1, he2⟩ := grunB E hG C hnewc hfr hdecl hbnd C.1.outputs
  have hfold0 := refRunBFV_fold _ _ _ _ _ hrun
  have hfoldg := refRunBFV_fold _ _ _ _ _ hgr
  have hok := inputs_frame G C (fun d _ _ => d.ok D.P.src) hGok (fun x => hfd x) hnewc hfrn hbn
    hdecl hbnd
  have hfit := inputs_frame G C (qFit D) hGfit (fun x => by simp [qFit, freshDecl]) hnewc hfrn
    hbn hdecl hbnd
  have hpl0 := inputs_frame G C (fun d bnd _ => qPlain D d bnd) hGpl
    (fun x => by simp [qPlain, freshDecl]) hnewc hfrn hbn hdecl hbnd
  have hplain : Challenge.CertifyBFV.plainBoundsOK D.Pe (composite G C) =
      Challenge.CertifyBFV.plainBoundsOK D.Pe C.1 := by
    rw [plainBoundsOK_eq, plainBoundsOK_eq]; exact hpl0
  have hdec0 := inputs_frame G C (fun d bnd _ => qDec D d bnd) hGconst
    (fun x => by simp [qDec, freshDecl, hdf]) hnewc hfrn hbn hdecl hbnd
  have hdec : Challenge.Profile.inputsDecOK D.Pe (composite G C) =
      Challenge.Profile.inputsDecOK D.Pe C.1 := by
    rw [inputsDecOK_eq, inputsDecOK_eq]; exact hdec0
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
      have hdf' := hdecl d hd hn
      have : ρ0 d.name = some ⟨.exact 0, 2, D.lvl, 1, 0⟩ := by
        rw [hv]
        show (G.inputs.find? (·.name = d.name)).map _ = _
        rw [hfind]; rfl
      simp only [metaOK, this, Option.elim_some]
      rw [hdf']; simp [freshDecl]
    · simp [hn]
  unfold admLM
  rw [c1, hl, c3, c5]
  simp only [Bool.true_and, Bool.and_true]
  beta_reduce at hok
  obtain ⟨-, -, -, hX4⟩ := hX
  by_cases h4 : (Source.eval D.P.src C.1 fun _ => .exact 0).isSome
  · have hcert := certifyBFVProfile_frame (P := D.Pe) (E := E) (composite G C) C.1 G.body rfl rfl
      hok hdec hplain ρg βg hgr ⟨he1, he2⟩ h4
    obtain ⟨ρC, hρC⟩ := Option.isSome_iff_exists.mp h4
    obtain ⟨-, hCf, -⟩ := Validation.IndCpaDLM.eval_parts hρC
    have hXe : X (composite G C) = X C.1 :=
      hX4 G.prog (composite G C) C.1 ρg rfl (rel_G_compositeB G C hnewc C.1.outputs).1
        (by rw [show G.prog.body = G.body from rfl, hfold0]; rfl) hfoldg he1 (by rw [hCf]; rfl)
        hGX
    have hadm : admBFV D (fun _ _ => E) (mk (composite G C) G.fresh (G.extend C).pt) =
        admBFV D (fun _ _ => E) (mk C.1 C.2.1 C.2.2) := by
      rw [admBFV_eq, admBFV_eq, inputsFit_eq, inputsFit_eq, (hmk (composite G C) _ _).1,
        (hmk (composite G C) _ _).2.1, (hmk C.1 _ _).1, (hmk C.1 _ _).2.1, hcert, hfit]
    rw [h4, hadm, (hmk (composite G C) _ _).1, hXe, Bool.true_and]
    cases hS : admBFV D (fun _ _ => E) (mk C.1 C.2.1 C.2.2)
    · simp
    · have h6 := admBFV_eval (hadm.trans hS)
      rw [(hmk _ _ _).1] at h6
      rw [h6]; simp
  · have hS : admBFV D (fun _ _ => E) (mk C.1 C.2.1 C.2.2) = false := by
      by_contra h
      have h6 := admBFV_eval (Bool.eq_true_of_not_eq_false h)
      rw [(hmk _ _ _).1] at h6
      exact h4 h6
    rw [Bool.eq_false_iff.mpr h4, hS]; simp

/-! ## Reachable global programs satisfy the invariant -/

theorem reach_invF (E : TraceBFV.Budget) (X : Program → Bool) (hX : XProp D.P X)
    (mk : Program → List Var → (Var → M D) → D.Circ)
    (hmk : ∀ p f c, D.prog (mk p f c) = p ∧ D.fresh (mk p f c) = f ∧ D.pt (mk p f c) = c)
    (hfd : ∀ x, (freshDecl D x).ok D.P.src = true)
    (hdf : decOK D.P.src.t (D.P.src.modulus D.lvl) D.eps = true) {G : Global D}
    (hR : Reach mk (fun C' => admBFV D (fun _ _ => E) C' && X (D.prog C')) G) : InvF E X G := by
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
    obtain ⟨hfresh, hbG, ⟨ρ0, β0, hrun⟩, hok, hfit, hconst, hplG, hXG⟩ := ih
    have hxin : x ∉ G.inputs.map (·.name) := fun h => hx (List.mem_append_left _ h)
    have hrel := rel_prefixB D.Pe G.prog
      ({ G with inputs := G.inputs ++ [freshDecl D x], fresh := G.fresh ++ [x] } : Global D).prog
      [freshDecl D x] rfl rfl
    have hfold := refRunBFV_fold _ _ _ _ _ hrun
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
    · rcases refRunBFV_frame (E := E) G.body _ _ ρ0 _ _ hfold hrel with ⟨h1, -⟩ | ⟨-, ρ₂, β₂, -, h2, -⟩
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
    · show ((G.inputs ++ [freshDecl D x]).all fun d => qDec D d (G.prog.boundOf d.name)) = true
      rw [List.all_append, hconst, Bool.true_and]
      simp [qDec, freshDecl, hbx, hdf]
    · show ((G.inputs ++ [freshDecl D x]).all fun d => qPlain D d (G.prog.boundOf d.name)) = true
      rw [List.all_append, hplG, Bool.true_and]
      simp [qPlain, freshDecl]
    · exact hX.2.2.1 G.prog _ rfl hrel.1 (by rw [show G.prog.body = G.body from rfl, hfold]; rfl)
        hXG
  | extend G C en _ hadm ih =>
    obtain ⟨hfresh, hbG, -, -, -, -, -, -⟩ := ih
    unfold admLM at hadm
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hadm
    obtain ⟨⟨⟨⟨⟨⟨-, -⟩, a3⟩, -⟩, -⟩, -⟩, ⟨a7, a8⟩⟩ := hadm
    have hnew : ∀ x ∈ constNames C ++ C.1.body.map Trace.dst, x ∉ G.names := fun x hx => by
      have := List.all_eq_true.mp a3 x hx; simpa using this
    rw [admBFV_eq, inputsFit_eq, (hmk _ _ _).1, (hmk _ _ _).2.1] at a7
    rw [(hmk _ _ _).1] at a8
    simp only [Bool.and_eq_true, Option.isSome_iff_exists] at a7
    obtain ⟨⟨r, hr⟩, hfit⟩ := a7
    have hconst := certifyBFV_dec hr
    rw [inputsDecOK_eq] at hconst
    have hplN := certifyBFV_plain hr
    rw [plainBoundsOK_eq] at hplN
    obtain ⟨B, hB⟩ := certifyBFV_analyze hr
    have hok := refAnalyzeBFV_ok hB
    obtain ⟨ρ, β, hrun⟩ := refAnalyzeBFV_run hB
    refine ⟨?_, ?_, ⟨ρ, β, hrun⟩, hok, hfit, hconst, hplN, ?_⟩
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

theorem xprop_bfv (P : FullParams) (lay : Budget.KSLayout) (rots : List ℕ) (E : TraceBFV.Budget) :
    XProp P fun p => Challenge.IndCpaDLM.bfvNeed P lay rots E p.body
      (initEnv P.src p fun _ => .exact 0) := by
  have hl := bfvNeedAt_local P lay rots E
  refine ⟨fun _ _ => rfl, fun p h => ?_, fun K₀ K h he hf hx => ?_,
    fun K₀ K S ρg h he hf hg hS hSf hx => ?_⟩ <;> dsimp only at *
  · rw [h]; rfl
  · obtain ⟨ρf, hρf⟩ := Option.isSome_iff_exists.mp hf
    rw [bfvNeed_eq] at hx ⊢
    rw [h, ← needFold_frame hl _ _ _ ρf hρf he]; exact hx
  · obtain ⟨ρf, hρf⟩ := Option.isSome_iff_exists.mp hf
    obtain ⟨ρS, hρS⟩ := Option.isSome_iff_exists.mp hSf
    rw [bfvNeed_eq] at hx ⊢
    rw [bfvNeed_eq, h, needFold_append _ _ _ _ _ hg, ← needFold_frame hl _ _ _ ρf hρf he, hx,
      Bool.true_and, ← needFold_frame hl _ _ _ ρS hρS hS]

/-! ## The locked statements, BFV -/

theorem admLM_fresh_bfv (D : AbsScheme) (mk : Program → List Var → (Var → M D) → D.Circ)
    (hmk : ∀ p f c, D.prog (mk p f c) = p ∧ D.fresh (mk p f c) = f ∧ D.pt (mk p f c) = c)
    (E : TraceBFV.Budget) (hfd : ∀ x, (freshDecl D x).ok D.P.src = true)
    (hdf : Challenge.BFV.decOK D.P.src.t (D.P.src.modulus D.lvl) D.eps = true) (G : Global D)
    (hG : Reach mk (admBFV D fun _ _ => E) G) (C : QCirc D) (en : List (Var × Bool))
    (hen : C.2.1 = en.map (·.1)) (hl : en.all (·.2) = true) (hfr : ∀ x ∈ C.2.1, x ∈ G.fresh)
    (hnew : ∀ x ∈ constNames C ++ C.1.body.map Trace.dst, x ∉ G.names)
    (hdecl : ∀ d ∈ C.1.inputs, d.name ∈ C.2.1 → d = freshDecl D d.name)
    (hbnd : ∀ x ∈ C.2.1, C.1.boundOf x = none) :
    admLM mk (admBFV D fun _ _ => E) G C en = admBFV D (fun _ _ => E) (mk C.1 C.2.1 C.2.2) := by
  have hc : (admBFV D fun _ _ => E) =
      fun C' => admBFV D (fun _ _ => E) C' && (fun _ => true) (D.prog C') :=
    funext fun C' => (Bool.and_true _).symm
  rw [hc] at hG ⊢
  rw [agree_bfv E _ (xprop_true D.P) mk hmk hfd hdf
    (reach_invF E _ (xprop_true D.P) mk hmk hfd hdf hG) C en hen hl hfr hnew hdecl hbnd]

theorem admLM_fresh_bfvClass (D : AbsScheme) (mk : Program → List Var → (Var → M D) → D.Circ)
    (hmk : ∀ p f c, D.prog (mk p f c) = p ∧ D.fresh (mk p f c) = f ∧ D.pt (mk p f c) = c)
    (lay : Budget.KSLayout) (rots : List ℕ) (E : TraceBFV.Budget)
    (hfd : ∀ x, (freshDecl D x).ok D.P.src = true)
    (hdf : Challenge.BFV.decOK D.P.src.t (D.P.src.modulus D.lvl) D.eps = true) (G : Global D)
    (hG : Reach mk (Challenge.IndCpaDLM.bfvClass D lay rots E) G) (C : QCirc D)
    (en : List (Var × Bool))
    (hen : C.2.1 = en.map (·.1)) (hl : en.all (·.2) = true) (hfr : ∀ x ∈ C.2.1, x ∈ G.fresh)
    (hnew : ∀ x ∈ constNames C ++ C.1.body.map Trace.dst, x ∉ G.names)
    (hdecl : ∀ d ∈ C.1.inputs, d.name ∈ C.2.1 → d = freshDecl D d.name)
    (hbnd : ∀ x ∈ C.2.1, C.1.boundOf x = none) :
    admLM mk (Challenge.IndCpaDLM.bfvClass D lay rots E) G C en =
      Challenge.IndCpaDLM.bfvClass D lay rots E (mk C.1 C.2.1 C.2.2) := by
  have hcls : ∀ C', Challenge.IndCpaDLM.bfvClass D lay rots E C' = (admBFV D (fun _ _ => E) C' &&
      Challenge.IndCpaDLM.bfvSide D.Pe lay && Challenge.IndCpaDLM.bfvNeed D.Pe lay rots E
        (D.prog C').body (initEnv D.P.src (D.prog C') fun _ => .exact 0)) := fun _ => rfl
  cases hside : Challenge.IndCpaDLM.bfvSide D.Pe lay
  · have hf : Challenge.IndCpaDLM.bfvClass D lay rots E = fun _ => false :=
      funext fun C' => by rw [hcls, hside]; simp
    rw [hf]
    unfold admLM; simp
  · have hc : Challenge.IndCpaDLM.bfvClass D lay rots E = fun C' => admBFV D (fun _ _ => E) C' &&
        (fun p => Challenge.IndCpaDLM.bfvNeed D.Pe lay rots E p.body
          (initEnv D.P.src p fun _ => .exact 0)) (D.prog C') :=
      funext fun C' => by rw [hcls, hside, Bool.and_true]
    rw [hc] at hG ⊢
    have hXk : XProp D.P fun p => Challenge.IndCpaDLM.bfvNeed D.Pe lay rots E p.body
        (initEnv D.P.src p fun _ => .exact 0) := xprop_bfv D.Pe lay rots E
    rw [agree_bfv E _ hXk mk hmk hfd hdf (reach_invF E _ hXk mk hmk hfd hdf hG) C en hen hl hfr
      hnew hdecl hbnd]
    beta_reduce
    rw [(hmk _ _ _).1]

example := (@admLM_fresh_bfv : type_of% @Challenge.IndCpaDLM.admLM_fresh_bfv)
example := (@admLM_fresh_bfvClass : type_of% @Challenge.IndCpaDLM.admLM_fresh_bfvClass)

/-! ## Instances -/

theorem admLM_fresh_bgvKSSeal (G : Global bgvKSSealData) (hG : Reach Challenge.IndCpaDLM.mkSeal Challenge.IndCpaDLM.admSeal G) (C : QCirc bgvKSSealData)
    (en : List (Var × Bool))
    (hen : C.2.1 = en.map (·.1)) (hl : en.all (·.2) = true) (hfr : ∀ x ∈ C.2.1, x ∈ G.fresh)
    (hnew : ∀ x ∈ constNames C ++ C.1.body.map Trace.dst, x ∉ G.names)
    (hdecl : ∀ d ∈ C.1.inputs, d.name ∈ C.2.1 → d = freshDecl bgvKSSealData d.name)
    (hbnd : ∀ x ∈ C.2.1, C.1.boundOf x = none) :
    admLM Challenge.IndCpaDLM.mkSeal Challenge.IndCpaDLM.admSeal G C en = Challenge.IndCpaDLM.admSeal (Challenge.IndCpaDLM.mkSeal C.1 C.2.1 C.2.2) :=
  admLM_fresh_ks bgvKSSealData Challenge.IndCpaDLM.mkSeal Validation.IndCpaDLM.hmkSeal bgvKSLayout
    [5] (Spec.Budget.certified bgvKSSeal bgvKSLayout) (fun _ => rfl) (by decide) G hG C en hen hl
    hfr hnew hdecl hbnd

theorem admLM_fresh_bgvSealExact (G : Global bgvSealData) (hG : Reach Challenge.IndCpaDLM.mkSealExact (exactClass bgvSealData bgvSealProfile) G) (C : QCirc bgvSealData)
    (en : List (Var × Bool))
    (hen : C.2.1 = en.map (·.1)) (hl : en.all (·.2) = true) (hfr : ∀ x ∈ C.2.1, x ∈ G.fresh)
    (hnew : ∀ x ∈ constNames C ++ C.1.body.map Trace.dst, x ∉ G.names)
    (hdecl : ∀ d ∈ C.1.inputs, d.name ∈ C.2.1 → d = freshDecl bgvSealData d.name)
    (hbnd : ∀ x ∈ C.2.1, C.1.boundOf x = none) :
    admLM Challenge.IndCpaDLM.mkSealExact (exactClass bgvSealData bgvSealProfile) G C en = (exactClass bgvSealData bgvSealProfile) (Challenge.IndCpaDLM.mkSealExact C.1 C.2.1 C.2.2) :=
  admLM_fresh_exact bgvSealData Challenge.IndCpaDLM.mkSealExact (fun _ _ _ => ⟨rfl, rfl, rfl⟩)
    (Spec.Budget.certified bgvSeal (Spec.Budget.uniformLayout 1)) (fun _ => rfl) (by decide) G hG C
    en hen hl hfr hnew hdecl hbnd

theorem admLM_fresh_bfvSeal (G : Global Challenge.IndCpaDLM.bfvSealData) (hG : Reach Challenge.IndCpaDLM.mkBFVSeal Challenge.IndCpaDLM.admBFVSeal G) (C : QCirc Challenge.IndCpaDLM.bfvSealData)
    (en : List (Var × Bool))
    (hen : C.2.1 = en.map (·.1)) (hl : en.all (·.2) = true) (hfr : ∀ x ∈ C.2.1, x ∈ G.fresh)
    (hnew : ∀ x ∈ constNames C ++ C.1.body.map Trace.dst, x ∉ G.names)
    (hdecl : ∀ d ∈ C.1.inputs, d.name ∈ C.2.1 → d = freshDecl Challenge.IndCpaDLM.bfvSealData d.name)
    (hbnd : ∀ x ∈ C.2.1, C.1.boundOf x = none) :
    admLM Challenge.IndCpaDLM.mkBFVSeal Challenge.IndCpaDLM.admBFVSeal G C en = Challenge.IndCpaDLM.admBFVSeal (Challenge.IndCpaDLM.mkBFVSeal C.1 C.2.1 C.2.2) :=
  admLM_fresh_bfvClass Challenge.IndCpaDLM.bfvSealData Challenge.IndCpaDLM.mkBFVSeal
    Validation.IndCpaDLM.hmkBFVSeal Challenge.IndCpaDLM.bfvSealLayout [5]
    Challenge.IndCpaDLM.bfvSealBudget (fun _ => rfl) Validation.IndCpaDLM.lm_two_stage_bfv_kernel.1
    G hG C en hen hl hfr hnew hdecl hbnd

example := (@admLM_fresh_bgvKSSeal : type_of% @Challenge.IndCpaDLM.admLM_fresh_bgvKSSeal)
example := (@admLM_fresh_bgvSealExact : type_of% @Challenge.IndCpaDLM.admLM_fresh_bgvSealExact)
example := (@admLM_fresh_bfvSeal : type_of% @Challenge.IndCpaDLM.admLM_fresh_bfvSeal)

end Validation.IndCpaDLM
