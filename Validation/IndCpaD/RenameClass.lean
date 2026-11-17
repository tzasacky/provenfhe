import Validation.IndCpaD.RenameEval
import Validation.IndCpaD.LMAgreeBFV

/-!
# Validation.IndCpaD.RenameClass — the certificate classes are kept by renaming

If a circuit is in one of the certificate classes (at a constant budget), so is every renaming of
it (`CircRen`).
-/

namespace Validation.IndCpaDRen
open Spec NPoly Scheme Source Spec.IndCpaDProfile Challenge.IndCpaDProfile Challenge.BFV
open Validation.IndCpaDFrame
open Validation.IndCpaDLM (qFit inputsFit_eq admBGV_eq admBFV_eq admBGV_eval admBFV_eval
  exactOnly_eq)

variable {D : AbsScheme}

theorem mem_map_inj {r : Var → Var} (hr : Function.Injective r) (l : List Var) (x : Var) :
    decide (r x ∈ l.map r) = decide (x ∈ l) := by
  simp [List.mem_map, hr.eq_iff]

theorem inputsFit_ren {r : Var → Var} {C0 C' : D.Circ} (h : CircRen D r C0 C') :
    D.inputsFit C' = D.inputsFit C0 := by
  rw [inputsFit_eq, inputsFit_eq, h.1.inputs, h.2.1, List.all_map]
  refine all_congr_mem _ fun d hd => ?_
  simp only [Function.comp_apply, renD, h.1.bounds d hd, List.mem_map, h.1.inj.eq_iff,
    exists_eq_right]
  rfl

theorem const_ren {r : Var → Var} {C0 C' : D.Circ} (h : CircRen D r C0 C') :
    ((D.prog C').inputs.all fun d => decide (d.name ∈ D.fresh C') || decide (D.P.src.t - 1 ≤ D.eps)) =
      ((D.prog C0).inputs.all fun d =>
        decide (d.name ∈ D.fresh C0) || decide (D.P.src.t - 1 ≤ D.eps)) := by
  rw [h.1.inputs, h.2.1, List.all_map]
  refine all_congr_mem _ fun d _ => ?_
  simp only [Function.comp_apply, renD, List.mem_map, h.1.inj.eq_iff, exists_eq_right]

theorem admBGV_ren (E : Trace.Budget) {r : Var → Var} {C0 C' : D.Circ} (h : CircRen D r C0 C')
    (hc : admBGV D (fun _ => E) C0 = true) : admBGV D (fun _ => E) C' = true := by
  rw [admBGV_eq] at hc ⊢
  simp only [Bool.and_eq_true] at hc ⊢
  obtain ⟨⟨h1, h2⟩, h3⟩ := hc
  exact ⟨⟨certifyProfile_ren h.1 h1, by rw [inputsFit_ren h]; exact h2⟩, by
    rw [const_ren h]; exact h3⟩

theorem admBFV_ren (E : TraceBFV.Budget) {r : Var → Var} {C0 C' : D.Circ} (h : CircRen D r C0 C')
    (hc : admBFV D (fun _ _ => E) C0 = true) : admBFV D (fun _ _ => E) C' = true := by
  rw [admBFV_eq] at hc ⊢
  simp only [Bool.and_eq_true] at hc ⊢
  exact ⟨certifyBFVProfile_ren h.1 hc.1, by rw [inputsFit_ren h]; exact hc.2⟩

theorem exactClass_ren (E : Trace.Budget) {r : Var → Var} {C0 C' : D.Circ}
    (h : CircRen D r C0 C') (hc : exactClass D (fun _ => E) C0 = true) :
    exactClass D (fun _ => E) C' = true := by
  have e : ∀ C, exactClass D (fun _ => E) C =
      (admBGV D (fun _ => E) C && exactOnly (D.prog C).body) := fun _ => rfl
  rw [e] at hc ⊢
  simp only [Bool.and_eq_true] at hc ⊢
  refine ⟨admBGV_ren E h hc.1, ?_⟩
  rw [exactOnly_eq, h.1.body, List.all_map]
  rw [exactOnly_eq] at hc
  refine List.all_eq_true.mpr fun i hi => ?_
  simp only [Function.comp_apply, exactInstr_ren]
  exact List.all_eq_true.mp hc.2 i hi

theorem fold0 {C0 : D.Circ} (hz : (Source.eval D.P.src (D.prog C0) fun _ => .exact 0).isSome) :
    ∃ ρf, (D.prog C0).body.foldlM (step D.P.src) (initEnv D.P.src (D.prog C0) fun _ => .exact 0) =
      some ρf := by
  obtain ⟨ρz, hρz⟩ := Option.isSome_iff_exists.mp hz
  exact ⟨ρz, (Validation.IndCpaDLM.eval_parts hρz).2.1⟩

theorem ksClass_ren (lay : Budget.KSLayout) (rots : List ℕ) (E : Trace.Budget) {r : Var → Var}
    {C0 C' : D.Circ} (h : CircRen D r C0 C') (hc : ksClass D lay rots (fun _ => E) C0 = true) :
    ksClass D lay rots (fun _ => E) C' = true := by
  have e : ∀ C, ksClass D lay rots (fun _ => E) C = (admBGV D (fun _ => E) C &&
      ksSide D.Pe lay && ksNeed D.Pe lay rots E (D.prog C).body
        (initEnv D.P.src (D.prog C) fun _ => .exact 0)) := fun _ => rfl
  rw [e] at hc ⊢
  simp only [Bool.and_eq_true] at hc ⊢
  obtain ⟨⟨h1, h2⟩, h3⟩ := hc
  obtain ⟨ρf, hf⟩ := fold0 (admBGV_eval h1)
  refine ⟨⟨admBGV_ren E h h1, h2⟩, ?_⟩
  rw [ksNeed_eq, h.1.body, needFold_ren h.1.inj (fun ρ ρ' i hρ => ksNeedAt_ren D.Pe lay rots E ρ ρ' i hρ)
    _ _ _ ρf (initEnv_ren h.1 _ _ fun _ _ => rfl) hf, ← ksNeed_eq]
  exact h3

theorem bfvClass_ren (lay : Budget.KSLayout) (rots : List ℕ) (E : TraceBFV.Budget) {r : Var → Var}
    {C0 C' : D.Circ} (h : CircRen D r C0 C')
    (hc : Challenge.IndCpaDLM.bfvClass D lay rots E C0 = true) :
    Challenge.IndCpaDLM.bfvClass D lay rots E C' = true := by
  have e : ∀ C, Challenge.IndCpaDLM.bfvClass D lay rots E C = (admBFV D (fun _ _ => E) C &&
      Challenge.IndCpaDLM.bfvSide D.Pe lay && Challenge.IndCpaDLM.bfvNeed D.Pe lay rots E
        (D.prog C).body (initEnv D.P.src (D.prog C) fun _ => .exact 0)) := fun _ => rfl
  rw [e] at hc ⊢
  simp only [Bool.and_eq_true] at hc ⊢
  obtain ⟨⟨h1, h2⟩, h3⟩ := hc
  obtain ⟨ρf, hf⟩ := fold0 (admBFV_eval h1)
  refine ⟨⟨admBFV_ren E h h1, h2⟩, ?_⟩
  rw [bfvNeed_eq, h.1.body, needFold_ren h.1.inj (fun ρ ρ' i hρ => bfvNeedAt_ren D.Pe lay rots E ρ ρ' i hρ)
    _ _ _ ρf (initEnv_ren h.1 _ _ fun _ _ => rfl) hf, ← bfvNeed_eq]
  exact h3

end Validation.IndCpaDRen
