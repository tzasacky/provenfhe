import Challenge.Fast
import Challenge.CertifyBFV
import Validation.Fast
import Validation.BFV.Sound
import Validation.BFV.PerInstr

/-!
# Validation.FastBFV — the fast BFV analyzer and certificate decision equal the locked ones

Proofs of the BFV pins of `Challenge.Fast`, by the argument of `Validation.Fast`: trees are
looked up as `List.find?` reads the lists, `Source.step` changes only the destination, so
`runBody` computes `refRunBFVAt`, and `mulLevelsGo`, `budgetsGo`, `checksGo` compute
`mulLevelsAux`, `budgetsAux`, `checksAux`; the checks, the budget and the assumptions of
`certifyBFV?` are the parameterised copies at the locked values, by `rfl`.

No `Challenge.*` definition is unfolded with `simp`/`rw`/`unfold`: local `rfl` equations only.
-/

namespace Validation.FastBFV
open Spec Spec.Source Spec.BudgetBFV Spec.CertifyBFV Challenge.BFV Challenge.BFVMul
open Challenge.CertifyBFV
open Spec.TraceBFV (Bnd)
open FHE.Noise.Fast (VMap mapOf boundMap initEnvMap)
open FHE.Noise.FastBFV
open Validation.Fast.Aux (mapOf_get insert_get boundMap_get initEnvMap_get)

namespace Aux

theorem inputBound_eq (P : FullParams) (prog : Program) (d : Decl) :
    inputBound P (boundMap prog) d = TraceBFV.inputBound P prog d := by
  rw [inputBound, boundMap_get]; rfl

/-- The initial bounds of `refAnalyzeBFV`. -/
def β₀ (P : FullParams) (prog : Program) : Var → Option Bnd :=
  fun x => (prog.inputs.find? (·.name = x)).map fun d =>
    if d.parts = 1 then .pt (TraceBFV.inputBound P prog d) else .ct (TraceBFV.inputBound P prog d)

theorem initBndMap_get (P : FullParams) (prog : Program) :
    (fun x => (initBndMap P prog)[x]?) = β₀ P prog := by
  funext x
  have e : (initBndMap P prog)[x]? = _ := mapOf_get _ _ _ _
  rw [e, β₀]
  simp only [inputBound_eq]

variable (P : FullParams) (E : ℕ → TraceBFV.Budget)

/-- The lookup functions of a pair of trees. -/
def look (r : VMap (Val P.src) × VMap Bnd) : Env P.src × (Var → Option Bnd) :=
  (fun x => r.1[x]?, fun x => r.2[x]?)

theorem refBoundBFVQ_eq (E : TraceBFV.Budget) (ℓ : ℕ) (β : Var → Option Bnd) (i : Instr) :
    refBoundBFVQ P E ℓ (P.src.modulus ℓ) β i = refBoundBFV P E ℓ β i := by
  cases i <;> rfl

theorem bndOKQ_eq (ℓ : ℕ) (b : Bnd) : bndOKQ P (P.src.modulus ℓ) b = bndOK P ℓ b := by
  cases b <;> rfl

theorem runBody_eq : ∀ (is : List Instr) (n : ℕ) (ρ : VMap (Val P.src)) (β : VMap Bnd),
    (runBody P E (fun ℓ => P.src.modulus ℓ) n is ρ β).map (look P) =
      refRunBFVAt P E n is (fun x => ρ[x]?) (fun x => β[x]?) := by
  intro is
  induction is with
  | nil => intro n ρ β; rfl
  | cons i is ih =>
    intro n ρ β
    rw [Validation.BFV.PerInstrAux.refRunAt_cons, runBody]
    simp only [refBoundBFVQ_eq, bndOKQ_eq]
    cases hd : domainOK (Pr := P.src) (fun x => ρ[x]?) i with
    | false => simp [guard]
    | true =>
      simp only [guard, ite_true, Option.bind_eq_bind, Option.pure_def, Option.bind_some]
      cases hs : step P.src (fun x => ρ[x]?) i with
      | none => rfl
      | some ρ' =>
        simp only [Option.bind_some]
        cases hv : ρ' (Trace.dst i) with
        | none => rfl
        | some v =>
          simp only [Option.bind_some]
          cases hb : refBoundBFV P (E n) v.level (fun x => β[x]?) i with
          | none => rfl
          | some b =>
            simp only [Option.bind_some]
            cases hg : bndOK P v.level b with
            | false => simp
            | true =>
              simp only [ite_true, Option.bind_some]
              rw [ih, insert_get, insert_get]
              obtain ⟨v', hv'⟩ := Validation.Headline.NoiseAux.step_set hs
              have : v' = v := by
                rw [hv'] at hv
                simpa [Env.set] using hv
              subst this
              rw [hv']
              rfl

/-- `refAnalyzeBFVAt`, as the run followed by reading the outputs. -/
theorem refAnalyzeBFV_eq (prog : Program) :
    refAnalyzeBFVAt P E prog = (run P E prog).bind fun r => outBound r prog.outputs := by
  have e : refAnalyzeBFVAt P E prog = (do
      guard (P.src.kind = .bfv)
      guard (prog.inputs.all fun d => d.ok P.src)
      let (ρ, β) ← refRunBFVAt P E 0 prog.body (initEnv P.src prog fun _ => .exact 0) (β₀ P prog)
      guard (prog.outputs.all fun o => (ρ o).isSome)
      let bs ← prog.outputs.mapM (ctBound β)
      pure (bs.foldl max 0)) := rfl
  rw [e, ← initEnvMap_get, ← initBndMap_get, ← runBody_eq, run,
    Validation.Fast.Aux.modAt_modsOf]
  by_cases h1 : P.src.kind = .bfv
  · by_cases h2 : (prog.inputs.all fun d => d.ok P.src) = true
    · simp only [Option.bind_eq_bind, guard, h1, h2, ite_true, Option.pure_def, Option.bind_some]
      cases runBody P E (fun ℓ => P.src.modulus ℓ) 0 prog.body (initEnvMap P.src prog)
        (initBndMap P prog) with
      | none => rfl
      | some r => rfl
    · simp [guard, h1, h2]
  · simp [guard, h1]

theorem analyze_eq (prog : Program) : analyze P E prog = refAnalyzeBFVAt P E prog := by
  rw [refAnalyzeBFV_eq]; rfl

end Aux

namespace Aux2
open Aux

theorem inputBound_eq' (P : FullParams) (prog : Program) :
    inputBound P (boundMap prog) = TraceBFV.inputBound P prog := by
  funext d; exact inputBound_eq _ _ _

/-! ### The multiplication levels -/

/-- The levels `mulLevelsAux` records at one instruction. -/
def hereOf {Pr : Params} (ρ : Env Pr) : Instr → List ℕ
  | .mul _ a _ | .square _ a => ((ρ a).map (·.level)).toList
  | _ => []

theorem mulLevelsAux_cons (Pr : Params) (i : Instr) (is : List Instr) (ρ : Env Pr) :
    mulLevelsAux Pr (i :: is) ρ =
      match step Pr ρ i with
      | some ρ' => hereOf ρ i ++ mulLevelsAux Pr is ρ'
      | none => hereOf ρ i := by
  cases i <;> rfl

theorem mulHere_eq {Pr : Params} (ρ : VMap (Val Pr)) (i : Instr) :
    mulHere ρ i = hereOf (fun x => ρ[x]?) i := by
  cases i <;> rfl

theorem hereOf_reverse {Pr : Params} (ρ : Env Pr) (i : Instr) :
    (hereOf ρ i).reverse = hereOf ρ i := by
  have h : ∀ o : Option ℕ, o.toList.reverse = o.toList := fun o => by cases o <;> rfl
  cases i <;> simp only [hereOf, List.reverse_nil, h]

theorem mulLevelsGo_eq (Pr : Params) : ∀ (is : List Instr) (ρ : VMap (Val Pr)) (acc : List ℕ),
    mulLevelsGo Pr is ρ acc = acc.reverse ++ mulLevelsAux Pr is (fun x => ρ[x]?) := by
  intro is
  induction is with
  | nil => intro ρ acc; simp [mulLevelsGo]; rfl
  | cons i is ih =>
    intro ρ acc
    rw [mulLevelsAux_cons, mulLevelsGo, mulHere_eq]
    cases hs : step Pr (fun x => ρ[x]?) i with
    | none => simp only [List.reverse_append, hereOf_reverse]
    | some ρ' =>
      obtain ⟨v, hv⟩ := Validation.Headline.NoiseAux.step_set hs
      have hd : ρ' (Trace.dst i) = some v := by rw [hv]; simp [Env.set]
      simp only [hd]
      rw [ih, List.reverse_append, hereOf_reverse, insert_get, List.append_assoc, hv]
      rfl

theorem mulLevels_eq (Pr : Params) (prog : Program) :
    FHE.Noise.FastBFV.mulLevels Pr prog = Challenge.CertifyBFV.mulLevels Pr prog := by
  have e : Challenge.CertifyBFV.mulLevels Pr prog =
      (mulLevelsAux Pr prog.body (initEnv Pr prog fun _ => .exact 0)).eraseDups := rfl
  rw [e, FHE.Noise.FastBFV.mulLevels, mulLevelsGo_eq, initEnvMap_get]
  rfl

/-! ### The operand levels of the multiplications and key switches -/

/-- The levels `opLevelsAux` records at one instruction. -/
def opHereOf {Pr : Params} (ρ : Env Pr) : Instr → List ℕ
  | .mul _ a _ | .square _ a | .relin _ a | .keySwitch _ a => ((ρ a).map (·.level)).toList
  | _ => []

theorem opLevelsAux_cons (Pr : Params) (i : Instr) (is : List Instr) (ρ : Env Pr) :
    opLevelsAux Pr (i :: is) ρ =
      match step Pr ρ i with
      | some ρ' => opHereOf ρ i ++ opLevelsAux Pr is ρ'
      | none => opHereOf ρ i := by
  cases i <;> rfl

theorem opHere_eq {Pr : Params} (ρ : VMap (Val Pr)) (i : Instr) :
    opHere ρ i = opHereOf (fun x => ρ[x]?) i := by
  cases i <;> rfl

theorem opHereOf_reverse {Pr : Params} (ρ : Env Pr) (i : Instr) :
    (opHereOf ρ i).reverse = opHereOf ρ i := by
  have h : ∀ o : Option ℕ, o.toList.reverse = o.toList := fun o => by cases o <;> rfl
  cases i <;> simp only [opHereOf, List.reverse_nil, h]

theorem opLevelsGo_eq (Pr : Params) : ∀ (is : List Instr) (ρ : VMap (Val Pr)) (acc : List ℕ),
    opLevelsGo Pr is ρ acc = acc.reverse ++ opLevelsAux Pr is (fun x => ρ[x]?) := by
  intro is
  induction is with
  | nil => intro ρ acc; simp [opLevelsGo]; rfl
  | cons i is ih =>
    intro ρ acc
    rw [opLevelsAux_cons, opLevelsGo, opHere_eq]
    cases hs : step Pr (fun x => ρ[x]?) i with
    | none => simp only [List.reverse_append, opHereOf_reverse]
    | some ρ' =>
      obtain ⟨v, hv⟩ := Validation.Headline.NoiseAux.step_set hs
      have hd : ρ' (Trace.dst i) = some v := by rw [hv]; simp [Env.set]
      simp only [hd]
      rw [ih, List.reverse_append, opHereOf_reverse, insert_get, List.append_assoc, hv]
      rfl

theorem opLevelsFast_eq (Pr : Params) (prog : Program) :
    FHE.Noise.FastBFV.opLevelsFast Pr prog = Challenge.CertifyBFV.opLevels Pr prog := by
  have e : Challenge.CertifyBFV.opLevels Pr prog =
      opLevelsAux Pr prog.body (initEnv Pr prog fun _ => .exact 0) := rfl
  rw [e, FHE.Noise.FastBFV.opLevelsFast, opLevelsGo_eq, initEnvMap_get]
  rfl

/-! ### The budgets and the per-instruction checks -/

/-- One step of `budgetsAux`, by `rfl`. -/
theorem budgetsAux_cons (x : InputBFV) (i : Instr) (is : List Instr) (ds : List ℕ)
    (ρ : Env x.P.src) :
    budgetsAux x (i :: is) ds ρ = stepBudget x ρ (ds.headD 0) i ::
      match step x.P.src ρ i with
      | some ρ' => budgetsAux x is ds.tail ρ'
      | none => [] := rfl

theorem checksAux_cons (x : InputBFV) (i : Instr) (is : List Instr) (ds : List ℕ)
    (ρ : Env x.P.src) :
    checksAux x (i :: is) ds ρ = (stepChecks x ρ (ds.headD 0) i &&
      match step x.P.src ρ i with
      | some ρ' => checksAux x is ds.tail ρ'
      | none => true) := rfl

theorem stepBudget_eq (x : InputBFV) (ρ : Env x.P.src) (dr : ℕ) (i : Instr) :
    stepBudgetWith x (maxPlainBound x.P x.prog) ρ dr i = stepBudget x ρ dr i := rfl

theorem budgetsGo_eq (x : InputBFV) : ∀ (is : List Instr) (ds : List ℕ)
    (ρ : VMap (Val x.P.src)) (acc : List TraceBFV.Budget),
    budgetsGo x (maxPlainBound x.P x.prog) is ds ρ acc =
      acc.reverse ++ budgetsAux x is ds (fun y => ρ[y]?) := by
  intro is
  induction is with
  | nil => intro ds ρ acc; simp [budgetsGo]; rfl
  | cons i is ih =>
    intro ds ρ acc
    rw [budgetsAux_cons, budgetsGo, stepBudget_eq]
    cases hs : step x.P.src (fun y => ρ[y]?) i with
    | none => simp
    | some ρ' =>
      obtain ⟨v, hv⟩ := Validation.Headline.NoiseAux.step_set hs
      have hd : ρ' (Trace.dst i) = some v := by rw [hv]; simp [Env.set]
      simp only [hd]
      rw [ih, insert_get, hv]
      simp
      rfl

theorem checksGo_eq (x : InputBFV) : ∀ (is : List Instr) (ds : List ℕ)
    (ρ : VMap (Val x.P.src)), checksGo x is ds ρ = checksAux x is ds (fun y => ρ[y]?) := by
  intro is
  induction is with
  | nil => intro ds ρ; rfl
  | cons i is ih =>
    intro ds ρ
    rw [checksAux_cons, checksGo]
    cases hs : step x.P.src (fun y => ρ[y]?) i with
    | none => rfl
    | some ρ' =>
      obtain ⟨v, hv⟩ := Validation.Headline.NoiseAux.step_set hs
      have hd : ρ' (Trace.dst i) = some v := by rw [hv]; simp [Env.set]
      simp only [hd]
      rw [ih, insert_get, hv]
      rfl

/-! ### The key switches with a declared drop -/

theorem ksDroppedGo_range : ∀ (is : List Instr) (ds : List ℕ),
    ksDroppedGo is ds = (List.range is.length).any fun n =>
      (is[n]?.map isKS).getD false && ds.getD n 0 != 0
  | [], _ => rfl
  | i :: is, ds => by
    rw [ksDroppedGo, ksDroppedGo_range is ds.tail, List.length_cons, List.range_succ_eq_map,
      List.any_cons, List.any_map]
    congr 1
    · cases ds <;> simp
    · congr 1
      funext n
      cases ds <;> simp

theorem ksDroppedGo_eq (x : InputBFV) : ksDroppedGo x.prog.body x.drops = ksDropped x := by
  rw [ksDroppedGo_range]; rfl

/-! ### Memoisation -/

theorem stepBudget_kind (x : InputBFV) (mpb : ℕ) (ρ : Env x.P.src) (dr : ℕ) (i : Instr) :
    stepBudgetWith x mpb ρ dr i =
      stepBudgetWith x mpb (envAt x.P.src (levelOf ρ (operand i))) dr (reprOf (kindOf i)) := by
  cases i <;> rfl

theorem stepChecks_kind (x : InputBFV) (ρ : Env x.P.src) (dr : ℕ) (i : Instr) :
    stepChecks x ρ dr i =
      stepChecks x (envAt x.P.src (levelOf ρ (operand i))) dr (reprOf (kindOf i)) := by
  cases i <;> rfl

theorem memo_spec {V : Type} (f : ℕ × ℕ × ℕ → V) (m : List ((ℕ × ℕ × ℕ) × V))
    (hm : ∀ p ∈ m, p.2 = f p.1) (k : ℕ × ℕ × ℕ) :
    (memo f m k).1 = f k ∧ ∀ p ∈ (memo f m k).2, p.2 = f p.1 := by
  unfold memo
  cases h : m.find? (·.1 == k) with
  | none =>
    refine ⟨rfl, ?_⟩
    intro p hp
    simp only [List.mem_cons] at hp
    rcases hp with rfl | hp
    · rfl
    · exact hm p hp
  | some p =>
    refine ⟨?_, hm⟩
    have hp := List.mem_of_find?_eq_some h
    have hk := List.find?_some h
    simp only [beq_iff_eq] at hk
    show p.2 = f k
    rw [hm p hp, hk]

theorem budgetsGoM_eq (x : InputBFV) (mpb : ℕ) : ∀ (is : List Instr) (ds : List ℕ)
    (ρ : VMap (Val x.P.src)) (acc : List TraceBFV.Budget) (m : List ((ℕ × ℕ × ℕ) × TraceBFV.Budget)),
    (∀ p ∈ m, p.2 = stepBudgetWith x mpb (envAt x.P.src p.1.1) p.1.2.1 (reprOf p.1.2.2)) →
    budgetsGoM x mpb is ds ρ acc m = budgetsGo x mpb is ds ρ acc := by
  intro is
  induction is with
  | nil => intro ds ρ acc m _; rfl
  | cons i is ih =>
    intro ds ρ acc m hm
    obtain ⟨h1, h2⟩ := memo_spec (fun k => stepBudgetWith x mpb (envAt x.P.src k.1) k.2.1
      (reprOf k.2.2)) m hm (levelOf (fun y => ρ[y]?) (operand i), ds.headD 0, kindOf i)
    rw [budgetsGoM, budgetsGo]
    simp only [h1, ← stepBudget_kind]
    cases step x.P.src (fun y => ρ[y]?) i with
    | none => rfl
    | some ρ' =>
      simp only []
      cases ρ' (Trace.dst i) with
      | none => rfl
      | some v => exact ih _ _ _ _ h2

theorem checksGoM_eq (x : InputBFV) : ∀ (is : List Instr) (ds : List ℕ)
    (ρ : VMap (Val x.P.src)) (m : List ((ℕ × ℕ × ℕ) × Bool)),
    (∀ p ∈ m, p.2 = stepChecks x (envAt x.P.src p.1.1) p.1.2.1 (reprOf p.1.2.2)) →
    checksGoM x is ds ρ m = checksGo x is ds ρ := by
  intro is
  induction is with
  | nil => intro ds ρ m _; rfl
  | cons i is ih =>
    intro ds ρ m hm
    obtain ⟨h1, h2⟩ := memo_spec (fun k => stepChecks x (envAt x.P.src k.1) k.2.1
      (reprOf k.2.2)) m hm (levelOf (fun y => ρ[y]?) (operand i), ds.headD 0, kindOf i)
    rw [checksGoM, checksGo]
    simp only [h1, ← stepChecks_kind]
    cases step x.P.src (fun y => ρ[y]?) i with
    | none => rfl
    | some ρ' =>
      simp only []
      cases ρ' (Trace.dst i) with
      | none => rfl
      | some v => simp only []; rw [ih _ _ _ h2]

/-! ### The outputs -/

variable (P : FullParams) (E : ℕ → TraceBFV.Budget)

theorem refRun_foldlM : ∀ (is : List Instr) (n : ℕ) (ρ : Env P.src) (β : Var → Option Bnd)
    (r : Env P.src × (Var → Option Bnd)), refRunBFVAt P E n is ρ β = some r →
      is.foldlM (step P.src) ρ = some r.1 := by
  intro is
  induction is with
  | nil =>
    intro n ρ β r h
    rw [Validation.BFV.PerInstrAux.refRunAt_nil] at h
    cases h; rfl
  | cons i is ih =>
    intro n ρ β r h
    obtain ⟨ρ', v, b, h1, -, -, -, h5, -⟩ := Validation.BFV.PerInstrAux.refRunAt_cons_some P h
    rw [List.foldlM_cons, h1]
    exact ih _ _ _ _ h5

theorem eval_of_run {prog : Program} {r : VMap (Val P.src) × VMap Bnd} (h : run P E prog = some r)
    (ho : ∀ o ∈ prog.outputs, (r.1[o]?).isSome = true) :
    eval P.src prog (fun _ => .exact 0) = some fun x => r.1[x]? := by
  rw [run] at h
  by_cases h1 : P.src.kind = .bfv
  · by_cases h2 : (prog.inputs.all fun d => d.ok P.src) = true
    · simp only [Option.bind_eq_bind, guard, h1, h2, ite_true, Option.pure_def,
        Option.bind_some] at h
      have hr := Aux.runBody_eq P E prog.body 0 (initEnvMap P.src prog) (initBndMap P prog)
      rw [Validation.Fast.Aux.modAt_modsOf] at h
      rw [h, initEnvMap_get] at hr
      have hf := refRun_foldlM P E _ _ _ _ _ hr.symm
      have hfit : (prog.inputs.all fun dcl : Decl =>
          (Msg.exact (0 : Poly P.src.t P.src.N)).fits P.src.kind) = true := by
        rw [h1]; simp [Msg.fits]
      have ho' : (prog.outputs.all fun o => (r.1[o]?).isSome) = true := by
        simpa using ho
      have hf' : List.foldlM (step P.src) (initEnv P.src prog fun _ => .exact 0) prog.body =
          some fun x => r.1[x]? := hf
      simp only [eval, Option.bind_eq_bind, guard, h2, hfit, ite_true, Option.pure_def,
        Option.bind_some, hf', ho']
    · simp [guard, h1, h2] at h
  · simp [guard, h1] at h

theorem outBound_isSome {Pr : Params} {r : VMap (Val Pr) × VMap Bnd} {outs : List Var} {b : ℕ}
    (h : outBound r outs = some b) : ∀ o ∈ outs, (r.1[o]?).isSome = true := by
  rw [outBound] at h
  cases hs : (outs.all fun o => (r.1[o]?).isSome) with
  | true => simpa using hs
  | false =>
    simp only [hs] at h
    simp [guard] at h

theorem outputsUnderS?_eq {prog : Program} {r : VMap (Val P.src) × VMap Bnd}
    (h : run P E prog = some r) (ho : ∀ o ∈ prog.outputs, (r.1[o]?).isSome = true) :
    Encrypt.outputsUnderS? P.src prog =
      prog.outputs.all fun o => (r.1[o]?).map (·.key) == some 1 := by
  have he := eval_of_run P E h ho
  simp only [Encrypt.outputsUnderS?, Encrypt.outputKey?, he, Option.bind_eq_bind,
    Option.bind_some, Option.pure_def]
  congr 1
  funext o
  cases r.1[o]? <;> rfl

end Aux2

open Aux Aux2

theorem certify_eq (x : InputBFV) : certify x = certifyBFV? x := by
  have e : certifyBFV? x = (do
      guard (checksOK x)
      let bs := (budgetsBFV x).toArray
      let E := budgetFn bs
      let B ← refAnalyzeBFVAt x.P E x.prog
      guard (Encrypt.outputsUnderS? x.P.src x.prog)
      let outs ← x.prog.outputs.mapM fun o =>
        (refAnalyzeBFVAt x.P E { x.prog with outputs := [o] }).map fun b => (o, b)
      pure ⟨E, B, outs, Challenge.CertifyBFV.mulLevels x.P.src x.prog, assumptionsOf x⟩) := rfl
  have hib : inputBound x.P (boundMap x.prog) = TraceBFV.inputBound x.P x.prog := by
    funext d; exact inputBound_eq _ _ _
  have hca : checksGoM x x.prog.body (dropsOf x) (initEnvMap x.P.src x.prog) [] =
      checksAux x x.prog.body (dropsOf x) (initEnv x.P.src x.prog fun _ => .exact 0) := by
    rw [checksGoM_eq x _ _ _ _ (by simp), checksGo_eq, initEnvMap_get]
  have hc : checksOKWith x (TraceBFV.inputBound x.P x.prog)
      (checksAux x x.prog.body (dropsOf x) (initEnv x.P.src x.prog fun _ => .exact 0)) =
      checksOK x := rfl
  have hmp : maxPlainBoundWith x.prog (TraceBFV.inputBound x.P x.prog) =
      maxPlainBound x.P x.prog := rfl
  have hbs : budgetsGoM x (maxPlainBound x.P x.prog) x.prog.body (dropsOf x)
      (initEnvMap x.P.src x.prog) [] [] = budgetsBFV x := by
    rw [budgetsGoM_eq x _ _ _ _ _ _ (by simp), budgetsGo_eq, initEnvMap_get]; rfl
  have hA : assumptionsOfWith x (Challenge.CertifyBFV.mulLevels x.P.src x.prog)
      (ksDroppedGo x.prog.body x.drops)
      ((opLevelsFast x.P.src x.prog).contains x.P.src.qs.length) = assumptionsOf x := by
    rw [ksDroppedGo_eq, opLevelsFast_eq]; rfl
  rw [e, certify]
  simp only []
  rw [hib, hca, hc, hmp, hbs, mulLevels_eq, hA]
  cases checksOK x with
  | false => simp [guard]
  | true =>
    simp only [guard, ite_true, Option.bind_eq_bind, Option.pure_def, Option.bind_some]
    rw [refAnalyzeBFV_eq]
    cases hr : run x.P (budgetFn (budgetsBFV x).toArray) x.prog with
    | none => rfl
    | some r =>
      simp only [Option.bind_some]
      cases hB : outBound r x.prog.outputs with
      | none => rfl
      | some B =>
        simp only [Option.bind_some]
        rw [outputsUnderS?_eq x.P _ hr (outBound_isSome hB)]
        have hf : (fun o => (refAnalyzeBFVAt x.P (budgetFn (budgetsBFV x).toArray)
            { x.prog with outputs := [o] }).map fun b => (o, b)) =
            fun o => (outBound r [o]).map fun b => (o, b) := by
          funext o
          have hrun : run x.P (budgetFn (budgetsBFV x).toArray)
              { x.prog with outputs := [o] } = some r := hr
          rw [refAnalyzeBFV_eq, hrun]; rfl
        rw [hf]

/-! ### The fresh-encryption decision -/

theorem freshInputNoise_eq (P : FullParams) (prog : Program) (fresh : List Var) (ε : ℕ) :
    FHE.Noise.FastBFV.freshInputNoise P prog fresh ε =
      Spec.EncryptBFV.freshInputNoise P prog fresh ε := by
  have hf : ∀ y : Var, ((mapOf (fun x : Var => x) (fun _ => ()) fresh)[y]?).isSome =
      decide (y ∈ fresh) := by
    intro y
    rw [mapOf_get, Option.isSome_map, Bool.eq_iff_iff]
    simp [List.find?_isSome]
  simp only [FHE.Noise.FastBFV.freshInputNoise, Spec.EncryptBFV.freshInputNoise, hf]

theorem freshOKBFV_eq (prog : Program) (fresh : List Var) :
    FHE.Noise.FastBFV.freshOKBFV prog fresh = Spec.EncryptBFV.freshOKBFV? prog fresh := by
  have hn : ∀ x : Var, ((mapOf (fun d : Decl => d.name) (fun _ => ()) prog.inputs)[x]?).isSome =
      prog.inputs.any fun d => d.name == x := by
    intro x
    rw [mapOf_get, Option.isSome_map, Bool.eq_iff_iff]
    simp [List.find?_isSome]
  have hf : ∀ y : Var, ((mapOf (fun x : Var => x) (fun _ => ()) fresh)[y]?).isSome = true ↔
      y ∈ fresh := by
    intro y
    rw [mapOf_get, Option.isSome_map]
    simp [List.find?_isSome]
  simp only [FHE.Noise.FastBFV.freshOKBFV, Spec.EncryptBFV.freshOKBFV?, hn, hf, boundMap_get]

theorem certifyFresh_eq (x : InputBFV) (m : Spec.EncryptBFV.FreshModeBFV) :
    FHE.Noise.FastBFV.certifyFresh x m = Challenge.BFVEncrypt.certifyBFVFresh? x m := by
  have hc : @FHE.Noise.FastBFV.certify = @certifyBFV? := by
    funext y; exact certify_eq y
  have hn : @FHE.Noise.FastBFV.freshInputNoise = @Spec.EncryptBFV.freshInputNoise := by
    funext P prog fresh ε; exact freshInputNoise_eq P prog fresh ε
  have ho : @FHE.Noise.FastBFV.freshOKBFV = @Spec.EncryptBFV.freshOKBFV? := by
    funext prog fresh; exact freshOKBFV_eq prog fresh
  have ha : @FHE.Noise.FastBFV.certifyAt = @Challenge.BFVEncrypt.certifyAt? := by
    funext y fresh ε used drift
    unfold FHE.Noise.FastBFV.certifyAt
    rw [hc, hn, ho]
    rfl
  unfold FHE.Noise.FastBFV.certifyFresh
  rw [ha]
  cases m <;> rfl

theorem stepsGo_eq (Pr : Params) : ∀ (is : List Instr) (ρ : VMap (Val Pr)),
    (stepsGo Pr is ρ).map (fun m => fun y => m[y]?) = is.foldlM (step Pr) (fun y => ρ[y]?) := by
  intro is
  induction is with
  | nil => intro ρ; rfl
  | cons i is ih =>
    intro ρ
    rw [List.foldlM_cons, stepsGo]
    cases hs : step Pr (fun y => ρ[y]?) i with
    | none => rfl
    | some ρ' =>
      obtain ⟨v, hv⟩ := Validation.Headline.NoiseAux.step_set hs
      have hd : ρ' (Trace.dst i) = some v := by rw [hv]; simp [Env.set]
      simp only [hd]
      rw [ih, insert_get, hv]
      rfl

theorem evalZ_eq (Pr : Params) (prog : Program) :
    (evalZ Pr prog).map (fun m => fun y => m[y]?) = eval Pr prog (fun _ => .exact 0) := by
  have e : eval Pr prog (fun _ => .exact 0) = (do
      guard (prog.inputs.all fun dcl => dcl.ok Pr)
      guard (prog.inputs.all fun _ => (Msg.exact (0 : Poly Pr.t Pr.N)).fits Pr.kind)
      let ρ ← prog.body.foldlM (step Pr) (initEnv Pr prog fun _ => .exact 0)
      guard (prog.outputs.all fun o => (ρ o).isSome)
      pure ρ) := rfl
  rw [e, evalZ, ← initEnvMap_get, ← stepsGo_eq]
  cases (prog.inputs.all fun dcl => dcl.ok Pr) <;>
    cases (prog.inputs.all fun _ => (Msg.exact (0 : Poly Pr.t Pr.N)).fits Pr.kind) <;>
    simp only [guard, Option.bind_eq_bind, Option.pure_def] <;> try rfl
  all_goals
    cases stepsGo Pr prog.body (initEnvMap Pr prog) with
    | none => rfl
    | some m =>
      simp only [Option.map_some, Option.bind_some]
      cases (prog.outputs.all fun o => (m[o]?).isSome) <;> rfl

theorem outputLevel_eq (x : InputBFV) (o : Var) :
    ((evalZ x.P.src x.prog).bind fun m => (m[o]?).map (·.level)) =
      Decrypt.outputLevel? x.P.src x.prog o := by
  have h := evalZ_eq x.P.src x.prog
  simp only [Decrypt.outputLevel?, ← h]
  cases evalZ x.P.src x.prog with
  | none => rfl
  | some m =>
    simp only [Option.map_some, Option.bind_some, Option.bind_eq_bind, Option.pure_def]
    cases m[o]? <;> rfl

theorem decryptLibExtOK_eq (x : InputBFV) (c : CertificateBFV) :
    FHE.Noise.FastBFV.decryptLibExtOK x c = Challenge.BFVDecryptLib.decryptLibExtOK? x c := by
  have e : Challenge.BFVDecryptLib.decryptLibExtOK? x c =
      (match Challenge.BFVDecryptLib.techLib? x.mul with
        | none => false
        | some behz => x.prog.outputs.all fun o =>
            match Decrypt.outputLevel? x.P.src x.prog o, c.outputs.lookup o with
            | some ℓ, some B => Challenge.BFVDecryptLib.outputLibOK? behz x.P.src.t x.P.src.qs ℓ B
            | _, _ => false) := rfl
  rw [e, FHE.Noise.FastBFV.decryptLibExtOK]
  simp only [outputLevel_eq]
  rfl

theorem decryptLibOK_eq (x : InputBFV) (c : CertificateBFV) :
    FHE.Noise.FastBFV.decryptLibOK x c = Challenge.BFVDecrypt.decryptLibOK? x c := by
  have e : Challenge.BFVDecrypt.decryptLibOK? x c = ((match x.mul with
      | some (.hps _) => true
      | some (.poverq _) => true
      | some (.leveled ..) => true
      | _ => false) &&
    Spec.DecryptBFV.decParamsOK? x.P.src.t x.P.src.qs &&
    x.prog.outputs.all (fun o => Decrypt.outputLevel? x.P.src x.prog o == some x.P.src.qs.length) &&
    c.outputs.all (fun ob => Spec.DecryptBFV.decLibOK? x.P.src.t x.P.src.qs ob.2)) := rfl
  have hl : ∀ o, ((evalZ x.P.src x.prog).bind fun m => (m[o]?).map (·.level)) =
      Decrypt.outputLevel? x.P.src x.prog o := by
    intro o
    have h := evalZ_eq x.P.src x.prog
    simp only [Decrypt.outputLevel?, ← h]
    cases evalZ x.P.src x.prog with
    | none => rfl
    | some m =>
      simp only [Option.map_some, Option.bind_some, Option.bind_eq_bind, Option.pure_def]
      cases m[o]? <;> rfl
  rw [e, FHE.Noise.FastBFV.decryptLibOK]
  simp only [hl]
  rfl

theorem budgets_eq (x : InputBFV) : FHE.Noise.FastBFV.budgets x = budgetsBFV x := by
  have hib : inputBound x.P (boundMap x.prog) = TraceBFV.inputBound x.P x.prog := by
    funext d; exact Aux.inputBound_eq _ _ _
  have hmp : maxPlainBoundWith x.prog (TraceBFV.inputBound x.P x.prog) =
      maxPlainBound x.P x.prog := rfl
  rw [FHE.Noise.FastBFV.budgets, hib, hmp, budgetsGoM_eq x _ _ _ _ _ _ (by simp), budgetsGo_eq,
    initEnvMap_get]; rfl

end Validation.FastBFV

/-! ### The pins -/

namespace Validation.Fast

theorem analyzeBFVFast_eq : Challenge.Fast.AnalyzerBFVEqRef FHE.Holes.analyzeBFVFast :=
  fun P E prog => Validation.FastBFV.Aux.analyze_eq P E prog

theorem certifyBFVFast_eq : Challenge.Fast.CertifierBFVEqRef FHE.Holes.certifyBFVFast :=
  fun x => Validation.FastBFV.certify_eq x

theorem certifyBFVFreshFast_eq :
    Challenge.Fast.CertifierBFVFreshEqRef FHE.Holes.certifyBFVFreshFast :=
  fun x m => Validation.FastBFV.certifyFresh_eq x m

theorem decryptLibFast_eq : Challenge.Fast.DecryptLibEqRef FHE.Holes.decryptLibFast :=
  fun x c => Validation.FastBFV.decryptLibOK_eq x c

theorem decryptLibExtFast_eq : Challenge.Fast.DecryptLibExtEqRef FHE.Holes.decryptLibExtFast :=
  fun x c => Validation.FastBFV.decryptLibExtOK_eq x c

end Validation.Fast

/-! ### Closed instances, evaluated by the kernel

The fast functions are structural recursion on lists and search trees, so closed instances
reduce in the kernel like those of the reference. -/

example : Challenge.CertifyBFV.summary (FHE.Holes.certifyBFVFast
      (Challenge.CertifyBFV.tinyIn Challenge.CertifyBFV.mulProg (some .textbook) false)) =
    Challenge.CertifyBFV.summary (Challenge.CertifyBFV.certifyBFV?
      (Challenge.CertifyBFV.tinyIn Challenge.CertifyBFV.mulProg (some .textbook) false)) := by
  decide +kernel
