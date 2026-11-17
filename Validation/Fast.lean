import Challenge.Fast
import Challenge.Certify
import Validation.Headline.Noise
import Validation.Certify

/-!
# Validation.Fast — the fast analyzers and certificate decisions equal the locked ones

Proofs of the pins of `Challenge.Fast`. The fast functions (`FHE.Noise.Fast`) keep the
environments of the reference analysis in search trees and run the body once. The proofs:

* a tree built by `mapOf` is looked up as `List.find?` reads the list (`mapOf_get`);
* `Source.step` changes only the destination (`step_set`, from `Validation.Headline.Noise`), so
  the lookup function of the tree after the insertion *is* the environment `step` returned, and
  `runBody` computes `refRun` (`runBody_eq`);
* `refAnalyze` is `run` followed by `outBound` (`refAnalyze_eq`), whatever the outputs, so the
  analyses of the one-output programs all read the same final environments;
* on those, `Spec.Encrypt.certOK?` is `certOK` (`certOK?_eq`).

No `Challenge.*` definition is unfolded with `simp`/`rw`/`unfold`: local `rfl` equations only.
-/

namespace Validation.Fast
open Spec Spec.Source Spec.Budget Spec.Encrypt Spec.Certify Challenge.Headline Challenge.Certify
open FHE.Noise.Fast

namespace Aux

/-! ### Trees -/

theorem mapOf_get {α β : Type} (key : α → Var) (val : α → β) (l : List α) (x : Var) :
    (mapOf key val l)[x]? = (l.find? fun a => key a = x).map val := by
  induction l with
  | nil => simp [mapOf]
  | cons a l ih =>
    have e : mapOf key val (a :: l) = (mapOf key val l).insert (key a) (val a) := rfl
    rw [e, Std.TreeMap.getElem?_insert, List.find?_cons, ih]
    by_cases h : key a = x <;> simp [h]

theorem insert_get {β : Type} (m : VMap β) (d : Var) (v : β) :
    (fun x => (m.insert d v)[x]?) = fun y => if y = d then some v else m[y]? := by
  funext y
  rw [Std.TreeMap.getElem?_insert]
  by_cases h : y = d
  · subst h; simp
  · have h' : ¬ d = y := fun e => h e.symm
    simp [h, h']

theorem boundMap_get (prog : Program) (x : Var) : (boundMap prog)[x]? = prog.boundOf x :=
  mapOf_get _ _ _ _

theorem initEnvMap_get (Pr : Params) (prog : Program) :
    (fun x => (initEnvMap Pr prog)[x]?) = initEnv Pr prog fun _ => .exact 0 := by
  funext x
  exact mapOf_get _ _ _ _

/-- The initial bounds of `refAnalyze`. -/
def β₀ (P : FullParams) (prog : Program) : Var → Option ℕ :=
  fun x => (prog.inputs.find? (·.name = x)).map fun _ =>
    match prog.boundOf x with
    | some b => min b P.inputNoise
    | none => P.inputNoise

theorem initBoundMap_get (P : FullParams) (prog : Program) :
    (fun x => (initBoundMap P prog)[x]?) = β₀ P prog := by
  funext x
  have e : (initBoundMap P prog)[x]? = _ := mapOf_get _ _ _ _
  rw [e, β₀]
  cases h : prog.inputs.find? (fun a => a.name = x) with
  | none => rfl
  | some d =>
    have hd : d.name = x := by simpa using List.find?_some h
    simp only [Option.map_some, boundMap_get, hd]
    rfl

/-! ### The run -/

variable (P : FullParams) (E : Trace.Budget)

/-- The lookup functions of a pair of trees. -/
def look (r : VMap (Val P.src) × VMap ℕ) : Env P.src × (Var → Option ℕ) :=
  (fun x => r.1[x]?, fun x => r.2[x]?)

theorem refRun_cons (i : Instr) (is : List Instr) (ρ : Env P.src) (β : Var → Option ℕ) :
    refRun P E (i :: is) ρ β = (do
      let ρ' ← step P.src ρ i
      let b ← refBound P E ρ β i
      let v ← ρ' (Trace.dst i)
      guard (2 * b < P.src.modulus v.level)
      refRun P E is ρ' (fun y => if y = Trace.dst i then some b else β y)) := rfl

theorem modAt_modsOf : modAt P (modsOf P) = fun ℓ => P.src.modulus ℓ := by
  funext ℓ
  unfold modAt
  cases h : (modsOf P)[ℓ]? with
  | none => rfl
  | some q =>
    simp only [modsOf, List.getElem?_toArray, List.getElem?_map] at h
    obtain ⟨k, hk, rfl⟩ := Option.map_eq_some_iff.mp h
    have : k = ℓ := by
      rw [List.getElem?_eq_some_iff] at hk
      obtain ⟨_, hk⟩ := hk
      simpa using hk.symm
    subst this
    rfl

theorem runBody_eq : ∀ (is : List Instr) (ρ : VMap (Val P.src)) (β : VMap ℕ),
    (runBody P E (fun ℓ => P.src.modulus ℓ) is ρ β).map (look P) =
      refRun P E is (fun x => ρ[x]?) (fun x => β[x]?) := by
  intro is
  induction is with
  | nil => intro ρ β; rfl
  | cons i is ih =>
    intro ρ β
    rw [refRun_cons, runBody]
    cases hs : step P.src (fun x => ρ[x]?) i with
    | none => rfl
    | some ρ' =>
      cases hb : refBound P E (fun x => ρ[x]?) (fun x => β[x]?) i with
      | none => rfl
      | some b =>
        simp only [Option.bind_eq_bind, Option.bind_some]
        cases hv : ρ' (Trace.dst i) with
        | none => rfl
        | some v =>
          simp only [Option.bind_some]
          by_cases hg : 2 * b < P.src.modulus v.level
          · simp only [guard, hg, ite_true, Option.pure_def, Option.bind_some]
            rw [ih, insert_get, insert_get]
            obtain ⟨v', hv'⟩ := Validation.Headline.NoiseAux.step_set hs
            have : v' = v := by
              rw [hv'] at hv
              simpa [Env.set] using hv
            subst this
            rw [hv']
            rfl
          · simp [guard, hg]

/-- `refAnalyze`, as the run followed by reading the outputs. -/
theorem refAnalyze_eq (prog : Program) :
    refAnalyze P E prog = (run P E prog).bind fun r => outBound r prog.outputs := by
  have e : refAnalyze P E prog = (do
      guard (P.src.kind = .bgv)
      guard (prog.inputs.all fun d => d.ok P.src)
      let (ρ, β) ← refRun P E prog.body (initEnv P.src prog fun _ => .exact 0) (β₀ P prog)
      guard (prog.outputs.all fun o => (ρ o).isSome)
      let bs ← prog.outputs.mapM β
      pure (bs.foldl max 0)) := rfl
  rw [e, ← initEnvMap_get, ← initBoundMap_get, ← runBody_eq, run, modAt_modsOf]
  by_cases h1 : P.src.kind = .bgv
  · by_cases h2 : (prog.inputs.all fun d => d.ok P.src) = true
    · simp only [Option.bind_eq_bind, guard, h1, h2, ite_true, Option.pure_def, Option.bind_some]
      cases runBody P E (fun ℓ => P.src.modulus ℓ) prog.body (initEnvMap P.src prog)
        (initBoundMap P prog) with
      | none => rfl
      | some r => rfl
    · simp [guard, h1, h2]
  · simp [guard, h1]

theorem analyze_eq (prog : Program) : analyze P E prog = refAnalyze P E prog := by
  rw [refAnalyze_eq]; rfl

/-! ### The outputs -/

theorem refRun_foldlM : ∀ (is : List Instr) (ρ : Env P.src) (β : Var → Option ℕ)
    (r : Env P.src × (Var → Option ℕ)), refRun P E is ρ β = some r →
      is.foldlM (step P.src) ρ = some r.1 := by
  intro is
  induction is with
  | nil =>
    intro ρ β r h
    rw [Validation.Headline.NoiseAux.refRun_nil] at h
    cases h; rfl
  | cons i is ih =>
    intro ρ β r h
    obtain ⟨ρ', b, v, h1, -, -, -, h5⟩ := Validation.Headline.NoiseAux.refRun_cons_some P E h
    rw [List.foldlM_cons, h1]
    exact ih _ _ _ h5

/-- Under an accepted run, the program with any outputs defined at the end evaluates (on
all-zero messages) to the final environment of the run. -/
theorem eval_of_run {prog : Program} {r : VMap (Val P.src) × VMap ℕ} (h : run P E prog = some r)
    (outs : List Var) (ho : ∀ o ∈ outs, (r.1[o]?).isSome = true) :
    eval P.src { prog with outputs := outs } (fun _ => .exact 0) = some fun x => r.1[x]? := by
  rw [run] at h
  by_cases h1 : P.src.kind = .bgv
  · by_cases h2 : (prog.inputs.all fun d => d.ok P.src) = true
    · simp only [Option.bind_eq_bind, guard, h1, h2, ite_true, Option.pure_def,
        Option.bind_some] at h
      have hr := runBody_eq P E prog.body (initEnvMap P.src prog) (initBoundMap P prog)
      rw [modAt_modsOf] at h
      rw [h, initEnvMap_get] at hr
      have hf := refRun_foldlM P E _ _ _ _ hr.symm
      have hfit : (prog.inputs.all fun dcl : Decl =>
          (Msg.exact (0 : Poly P.src.t P.src.N)).fits P.src.kind) = true := by
        rw [h1]; simp [Msg.fits]
      have ho' : (outs.all fun o => (r.1[o]?).isSome) = true := by
        simpa using ho
      have hf' : List.foldlM (step P.src)
          (initEnv P.src { prog with outputs := outs } fun _ => .exact 0) prog.body =
          some fun x => r.1[x]? := hf
      simp only [eval, Option.bind_eq_bind, guard, h2, hfit, ite_true, Option.pure_def,
        Option.bind_some, hf', ho']
    · simp [guard, h1, h2] at h
  · simp [guard, h1] at h

theorem certOK?_eq {prog : Program} {r : VMap (Val P.src) × VMap ℕ} (h : run P E prog = some r)
    (o : Var) (b : ℕ) (sw : Bool) (ho : (r.1[o]?).isSome = true) :
    certOK? P { prog with outputs := [o] } b sw = certOK P r o b sw := by
  have he := eval_of_run P E h [o] (by simpa using ho)
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp ho
  simp only [certOK?, outputsUnderS?, outputKey?, Decrypt.decryptAllOK?, Decrypt.outputLevel?,
    he, certOK, hv, Option.bind_eq_bind, Option.bind_some, Option.pure_def, List.all_cons,
    List.all_nil, Bool.and_true, Option.map_some]

theorem outBound_isSome {Pr : Params} {r : VMap (Val Pr) × VMap ℕ} {o : Var} {b : ℕ}
    (h : outBound r [o] = some b) : (r.1[o]?).isSome = true := by
  rw [outBound] at h
  cases hs : (r.1[o]?).isSome with
  | true => rfl
  | false =>
    simp only [List.all_cons, List.all_nil, Bool.and_true, hs] at h
    simp [guard] at h

theorem outputBound?_eq {prog : Program} {r : VMap (Val P.src) × VMap ℕ}
    (h : run P E prog = some r) (sw : Bool) (o : Var) :
    outputBound? P E prog sw o = outputBound P r sw o := by
  have e : outputBound? P E prog sw o = (do
      let b ← refAnalyze P E { prog with outputs := [o] }
      guard (certOK? P { prog with outputs := [o] } b sw)
      pure b) := rfl
  have hrun : run P E { prog with outputs := [o] } = some r := h
  rw [e, refAnalyze_eq, hrun, outputBound]
  simp only [Option.bind_eq_bind, Option.bind_some]
  cases hb : outBound r [o] with
  | none => rfl
  | some b =>
    simp only [Option.bind_some]
    rw [certOK?_eq P E h o b sw (outBound_isSome hb)]

end Aux

/-! ### The certificate decision -/

open Aux

theorem inputsMsgOK_eq (P : FullParams) (prog : Program) :
    inputsMsgOK P prog = inputsMsgOK? P prog := by
  have e : inputsMsgOK? P prog = (prog.inputs.all fun d =>
      decide (P.src.t < P.src.modulus d.level) &&
        (prog.boundOf d.name).all fun b => decide (P.src.t / 2 ≤ b)) := rfl
  have e2 : inputsMsgOK P prog = (prog.inputs.all fun d =>
      decide (P.src.t < modAt P (modsOf P) d.level) &&
        ((boundMap prog)[d.name]?).all fun b => decide (P.src.t / 2 ≤ b)) := rfl
  rw [e, e2, modAt_modsOf]
  simp only [boundMap_get]

theorem checked_eq (P : FullParams) (lay : KSLayout) (prog : Program) (sw : Bool) :
    checked P lay prog sw = checked? P lay prog sw := by
  have e : checked? P lay prog sw = (do
      guard (schemeParamsOK? P)
      guard (specialOK? P)
      guard (layoutOK? P lay)
      guard (keysRestrict? P)
      guard (!prog.outputs.isEmpty)
      guard (inputsMsgOK? P prog)
      let B ← refAnalyze P (certified P lay) prog
      let outs ← prog.outputs.mapM fun o =>
        (outputBound? P (certified P lay) prog sw o).map fun b => (o, b)
      pure (B, outs)) := rfl
  rw [e, checked, refAnalyze_eq, inputsMsgOK_eq]
  cases hr : run P (certified P lay) prog with
  | none => simp only [Option.bind_eq_bind, Option.bind_none]
  | some r =>
    have hf : (fun o => (outputBound? P (certified P lay) prog sw o).map fun b => (o, b)) =
        fun o => (outputBound P r sw o).map fun b => (o, b) := by
      funext o; rw [outputBound?_eq P _ hr]
    rw [hf]
    rfl

theorem freshOK_eq (P : FullParams) (prog : Program) (fresh : List Var) :
    freshOK P prog fresh = freshOK? P prog fresh := by
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
  simp only [freshOK, freshOK?, hn, hf, boundMap_get]
  congr!

theorem certify_eq (x : Input) : certify x = certify? x := by
  have h1 : @checked = @checked? := by
    funext P lay prog sw; exact checked_eq P lay prog sw
  have h2 : @freshOK = @freshOK? := by
    funext P prog fresh; exact freshOK_eq P prog fresh
  unfold certify
  rw [h1, h2]
  rfl

/-! ### The pins -/

theorem analyzeFast_eq : Challenge.Fast.AnalyzerEqRef FHE.Holes.analyzeFast :=
  fun P E prog => Aux.analyze_eq P E prog

theorem certifyFast_eq : Challenge.Fast.CertifierEqRef FHE.Holes.certifyFast :=
  fun x => certify_eq x

end Validation.Fast

/-! ### Closed instances, evaluated by the kernel

The fast functions are structural recursion on lists and search trees, so closed instances
reduce in the kernel like those of the reference. -/

section Closed
open Spec Spec.Source Challenge.Headline Challenge.Corpus

example : FHE.Holes.analyzeFast .exampleBGV31 noBudget addMulProg = some (2 ^ 57) := by
  decide +kernel
example : FHE.Holes.analyzeFast FullParams.tinyBGV (Budget.certified FullParams.tinyBGV (Budget.uniformLayout 1))
    mulSwitchProg = refAnalyze FullParams.tinyBGV (Budget.certified FullParams.tinyBGV (Budget.uniformLayout 1))
    mulSwitchProg := by decide +kernel
example : (FHE.Holes.certifyFast
      (Challenge.Certify.tinyInput Challenge.Certify.threeOutProg true .worstCase)).map
        (fun c => (c.bound, c.outputs)) =
    (Challenge.Certify.certify?
      (Challenge.Certify.tinyInput Challenge.Certify.threeOutProg true .worstCase)).map
        (fun c => (c.bound, c.outputs)) := by
  decide +kernel

end Closed
