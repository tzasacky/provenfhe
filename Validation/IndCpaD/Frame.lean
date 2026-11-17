import Validation.IndCpaD.LM
import Validation.Fast
import Validation.BFV.PerInstr
import Challenge.IndCpaD.LMBFV

/-!
# Validation.IndCpaD.Frame — locality of the reference analyses

The reference analyses (`Challenge.Headline.refRun`, `Challenge.BFV.refRunBFV`) and the
replay-driven checks (`ksNeed`, `bfvNeed`) read, at each instruction, only the operands of that
instruction. So on two environments that agree where the smaller one is defined, a body whose
replay runs on the smaller one gets the same verdict and the same values on both (`refRun_frame`,
`refRunBFV_frame`, `ksNeed_frame`, `bfvNeed_frame`). Local copies of the locked definitions
(`…V`, equal by `rfl`) are unfolded instead of the locked ones.
-/

namespace Validation.IndCpaDFrame
open Spec Spec.Source Challenge.Headline Challenge.BFV
open Validation.IndCpaDLM (Ext ext_envSet step_ext)

/-! ## Operands -/

/-- The operands an instruction reads. -/
def ops : Instr → List Var
  | .add _ a b | .sub _ a b | .mul _ a b | .addPlain _ a b | .subPlain _ a b
  | .mulPlain _ a b => [a, b]
  | .square _ a | .mulConst _ a _ | .copy _ a | .toEval _ a | .toCoeff _ a | .relin _ a
  | .keySwitch _ a | .automorph _ a _ | .modSwitch _ a | .dropLimbs _ a _ => [a]

theorem step_ops {Pr : Params} {ρ ρ' : Env Pr} {i : Instr} (h : step Pr ρ i = some ρ') :
    ∀ y ∈ ops i, (ρ y).isSome := by
  cases i <;> simp only [step, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq, guard] at h <;> simp only [ops, List.mem_cons, List.not_mem_nil,
    or_false] <;> intro y hy <;> aesop

/-- Agreement on the operands, from an extension where the smaller environment is defined. -/
theorem agree_of_ext {α : Type} {f g : Var → Option α} (h : Ext f g) {y : Var}
    (hy : (f y).isSome) : f y = g y := by
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hy
  rw [hv, h y v hv]

/-! ## The BGV reference analysis -/

section BGV
variable {P : FullParams} {E : Trace.Budget}

/-- `refBound`, unfolded. -/
def refBoundV (P : FullParams) (E : Trace.Budget) (ρ : Env P.src) (β : Var → Option ℕ) :
    Instr → Option ℕ
  | .add _ a b | .sub _ a b | .addPlain _ a b | .subPlain _ a b => do
    let x ← β a; let y ← β b
    pure (x + y)
  | .mul _ a b | .mulPlain _ a b => do
    let x ← β a; let y ← β b
    pure (P.src.N * x * y)
  | .square _ a => do
    let x ← β a
    pure (P.src.N * x * x)
  | .mulConst _ a c => do
    let x ← β a
    pure (c.natAbs * x)
  | .copy _ a | .toEval _ a | .toCoeff _ a | .automorph _ a _ | .dropLimbs _ a _ => β a
  | .relin _ a | .keySwitch _ a => do
    let x ← β a
    pure (x + E.keySwitch)
  | .modSwitch _ a => do
    let x ← β a; let v ← ρ a
    let q ← P.src.qs[v.level - 1]?
    pure (x / q + E.modSwitchAt v.parts)

theorem refRun_cons (i : Instr) (is : List Instr) (ρ : Env P.src) (β : Var → Option ℕ) :
    refRun P E (i :: is) ρ β = (do
      let ρ' ← step P.src ρ i
      let b ← refBound P E ρ β i
      let v ← ρ' (Trace.dst i)
      guard (2 * b < P.src.modulus v.level)
      refRun P E is ρ' (fun y => if y = Trace.dst i then some b else β y)) := rfl

theorem refBound_eq (ρ : Env P.src) (β : Var → Option ℕ) (i : Instr) :
    refBound P E ρ β i = refBoundV P E ρ β i := by
  cases i <;> rfl

theorem refBound_congr {ρ ρ₂ : Env P.src} {β β₂ : Var → Option ℕ} {i : Instr}
    (h : ∀ y ∈ ops i, ρ y = ρ₂ y ∧ β y = β₂ y) :
    refBound P E ρ β i = refBound P E ρ₂ β₂ i := by
  rw [refBound_eq, refBound_eq]
  cases i <;> simp only [ops, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq] at h <;> simp only [refBoundV, h]

/-- The two analyses are related: the smaller environments extend into the larger ones, and the
bound environment is defined wherever the replay environment is. -/
def Rel {α : Type} (ρ ρ₂ : Env P.src) (β β₂ : Var → Option α) : Prop :=
  Ext ρ ρ₂ ∧ Ext β β₂ ∧ ∀ x, (ρ x).isSome → (β x).isSome

theorem rel_set {α : Type} {ρ ρ₂ : Env P.src} {β β₂ : Var → Option α} (h : Rel ρ ρ₂ β β₂)
    (d : Var) (v : Val P.src) (b : α) :
    Rel (ρ.set d v) (ρ₂.set d v) (fun y => if y = d then some b else β y)
      (fun y => if y = d then some b else β₂ y) := by
  refine ⟨ext_envSet h.1 d v, ?_, ?_⟩
  · intro x w hx
    by_cases hxd : x = d
    · simpa [hxd] using hx
    · simp only [hxd, ↓reduceIte] at hx ⊢; exact h.2.1 x w hx
  · intro x hx
    by_cases hxd : x = d
    · simp [hxd]
    · simp only [hxd, ↓reduceIte]
      apply h.2.2 x
      simpa [Env.set, hxd] using hx

theorem rel_ops {α : Type} {ρ ρ₂ ρ' : Env P.src} {β β₂ : Var → Option α} (h : Rel ρ ρ₂ β β₂)
    {i : Instr} (hs : step P.src ρ i = some ρ') : ∀ y ∈ ops i, ρ y = ρ₂ y ∧ β y = β₂ y :=
  fun y hy => ⟨agree_of_ext h.1 (step_ops hs y hy),
    agree_of_ext h.2.1 (h.2.2 y (step_ops hs y hy))⟩

/-- **Locality of the BGV reference analysis.** -/
theorem refRun_frame : ∀ (body : List Instr) (ρ ρ₂ ρf : Env P.src) (β β₂ : Var → Option ℕ),
    body.foldlM (step P.src) ρ = some ρf → Rel ρ ρ₂ β β₂ →
    (refRun P E body ρ β = none ∧ refRun P E body ρ₂ β₂ = none) ∨
    ∃ βf ρ₂f β₂f, refRun P E body ρ β = some (ρf, βf) ∧
      refRun P E body ρ₂ β₂ = some (ρ₂f, β₂f) ∧ Rel ρf ρ₂f βf β₂f
  | [], ρ, ρ₂, ρf, β, β₂, h, hr => by
    simp only [List.foldlM_nil, Option.pure_def, Option.some.injEq] at h
    subst h
    exact Or.inr ⟨β, ρ₂, β₂, rfl, rfl, hr⟩
  | i :: is, ρ, ρ₂, ρf, β, β₂, h, hr => by
    simp only [List.foldlM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨ρ1, h1, h2⟩ := h
    obtain ⟨v, rfl, h1'⟩ := step_ext h1 hr.1
    have hb := refBound_congr (E := E) (rel_ops hr h1)
    rw [refRun_cons, refRun_cons, h1, h1']
    simp only [Option.bind_eq_bind, Option.bind_some, ← hb]
    have hd : (ρ.set (Trace.dst i) v) (Trace.dst i) = some v := by simp [Env.set]
    have hd₂ : (ρ₂.set (Trace.dst i) v) (Trace.dst i) = some v := by simp [Env.set]
    rcases hbv : refBound P E ρ β i with _ | b
    · left; simp
    simp only [Option.bind_some, hd, hd₂]
    by_cases hg : 2 * b < P.src.modulus v.level
    · simp only [hg, guard, if_true, Option.pure_def, Option.bind_some]
      exact refRun_frame is _ _ ρf _ _ h2 (rel_set hr _ v b)
    · left; simp [hg, guard]

theorem refRun_nodst : ∀ (body : List Instr) (ρ ρf : Env P.src) (β βf : Var → Option ℕ),
    refRun P E body ρ β = some (ρf, βf) → ∀ x, x ∉ body.map Trace.dst → ρf x = ρ x ∧ βf x = β x
  | [], ρ, ρf, β, βf, h, x, _ => by
    simp only [Validation.Headline.NoiseAux.refRun_nil P E, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h; exact ⟨rfl, rfl⟩
  | i :: is, ρ, ρf, β, βf, h, x, hx => by
    obtain ⟨ρ', b, v, h1, -, -, -, h5⟩ := Validation.Headline.NoiseAux.refRun_cons_some P E h
    simp only [List.map_cons, List.mem_cons, not_or] at hx
    obtain ⟨e1, e2⟩ := refRun_nodst is _ _ _ _ h5 x hx.2
    obtain ⟨w, rfl⟩ := Validation.Headline.NoiseAux.step_set h1
    simp only [Env.set, hx.1, ↓reduceIte] at e1 e2
    exact ⟨e1, e2⟩

theorem refRun_fold : ∀ (body : List Instr) (ρ ρf : Env P.src) (β βf : Var → Option ℕ),
    refRun P E body ρ β = some (ρf, βf) → body.foldlM (step P.src) ρ = some ρf
  | [], ρ, ρf, β, βf, h => by
    simp only [Validation.Headline.NoiseAux.refRun_nil P E, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h; rfl
  | i :: is, ρ, ρf, β, βf, h => by
    obtain ⟨ρ', b, v, h1, -, -, -, h5⟩ := Validation.Headline.NoiseAux.refRun_cons_some P E h
    simp only [List.foldlM_cons, h1, Option.bind_eq_bind, Option.bind_some]
    exact refRun_fold is _ _ _ _ h5

theorem refRun_append (pre rest : List Instr) (ρ : Env P.src) (β : Var → Option ℕ) :
    refRun P E (pre ++ rest) ρ β = (refRun P E pre ρ β).bind fun r => refRun P E rest r.1 r.2 := by
  induction pre generalizing ρ β with
  | nil => rfl
  | cons i is ih =>
    rw [List.cons_append, refRun_cons, refRun_cons]
    simp only [Option.bind_eq_bind, ih, Option.bind_assoc]

end BGV

end Validation.IndCpaDFrame

namespace Validation.IndCpaDFrame
open Spec Spec.Source Challenge.Headline Challenge.BFV
open Validation.IndCpaDLM (Ext ext_envSet step_ext)

theorem mapM_congr_mem {α β : Type} {f g : α → Option β} :
    ∀ (l : List α), (∀ a ∈ l, f a = g a) → l.mapM f = l.mapM g
  | [], _ => rfl
  | a :: l, h => by
    simp only [List.mapM_cons, h a (by simp), mapM_congr_mem l (fun x hx => h x (by simp [hx]))]

theorem all_congr_mem {α : Type} {f g : α → Bool} :
    ∀ (l : List α), (∀ a ∈ l, f a = g a) → l.all f = l.all g
  | [], _ => rfl
  | a :: l, h => by
    simp only [List.all_cons, h a (by simp), all_congr_mem l (fun x hx => h x (by simp [hx]))]

/-! ## The BGV analysis of a program whose body extends another's -/

section BGVProg
variable {P : FullParams} {E : Trace.Budget}

/-- The initial bounds of `refAnalyze`. -/
def beta0 (P : FullParams) (prog : Program) : Var → Option ℕ := fun x =>
  (prog.inputs.find? (·.name = x)).map fun _ =>
    match prog.boundOf x with
    | some b => min b P.inputNoise
    | none => P.inputNoise

theorem refAnalyze_eq (P : FullParams) (E : Trace.Budget) (prog : Program) :
    refAnalyze P E prog = (do
      guard (P.src.kind = .bgv)
      guard (prog.inputs.all fun d => d.ok P.src)
      let r ← refRun P E prog.body (initEnv P.src prog fun _ => .exact 0) (beta0 P prog)
      guard (prog.outputs.all fun o => (r.1 o).isSome)
      let bs ← prog.outputs.mapM r.2
      pure (bs.foldl max 0)) := rfl

theorem rel_init (P : FullParams) (prog : Program) :
    ∀ x, (initEnv P.src prog (fun _ => .exact 0) x).isSome → (beta0 P prog x).isSome := by
  intro x hx
  simp only [initEnv, beta0, Option.isSome_map] at hx ⊢
  exact hx

/-- **The BGV reference analysis of `K` (body `pre ++ S.body`) equals that of `S`**, when the
analysis of `pre` succeeds and ends in environments extending `S`'s initial ones, `S` runs on
zero messages, the outputs are the same and the input checks agree. -/
theorem refAnalyze_frame (K S : Program) (pre : List Instr) (hK : K.body = pre ++ S.body)
    (hout : K.outputs = S.outputs)
    (hok : (K.inputs.all fun d => d.ok P.src) = (S.inputs.all fun d => d.ok P.src))
    (ρg : Env P.src) (βg : Var → Option ℕ)
    (hpre : refRun P E pre (initEnv P.src K fun _ => .exact 0) (beta0 P K) = some (ρg, βg))
    (hrel : Ext (initEnv P.src S fun _ => .exact 0) ρg ∧ Ext (beta0 P S) βg)
    (hS : (Source.eval P.src S fun _ => .exact 0).isSome) :
    refAnalyze P E K = refAnalyze P E S := by
  obtain ⟨ρS, hρS⟩ := Option.isSome_iff_exists.mp hS
  obtain ⟨hSok, hSfold, hSout⟩ := Validation.IndCpaDLM.eval_parts hρS
  rw [refAnalyze_eq, refAnalyze_eq, hK, refRun_append, hpre, hout, hok]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rcases refRun_frame (E := E) S.body _ ρg ρS _ βg hSfold ⟨hrel.1, hrel.2, rel_init P S⟩ with
    ⟨h1, h2⟩ | ⟨βf, ρ₂f, β₂f, h1, h2, hr⟩
  · simp only [h1, h2, Option.bind_none]
  · simp only [h1, h2, Option.bind_some]
    have ho : ∀ o ∈ S.outputs, (ρS o).isSome ∧ (ρ₂f o).isSome ∧ βf o = β₂f o := by
      intro o hoS
      have h := hSout o hoS
      exact ⟨h, by rw [← agree_of_ext hr.1 h]; exact h, agree_of_ext hr.2.1 (hr.2.2 o h)⟩
    have e1 : (S.outputs.all fun o => (ρS o).isSome) = true :=
      List.all_eq_true.mpr fun o h => (ho o h).1
    have e2 : (S.outputs.all fun o => (ρ₂f o).isSome) = true :=
      List.all_eq_true.mpr fun o h => (ho o h).2.1
    rw [e1, e2, mapM_congr_mem S.outputs fun o h => (ho o h).2.2]

theorem refAnalyze_ok {P : FullParams} {E : Trace.Budget} {prog : Program} {B : ℕ}
    (h : refAnalyze P E prog = some B) : (prog.inputs.all fun d => d.ok P.src) = true := by
  rw [refAnalyze_eq] at h
  by_contra hc
  simp [hc, guard] at h

/-- `Source.eval` of `K` extends that of `S`, under the hypotheses of `refAnalyze_frame`. -/
theorem eval_frame (K S : Program) (pre : List Instr) (hK : K.body = pre ++ S.body)
    (hout : K.outputs = S.outputs) (hKok : (K.inputs.all fun d => d.ok P.src) = true)
    (ρg : Env P.src)
    (hpre : pre.foldlM (step P.src) (initEnv P.src K fun _ => .exact 0) = some ρg)
    (hrel : Ext (initEnv P.src S fun _ => .exact 0) ρg) (ρS : Env P.src)
    (hS : Source.eval P.src S (fun _ => .exact 0) = some ρS) :
    ∃ ρK, Source.eval P.src K (fun _ => .exact 0) = some ρK ∧ Ext ρS ρK := by
  obtain ⟨-, hSfold, hSout⟩ := Validation.IndCpaDLM.eval_parts hS
  obtain ⟨ρK, hK1, hK2⟩ := Validation.IndCpaDLM.foldl_ext S.body _ _ ρS hSfold hrel
  have hf : K.body.foldlM (step P.src) (initEnv P.src K fun _ => .exact 0) = some ρK := by
    rw [hK, List.foldlM_append, hpre]; exact hK1
  refine ⟨ρK, ?_, hK2⟩
  have := Validation.IndCpaDLM.eval_of_parts (m := fun _ => 0) hKok hf (fun o ho => by
    rw [hout] at ho
    rw [← agree_of_ext hK2 (hSout o ho)]; exact hSout o ho)
  exact this

theorem outputsUnderS_frame (K S : Program) (hout : K.outputs = S.outputs) (ρK ρS : Env P.src)
    (hK : Source.eval P.src K (fun _ => .exact 0) = some ρK)
    (hS : Source.eval P.src S (fun _ => .exact 0) = some ρS) (hx : Ext ρS ρK) :
    Encrypt.outputsUnderS? P.src K = Encrypt.outputsUnderS? P.src S := by
  obtain ⟨-, -, hSout⟩ := Validation.IndCpaDLM.eval_parts hS
  unfold Encrypt.outputsUnderS? Encrypt.outputKey?
  rw [hout]
  simp only [hK, hS, Option.bind_eq_bind, Option.bind_some]
  exact all_congr_mem S.outputs fun o ho => by rw [← agree_of_ext hx (hSout o ho)]

theorem eval_restrict {Pr : Params} {S : Program} {ρS : Env Pr}
    (hS : Source.eval Pr S (fun _ => .exact 0) = some ρS) (os : List Var)
    (hos : ∀ o ∈ os, (ρS o).isSome) :
    Source.eval Pr { S with outputs := os } (fun _ => .exact 0) = some ρS := by
  obtain ⟨hok, hf, -⟩ := Validation.IndCpaDLM.eval_parts hS
  exact Validation.IndCpaDLM.eval_of_parts (m := fun _ => 0) hok hf hos

theorem certifyProfile_eq (P : FullParams) (E : Trace.Budget) (prog : Program) (sw : Bool) :
    Challenge.Profile.certifyProfile? P E prog sw = (do
      guard (schemeParamsOK? P)
      guard (P.src.kind = .bgv)
      guard (!prog.outputs.isEmpty)
      guard (Challenge.Certify.inputsMsgOK? P prog)
      let B ← refAnalyze P E prog
      let outs ← prog.outputs.mapM fun o =>
        (Challenge.Certify.outputBound? P E prog sw o).map fun b => (o, b)
      pure (B, outs)) := rfl

theorem outputBound_eq (P : FullParams) (E : Trace.Budget) (prog : Program) (sw : Bool)
    (o : Var) : Challenge.Certify.outputBound? P E prog sw o = (do
      let b ← refAnalyze P E { prog with outputs := [o] }
      guard (Encrypt.certOK? P { prog with outputs := [o] } b sw)
      pure b) := rfl

/-- **The BGV profile certificate of `K` equals that of `S`** (hypotheses of
`refAnalyze_frame`). -/
theorem certifyProfile_frame (K S : Program) (pre : List Instr) (hK : K.body = pre ++ S.body)
    (hout : K.outputs = S.outputs)
    (hok : (K.inputs.all fun d => d.ok P.src) = (S.inputs.all fun d => d.ok P.src))
    (hmsg : Challenge.Certify.inputsMsgOK? P K = Challenge.Certify.inputsMsgOK? P S)
    (ρg : Env P.src) (βg : Var → Option ℕ)
    (hpre : refRun P E pre (initEnv P.src K fun _ => .exact 0) (beta0 P K) = some (ρg, βg))
    (hrel : Ext (initEnv P.src S fun _ => .exact 0) ρg ∧ Ext (beta0 P S) βg)
    (hS : (Source.eval P.src S fun _ => .exact 0).isSome) :
    Challenge.Profile.certifyProfile? P E K false = Challenge.Profile.certifyProfile? P E S false := by
  obtain ⟨ρS, hρS⟩ := Option.isSome_iff_exists.mp hS
  obtain ⟨-, -, hSout⟩ := Validation.IndCpaDLM.eval_parts hρS
  have hfold := refRun_fold pre _ _ _ _ hpre
  rw [certifyProfile_eq, certifyProfile_eq, hout, hmsg,
    refAnalyze_frame K S pre hK hout hok ρg βg hpre hrel hS]
  have hmap : (S.outputs.mapM fun o =>
      (Challenge.Certify.outputBound? P E K false o).map fun b => (o, b)) =
      S.outputs.mapM fun o => (Challenge.Certify.outputBound? P E S false o).map fun b => (o, b) :=
    mapM_congr_mem S.outputs fun o ho => by
      have hS' := eval_restrict hρS [o] (by simpa using hSout o ho)
      have hra := refAnalyze_frame (E := E) { K with outputs := [o] } { S with outputs := [o] }
        pre hK rfl hok ρg βg hpre hrel (by rw [hS']; rfl)
      rw [outputBound_eq, outputBound_eq, hra]
      rcases hb : refAnalyze P E { S with outputs := [o] } with _ | b
      · rfl
      have hKok := refAnalyze_ok (hra.trans hb)
      obtain ⟨ρK, hK', hx⟩ := eval_frame { K with outputs := [o] } { S with outputs := [o] } pre
        hK rfl hKok ρg hfold hrel.1 ρS hS'
      have hu := outputsUnderS_frame { K with outputs := [o] } { S with outputs := [o] } rfl ρK ρS
        hK' hS' hx
      simp only [Option.bind_eq_bind, Option.bind_some, Encrypt.certOK?, hu, Bool.not_false,
        Bool.true_or]
  rw [hmap]

theorem refAnalyze_eval {P : FullParams} {E : Trace.Budget} {prog : Program} {B : ℕ}
    (h : refAnalyze P E prog = some B) : (Source.eval P.src prog fun _ => .exact 0).isSome := by
  have hok := refAnalyze_ok h
  rw [refAnalyze_eq] at h
  rcases hr : refRun P E prog.body (initEnv P.src prog fun _ => .exact 0) (beta0 P prog) with
    _ | ⟨ρf, βf⟩
  · simp [hr] at h
  have hf := refRun_fold _ _ _ _ _ hr
  have hout : (prog.outputs.all fun o => (ρf o).isSome) = true := by
    by_contra hc
    rw [List.all_eq_true] at hc
    simp [hr, hc, guard] at h
  rw [Validation.IndCpaDLM.eval_of_parts (m := fun _ => 0) hok hf
    (fun o ho => List.all_eq_true.mp hout o ho)]
  rfl

theorem certifyProfile_analyze {P : FullParams} {E : Trace.Budget} {prog : Program}
    {r : ℕ × List (Var × ℕ)} (h : Challenge.Profile.certifyProfile? P E prog false = some r) :
    ∃ B, refAnalyze P E prog = some B := by
  rw [certifyProfile_eq] at h
  rcases hB : refAnalyze P E prog with _ | B
  · simp [hB] at h
  · exact ⟨B, rfl⟩

theorem refAnalyze_run {P : FullParams} {E : Trace.Budget} {prog : Program} {B : ℕ}
    (h : refAnalyze P E prog = some B) : ∃ ρ β,
      refRun P E prog.body (initEnv P.src prog fun _ => .exact 0) (beta0 P prog) = some (ρ, β) := by
  rw [refAnalyze_eq] at h
  rcases hr : refRun P E prog.body (initEnv P.src prog fun _ => .exact 0) (beta0 P prog) with
    _ | ⟨ρf, βf⟩
  · simp [hr] at h
  · exact ⟨ρf, βf, rfl⟩

end BGVProg

end Validation.IndCpaDFrame

/-! ## Checks along the zero-message replay -/

namespace Validation.IndCpaDFrame
open Spec Spec.Source Spec.Budget Challenge.Headline Challenge.BFV
open Validation.IndCpaDLM (Ext ext_envSet step_ext)

/-- A check made instruction by instruction along the replay (the shape of `ksNeed`, `bfvNeed`). -/
def needFold {Pr : Params} (f : Env Pr → Instr → Bool) : List Instr → Env Pr → Bool
  | [], _ => true
  | i :: is, ρ => f ρ i && (step Pr ρ i).elim true (needFold f is)

/-- The check reads only the operands. -/
def Local {Pr : Params} (f : Env Pr → Instr → Bool) : Prop :=
  ∀ ρ ρ₂ i, (∀ y ∈ ops i, ρ y = ρ₂ y) → f ρ i = f ρ₂ i

theorem needFold_frame {Pr : Params} {f : Env Pr → Instr → Bool} (hf : Local f) :
    ∀ (body : List Instr) (ρ ρ₂ ρf : Env Pr), body.foldlM (step Pr) ρ = some ρf → Ext ρ ρ₂ →
      needFold f body ρ = needFold f body ρ₂
  | [], _, _, _, _, _ => rfl
  | i :: is, ρ, ρ₂, ρf, h, hx => by
    simp only [List.foldlM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨ρ1, h1, h2⟩ := h
    obtain ⟨v, rfl, h1'⟩ := step_ext h1 hx
    have hfi := hf ρ ρ₂ i fun y hy => agree_of_ext hx (step_ops h1 y hy)
    show (f ρ i && (step Pr ρ i).elim true (needFold f is)) =
      (f ρ₂ i && (step Pr ρ₂ i).elim true (needFold f is))
    rw [hfi, h1, h1']
    simp only [Option.elim_some]
    rw [needFold_frame hf is _ _ ρf h2 (ext_envSet hx _ v)]

theorem needFold_append {Pr : Params} (f : Env Pr → Instr → Bool) :
    ∀ (pre rest : List Instr) (ρ ρ' : Env Pr), pre.foldlM (step Pr) ρ = some ρ' →
      needFold f (pre ++ rest) ρ = (needFold f pre ρ && needFold f rest ρ')
  | [], rest, ρ, ρ', h => by
    simp only [List.foldlM_nil, Option.pure_def, Option.some.injEq] at h
    subst h; simp [needFold]
  | i :: is, rest, ρ, ρ', h => by
    simp only [List.foldlM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨ρ1, h1, h2⟩ := h
    show (f ρ i && (step Pr ρ i).elim true (needFold f (is ++ rest))) =
      ((f ρ i && (step Pr ρ i).elim true (needFold f is)) && needFold f rest ρ')
    rw [h1]
    simp only [Option.elim_some]
    rw [needFold_append f is rest ρ1 ρ' h2, Bool.and_assoc]

section KS
variable (P : FullParams) (lay : KSLayout) (rots : List ℕ) (E : Trace.Budget)

def ksNeedAtV (ρ : Env P.src) : Instr → Bool
  | .relin _ a => (ρ a).elim true fun x => decide (ksBoundAt P lay x.level ≤ E.keySwitch)
  | .keySwitch _ a => (ρ a).elim true fun x =>
      decide (ksBoundAt P lay x.level ≤ E.keySwitch) && decide (x.key ∈ rots)
  | .modSwitch _ a => (ρ a).elim true fun x =>
      decide (msBudgetAt P x.parts ≤ E.modSwitchAt x.parts)
  | _ => true

theorem ksNeedAt_eq (ρ : Env P.src) (i : Instr) :
    Challenge.IndCpaDProfile.ksNeedAt P lay rots E ρ i = ksNeedAtV P lay rots E ρ i := by
  cases i <;> rfl

theorem ksNeed_eq : ∀ (body : List Instr) (ρ : Env P.src),
    Challenge.IndCpaDProfile.ksNeed P lay rots E body ρ =
      needFold (Challenge.IndCpaDProfile.ksNeedAt P lay rots E) body ρ
  | [], _ => rfl
  | i :: is, ρ => by
    show (Challenge.IndCpaDProfile.ksNeedAt P lay rots E ρ i &&
        (step P.src ρ i).elim true (Challenge.IndCpaDProfile.ksNeed P lay rots E is)) =
      (Challenge.IndCpaDProfile.ksNeedAt P lay rots E ρ i &&
        (step P.src ρ i).elim true (needFold (Challenge.IndCpaDProfile.ksNeedAt P lay rots E) is))
    congr 1
    cases step P.src ρ i with
    | none => rfl
    | some ρ' => exact ksNeed_eq is ρ'

theorem ksNeedAt_local : Local (Challenge.IndCpaDProfile.ksNeedAt P lay rots E) := by
  intro ρ ρ₂ i h
  rw [ksNeedAt_eq, ksNeedAt_eq]
  cases i <;> simp only [ops, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq] at h <;> simp only [ksNeedAtV, h]

end KS

section BFVNeed
variable (P : FullParams) (lay : KSLayout) (rots : List ℕ) (E : TraceBFV.Budget)

def bfvNeedAtV (ρ : Env P.src) : Instr → Bool
  | .mul _ a b => (ρ a).elim true fun x => (ρ b).elim true fun y =>
      decide (BudgetBFV.mulLift P ≤ E.mulLift) && decide (BudgetBFV.mulRound P ≤ E.mulRound) &&
        decide (x.parts = 2) && decide (y.parts = 2)
  | .square _ a => (ρ a).elim true fun x =>
      decide (BudgetBFV.mulLift P ≤ E.mulLift) && decide (BudgetBFV.mulRound P ≤ E.mulRound) &&
        decide (x.parts = 2)
  | .relin _ a => (ρ a).elim true fun x => decide (BudgetBFV.ksBoundAt P lay x.level ≤ E.keySwitch)
  | .keySwitch _ a => (ρ a).elim true fun x =>
      decide (BudgetBFV.ksBoundAt P lay x.level ≤ E.keySwitch) && decide (x.key ∈ rots)
  | .modSwitch _ a => (ρ a).elim true fun x =>
      decide (BudgetBFV.msBudget P ≤ E.modSwitch) && decide (x.parts = 2)
  | _ => true

theorem bfvNeedAt_eq (ρ : Env P.src) (i : Instr) :
    Challenge.IndCpaDLM.bfvNeedAt P lay rots E ρ i = bfvNeedAtV P lay rots E ρ i := by
  cases i <;> rfl

theorem bfvNeed_eq : ∀ (body : List Instr) (ρ : Env P.src),
    Challenge.IndCpaDLM.bfvNeed P lay rots E body ρ =
      needFold (Challenge.IndCpaDLM.bfvNeedAt P lay rots E) body ρ
  | [], _ => rfl
  | i :: is, ρ => by
    show (Challenge.IndCpaDLM.bfvNeedAt P lay rots E ρ i &&
        (step P.src ρ i).elim true (Challenge.IndCpaDLM.bfvNeed P lay rots E is)) =
      (Challenge.IndCpaDLM.bfvNeedAt P lay rots E ρ i &&
        (step P.src ρ i).elim true (needFold (Challenge.IndCpaDLM.bfvNeedAt P lay rots E) is))
    congr 1
    cases step P.src ρ i with
    | none => rfl
    | some ρ' => exact bfvNeed_eq is ρ'

theorem bfvNeedAt_local : Local (Challenge.IndCpaDLM.bfvNeedAt P lay rots E) := by
  intro ρ ρ₂ i h
  rw [bfvNeedAt_eq, bfvNeedAt_eq]
  cases i <;> simp only [ops, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq] at h <;> simp only [bfvNeedAtV, h]

end BFVNeed

end Validation.IndCpaDFrame


/-! ## The BFV reference analysis -/

namespace Validation.IndCpaDFrame
open Spec Spec.Source Challenge.Headline Challenge.BFV
open Spec.TraceBFV (Bnd)
open Validation.IndCpaDLM (Ext ext_envSet step_ext)

section BFV
variable {P : FullParams} {E : TraceBFV.Budget}

def refBoundBFVV (P : FullParams) (E : TraceBFV.Budget) (ℓ : ℕ) (β : Var → Option Bnd) :
    Instr → Option Bnd
  | .add _ a b | .sub _ a b =>
    match β a, β b with
    | some (.ct x), some (.ct y) => some (.ct (x + y + P.src.modulus ℓ % P.src.t))
    | _, _ => none
  | .addPlain _ a p | .subPlain _ a p =>
    match β a, β p with
    | some (.ct x), some (.pt y) =>
      some (.ct (x + P.src.modulus ℓ % P.src.t * ((y + P.src.t - 1) / P.src.t) + E.plainAdd))
    | _, _ => none
  | .mulPlain _ a p =>
    match β a, β p with
    | some (.ct x), some (.pt y) =>
      some (.ct (P.src.N * y * (x + P.src.modulus ℓ % P.src.t)))
    | _, _ => none
  | .mul _ a b =>
    match β a, β b with
    | some (.ct x), some (.ct y) =>
      some (.ct (mulBound P.src.N P.src.t (P.src.modulus ℓ) E.mulLift E.mulRound x y))
    | _, _ => none
  | .square _ a =>
    match β a with
    | some (.ct x) =>
      some (.ct (mulBound P.src.N P.src.t (P.src.modulus ℓ) E.mulLift E.mulRound x x))
    | _ => none
  | .mulConst _ a c =>
    match β a with
    | some (.ct x) => some (.ct (c.natAbs * (x + P.src.modulus ℓ % P.src.t)))
    | _ => none
  | .copy _ a | .toEval _ a | .toCoeff _ a => β a
  | .automorph _ a _ =>
    match β a with
    | some (.ct x) => some (.ct (x + P.src.modulus ℓ % P.src.t))
    | _ => none
  | .relin _ a | .keySwitch _ a =>
    match β a with
    | some (.ct x) => some (.ct (x + E.keySwitch))
    | _ => none
  | .modSwitch _ a =>
    match β a, P.src.qs[ℓ]? with
    | some (.ct x), some q => some (.ct (x / q + E.modSwitch + P.src.modulus ℓ % P.src.t))
    | _, _ => none
  | .dropLimbs _ _ _ => none

theorem refBoundBFV_eq (ℓ : ℕ) (β : Var → Option Bnd) (i : Instr) :
    refBoundBFV P E ℓ β i = refBoundBFVV P E ℓ β i := by
  cases i <;> rfl

theorem refBoundBFV_congr {ℓ : ℕ} {β β₂ : Var → Option Bnd} {i : Instr}
    (h : ∀ y ∈ ops i, β y = β₂ y) : refBoundBFV P E ℓ β i = refBoundBFV P E ℓ β₂ i := by
  rw [refBoundBFV_eq, refBoundBFV_eq]
  cases i <;> simp only [ops, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq] at h <;> simp only [refBoundBFVV, h]

def domainOKV {Pr : Params} (ρ : Env Pr) : Instr → Bool
  | .mul _ a b =>
    match ρ a, ρ b with
    | some x, some y => x.parts == 2 && y.parts == 2
    | _, _ => false
  | .square _ a | .modSwitch _ a =>
    match ρ a with
    | some x => x.parts == 2
    | none => false
  | _ => true

theorem domainOK_eq {Pr : Params} (ρ : Env Pr) (i : Instr) : domainOK ρ i = domainOKV ρ i := by
  cases i <;> rfl

theorem domainOK_congr {Pr : Params} {ρ ρ₂ : Env Pr} {i : Instr}
    (h : ∀ y ∈ ops i, ρ y = ρ₂ y) : domainOK ρ i = domainOK ρ₂ i := by
  rw [domainOK_eq, domainOK_eq]
  cases i <;> simp only [ops, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq] at h <;> simp only [domainOKV, h]

/-- **Locality of the BFV reference analysis.** -/
theorem refRunBFV_frame : ∀ (body : List Instr) (ρ ρ₂ ρf : Env P.src) (β β₂ : Var → Option Bnd),
    body.foldlM (step P.src) ρ = some ρf → Rel ρ ρ₂ β β₂ →
    (refRunBFV P E body ρ β = none ∧ refRunBFV P E body ρ₂ β₂ = none) ∨
    ∃ βf ρ₂f β₂f, refRunBFV P E body ρ β = some (ρf, βf) ∧
      refRunBFV P E body ρ₂ β₂ = some (ρ₂f, β₂f) ∧ Rel ρf ρ₂f βf β₂f
  | [], ρ, ρ₂, ρf, β, β₂, h, hr => by
    simp only [List.foldlM_nil, Option.pure_def, Option.some.injEq] at h
    subst h
    exact Or.inr ⟨β, ρ₂, β₂, rfl, rfl, hr⟩
  | i :: is, ρ, ρ₂, ρf, β, β₂, h, hr => by
    simp only [List.foldlM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨ρ1, h1, h2⟩ := h
    obtain ⟨v, rfl, h1'⟩ := step_ext h1 hr.1
    have hops := rel_ops hr h1
    have hd := domainOK_congr (i := i) fun y hy => (hops y hy).1
    have hb := refBoundBFV_congr (P := P) (E := E) (ℓ := v.level) (i := i) fun y hy => (hops y hy).2
    rw [Validation.BFV.PerInstrAux.refRun_cons, Validation.BFV.PerInstrAux.refRun_cons, ← hd,
      h1, h1']
    have hdv : (ρ.set (Trace.dst i) v) (Trace.dst i) = some v := by simp [Env.set]
    have hdv₂ : (ρ₂.set (Trace.dst i) v) (Trace.dst i) = some v := by simp [Env.set]
    cases hdo : domainOK ρ i
    · left; simp [guard]
    simp only [guard, if_true, Option.pure_def, Option.bind_eq_bind, Option.bind_some, hdv, hdv₂,
      ← hb]
    rcases hbv : refBoundBFV P E v.level β i with _ | b
    · left; simp
    simp only [Option.bind_some]
    by_cases hg : bndOK P v.level b = true
    · simp only [hg, if_true, Option.bind_some]
      exact refRunBFV_frame is _ _ ρf _ _ h2 (rel_set hr _ v b)
    · left; simp [hg]

theorem refRunBFV_nodst : ∀ (body : List Instr) (ρ ρf : Env P.src) (β βf : Var → Option Bnd),
    refRunBFV P E body ρ β = some (ρf, βf) → ∀ x, x ∉ body.map Trace.dst →
      ρf x = ρ x ∧ βf x = β x
  | [], ρ, ρf, β, βf, h, x, _ => by
    simp only [Validation.BFV.SoundAux.refRun_nil P E, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h; exact ⟨rfl, rfl⟩
  | i :: is, ρ, ρf, β, βf, h, x, hx => by
    obtain ⟨ρ', v, b, h1, -, -, -, h5, -⟩ := Validation.BFV.SoundAux.refRun_cons_some P E h
    simp only [List.map_cons, List.mem_cons, not_or] at hx
    obtain ⟨e1, e2⟩ := refRunBFV_nodst is _ _ _ _ h5 x hx.2
    obtain ⟨w, rfl⟩ := Validation.Headline.NoiseAux.step_set h1
    simp only [Env.set, hx.1, ↓reduceIte] at e1 e2
    exact ⟨e1, e2⟩

theorem refRunBFV_fold : ∀ (body : List Instr) (ρ ρf : Env P.src) (β βf : Var → Option Bnd),
    refRunBFV P E body ρ β = some (ρf, βf) → body.foldlM (step P.src) ρ = some ρf
  | [], ρ, ρf, β, βf, h => by
    simp only [Validation.BFV.SoundAux.refRun_nil P E, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h; rfl
  | i :: is, ρ, ρf, β, βf, h => by
    obtain ⟨ρ', v, b, h1, -, -, -, h5, -⟩ := Validation.BFV.SoundAux.refRun_cons_some P E h
    simp only [List.foldlM_cons, h1, Option.bind_eq_bind, Option.bind_some]
    exact refRunBFV_fold is _ _ _ _ h5

theorem refRunBFV_append (pre rest : List Instr) (ρ : Env P.src) (β : Var → Option Bnd) :
    refRunBFV P E (pre ++ rest) ρ β =
      (refRunBFV P E pre ρ β).bind fun r => refRunBFV P E rest r.1 r.2 := by
  induction pre generalizing ρ β with
  | nil => rfl
  | cons i is ih =>
    rw [List.cons_append, Validation.BFV.PerInstrAux.refRun_cons,
      Validation.BFV.PerInstrAux.refRun_cons]
    simp only [Option.bind_eq_bind, ih, Option.bind_assoc]

end BFV

end Validation.IndCpaDFrame

namespace Validation.IndCpaDFrame
open Spec Spec.Source Challenge.Headline Challenge.BFV
open Spec.TraceBFV (Bnd)
open Validation.IndCpaDLM (Ext ext_envSet step_ext)

section BFVProg
variable {P : FullParams} {E : TraceBFV.Budget}

/-- The initial bounds of `refAnalyzeBFVAt`. -/
def beta0B (P : FullParams) (prog : Program) : Var → Option Bnd := fun x =>
  (prog.inputs.find? (·.name = x)).map fun d =>
    if d.parts = 1 then .pt (TraceBFV.inputBound P prog d) else .ct (TraceBFV.inputBound P prog d)

theorem refAnalyzeBFV_eq (P : FullParams) (E : TraceBFV.Budget) (prog : Program) :
    refAnalyzeBFVAt P (fun _ => E) prog = (do
      guard (P.src.kind = .bfv)
      guard (prog.inputs.all fun d => d.ok P.src)
      let r ← refRunBFV P E prog.body (initEnv P.src prog fun _ => .exact 0) (beta0B P prog)
      guard (prog.outputs.all fun o => (r.1 o).isSome)
      let bs ← prog.outputs.mapM (ctBound r.2)
      pure (bs.foldl max 0)) := by
  rw [← Validation.BFV.PerInstrAux.refRunAt_const P E prog.body 0]
  rfl

theorem ctBound_eq (β : Var → Option Bnd) (o : Var) :
    ctBound β o = (match β o with
      | some (.ct b) => some b
      | _ => none) := rfl

theorem rel_initB (P : FullParams) (prog : Program) :
    ∀ x, (initEnv P.src prog (fun _ => .exact 0) x).isSome → (beta0B P prog x).isSome := by
  intro x hx
  simp only [initEnv, beta0B, Option.isSome_map] at hx ⊢
  exact hx

theorem refAnalyzeBFV_frame (K S : Program) (pre : List Instr) (hK : K.body = pre ++ S.body)
    (hout : K.outputs = S.outputs)
    (hok : (K.inputs.all fun d => d.ok P.src) = (S.inputs.all fun d => d.ok P.src))
    (ρg : Env P.src) (βg : Var → Option Bnd)
    (hpre : refRunBFV P E pre (initEnv P.src K fun _ => .exact 0) (beta0B P K) = some (ρg, βg))
    (hrel : Ext (initEnv P.src S fun _ => .exact 0) ρg ∧ Ext (beta0B P S) βg)
    (hS : (Source.eval P.src S fun _ => .exact 0).isSome) :
    refAnalyzeBFVAt P (fun _ => E) K = refAnalyzeBFVAt P (fun _ => E) S := by
  obtain ⟨ρS, hρS⟩ := Option.isSome_iff_exists.mp hS
  obtain ⟨hSok, hSfold, hSout⟩ := Validation.IndCpaDLM.eval_parts hρS
  rw [refAnalyzeBFV_eq, refAnalyzeBFV_eq, hK, refRunBFV_append, hpre, hout, hok]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rcases refRunBFV_frame (E := E) S.body _ ρg ρS _ βg hSfold ⟨hrel.1, hrel.2, rel_initB P S⟩ with
    ⟨h1, h2⟩ | ⟨βf, ρ₂f, β₂f, h1, h2, hr⟩
  · simp only [h1, h2, Option.bind_none]
  · simp only [h1, h2, Option.bind_some]
    have ho : ∀ o ∈ S.outputs, (ρS o).isSome ∧ (ρ₂f o).isSome ∧ βf o = β₂f o := by
      intro o hoS
      have h := hSout o hoS
      exact ⟨h, by rw [← agree_of_ext hr.1 h]; exact h, agree_of_ext hr.2.1 (hr.2.2 o h)⟩
    have e1 : (S.outputs.all fun o => (ρS o).isSome) = true :=
      List.all_eq_true.mpr fun o h => (ho o h).1
    have e2 : (S.outputs.all fun o => (ρ₂f o).isSome) = true :=
      List.all_eq_true.mpr fun o h => (ho o h).2.1
    have hm : S.outputs.mapM (ctBound βf) = S.outputs.mapM (ctBound β₂f) :=
      mapM_congr_mem _ fun o h => by rw [ctBound_eq, ctBound_eq, (ho o h).2.2]
    rw [e1, e2, hm]

theorem refAnalyzeBFV_ok {prog : Program} {B : ℕ}
    (h : refAnalyzeBFVAt P (fun _ => E) prog = some B) :
    (prog.inputs.all fun d => d.ok P.src) = true := by
  rw [refAnalyzeBFV_eq] at h
  by_contra hc
  simp [hc, guard] at h

theorem refAnalyzeBFV_run {prog : Program} {B : ℕ}
    (h : refAnalyzeBFVAt P (fun _ => E) prog = some B) : ∃ ρ β,
      refRunBFV P E prog.body (initEnv P.src prog fun _ => .exact 0) (beta0B P prog) =
        some (ρ, β) := by
  rw [refAnalyzeBFV_eq] at h
  rcases hr : refRunBFV P E prog.body (initEnv P.src prog fun _ => .exact 0) (beta0B P prog) with
    _ | ⟨ρf, βf⟩
  · simp [hr] at h
  · exact ⟨ρf, βf, rfl⟩

theorem refAnalyzeBFV_eval {prog : Program} {B : ℕ}
    (h : refAnalyzeBFVAt P (fun _ => E) prog = some B) :
    (Source.eval P.src prog fun _ => .exact 0).isSome := by
  have hok := refAnalyzeBFV_ok h
  rw [refAnalyzeBFV_eq] at h
  rcases hr : refRunBFV P E prog.body (initEnv P.src prog fun _ => .exact 0) (beta0B P prog) with
    _ | ⟨ρf, βf⟩
  · simp [hr] at h
  have hf := refRunBFV_fold _ _ _ _ _ hr
  have hout : (prog.outputs.all fun o => (ρf o).isSome) = true := by
    by_contra hc
    rw [List.all_eq_true] at hc
    simp [hr, hc, guard] at h
  rw [Validation.IndCpaDLM.eval_of_parts (m := fun _ => 0) hok hf
    (fun o ho => List.all_eq_true.mp hout o ho)]
  rfl

theorem certifyBFVProfile_eq (P : FullParams) (E : ℕ → TraceBFV.Budget) (prog : Program) :
    Challenge.Profile.certifyBFVProfile? P E prog = (do
      guard (schemeParamsOK? P)
      guard (P.src.kind = .bfv)
      guard (!prog.outputs.isEmpty)
      guard (Challenge.Profile.inputsDecOK P prog)
      guard (Challenge.CertifyBFV.plainBoundsOK P prog)
      guard (P.src.t - 1 ≤ P.src.qs.headD 0 / 2)
      let B ← refAnalyzeBFVAt P E prog
      guard (Encrypt.outputsUnderS? P.src prog)
      let outs ← prog.outputs.mapM fun o =>
        (refAnalyzeBFVAt P E { prog with outputs := [o] }).map fun b => (o, b)
      pure (B, outs)) := rfl

theorem certifyBFVProfile_frame (K S : Program) (pre : List Instr) (hK : K.body = pre ++ S.body)
    (hout : K.outputs = S.outputs)
    (hok : (K.inputs.all fun d => d.ok P.src) = (S.inputs.all fun d => d.ok P.src))
    (hdec : Challenge.Profile.inputsDecOK P K = Challenge.Profile.inputsDecOK P S)
    (hplain : Challenge.CertifyBFV.plainBoundsOK P K = Challenge.CertifyBFV.plainBoundsOK P S)
    (ρg : Env P.src) (βg : Var → Option Bnd)
    (hpre : refRunBFV P E pre (initEnv P.src K fun _ => .exact 0) (beta0B P K) = some (ρg, βg))
    (hrel : Ext (initEnv P.src S fun _ => .exact 0) ρg ∧ Ext (beta0B P S) βg)
    (hS : (Source.eval P.src S fun _ => .exact 0).isSome) :
    Challenge.Profile.certifyBFVProfile? P (fun _ => E) K =
      Challenge.Profile.certifyBFVProfile? P (fun _ => E) S := by
  obtain ⟨ρS, hρS⟩ := Option.isSome_iff_exists.mp hS
  obtain ⟨-, -, hSout⟩ := Validation.IndCpaDLM.eval_parts hρS
  have hfold := refRunBFV_fold _ _ _ _ _ hpre
  have hra := refAnalyzeBFV_frame K S pre hK hout hok ρg βg hpre hrel hS
  have hmap : (S.outputs.mapM fun o =>
      (refAnalyzeBFVAt P (fun _ => E) { K with outputs := [o] }).map fun b => (o, b)) =
      S.outputs.mapM fun o =>
        (refAnalyzeBFVAt P (fun _ => E) { S with outputs := [o] }).map fun b => (o, b) :=
    mapM_congr_mem S.outputs fun o ho => by
      have hS' := eval_restrict hρS [o] (by simpa using hSout o ho)
      rw [refAnalyzeBFV_frame (E := E) { K with outputs := [o] } { S with outputs := [o] } pre hK
        rfl hok ρg βg hpre hrel (by rw [hS']; rfl)]
  rw [certifyBFVProfile_eq, certifyBFVProfile_eq, hout, hdec, hplain, hra, hmap]
  rcases hb : refAnalyzeBFVAt P (fun _ => E) S with _ | B
  · rfl
  have hKok := refAnalyzeBFV_ok (hra.trans hb)
  obtain ⟨ρK, hK', hx⟩ := eval_frame K S pre hK hout hKok ρg hfold hrel.1 ρS hρS
  rw [outputsUnderS_frame K S hout ρK ρS hK' hρS hx]

end BFVProg

end Validation.IndCpaDFrame
