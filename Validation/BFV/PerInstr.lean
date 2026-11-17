import Challenge.BFV.PerInstr
import Validation.BFV.Sound
import Validation.BFVMul.Cert

/-!
# Validation.BFV.PerInstr — proofs of the pins of `Challenge.BFV.PerInstr`

The inductions of `Validation.BFV.Sound` (`run_sound`, `refAnalyze_some`, `refAnalyze_sound`) with
the position of the instruction as an index; the step lemma `SoundAux.dst_ok` is used as it is, at
the budget `E n` of the instruction. The one-budget proofs are untouched.

Helper lemmas are in `Validation.BFV.PerInstrAux`; the pins in `Validation.BFV` and
`Validation.BFVMul`.
-/

namespace Validation.BFV.PerInstrAux
open Spec NPoly Scheme Source Correct Challenge.BFV
open Spec.TraceBFV (Bnd)
open Validation.Ring Validation.Scheme Validation.Source Validation.BFV.SoundAux

section Ref
variable (P : FullParams)

theorem refRunAt_nil (E : ℕ → TraceBFV.Budget) (n : ℕ) (ρ : Env P.src) (β : Var → Option Bnd) :
    refRunBFVAt P E n [] ρ β = some (ρ, β) := rfl

theorem refRunAt_cons (E : ℕ → TraceBFV.Budget) (n : ℕ) (i : Instr) (is : List Instr)
    (ρ : Env P.src) (β : Var → Option Bnd) :
    refRunBFVAt P E n (i :: is) ρ β = (do
      guard (domainOK ρ i)
      let ρ' ← step P.src ρ i
      let v ← ρ' (Trace.dst i)
      let b ← refBoundBFV P (E n) v.level β i
      guard (bndOK P v.level b)
      refRunBFVAt P E (n + 1) is ρ' (fun y => if y = Trace.dst i then some b else β y)) := rfl

theorem refRun_cons (E : TraceBFV.Budget) (i : Instr) (is : List Instr)
    (ρ : Env P.src) (β : Var → Option Bnd) :
    refRunBFV P E (i :: is) ρ β = (do
      guard (domainOK ρ i)
      let ρ' ← step P.src ρ i
      let v ← ρ' (Trace.dst i)
      let b ← refBoundBFV P E v.level β i
      guard (bndOK P v.level b)
      refRunBFV P E is ρ' (fun y => if y = Trace.dst i then some b else β y)) := rfl

theorem refRunAt_const (E : TraceBFV.Budget) : ∀ (body : List Instr) (n : ℕ) (ρ : Env P.src)
    (β : Var → Option Bnd), refRunBFVAt P (fun _ => E) n body ρ β = refRunBFV P E body ρ β
  | [], _, _, _ => rfl
  | i :: is, n, ρ, β => by
    have ih := fun ρ β => refRunAt_const E is (n + 1) ρ β
    rw [refRunAt_cons, refRun_cons]
    simp only [ih]

theorem refRunAt_congr (E E' : ℕ → TraceBFV.Budget) : ∀ (body : List Instr) (n : ℕ)
    (_ : ∀ j, j < body.length → E (n + j) = E' (n + j)) (ρ : Env P.src) (β : Var → Option Bnd),
    refRunBFVAt P E n body ρ β = refRunBFVAt P E' n body ρ β
  | [], _, _, _, _ => rfl
  | i :: is, n, h, ρ, β => by
    have h0 : E n = E' n := by simpa using h 0 (by simp)
    have ih := fun ρ β => refRunAt_congr E E' is (n + 1)
      (fun j hj => by
        have := h (j + 1) (by simpa using hj)
        rwa [show n + (j + 1) = n + 1 + j by omega] at this) ρ β
    rw [refRunAt_cons, refRunAt_cons, h0]
    simp only [ih]

theorem refRunAt_cons_some {E : ℕ → TraceBFV.Budget} {n : ℕ} {i : Instr} {is : List Instr}
    {ρ : Env P.src} {β : Var → Option Bnd}
    {r : Env P.src × (Var → Option Bnd)} (h : refRunBFVAt P E n (i :: is) ρ β = some r) :
    ∃ ρ' v b, step P.src ρ i = some ρ' ∧ ρ' (Trace.dst i) = some v ∧
      refBoundBFV P (E n) v.level β i = some b ∧ bndOK P v.level b = true ∧
      refRunBFVAt P E (n + 1) is ρ' (fun y => if y = Trace.dst i then some b else β y) = some r ∧
      domainOK ρ i = true := by
  rw [refRunAt_cons] at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, guard] at h
  obtain ⟨_, h0, ρ', h1, v, h2, b, h3, h4⟩ := h
  have hd : domainOK ρ i = true := by by_contra hd; simp [hd] at h0
  split_ifs at h4 with hq
  · exact ⟨ρ', v, b, h1, h2, h3, hq, by simpa using h4, hd⟩
  · simp at h4

end Ref

section Run
variable {P : FullParams}

theorem runAt_cons (E : ℕ → TraceBFV.Budget) (s : IntPoly P.src.N) (n : ℕ) (i : Instr)
    (is : List Instr) (ρ : Env P.src) (σ σf : Trace.CtEnv P) :
    TraceBFV.RunAt P E s n (i :: is) ρ σ σf ↔
      ∃ ρ' σ', step P.src ρ i = some ρ' ∧ TraceBFV.StepOK P (E n) s ρ ρ' σ σ' i ∧
        TraceBFV.RunAt P E s (n + 1) is ρ' σ' σf := Iff.rfl

theorem run_soundAt (hk : P.src.kind = .bfv) (hP : SchemeParamsOK P) (E : ℕ → TraceBFV.Budget)
    (s : IntPoly P.src.N) : ∀ (body : List Instr) (n : ℕ) (ρ : Env P.src) (β : Var → Option Bnd)
    (r : Env P.src × (Var → Option Bnd)), AllExact ρ →
    refRunBFVAt P E n body (zenv ρ) β = some r →
    ∃ ρf, body.foldlM (step P.src) ρ = some ρf ∧ r.1 = zenv ρf ∧
      ∀ σ σf, Inv P s ρ β σ → TraceBFV.RunAt P E s n body ρ σ σf → Inv P s ρf r.2 σf := by
  intro body
  induction body with
  | nil =>
    intro n ρ β r _ h
    rw [refRunAt_nil] at h
    cases h
    refine ⟨ρ, rfl, rfl, ?_⟩
    intro σ σf hinv hrun
    have : σf = σ := hrun
    subst this; exact hinv
  | cons i is ih =>
    intro n ρ β r hρ h
    obtain ⟨ρz', vz, b, h1, h3, h2, h4, h5, -⟩ := refRunAt_cons_some P h
    obtain ⟨hz, hex⟩ := step_zenv hk hρ i
    rw [hz] at h1
    obtain ⟨ρ', hs, rfl⟩ := Option.map_eq_some_iff.mp h1
    have hρ' := hex ρ' hs
    obtain ⟨ρf, hf, hr, hinvf⟩ := ih (n + 1) ρ' _ r hρ' h5
    refine ⟨ρf, ?_, hr, ?_⟩
    · simp only [List.foldlM_cons, hs, Option.bind_eq_bind, Option.bind_some]; exact hf
    intro σ σf hinv hrun
    obtain ⟨ρ'', σ', hs', hok, hrun'⟩ := (runAt_cons E s n i is ρ σ σf).mp hrun
    rw [hs] at hs'; cases hs'
    simp only [zenv] at h3
    obtain ⟨v, hv, rfl⟩ := Option.map_eq_some_iff.mp h3
    have h2' : refBoundBFV P (E n) v.level β i = some b := h2
    have h4' : bndOK P v.level b = true := h4
    obtain ⟨ct, hσ', hct⟩ := dst_ok hk hP (E n) s hinv h2' hs hv h4' hok
    refine hinvf σ' σf ?_ hrun'
    obtain ⟨w, hw⟩ := step_set hs
    intro y by' hy
    by_cases hyd : y = Trace.dst i
    · subst hyd
      simp only [ite_true, Option.some.injEq] at hy
      subst hy
      refine ⟨v, ct, hv, ?_, hct⟩
      rw [hσ']; simp [Trace.CtEnv.set]
    · simp only [hyd, ite_false] at hy
      obtain ⟨v', ct', h1', h2', h3'⟩ := hinv y by' hy
      refine ⟨v', ct', ?_, ?_, h3'⟩
      · rw [hw]; simp [Env.set, hyd, h1']
      · rw [hσ']; simp [Trace.CtEnv.set, hyd, h2']

end Run

section Main
variable {P : FullParams}

theorem refAnalyzeAt_eq (P : FullParams) (E : ℕ → TraceBFV.Budget) (prog : Program) :
    refAnalyzeBFVAt P E prog = (do
      guard (P.src.kind = .bfv)
      guard (prog.inputs.all fun d => d.ok P.src)
      let β₀ : Var → Option Bnd := fun x => (prog.inputs.find? (·.name = x)).map fun d =>
        if d.parts = 1 then .pt (TraceBFV.inputBound P prog d)
        else .ct (TraceBFV.inputBound P prog d)
      let (ρ, β) ← refRunBFVAt P E 0 prog.body (initEnv P.src prog fun _ => .exact 0) β₀
      guard (prog.outputs.all fun o => (ρ o).isSome)
      let bs ← prog.outputs.mapM (ctBound β)
      pure (bs.foldl max 0)) := rfl

theorem refAnalyze_eq (P : FullParams) (E : TraceBFV.Budget) (prog : Program) :
    refAnalyzeBFV P E prog = (do
      guard (P.src.kind = .bfv)
      guard (prog.inputs.all fun d => d.ok P.src)
      let β₀ : Var → Option Bnd := fun x => (prog.inputs.find? (·.name = x)).map fun d =>
        if d.parts = 1 then .pt (TraceBFV.inputBound P prog d)
        else .ct (TraceBFV.inputBound P prog d)
      let (ρ, β) ← refRunBFV P E prog.body (initEnv P.src prog fun _ => .exact 0) β₀
      guard (prog.outputs.all fun o => (ρ o).isSome)
      let bs ← prog.outputs.mapM (ctBound β)
      pure (bs.foldl max 0)) := rfl

theorem refAnalyzeAt_some {E : ℕ → TraceBFV.Budget} {prog : Program} {B : ℕ}
    (h : refAnalyzeBFVAt P E prog = some B) :
    P.src.kind = .bfv ∧ (prog.inputs.all fun d => d.ok P.src) = true ∧
      ∃ ρz β, refRunBFVAt P E 0 prog.body (initEnv P.src prog fun _ => .exact 0)
        (fun x => (prog.inputs.find? (·.name = x)).map fun d =>
          if d.parts = 1 then .pt (TraceBFV.inputBound P prog d)
          else .ct (TraceBFV.inputBound P prog d)) = some (ρz, β) ∧
      (prog.outputs.all fun o => (ρz o).isSome) = true ∧
      ∃ bs, prog.outputs.mapM (ctBound β) = some bs ∧ bs.foldl max 0 = B := by
  rw [refAnalyzeAt_eq] at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, guard] at h
  obtain ⟨_, h0, _, hd, ⟨ρz, β⟩, h1, _, h2, bs, h3, h4⟩ := h
  have hk : P.src.kind = .bfv := by by_contra hk; simp [hk] at h0
  have hd' : (prog.inputs.all fun d => d.ok P.src) = true := by by_contra hd'; simp [hd'] at hd
  by_cases hc : (prog.outputs.all fun o => (ρz o).isSome) = true
  · exact ⟨hk, hd', ρz, β, h1, hc, bs, h3, by simpa using h4⟩
  · simp [hc] at h2

theorem refAnalyzeAt_sound : NoiseSoundBFVAt refAnalyzeBFVAt := by
  intro P E prog B hP hk hB s msgs cts hin
  obtain ⟨-, hdecl, ρz, βf, hrun, hout, bs, hbs, hB'⟩ := refAnalyzeAt_some hB
  have hfind : ∀ x d, prog.inputs.find? (·.name = x) = some d → d.name = x ∧
      (∃ m, msgs x = .exact m) := by
    intro x d hd
    have hn : d.name = x := by simpa using List.find?_some hd
    have he := hin x d hd
    refine ⟨hn, ?_⟩
    rw [← hn]
    by_cases hp : d.parts = 1
    · simp only [hp, ↓reduceIte] at he
      obtain ⟨m, hm, -⟩ := plain_elim he
      exact ⟨m, hm⟩
    · simp only [hp, ↓reduceIte] at he
      obtain ⟨m, hm, -⟩ := enc_elim hk he
      exact ⟨m, hm⟩
  have hρ0 : AllExact (initEnv P.src prog msgs) := by
    intro x v hv
    simp only [initEnv, Option.map_eq_some_iff] at hv
    obtain ⟨d, hd, rfl⟩ := hv
    exact (hfind x d hd).2
  have hz0 : zenv (initEnv P.src prog msgs) = initEnv P.src prog fun _ => .exact 0 := by
    funext x; simp only [zenv, initEnv, Option.map_map]; rfl
  rw [← hz0] at hrun
  obtain ⟨ρf, hf, hr, hinv⟩ := run_soundAt hk hP E s prog.body 0 _ _ _ hρ0 hrun
  simp only at hr
  refine ⟨ρf, ?_, ?_⟩
  · have hfits : (prog.inputs.all fun dcl => (msgs dcl.name).fits P.src.kind) = true := by
      rw [List.all_eq_true]; intro dcl hdcl
      obtain ⟨d, hd⟩ : ∃ d, prog.inputs.find? (·.name = dcl.name) = some d := by
        rw [← Option.isSome_iff_exists, List.find?_isSome]
        exact ⟨dcl, hdcl, by simp⟩
      obtain ⟨m, hm⟩ := (hfind _ d hd).2
      rw [hm, hk]; rfl
    have hout' : (prog.outputs.all fun o => (ρf o).isSome) = true := by
      rw [hr] at hout; simpa [zenv] using hout
    simp only [List.all_eq_true] at hout'
    simp only [eval, hdecl, hfits, hf, guard, List.all_eq_true, Option.bind_eq_bind, ite_true,
      Option.pure_def, Option.bind_some]
    have hc : (∀ x ∈ prog.outputs, (ρf x).isSome = true) = True := eq_true hout'
    simp only [hc, ite_true, Option.bind_some]
  · intro σ hrunσ o ho
    have hinv0 : Inv P s (initEnv P.src prog msgs)
        (fun x => (prog.inputs.find? (·.name = x)).map fun d =>
          if d.parts = 1 then .pt (TraceBFV.inputBound P prog d)
          else .ct (TraceBFV.inputBound P prog d))
        (Trace.initCt P prog cts) := by
      intro x b hb
      obtain ⟨d, hd, hbe⟩ := Option.map_eq_some_iff.mp hb
      obtain ⟨hn, -⟩ := hfind x d hd
      have he := hin x d hd
      have he' : Sem P s b (inputVal P msgs d) (cts x) := by
        by_cases hp : d.parts = 1
        · simp only [hp, ↓reduceIte] at he hbe; subst hbe; exact he
        · simp only [hp, ↓reduceIte] at he hbe; subst hbe; exact he
      unfold inputVal at he'; rw [hn] at he'
      exact ⟨_, cts x, by simp [initEnv, hd], by simp [Trace.initCt, hd], he'⟩
    obtain ⟨b, hb, hβ⟩ := mapM_some (ctBound βf) _ bs hbs o ho
    obtain ⟨v, ct, hv, hct, he⟩ := hinv _ σ hinv0 hrunσ o (.ct b) (ctBound_some hβ)
    exact ⟨v, ct, hv, hct, encrypts_mono hk he (hB' ▸ le_foldl_max 0 hb)⟩

end Main

end Validation.BFV.PerInstrAux

namespace Validation.BFV
open Spec NPoly Scheme Source Correct Challenge.BFV
open Validation.BFV.PerInstrAux

section
variable (P : FullParams)

theorem runAt_const (E : TraceBFV.Budget) (s : IntPoly P.src.N) (n : ℕ) (body : List Instr)
    (ρ : Env P.src) (σ σf : Trace.CtEnv P) :
    TraceBFV.RunAt P (fun _ => E) s n body ρ σ σf ↔ TraceBFV.Run P E s body ρ σ σf := by
  induction body generalizing n ρ σ with
  | nil => exact Iff.rfl
  | cons i is ih =>
    rw [runAt_cons]
    constructor
    · rintro ⟨ρ', σ', h1, h2, h3⟩
      exact ⟨ρ', σ', h1, h2, (ih (n + 1) ρ' σ').mp h3⟩
    · rintro ⟨ρ', σ', h1, h2, h3⟩
      exact ⟨ρ', σ', h1, h2, (ih (n + 1) ρ' σ').mpr h3⟩

theorem runAt_congr (E E' : ℕ → TraceBFV.Budget) (s : IntPoly P.src.N) (n : ℕ)
    (body : List Instr) (h : ∀ j, j < body.length → E (n + j) = E' (n + j))
    (ρ : Env P.src) (σ σf : Trace.CtEnv P) :
    TraceBFV.RunAt P E s n body ρ σ σf ↔ TraceBFV.RunAt P E' s n body ρ σ σf := by
  induction body generalizing n ρ σ with
  | nil => exact Iff.rfl
  | cons i is ih =>
    have h0 : E n = E' n := by simpa using h 0 (by simp)
    have h' : ∀ j, j < is.length → E (n + 1 + j) = E' (n + 1 + j) := fun j hj => by
      have := h (j + 1) (by simpa using hj)
      rwa [show n + (j + 1) = n + 1 + j by omega] at this
    rw [runAt_cons, runAt_cons, h0]
    constructor
    · rintro ⟨ρ', σ', h1, h2, h3⟩
      exact ⟨ρ', σ', h1, h2, (ih (n + 1) h' ρ' σ').mp h3⟩
    · rintro ⟨ρ', σ', h1, h2, h3⟩
      exact ⟨ρ', σ', h1, h2, (ih (n + 1) h' ρ' σ').mpr h3⟩

theorem refAnalyzeBFVAt_const (E : TraceBFV.Budget) (prog : Source.Program) :
    refAnalyzeBFVAt P (fun _ => E) prog = refAnalyzeBFV P E prog := by
  rw [refAnalyzeAt_eq, refAnalyze_eq]
  simp only [refRunAt_const]

theorem refAnalyzeBFVAt_congr (E E' : ℕ → TraceBFV.Budget) (prog : Source.Program)
    (h : ∀ j, j < prog.body.length → E j = E' j) :
    refAnalyzeBFVAt P E prog = refAnalyzeBFVAt P E' prog := by
  have hc := refRunAt_congr P E E' prog.body 0 (fun j hj => by simpa using h j hj)
  rw [refAnalyzeAt_eq, refAnalyzeAt_eq]
  simp only [hc]

end

theorem refAnalyzeBFVAt_sound : NoiseSoundBFVAt refAnalyzeBFVAt := refAnalyzeAt_sound

theorem refAnalyzeBFVAt_rejects_nonBFV (P : FullParams) (E : ℕ → TraceBFV.Budget)
    (prog : Source.Program) (hk : P.src.kind ≠ .bfv) : refAnalyzeBFVAt P E prog = none := by
  rcases h : refAnalyzeBFVAt P E prog with _ | B
  · rfl
  · exact absurd (refAnalyzeAt_some h).1 hk

example := (@runAt_const : type_of% @Challenge.BFV.runAt_const)
example := (@runAt_congr : type_of% @Challenge.BFV.runAt_congr)
example := (@refAnalyzeBFVAt_const : type_of% @Challenge.BFV.refAnalyzeBFVAt_const)
example := (@refAnalyzeBFVAt_congr : type_of% @Challenge.BFV.refAnalyzeBFVAt_congr)
example := (@refAnalyzeBFVAt_sound : type_of% @Challenge.BFV.refAnalyzeBFVAt_sound)
example := (@refAnalyzeBFVAt_rejects_nonBFV :
  type_of% @Challenge.BFV.refAnalyzeBFVAt_rejects_nonBFV)

end Validation.BFV

namespace Validation.BFVMul
open Spec NPoly Scheme Source Correct Challenge.BFV Challenge.BFVMul

variable (P : FullParams)

theorem certifiedAt_decrypts (E : ℕ → TraceBFV.Budget) (prog : Program) (B : ℕ)
    (hP : SchemeParamsOK P) (hk : P.src.kind = .bfv)
    (h : refAnalyzeBFVAt P E prog = some B)
    (hc : Encrypt.outputsUnderS? P.src prog = true)
    (s : IntPoly P.src.N) (msgs : Var → Msg P.src.t P.src.N)
    (cts : Var → List (IntPoly P.src.N)) (hin : TraceBFV.InputsOK P s prog msgs cts) :
    OutputsDecryptAt P E prog s msgs cts := by
  obtain ⟨ρ, hev, hrun⟩ := Validation.BFV.refAnalyzeBFVAt_sound P E prog B hP hk h s msgs cts hin
  refine ⟨ρ, hev, fun σ hσ o ho => ?_⟩
  obtain ⟨v, ct, hv, hct, henc⟩ := hrun σ hσ o ho
  have hkey : v.key = 1 := by
    have h1 := List.all_eq_true.mp hc o ho
    rw [Cert.outputKey?_eq_bfv P.src hk prog msgs ρ hev o v hv] at h1
    simpa using h1
  obtain ⟨m, hm, hdm⟩ := Validation.BFV.encrypts_bfv_decrypts P hk s B v ct henc
  rw [hkey, FHE.KeySwitch.automorph_one] at hdm
  exact ⟨v, ct, m, hv, hct, hm, hkey, hdm⟩

example := (@certifiedAt_decrypts : type_of% @Challenge.BFVMul.certifiedAt_decrypts)

end Validation.BFVMul
