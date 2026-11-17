import Challenge.Sanity.EndToEnd
import Validation.Profile.Achieve
import Validation.Profile.Inputs
import Validation.Certify
import Validation.CertifyBFV

/-!
# Validation.Sanity.EndToEnd — proofs of the pins of `Challenge.Sanity.EndToEnd`

Compositions of existing pins. Two new facts: the zero-message replay that the BFV reference
analysis runs checks `domainOK` at every instruction, and a run on any messages has the same
numbers of components (`Validation.IndCpaD.foldlM_zenv`), so acceptance gives the two-component
hypotheses of `achieve_bfv`; and every key a replay reaches is below `2N`, so keys for every
Galois element below `2N` cover every key switch. No locked definition is unfolded by name.
-/

namespace Validation.Sanity
open Spec NPoly Scheme Source Correct Challenge.Profile Challenge.CertifyBFV Challenge.BFV
  Challenge.RealizeBFV Challenge.Realize Challenge.IndCpaDProfile Challenge.ProfileAchieve
  Spec.CertifyBFV Validation.Ring Validation.Scheme

/-! ## Keys -/

theorem keyValid_any {N : ℕ} (kind : Kind) (t B : ℕ) (s : IntPoly N) (req : KeyReq N)
    (a : Poly req.modulus N) : ∃ b : Poly req.modulus N, KeyValid kind t B s req b a := by
  refine ⟨req.factor * ofInt req.modulus (req.target.eval s) - a * ofInt req.modulus s, ?_⟩
  have he : centered (req.factor * ofInt req.modulus (req.target.eval s) -
      a * ofInt req.modulus s + a * ofInt req.modulus s -
      req.factor * ofInt req.modulus (req.target.eval s)) = 0 := by
    have : req.factor * ofInt req.modulus (req.target.eval s) - a * ofInt req.modulus s +
        a * ofInt req.modulus s - req.factor * ofInt req.modulus (req.target.eval s) = 0 := by
      apply eq_of_neZero; intro; ring
    rw [this, centered_zero]
  refine ⟨?_, fun _ i => ?_⟩
  · show normInf (centered _) ≤ B
    rw [he, normInf_zero]; exact Nat.zero_le _
  · show (t : ℤ) ∣ (centered _).coeff i
    rw [he]; exact dvd_zero _

theorem gadgetKeys_exist_any (P : FullParams) (lay : Budget.KSLayout) (ℓ : ℕ) (tgt : KeyTarget)
    (s : IntPoly P.src.N) (as : List (IntPoly P.src.N)) (has : as.length = (lay.sizes ℓ).length) :
    ∃ keys : List (IntPoly P.src.N × IntPoly P.src.N),
      keys.map Prod.snd = as ∧ Budget.GadgetKeysOK P lay ℓ tgt s keys := by
  have hex : ∀ j : ℕ, ∃ b : Poly (Budget.gadgetReq P lay ℓ tgt j).modulus P.src.N,
      KeyValid P.src.kind P.src.t P.keyNoise s (Budget.gadgetReq P lay ℓ tgt j) b
        (ofInt _ (as.getD j 0)) := fun j =>
    keyValid_any P.src.kind P.src.t P.keyNoise s _ _
  choose b hb using hex
  refine ⟨(List.range as.length).map fun j => (centered (b j), as.getD j 0), ?_, ?_, ?_⟩
  · apply List.ext_getElem (by simp)
    intro j h1 h2
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2]
  · simp [has]
  · intro j hj
    rw [List.getElem_map, List.getElem_range]
    show KeyValid _ _ _ _ _ (ofInt _ (centered (b j))) _
    rw [ofInt_centered]
    exact hb j

/-! ## Keys stay below `2N` -/

/-- Every defined variable is under a Galois element below `2N`. -/
def KeysLt (Pr : Params) (ρ : Env Pr) : Prop := ∀ x v, ρ x = some v → v.key < 2 * Pr.N

theorem keysLt_set {Pr : Params} {ρ : Env Pr} (h : KeysLt Pr ρ) (d : Var) (v : Val Pr)
    (hv : v.key < 2 * Pr.N) : KeysLt Pr (ρ.set d v) := by
  intro y w hw
  simp only [Env.set] at hw
  split_ifs at hw
  · cases hw; exact hv
  · exact h y w hw

theorem keysLt_step {Pr : Params} (hN : 0 < Pr.N) {ρ ρ' : Env Pr} {i : Instr} (h : KeysLt Pr ρ)
    (hstep : step Pr ρ i = some ρ') : KeysLt Pr ρ' := by
  cases i with
  | add d a b | sub d a b | mul d a b | addPlain d a b | subPlain d a b | mulPlain d a b =>
    rcases hx : ρ a with _ | x
    · simp [step, hx] at hstep
    rcases hy : ρ b with _ | y
    · simp [step, hx, hy] at hstep
    simp only [step, hx, hy, Option.bind_eq_bind, Option.bind_some, Option.pure_def] at hstep
    obtain ⟨-, h2⟩ := Validation.Trace.guard_bind_eq_some hstep
    obtain ⟨m, -, h3⟩ := Option.bind_eq_some_iff.mp h2
    cases h3
    exact keysLt_set h _ _ (h a x hx)
  | square d a =>
    rcases hx : ρ a with _ | x
    · simp [step, hx] at hstep
    simp only [step, hx, Option.bind_eq_bind, Option.bind_some, Option.pure_def] at hstep
    obtain ⟨-, h2⟩ := Validation.Trace.guard_bind_eq_some hstep
    obtain ⟨m, -, h3⟩ := Option.bind_eq_some_iff.mp h2
    cases h3
    exact keysLt_set h _ _ (h a x hx)
  | mulConst d a _ | copy d a | toEval d a | toCoeff d a =>
    rcases hx : ρ a with _ | x
    · simp [step, hx] at hstep
    simp only [step, hx, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
      Option.some.injEq] at hstep
    subst hstep
    exact keysLt_set h _ _ (h a x hx)
  | relin d a =>
    rcases hx : ρ a with _ | x
    · simp [step, hx] at hstep
    simp only [step, hx, Option.bind_eq_bind, Option.bind_some, Option.pure_def] at hstep
    obtain ⟨-, h2⟩ := Validation.Trace.guard_bind_eq_some hstep
    cases h2
    exact keysLt_set h _ _ (h a x hx)
  | keySwitch d a =>
    rcases hx : ρ a with _ | x
    · simp [step, hx] at hstep
    simp only [step, hx, Option.bind_eq_bind, Option.bind_some, Option.pure_def] at hstep
    obtain ⟨-, h2⟩ := Validation.Trace.guard_bind_eq_some hstep
    cases h2
    exact keysLt_set h _ _ (by show 1 < 2 * Pr.N; omega)
  | automorph d a g =>
    rcases hx : ρ a with _ | x
    · simp [step, hx] at hstep
    simp only [step, hx, Option.bind_eq_bind, Option.bind_some, Option.pure_def] at hstep
    obtain ⟨-, h2⟩ := Validation.Trace.guard_bind_eq_some hstep
    cases h2
    exact keysLt_set h _ _ (by show (x.key * g) % (2 * Pr.N) < 2 * Pr.N; exact Nat.mod_lt _ (by omega))
  | dropLimbs d a k =>
    rcases hx : ρ a with _ | x
    · simp [step, hx] at hstep
    simp only [step, hx, Option.bind_eq_bind, Option.bind_some, Option.pure_def] at hstep
    obtain ⟨-, h2⟩ := Validation.Trace.guard_bind_eq_some hstep
    cases h2
    exact keysLt_set h _ _ (h a x hx)
  | modSwitch d a =>
    rcases hx : ρ a with _ | x
    · simp [step, hx] at hstep
    simp only [step, hx, Option.bind_eq_bind, Option.bind_some, Option.pure_def] at hstep
    obtain ⟨-, h2⟩ := Validation.Trace.guard_bind_eq_some hstep
    obtain ⟨q, -, h3⟩ := Option.bind_eq_some_iff.mp h2
    cases h3
    exact keysLt_set h _ _ (h a x hx)

theorem keysLt_foldlM {Pr : Params} (hN : 0 < Pr.N) :
    ∀ (body : List Instr) (ρ ρ' : Env Pr), KeysLt Pr ρ →
      body.foldlM (step Pr) ρ = some ρ' → KeysLt Pr ρ'
  | [], ρ, ρ', h, hf => by cases (Option.some.inj hf : ρ = ρ'); exact h
  | i :: is, ρ, ρ', h, hf => by
    rw [List.foldlM_cons] at hf
    obtain ⟨ρ1, h1, hf⟩ := Option.bind_eq_some_iff.mp hf
    exact keysLt_foldlM hN is ρ1 ρ' (keysLt_step hN h h1) hf

theorem keysLt_init {Pr : Params} (prog : Program) (msgs : Var → Msg Pr.t Pr.N)
    (hd : (prog.inputs.all fun d => d.ok Pr) = true) : KeysLt Pr (initEnv Pr prog msgs) := by
  intro x v hv
  simp only [initEnv, Option.map_eq_some_iff] at hv
  obtain ⟨d, hd', rfl⟩ := hv
  have hok := List.all_eq_true.mp hd d (List.mem_of_find?_eq_some hd')
  simp only [Decl.ok, decide_eq_true_eq] at hok
  exact hok.2.2.2.2

theorem N_pos {P : FullParams} (hP : SchemeParamsOK P) : 0 < P.src.N := by
  obtain ⟨k, hk⟩ := hP.N_pow2
  rw [hk]; exact Nat.two_pow_pos k

/-- Every key switch of a replay on any messages is under a Galois element below `2N`. -/
theorem rot_range {Pr : Params} (hN : 0 < Pr.N) (prog : Program) (msgs : Var → Msg Pr.t Pr.N)
    (hd : (prog.inputs.all fun d => d.ok Pr) = true) :
    ∀ (pre post : List Instr) (d a : Var) (ρ : Env Pr) (x : Val Pr),
      prog.body = pre ++ .keySwitch d a :: post →
      pre.foldlM (step Pr) (initEnv Pr prog msgs) = some ρ → ρ a = some x →
      x.key ∈ List.range (2 * Pr.N) := by
  intro pre post d a ρ x _ hρ hx
  exact List.mem_range.mpr (keysLt_foldlM hN pre _ ρ (keysLt_init prog msgs hd) hρ a x hx)

/-! ## BFV: acceptance gives the two-component conditions -/

open Validation.BFV.SoundAux (zenv zv) in
theorem domain_at {P : FullParams} {E : ℕ → TraceBFV.Budget} (i : Instr) (post : List Instr) :
    ∀ (pre : List Instr) (n : ℕ) (ρ0 ρ : Env P.src) (β : Var → Option TraceBFV.Bnd)
      (r : Env P.src × (Var → Option TraceBFV.Bnd)),
      refRunBFVAt P E n (pre ++ i :: post) ρ0 β = some r →
      pre.foldlM (step P.src) ρ0 = some ρ → domainOK ρ i = true
  | [], n, ρ0, ρ, β, r, h, hf => by
    cases (Option.some.inj hf : ρ0 = ρ)
    obtain ⟨-, -, -, -, -, -, -, -, hd⟩ := Validation.BFV.PerInstrAux.refRunAt_cons_some P h
    exact hd
  | j :: pre, n, ρ0, ρ, β, r, h, hf => by
    rw [List.foldlM_cons] at hf
    obtain ⟨ρ1, h1, hf⟩ := Option.bind_eq_some_iff.mp hf
    obtain ⟨ρ', v, b, h2, -, -, -, h3, -⟩ := Validation.BFV.PerInstrAux.refRunAt_cons_some P h
    rw [h1] at h2; cases h2
    exact domain_at i post pre (n + 1) ρ1 ρ _ r h3 hf

open Validation.BFV.SoundAux (zenv zv) in
/-- On any messages, the operands of every `mul`, `square` and `modSwitch` of an accepted program
have two components. -/
theorem domain_run {P : FullParams} {E : ℕ → TraceBFV.Budget} {prog : Program} {B : ℕ}
    {outs : List (Var × ℕ)} (h : certifyBFVProfile? P E prog = some (B, outs))
    (msgs : Var → Msg P.src.t P.src.N) (pre post : List Instr) (i : Instr) (ρ : Env P.src)
    (hbody : prog.body = pre ++ i :: post)
    (hρ : pre.foldlM (step P.src) (initEnv P.src prog msgs) = some ρ) :
    domainOK (zenv ρ) i = true := by
  obtain ⟨-, hk, -, -, hB, -⟩ := Validation.Profile.certifyBFVProfile?_some h
  obtain ⟨-, -, ρz, β, hrun, -⟩ := Validation.BFV.PerInstrAux.refAnalyzeAt_some hB
  have hz0 : zenv (initEnv P.src prog msgs) = initEnv P.src prog fun _ => .exact 0 := by
    funext y; simp only [zenv, initEnv, Option.map_map]; rfl
  have hz := Validation.IndCpaD.foldlM_zenv hk pre (initEnv P.src prog msgs)
  rw [hρ, hz0] at hz
  rw [hbody] at hrun
  exact domain_at i post pre 0 _ _ _ _ hrun hz

open Validation.BFV.SoundAux (zenv zv) in
theorem zenv_some {Pr : Params} {ρ : Env Pr} {a : Var} {x : Val Pr} (hx : ρ a = some x) :
    zenv ρ a = some (zv x) := by
  show (ρ a).map zv = _; rw [hx]; rfl

theorem dom_mul {Pr : Params} (ρ : Env Pr) (d a b : Var) (x y : Val Pr) (hx : ρ a = some x)
    (hy : ρ b = some y) : domainOK ρ (.mul d a b) = (x.parts == 2 && y.parts == 2) := by
  show (match ρ a, ρ b with
    | some x, some y => x.parts == 2 && y.parts == 2
    | _, _ => false) = _
  rw [hx, hy]

theorem dom_square {Pr : Params} (ρ : Env Pr) (d a : Var) (x : Val Pr) (hx : ρ a = some x) :
    domainOK ρ (.square d a) = (x.parts == 2) := by
  show (match ρ a with
    | some x => x.parts == 2
    | none => false) = _
  rw [hx]

theorem dom_modSwitch {Pr : Params} (ρ : Env Pr) (d a : Var) (x : Val Pr) (hx : ρ a = some x) :
    domainOK ρ (.modSwitch d a) = (x.parts == 2) := by
  show (match ρ a with
    | some x => x.parts == 2
    | none => false) = _
  rw [hx]

theorem achieve_bfv_accepted (P : FullParams) (E : ℕ → TraceBFV.Budget) (prog : Program) (B : ℕ)
    (outs : List (Var × ℕ)) (h : certifyBFVProfile? P E prog = some (B, outs))
    (lay : Budget.KSLayout) (U r : ℕ) (hc : coversBFVAt? P lay U r prog E = true) (hr : 1 ≤ r)
    (hdecl : ksDeclOK? P lay = true) (rots : List ℕ)
    (hrot : ∀ (pre post : List Instr) (d a : Var) (ρ : Env P.src) (x : Val P.src),
      prog.body = pre ++ .keySwitch d a :: post →
      pre.foldlM (step P.src) (initEnv P.src prog fun _ => .exact 0) = some ρ →
      ρ a = some x → x.key ∈ rots)
    (s : IntPoly P.src.N) (hs : SecretOK P.secretBound s)
    (rk : ℕ → List (IntPoly P.src.N × IntPoly P.src.N))
    (gk : ℕ → ℕ → List (IntPoly P.src.N × IntPoly P.src.N))
    (hkeys : ∀ ℓ, 1 ≤ ℓ → ℓ ≤ P.src.qs.length →
      Budget.GadgetKeysOK P lay ℓ .square s (rk ℓ) ∧
      ∀ g ∈ rots, Budget.GadgetKeysOK P lay ℓ (.galois g) s (gk g ℓ))
    (msgs : Var → Msg P.src.t P.src.N) (cts : Var → List (IntPoly P.src.N))
    (hin : TraceBFV.InputsOK P s prog msgs cts) :
    ∃ σf, bfvRun P lay rk gk prog.body (initEnv P.src prog fun _ => .exact 0)
        (Trace.initCt P prog cts) = some σf ∧
      TraceBFV.RunAt P E s 0 prog.body (initEnv P.src prog msgs) (Trace.initCt P prog cts) σf ∧
      OutputsCertifiedBFV P E prog outs s msgs cts := by
  obtain ⟨-, hk, -, -, -, -⟩ := Validation.Profile.certifyBFVProfile?_some h
  have hdom := fun pre post i ρ hbody hρ => domain_run h msgs pre post i ρ hbody hρ
  have hz0 : Validation.BFV.SoundAux.zenv (initEnv P.src prog msgs) =
      initEnv P.src prog fun _ => .exact 0 := by
    funext y; simp only [Validation.BFV.SoundAux.zenv, initEnv, Option.map_map]; rfl
  obtain ⟨σf, hf, hrun, -⟩ := Validation.ProfileAchieve.achieve_bfv P E prog B outs h lay U r hc
    hr hdecl rots s hs rk gk hkeys msgs cts hin
    (fun pre post d a ρ x hbody hρ hx => by
      have hz := Validation.IndCpaD.foldlM_zenv hk pre (initEnv P.src prog msgs)
      rw [hρ, hz0] at hz
      exact hrot pre post d a _ (Validation.BFV.SoundAux.zv x) hbody hz (zenv_some hx))
    (fun pre post d a b ρ x y hbody hρ hx hy => by
      have := hdom pre post _ ρ hbody hρ
      rw [dom_mul _ d a b _ _ (zenv_some hx) (zenv_some hy)] at this
      simp only [Bool.and_eq_true, beq_iff_eq] at this
      exact this)
    (fun pre post d a ρ x hbody hρ hx => by
      have := hdom pre post _ ρ hbody hρ
      rw [dom_square _ d a _ (zenv_some hx)] at this
      simp only [beq_iff_eq] at this
      exact this)
    (fun pre post d a ρ x hbody hρ hx => by
      have := hdom pre post _ ρ hbody hρ
      rw [dom_modSwitch _ d a _ (zenv_some hx)] at this
      simp only [beq_iff_eq] at this
      exact this)
  exact ⟨σf, hf, hrun, Validation.Profile.certifyBFVProfile?_sound P E prog B outs h s msgs cts hin⟩

theorem certifyBFVProfile?_end_to_end (P : FullParams) (E : ℕ → TraceBFV.Budget) (prog : Program)
    (B : ℕ) (outs : List (Var × ℕ)) (h : certifyBFVProfile? P E prog = some (B, outs))
    (lay : Budget.KSLayout) (U r : ℕ) (hc : coversBFVAt? P lay U r prog E = true) (hr : 1 ≤ r)
    (hdecl : ksDeclOK? P lay = true)
    (s : IntPoly P.src.N) (hs : SecretOK P.secretBound s) (m : Var → Poly P.src.t P.src.N) :
    ∃ (rk : ℕ → List (IntPoly P.src.N × IntPoly P.src.N))
      (gk : ℕ → ℕ → List (IntPoly P.src.N × IntPoly P.src.N))
      (cts : Var → List (IntPoly P.src.N)) (σf : Trace.CtEnv P),
      (∀ ℓ, 1 ≤ ℓ → ℓ ≤ P.src.qs.length →
        Budget.GadgetKeysOK P lay ℓ .square s (rk ℓ) ∧
        ∀ g, Budget.GadgetKeysOK P lay ℓ (.galois g) s (gk g ℓ)) ∧
      TraceBFV.InputsOK P s prog (fun x => .exact (m x)) cts ∧
      bfvRun P lay rk gk prog.body (initEnv P.src prog fun _ => .exact 0)
        (Trace.initCt P prog cts) = some σf ∧
      TraceBFV.RunAt P E s 0 prog.body (initEnv P.src prog fun x => .exact (m x))
        (Trace.initCt P prog cts) σf ∧
      OutputsCertifiedBFV P E prog outs s (fun x => .exact (m x)) cts := by
  have hrk : ∀ ℓ, ∃ k, Budget.GadgetKeysOK P lay ℓ .square s k := fun ℓ =>
    Validation.Budget.RunAux.gadgetKeys_exist P lay ℓ .square s
  have hgk : ∀ g ℓ, ∃ k, Budget.GadgetKeysOK P lay ℓ (.galois g) s k := fun g ℓ =>
    Validation.Budget.RunAux.gadgetKeys_exist P lay ℓ (.galois g) s
  choose rk hrk using hrk
  choose gk hgk using hgk
  obtain ⟨cts, hin⟩ :=
    Validation.ProfileInputs.certifyBFVProfile?_inputs_exist_all P E prog B outs h s m
  have hkeys : ∀ ℓ, 1 ≤ ℓ → ℓ ≤ P.src.qs.length →
      Budget.GadgetKeysOK P lay ℓ .square s (rk ℓ) ∧
      ∀ g, Budget.GadgetKeysOK P lay ℓ (.galois g) s (gk g ℓ) :=
    fun ℓ _ _ => ⟨hrk ℓ, fun g => hgk g ℓ⟩
  obtain ⟨hP, -, -, -, hB, -⟩ := Validation.Profile.certifyBFVProfile?_some h
  obtain ⟨-, hd, -⟩ := Validation.BFV.PerInstrAux.refAnalyzeAt_some hB
  obtain ⟨σf, hf, hrun, hcert⟩ := achieve_bfv_accepted P E prog B outs h lay U r hc hr hdecl
    (List.range (2 * P.src.N)) (rot_range (N_pos hP) prog _ hd) s hs
    rk gk (fun ℓ h1 h2 => ⟨(hkeys ℓ h1 h2).1, fun g _ => (hkeys ℓ h1 h2).2 g⟩) _ cts hin
  exact ⟨rk, gk, cts, σf, hkeys, hin, hf, hrun, hcert⟩

/-! ## BGV, profile mode -/

open Validation.BFV.SoundAux (zenv zv) in
theorem achieve_bgv_accepted (P : FullParams) (E : Trace.Budget) (prog : Program) (sw : Bool)
    (B : ℕ) (outs : List (Var × ℕ)) (h : certifyProfile? P E prog sw = some (B, outs))
    (lay : Budget.KSLayout) (K : ℕ) (hc : coversBGV? P lay K E = true)
    (hcan : lay.canonical = true) (hlo : Spec.Certify.layoutOK? P lay = true)
    (hkr : Spec.Certify.keysRestrict? P = true)
    (hms : ∀ (pre post : List Instr) (d a : Var) (ρ : Env P.src) (x : Val P.src),
      prog.body = pre ++ .modSwitch d a :: post →
      pre.foldlM (step P.src) (initEnv P.src prog fun _ => .exact 0) = some ρ →
      ρ a = some x → x.parts ≤ K)
    (rots : List ℕ)
    (hrot : ∀ (pre post : List Instr) (d a : Var) (ρ : Env P.src) (x : Val P.src),
      prog.body = pre ++ .keySwitch d a :: post →
      pre.foldlM (step P.src) (initEnv P.src prog fun _ => .exact 0) = some ρ →
      ρ a = some x → x.key ∈ rots)
    (s : IntPoly P.src.N) (hs : SecretOK P.secretBound s)
    (rk : List (IntPoly P.src.N × IntPoly P.src.N))
    (hrk : Budget.GadgetKeysOK P lay P.src.qs.length .square s rk)
    (gk : ℕ → List (IntPoly P.src.N × IntPoly P.src.N))
    (hgk : ∀ g ∈ rots, Budget.GadgetKeysOK P lay P.src.qs.length (.galois g) s (gk g))
    (msgs : Var → Msg P.src.t P.src.N) (cts : Var → List (IntPoly P.src.N))
    (hin : InputsOK P s prog msgs cts) (hb : Trace.BoundsOK P s prog msgs cts) :
    ∃ σf, ksRun P lay rk gk prog.body (initEnv P.src prog fun _ => .exact 0)
        (Trace.initCt P prog cts) = some σf ∧
      Trace.Run P E s prog.body (initEnv P.src prog msgs) (Trace.initCt P prog cts) σf ∧
      Challenge.Certify.OutputsCertified P E prog sw outs s msgs cts := by
  obtain ⟨hP, hk, hB, -⟩ := Validation.Profile.certifyProfile?_some h
  have hd : (prog.inputs.all fun d => d.ok P.src) = true := by
    have := (Validation.Headline.NoiseAux.refAnalyze_some hB)
    exact this.2.1
  have hz0 : zenv (initEnv P.src prog msgs) = initEnv P.src prog fun _ => .exact 0 := by
    funext y; simp only [zenv, initEnv, Option.map_map]; rfl
  obtain ⟨σf, hf, hrun, -⟩ := Validation.ProfileAchieve.achieve_bgv P E prog sw B outs h lay K hc
    hcan hlo hkr rots s hs rk hrk gk hgk msgs cts hin hb
    (fun pre post d a ρ x hbody hρ hx => by
      have hz := Validation.IndCpaDProfile.foldlM_zenv_bgv hk pre (initEnv P.src prog msgs)
      rw [hρ, hz0] at hz
      exact hrot pre post d a (zenv ρ) (zv x) hbody hz (zenv_some hx))
    (fun pre post d a ρ x hbody hρ hx => by
      have hz := Validation.IndCpaDProfile.foldlM_zenv_bgv hk pre (initEnv P.src prog msgs)
      rw [hρ, hz0] at hz
      exact hms pre post d a (zenv ρ) (zv x) hbody hz (zenv_some hx))
  exact ⟨σf, hf, hrun, Validation.Profile.certifyProfile?_sound P E prog sw B outs h s msgs cts
    hin hb⟩

theorem certifyProfile?_end_to_end (P : FullParams) (E : Trace.Budget) (prog : Program) (sw : Bool)
    (B : ℕ) (outs : List (Var × ℕ)) (h : certifyProfile? P E prog sw = some (B, outs))
    (lay : Budget.KSLayout) (K : ℕ) (hc : coversBGV? P lay K E = true)
    (hcan : lay.canonical = true) (hlo : Spec.Certify.layoutOK? P lay = true)
    (hkr : Spec.Certify.keysRestrict? P = true)
    (hms : ∀ (pre post : List Instr) (d a : Var) (ρ : Env P.src) (x : Val P.src),
      prog.body = pre ++ .modSwitch d a :: post →
      pre.foldlM (step P.src) (initEnv P.src prog fun _ => .exact 0) = some ρ →
      ρ a = some x → x.parts ≤ K)
    (s : IntPoly P.src.N) (hs : SecretOK P.secretBound s) (m : Var → Poly P.src.t P.src.N) :
    ∃ (rk : List (IntPoly P.src.N × IntPoly P.src.N))
      (gk : ℕ → List (IntPoly P.src.N × IntPoly P.src.N))
      (cts : Var → List (IntPoly P.src.N)) (σf : Trace.CtEnv P),
      Budget.GadgetKeysOK P lay P.src.qs.length .square s rk ∧
      (∀ g, Budget.GadgetKeysOK P lay P.src.qs.length (.galois g) s (gk g)) ∧
      InputsOK P s prog (fun x => .exact (m x)) cts ∧
      Trace.BoundsOK P s prog (fun x => .exact (m x)) cts ∧
      ksRun P lay rk gk prog.body (initEnv P.src prog fun _ => .exact 0)
        (Trace.initCt P prog cts) = some σf ∧
      Trace.Run P E s prog.body (initEnv P.src prog fun x => .exact (m x))
        (Trace.initCt P prog cts) σf ∧
      Challenge.Certify.OutputsCertified P E prog sw outs s (fun x => .exact (m x)) cts := by
  obtain ⟨rk, hrk⟩ := Validation.Budget.RunAux.gadgetKeys_exist P lay P.src.qs.length .square s
  have hgk : ∀ g, ∃ k, Budget.GadgetKeysOK P lay P.src.qs.length (.galois g) s k := fun g =>
    Validation.Budget.RunAux.gadgetKeys_exist P lay _ (.galois g) s
  choose gk hgk using hgk
  obtain ⟨cts, hin, hb⟩ :=
    Validation.ProfileInputs.certifyProfile?_inputs_exist_all P E prog sw B outs h s m
  obtain ⟨hP, -, hB, -⟩ := Validation.Profile.certifyProfile?_some h
  have hd := (Validation.Headline.NoiseAux.refAnalyze_some hB).2.1
  obtain ⟨σf, hf, hrun, hcert⟩ := achieve_bgv_accepted P E prog sw B outs h lay K hc hcan hlo hkr
    hms (List.range (2 * P.src.N)) (rot_range (N_pos hP) prog _ hd) s hs rk hrk gk
    (fun g _ => hgk g) _ cts hin hb
  exact ⟨rk, gk, cts, σf, hrk, hgk, hin, hb, hf, hrun, hcert⟩

/-! ## Default mode -/

theorem certifyBFV?_end_to_end (x : InputBFV) (c : CertificateBFV) (h : certifyBFV? x = some c)
    (s : IntPoly x.P.src.N) (hs : SecretOK x.P.secretBound s)
    (m : Var → Poly x.P.src.t x.P.src.N) :
    ∃ (cts : Var → List (IntPoly x.P.src.N)) (σ : Trace.CtEnv x.P),
      TraceBFV.InputsOK x.P s x.prog (fun y => .exact (m y)) cts ∧
      TraceBFV.RunAt x.P c.budget s 0 x.prog.body (initEnv x.P.src x.prog fun y => .exact (m y))
        (Trace.initCt x.P x.prog cts) σ ∧
      OutputsCertifiedBFV x.P c.budget x.prog c.outputs s (fun y => .exact (m y)) cts := by
  obtain ⟨cts, hin⟩ := Validation.ProfileInputs.certifyBFV?_inputs_exist x c h s m
  obtain ⟨σ, hσ⟩ := Validation.CertifyBFV.certifyBFV?_textbook_run_exists x c h s hs _ cts hin
  exact ⟨cts, σ, hin, hσ, Validation.CertifyBFV.certifyBFV?_sound x c h s _ cts hin⟩

theorem certify?_end_to_end (x : Certify.Input) (c : Certify.Certificate)
    (h : Challenge.Certify.certify? x = some c)
    (s : IntPoly c.params.src.N) (hs : SecretOK c.params.secretBound s)
    (m : Var → Poly c.params.src.t c.params.src.N) :
    ∃ (cts : Var → List (IntPoly c.params.src.N)) (σ : Trace.CtEnv c.params),
      InputsOK c.params s x.prog (fun y => .exact (m y)) cts ∧
      Trace.BoundsOK c.params s x.prog (fun y => .exact (m y)) cts ∧
      Trace.Run c.params c.budget s x.prog.body (initEnv c.params.src x.prog fun y => .exact (m y))
        (Trace.initCt c.params x.prog cts) σ ∧
      Challenge.Certify.OutputsCertified c.params c.budget x.prog x.switched c.outputs s
        (fun y => .exact (m y)) cts := by
  obtain ⟨cts, hin, hb⟩ := Validation.ProfileInputs.certify?_inputs_exist x c h s m
  obtain ⟨σ, hσ⟩ := Validation.Certify.certified_run_exists x c h s hs _ cts hin
  exact ⟨cts, σ, hin, hb, hσ, Validation.Certify.certify?_sound x c h s _ cts hin hb⟩

example := (@gadgetKeys_exist_any : type_of% @Challenge.Sanity.gadgetKeys_exist_any)
example := (@achieve_bfv_accepted : type_of% @Challenge.Sanity.achieve_bfv_accepted)
example := (@certifyBFVProfile?_end_to_end :
  type_of% @Challenge.Sanity.certifyBFVProfile?_end_to_end)
example := (@certifyBFV?_end_to_end : type_of% @Challenge.Sanity.certifyBFV?_end_to_end)
example := (@certify?_end_to_end : type_of% @Challenge.Sanity.certify?_end_to_end)
example := (@achieve_bgv_accepted : type_of% @Challenge.Sanity.achieve_bgv_accepted)
example := (@certifyProfile?_end_to_end : type_of% @Challenge.Sanity.certifyProfile?_end_to_end)

end Validation.Sanity
