import Challenge.Budget
import Validation.Headline.Noise
import Validation.Budget.Basic
import Validation.Budget.KeySwitch
import Validation.Scheme.Sound

/-!
# Validation.Budget.RunExists — every well-formed program has a run at the certified budget

Proofs of `Challenge.Budget.wellFormed_run_exists` and `Challenge.Budget.certified_run_exists`.

Induction over the body with the invariant "every variable defined in the message environment
holds, in the ciphertext environment, a ciphertext with the recorded number of components, at a
level inside the chain". Each step is the textbook one, by the pin for its instruction
(`Validation.Trace.stepOK_*`, `relin_realizable`, `keySwitch_realizable`); the gadget keys of a
key switch are the noiseless ones (`Validation.Scheme.keyValid_exists`).
-/

namespace Validation.Budget
open Spec NPoly Scheme Source Correct Spec.Budget Challenge.Headline
open Validation.Scheme Validation.Source Validation.Trace Validation.Headline.NoiseAux

namespace RunAux

variable {P : FullParams}

/-- Every defined variable holds a ciphertext with the recorded number of components. -/
def Shape (P : FullParams) (ρ : Env P.src) (σ : Trace.CtEnv P) : Prop :=
  ∀ x v, ρ x = some v → ∃ ct, σ x = some ct ∧ ct.length = v.parts

/-- Every defined variable is at a level inside the modulus chain. -/
def Levels (P : FullParams) (ρ : Env P.src) : Prop :=
  ∀ x v, ρ x = some v → 1 ≤ v.level ∧ v.level ≤ P.src.qs.length

theorem levels_set {ρ : Env P.src} (h : Levels P ρ) (d : Var) (v : Val P.src)
    (h1 : 1 ≤ v.level) (h2 : v.level ≤ P.src.qs.length) : Levels P (ρ.set d v) := by
  intro y w hw
  simp only [Env.set] at hw
  split_ifs at hw
  · cases hw; exact ⟨h1, h2⟩
  · exact h y w hw

/-- `step` keeps levels inside the chain. -/
theorem levels_step {ρ ρ' : Env P.src} {i : Instr} (h : Levels P ρ)
    (hstep : step P.src ρ i = some ρ') : Levels P ρ' := by
  cases i with
  | add d a b | sub d a b | mul d a b | addPlain d a b | subPlain d a b | mulPlain d a b =>
    rcases hx : ρ a with _ | x
    · simp [step, hx] at hstep
    rcases hy : ρ b with _ | y
    · simp [step, hx, hy] at hstep
    simp only [step, hx, hy, Option.bind_eq_bind, Option.bind_some, Option.pure_def] at hstep
    obtain ⟨-, h2⟩ := guard_bind_eq_some hstep
    obtain ⟨m, -, h3⟩ := Option.bind_eq_some_iff.mp h2
    cases h3
    exact levels_set h _ _ (h a x hx).1 (h a x hx).2
  | square d a =>
    rcases hx : ρ a with _ | x
    · simp [step, hx] at hstep
    simp only [step, hx, Option.bind_eq_bind, Option.bind_some, Option.pure_def] at hstep
    obtain ⟨-, h2⟩ := guard_bind_eq_some hstep
    obtain ⟨m, -, h3⟩ := Option.bind_eq_some_iff.mp h2
    cases h3
    exact levels_set h _ _ (h a x hx).1 (h a x hx).2
  | mulConst d a _ | copy d a | toEval d a | toCoeff d a =>
    rcases hx : ρ a with _ | x
    · simp [step, hx] at hstep
    simp only [step, hx, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
      Option.some.injEq] at hstep
    subst hstep
    exact levels_set h _ _ (h a x hx).1 (h a x hx).2
  | relin d a | keySwitch d a | automorph d a _ =>
    rcases hx : ρ a with _ | x
    · simp [step, hx] at hstep
    simp only [step, hx, Option.bind_eq_bind, Option.bind_some, Option.pure_def] at hstep
    obtain ⟨-, h2⟩ := guard_bind_eq_some hstep
    cases h2
    exact levels_set h _ _ (h a x hx).1 (h a x hx).2
  | dropLimbs d a k =>
    rcases hx : ρ a with _ | x
    · simp [step, hx] at hstep
    simp only [step, hx, Option.bind_eq_bind, Option.bind_some, Option.pure_def] at hstep
    obtain ⟨hg, h2⟩ := guard_bind_eq_some hstep
    cases h2
    have := h a x hx
    exact levels_set h _ _ (by show 1 ≤ x.level - k; omega) (by show x.level - k ≤ _; omega)
  | modSwitch d a =>
    rcases hx : ρ a with _ | x
    · simp [step, hx] at hstep
    simp only [step, hx, Option.bind_eq_bind, Option.bind_some, Option.pure_def] at hstep
    obtain ⟨hg, h2⟩ := guard_bind_eq_some hstep
    obtain ⟨q, -, h3⟩ := Option.bind_eq_some_iff.mp h2
    cases h3
    have := h a x hx
    exact levels_set h _ _ (by show 1 ≤ x.level - 1; omega) (by show x.level - 1 ≤ _; omega)

/-- A step that meets its contract keeps the shapes. -/
theorem shape_step {E : Trace.Budget} {s : IntPoly P.src.N} {ρ ρ' : Env P.src}
    {σ σ' : Trace.CtEnv P} {i : Instr} (h : Shape P ρ σ) (hstep : step P.src ρ i = some ρ')
    (hok : Trace.StepOK P E s ρ ρ' σ σ' i) : Shape P ρ' σ' := by
  obtain ⟨w, hw⟩ := step_set hstep
  obtain ⟨v, ct, hv, hlen, hσ', -⟩ := hok
  intro y vy hy
  by_cases hyd : y = Trace.dst i
  · subst hyd
    rw [hv] at hy; cases hy
    exact ⟨ct, by rw [hσ']; simp [Trace.CtEnv.set], hlen⟩
  · rw [hw] at hy
    simp only [Env.set, hyd, ite_false] at hy
    obtain ⟨ct', h1, h2⟩ := h y vy hy
    exact ⟨ct', by rw [hσ']; simp [Trace.CtEnv.set, hyd, h1], h2⟩

/-- Valid gadget keys exist for every secret, layout, level and target (the noiseless ones). -/
theorem gadgetKeys_exist (P : FullParams) (lay : KSLayout) (ℓ : ℕ) (tgt : KeyTarget)
    (s : IntPoly P.src.N) :
    ∃ keys : List (IntPoly P.src.N × IntPoly P.src.N), GadgetKeysOK P lay ℓ tgt s keys := by
  have hex : ∀ j : ℕ, ∃ b a : Poly (P.src.modulus ℓ * specialProd P) P.src.N,
      KeyValid P.src.kind P.src.t P.keyNoise s (gadgetReq P lay ℓ tgt j) b a := fun j =>
    keyValid_exists P.src.kind P.src.t P.keyNoise s (gadgetReq P lay ℓ tgt j)
  choose b a hba using hex
  refine ⟨(List.range (lay.sizes ℓ).length).map fun j => (centered (b j), centered (a j)),
    by simp, ?_⟩
  intro j hj
  simp only [List.getElem_map, List.getElem_range]
  have e1 : ofInt (gadgetReq P lay ℓ tgt j).modulus (centered (b j)) = b j := ofInt_centered _
  have e2 : ofInt (gadgetReq P lay ℓ tgt j).modulus (centered (a j)) = a j := ofInt_centered _
  rw [e1, e2]
  exact hba j

section Step
variable (lay : KSLayout) (hk : P.src.kind = .bgv) (hP : SchemeParamsOK P) (hS : SpecialOK P)
  (hlay : ∀ ℓ, 1 ≤ ℓ → ℓ ≤ P.src.qs.length → lay.okAt ℓ = true)
  (s : IntPoly P.src.N) (hs : SecretOK P.secretBound s)
include hk hP hS hlay hs

/-- **One step.** Every instruction `step` accepts has a textbook realization meeting its
contract at the certified budget. -/
theorem step_exists {ρ ρ' : Env P.src} {σ : Trace.CtEnv P} (i : Instr)
    (hsh : Shape P ρ σ) (hlv : Levels P ρ) (hstep : step P.src ρ i = some ρ') :
    ∃ σ', Trace.StepOK P (certified P lay) s ρ ρ' σ σ' i := by
  cases i with
  | add d a b =>
    rcases hx : ρ a with _ | x
    · simp [step, hx] at hstep
    rcases hy : ρ b with _ | y
    · simp [step, hx, hy] at hstep
    obtain ⟨ca, ha, hla⟩ := hsh a x hx
    obtain ⟨cb, hb, hlb⟩ := hsh b y hy
    exact ⟨_, stepOK_add_padded P _ s ρ ρ' σ d a b x y ca cb hstep hx hy ha hb hla hlb⟩
  | sub d a b =>
    rcases hx : ρ a with _ | x
    · simp [step, hx] at hstep
    rcases hy : ρ b with _ | y
    · simp [step, hx, hy] at hstep
    obtain ⟨ca, ha, hla⟩ := hsh a x hx
    obtain ⟨cb, hb, hlb⟩ := hsh b y hy
    exact ⟨_, stepOK_sub_padded P _ s ρ ρ' σ d a b x y ca cb hstep hx hy ha hb hla hlb⟩
  | mul d a b =>
    rcases hx : ρ a with _ | x
    · simp [step, hx] at hstep
    rcases hy : ρ b with _ | y
    · simp [step, hx, hy] at hstep
    obtain ⟨ca, ha, hla⟩ := hsh a x hx
    obtain ⟨cb, hb, hlb⟩ := hsh b y hy
    exact ⟨_, stepOK_mul_tensor P _ s ρ ρ' σ d a b x y ca cb hstep hx hy ha hb hla hlb⟩
  | square d a =>
    rcases hx : ρ a with _ | x
    · simp [step, hx] at hstep
    obtain ⟨ca, ha, hla⟩ := hsh a x hx
    exact ⟨_, stepOK_square_textbook P _ s ρ ρ' σ d a x ca hstep hx ha hla⟩
  | mulConst d a c =>
    rcases hx : ρ a with _ | x
    · simp [step, hx] at hstep
    obtain ⟨ca, ha, hla⟩ := hsh a x hx
    exact ⟨_, stepOK_mulConst_textbook P _ s ρ ρ' σ d a c x ca hstep hx ha hla⟩
  | copy d a =>
    rcases hx : ρ a with _ | x
    · simp [step, hx] at hstep
    obtain ⟨ca, ha, hla⟩ := hsh a x hx
    exact ⟨_, stepOK_copy_textbook P _ s ρ ρ' σ d a _ (Or.inl rfl) x ca hstep hx ha hla⟩
  | toEval d a =>
    rcases hx : ρ a with _ | x
    · simp [step, hx] at hstep
    obtain ⟨ca, ha, hla⟩ := hsh a x hx
    exact ⟨_, stepOK_copy_textbook P _ s ρ ρ' σ d a _ (Or.inr (Or.inl rfl)) x ca hstep hx ha hla⟩
  | toCoeff d a =>
    rcases hx : ρ a with _ | x
    · simp [step, hx] at hstep
    obtain ⟨ca, ha, hla⟩ := hsh a x hx
    exact ⟨_, stepOK_copy_textbook P _ s ρ ρ' σ d a _ (Or.inr (Or.inr rfl)) x ca hstep hx ha hla⟩
  | automorph d a g =>
    rcases hx : ρ a with _ | x
    · simp [step, hx] at hstep
    obtain ⟨ca, ha, hla⟩ := hsh a x hx
    exact ⟨_, stepOK_automorph_textbook P _ s ρ ρ' σ d a g x ca hstep hx ha hla⟩
  | dropLimbs d a k =>
    rcases hx : ρ a with _ | x
    · simp [step, hx] at hstep
    obtain ⟨ca, ha, hla⟩ := hsh a x hx
    exact ⟨_, stepOK_dropLimbs_textbook P _ s ρ ρ' σ d a k x ca hstep hx ha hla⟩
  | addPlain d a p =>
    rcases hx : ρ a with _ | x
    · simp [step, hx] at hstep
    rcases hy : ρ p with _ | y
    · simp [step, hx, hy] at hstep
    obtain ⟨ca, ha, hla⟩ := hsh a x hx
    obtain ⟨cb, hb, hlb⟩ := hsh p y hy
    have hstep' := hstep
    simp only [step, hx, hy, Option.bind_eq_bind, Option.bind_some, Option.pure_def] at hstep'
    obtain ⟨⟨hy1, -⟩, -⟩ := guard_bind_eq_some hstep'
    obtain ⟨c, rfl⟩ := List.length_eq_one_iff.mp (hlb.trans hy1)
    exact ⟨_, stepOK_addPlain_textbook P _ s ρ ρ' σ d a p x y ca c hstep hx hy ha hb hla⟩
  | subPlain d a p =>
    rcases hx : ρ a with _ | x
    · simp [step, hx] at hstep
    rcases hy : ρ p with _ | y
    · simp [step, hx, hy] at hstep
    obtain ⟨ca, ha, hla⟩ := hsh a x hx
    obtain ⟨cb, hb, hlb⟩ := hsh p y hy
    have hstep' := hstep
    simp only [step, hx, hy, Option.bind_eq_bind, Option.bind_some, Option.pure_def] at hstep'
    obtain ⟨⟨hy1, -⟩, -⟩ := guard_bind_eq_some hstep'
    obtain ⟨c, rfl⟩ := List.length_eq_one_iff.mp (hlb.trans hy1)
    exact ⟨_, stepOK_subPlain_textbook P _ s ρ ρ' σ d a p x y ca c hstep hx hy ha hb hla⟩
  | mulPlain d a p =>
    rcases hx : ρ a with _ | x
    · simp [step, hx] at hstep
    rcases hy : ρ p with _ | y
    · simp [step, hx, hy] at hstep
    obtain ⟨ca, ha, hla⟩ := hsh a x hx
    obtain ⟨cb, hb, hlb⟩ := hsh p y hy
    have hstep' := hstep
    simp only [step, hx, hy, Option.bind_eq_bind, Option.bind_some, Option.pure_def] at hstep'
    obtain ⟨⟨hy1, -, -⟩, -⟩ := guard_bind_eq_some hstep'
    obtain ⟨c, rfl⟩ := List.length_eq_one_iff.mp (hlb.trans hy1)
    exact ⟨_, stepOK_mulPlain_textbook P _ s ρ ρ' σ d a p x y ca c hstep hx hy ha hb hla⟩
  | modSwitch d a =>
    rcases hx : ρ a with _ | x
    · simp [step, hx] at hstep
    obtain ⟨ca, ha, hla⟩ := hsh a x hx
    exact ⟨_, stepOK_modSwitch_textbook_parts P hk hP _ s hs ρ ρ' σ d a x ca
      (le_of_eq (certified_modSwitchAt P lay x.parts).symm) hstep hx ha hla⟩
  | relin d a =>
    rcases hx : ρ a with _ | x
    · simp [step, hx] at hstep
    obtain ⟨ca, ha, hla⟩ := hsh a x hx
    obtain ⟨h1, hL⟩ := hlv a x hx
    obtain ⟨f, hf⟩ := relin_realizable P lay hk hP hS x.level h1 hL (hlay _ h1 hL)
    obtain ⟨keys, hkeys⟩ := gadgetKeys_exist P lay x.level .square s
    exact ⟨_, hf (certified P lay) (ksBoundAt_le_ksBudget P lay x.level h1 hL) s hs keys hkeys
      ρ ρ' σ d a x ca hstep hx ha rfl hla⟩
  | keySwitch d a =>
    rcases hx : ρ a with _ | x
    · simp [step, hx] at hstep
    obtain ⟨ca, ha, hla⟩ := hsh a x hx
    obtain ⟨h1, hL⟩ := hlv a x hx
    obtain ⟨f, hf⟩ := keySwitch_realizable P lay hk hP hS x.level h1 hL (hlay _ h1 hL)
    obtain ⟨keys, hkeys⟩ := gadgetKeys_exist P lay x.level (.galois x.key) s
    exact ⟨_, hf (certified P lay) (ksBoundAt_le_ksBudget P lay x.level h1 hL) s hs
      ρ ρ' σ d a x ca hstep hx ha rfl hla keys hkeys⟩

/-- **The run.** From shapes and levels, every body `foldlM step` accepts has a run. -/
theorem run_exists : ∀ (body : List Instr) (ρ ρf : Env P.src) (σ : Trace.CtEnv P),
    Shape P ρ σ → Levels P ρ → body.foldlM (step P.src) ρ = some ρf →
    ∃ σf, Trace.Run P (certified P lay) s body ρ σ σf
  | [], _, _, σ, _, _, _ => ⟨σ, rfl⟩
  | i :: is, ρ, ρf, σ, hsh, hlv, h => by
    simp only [List.foldlM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨ρ', hstep, hrest⟩ := h
    obtain ⟨σ', hok⟩ := step_exists lay hk hP hS hlay s hs i hsh hlv hstep
    obtain ⟨σf, hrun⟩ := run_exists is ρ' ρf σ' (shape_step hsh hstep hok)
      (levels_step hlv hstep) hrest
    exact ⟨σf, ρ', σ', hstep, hok, hrun⟩

end Step

end RunAux

open RunAux

theorem wellFormed_run_exists (P : FullParams) (lay : KSLayout) (prog : Source.Program)
    (hP : SchemeParamsOK P) (hk : P.src.kind = .bgv) (hS : SpecialOK P)
    (hlay : ∀ ℓ, 1 ≤ ℓ → ℓ ≤ P.src.qs.length → lay.okAt ℓ = true)
    (s : IntPoly P.src.N) (hs : SecretOK P.secretBound s)
    (msgs : Var → Msg P.src.t P.src.N) (ρ : Env P.src)
    (h : Source.eval P.src prog msgs = some ρ)
    (cts : Var → List (IntPoly P.src.N))
    (hlen : ∀ x d, prog.inputs.find? (·.name = x) = some d → (cts x).length = d.parts) :
    ∃ σ, Trace.Run P (certified P lay) s prog.body (initEnv P.src prog msgs)
      (Trace.initCt P prog cts) σ := by
  simp only [eval, Option.bind_eq_bind, Option.pure_def] at h
  obtain ⟨hdecl, h⟩ := guard_bind_eq_some h
  obtain ⟨-, h⟩ := guard_bind_eq_some h
  obtain ⟨ρf, hbody, -⟩ := Option.bind_eq_some_iff.mp h
  refine run_exists lay hk hP hS hlay s hs prog.body _ ρf _ ?_ ?_ hbody
  · intro x v hv
    simp only [initEnv, Option.map_eq_some_iff] at hv
    obtain ⟨d, hd, rfl⟩ := hv
    exact ⟨cts x, by simp [Trace.initCt, hd], hlen x d hd⟩
  · intro x v hv
    simp only [initEnv, Option.map_eq_some_iff] at hv
    obtain ⟨d, hd, rfl⟩ := hv
    have hok := List.all_eq_true.mp hdecl d (List.mem_of_find?_eq_some hd)
    simp only [Decl.ok, decide_eq_true_eq] at hok
    exact ⟨hok.2.1, hok.2.2.1⟩

theorem certified_run_exists (P : FullParams) (lay : KSLayout) (prog : Source.Program) (B : ℕ)
    (hP : SchemeParamsOK P) (hk : P.src.kind = .bgv) (hS : SpecialOK P)
    (hlay : ∀ ℓ, 1 ≤ ℓ → ℓ ≤ P.src.qs.length → lay.okAt ℓ = true)
    (h : refAnalyze P (certified P lay) prog = some B)
    (s : IntPoly P.src.N) (hs : SecretOK P.secretBound s)
    (msgs : Var → Msg P.src.t P.src.N) (cts : Var → List (IntPoly P.src.N))
    (hin : InputsOK P s prog msgs cts) :
    ∃ σ, Trace.Run P (certified P lay) s prog.body (initEnv P.src prog msgs)
      (Trace.initCt P prog cts) σ := by
  obtain ⟨ρ, hρ⟩ := refAnalyze_eval hk h s msgs cts hin
  refine wellFormed_run_exists P lay prog hP hk hS hlay s hs msgs ρ hρ cts ?_
  intro x d hd
  have he := hin x d hd
  rw [encrypts_bgv_iff P hk] at he
  exact he.1

end Validation.Budget
