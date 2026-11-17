import Challenge.Headline
import Validation.Source

/-!
# Validation.Headline.Noise — the BGV noise headline (H6)

`FHE.Holes.analyze` is `Challenge.Headline.refAnalyze` (through `FHE.Noise.analyze`). This file
proves that analysis sound against every ciphertext-level run meeting the `Spec.Trace` phase
contracts (`analyze_sound`), never worse than the reference (`analyze_tight`, trivially), and
accepting the depth-2 corpus program (`analyze_accepts_addMul`, by kernel evaluation).

**Invariant.** Along a run, every variable `x` with a tracked bound `β x = some b` holds, in the
ciphertext environment, a ciphertext that `Encrypts` the value of `x` in the message environment
with noise at most `b`. Each phase contract plus the `2 · b < Q` check that the analysis performs
at each step makes the centred lift of the new phase exact, which re-establishes the invariant.

**Messages.** The reference analysis runs `Source.step` on all-zero messages; the run uses the
real ones. For BGV, with every message `.exact`, zeroing the messages commutes with `step`
(`step_zenv`), so both runs see the same shapes and the same levels.

No `Challenge.*` definition is unfolded with `simp`/`rw`/`unfold`: the local `rfl` lemmas below
give the needed equations, so no new `Challenge.*` equation lemma is generated.
-/

namespace Validation.Headline
open Spec NPoly Scheme Source Correct Challenge.Headline
open Validation.Ring Validation.Scheme Validation.Source

-- Helper definitions and lemmas, kept out of the shared `Validation.Headline` namespace.
namespace NoiseAux

/-! ### Zeroing messages -/

section Zero
variable {Pr : Params}

/-- The value with its message replaced by the exact zero message. -/
def zv (v : Val Pr) : Val Pr := { v with msg := .exact 0 }

/-- The environment with every message replaced by zero. -/
def zenv (ρ : Env Pr) : Env Pr := fun x => (ρ x).map zv

/-- Every message is exact (as `Encrypts` requires for BGV). -/
def AllExact (ρ : Env Pr) : Prop := ∀ x v, ρ x = some v → ∃ m, v.msg = .exact m

theorem zenv_set (ρ : Env Pr) (d : Var) (v : Val Pr) :
    zenv (ρ.set d v) = (zenv ρ).set d (zv v) := by
  funext y; simp only [zenv, Env.set]; split_ifs <;> rfl

theorem allExact_set {ρ : Env Pr} (h : AllExact ρ) (d : Var) (v : Val Pr) (m : Poly Pr.t Pr.N)
    (hm : v.msg = .exact m) : AllExact (ρ.set d v) := by
  intro y w hw
  simp only [Env.set] at hw
  split_ifs at hw
  · cases hw; exact ⟨m, hm⟩
  · exact h y w hw


theorem npoly_zero_add {R : Type} [CommRing R] {N : ℕ} : (0 : NPoly R N) + 0 = 0 := by ext; simp
theorem npoly_zero_sub {R : Type} [CommRing R] {N : ℕ} : (0 : NPoly R N) - 0 = 0 := by ext; simp
theorem npoly_zero_mul {R : Type} [CommRing R] {N : ℕ} : (0 : NPoly R N) * 0 = 0 := by
  ext k; simp [coeff_mul']
theorem npoly_smul_zero {R : Type} [CommRing R] {N : ℕ} (c : R) : c • (0 : NPoly R N) = 0 := by
  ext; simp

theorem step_zenv (hk : Pr.kind = .bgv) {ρ : Env Pr} (hρ : AllExact ρ) (i : Instr) :
    step Pr (zenv ρ) i = (step Pr ρ i).map zenv ∧ ∀ ρ', step Pr ρ i = some ρ' → AllExact ρ' := by
  cases i with
  | add d a b | sub d a b | mul d a b | addPlain d a b | subPlain d a b | mulPlain d a b =>
    rcases h1 : ρ a with _ | x
    · simp [step, zenv, h1]
    rcases h2 : ρ b with _ | y
    · simp [step, zenv, h1, h2]
    obtain ⟨m, hm⟩ := hρ a x h1
    obtain ⟨m', hm'⟩ := hρ b y h2
    simp only [step, zenv, h1, h2, zv, hm, hm', Msg.lift₂, hk, Option.map_some, Option.bind_eq_bind,
      Option.bind_some, Option.pure_def, guard]
    refine ⟨?_, ?_⟩
    · split_ifs <;> simp [zenv_set, zv, npoly_zero_add, npoly_zero_sub, npoly_zero_mul]
    · intro ρ' h; split_ifs at h <;> simp at h
      all_goals (subst h; exact allExact_set hρ _ _ _ rfl)
  | square d a | mulConst d a _ | copy d a | toEval d a | toCoeff d a | relin d a | keySwitch d a
  | automorph d a _ | modSwitch d a | dropLimbs d a _ =>
    rcases h1 : ρ a with _ | x
    · simp [step, zenv, h1]
    obtain ⟨m, hm⟩ := hρ a x h1
    rcases hq : Pr.qs[x.level - 1]? with _ | q
    all_goals simp only [step, zenv, h1, zv, hm, hq, Msg.lift₂, Msg.lift₁, hk, Option.map_some,
      Option.bind_eq_bind, Option.bind_some, Option.bind_none, Option.pure_def, guard]
    all_goals refine ⟨?_, ?_⟩
    all_goals first
    | (try split_ifs
       all_goals simp [zenv_set, zv, npoly_zero_mul, npoly_smul_zero, automorph_zero]
       done)
    | (intro ρ' h
       try split_ifs at h
       all_goals simp at h
       all_goals (subst h; first | exact allExact_set hρ _ _ _ rfl | exact allExact_set hρ _ _ _ hm))
end Zero

/-! ### Equations of the reference analysis (by `rfl`, no `Challenge.*` equation lemmas) -/

section Ref
variable (P : FullParams) (E : Trace.Budget)

theorem refRun_nil (ρ : Env P.src) (β : Var → Option ℕ) : refRun P E [] ρ β = some (ρ, β) := rfl

theorem refRun_cons_some {i : Instr} {is : List Instr} {ρ : Env P.src} {β : Var → Option ℕ}
    {r : Env P.src × (Var → Option ℕ)} (h : refRun P E (i :: is) ρ β = some r) :
    ∃ ρ' b v, step P.src ρ i = some ρ' ∧ refBound P E ρ β i = some b ∧
      ρ' (Trace.dst i) = some v ∧ 2 * b < P.src.modulus v.level ∧
      refRun P E is ρ' (fun y => if y = Trace.dst i then some b else β y) = some r := by
  have e : refRun P E (i :: is) ρ β = (do
      let ρ' ← step P.src ρ i
      let b ← refBound P E ρ β i
      let v ← ρ' (Trace.dst i)
      guard (2 * b < P.src.modulus v.level)
      refRun P E is ρ' (fun y => if y = Trace.dst i then some b else β y)) := rfl
  rw [e] at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, guard] at h
  obtain ⟨ρ', h1, b, h2, v, h3, h4⟩ := h
  split_ifs at h4 with hq
  · exact ⟨ρ', b, v, h1, h2, h3, hq, by simpa using h4⟩
  · simp at h4

end Ref

/-! ### The invariant -/

section Inv
variable (P : FullParams)

/-- Every tracked bound is the noise bound of the variable's ciphertext for its value. -/
def Inv (s : IntPoly P.src.N) (ρ : Env P.src) (β : Var → Option ℕ) (σ : Trace.CtEnv P) : Prop :=
  ∀ x b, β x = some b → ∃ v ct, ρ x = some v ∧ σ x = some ct ∧ Encrypts P s b v ct

variable {P}

theorem enc_elim (hk : P.src.kind = .bgv) {s : IntPoly P.src.N} {b : ℕ} {v : Val P.src}
    {ct : List (IntPoly P.src.N)} (h : Encrypts P s b v ct) :
    ∃ m, v.msg = .exact m ∧
      (∀ i, |(centered (Trace.phaseAt P (P.src.modulus v.level) v.key s ct)).coeff i| ≤ b) ∧
      ofInt P.src.t (centered (Trace.phaseAt P (P.src.modulus v.level) v.key s ct)) = m := by
  rw [encrypts_bgv_iff P hk] at h
  obtain ⟨-, m, hm, hb⟩ := h
  exact ⟨m, hm, BGVEncrypts.bound hb, BGVEncrypts.msg hb⟩

theorem enc_intro (hk : P.src.kind = .bgv) {s : IntPoly P.src.N} {b : ℕ} {v : Val P.src}
    {ct : List (IntPoly P.src.N)} {m : Poly P.src.t P.src.N} (Φ : IntPoly P.src.N)
    (hm : v.msg = .exact m) (hl : ct.length = v.parts)
    (hph : Trace.phaseAt P (P.src.modulus v.level) v.key s ct = ofInt _ Φ)
    (hb : ∀ i, |Φ.coeff i| ≤ b) (hQ : 2 * b < P.src.modulus v.level) (hmt : ofInt P.src.t Φ = m) :
    Encrypts P s b v ct :=
  (encrypts_bgv_iff P hk s b v ct).mpr ⟨hl, m, hm, bgvEncrypts_of_phase Φ hph hb hQ hmt⟩

theorem phaseAt_centered (Q key : ℕ) (s : IntPoly P.src.N) (ct : List (IntPoly P.src.N)) :
    Trace.phaseAt P Q key s ct = ofInt Q (centered (Trace.phaseAt P Q key s ct)) :=
  (ofInt_centered _).symm

theorem encrypts_mono (hk : P.src.kind = .bgv) {s : IntPoly P.src.N} {b b' : ℕ} {v : Val P.src}
    {ct : List (IntPoly P.src.N)} (h : Encrypts P s b v ct) (hbb : b ≤ b') : Encrypts P s b' v ct := by
  rw [encrypts_bgv_iff P hk] at h ⊢
  obtain ⟨hl, m, hm, h1, h2⟩ := h
  exact ⟨hl, m, hm, h1, h2.trans hbb⟩

/-- The operand of a step: what the invariant says about it. -/
theorem operand {s : IntPoly P.src.N} {ρ : Env P.src} {β : Var → Option ℕ} {σ : Trace.CtEnv P}
    (h : Inv P s ρ β σ) {a : Var} {b : ℕ} {x : Val P.src} {ca : List (IntPoly P.src.N)}
    (hβ : β a = some b) (hx : ρ a = some x) (hc : σ a = some ca) : Encrypts P s b x ca := by
  obtain ⟨x', ca', hx', hc', he⟩ := h a b hβ
  rw [hx] at hx'; rw [hc] at hc'
  cases hx'; cases hc'
  exact he

end Inv

/-! ### Per-operation noise arithmetic -/

theorem ite_bind_some {p : Prop} [Decidable p] {α : Type} {f : Unit → Option α} {r : α}
    (h : (if p then some () else none).bind f = some r) : p ∧ f () = some r := by
  by_cases hp : p
  · simp only [hp, ite_true, Option.bind_some] at h; exact ⟨hp, h⟩
  · simp [hp] at h

theorem npoly_add_zero {R : Type} [CommRing R] {N : ℕ} (a : NPoly R N) : a + 0 = a := by
  ext; simp

theorem ofInt_zsmul {N : ℕ} (Q : ℕ) (c : ℤ) (a : IntPoly N) :
    ofInt Q (c • a) = (c : ZMod Q) • ofInt Q a := by
  ext j; simp

theorem ofInt_eq_zero_of_dvd {N : ℕ} (t : ℕ) (e : IntPoly N) (h : ∀ j, (t : ℤ) ∣ e.coeff j) :
    ofInt t e = 0 := by
  ext j; simp only [coeff_ofInt, coeff_zero']
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr (h j)

/-- The noise arithmetic of the exact division in `modSwitch`. -/
theorem abs_div_le (q bx M : ℕ) (u d : ℤ) (hu : |u| ≤ bx) (hd : |d| ≤ ((q * M : ℕ) : ℤ))
    (hq : (q : ℤ) ∣ u + d) : |(u + d) / (q : ℤ)| ≤ ((bx / q + M : ℕ) : ℤ) := by
  rcases Nat.eq_zero_or_pos q with h0 | hpos
  · subst h0; simp
  obtain ⟨k, hk⟩ := hq
  rw [hk, Int.mul_ediv_cancel_left _ (by exact_mod_cast hpos.ne')]
  have h1 : |(q : ℤ) * k| ≤ bx + ((q * M : ℕ) : ℤ) := by
    rw [← hk]; exact (abs_add_le _ _).trans (add_le_add hu hd)
  rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℤ) ≤ q), ← Int.natCast_natAbs] at h1
  rw [← Int.natCast_natAbs]
  have h2 : q * k.natAbs ≤ bx + q * M := by exact_mod_cast h1
  have h3 : k.natAbs ≤ (bx + q * M) / q := by
    rw [Nat.le_div_iff_mul_le hpos]; linarith
  rw [Nat.add_mul_div_left _ _ hpos] at h3
  exact_mod_cast h3

section DstOK
variable {P : FullParams}

/-- **One step.** If the invariant holds before an instruction, the reference analysis gives it
the bound `b` with `2 · b < Q` at the destination's level, and the ciphertext step meets its
`Spec.Trace` contract, then the destination ciphertext encrypts the destination's new value with
noise at most `b`. One case per operation. -/
theorem dst_ok (hk : P.src.kind = .bgv) (hP : SchemeParamsOK P) (E : Trace.Budget) (s : IntPoly P.src.N)
    {ρ ρ' : Env P.src} {σ σ' : Trace.CtEnv P} {β : Var → Option ℕ} {i : Instr} {b : ℕ}
    {v : Val P.src} (hinv : Inv P s ρ β σ) (hb : refBound P E (zenv ρ) β i = some b)
    (hstep : step P.src ρ i = some ρ') (hv : ρ' (Trace.dst i) = some v)
    (hQ : 2 * b < P.src.modulus v.level) (hok : Trace.StepOK P E s ρ ρ' σ σ' i) :
    ∃ ct, σ' = σ.set (Trace.dst i) ct ∧ Encrypts P s b v ct := by
  obtain ⟨v', ct, hv', hlen, hσ', hφ⟩ := hok
  rw [hv] at hv'; cases hv'
  refine ⟨ct, hσ', ?_⟩
  cases i with
  | add d a c =>
    obtain ⟨x, y, ca, cc, hx, hy, hca, hcc, hφ⟩ := hφ
    have e : refBound P E (zenv ρ) β (.add d a c) = (do let x ← β a; let y ← β c; pure (x + y)) := rfl
    rw [e] at hb
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at hb
    obtain ⟨bx, hbx, by', hby, rfl⟩ := hb
    obtain ⟨m, hm, hbm, hmm⟩ := enc_elim hk (operand hinv hbx hx hca)
    obtain ⟨m', hm', hbm', hmm'⟩ := enc_elim hk (operand hinv hby hy hcc)
    simp [step, hx, hy, hm, hm', Msg.lift₂, guard] at hstep
    obtain ⟨hg, hstep⟩ := ite_bind_some hstep
    simp only [Option.some.injEq] at hstep
    subst hstep
    simp only [Trace.dst, set_self, Option.some.injEq] at hv; subst hv
    obtain ⟨hl, hkey⟩ := hg
    dsimp only at hφ hQ ⊢
    rw [← hl, ← hkey] at hbm' hmm'
    refine enc_intro hk (centered (Trace.phaseAt P (P.src.modulus x.level) x.key s ca) +
      centered (Trace.phaseAt P (P.src.modulus x.level) x.key s cc)) rfl hlen ?_ ?_ hQ ?_
    · rw [hφ, ← hkey, ofInt_add, ← phaseAt_centered, ← phaseAt_centered]
    · intro j; rw [coeff_add']; push_cast
      exact (abs_add_le _ _).trans (add_le_add (hbm j) (hbm' j))
    · rw [ofInt_add, hmm, hmm']
  | sub d a c =>
    obtain ⟨x, y, ca, cc, hx, hy, hca, hcc, hφ⟩ := hφ
    have e : refBound P E (zenv ρ) β (.sub d a c) = (do let x ← β a; let y ← β c; pure (x + y)) := rfl
    rw [e] at hb
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at hb
    obtain ⟨bx, hbx, by', hby, rfl⟩ := hb
    obtain ⟨m, hm, hbm, hmm⟩ := enc_elim hk (operand hinv hbx hx hca)
    obtain ⟨m', hm', hbm', hmm'⟩ := enc_elim hk (operand hinv hby hy hcc)
    simp [step, hx, hy, hm, hm', Msg.lift₂, guard] at hstep
    obtain ⟨hg, hstep⟩ := ite_bind_some hstep
    simp only [Option.some.injEq] at hstep
    subst hstep
    simp only [Trace.dst, set_self, Option.some.injEq] at hv; subst hv
    obtain ⟨hl, hkey⟩ := hg
    dsimp only at hφ hQ ⊢
    rw [← hl, ← hkey] at hbm' hmm'
    refine enc_intro hk (centered (Trace.phaseAt P (P.src.modulus x.level) x.key s ca) -
      centered (Trace.phaseAt P (P.src.modulus x.level) x.key s cc)) rfl hlen ?_ ?_ hQ ?_
    · rw [hφ, ← hkey, ofInt_sub, ← phaseAt_centered, ← phaseAt_centered]
    · intro j; rw [coeff_sub']; push_cast
      exact (abs_sub _ _).trans (add_le_add (hbm j) (hbm' j))
    · rw [ofInt_sub, hmm, hmm']
  | mul d a c =>
    obtain ⟨x, y, ca, cc, hx, hy, hca, hcc, hφ⟩ := hφ
    have e : refBound P E (zenv ρ) β (.mul d a c) =
      (do let x ← β a; let y ← β c; pure (P.src.N * x * y)) := rfl
    rw [e] at hb
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at hb
    obtain ⟨bx, hbx, by', hby, rfl⟩ := hb
    obtain ⟨m, hm, hbm, hmm⟩ := enc_elim hk (operand hinv hbx hx hca)
    obtain ⟨m', hm', hbm', hmm'⟩ := enc_elim hk (operand hinv hby hy hcc)
    simp [step, hx, hy, hm, hm', Msg.lift₂, guard] at hstep
    obtain ⟨hg, hstep⟩ := ite_bind_some hstep
    simp only [Option.some.injEq] at hstep
    subst hstep
    simp only [Trace.dst, set_self, Option.some.injEq] at hv; subst hv
    obtain ⟨hl, hkey, -⟩ := hg
    dsimp only at hφ hQ ⊢
    rw [← hl, ← hkey] at hbm' hmm'
    refine enc_intro hk (centered (Trace.phaseAt P (P.src.modulus x.level) x.key s ca) *
      centered (Trace.phaseAt P (P.src.modulus x.level) x.key s cc)) rfl hlen ?_ ?_ hQ ?_
    · rw [hφ, ← hkey, ofInt_mul, ← phaseAt_centered, ← phaseAt_centered]
    · intro j; push_cast
      exact abs_coeff_mul_le_N _ _ _ _ hbm hbm' j
    · rw [ofInt_mul, hmm, hmm']
  | square d a =>
    obtain ⟨x, ca, hx, hca, hφ⟩ := hφ
    have e : refBound P E (zenv ρ) β (.square d a) =
      (do let x ← β a; pure (P.src.N * x * x)) := rfl
    rw [e] at hb
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at hb
    obtain ⟨bx, hbx, rfl⟩ := hb
    obtain ⟨m, hm, hbm, hmm⟩ := enc_elim hk (operand hinv hbx hx hca)
    simp [step, hx, hm, Msg.lift₂, guard] at hstep
    obtain ⟨hg, hstep⟩ := ite_bind_some hstep
    simp only [Option.some.injEq] at hstep
    subst hstep
    simp only [Trace.dst, set_self, Option.some.injEq] at hv; subst hv
    dsimp only at hφ hQ ⊢
    refine enc_intro hk (centered (Trace.phaseAt P (P.src.modulus x.level) x.key s ca) *
      centered (Trace.phaseAt P (P.src.modulus x.level) x.key s ca)) rfl hlen ?_ ?_ hQ ?_
    · rw [hφ, ofInt_mul, ← phaseAt_centered]
    · intro j; push_cast
      exact abs_coeff_mul_le_N _ _ _ _ hbm hbm j
    · rw [ofInt_mul, hmm]
  | mulConst d a c =>
    obtain ⟨x, ca, hx, hca, hφ⟩ := hφ
    have e : refBound P E (zenv ρ) β (.mulConst d a c) =
      (do let x ← β a; pure (c.natAbs * x)) := rfl
    rw [e] at hb
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at hb
    obtain ⟨bx, hbx, rfl⟩ := hb
    obtain ⟨m, hm, hbm, hmm⟩ := enc_elim hk (operand hinv hbx hx hca)
    simp [step, hx, hm, Msg.lift₁] at hstep
    subst hstep
    simp only [Trace.dst, set_self, Option.some.injEq] at hv; subst hv
    dsimp only at hφ hQ ⊢
    refine enc_intro hk (c • centered (Trace.phaseAt P (P.src.modulus x.level) x.key s ca)) rfl hlen
      ?_ ?_ hQ ?_
    · rw [hφ, ofInt_zsmul, ← phaseAt_centered]
    · intro j
      rw [coeff_smul', abs_mul]
      push_cast
      exact mul_le_mul_of_nonneg_left (hbm j) (abs_nonneg c)
    · rw [ofInt_zsmul, hmm]
  | copy d a | toEval d a | toCoeff d a =>
    obtain ⟨x, ca, hx, hca, hφ⟩ := hφ
    have hb' : β a = some b := hb
    obtain ⟨m, hm, hbm, hmm⟩ := enc_elim hk (operand hinv hb' hx hca)
    simp [step, hx] at hstep
    subst hstep
    simp only [Trace.dst, set_self, Option.some.injEq] at hv; subst hv
    refine enc_intro hk (centered (Trace.phaseAt P (P.src.modulus x.level) x.key s ca)) hm hlen
      ?_ hbm hQ hmm
    rw [hφ, ← phaseAt_centered]
  | automorph d a g =>
    obtain ⟨x, ca, hx, hca, hφ⟩ := hφ
    have hb' : β a = some b := hb
    obtain ⟨m, hm, hbm, hmm⟩ := enc_elim hk (operand hinv hb' hx hca)
    simp [step, hx, hm, Msg.lift₁, guard] at hstep
    obtain ⟨hg, hstep⟩ := ite_bind_some hstep
    simp only [Option.some.injEq] at hstep
    subst hstep
    simp only [Trace.dst, set_self, Option.some.injEq] at hv; subst hv
    dsimp only at hφ hQ ⊢
    refine enc_intro hk (automorph g (centered (Trace.phaseAt P (P.src.modulus x.level) x.key s ca)))
      rfl hlen ?_ ?_ hQ ?_
    · rw [hφ, ofInt_automorph, ← phaseAt_centered]
    · intro j
      exact abs_coeff_automorph_le hP.N_pow2 hg _ _ hbm j
    · rw [ofInt_automorph, hmm]
  | relin d a | keySwitch d a =>
    obtain ⟨x, ca, er, hx, hca, her, hdiv, hφ⟩ := hφ
    have e1 : refBound P E (zenv ρ) β (.relin d a) =
      (do let x ← β a; pure (x + E.keySwitch)) := rfl
    have e2 : refBound P E (zenv ρ) β (.keySwitch d a) =
      (do let x ← β a; pure (x + E.keySwitch)) := rfl
    first | rw [e1] at hb | rw [e2] at hb
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at hb
    obtain ⟨bx, hbx, rfl⟩ := hb
    obtain ⟨m, hm, hbm, hmm⟩ := enc_elim hk (operand hinv hbx hx hca)
    simp [step, hx, guard] at hstep
    obtain ⟨hg, hstep⟩ := ite_bind_some hstep
    simp only [Option.some.injEq] at hstep
    subst hstep
    simp only [Trace.dst, set_self, Option.some.injEq] at hv; subst hv
    dsimp only at hφ hQ ⊢
    refine enc_intro hk (centered (Trace.phaseAt P (P.src.modulus x.level) x.key s ca) + er)
      hm hlen ?_ ?_ hQ ?_
    · rw [hφ, ofInt_add, ← phaseAt_centered]
    · intro j; rw [coeff_add']; push_cast
      exact (abs_add_le _ _).trans (add_le_add (hbm j) ((normInf_le_iff _ _).mp her j))
    · rw [ofInt_add, hmm, ofInt_eq_zero_of_dvd _ _ hdiv, npoly_add_zero]
  | modSwitch d a =>
    obtain ⟨x, ca, δ, q, hx, hca, hq, hδ, htδ, hqδ, hφ⟩ := hφ
    have e : refBound P E (zenv ρ) β (.modSwitch d a) =
      (do let x ← β a; let v ← zenv ρ a; let q ← P.src.qs[v.level - 1]?
          pure (x / q + E.modSwitchAt v.parts)) := rfl
    rw [e] at hb
    simp only [zenv, hx, Option.map_some, zv, hq, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.pure_def, Option.some.injEq, Option.bind_some] at hb
    obtain ⟨bx, hbx, rfl⟩ := hb
    obtain ⟨m, hm, hbm, hmm⟩ := enc_elim hk (operand hinv hbx hx hca)
    obtain ⟨hlt, hqe⟩ := List.getElem?_eq_some_iff.mp hq
    have hfacts := qLast_facts P hP _ hlt
    have hq' : P.src.qs[x.level - 1]! = q := by simp [hlt, hqe]
    rw [hq'] at hfacts
    have hpos : 0 < q := hfacts.1.pos
    have hcop : Nat.Coprime q P.src.t := hfacts.2.symm
    simp [step, hx, hm, hq, Msg.lift₁, hk, guard] at hstep
    obtain ⟨hg, hstep⟩ := ite_bind_some hstep
    simp only [Option.some.injEq] at hstep
    subst hstep
    simp only [Trace.dst, set_self, Option.some.injEq] at hv; subst hv
    dsimp only at hφ hQ hδ htδ hqδ ⊢
    set Φ := centered (Trace.phaseAt P (P.src.modulus x.level) x.key s ca) with hΦdef
    refine enc_intro hk ⟨fun j => (Φ.coeff j + δ.coeff j) / (q : ℤ)⟩ rfl hlen hφ ?_ hQ ?_
    · intro j
      exact abs_div_le q bx (E.modSwitchAt x.parts) _ _ (hbm j) ((normInf_le_iff _ _).mp hδ j) (hqδ j)
    · ext j
      simp only [coeff_ofInt, coeff_smul']
      have hinv := ZMod.coe_mul_inv_eq_one q hcop
      obtain ⟨k, hk'⟩ := hqδ j
      rw [hk', Int.mul_ediv_cancel_left _ (by exact_mod_cast hpos.ne')]
      have h1 := congrArg (Int.cast : ℤ → ZMod P.src.t) hk'
      push_cast at h1
      have hΦm : ((Φ.coeff j : ℤ) : ZMod P.src.t) = m.coeff j := by
        have := congrArg (fun p => p.coeff j) hmm; simpa using this
      have hδ0 : ((δ.coeff j : ℤ) : ZMod P.src.t) = 0 :=
        (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr (htδ j)
      linear_combination (-(k : ZMod P.src.t)) * hinv - ((q : ZMod P.src.t))⁻¹ * h1 +
        ((q : ZMod P.src.t))⁻¹ * hΦm + ((q : ZMod P.src.t))⁻¹ * hδ0
  | addPlain d a c =>
    obtain ⟨x, y, ca, cc, hx, hy, hca, hcc, hφ⟩ := hφ
    have e : refBound P E (zenv ρ) β (.addPlain d a c) =
      (do let x ← β a; let y ← β c; pure (x + y)) := rfl
    rw [e] at hb
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at hb
    obtain ⟨bx, hbx, by', hby, rfl⟩ := hb
    obtain ⟨m, hm, hbm, hmm⟩ := enc_elim hk (operand hinv hbx hx hca)
    obtain ⟨m', hm', hbm', hmm'⟩ := enc_elim hk (operand hinv hby hy hcc)
    simp [step, hx, hy, hm, hm', Msg.lift₂, guard] at hstep
    obtain ⟨hg, hstep⟩ := ite_bind_some hstep
    simp only [Option.some.injEq] at hstep
    subst hstep
    simp only [Trace.dst, set_self, Option.some.injEq] at hv; subst hv
    obtain ⟨-, hl⟩ := hg
    dsimp only at hφ hQ ⊢
    rw [← hl] at hbm' hmm'
    refine enc_intro hk (centered (Trace.phaseAt P (P.src.modulus x.level) x.key s ca) +
      centered (Trace.phaseAt P (P.src.modulus x.level) y.key s cc)) rfl hlen ?_ ?_ hQ ?_
    · rw [hφ, ofInt_add, ← phaseAt_centered, ← phaseAt_centered]
    · intro j; rw [coeff_add']; push_cast
      exact (abs_add_le _ _).trans (add_le_add (hbm j) (hbm' j))
    · rw [ofInt_add, hmm, hmm']
  | subPlain d a c =>
    obtain ⟨x, y, ca, cc, hx, hy, hca, hcc, hφ⟩ := hφ
    have e : refBound P E (zenv ρ) β (.subPlain d a c) =
      (do let x ← β a; let y ← β c; pure (x + y)) := rfl
    rw [e] at hb
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at hb
    obtain ⟨bx, hbx, by', hby, rfl⟩ := hb
    obtain ⟨m, hm, hbm, hmm⟩ := enc_elim hk (operand hinv hbx hx hca)
    obtain ⟨m', hm', hbm', hmm'⟩ := enc_elim hk (operand hinv hby hy hcc)
    simp [step, hx, hy, hm, hm', Msg.lift₂, guard] at hstep
    obtain ⟨hg, hstep⟩ := ite_bind_some hstep
    simp only [Option.some.injEq] at hstep
    subst hstep
    simp only [Trace.dst, set_self, Option.some.injEq] at hv; subst hv
    obtain ⟨-, hl⟩ := hg
    dsimp only at hφ hQ ⊢
    rw [← hl] at hbm' hmm'
    refine enc_intro hk (centered (Trace.phaseAt P (P.src.modulus x.level) x.key s ca) -
      centered (Trace.phaseAt P (P.src.modulus x.level) y.key s cc)) rfl hlen ?_ ?_ hQ ?_
    · rw [hφ, ofInt_sub, ← phaseAt_centered, ← phaseAt_centered]
    · intro j; rw [coeff_sub']; push_cast
      exact (abs_sub _ _).trans (add_le_add (hbm j) (hbm' j))
    · rw [ofInt_sub, hmm, hmm']
  | mulPlain d a c =>
    obtain ⟨x, y, ca, cc, hx, hy, hca, hcc, hφ⟩ := hφ
    have e : refBound P E (zenv ρ) β (.mulPlain d a c) =
      (do let x ← β a; let y ← β c; pure (P.src.N * x * y)) := rfl
    rw [e] at hb
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at hb
    obtain ⟨bx, hbx, by', hby, rfl⟩ := hb
    obtain ⟨m, hm, hbm, hmm⟩ := enc_elim hk (operand hinv hbx hx hca)
    obtain ⟨m', hm', hbm', hmm'⟩ := enc_elim hk (operand hinv hby hy hcc)
    simp [step, hx, hy, hm, hm', Msg.lift₂, guard] at hstep
    obtain ⟨hg, hstep⟩ := ite_bind_some hstep
    simp only [Option.some.injEq] at hstep
    subst hstep
    simp only [Trace.dst, set_self, Option.some.injEq] at hv; subst hv
    obtain ⟨-, hl, -⟩ := hg
    dsimp only at hφ hQ ⊢
    rw [← hl] at hbm' hmm'
    refine enc_intro hk (centered (Trace.phaseAt P (P.src.modulus x.level) x.key s ca) *
      centered (Trace.phaseAt P (P.src.modulus x.level) y.key s cc)) rfl hlen ?_ ?_ hQ ?_
    · rw [hφ, ofInt_mul, ← phaseAt_centered, ← phaseAt_centered]
    · intro j; push_cast
      exact abs_coeff_mul_le_N _ _ _ _ hbm hbm' j
    · rw [ofInt_mul, hmm, hmm']
  | dropLimbs d a k =>
    obtain ⟨x, ca, hx, hca, hφ⟩ := hφ
    have hb' : β a = some b := hb
    obtain ⟨m, hm, hbm, hmm⟩ := enc_elim hk (operand hinv hb' hx hca)
    simp [step, hx, guard] at hstep
    obtain ⟨hg, hstep⟩ := ite_bind_some hstep
    simp only [Option.some.injEq] at hstep
    subst hstep
    simp only [Trace.dst, set_self, Option.some.injEq] at hv; subst hv
    dsimp only at hφ hQ ⊢
    exact enc_intro hk (centered (Trace.phaseAt P (P.src.modulus x.level) x.key s ca)) hm hlen
      hφ hbm hQ hmm
end DstOK

/-- `step` changes only the destination. -/
theorem step_set {Pr : Params} {ρ ρ' : Env Pr} {i : Instr} (h : step Pr ρ i = some ρ') :
    ∃ v, ρ' = ρ.set (Trace.dst i) v := by
  cases i <;> simp only [step, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq, guard] at h
  all_goals (simp only [Trace.dst]; aesop)

/-! ### The run -/

section Run
variable {P : FullParams}

theorem run_sound (hk : P.src.kind = .bgv) (hP : SchemeParamsOK P) (E : Trace.Budget)
    (s : IntPoly P.src.N) : ∀ (body : List Instr) (ρ : Env P.src) (β : Var → Option ℕ)
    (r : Env P.src × (Var → Option ℕ)), AllExact ρ → refRun P E body (zenv ρ) β = some r →
    ∃ ρf, body.foldlM (step P.src) ρ = some ρf ∧ r.1 = zenv ρf ∧
      ∀ σ σf, Inv P s ρ β σ → Trace.Run P E s body ρ σ σf → Inv P s ρf r.2 σf := by
  intro body
  induction body with
  | nil =>
    intro ρ β r _ h
    rw [refRun_nil] at h
    cases h
    refine ⟨ρ, rfl, rfl, ?_⟩
    intro σ σf hinv hrun
    have : σf = σ := hrun
    subst this; exact hinv
  | cons i is ih =>
    intro ρ β r hρ h
    obtain ⟨ρz', b, vz, h1, h2, h3, h4, h5⟩ := refRun_cons_some P E h
    obtain ⟨hz, hex⟩ := step_zenv hk hρ i
    rw [hz] at h1
    obtain ⟨ρ', hs, rfl⟩ := Option.map_eq_some_iff.mp h1
    have hρ' := hex ρ' hs
    obtain ⟨ρf, hf, hr, hinvf⟩ := ih ρ' _ r hρ' h5
    refine ⟨ρf, ?_, hr, ?_⟩
    · simp only [List.foldlM_cons, hs, Option.bind_eq_bind, Option.bind_some]; exact hf
    intro σ σf hinv hrun
    obtain ⟨ρ'', σ', hs', hok, hrun'⟩ := hrun
    rw [hs] at hs'; cases hs'
    simp only [zenv] at h3
    obtain ⟨v, hv, rfl⟩ := Option.map_eq_some_iff.mp h3
    obtain ⟨ct, hσ', hct⟩ := dst_ok hk hP E s hinv h2 hs hv h4 hok
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

/-! ### Lists -/

theorem le_foldl_max_init (l : List ℕ) (a : ℕ) : a ≤ l.foldl max a := by
  induction l generalizing a with
  | nil => exact le_rfl
  | cons x l ih => exact (le_max_left a x).trans (ih _)

theorem le_foldl_max {b : ℕ} : ∀ {l : List ℕ} (a : ℕ), b ∈ l → b ≤ l.foldl max a
  | x :: l, a, h => by
    rcases List.mem_cons.mp h with rfl | h
    · exact (le_max_right a b).trans (le_foldl_max_init l _)
    · exact le_foldl_max (max a x) h

theorem mapM_some {α β : Type} (f : α → Option β) : ∀ (l : List α) (bs : List β),
    l.mapM f = some bs → ∀ o ∈ l, ∃ b ∈ bs, f o = some b
  | [], _, _, o, ho => by simp at ho
  | x :: l, bs, h, o, ho => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨b, hb, bs', hbs', rfl⟩ := h
    rcases List.mem_cons.mp ho with rfl | ho
    · exact ⟨b, List.mem_cons_self .., hb⟩
    · obtain ⟨b', hb', hfb'⟩ := mapM_some f l bs' hbs' o ho
      exact ⟨b', List.mem_cons_of_mem _ hb', hfb'⟩

/-! ### The headline, for the reference analysis -/

section Main
variable {P : FullParams}

theorem refAnalyze_some {E : Trace.Budget} {prog : Program} {B : ℕ}
    (h : refAnalyze P E prog = some B) :
    P.src.kind = .bgv ∧ (prog.inputs.all fun d => d.ok P.src) = true ∧ ∃ ρz β, refRun P E prog.body (initEnv P.src prog fun _ => .exact 0)
        (fun x => (prog.inputs.find? (·.name = x)).map fun _ =>
          match prog.boundOf x with
          | some b => min b P.inputNoise
          | none => P.inputNoise) = some (ρz, β) ∧
      (prog.outputs.all fun o => (ρz o).isSome) = true ∧
      ∃ bs, prog.outputs.mapM β = some bs ∧ bs.foldl max 0 = B := by
  have e : refAnalyze P E prog = (do
      guard (P.src.kind = .bgv)
      guard (prog.inputs.all fun d => d.ok P.src)
      let β₀ : Var → Option ℕ := fun x => (prog.inputs.find? (·.name = x)).map fun _ =>
        match prog.boundOf x with
        | some b => min b P.inputNoise
        | none => P.inputNoise
      let (ρ, β) ← refRun P E prog.body (initEnv P.src prog fun _ => .exact 0) β₀
      guard (prog.outputs.all fun o => (ρ o).isSome)
      let bs ← prog.outputs.mapM β
      pure (bs.foldl max 0)) := rfl
  rw [e] at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, guard] at h
  obtain ⟨_, h0, _, hd, ⟨ρz, β⟩, h1, _, h2, bs, h3, h4⟩ := h
  have hk : P.src.kind = .bgv := by by_contra hk; simp [hk] at h0
  have hd' : (prog.inputs.all fun d => d.ok P.src) = true := by by_contra hd'; simp [hd'] at hd
  by_cases hc : (prog.outputs.all fun o => (ρz o).isSome) = true
  · exact ⟨hk, hd', ρz, β, h1, hc, bs, h3, by simpa using h4⟩
  · simp [hc] at h2

/-- **Soundness of the reference analysis.** -/
theorem refAnalyze_sound : NoiseSoundBGV refAnalyze := by
  intro P E prog B hP hk hB s msgs cts hin hbd
  obtain ⟨-, hdecl, ρz, βf, hrun, hout, bs, hbs, hB'⟩ := refAnalyze_some hB
  have hfind : ∀ x d, prog.inputs.find? (·.name = x) = some d → d.name = x ∧
      (∃ m, msgs x = .exact m) ∧ Encrypts P s P.inputNoise (inputVal P msgs d) (cts x) := by
    intro x d hd
    have hn : d.name = x := by simpa using List.find?_some hd
    have he := hin x d hd
    obtain ⟨m, hm, -⟩ := enc_elim hk he
    refine ⟨hn, ⟨m, ?_⟩, he⟩
    rw [← hn]; exact hm
  have hρ0 : AllExact (initEnv P.src prog msgs) := by
    intro x v hv
    simp only [initEnv, Option.map_eq_some_iff] at hv
    obtain ⟨d, hd, rfl⟩ := hv
    exact (hfind x d hd).2.1
  have hz0 : zenv (initEnv P.src prog msgs) = initEnv P.src prog fun _ => .exact 0 := by
    funext x; simp only [zenv, initEnv, Option.map_map]; rfl
  rw [← hz0] at hrun
  obtain ⟨ρf, hf, hr, hinv⟩ := run_sound hk hP E s prog.body _ _ _ hρ0 hrun
  simp only at hr
  refine ⟨ρf, ?_, ?_⟩
  · have hfits : (prog.inputs.all fun dcl => (msgs dcl.name).fits P.src.kind) = true := by
      rw [List.all_eq_true]; intro dcl hdcl
      obtain ⟨d, hd⟩ : ∃ d, prog.inputs.find? (·.name = dcl.name) = some d := by
        rw [← Option.isSome_iff_exists, List.find?_isSome]
        exact ⟨dcl, hdcl, by simp⟩
      obtain ⟨m, hm⟩ := (hfind _ d hd).2.1
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
        (fun x => (prog.inputs.find? (·.name = x)).map fun _ =>
          match prog.boundOf x with
          | some b => min b P.inputNoise
          | none => P.inputNoise)
        (Trace.initCt P prog cts) := by
      intro x b hb
      obtain ⟨d, hd, hbe⟩ := Option.map_eq_some_iff.mp hb
      obtain ⟨hn, -, he⟩ := hfind x d hd
      have he' : Encrypts P s b (inputVal P msgs d) (cts x) := by
        cases hbo : prog.boundOf x with
        | none =>
          simp only [hbo] at hbe
          subst hbe; exact he
        | some b0 =>
          simp only [hbo] at hbe
          subst hbe
          rcases le_total b0 P.inputNoise with hle | hle
          · rw [min_eq_left hle]; exact hbd x d b0 hd hbo
          · rw [min_eq_right hle]; exact he
      unfold inputVal at he'; rw [hn] at he'
      exact ⟨_, cts x, by simp [initEnv, hd], by simp [Trace.initCt, hd], he'⟩
    obtain ⟨b, hb, hβ⟩ := mapM_some βf _ bs hbs o ho
    obtain ⟨v, ct, hv, hct, he⟩ := hinv _ σ hinv0 hrunσ o b hβ
    exact ⟨v, ct, hv, hct, encrypts_mono hk he (hB' ▸ le_foldl_max 0 hb)⟩

/-- **Acceptance implies well-formedness**: a program the reference analysis accepts evaluates
on every input whose messages have the shape `InputsOK` requires. (No noise bound of an input is
used: zeroing the messages commutes with `step`.) -/
theorem refAnalyze_eval (hk : P.src.kind = .bgv) {E : Trace.Budget} {prog : Program} {B : ℕ}
    (hB : refAnalyze P E prog = some B) (s : IntPoly P.src.N) (msgs : Var → Msg P.src.t P.src.N)
    (cts : Var → List (IntPoly P.src.N)) (hin : InputsOK P s prog msgs cts) :
    ∃ ρ, Source.eval P.src prog msgs = some ρ := by
  obtain ⟨-, hdecl, ρz, βf, hrun, hout, -⟩ := refAnalyze_some hB
  have hfind : ∀ x d, prog.inputs.find? (·.name = x) = some d → ∃ m, msgs x = .exact m := by
    intro x d hd
    have hn : d.name = x := by simpa using List.find?_some hd
    obtain ⟨m, hm, -⟩ := enc_elim hk (hin x d hd)
    exact ⟨m, by rw [← hn]; exact hm⟩
  have hρ0 : AllExact (initEnv P.src prog msgs) := by
    intro x v hv
    simp only [initEnv, Option.map_eq_some_iff] at hv
    obtain ⟨d, hd, rfl⟩ := hv
    exact hfind x d hd
  have hz0 : zenv (initEnv P.src prog msgs) = initEnv P.src prog fun _ => .exact 0 := by
    funext x; simp only [zenv, initEnv, Option.map_map]; rfl
  rw [← hz0] at hrun
  have heval : ∀ ρf', prog.body.foldlM (step P.src) (initEnv P.src prog msgs) = some ρf' →
      ρz = zenv ρf' → Source.eval P.src prog msgs = some ρf' := by
    intro ρf hf hr
    have hfits : (prog.inputs.all fun dcl => (msgs dcl.name).fits P.src.kind) = true := by
      rw [List.all_eq_true]; intro dcl hdcl
      obtain ⟨d, hd⟩ : ∃ d, prog.inputs.find? (·.name = dcl.name) = some d := by
        rw [← Option.isSome_iff_exists, List.find?_isSome]
        exact ⟨dcl, hdcl, by simp⟩
      obtain ⟨m, hm⟩ := hfind _ d hd
      rw [hm, hk]; rfl
    have hout' : (prog.outputs.all fun o => (ρf o).isSome) = true := by
      rw [hr] at hout; simpa [zenv] using hout
    simp only [List.all_eq_true] at hout'
    simp only [eval, hdecl, hfits, hf, guard, List.all_eq_true, Option.bind_eq_bind, ite_true,
      Option.pure_def, Option.bind_some]
    have hc : (∀ x ∈ prog.outputs, (ρf x).isSome = true) = True := eq_true hout'
    simp only [hc, ite_true, Option.bind_some]
  -- the run on the real messages exists: zeroing messages commutes with `step`
  have hfold : ∀ (body : List Instr) (ρ : Env P.src) (β : Var → Option ℕ)
      (r : Env P.src × (Var → Option ℕ)), AllExact ρ → refRun P E body (zenv ρ) β = some r →
      ∃ ρf, body.foldlM (step P.src) ρ = some ρf ∧ r.1 = zenv ρf := by
    intro body
    induction body with
    | nil =>
      intro ρ β r _ h
      rw [refRun_nil] at h; cases h
      exact ⟨ρ, rfl, rfl⟩
    | cons i is ih =>
      intro ρ β r hρ h
      obtain ⟨ρz', b, vz, h1, -, -, -, h5⟩ := refRun_cons_some P E h
      obtain ⟨hz, hex⟩ := step_zenv hk hρ i
      rw [hz] at h1
      obtain ⟨ρ', hs, rfl⟩ := Option.map_eq_some_iff.mp h1
      obtain ⟨ρf, hf, hr⟩ := ih ρ' _ r (hex ρ' hs) h5
      exact ⟨ρf, by simp only [List.foldlM_cons, hs, Option.bind_eq_bind, Option.bind_some]; exact hf, hr⟩
  obtain ⟨ρf, hf, hr⟩ := hfold prog.body _ _ _ hρ0 hrun
  exact ⟨ρf, heval ρf hf hr⟩

theorem refAnalyze_tight : NoiseTightBGV refAnalyze :=
  fun _ _ _ B _ _ h => ⟨B, h, le_rfl⟩

theorem refAnalyze_nonBGV (E : Trace.Budget) (prog : Program) (hk : P.src.kind ≠ .bgv) :
    refAnalyze P E prog = none := by
  rcases h : refAnalyze P E prog with _ | B
  · rfl
  · exact absurd (refAnalyze_some h).1 hk

end Main

end NoiseAux

/-! ### The pins -/

open NoiseAux

/-- **Headline 2 (H6, BGV): soundness.** -/
theorem analyze_sound : NoiseSoundBGV FHE.Holes.analyze := refAnalyze_sound

/-- The analyzer is the reference analysis, so it is never worse than it. -/
theorem analyze_tight : NoiseTightBGV FHE.Holes.analyze := refAnalyze_tight

theorem analyze_addMul_eq :
    FHE.Holes.analyze .exampleBGV31 noBudget addMulProg = some (2 ^ 57) := by
  decide +kernel

theorem analyze_accepts_addMul : NoiseAcceptsAddMul FHE.Holes.analyze :=
  ⟨2 ^ 57, analyze_addMul_eq, le_rfl⟩

/-- **Scope.** Nothing outside BGV is accepted. -/
theorem analyze_rejects_nonBGV : NoiseRejectsNonBGV FHE.Holes.analyze :=
  fun _ E prog hk => refAnalyze_nonBGV E prog hk

/-- The reference analyzer rejects every program with an ill-formed input declaration. -/
theorem refAnalyze_badDecl (P : FullParams) (E : Trace.Budget) (prog : Source.Program) (d : Decl)
    (hd : d ∈ prog.inputs)
    (h : d.parts = 0 ∨ d.level = 0 ∨ P.src.qs.length < d.level ∨ d.key % 2 = 0 ∨
      2 * P.src.N ≤ d.key) :
    refAnalyze P E prog = none := by
  rcases h' : refAnalyze P E prog with _ | B
  · rfl
  · have hall := (refAnalyze_some h').2.1
    have hok := List.all_eq_true.mp hall d hd
    simp only [Decl.ok, decide_eq_true_eq] at hok
    omega
end Validation.Headline
