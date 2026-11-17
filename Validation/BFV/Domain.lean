import Challenge.BFV.Domain
import Validation.BFV.Sound
import Validation.BFV.Textbook
import Validation.BFV.KeySwitch
import Validation.BFV.Params
import Validation.Budget.RunExists

/-!
# Validation.BFV.Domain — the domain of the certified BFV budget

Proofs of the pins of `Challenge/BFV/Domain.lean`:

* the remaining textbook pins (`sub`, `subPlain`, `square`, `mulConst`, `copy`, `automorph`);
* `refAnalyzeBFV_rejects_unrelinearized`: the analysis of `pre ++ i :: post` reaches `i` with the
  environment `foldlM step` computes, where `domainOK` fails;
* `certified_run_exists`: induction over the body with the invariant "every variable defined in
  the message environment holds, in the ciphertext environment, a ciphertext with the recorded
  number of components, at a level inside the chain" (`Validation.Budget.RunAux.Shape`,
  `Levels`, shared with BGV). Acceptance gives, at every step, that `Source.step` succeeds and
  that `domainOK` holds; each step is then the textbook one of its pin. The gadget keys of a key
  switch are the noiseless ones (`Validation.Budget.RunAux.gadgetKeys_exist`).

`run_exists` is stated for any budget that dominates the certified one.
-/

namespace Validation.BFV
open Spec NPoly Scheme Source Correct Challenge.BFV
open Spec.TraceBFV (Bnd)
open Validation.Ring Validation.Scheme Validation.Source
open SoundAux
open Validation.Budget.RunAux (Shape Levels levels_step gadgetKeys_exist)

/-! ### The textbook pins -/

section Pins
variable (P : FullParams)

theorem stepOK_sub_padded (E : TraceBFV.Budget) (s : IntPoly P.src.N) (ρ ρ' : Env P.src)
    (σ : Trace.CtEnv P) (d a b : Var) (x y : Val P.src) (ca cb : List (IntPoly P.src.N))
    (hstep : step P.src ρ (.sub d a b) = some ρ') (hx : ρ a = some x) (hy : ρ b = some y)
    (ha : σ a = some ca) (hb : σ b = some cb)
    (hla : ca.length = x.parts) (hlb : cb.length = y.parts) :
    TraceBFV.StepOK P E s ρ ρ' σ (σ.set d (Challenge.Source.padZip (· - ·) ca cb))
      (.sub d a b) := by
  simp only [step, hx, hy, Option.bind_eq_bind, Option.bind_some, Option.pure_def] at hstep
  obtain ⟨⟨-, hkey⟩, h2⟩ := Validation.Trace.guard_bind_eq_some hstep
  obtain ⟨m, -, h3⟩ := Option.bind_eq_some_iff.mp h2
  cases h3
  refine ⟨_, _, set_self _ _ _, ?_, rfl, ?_⟩
  · simp [length_padZip, hla, hlb]
  · refine ⟨x, y, ca, cb, hx, hy, ha, hb, ?_⟩
    dsimp only
    rw [← hkey]
    unfold Trace.phaseAt
    rw [phase_padZip_sub]

theorem bfvSubPlain_def {N : ℕ} (t Q : ℕ) (c : List (IntPoly N)) (p : IntPoly N) :
    bfvSubPlain t Q c p = Challenge.Source.padZip (· - ·) c
      [@HSMul.hSMul ℤ (IntPoly N) (IntPoly N) (@instHSMul _ _ NPoly.instSMul)
        ((Q / t : ℕ) : ℤ) p] := rfl

theorem stepOK_subPlain_textbook (E : TraceBFV.Budget) (s : IntPoly P.src.N) (ρ ρ' : Env P.src)
    (σ : Trace.CtEnv P) (d a p : Var) (x y : Val P.src) (ca : List (IntPoly P.src.N))
    (c : IntPoly P.src.N)
    (hstep : step P.src ρ (.subPlain d a p) = some ρ') (hx : ρ a = some x) (hy : ρ p = some y)
    (ha : σ a = some ca) (hp : σ p = some [c]) (hla : ca.length = x.parts) :
    TraceBFV.StepOK P E s ρ ρ' σ
      (σ.set d (bfvSubPlain P.src.t (P.src.modulus x.level) ca c)) (.subPlain d a p) := by
  simp only [step, hx, hy, Option.bind_eq_bind, Option.bind_some, Option.pure_def] at hstep
  obtain ⟨⟨hy1, -⟩, h2⟩ := Validation.Trace.guard_bind_eq_some hstep
  obtain ⟨m, -, h3⟩ := Option.bind_eq_some_iff.mp h2
  cases h3
  refine ⟨_, _, set_self _ _ _, ?_, rfl, ?_⟩
  · simp [bfvSubPlain_def, length_padZip, hla, hy1]
  · refine ⟨x, y, ca, [c], 0, hx, hy, ha, hp, ?_, ?_⟩
    · rw [normInf_zero]; exact Nat.zero_le _
    dsimp only
    rw [Validation.Trace.phaseAt_singleton]
    unfold Trace.phaseAt
    rw [bfvSubPlain_def]
    rw [phase_padZip_sub, List.map_cons, List.map_nil, phase_singleton, ofInt_zero]
    have hsm : ofInt (P.src.modulus x.level)
        (@HSMul.hSMul ℤ (IntPoly P.src.N) (IntPoly P.src.N) (@instHSMul _ _ NPoly.instSMul)
          ((P.src.modulus x.level / P.src.t : ℕ) : ℤ) c) =
        ((P.src.modulus x.level / P.src.t : ℕ) : ZMod (P.src.modulus x.level)) •
          ofInt (P.src.modulus x.level) c := by
      ext i
      show (((((P.src.modulus x.level / P.src.t : ℕ) : ℤ) * c.coeff i : ℤ)) :
        ZMod (P.src.modulus x.level)) = _ * ((c.coeff i : ℤ) : ZMod (P.src.modulus x.level))
      rw [Int.cast_mul, Int.cast_natCast]
    rw [hsm]
    apply eq_of_neZero; intro; ring

theorem stepOK_square_textbook (hP : SchemeParamsOK P) (E : TraceBFV.Budget)
    (hL : BudgetBFV.mulLift P ≤ E.mulLift) (hR : BudgetBFV.mulRound P ≤ E.mulRound)
    (s : IntPoly P.src.N) (hs : SecretOK P.secretBound s) (ρ ρ' : Env P.src)
    (σ : Trace.CtEnv P) (d a : Var) (x : Val P.src) (ca : List (IntPoly P.src.N))
    (hstep : step P.src ρ (.square d a) = some ρ') (hx : ρ a = some x)
    (ha : σ a = some ca) (hla : ca.length = 2) (h2x : x.parts = 2) :
    TraceBFV.StepOK P E s ρ ρ' σ
      (σ.set d (bfvMul P.src.t (P.src.modulus x.level) ca ca)) (.square d a) := by
  simp only [step, hx, Option.bind_eq_bind, Option.bind_some, Option.pure_def] at hstep
  obtain ⟨-, h2⟩ := Validation.Trace.guard_bind_eq_some hstep
  obtain ⟨m, -, h3⟩ := Option.bind_eq_some_iff.mp h2
  cases h3
  obtain ⟨a0, a1, rfl⟩ := List.length_eq_two.mp hla
  have hN : NeZero P.src.N := ⟨by obtain ⟨k, hk⟩ := hP.N_pow2; rw [hk]; positivity⟩
  have hQ : 0 < P.src.modulus x.level := modulus_pos' P hP _
  have ht : bfvMul P.src.t (P.src.modulus x.level) [a0, a1] [a0, a1] =
      [scaleRound P.src.t (P.src.modulus x.level)
          (centered (ofInt (P.src.modulus x.level) a0) *
            centered (ofInt (P.src.modulus x.level) a0)),
       scaleRound P.src.t (P.src.modulus x.level)
          (centered (ofInt (P.src.modulus x.level) a0) *
              centered (ofInt (P.src.modulus x.level) a1) +
            centered (ofInt (P.src.modulus x.level) a1) *
              centered (ofInt (P.src.modulus x.level) a0)),
       scaleRound P.src.t (P.src.modulus x.level)
          (centered (ofInt (P.src.modulus x.level) a1) *
            centered (ofInt (P.src.modulus x.level) a1))] := rfl
  rw [ht]
  refine ⟨_, _, set_self _ _ _, ?_, rfl, ?_⟩
  · simp [h2x]
  refine ⟨x, [a0, a1], ?_⟩
  dsimp only
  unfold Trace.phaseAt
  have hS : (∑ j, |(automorph x.key s).coeff j|) ≤ (P.src.N : ℤ) * (P.secretBound : ℤ) :=
    (sum_abs_automorph_le _ _).trans (sum_abs_le s _ ((normInf_le_iff _ _).mp hs))
  generalize automorph x.key s = sk at hS ⊢
  generalize P.src.modulus x.level = Q at hQ ⊢
  obtain ⟨ka, hka, hΨa⟩ := lift_core Q hQ sk (centered (ofInt Q a0)) (centered (ofInt Q a1))
    (centered (phase (ofInt Q sk) ([a0, a1].map (ofInt Q)))) _ hS
    (fun i => two_abs_valMinAbs_le hQ _) (fun i => two_abs_valMinAbs_le hQ _)
    (fun i => two_abs_valMinAbs_le hQ _)
    (by simp only [ofInt_add, ofInt_mul, ofInt_centered, phase_map_ofInt_two])
  obtain ⟨D, hD, hXD⟩ := mul_core P.src.t Q sk
    (centered (ofInt Q a0) + sk * centered (ofInt Q a1))
    (centered (ofInt Q a0) + sk * centered (ofInt Q a1))
    (scaleRound P.src.t Q (centered (ofInt Q a0) * centered (ofInt Q a0)))
    (scaleRound P.src.t Q (centered (ofInt Q a0) * centered (ofInt Q a1) +
      centered (ofInt Q a1) * centered (ofInt Q a0)))
    (scaleRound P.src.t Q (centered (ofInt Q a1) * centered (ofInt Q a1)))
    _ _ _ _ hS (by ring)
    (fun i => two_abs_roundDiv_sub_le _ _ hQ) (fun i => two_abs_roundDiv_sub_le _ _ hQ)
    (fun i => two_abs_roundDiv_sub_le _ _ hQ)
  refine ⟨ka,
    scaleRound P.src.t Q (centered (ofInt Q a0) * centered (ofInt Q a0)) +
      sk * scaleRound P.src.t Q (centered (ofInt Q a0) * centered (ofInt Q a1) +
        centered (ofInt Q a1) * centered (ofInt Q a0)) +
      (sk * sk) * scaleRound P.src.t Q (centered (ofInt Q a1) * centered (ofInt Q a1)),
    D, hx, ha, ?_, ?_, ?_, ?_⟩
  · rw [normInf_le_iff]
    intro i
    have h' : 2 * |ka.coeff i| ≤ 2 + ((P.src.N * P.secretBound : ℕ) : ℤ) := by
      push_cast; exact hka i
    unfold BudgetBFV.mulLift at hL
    generalize P.src.N * P.secretBound = m at h' hL
    generalize |ka.coeff i| = z at h'
    omega
  · have hle : normInf D ≤ Q * E.mulRound / 2 := by
      rw [normInf_le_iff]
      intro i
      have h' : 2 * |D.coeff i| ≤ ((Q * BudgetBFV.mulRound P : ℕ) : ℤ) := by
        unfold BudgetBFV.mulRound; push_cast; exact hD i
      have h'' : Q * BudgetBFV.mulRound P ≤ Q * E.mulRound := Nat.mul_le_mul_left _ hR
      generalize Q * BudgetBFV.mulRound P = u at h' h''
      generalize Q * E.mulRound = w at h'' ⊢
      generalize |D.coeff i| = z at h'
      omega
    omega
  · rw [specSMul_eq_intCast_mul, specSMul_eq_intCast_mul, specSMul_eq_intCast_mul, ← hΨa]
    exact hXD
  · simp only [List.map_cons, List.map_nil, phase_three', ofInt_add, ofInt_mul]

/-- The phase of a ciphertext whose components are multiplied by an integer. -/
theorem phase_map_mulConst {N q : ℕ} (s : Poly q N) (c : ℤ) : ∀ a : List (IntPoly N),
    phase s ((a.map (bfvMulConst c)).map (ofInt q)) = (c : ZMod q) • phase s (a.map (ofInt q))
  | [] => by
    apply eq_of_neZero; intro
    simp only [List.map_nil, phase_nil, smul_eq_const_mul, mul_zero]
  | x :: a => by
    apply eq_of_neZero; intro
    have hx : ofInt q (bfvMulConst c x) = const (c : ZMod q) * ofInt q x := by
      show ofInt q (⟨fun i => c * x.coeff i⟩ : IntPoly N) = _
      rw [scale_eq_const_mul, ofInt_mul, ofInt_const]
    simp only [List.map_cons, phase_cons, phase_map_mulConst s c a, hx, smul_eq_const_mul]
    ring

theorem stepOK_mulConst_textbook (E : TraceBFV.Budget) (s : IntPoly P.src.N) (ρ ρ' : Env P.src)
    (σ : Trace.CtEnv P) (d a : Var) (c : ℤ) (x : Val P.src) (ca : List (IntPoly P.src.N))
    (hstep : step P.src ρ (.mulConst d a c) = some ρ') (hx : ρ a = some x)
    (ha : σ a = some ca) (hla : ca.length = x.parts) :
    TraceBFV.StepOK P E s ρ ρ' σ (σ.set d (ca.map (bfvMulConst c))) (.mulConst d a c) := by
  simp only [step, hx, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
    Option.some.injEq] at hstep
  subst hstep
  refine ⟨_, _, set_self _ _ _, ?_, rfl, ?_⟩
  · simp [hla]
  · refine ⟨x, ca, hx, ha, ?_⟩
    dsimp only
    unfold Trace.phaseAt
    rw [phase_map_mulConst]

theorem stepOK_copy_textbook (E : TraceBFV.Budget) (s : IntPoly P.src.N) (ρ ρ' : Env P.src)
    (σ : Trace.CtEnv P) (i : Instr) (d a : Var) (x : Val P.src) (ca : List (IntPoly P.src.N))
    (hi : i = .copy d a ∨ i = .toEval d a ∨ i = .toCoeff d a)
    (hstep : step P.src ρ i = some ρ') (hx : ρ a = some x)
    (ha : σ a = some ca) (hla : ca.length = x.parts) :
    TraceBFV.StepOK P E s ρ ρ' σ (σ.set d ca) i := by
  rcases hi with rfl | rfl | rfl
  all_goals
    simp only [step, hx, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
      Option.some.injEq] at hstep
    subst hstep
    exact ⟨_, _, set_self _ _ _, hla, rfl, x, ca, hx, ha, rfl⟩

theorem stepOK_automorph_textbook (E : TraceBFV.Budget) (s : IntPoly P.src.N) (ρ ρ' : Env P.src)
    (σ : Trace.CtEnv P) (d a : Var) (g : ℕ) (x : Val P.src) (ca : List (IntPoly P.src.N))
    (hstep : step P.src ρ (.automorph d a g) = some ρ') (hx : ρ a = some x)
    (ha : σ a = some ca) (hla : ca.length = x.parts) :
    TraceBFV.StepOK P E s ρ ρ' σ (σ.set d (ca.map (automorph g))) (.automorph d a g) := by
  simp only [step, hx, Option.bind_eq_bind, Option.bind_some, Option.pure_def] at hstep
  obtain ⟨hg, h2⟩ := Validation.Trace.guard_bind_eq_some hstep
  cases h2
  refine ⟨_, _, set_self _ _ _, ?_, rfl, ?_⟩
  · simp [hla]
  · refine ⟨x, ca, hx, ha, ?_⟩
    dsimp only
    unfold Trace.phaseAt
    have hmap : (ca.map (automorph g)).map (ofInt (P.src.modulus x.level)) =
        (ca.map (ofInt (P.src.modulus x.level))).map (automorph g) := by
      simp only [List.map_map]
      congr 1; funext c; exact ofInt_automorph _ g c
    rw [hmap, automorph_mod, ← automorph_automorph hg, ofInt_automorph, phase_automorph hg]

end Pins

/-! ### `domainOK`, by cases

Stated here and proved by `rfl` after case analysis, so that no proof below unfolds `domainOK`
with `simp` (which would generate its equation lemmas, in the `Challenge` namespace, in this
module). -/

section Dom
variable {Pr : Params}

theorem dom_mul (ρ : Env Pr) (d a b : Var) : domainOK ρ (.mul d a b) =
    ((ρ a).any (fun x => x.parts == 2) && (ρ b).any (fun y => y.parts == 2)) := by
  have key : ∀ oa ob : Option (Val Pr),
      (match oa, ob with
        | some x, some y => x.parts == 2 && y.parts == 2
        | _, _ => false) =
      (oa.any (fun x => x.parts == 2) && ob.any (fun y => y.parts == 2)) := by
    intro oa ob
    cases oa <;> cases ob <;> first | rfl | exact (Bool.and_false _).symm
  exact key (ρ a) (ρ b)

theorem dom_sq (ρ : Env Pr) (d a : Var) : domainOK ρ (.square d a) =
    (ρ a).any (fun x => x.parts == 2) := by
  have key : ∀ oa : Option (Val Pr),
      (match oa with
        | some x => x.parts == 2
        | none => false) = oa.any (fun x => x.parts == 2) := by
    intro oa; cases oa <;> rfl
  exact key (ρ a)

theorem dom_ms (ρ : Env Pr) (d a : Var) : domainOK ρ (.modSwitch d a) =
    (ρ a).any (fun x => x.parts == 2) := by
  have key : ∀ oa : Option (Val Pr),
      (match oa with
        | some x => x.parts == 2
        | none => false) = oa.any (fun x => x.parts == 2) := by
    intro oa; cases oa <;> rfl
  exact key (ρ a)

end Dom

/-! ### Rejection outside the domain -/

section Reject
variable {P : FullParams}

/-- The analysis of `pre ++ rest` reaches `rest` with the environment `foldlM step` computes. -/
theorem refRun_append_some (E : TraceBFV.Budget) : ∀ (pre rest : List Instr) (ρ : Env P.src)
    (β : Var → Option Bnd) (r : Env P.src × (Var → Option Bnd)),
    refRunBFV P E (pre ++ rest) ρ β = some r →
    ∃ ρ' β', pre.foldlM (step P.src) ρ = some ρ' ∧ refRunBFV P E rest ρ' β' = some r
  | [], rest, ρ, β, r, h => ⟨ρ, β, rfl, h⟩
  | i :: pre, rest, ρ, β, r, h => by
    obtain ⟨ρ1, v, b, h1, -, -, -, h5, -⟩ := refRun_cons_some P E h
    obtain ⟨ρ', β', hf, hr⟩ := refRun_append_some E pre rest ρ1 _ r h5
    refine ⟨ρ', β', ?_, hr⟩
    simp only [List.foldlM_cons, h1, Option.bind_eq_bind, Option.bind_some]
    exact hf

theorem refAnalyzeBFV_rejects_unrelinearized (P : FullParams) (E : TraceBFV.Budget)
    (prog : Source.Program) (pre post : List Instr) (i : Instr) (ρ : Env P.src) (x : Val P.src)
    (hbody : prog.body = pre ++ i :: post)
    (hpre : pre.foldlM (step P.src) (initEnv P.src prog fun _ => .exact 0) = some ρ)
    (hx : x.parts ≠ 2)
    (hi : (∃ d a b, i = .mul d a b ∧ (ρ a = some x ∨ ρ b = some x)) ∨
      (∃ d a, (i = .square d a ∨ i = .modSwitch d a) ∧ ρ a = some x)) :
    refAnalyzeBFV P E prog = none := by
  rcases h : refAnalyzeBFV P E prog with _ | B
  · rfl
  exfalso
  obtain ⟨-, -, ρz, β, hrun, -⟩ := refAnalyze_some h
  rw [hbody] at hrun
  obtain ⟨ρ', β', hf, hr⟩ := refRun_append_some E pre (i :: post) _ _ _ hrun
  rw [hpre] at hf
  cases hf
  obtain ⟨-, -, -, -, -, -, -, -, hdom⟩ := refRun_cons_some P E hr
  rcases hi with ⟨d, a, b, rfl, ha | hb⟩ | ⟨d, a, rfl | rfl, ha⟩
  · rcases hy : ρ b with _ | y
    · simp [dom_mul, ha, hy] at hdom
    · simp [dom_mul, ha, hy, hx] at hdom
  · rcases hy : ρ a with _ | y
    · simp [dom_mul, hb, hy] at hdom
    · simp [dom_mul, hb, hy, hx] at hdom
  · simp [dom_sq, ha, hx] at hdom
  · simp [dom_ms, ha, hx] at hdom

theorem refAnalyzeBFV_rejects_seal_scenarios :
    refAnalyzeBFV sealBFV sealBudget
      { inputs := [⟨"a", 2, 4, 1, 1⟩, ⟨"b", 2, 4, 1, 1⟩],
        body := [.mul "c" "a" "b", .modSwitch "c" "c"], outputs := ["c"] } = none ∧
    refAnalyzeBFV sealBFV sealBudget
      { inputs := [⟨"c", 3, 4, 1, 1⟩], body := [.mul "d" "c" "c"], outputs := ["d"] } = none ∧
    refAnalyzeBFV sealBFV sealBudget
      { inputs := [⟨"c", 3, 4, 1, 1⟩], body := [.square "d" "c"], outputs := ["d"] } = none := by
  decide +kernel

end Reject

/-! ### Every accepted program has a run -/

section Run
variable {P : FullParams}

/-- `domainOK` does not read the messages. -/
theorem domainOK_zenv (ρ : Env P.src) (i : Instr) : domainOK (zenv ρ) i = domainOK ρ i := by
  cases i with
  | mul d a b =>
    rcases hx : ρ a with _ | x <;> rcases hy : ρ b with _ | y <;>
      simp [dom_mul, zenv, zv, hx, hy]
  | square d a | modSwitch d a =>
    rcases hx : ρ a with _ | x <;> simp [dom_sq, dom_ms, zenv, zv, hx]
  | _ => rfl

/-- A step that meets its BFV contract keeps the shapes. -/
theorem shape_step {E : TraceBFV.Budget} {s : IntPoly P.src.N} {ρ ρ' : Env P.src}
    {σ σ' : Trace.CtEnv P} {i : Instr} (h : Shape P ρ σ) (hstep : step P.src ρ i = some ρ')
    (hok : TraceBFV.StepOK P E s ρ ρ' σ σ' i) : Shape P ρ' σ' := by
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

section Step
variable (lay : Budget.KSLayout) (hk : P.src.kind = .bfv) (hP : SchemeParamsOK P)
  (hS : Budget.SpecialOK P)
  (hlay : ∀ ℓ, 1 ≤ ℓ → ℓ ≤ P.src.qs.length → lay.okAt ℓ = true)
  (E : TraceBFV.Budget) (hEk : BudgetBFV.ksBudget P lay ≤ E.keySwitch)
  (hEm : BudgetBFV.msBudget P ≤ E.modSwitch) (hEl : BudgetBFV.mulLift P ≤ E.mulLift)
  (hEr : BudgetBFV.mulRound P ≤ E.mulRound)
  (s : IntPoly P.src.N) (hs : SecretOK P.secretBound s)
include hk hP hS hlay hEk hEm hEl hEr hs

/-- **One step.** Every instruction that `step` accepts and that is in the domain has a textbook
realization meeting its contract, at every budget that dominates the certified one. -/
theorem step_exists {ρ ρ' : Env P.src} {σ : Trace.CtEnv P} (i : Instr)
    (hsh : Shape P ρ σ) (hlv : Levels P ρ) (hstep : step P.src ρ i = some ρ')
    (hdom : domainOK ρ i = true) :
    ∃ σ', TraceBFV.StepOK P E s ρ ρ' σ σ' i := by
  cases i with
  | add d a b =>
    rcases hx : ρ a with _ | x
    · simp [step, hx] at hstep
    rcases hy : ρ b with _ | y
    · simp [step, hx, hy] at hstep
    obtain ⟨ca, ha, hla⟩ := hsh a x hx
    obtain ⟨cb, hb, hlb⟩ := hsh b y hy
    exact ⟨_, stepOK_add_padded P E s ρ ρ' σ d a b x y ca cb hstep hx hy ha hb hla hlb⟩
  | sub d a b =>
    rcases hx : ρ a with _ | x
    · simp [step, hx] at hstep
    rcases hy : ρ b with _ | y
    · simp [step, hx, hy] at hstep
    obtain ⟨ca, ha, hla⟩ := hsh a x hx
    obtain ⟨cb, hb, hlb⟩ := hsh b y hy
    exact ⟨_, stepOK_sub_padded P E s ρ ρ' σ d a b x y ca cb hstep hx hy ha hb hla hlb⟩
  | mul d a b =>
    rcases hx : ρ a with _ | x
    · simp [step, hx] at hstep
    rcases hy : ρ b with _ | y
    · simp [step, hx, hy] at hstep
    obtain ⟨ca, ha, hla⟩ := hsh a x hx
    obtain ⟨cb, hb, hlb⟩ := hsh b y hy
    simp [dom_mul, hx, hy] at hdom
    exact ⟨_, stepOK_mul_textbook P hP E hEl hEr s hs ρ ρ' σ d a b x y ca cb hstep hx hy ha hb
      (hla.trans hdom.1) (hlb.trans hdom.2) hdom.1 hdom.2⟩
  | square d a =>
    rcases hx : ρ a with _ | x
    · simp [step, hx] at hstep
    obtain ⟨ca, ha, hla⟩ := hsh a x hx
    simp [dom_sq, hx] at hdom
    exact ⟨_, stepOK_square_textbook P hP E hEl hEr s hs ρ ρ' σ d a x ca hstep hx ha
      (hla.trans hdom) hdom⟩
  | mulConst d a c =>
    rcases hx : ρ a with _ | x
    · simp [step, hx] at hstep
    obtain ⟨ca, ha, hla⟩ := hsh a x hx
    exact ⟨_, stepOK_mulConst_textbook P E s ρ ρ' σ d a c x ca hstep hx ha hla⟩
  | copy d a =>
    rcases hx : ρ a with _ | x
    · simp [step, hx] at hstep
    obtain ⟨ca, ha, hla⟩ := hsh a x hx
    exact ⟨_, stepOK_copy_textbook P E s ρ ρ' σ _ d a x ca (Or.inl rfl) hstep hx ha hla⟩
  | toEval d a =>
    rcases hx : ρ a with _ | x
    · simp [step, hx] at hstep
    obtain ⟨ca, ha, hla⟩ := hsh a x hx
    exact ⟨_, stepOK_copy_textbook P E s ρ ρ' σ _ d a x ca (Or.inr (Or.inl rfl)) hstep hx ha hla⟩
  | toCoeff d a =>
    rcases hx : ρ a with _ | x
    · simp [step, hx] at hstep
    obtain ⟨ca, ha, hla⟩ := hsh a x hx
    exact ⟨_, stepOK_copy_textbook P E s ρ ρ' σ _ d a x ca (Or.inr (Or.inr rfl)) hstep hx ha hla⟩
  | automorph d a g =>
    rcases hx : ρ a with _ | x
    · simp [step, hx] at hstep
    obtain ⟨ca, ha, hla⟩ := hsh a x hx
    exact ⟨_, stepOK_automorph_textbook P E s ρ ρ' σ d a g x ca hstep hx ha hla⟩
  | addPlain d a p =>
    rcases hx : ρ a with _ | x
    · simp [step, hx] at hstep
    rcases hy : ρ p with _ | y
    · simp [step, hx, hy] at hstep
    obtain ⟨ca, ha, hla⟩ := hsh a x hx
    obtain ⟨cb, hb, hlb⟩ := hsh p y hy
    have hstep' := hstep
    simp only [step, hx, hy, Option.bind_eq_bind, Option.bind_some, Option.pure_def] at hstep'
    obtain ⟨⟨hy1, -⟩, -⟩ := Validation.Trace.guard_bind_eq_some hstep'
    obtain ⟨c, rfl⟩ := List.length_eq_one_iff.mp (hlb.trans hy1)
    exact ⟨_, stepOK_addPlain_textbook P E s ρ ρ' σ d a p x y ca c hstep hx hy ha hb hla⟩
  | subPlain d a p =>
    rcases hx : ρ a with _ | x
    · simp [step, hx] at hstep
    rcases hy : ρ p with _ | y
    · simp [step, hx, hy] at hstep
    obtain ⟨ca, ha, hla⟩ := hsh a x hx
    obtain ⟨cb, hb, hlb⟩ := hsh p y hy
    have hstep' := hstep
    simp only [step, hx, hy, Option.bind_eq_bind, Option.bind_some, Option.pure_def] at hstep'
    obtain ⟨⟨hy1, -⟩, -⟩ := Validation.Trace.guard_bind_eq_some hstep'
    obtain ⟨c, rfl⟩ := List.length_eq_one_iff.mp (hlb.trans hy1)
    exact ⟨_, stepOK_subPlain_textbook P E s ρ ρ' σ d a p x y ca c hstep hx hy ha hb hla⟩
  | mulPlain d a p =>
    rcases hx : ρ a with _ | x
    · simp [step, hx] at hstep
    rcases hy : ρ p with _ | y
    · simp [step, hx, hy] at hstep
    obtain ⟨ca, ha, hla⟩ := hsh a x hx
    obtain ⟨cb, hb, hlb⟩ := hsh p y hy
    have hstep' := hstep
    simp only [step, hx, hy, Option.bind_eq_bind, Option.bind_some, Option.pure_def] at hstep'
    obtain ⟨⟨hy1, -, -⟩, -⟩ := Validation.Trace.guard_bind_eq_some hstep'
    obtain ⟨c, rfl⟩ := List.length_eq_one_iff.mp (hlb.trans hy1)
    exact ⟨_, stepOK_mulPlain_textbook P E s ρ ρ' σ d a p x y ca c hstep hx hy ha hb hla⟩
  | modSwitch d a =>
    rcases hx : ρ a with _ | x
    · simp [step, hx] at hstep
    obtain ⟨ca, ha, hla⟩ := hsh a x hx
    simp [dom_ms, hx] at hdom
    exact ⟨_, stepOK_modSwitch_textbook P hP E hEm s hs ρ ρ' σ d a x ca hstep hx ha
      (hlv a x hx).2 hdom (hla.trans hdom)⟩
  | relin d a =>
    rcases hx : ρ a with _ | x
    · simp [step, hx] at hstep
    obtain ⟨ca, ha, hla⟩ := hsh a x hx
    obtain ⟨h1, hL⟩ := hlv a x hx
    obtain ⟨f, hf⟩ := relin_realizable P lay hP hS x.level hL (hlay _ h1 hL)
    obtain ⟨keys, hkeys⟩ := gadgetKeys_exist P lay x.level .square s
    exact ⟨_, hf E ((ksBoundAt_le_ksBudget P lay x.level h1 hL).trans hEk) s hs keys hkeys
      ρ ρ' σ d a x ca hstep hx ha rfl hla⟩
  | keySwitch d a =>
    rcases hx : ρ a with _ | x
    · simp [step, hx] at hstep
    obtain ⟨ca, ha, hla⟩ := hsh a x hx
    obtain ⟨h1, hL⟩ := hlv a x hx
    obtain ⟨f, hf⟩ := keySwitch_realizable P lay hP hS x.level hL (hlay _ h1 hL)
    obtain ⟨keys, hkeys⟩ := gadgetKeys_exist P lay x.level (.galois x.key) s
    exact ⟨_, hf E ((ksBoundAt_le_ksBudget P lay x.level h1 hL).trans hEk) s hs
      ρ ρ' σ d a x ca hstep hx ha rfl hla keys hkeys⟩
  | dropLimbs d a k =>
    rcases hx : ρ a with _ | x
    · simp [step, hx] at hstep
    · simp [step, hx, hk] at hstep

/-- **The run.** From shapes, levels and exact messages, every body the analysis accepts (at any
budget `E'`: only `Source.step` and `domainOK` are used) has a run. -/
theorem run_exists (E' : TraceBFV.Budget) : ∀ (body : List Instr) (ρ : Env P.src)
    (σ : Trace.CtEnv P) (β : Var → Option Bnd) (r : Env P.src × (Var → Option Bnd)),
    AllExact ρ → Shape P ρ σ → Levels P ρ → refRunBFV P E' body (zenv ρ) β = some r →
    ∃ σf, TraceBFV.Run P E s body ρ σ σf
  | [], _, σ, _, _, _, _, _, _ => ⟨σ, rfl⟩
  | i :: is, ρ, σ, β, r, hρ, hsh, hlv, h => by
    obtain ⟨ρz', vz, b, h1, -, -, -, h5, hdom⟩ := refRun_cons_some P E' h
    obtain ⟨hz, hex⟩ := step_zenv hk hρ i
    rw [hz] at h1
    obtain ⟨ρ', hstep, rfl⟩ := Option.map_eq_some_iff.mp h1
    rw [domainOK_zenv] at hdom
    obtain ⟨σ', hok⟩ := step_exists lay hk hP hS hlay E hEk hEm hEl hEr s hs i hsh hlv hstep hdom
    obtain ⟨σf, hrun⟩ := run_exists E' is ρ' σ' _ r (hex ρ' hstep) (shape_step hsh hstep hok)
      (levels_step hlv hstep) h5
    exact ⟨σf, ρ', σ', hstep, hok, hrun⟩

end Step

/-- Run existence at any budget that dominates the certified one, for a program accepted at any
budget. -/
theorem run_exists_of_accepts (P : FullParams) (lay : Budget.KSLayout) (prog : Source.Program)
    (B : ℕ) (hP : SchemeParamsOK P) (hS : Budget.SpecialOK P)
    (hlay : ∀ ℓ, 1 ≤ ℓ → ℓ ≤ P.src.qs.length → lay.okAt ℓ = true)
    (E E' : TraceBFV.Budget) (hEk : BudgetBFV.ksBudget P lay ≤ E.keySwitch)
    (hEm : BudgetBFV.msBudget P ≤ E.modSwitch) (hEl : BudgetBFV.mulLift P ≤ E.mulLift)
    (hEr : BudgetBFV.mulRound P ≤ E.mulRound)
    (h : refAnalyzeBFV P E' prog = some B)
    (s : IntPoly P.src.N) (hs : SecretOK P.secretBound s)
    (msgs : Var → Msg P.src.t P.src.N) (cts : Var → List (IntPoly P.src.N))
    (hin : TraceBFV.InputsOK P s prog msgs cts) :
    ∃ σ, TraceBFV.Run P E s prog.body (initEnv P.src prog msgs) (Trace.initCt P prog cts) σ := by
  obtain ⟨hk, hdecl, ρz, βf, hrun, -⟩ := refAnalyze_some h
  have hfind : ∀ x d, prog.inputs.find? (·.name = x) = some d →
      (∃ m, msgs x = .exact m) ∧ (cts x).length = d.parts := by
    intro x d hd
    have hn : d.name = x := by simpa using List.find?_some hd
    have he := hin x d hd
    rw [← hn]
    by_cases hp : d.parts = 1
    · simp only [hp, ↓reduceIte] at he
      obtain ⟨m, hm, -⟩ := plain_elim he
      exact ⟨⟨m, hm⟩, by rw [hn]; exact he.1⟩
    · simp only [hp, ↓reduceIte] at he
      obtain ⟨m, hm, hl, -⟩ := enc_elim hk he
      exact ⟨⟨m, hm⟩, by rw [hn]; exact hl⟩
  have hρ0 : AllExact (initEnv P.src prog msgs) := by
    intro x v hv
    simp only [initEnv, Option.map_eq_some_iff] at hv
    obtain ⟨d, hd, rfl⟩ := hv
    exact (hfind x d hd).1
  have hz0 : zenv (initEnv P.src prog msgs) = initEnv P.src prog fun _ => .exact 0 := by
    funext x; simp only [zenv, initEnv, Option.map_map]; rfl
  rw [← hz0] at hrun
  refine run_exists lay hk hP hS hlay E hEk hEm hEl hEr s hs E' prog.body _ _ _ _ hρ0 ?_ ?_ hrun
  · intro x v hv
    simp only [initEnv, Option.map_eq_some_iff] at hv
    obtain ⟨d, hd, rfl⟩ := hv
    exact ⟨cts x, by simp [Trace.initCt, hd], (hfind x d hd).2⟩
  · intro x v hv
    simp only [initEnv, Option.map_eq_some_iff] at hv
    obtain ⟨d, hd, rfl⟩ := hv
    have hok := List.all_eq_true.mp hdecl d (List.mem_of_find?_eq_some hd)
    simp only [Decl.ok, decide_eq_true_eq] at hok
    exact ⟨hok.2.1, hok.2.2.1⟩

theorem certified_run_exists (P : FullParams) (lay : Budget.KSLayout) (prog : Source.Program)
    (B : ℕ) (hP : SchemeParamsOK P) (hS : Budget.SpecialOK P)
    (hlay : ∀ ℓ, 1 ≤ ℓ → ℓ ≤ P.src.qs.length → lay.okAt ℓ = true)
    (h : refAnalyzeBFV P (BudgetBFV.certified P lay) prog = some B)
    (s : IntPoly P.src.N) (hs : SecretOK P.secretBound s)
    (msgs : Var → Msg P.src.t P.src.N) (cts : Var → List (IntPoly P.src.N))
    (hin : TraceBFV.InputsOK P s prog msgs cts) :
    ∃ σ, TraceBFV.Run P (BudgetBFV.certified P lay) s prog.body (initEnv P.src prog msgs)
      (Trace.initCt P prog cts) σ :=
  run_exists_of_accepts P lay prog B hP hS hlay _ _ le_rfl le_rfl le_rfl le_rfl h s hs msgs cts
    hin

theorem refAnalyzeBFV_accepts_sealMS_eq :
    refAnalyzeBFV sealBFV sealBudget sealProgMS = some 84532264266092636134471690 := by
  decide +kernel

theorem refAnalyzeBFV_accepts_sealMS :
    ∃ B, refAnalyzeBFV sealBFV sealBudget sealProgMS = some B ∧ B ≤ 2 ^ 87 :=
  ⟨_, refAnalyzeBFV_accepts_sealMS_eq, by norm_num⟩

theorem sealProgMS_run_exists (s : IntPoly sealBFV.src.N) (hs : SecretOK sealBFV.secretBound s)
    (msgs : Var → Msg sealBFV.src.t sealBFV.src.N) (cts : Var → List (IntPoly sealBFV.src.N))
    (hin : TraceBFV.InputsOK sealBFV s sealProgMS msgs cts) :
    ∃ σ, TraceBFV.Run sealBFV sealBudget s sealProgMS.body
      (initEnv sealBFV.src sealProgMS msgs) (Trace.initCt sealBFV sealProgMS cts) σ :=
  certified_run_exists sealBFV (Budget.uniformLayout 1) sealProgMS _ sealBFV_ok
    (Validation.Budget.specialOK?_sound _ (by decide +kernel))
    (fun ℓ _ _ => Validation.Budget.uniformLayout_ok 1 false ℓ)
    refAnalyzeBFV_accepts_sealMS_eq s hs msgs cts hin

end Run

example := (@stepOK_sub_padded : type_of% @Challenge.BFV.stepOK_sub_padded)
example := (@stepOK_subPlain_textbook : type_of% @Challenge.BFV.stepOK_subPlain_textbook)
example := (@stepOK_square_textbook : type_of% @Challenge.BFV.stepOK_square_textbook)
example := (@stepOK_mulConst_textbook : type_of% @Challenge.BFV.stepOK_mulConst_textbook)
example := (@stepOK_copy_textbook : type_of% @Challenge.BFV.stepOK_copy_textbook)
example := (@stepOK_automorph_textbook : type_of% @Challenge.BFV.stepOK_automorph_textbook)
example := (@refAnalyzeBFV_rejects_unrelinearized :
  type_of% @Challenge.BFV.refAnalyzeBFV_rejects_unrelinearized)
example := (@refAnalyzeBFV_rejects_seal_scenarios :
  type_of% @Challenge.BFV.refAnalyzeBFV_rejects_seal_scenarios)
example := (@certified_run_exists : type_of% @Challenge.BFV.certified_run_exists)
example := (@refAnalyzeBFV_accepts_sealMS : type_of% @Challenge.BFV.refAnalyzeBFV_accepts_sealMS)
example := (@sealProgMS_run_exists : type_of% @Challenge.BFV.sealProgMS_run_exists)

end Validation.BFV
