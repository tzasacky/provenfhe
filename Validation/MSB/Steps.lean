import Validation.MSB.Basic
import Validation.Trace

/-!
# Validation.MSB.Steps — an MSB step is, read through `t`, an LSB step

Proofs of `Challenge.MSB.stepOK_toLSB` and `run_toLSB` (item 3).
-/

namespace Validation.MSB
open Spec NPoly Scheme Source Spec.MSB
open Validation.Ring Validation.Scheme

section Poly
variable {N Q : ℕ}

theorem smul_add' (c : ZMod Q) (a b : Poly Q N) : c • (a + b) = c • a + c • b := by
  ext i; show c * (a.coeff i + b.coeff i) = c * a.coeff i + c * b.coeff i; ring

theorem smul_sub' (c : ZMod Q) (a b : Poly Q N) : c • (a - b) = c • a - c • b := by
  ext i; show c * (a.coeff i - b.coeff i) = c * a.coeff i - c * b.coeff i; ring

theorem smul_smul_comm' (c d : ZMod Q) (a : Poly Q N) : c • (d • a) = d • (c • a) := by
  ext i; show c * (d * a.coeff i) = d * (c * a.coeff i); ring

theorem smul_mul_smul' (c : ZMod Q) (a b : Poly Q N) :
    c • (c • (a * b)) = (c • a) * (c • b) := by
  apply eq_of_neZero; intro
  simp only [smul_eq_const_mul]; ring

theorem automorph_smul' (g : ℕ) (c : ZMod Q) (a : Poly Q N) :
    automorph g (c • a) = c • automorph g a := by
  ext k
  show (automorph g (c • a)).coeff k = c * (automorph g a).coeff k
  rw [coeff_automorph', coeff_automorph', Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  show (if _ then c * a.coeff i else if _ then -(c * a.coeff i) else 0) = _
  split_ifs <;> ring

theorem ofInt_smul_int (t : ℕ) (e : IntPoly N) :
    ofInt Q ((t : ℤ) • e) = (t : ZMod Q) • ofInt Q e := ofInt_smul Q t e

theorem normInf_smul_le (t : ℕ) (e : IntPoly N) : normInf ((t : ℤ) • e) ≤ t * normInf e := by
  rw [normInf_le_iff]
  intro i
  show |(t : ℤ) * e.coeff i| ≤ ((t * normInf e : ℕ) : ℤ)
  rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℤ) ≤ t)]
  push_cast
  exact mul_le_mul_of_nonneg_left (abs_coeff_le_normInf e i) (by positivity)

end Poly

variable (P : FullParams)

theorem toLSBEnv_set (σ : Trace.CtEnv P) (d : Var) (ct : List (IntPoly P.src.N)) :
    toLSBEnv P (σ.set d ct) = (toLSBEnv P σ).set d (toLSB P.src.t ct) := by
  funext y
  unfold toLSBEnv Trace.CtEnv.set
  by_cases h : y = d <;> simp [h]

theorem toLSBEnv_apply (σ : Trace.CtEnv P) (a : Var) (ca : List (IntPoly P.src.N))
    (h : σ a = some ca) : toLSBEnv P σ a = some (toLSB P.src.t ca) := by
  simp [toLSBEnv, h]

theorem length_toLSB {N : ℕ} (t : ℕ) (ct : List (IntPoly N)) : (toLSB t ct).length = ct.length := by
  simp [toLSB]

/-- What `step` gives for a modulus switch. -/
theorem step_modSwitch {ρ ρ' : Env P.src} {d a : Var} {x v : Val P.src}
    (hstep : step P.src ρ (.modSwitch d a) = some ρ') (hx : ρ a = some x)
    (hv : ρ' d = some v) :
    v.level = x.level - 1 ∧ 2 ≤ x.level ∧ x.level ≤ P.src.qs.length := by
  simp only [step, hx, Option.bind_eq_bind, Option.bind_some, Option.pure_def] at hstep
  obtain ⟨h2, h3⟩ := Validation.Trace.guard_bind_eq_some hstep
  cases hq : P.src.qs[x.level - 1]? with
  | none => rw [hq] at h3; simp at h3
  | some q =>
    rw [hq, Option.bind_some] at h3
    cases h3
    have hlt : x.level - 1 < P.src.qs.length := by
      by_contra hc; rw [List.getElem?_eq_none (by omega)] at hq; simp at hq
    simp only [Env.set, ite_true, Option.some.injEq] at hv
    subst hv
    exact ⟨rfl, h2, by omega⟩

/-- What `step` gives for dropping limbs. -/
theorem step_dropLimbs {ρ ρ' : Env P.src} {d a : Var} {k : ℕ} {x v : Val P.src}
    (hstep : step P.src ρ (.dropLimbs d a k) = some ρ') (hx : ρ a = some x)
    (hv : ρ' d = some v) : v.level = x.level - k := by
  simp only [step, hx, Option.bind_eq_bind, Option.bind_some, Option.pure_def] at hstep
  obtain ⟨-, h3⟩ := Validation.Trace.guard_bind_eq_some hstep
  cases h3
  simp only [Env.set, ite_true, Option.some.injEq] at hv
  subst hv; rfl

theorem stepOK_toLSB (E : Trace.Budget) (s : IntPoly P.src.N)
    (ρ ρ' : Env P.src) (σ σ' : Trace.CtEnv P) (i : Instr) (hstep : step P.src ρ i = some ρ')
    (h : MSB.StepOK P E s ρ ρ' σ σ' i) :
    Trace.StepOK P E s ρ ρ' (toLSBEnv P σ) (toLSBEnv P σ') i := by
  obtain ⟨v, ct, hv, hlen, hσ', hc⟩ := h
  refine ⟨v, toLSB P.src.t ct, hv, by rw [length_toLSB, hlen], by rw [hσ', toLSBEnv_set], ?_⟩
  have hphase := fun Q key ct => phaseAt_toLSB P Q key s ct
  cases i with
  | add _ a b | addPlain _ a b =>
    obtain ⟨x, y, ca, cb, hx, hy, ha, hb, he⟩ := hc
    refine ⟨x, y, _, _, hx, hy, toLSBEnv_apply P σ a ca ha, toLSBEnv_apply P σ b cb hb, ?_⟩
    try dsimp only at he ⊢
    rw [hphase, hphase, hphase, he, smul_add']
  | sub _ a b | subPlain _ a b =>
    obtain ⟨x, y, ca, cb, hx, hy, ha, hb, he⟩ := hc
    refine ⟨x, y, _, _, hx, hy, toLSBEnv_apply P σ a ca ha, toLSBEnv_apply P σ b cb hb, ?_⟩
    try dsimp only at he ⊢
    rw [hphase, hphase, hphase, he, smul_sub']
  | mul _ a b | mulPlain _ a b =>
    obtain ⟨x, y, ca, cb, hx, hy, ha, hb, he⟩ := hc
    refine ⟨x, y, _, _, hx, hy, toLSBEnv_apply P σ a ca ha, toLSBEnv_apply P σ b cb hb, ?_⟩
    try dsimp only at he ⊢
    rw [hphase, hphase, hphase, he, smul_mul_smul']
  | square _ a =>
    obtain ⟨x, ca, hx, ha, he⟩ := hc
    refine ⟨x, _, hx, toLSBEnv_apply P σ a ca ha, ?_⟩
    try dsimp only at he ⊢
    rw [hphase, hphase, he, smul_mul_smul']
  | mulConst _ a c =>
    obtain ⟨x, ca, hx, ha, he⟩ := hc
    refine ⟨x, _, hx, toLSBEnv_apply P σ a ca ha, ?_⟩
    try dsimp only at he ⊢
    rw [hphase, hphase, he, smul_smul_comm']
  | copy _ a | toEval _ a | toCoeff _ a =>
    obtain ⟨x, ca, hx, ha, he⟩ := hc
    refine ⟨x, _, hx, toLSBEnv_apply P σ a ca ha, ?_⟩
    try dsimp only at he ⊢
    rw [hphase, hphase, he]
  | automorph _ a g =>
    obtain ⟨x, ca, hx, ha, he⟩ := hc
    refine ⟨x, _, hx, toLSBEnv_apply P σ a ca ha, ?_⟩
    try dsimp only at he ⊢
    rw [hphase, hphase, he, automorph_smul']
  | relin _ a | keySwitch _ a =>
    obtain ⟨x, ca, e, hx, ha, hb, he⟩ := hc
    refine ⟨x, _, (P.src.t : ℤ) • e, hx, toLSBEnv_apply P σ a ca ha,
      (normInf_smul_le _ e).trans hb, fun j => ⟨e.coeff j, rfl⟩, ?_⟩
    try dsimp only at he ⊢
    rw [hphase, hphase, he, smul_add', ofInt_smul_int]
  | dropLimbs d a k =>
    obtain ⟨x, ca, hx, ha, he⟩ := hc
    refine ⟨x, _, hx, toLSBEnv_apply P σ a ca ha, ?_⟩
    try dsimp only at he ⊢
    rw [hphase, he, hphase, ← ofInt_smul_int]
    have hl := step_dropLimbs P hstep hx hv
    apply Validation.Source.ofInt_eq_of_dvd (Q := P.src.modulus x.level)
    · rw [hl]; exact Validation.Source.modulus_sub_dvd _ _ _
    · rw [ofInt_smul_int, ofInt_centered, ofInt_centered]
  | modSwitch d a =>
    obtain ⟨x, ca, δ, q, hx, ha, hq, hc⟩ := hc
    try dsimp only at hc ⊢
    obtain ⟨hb, hdvd, he⟩ := hc
    obtain ⟨hl, h2, hL⟩ := step_modSwitch P hstep hx hv
    have hqq : P.src.qs[x.level - 1]! = q := by simp [hq]
    have hM : P.src.modulus x.level = P.src.modulus v.level * q := by
      rw [hl, ← hqq]; exact Validation.Source.modulus_pred _ _ (by omega) hL
    refine ⟨x, _, (P.src.t : ℤ) • δ, q, hx, toLSBEnv_apply P σ a ca ha, hq, ?_⟩
    try dsimp only
    set M := P.src.modulus x.level
    set Q := P.src.modulus v.level
    set φa := Trace.phaseAt P M x.key s ca
    set Ψ := centered φa
    have hΦ : ∀ j, ∃ w : ℤ, (centered ((P.src.t : ZMod M) • φa)).coeff j =
        (P.src.t : ℤ) * Ψ.coeff j + M * w := by
      intro j
      have h1 : ((((centered ((P.src.t : ZMod M) • φa)).coeff j : ℤ)) : ZMod M) =
          (((P.src.t : ℤ) * Ψ.coeff j : ℤ) : ZMod M) := by
        rw [coeff_centered, ZMod.coe_valMinAbs]
        push_cast
        rw [coeff_centered, ZMod.coe_valMinAbs]; rfl
      exact exists_eq_add_mul_of_cast_eq h1
    choose w hw using hΦ
    rw [hphase]
    refine ⟨(normInf_smul_le _ δ).trans (by rw [mul_comm]; nlinarith [hb]),
      fun j => ⟨δ.coeff j, rfl⟩, fun j => ?_, ?_⟩
    · obtain ⟨A, hA⟩ := hdvd j
      refine ⟨(P.src.t : ℤ) * A + Q * w j, ?_⟩
      show (centered ((P.src.t : ZMod M) • φa)).coeff j + (P.src.t : ℤ) * δ.coeff j = _
      rw [hw j, hM]; push_cast
      linear_combination (P.src.t : ℤ) * hA
    · rw [hphase, he, ← ofInt_smul_int]
      ext j
      obtain ⟨A, hA⟩ := hdvd j
      simp only [coeff_ofInt]
      show (((P.src.t : ℤ) * ((Ψ.coeff j + δ.coeff j) / q) : ℤ) : ZMod Q) =
        ((((centered ((P.src.t : ZMod M) • φa)).coeff j + (P.src.t : ℤ) * δ.coeff j) / q : ℤ) : ZMod Q)
      have hsum : (centered ((P.src.t : ZMod M) • φa)).coeff j + (P.src.t : ℤ) * δ.coeff j =
          q * ((P.src.t : ℤ) * A + Q * w j) := by
        rw [hw j, hM]; push_cast; linear_combination (P.src.t : ℤ) * hA
      rw [hsum, hA]
      rcases Nat.eq_zero_or_pos q with hq0 | hq0
      · subst hq0; simp
      · have hq0' : (q : ℤ) ≠ 0 := by exact_mod_cast hq0.ne'
        rw [Int.mul_ediv_cancel_left _ hq0', Int.mul_ediv_cancel_left _ hq0']
        push_cast; simp

theorem run_toLSB (E : Trace.Budget) (s : IntPoly P.src.N) : ∀ (body : List Instr)
    (ρ : Env P.src) (σ σf : Trace.CtEnv P), MSB.Run P E s body ρ σ σf →
    Trace.Run P E s body ρ (toLSBEnv P σ) (toLSBEnv P σf)
  | [], _, σ, σf, h => by
    have h' : σf = σ := h
    show toLSBEnv P σf = toLSBEnv P σ
    rw [h']
  | i :: is, ρ, σ, σf, h => by
    obtain ⟨ρ', σ', hs, hok, hr⟩ := h
    exact ⟨ρ', toLSBEnv P σ', hs, stepOK_toLSB P E s ρ ρ' σ σ' i hs hok,
      run_toLSB E s is ρ' σ' σf hr⟩

end Validation.MSB
