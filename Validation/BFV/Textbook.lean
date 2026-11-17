import Challenge.BFV.Defs
import Validation.Trace
import Validation.BFV.Mul

/-!
# Validation.BFV.Textbook — the textbook BFV algorithms meet the phase contracts

Proofs of the realizability pins `stepOK_add_padded`, `stepOK_addPlain_textbook`,
`stepOK_mulPlain_textbook`, `stepOK_mul_textbook`, `stepOK_modSwitch_textbook` of
`Challenge.BFV`: each textbook operation meets its contract in `Spec.TraceBFV.StepOK`, within
`Spec.BudgetBFV`.
-/

namespace Validation.BFV
open Spec NPoly Scheme Source Correct Challenge.BFV
open Validation.Ring Validation.Scheme Validation.Source

/-! ### Integer facts -/

/-- `|b·⌊a/b⌉ − a| ≤ b/2`. -/
theorem two_abs_roundDiv_sub_le (a : ℤ) (b : ℕ) (hb : 0 < b) :
    2 * |(b : ℤ) * roundDiv a b - a| ≤ b := by
  unfold roundDiv
  have hb' : (0 : ℤ) < b := by exact_mod_cast hb
  have h1 := Int.emod_add_mul_ediv (2 * a + b) (2 * b)
  have h2 := Int.emod_nonneg (2 * a + b) (show (2 * (b : ℤ)) ≠ 0 by omega)
  have h3 := Int.emod_lt_of_pos (2 * a + b) (show (0 : ℤ) < 2 * b by omega)
  rcases abs_cases ((b : ℤ) * ((2 * a + b) / (2 * b)) - a) with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;>
    linarith

theorem abs_le_half {x : ℤ} {Q : ℕ} (h : 2 * |x| ≤ Q) : |x| ≤ ((Q / 2 : ℕ) : ℤ) := by
  generalize |x| = z at h
  omega

variable {N : ℕ}

/-- The Spec scalar multiplication by an integer is multiplication by the constant. -/
theorem specSMul_eq_intCast_mul [NeZero N] (c : ℤ) (p : IntPoly N) :
    @HSMul.hSMul ℤ (IntPoly N) (IntPoly N) (@instHSMul _ _ NPoly.instSMul) c p
      = (c : IntPoly N) * p := by
  ext i
  rw [coeff_intCast_mul]
  rfl

/-! ### The lift of a two-component phase -/

/-- The integer phase `c₀ + s·c₁` of representatives within `Q/2` is the centred phase plus
`Q·k` with `2·‖k‖∞ ≤ 2 + ‖s‖₁`. -/
theorem lift_core [NeZero N] (Q : ℕ) (hQ : 0 < Q) (sk c0 c1 Φ : IntPoly N) (S : ℤ)
    (hS : ∑ j, |sk.coeff j| ≤ S)
    (h0 : ∀ i, 2 * |c0.coeff i| ≤ Q) (h1 : ∀ i, 2 * |c1.coeff i| ≤ Q)
    (hΦ : ∀ i, 2 * |Φ.coeff i| ≤ Q)
    (hE : ofInt Q (c0 + sk * c1) = ofInt Q Φ) :
    ∃ k : IntPoly N, (∀ i, 2 * |k.coeff i| ≤ 2 + S) ∧
      c0 + sk * c1 = Φ + ((Q : ℤ) : IntPoly N) * k := by
  have hK : ∀ i, ∃ j : ℤ, (c0 + sk * c1).coeff i = Φ.coeff i + (Q : ℤ) * j := by
    intro i
    have := congrArg (fun p => p.coeff i) hE
    simp only [coeff_ofInt] at this
    exact exists_eq_add_mul_of_cast_eq this
  choose K hK using hK
  refine ⟨⟨K⟩, ?_, ?_⟩
  · intro i
    show 2 * |K i| ≤ 2 + S
    have hQ' : (0 : ℤ) < Q := by exact_mod_cast hQ
    have hS0 : (0 : ℤ) ≤ ∑ j, |sk.coeff j| := Finset.sum_nonneg fun _ _ => abs_nonneg _
    have hh : 2 * ((Q / 2 : ℕ) : ℤ) ≤ Q := two_mul_half_le Q
    have hh0 : (0 : ℤ) ≤ ((Q / 2 : ℕ) : ℤ) := by positivity
    have hm := abs_coeff_mul_le sk c1 _ (fun j => abs_le_half (h1 j)) i
    have hSh : (∑ j, |sk.coeff j|) * ((Q / 2 : ℕ) : ℤ) ≤ S * ((Q / 2 : ℕ) : ℤ) :=
      mul_le_mul_of_nonneg_right hS hh0
    have hSQ : 2 * (S * ((Q / 2 : ℕ) : ℤ)) ≤ S * Q := by
      have := mul_le_mul_of_nonneg_left hh (hS0.trans hS)
      linarith
    have e := hK i
    rw [coeff_add'] at e
    have e' : (Q : ℤ) * K i = c0.coeff i + (sk * c1).coeff i + (-Φ.coeff i) := by linarith
    have hab : (Q : ℤ) * |K i| ≤ |c0.coeff i| + |(sk * c1).coeff i| + |Φ.coeff i| := by
      rw [← abs_of_pos hQ', ← abs_mul, e']
      refine (abs_add_three _ _ _).trans ?_
      rw [abs_neg]
    have h0i := h0 i
    have hΦi := hΦ i
    have : (Q : ℤ) * (2 * |K i|) ≤ Q * (2 + S) := by nlinarith
    exact le_of_mul_le_mul_left this hQ'
  · ext i
    rw [hK i, coeff_add', coeff_intCast_mul]

/-! ### The scaling error of the product -/

theorem mul_core [NeZero N] (t Q : ℕ) (sk Ψa Ψb X0 X1 X2 T0 T1 T2 : IntPoly N) (S : ℤ)
    (hS : ∑ j, |sk.coeff j| ≤ S)
    (hT : Ψa * Ψb = T0 + sk * T1 + (sk * sk) * T2)
    (h0 : ∀ i, 2 * |(Q : ℤ) * X0.coeff i - (t : ℤ) * T0.coeff i| ≤ Q)
    (h1 : ∀ i, 2 * |(Q : ℤ) * X1.coeff i - (t : ℤ) * T1.coeff i| ≤ Q)
    (h2 : ∀ i, 2 * |(Q : ℤ) * X2.coeff i - (t : ℤ) * T2.coeff i| ≤ Q) :
    ∃ D : IntPoly N, (∀ i, 2 * |D.coeff i| ≤ (Q : ℤ) * (1 + S + S * S)) ∧
      ((Q : ℤ) : IntPoly N) * (X0 + sk * X1 + (sk * sk) * X2) =
        (((t : ℤ)) : IntPoly N) * (Ψa * Ψb) + D := by
  obtain ⟨D0, hD0⟩ : ∃ D0, D0 = ((Q : ℤ) : IntPoly N) * X0 - ((t : ℤ) : IntPoly N) * T0 := ⟨_, rfl⟩
  obtain ⟨D1, hD1⟩ : ∃ D1, D1 = ((Q : ℤ) : IntPoly N) * X1 - ((t : ℤ) : IntPoly N) * T1 := ⟨_, rfl⟩
  obtain ⟨D2, hD2⟩ : ∃ D2, D2 = ((Q : ℤ) : IntPoly N) * X2 - ((t : ℤ) : IntPoly N) * T2 := ⟨_, rfl⟩
  have hc0 : ∀ i, |D0.coeff i| ≤ ((Q / 2 : ℕ) : ℤ) := by
    intro i; rw [hD0, coeff_sub', coeff_intCast_mul, coeff_intCast_mul]; exact abs_le_half (h0 i)
  have hc1 : ∀ i, |D1.coeff i| ≤ ((Q / 2 : ℕ) : ℤ) := by
    intro i; rw [hD1, coeff_sub', coeff_intCast_mul, coeff_intCast_mul]; exact abs_le_half (h1 i)
  have hc2 : ∀ i, |D2.coeff i| ≤ ((Q / 2 : ℕ) : ℤ) := by
    intro i; rw [hD2, coeff_sub', coeff_intCast_mul, coeff_intCast_mul]; exact abs_le_half (h2 i)
  refine ⟨D0 + sk * D1 + sk * (sk * D2), ?_, ?_⟩
  · intro i
    have hS0 : (0 : ℤ) ≤ ∑ j, |sk.coeff j| := Finset.sum_nonneg fun _ _ => abs_nonneg _
    have hS0' : (0 : ℤ) ≤ S := hS0.trans hS
    have hh : 2 * ((Q / 2 : ℕ) : ℤ) ≤ Q := two_mul_half_le Q
    have hh0 : (0 : ℤ) ≤ ((Q / 2 : ℕ) : ℤ) := by positivity
    have b0 := hc0 i
    have b1 := abs_coeff_mul_le sk D1 _ hc1 i
    have b2' : ∀ j, |(sk * D2).coeff j| ≤ (∑ j, |sk.coeff j|) * ((Q / 2 : ℕ) : ℤ) :=
      abs_coeff_mul_le sk D2 _ hc2
    have b2 := abs_coeff_mul_le sk (sk * D2) _ b2' i
    have A : (∑ j, |sk.coeff j|) * ((Q / 2 : ℕ) : ℤ) ≤ S * ((Q / 2 : ℕ) : ℤ) :=
      mul_le_mul_of_nonneg_right hS hh0
    have B : (∑ j, |sk.coeff j|) * ((∑ j, |sk.coeff j|) * ((Q / 2 : ℕ) : ℤ)) ≤
        S * (S * ((Q / 2 : ℕ) : ℤ)) :=
      mul_le_mul hS A (mul_nonneg hS0 hh0) hS0'
    have C : 2 * ((Q / 2 : ℕ) : ℤ) * (1 + S + S * S) ≤ (Q : ℤ) * (1 + S + S * S) :=
      mul_le_mul_of_nonneg_right hh (by nlinarith)
    rw [coeff_add', coeff_add']
    have tri : |D0.coeff i + (sk * D1).coeff i + (sk * (sk * D2)).coeff i| ≤
        |D0.coeff i| + |(sk * D1).coeff i| + |(sk * (sk * D2)).coeff i| := abs_add_three _ _ _
    nlinarith
  · subst hD0 hD1 hD2
    rw [hT]
    ring

variable (P : FullParams)

theorem modulus_pos' (hP : SchemeParamsOK P) (ℓ : ℕ) : 0 < P.src.modulus ℓ := by
  unfold Params.modulus
  apply List.prod_pos
  intro q hq
  exact (hP.prime q (List.mem_of_mem_take hq)).pos

/-! ### The pins -/

/-- Componentwise addition (the shorter ciphertext padded with zero components) meets the `add`
contract. -/
theorem stepOK_add_padded (E : TraceBFV.Budget) (s : IntPoly P.src.N) (ρ ρ' : Env P.src)
    (σ : Trace.CtEnv P) (d a b : Var) (x y : Val P.src) (ca cb : List (IntPoly P.src.N))
    (hstep : step P.src ρ (.add d a b) = some ρ') (hx : ρ a = some x) (hy : ρ b = some y)
    (ha : σ a = some ca) (hb : σ b = some cb)
    (hla : ca.length = x.parts) (hlb : cb.length = y.parts) :
    TraceBFV.StepOK P E s ρ ρ' σ (σ.set d (Challenge.Source.padZip (· + ·) ca cb))
      (.add d a b) := by
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
    rw [phase_padZip_add]

theorem bfvAddPlain_def {N : ℕ} (t Q : ℕ) (c : List (IntPoly N)) (p : IntPoly N) :
    bfvAddPlain t Q c p = Challenge.Source.padZip (· + ·) c
      [@HSMul.hSMul ℤ (IntPoly N) (IntPoly N) (@instHSMul _ _ NPoly.instSMul)
        ((Q / t : ℕ) : ℤ) p] := rfl

/-- Adding `⌊Q/t⌋·p` to the first component meets the `addPlain` contract, with no deviation
(every budget). -/
theorem stepOK_addPlain_textbook (E : TraceBFV.Budget) (s : IntPoly P.src.N) (ρ ρ' : Env P.src)
    (σ : Trace.CtEnv P) (d a p : Var) (x y : Val P.src) (ca : List (IntPoly P.src.N))
    (c : IntPoly P.src.N)
    (hstep : step P.src ρ (.addPlain d a p) = some ρ') (hx : ρ a = some x) (hy : ρ p = some y)
    (ha : σ a = some ca) (hp : σ p = some [c]) (hla : ca.length = x.parts) :
    TraceBFV.StepOK P E s ρ ρ' σ
      (σ.set d (bfvAddPlain P.src.t (P.src.modulus x.level) ca c)) (.addPlain d a p) := by
  simp only [step, hx, hy, Option.bind_eq_bind, Option.bind_some, Option.pure_def] at hstep
  obtain ⟨⟨hy1, -⟩, h2⟩ := Validation.Trace.guard_bind_eq_some hstep
  obtain ⟨m, -, h3⟩ := Option.bind_eq_some_iff.mp h2
  cases h3
  refine ⟨_, _, set_self _ _ _, ?_, rfl, ?_⟩
  · simp [bfvAddPlain_def, length_padZip, hla, hy1]
  · refine ⟨x, y, ca, [c], 0, hx, hy, ha, hp, ?_, ?_⟩
    · rw [normInf_zero]; exact Nat.zero_le _
    dsimp only
    rw [Validation.Trace.phaseAt_singleton]
    unfold Trace.phaseAt
    rw [bfvAddPlain_def]
    rw [phase_padZip_add, List.map_cons, List.map_nil, phase_singleton, ofInt_zero]
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

/-- Multiplying every component by the plaintext polynomial meets the `mulPlain` contract. -/
theorem stepOK_mulPlain_textbook (E : TraceBFV.Budget) (s : IntPoly P.src.N) (ρ ρ' : Env P.src)
    (σ : Trace.CtEnv P) (d a p : Var) (x y : Val P.src) (ca : List (IntPoly P.src.N))
    (c : IntPoly P.src.N)
    (hstep : step P.src ρ (.mulPlain d a p) = some ρ') (hx : ρ a = some x) (hy : ρ p = some y)
    (ha : σ a = some ca) (hp : σ p = some [c]) (hla : ca.length = x.parts) :
    TraceBFV.StepOK P E s ρ ρ' σ (σ.set d (ca.map (c * ·))) (.mulPlain d a p) := by
  simp only [step, hx, hy, Option.bind_eq_bind, Option.bind_some, Option.pure_def] at hstep
  obtain ⟨-, h2⟩ := Validation.Trace.guard_bind_eq_some hstep
  obtain ⟨m, -, h3⟩ := Option.bind_eq_some_iff.mp h2
  cases h3
  refine ⟨_, _, set_self _ _ _, ?_, rfl, ?_⟩
  · simp [hla]
  · refine ⟨x, y, ca, [c], hx, hy, ha, hp, ?_⟩
    dsimp only
    rw [Validation.Trace.phaseAt_singleton]
    unfold Trace.phaseAt
    rw [phase_map_mul]

/-- **Textbook multiplication meets the `mul` contract** with `mulLift = ⌊(2 + N·B_s)/2⌋` and
`mulRound = 1 + N·B_s + (N·B_s)²` (`Spec.BudgetBFV`), for two-component operands under any
secret within the bound. -/
theorem stepOK_mul_textbook (hP : SchemeParamsOK P) (E : TraceBFV.Budget)
    (hL : BudgetBFV.mulLift P ≤ E.mulLift) (hR : BudgetBFV.mulRound P ≤ E.mulRound)
    (s : IntPoly P.src.N) (hs : SecretOK P.secretBound s) (ρ ρ' : Env P.src)
    (σ : Trace.CtEnv P) (d a b : Var) (x y : Val P.src) (ca cb : List (IntPoly P.src.N))
    (hstep : step P.src ρ (.mul d a b) = some ρ') (hx : ρ a = some x) (hy : ρ b = some y)
    (ha : σ a = some ca) (hb : σ b = some cb)
    (hla : ca.length = 2) (hlb : cb.length = 2) (h2x : x.parts = 2) (h2y : y.parts = 2) :
    TraceBFV.StepOK P E s ρ ρ' σ
      (σ.set d (bfvMul P.src.t (P.src.modulus x.level) ca cb)) (.mul d a b) := by
  simp only [step, hx, hy, Option.bind_eq_bind, Option.bind_some, Option.pure_def] at hstep
  obtain ⟨⟨-, hkey, -⟩, h2⟩ := Validation.Trace.guard_bind_eq_some hstep
  obtain ⟨m, -, h3⟩ := Option.bind_eq_some_iff.mp h2
  cases h3
  obtain ⟨a0, a1, rfl⟩ := List.length_eq_two.mp hla
  obtain ⟨b0, b1, rfl⟩ := List.length_eq_two.mp hlb
  have hN : NeZero P.src.N := ⟨by obtain ⟨k, hk⟩ := hP.N_pow2; rw [hk]; positivity⟩
  have hQ : 0 < P.src.modulus x.level := modulus_pos' P hP _
  have ht : bfvMul P.src.t (P.src.modulus x.level) [a0, a1] [b0, b1] =
      [scaleRound P.src.t (P.src.modulus x.level)
          (centered (ofInt (P.src.modulus x.level) a0) *
            centered (ofInt (P.src.modulus x.level) b0)),
       scaleRound P.src.t (P.src.modulus x.level)
          (centered (ofInt (P.src.modulus x.level) a0) *
              centered (ofInt (P.src.modulus x.level) b1) +
            centered (ofInt (P.src.modulus x.level) a1) *
              centered (ofInt (P.src.modulus x.level) b0)),
       scaleRound P.src.t (P.src.modulus x.level)
          (centered (ofInt (P.src.modulus x.level) a1) *
            centered (ofInt (P.src.modulus x.level) b1))] := rfl
  rw [ht]
  refine ⟨_, _, set_self _ _ _, ?_, rfl, ?_⟩
  · simp [h2x, h2y]
  refine ⟨x, y, [a0, a1], [b0, b1], ?_⟩
  dsimp only
  rw [← hkey]
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
  obtain ⟨kb, hkb, hΨb⟩ := lift_core Q hQ sk (centered (ofInt Q b0)) (centered (ofInt Q b1))
    (centered (phase (ofInt Q sk) ([b0, b1].map (ofInt Q)))) _ hS
    (fun i => two_abs_valMinAbs_le hQ _) (fun i => two_abs_valMinAbs_le hQ _)
    (fun i => two_abs_valMinAbs_le hQ _)
    (by simp only [ofInt_add, ofInt_mul, ofInt_centered, phase_map_ofInt_two])
  obtain ⟨D, hD, hXD⟩ := mul_core P.src.t Q sk
    (centered (ofInt Q a0) + sk * centered (ofInt Q a1))
    (centered (ofInt Q b0) + sk * centered (ofInt Q b1))
    (scaleRound P.src.t Q (centered (ofInt Q a0) * centered (ofInt Q b0)))
    (scaleRound P.src.t Q (centered (ofInt Q a0) * centered (ofInt Q b1) +
      centered (ofInt Q a1) * centered (ofInt Q b0)))
    (scaleRound P.src.t Q (centered (ofInt Q a1) * centered (ofInt Q b1)))
    _ _ _ _ hS (by ring)
    (fun i => two_abs_roundDiv_sub_le _ _ hQ) (fun i => two_abs_roundDiv_sub_le _ _ hQ)
    (fun i => two_abs_roundDiv_sub_le _ _ hQ)
  refine ⟨ka, kb,
    scaleRound P.src.t Q (centered (ofInt Q a0) * centered (ofInt Q b0)) +
      sk * scaleRound P.src.t Q (centered (ofInt Q a0) * centered (ofInt Q b1) +
        centered (ofInt Q a1) * centered (ofInt Q b0)) +
      (sk * sk) * scaleRound P.src.t Q (centered (ofInt Q a1) * centered (ofInt Q b1)),
    D, hx, hy, ha, hb, ?_, ?_, ?_, ?_, ?_⟩
  · rw [normInf_le_iff]
    intro i
    have h' : 2 * |ka.coeff i| ≤ 2 + ((P.src.N * P.secretBound : ℕ) : ℤ) := by
      push_cast; exact hka i
    unfold BudgetBFV.mulLift at hL
    generalize P.src.N * P.secretBound = m at h' hL
    generalize |ka.coeff i| = z at h'
    omega
  · rw [normInf_le_iff]
    intro i
    have h' : 2 * |kb.coeff i| ≤ 2 + ((P.src.N * P.secretBound : ℕ) : ℤ) := by
      push_cast; exact hkb i
    unfold BudgetBFV.mulLift at hL
    generalize P.src.N * P.secretBound = m at h' hL
    generalize |kb.coeff i| = z at h'
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
  · rw [specSMul_eq_intCast_mul, specSMul_eq_intCast_mul, specSMul_eq_intCast_mul,
      specSMul_eq_intCast_mul, ← hΨa, ← hΨb]
    exact hXD
  · simp only [List.map_cons, List.map_nil, phase_three', ofInt_add, ofInt_mul]

/-- **Rounding every component meets the `modSwitch` contract** with
`modSwitch = ⌈(1 + N·B_s)/2⌉`, for two-component ciphertexts. -/
theorem stepOK_modSwitch_textbook (hP : SchemeParamsOK P) (E : TraceBFV.Budget)
    (hE : BudgetBFV.msBudget P ≤ E.modSwitch)
    (s : IntPoly P.src.N) (hs : SecretOK P.secretBound s) (ρ ρ' : Env P.src)
    (σ : Trace.CtEnv P) (d a : Var) (x : Val P.src) (ca : List (IntPoly P.src.N))
    (hstep : step P.src ρ (.modSwitch d a) = some ρ') (hx : ρ a = some x)
    (ha : σ a = some ca) (hℓL : x.level ≤ P.src.qs.length) (h2 : x.parts = 2)
    (hla : ca.length = 2) :
    TraceBFV.StepOK P E s ρ ρ' σ
      (σ.set d (ca.map (bfvModSwitchComp P.src.qs[x.level - 1]!))) (.modSwitch d a) := by
  simp only [step, hx, Option.bind_eq_bind, Option.bind_some, Option.pure_def] at hstep
  obtain ⟨hℓ, h3⟩ := Validation.Trace.guard_bind_eq_some hstep
  have hlt : x.level - 1 < P.src.qs.length := by omega
  have hgetD : P.src.qs[x.level - 1]? = some P.src.qs[x.level - 1]! := by simp [hlt]
  rw [hgetD, Option.bind_some] at h3
  cases h3
  refine ⟨_, _, set_self _ _ _, ?_, rfl, ?_⟩
  · simp [hla, h2]
  obtain ⟨c0, c1, rfl⟩ := List.length_eq_two.mp hla
  obtain ⟨hqp, -⟩ := qLast_facts P hP (x.level - 1) hlt
  have hQQ : P.src.modulus x.level = P.src.modulus (x.level - 1) * P.src.qs[x.level - 1]! :=
    modulus_pred _ _ (by omega) hℓL
  refine ⟨x, [c0, c1], ?_⟩
  dsimp only
  generalize P.src.qs[x.level - 1]! = q at hgetD hqp hQQ ⊢
  have hq0 : 0 < q := hqp.pos
  unfold Trace.phaseAt
  rw [hQQ]
  generalize hsk : automorph x.key s = sk
  generalize P.src.modulus (x.level - 1) = Q'
  set Φ := centered (phase (ofInt (Q' * q) sk) ([c0, c1].map (ofInt (Q' * q)))) with hΦ
  have hE' : ofInt (Q' * q) (c0 + sk * c1) = ofInt (Q' * q) Φ := by
    rw [hΦ, ofInt_centered, phase_map_ofInt_two]
  let dl : IntPoly P.src.N → IntPoly P.src.N := fun c =>
    ⟨fun i => (q : ℤ) * roundDiv (c.coeff i) q - c.coeff i⟩
  have hdiv : ∀ c : IntPoly P.src.N, ∀ i,
      (q : ℤ) * (bfvModSwitchComp q c).coeff i = c.coeff i + (dl c).coeff i := by
    intro c i
    show (q : ℤ) * roundDiv (c.coeff i) q = c.coeff i + ((q : ℤ) * roundDiv (c.coeff i) q - c.coeff i)
    ring
  have hdl : ∀ c : IntPoly P.src.N, ∀ i, |(dl c).coeff i| ≤ ((q / 2 : ℕ) : ℤ) := by
    intro c i
    exact abs_le_half (two_abs_roundDiv_sub_le _ _ hq0)
  obtain ⟨e, he, hqe⟩ := divq_core Q' q sk c0 c1 Φ (dl c0) (dl c1)
    (bfvModSwitchComp q c0) (bfvModSwitchComp q c1) hE' (hdiv c0) (hdiv c1)
  have hS : (∑ j, |sk.coeff j|) ≤ (P.src.N : ℤ) * (P.secretBound : ℤ) := by
    rw [← hsk]
    exact (sum_abs_automorph_le _ _).trans (sum_abs_le s _ ((normInf_le_iff _ _).mp hs))
  refine ⟨dl c0 + sk * dl c1, q, hx, ha, hgetD, ?_, ?_, ?_⟩
  · -- the bound
    rw [normInf_le_iff]
    intro i
    rw [coeff_add']
    have h0 := hdl c0 i
    have h1 := abs_coeff_mul_le sk (dl c1) _ (hdl c1) i
    have hh : 2 * ((q / 2 : ℕ) : ℤ) ≤ q := two_mul_half_le q
    have hh0 : (0 : ℤ) ≤ ((q / 2 : ℕ) : ℤ) := by positivity
    have hq0' : (0 : ℤ) ≤ (q : ℤ) := by positivity
    have hE'' : (1 + (P.src.N : ℤ) * P.secretBound) ≤ 2 * (E.modSwitch : ℤ) := by
      have : 1 + P.src.N * P.secretBound ≤ 2 * E.modSwitch := by
        unfold BudgetBFV.msBudget at hE; omega
      exact_mod_cast this
    have h3 : (∑ j, |sk.coeff j|) * ((q / 2 : ℕ) : ℤ) ≤
        ((P.src.N : ℤ) * P.secretBound) * ((q / 2 : ℕ) : ℤ) :=
      mul_le_mul_of_nonneg_right hS hh0
    have hx0 : (0 : ℤ) ≤ 1 + (P.src.N : ℤ) * P.secretBound := by positivity
    have h5 : 2 * ((q / 2 : ℕ) : ℤ) * (1 + (P.src.N : ℤ) * P.secretBound) ≤
        (q : ℤ) * (1 + (P.src.N : ℤ) * P.secretBound) :=
      mul_le_mul_of_nonneg_right hh hx0
    have h6 : (q : ℤ) * (1 + (P.src.N : ℤ) * P.secretBound) ≤
        (q : ℤ) * (2 * (E.modSwitch : ℤ)) := mul_le_mul_of_nonneg_left hE'' hq0'
    have tri := abs_add_le ((dl c0).coeff i) ((sk * dl c1).coeff i)
    push_cast
    nlinarith
  · -- q ∣ Φ + δ
    intro j
    refine ⟨e.coeff j, ?_⟩
    rw [coeff_add', hqe j]; ring
  · -- the new phase
    rw [show [c0, c1].map (bfvModSwitchComp q) =
      [bfvModSwitchComp q c0, bfvModSwitchComp q c1] from rfl,
      phase_map_ofInt_two, he]
    congr 1
    ext j
    show e.coeff j = (Φ.coeff j + (dl c0 + sk * dl c1).coeff j) / q
    rw [coeff_add', ← add_assoc, ← hqe j, Int.mul_ediv_cancel_left _ (by exact_mod_cast hq0.ne')]

end Validation.BFV
