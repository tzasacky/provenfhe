import Challenge.BFVMul
import Validation.BFV.Params
import Validation.BFV.Textbook
import Validation.BFVMul.Approx

/-!
# Validation.BFVMul.Ops — the remaining textbook BFV operations, and plaintext addition by rounding

Proofs of the pins `stepOK_sub_padded`, `stepOK_subPlain_textbook`, `stepOK_mulConst_textbook`,
`stepOK_automorph_textbook`, `stepOK_square_textbook`, `stepOK_addPlain_rounded`,
`stepOK_subPlain_rounded`, `plainAddRoundedAt_le` of `Challenge.BFVMul`.

* The first four are the phase identities of `Validation/Trace.lean`, read in `Spec.TraceBFV.StepOK`.
* `stepOK_square_textbook` is `stepOK_square_approx` at lift slack `0` and rounding slack `1`.
* Plaintext addition by rounding: with `Q = t·Δ + r`,
  `⌊Q·p/t⌉ = Δ·p + ⌊r·p/t⌉` and `|⌊r·p/t⌉| ≤ ⌊(2·r·b + t)/(2t)⌋` for `|p| ≤ b`
  (`abs_roundDiv_scale_sub_le`); the deviation `δ` of the contract is `±⌊r·p/t⌉`.

The helper lemmas are in the namespace `Validation.BFVMul.Ops`; the pins in `Validation.BFVMul`.
-/

namespace Validation.BFVMul.Ops
open Spec NPoly Scheme Source Correct Challenge.BFV Challenge.BFVMul
open Validation.Ring Validation.Scheme Validation.Source Validation.BFV

variable {N : ℕ}

/-! ### Scalar multiples -/

theorem ofInt_zsmul (q : ℕ) (c : ℤ) (a : IntPoly N) :
    ofInt q (c • a) = (c : ZMod q) • ofInt q a := by
  ext i; simp [ofInt]

/-- The phase of a ciphertext with every component multiplied by the integer `c`. -/
theorem phase_map_zsmul {q : ℕ} (s : Poly q N) (c : ℤ) : ∀ a : List (IntPoly N),
    phase s ((a.map (c • ·)).map (ofInt q)) = (c : ZMod q) • phase s (a.map (ofInt q))
  | [] => by
      simp only [List.map_nil, phase]
      ext i; simp
  | a :: as => by
      simp only [List.map_cons, phase]
      rw [phase_map_zsmul s c as, ofInt_zsmul]
      apply eq_of_neZero; intro
      rw [smul_add, mul_smul_comm]

/-- `ofInt` of the Spec scalar multiple by a natural number cast to `ℤ`. -/
theorem ofInt_specSMul_natCast (Q k : ℕ) (c : IntPoly N) :
    ofInt Q (@HSMul.hSMul ℤ (IntPoly N) (IntPoly N) (@instHSMul _ _ NPoly.instSMul)
        ((k : ℕ) : ℤ) c) = ((k : ℕ) : ZMod Q) • ofInt Q c := by
  ext i
  show ((((k : ℕ) : ℤ) * c.coeff i : ℤ) : ZMod Q) = _ * ((c.coeff i : ℤ) : ZMod Q)
  rw [Int.cast_mul, Int.cast_natCast]

theorem bfvSubPlain_def (t Q : ℕ) (c : List (IntPoly N)) (p : IntPoly N) :
    bfvSubPlain t Q c p = Challenge.Source.padZip (· - ·) c
      [@HSMul.hSMul ℤ (IntPoly N) (IntPoly N) (@instHSMul _ _ NPoly.instSMul)
        ((Q / t : ℕ) : ℤ) p] := rfl

/-! ### Rounding the scaled plaintext -/

/-- `|⌊Q·p/t⌉ − ⌊Q/t⌋·p| ≤ ⌊(2·(Q mod t)·b + t)/(2t)⌋` for `|p| ≤ b` (also at `t = 0`, where
both sides are `0`). -/
theorem abs_roundDiv_scale_sub_le (t Q b : ℕ) (p : ℤ) (hp : |p| ≤ b) :
    |roundDiv ((Q : ℤ) * p) t - ((Q / t : ℕ) : ℤ) * p| ≤
      (((2 * (Q % t) * b + t) / (2 * t) : ℕ) : ℤ) := by
  rcases Nat.eq_zero_or_pos t with rfl | ht
  · simp [roundDiv]
  have ht' : (0 : ℤ) < 2 * (t : ℤ) := by positivity
  have hQ : (Q : ℤ) = (t : ℤ) * ((Q / t : ℕ) : ℤ) + ((Q % t : ℕ) : ℤ) := by
    exact_mod_cast (Nat.div_add_mod Q t).symm
  generalize ((Q / t : ℕ) : ℤ) = Δ at hQ ⊢
  have hr0 : (0 : ℤ) ≤ ((Q % t : ℕ) : ℤ) := by positivity
  have hcast : (((2 * (Q % t) * b + t) / (2 * t) : ℕ) : ℤ) =
      (2 * ((Q % t : ℕ) : ℤ) * b + t) / (2 * t) := by push_cast; rfl
  rw [hcast]
  generalize ((Q % t : ℕ) : ℤ) = r at hQ hr0 ⊢
  have hround : roundDiv ((Q : ℤ) * p) t = (2 * r * p + t) / (2 * t) + Δ * p := by
    unfold roundDiv
    rw [← Int.add_mul_ediv_left _ _ ht'.ne', hQ]
    congr 1; ring
  rw [hround, add_sub_cancel_right]
  obtain ⟨hp1, hp2⟩ := abs_le.mp hp
  have hup : r * p ≤ r * b := mul_le_mul_of_nonneg_left hp2 hr0
  have hlo : -(r * b) ≤ r * p := by
    have := mul_le_mul_of_nonneg_left hp1 hr0
    linarith
  have hK1 := Int.emod_add_mul_ediv (2 * r * b + t) (2 * t)
  have hK2 := Int.emod_lt_of_pos (2 * r * b + t) ht'
  rw [abs_le]
  constructor
  · rw [Int.le_ediv_iff_mul_le ht']
    linarith
  · exact Int.ediv_le_ediv ht' (by linarith)

/-- The deviation of `⌊Q·p/t⌉` from `⌊Q/t⌋·p`, coefficient by coefficient. -/
def scaleDev (t Q : ℕ) (p : IntPoly N) : IntPoly N :=
  ⟨fun i => roundDiv (Q * p.coeff i) t - ((Q / t : ℕ) : ℤ) * p.coeff i⟩

theorem abs_scaleDev_le (t Q b : ℕ) (p : IntPoly N) (hp : normInf p ≤ b) (i : Fin N) :
    |(scaleDev t Q p).coeff i| ≤ (((2 * (Q % t) * b + t) / (2 * t) : ℕ) : ℤ) :=
  abs_roundDiv_scale_sub_le t Q b _ ((normInf_le_iff _ _).mp hp i)

/-- `⌊Q·p/t⌉ ≡ ⌊Q/t⌋·p + δ (mod Q')` with `δ = scaleDev t Q p`, for every modulus `Q'`. -/
theorem ofInt_scaleUp (Q' t Q : ℕ) (p : IntPoly N) :
    ofInt Q' (scaleUp t Q p) =
      ((Q / t : ℕ) : ZMod Q') • ofInt Q' p + ofInt Q' (scaleDev t Q p) := by
  ext i
  show ((roundDiv (Q * p.coeff i) t : ℤ) : ZMod Q') =
    ((Q / t : ℕ) : ZMod Q') * ((p.coeff i : ℤ) : ZMod Q') +
      ((roundDiv (Q * p.coeff i) t - ((Q / t : ℕ) : ℤ) * p.coeff i : ℤ) : ZMod Q')
  rw [Int.cast_sub, Int.cast_mul, Int.cast_natCast]
  ring

/-- The definition of `bfvAddPlainRounded`, by `rfl` (no equation lemma of the locked
definition is realised here). -/
theorem bfvAddPlainRounded_def (t Q : ℕ) (c : List (IntPoly N)) (p : IntPoly N) :
    bfvAddPlainRounded t Q c p = Challenge.Source.padZip (· + ·) c [scaleUp t Q p] :=
  rfl

/-- The definition of `bfvSubPlainRounded`, by `rfl`. -/
theorem bfvSubPlainRounded_def (t Q : ℕ) (c : List (IntPoly N)) (p : IntPoly N) :
    bfvSubPlainRounded t Q c p = Challenge.Source.padZip (· - ·) c [scaleUp t Q p] :=
  rfl

end Validation.BFVMul.Ops

namespace Validation.BFVMul
open Spec NPoly Scheme Source Correct Challenge.BFV Challenge.BFVMul
open Validation.Ring Validation.Scheme Validation.Source Validation.BFV
open Validation.BFVMul.Approx Validation.BFVMul.Ops

variable (P : FullParams)

/-! ### The pins: textbook operations -/

/-- Componentwise subtraction (the shorter ciphertext padded with zero components) meets the
`sub` contract. -/
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

/-- Subtracting `⌊Q/t⌋·p` from the first component meets the `subPlain` contract, with no
deviation (every budget). -/
theorem stepOK_subPlain_textbook (E : TraceBFV.Budget) (s : IntPoly P.src.N) (ρ ρ' : Env P.src)
    (σ : Trace.CtEnv P) (d a p : Var) (x y : Val P.src) (ca : List (IntPoly P.src.N))
    (c : IntPoly P.src.N)
    (hstep : step P.src ρ (.subPlain d a p) = some ρ') (hx : ρ a = some x) (hy : ρ p = some y)
    (ha : σ a = some ca) (hp : σ p = some [c]) (hla : ca.length = x.parts) (h1 : 1 ≤ x.parts) :
    TraceBFV.StepOK P E s ρ ρ' σ
      (σ.set d (bfvSubPlain P.src.t (P.src.modulus x.level) ca c)) (.subPlain d a p) := by
  simp only [step, hx, hy, Option.bind_eq_bind, Option.bind_some, Option.pure_def] at hstep
  have _ := h1
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
    rw [bfvSubPlain_def, phase_padZip_sub, List.map_cons, List.map_nil, phase_singleton,
      ofInt_zero, ofInt_specSMul_natCast]
    apply eq_of_neZero; intro; ring

/-- `stepOK_mulConst_textbook`, with the `ℤ`-action of `Validation.Ring` in the statement. -/
theorem stepOK_mulConst_aux (E : TraceBFV.Budget) (s : IntPoly P.src.N) (ρ ρ' : Env P.src)
    (σ : Trace.CtEnv P) (d a : Var) (c : ℤ) (x : Val P.src) (ca : List (IntPoly P.src.N))
    (hstep : step P.src ρ (.mulConst d a c) = some ρ') (hx : ρ a = some x)
    (ha : σ a = some ca) (hla : ca.length = x.parts) :
    TraceBFV.StepOK P E s ρ ρ' σ (σ.set d (ca.map (c • ·))) (.mulConst d a c) := by
  simp only [step, hx, Option.bind_eq_bind, Option.bind_some, Option.pure_def] at hstep
  cases hstep
  refine ⟨_, _, set_self _ _ _, ?_, rfl, ?_⟩
  · simp [hla]
  · refine ⟨x, ca, hx, ha, ?_⟩
    dsimp only
    unfold Trace.phaseAt
    exact Validation.BFVMul.Ops.phase_map_zsmul _ c ca

section MulConst

-- The locked statement is elaborated without `Validation.Ring` in scope: its `c • ·` is the
-- action from `Spec.NPoly.instSMul`. Removing the later instance here gives the same term.
attribute [-instance] Validation.Ring.instSMulInt

/-- Multiplying every component by the integer constant meets the `mulConst` contract. -/
theorem stepOK_mulConst_textbook (E : TraceBFV.Budget) (s : IntPoly P.src.N) (ρ ρ' : Env P.src)
    (σ : Trace.CtEnv P) (d a : Var) (c : ℤ) (x : Val P.src) (ca : List (IntPoly P.src.N))
    (hstep : step P.src ρ (.mulConst d a c) = some ρ') (hx : ρ a = some x)
    (ha : σ a = some ca) (hla : ca.length = x.parts) :
    TraceBFV.StepOK P E s ρ ρ' σ (σ.set d (ca.map (c • ·))) (.mulConst d a c) :=
  stepOK_mulConst_aux P E s ρ ρ' σ d a c x ca hstep hx ha hla

end MulConst

/-- **Rotation.** Applying `X ↦ X^g` to every component meets the `automorph` contract: the
result is read under `σ_g` of the operand's key. -/
theorem stepOK_automorph_textbook (hP : SchemeParamsOK P) (E : TraceBFV.Budget)
    (s : IntPoly P.src.N) (ρ ρ' : Env P.src) (σ : Trace.CtEnv P) (d a : Var) (g : ℕ)
    (x : Val P.src) (ca : List (IntPoly P.src.N))
    (hstep : step P.src ρ (.automorph d a g) = some ρ') (hx : ρ a = some x)
    (ha : σ a = some ca) (hla : ca.length = x.parts) :
    TraceBFV.StepOK P E s ρ ρ' σ (σ.set d (ca.map (automorph g))) (.automorph d a g) := by
  have _ := hP
  simp only [step, hx, Option.bind_eq_bind, Option.bind_some, Option.pure_def] at hstep
  obtain ⟨hg, h2⟩ := Validation.Trace.guard_bind_eq_some hstep
  cases h2
  refine ⟨_, _, set_self _ _ _, ?_, rfl, ?_⟩
  · simp [hla]
  · refine ⟨x, ca, hx, ha, ?_⟩
    dsimp only
    unfold Trace.phaseAt
    have hmap : ∀ Q : ℕ, (ca.map (automorph g)).map (ofInt Q) =
        (ca.map (ofInt Q)).map (automorph g) := by
      intro Q
      simp only [List.map_map]
      congr 1; funext c; exact ofInt_automorph Q g c
    rw [hmap, automorph_mod, ← automorph_automorph hg, ofInt_automorph, phase_automorph hg]

/-- **Textbook squaring meets the `square` contract** within the textbook budget: `bfvMul` of the
operand with itself. -/
theorem stepOK_square_textbook (hP : SchemeParamsOK P) (E : TraceBFV.Budget)
    (hL : BudgetBFV.mulLift P ≤ E.mulLift) (hR : BudgetBFV.mulRound P ≤ E.mulRound)
    (s : IntPoly P.src.N) (hs : SecretOK P.secretBound s) (ρ ρ' : Env P.src)
    (σ : Trace.CtEnv P) (d a : Var) (x : Val P.src) (ca : List (IntPoly P.src.N))
    (hstep : step P.src ρ (.square d a) = some ρ') (hx : ρ a = some x)
    (ha : σ a = some ca) (hla : ca.length = 2) (h2x : x.parts = 2)
    (hℓ : 1 ≤ x.level) (hℓL : x.level ≤ P.src.qs.length) :
    TraceBFV.StepOK P E s ρ ρ' σ
      (σ.set d (bfvMul P.src.t (P.src.modulus x.level) ca ca)) (.square d a) := by
  have hN : NeZero P.src.N := ⟨by obtain ⟨k, hk⟩ := hP.N_pow2; rw [hk]; positivity⟩
  have hQ : 0 < P.src.modulus x.level := modulus_pos' P hP _
  obtain ⟨a0, a1, rfl⟩ := List.length_eq_two.mp hla
  refine Validation.BFVMul.stepOK_square_approx P hP 0 1 E
    (by unfold BudgetBFV.mulLiftApprox; omega) (by unfold BudgetBFV.mulRoundApprox; omega)
    s hs ρ ρ' σ d a x [a0, a1] hstep hx ha rfl h2x hℓ hℓL [0, 0]
    (bfvMul P.src.t (P.src.modulus x.level) [a0, a1] [a0, a1]) _ rfl rfl ?_ ?_ rfl
  · intro u hu
    have : u = 0 := by simpa using hu
    rw [this, normInf_zero]
  · intro j i
    have hAL : approxLift (P.src.modulus x.level) [a0, a1] [0, 0] =
        [centered (ofInt (P.src.modulus x.level) a0),
         centered (ofInt (P.src.modulus x.level) a1)] := by
      rw [approxLift_two, mul_zero, add_zero, add_zero]
    rw [hAL, Nat.cast_one, mul_one]
    generalize P.src.modulus x.level = Q at hQ ⊢
    rcases j with _ | _ | _ | j
    · exact two_abs_roundDiv_sub_le _ _ hQ
    · exact two_abs_roundDiv_sub_le _ _ hQ
    · exact two_abs_roundDiv_sub_le _ _ hQ
    · show 2 * |(Q : ℤ) * (0 : ℤ) - (P.src.t : ℤ) * (0 : ℤ)| ≤ (Q : ℤ)
      simp

/-! ### The pins: plaintext addition by rounding -/

/-- **Adding `⌊Q·p/t⌉` meets the `addPlain` contract** with deviation at most
`⌊(2·(Q mod t)·b + t)/(2t)⌋` for a stored plaintext polynomial with `‖p‖∞ ≤ b`. -/
theorem stepOK_addPlain_rounded (hP : SchemeParamsOK P) (E : TraceBFV.Budget)
    (s : IntPoly P.src.N) (ρ ρ' : Env P.src)
    (σ : Trace.CtEnv P) (d a p : Var) (x y : Val P.src) (ca : List (IntPoly P.src.N))
    (c : IntPoly P.src.N) (b : ℕ) (hc : normInf c ≤ b)
    (hE : BudgetBFV.plainAddRoundedAt P x.level b ≤ E.plainAdd)
    (hstep : step P.src ρ (.addPlain d a p) = some ρ') (hx : ρ a = some x) (hy : ρ p = some y)
    (ha : σ a = some ca) (hp : σ p = some [c]) (hla : ca.length = x.parts) (h1 : 1 ≤ x.parts) :
    TraceBFV.StepOK P E s ρ ρ' σ
      (σ.set d (bfvAddPlainRounded P.src.t (P.src.modulus x.level) ca c)) (.addPlain d a p) := by
  have _ := hP
  have _ := h1
  simp only [step, hx, hy, Option.bind_eq_bind, Option.bind_some, Option.pure_def] at hstep
  obtain ⟨⟨hy1, -⟩, h2⟩ := Validation.Trace.guard_bind_eq_some hstep
  obtain ⟨m, -, h3⟩ := Option.bind_eq_some_iff.mp h2
  cases h3
  refine ⟨_, _, set_self _ _ _, ?_, rfl, ?_⟩
  · simp [bfvAddPlainRounded_def, length_padZip, hla, hy1]
  · refine ⟨x, y, ca, [c], scaleDev P.src.t (P.src.modulus x.level) c, hx, hy, ha, hp, ?_, ?_⟩
    · rw [normInf_le_iff]
      intro i
      exact (abs_scaleDev_le _ _ b c hc i).trans (Nat.cast_le.mpr hE)
    dsimp only
    rw [Validation.Trace.phaseAt_singleton]
    unfold Trace.phaseAt
    rw [bfvAddPlainRounded_def]
    rw [phase_padZip_add, List.map_cons, List.map_nil, phase_singleton, ofInt_scaleUp]
    apply eq_of_neZero; intro; ring

/-- **Subtracting `⌊Q·p/t⌉` meets the `subPlain` contract** with the same deviation. -/
theorem stepOK_subPlain_rounded (hP : SchemeParamsOK P) (E : TraceBFV.Budget)
    (s : IntPoly P.src.N) (ρ ρ' : Env P.src)
    (σ : Trace.CtEnv P) (d a p : Var) (x y : Val P.src) (ca : List (IntPoly P.src.N))
    (c : IntPoly P.src.N) (b : ℕ) (hc : normInf c ≤ b)
    (hE : BudgetBFV.plainAddRoundedAt P x.level b ≤ E.plainAdd)
    (hstep : step P.src ρ (.subPlain d a p) = some ρ') (hx : ρ a = some x) (hy : ρ p = some y)
    (ha : σ a = some ca) (hp : σ p = some [c]) (hla : ca.length = x.parts) (h1 : 1 ≤ x.parts) :
    TraceBFV.StepOK P E s ρ ρ' σ
      (σ.set d (bfvSubPlainRounded P.src.t (P.src.modulus x.level) ca c)) (.subPlain d a p) := by
  have _ := hP
  have _ := h1
  simp only [step, hx, hy, Option.bind_eq_bind, Option.bind_some, Option.pure_def] at hstep
  obtain ⟨⟨hy1, -⟩, h2⟩ := Validation.Trace.guard_bind_eq_some hstep
  obtain ⟨m, -, h3⟩ := Option.bind_eq_some_iff.mp h2
  cases h3
  refine ⟨_, _, set_self _ _ _, ?_, rfl, ?_⟩
  · simp [bfvSubPlainRounded_def, length_padZip, hla, hy1]
  · refine ⟨x, y, ca, [c], -scaleDev P.src.t (P.src.modulus x.level) c, hx, hy, ha, hp, ?_, ?_⟩
    · rw [normInf_le_iff]
      intro i
      rw [coeff_neg', abs_neg]
      exact (abs_scaleDev_le _ _ b c hc i).trans (Nat.cast_le.mpr hE)
    dsimp only
    rw [Validation.Trace.phaseAt_singleton]
    unfold Trace.phaseAt
    rw [bfvSubPlainRounded_def]
    rw [phase_padZip_sub, List.map_cons, List.map_nil, phase_singleton, ofInt_scaleUp, ofInt_neg]
    apply eq_of_neZero; intro; ring

/-- `plainAddRounded` covers every level of the chain. -/
theorem plainAddRoundedAt_le (b ℓ : ℕ) (h1 : 1 ≤ ℓ) (hℓ : ℓ ≤ P.src.qs.length) :
    BudgetBFV.plainAddRoundedAt P ℓ b ≤ BudgetBFV.plainAddRounded P b := by
  unfold BudgetBFV.plainAddRounded
  apply (Validation.Budget.le_foldl_max _ 0).2
  refine List.mem_map.mpr ⟨ℓ - 1, List.mem_range.mpr (by omega), ?_⟩
  have : ℓ - 1 + 1 = ℓ := by omega
  rw [this]

end Validation.BFVMul
