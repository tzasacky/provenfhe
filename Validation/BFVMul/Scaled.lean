import Challenge.BFVMul
import Validation.BFVMul.Ops

/-!
# Validation.BFVMul.Scaled — plaintext addition of any polynomial within one unit of `Q·p/t`

Proofs of `plainAddScaledAt_le` (as locked) and of `stepOK_addPlain_scaled`,
`stepOK_subPlain_scaled` of `Challenge.BFVMul` **with the extra hypothesis `0 < P.src.t`**.

With `Q = t·Δ + r` and `δ = w − Δ·p`: `t·δ = (t·w − Q·p) + r·p`, so `|t·δ| ≤ t + r·b` for
`|p| ≤ b`, and `|δ| ≤ ⌊r·b/t⌋ + 1` (`abs_scaled_sub_le`).

**Why `t > 0` is needed.** The two locked step statements are false at `t = 0`, which an
earlier version of `SchemeParamsOK` allowed: then `hw` only says `Q·c = 0` (so `c = 0`), `w` is unconstrained,
`plainAddScaledAt = 1`, and the contract would need `δ ≡ w (mod Q)` with `‖δ‖∞ ≤ 1`. For
instance `N = 1`, `qs = [5]`, `t = 0`, `c = 0`, `w = 2`, `b = 0`,
`E.plainAdd = 1`. `0 < P.src.t` (or `P.src.kind = .bfv`, which gives `2 ≤ t` with `hP`) is
enough.

The helper lemmas are in the namespace `Validation.BFVMul.Scaled`; the pins in
`Validation.BFVMul`.
-/

namespace Validation.BFVMul.Scaled
open Spec NPoly Scheme Source Correct Challenge.BFV Challenge.BFVMul
open Validation.Ring Validation.Scheme Validation.Source Validation.BFV

variable {N : ℕ}

/-- `|w − ⌊Q/t⌋·p| ≤ ⌊(Q mod t)·b/t⌋ + 1` for `|t·w − Q·p| ≤ t`, `|p| ≤ b`, `t > 0`. -/
theorem abs_scaled_sub_le (t Q b : ℕ) (ht : 0 < t) (w p : ℤ) (hp : |p| ≤ b)
    (hw : |(t : ℤ) * w - (Q : ℤ) * p| ≤ t) :
    |w - ((Q / t : ℕ) : ℤ) * p| ≤ ((Q % t * b / t + 1 : ℕ) : ℤ) := by
  have ht' : (0 : ℤ) < t := by exact_mod_cast ht
  have hQ : (Q : ℤ) = (t : ℤ) * ((Q / t : ℕ) : ℤ) + ((Q % t : ℕ) : ℤ) := by
    exact_mod_cast (Nat.div_add_mod Q t).symm
  have hK : ((Q % t * b : ℕ) : ℤ) < (t : ℤ) * (((Q % t * b / t : ℕ) : ℤ) + 1) := by
    exact_mod_cast Nat.lt_mul_div_succ (Q % t * b) ht
  rw [Nat.cast_add, Nat.cast_one]
  generalize ((Q % t * b / t : ℕ) : ℤ) = K at hK ⊢
  rw [Nat.cast_mul] at hK
  generalize ((Q / t : ℕ) : ℤ) = Δ at hQ ⊢
  have hr0 : (0 : ℤ) ≤ ((Q % t : ℕ) : ℤ) := by positivity
  generalize ((Q % t : ℕ) : ℤ) = r at hQ hr0 hK
  have hrp : |r * p| ≤ r * b := by
    rw [abs_mul, abs_of_nonneg hr0]
    exact mul_le_mul_of_nonneg_left hp hr0
  have e : (t : ℤ) * (w - Δ * p) = ((t : ℤ) * w - (Q : ℤ) * p) + r * p := by rw [hQ]; ring
  have h1 : (t : ℤ) * |w - Δ * p| ≤ t + r * b := by
    rw [← abs_of_pos ht', ← abs_mul, e, abs_of_pos ht']
    exact (abs_add_le _ _).trans (add_le_add hw hrp)
  by_contra h
  have h2 : K + 1 + 1 ≤ |w - Δ * p| := Int.add_one_le_iff.mpr (not_le.mp h)
  have h3 := mul_le_mul_of_nonneg_left h2 ht'.le
  linarith

/-- The deviation of `w` from `⌊Q/t⌋·p`, coefficient by coefficient. -/
def dev (t Q : ℕ) (w p : IntPoly N) : IntPoly N :=
  ⟨fun i => w.coeff i - ((Q / t : ℕ) : ℤ) * p.coeff i⟩

theorem abs_dev_le (t Q b : ℕ) (ht : 0 < t) (w p : IntPoly N) (hp : normInf p ≤ b)
    (hw : ∀ i, |(t : ℤ) * w.coeff i - (Q : ℤ) * p.coeff i| ≤ t) (i : Fin N) :
    |(dev t Q w p).coeff i| ≤ ((Q % t * b / t + 1 : ℕ) : ℤ) :=
  abs_scaled_sub_le t Q b ht _ _ ((normInf_le_iff _ _).mp hp i) (hw i)

/-- `w ≡ ⌊Q/t⌋·p + δ (mod Q')` with `δ = dev t Q w p`, for every modulus `Q'`. -/
theorem ofInt_eq_smul_add_dev (Q' t Q : ℕ) (w p : IntPoly N) :
    ofInt Q' w = ((Q / t : ℕ) : ZMod Q') • ofInt Q' p + ofInt Q' (dev t Q w p) := by
  ext i
  show ((w.coeff i : ℤ) : ZMod Q') =
    ((Q / t : ℕ) : ZMod Q') * ((p.coeff i : ℤ) : ZMod Q') +
      ((w.coeff i - ((Q / t : ℕ) : ℤ) * p.coeff i : ℤ) : ZMod Q')
  rw [Int.cast_sub, Int.cast_mul, Int.cast_natCast]
  ring

end Validation.BFVMul.Scaled

namespace Validation.BFVMul
open Spec NPoly Scheme Source Correct Challenge.BFV Challenge.BFVMul
open Validation.Ring Validation.Scheme Validation.Source Validation.BFV
open Validation.BFVMul.Scaled

variable (P : FullParams)

/-- **Adding any polynomial within one unit of `Q·p/t` meets the `addPlain` contract** with
deviation at most `⌊(Q mod t)·b/t⌋ + 1`. Amended: `ht : 0 < P.src.t` (module docstring). -/
theorem stepOK_addPlain_scaled (hP : SchemeParamsOK P) (ht : 0 < P.src.t)
    (E : TraceBFV.Budget)
    (s : IntPoly P.src.N) (ρ ρ' : Env P.src)
    (σ : Trace.CtEnv P) (d a p : Var) (x y : Val P.src) (ca : List (IntPoly P.src.N))
    (c w : IntPoly P.src.N) (b : ℕ) (hc : normInf c ≤ b)
    (hw : ∀ i, |(P.src.t : ℤ) * w.coeff i - (P.src.modulus x.level : ℤ) * c.coeff i| ≤ P.src.t)
    (hE : BudgetBFV.plainAddScaledAt P x.level b ≤ E.plainAdd)
    (hstep : step P.src ρ (.addPlain d a p) = some ρ') (hx : ρ a = some x) (hy : ρ p = some y)
    (ha : σ a = some ca) (hp : σ p = some [c]) (hla : ca.length = x.parts) (h1 : 1 ≤ x.parts) :
    TraceBFV.StepOK P E s ρ ρ' σ
      (σ.set d (Challenge.Source.padZip (· + ·) ca [w])) (.addPlain d a p) := by
  have _ := hP
  have _ := h1
  simp only [step, hx, hy, Option.bind_eq_bind, Option.bind_some, Option.pure_def] at hstep
  obtain ⟨⟨hy1, -⟩, h2⟩ := Validation.Trace.guard_bind_eq_some hstep
  obtain ⟨m, -, h3⟩ := Option.bind_eq_some_iff.mp h2
  cases h3
  refine ⟨_, _, set_self _ _ _, ?_, rfl, ?_⟩
  · simp [length_padZip, hla, hy1]
  · refine ⟨x, y, ca, [c], dev P.src.t (P.src.modulus x.level) w c, hx, hy, ha, hp, ?_, ?_⟩
    · rw [normInf_le_iff]
      intro i
      exact (abs_dev_le _ _ b ht w c hc hw i).trans (Nat.cast_le.mpr hE)
    dsimp only
    rw [Validation.Trace.phaseAt_singleton]
    unfold Trace.phaseAt
    rw [phase_padZip_add, List.map_cons, List.map_nil, phase_singleton,
      ofInt_eq_smul_add_dev _ P.src.t (P.src.modulus x.level) w c]
    apply eq_of_neZero; intro; ring

/-- **Subtracting any polynomial within one unit of `Q·p/t` meets the `subPlain` contract** with
the same deviation. Amended: `ht : 0 < P.src.t` (module docstring). -/
theorem stepOK_subPlain_scaled (hP : SchemeParamsOK P) (ht : 0 < P.src.t)
    (E : TraceBFV.Budget)
    (s : IntPoly P.src.N) (ρ ρ' : Env P.src)
    (σ : Trace.CtEnv P) (d a p : Var) (x y : Val P.src) (ca : List (IntPoly P.src.N))
    (c w : IntPoly P.src.N) (b : ℕ) (hc : normInf c ≤ b)
    (hw : ∀ i, |(P.src.t : ℤ) * w.coeff i - (P.src.modulus x.level : ℤ) * c.coeff i| ≤ P.src.t)
    (hE : BudgetBFV.plainAddScaledAt P x.level b ≤ E.plainAdd)
    (hstep : step P.src ρ (.subPlain d a p) = some ρ') (hx : ρ a = some x) (hy : ρ p = some y)
    (ha : σ a = some ca) (hp : σ p = some [c]) (hla : ca.length = x.parts) (h1 : 1 ≤ x.parts) :
    TraceBFV.StepOK P E s ρ ρ' σ
      (σ.set d (Challenge.Source.padZip (· - ·) ca [w])) (.subPlain d a p) := by
  have _ := hP
  have _ := h1
  simp only [step, hx, hy, Option.bind_eq_bind, Option.bind_some, Option.pure_def] at hstep
  obtain ⟨⟨hy1, -⟩, h2⟩ := Validation.Trace.guard_bind_eq_some hstep
  obtain ⟨m, -, h3⟩ := Option.bind_eq_some_iff.mp h2
  cases h3
  refine ⟨_, _, set_self _ _ _, ?_, rfl, ?_⟩
  · simp [length_padZip, hla, hy1]
  · refine ⟨x, y, ca, [c], -dev P.src.t (P.src.modulus x.level) w c, hx, hy, ha, hp, ?_, ?_⟩
    · rw [normInf_le_iff]
      intro i
      rw [coeff_neg', abs_neg]
      exact (abs_dev_le _ _ b ht w c hc hw i).trans (Nat.cast_le.mpr hE)
    dsimp only
    rw [Validation.Trace.phaseAt_singleton]
    unfold Trace.phaseAt
    rw [phase_padZip_sub, List.map_cons, List.map_nil, phase_singleton,
      ofInt_eq_smul_add_dev _ P.src.t (P.src.modulus x.level) w c, ofInt_neg]
    apply eq_of_neZero; intro; ring

/-- `plainAddScaled` covers every level of the chain. -/
theorem plainAddScaledAt_le (b ℓ : ℕ) (h1 : 1 ≤ ℓ) (hℓ : ℓ ≤ P.src.qs.length) :
    BudgetBFV.plainAddScaledAt P ℓ b ≤ BudgetBFV.plainAddScaled P b := by
  unfold BudgetBFV.plainAddScaled
  apply (Validation.Budget.le_foldl_max _ 0).2
  refine List.mem_map.mpr ⟨ℓ - 1, List.mem_range.mpr (by omega), ?_⟩
  have : ℓ - 1 + 1 = ℓ := by omega
  rw [this]

end Validation.BFVMul
