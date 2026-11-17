import FHE.RNS.Basis
import Mathlib.Data.Rat.Floor
import Mathlib.Tactic.FieldSimp

/-!
# FHE.RNS.BaseConv — fast (approximate) base conversion

Source basis `B = (q₀, …, q_{ℓ-1})`, `Q = ∏ qᵢ`; target moduli `p₀, …, p_{m-1}` (arbitrary
positive integers: they need not be coprime to each other or to `Q`).

**Fast base conversion** (BEHZ 2016 §2.2; HPS 2018 §2.1; the `ApproxSwitchCRTBasis` of OpenFHE):

  `FastBConv(x; B → p)ⱼ = Σᵢ [xᵢ · q̃ᵢ]_{qᵢ} · q̂ᵢ  mod pⱼ`.

Everything is a consequence of one integer. Write `yᵢ = [xᵢ · q̃ᵢ]_{qᵢ}` and
`D = Σᵢ yᵢ · q̂ᵢ ∈ ℤ`. Then `FastBConv(x)ⱼ = D mod pⱼ` (`fastBConv_eq_intCast`) for every `j`, with
the *same* `D` for every target modulus, and `D ≡ X (mod Q)` for every integer `X` with residues
`x` (`Basis.prod_dvd_sum_sub`).

Two conventions for the representative `[·]_{qᵢ}`:

| convention | `yᵢ ∈` | bound on `D` | `D = x̂ + u·Q` with |
|---|---|---|---|
| canonical (`fastBConv`, `fbcInt`; BEHZ, OpenFHE) | `[0, qᵢ)` | `0 ≤ D ≤ ℓ·(Q−1)` | `x̂ = lift x ∈ [0,Q)`: `0 ≤ u < ℓ` (`ℓ > 0`) |
| centred (`fastBConvC`, `fbcIntC`; `valMinAbs`) | `(−qᵢ/2, qᵢ/2]` | `2·|D| ≤ ℓ·Q` | `x̂ = liftC x ∈ (−Q/2, Q/2]`: `2·|u| ≤ ℓ`; `x̂ = lift x`: `−ℓ−2 < 2u ≤ ℓ` |

The canonical overflow is also `u = ⌊Σᵢ yᵢ/qᵢ⌋` (HPS 2018, §2.2: `D/Q = Σ yᵢ/qᵢ` and
`lift x / Q ∈ [0,1)`), which is `fbcOverflow_eq_floor`.
-/

namespace FHE.RNS

open Finset

namespace Basis

variable {ℓ : ℕ} (B : Basis ℓ)

/-- The integer behind canonical fast base conversion: `Σᵢ [xᵢ·q̃ᵢ]_{qᵢ} · q̂ᵢ` with
`[·] ∈ [0, qᵢ)`. -/
def fbcInt (x : (i : Fin ℓ) → ZMod (B.q i)) : ℤ :=
  ∑ i, ((x i * B.hatInv i).val : ℤ) * B.hat i

/-- The integer behind centred fast base conversion: `Σᵢ [xᵢ·q̃ᵢ]_{qᵢ} · q̂ᵢ` with
`[·] ∈ (−qᵢ/2, qᵢ/2]` (`ZMod.valMinAbs`). -/
def fbcIntC (x : (i : Fin ℓ) → ZMod (B.q i)) : ℤ :=
  ∑ i, (x i * B.hatInv i).valMinAbs * B.hat i

/-- **Fast base conversion** `B → p`, canonical representatives (BEHZ / OpenFHE convention).
Computable; `hat` is reduced mod `pⱼ` by the cast. -/
def fastBConv {m : ℕ} (p : Fin m → ℕ) (x : (i : Fin ℓ) → ZMod (B.q i)) :
    (j : Fin m) → ZMod (p j) :=
  fun j => ∑ i, (((x i * B.hatInv i).val : ℕ) : ZMod (p j)) * (B.hat i : ZMod (p j))

/-- **Fast base conversion** `B → p` with centred representatives. -/
def fastBConvC {m : ℕ} (p : Fin m → ℕ) (x : (i : Fin ℓ) → ZMod (B.q i)) :
    (j : Fin m) → ZMod (p j) :=
  fun j => ∑ i, (((x i * B.hatInv i).valMinAbs : ℤ) : ZMod (p j)) * (B.hat i : ZMod (p j))

theorem fastBConv_eq_intCast {m : ℕ} (p : Fin m → ℕ) (x : (i : Fin ℓ) → ZMod (B.q i))
    (j : Fin m) : B.fastBConv p x j = (B.fbcInt x : ZMod (p j)) := by
  simp [fastBConv, fbcInt]

theorem fastBConvC_eq_intCast {m : ℕ} (p : Fin m → ℕ) (x : (i : Fin ℓ) → ZMod (B.q i))
    (j : Fin m) : B.fastBConvC p x j = (B.fbcIntC x : ZMod (p j)) := by
  simp [fastBConvC, fbcIntC]

/-! ### Congruence: `D ≡ X (mod Q)` -/

theorem prod_dvd_fbcInt_sub (x : (i : Fin ℓ) → ZMod (B.q i)) (X : ℤ)
    (hX : ∀ i, (X : ZMod (B.q i)) = x i) : (B.prod : ℤ) ∣ B.fbcInt x - X :=
  B.prod_dvd_sum_sub x X hX _ fun i => by simp

theorem prod_dvd_fbcIntC_sub (x : (i : Fin ℓ) → ZMod (B.q i)) (X : ℤ)
    (hX : ∀ i, (X : ZMod (B.q i)) = x i) : (B.prod : ℤ) ∣ B.fbcIntC x - X :=
  B.prod_dvd_sum_sub x X hX _ fun _ => ZMod.coe_valMinAbs _

/-- The residues of `D` modulo the source moduli are `x` (`D` is a lift of `x`). -/
theorem fbcInt_residue (x : (i : Fin ℓ) → ZMod (B.q i)) (i : Fin ℓ) :
    (B.fbcInt x : ZMod (B.q i)) = x i := by
  have h := B.prod_dvd_fbcInt_sub x _ (B.lift_residue x)
  have h' : ((B.q i : ℕ) : ℤ) ∣ B.fbcInt x - (B.lift x : ℤ) :=
    (Int.natCast_dvd_natCast.mpr (B.q_dvd_prod i)).trans h
  rw [← B.lift_residue x i, ZMod.intCast_eq_intCast_iff_dvd_sub]
  exact (dvd_neg.mpr h').trans (by ring_nf; exact dvd_rfl)

theorem fbcIntC_residue (x : (i : Fin ℓ) → ZMod (B.q i)) (i : Fin ℓ) :
    (B.fbcIntC x : ZMod (B.q i)) = x i := by
  have h := B.prod_dvd_fbcIntC_sub x _ (B.lift_residue x)
  have h' : ((B.q i : ℕ) : ℤ) ∣ B.fbcIntC x - (B.lift x : ℤ) :=
    (Int.natCast_dvd_natCast.mpr (B.q_dvd_prod i)).trans h
  rw [← B.lift_residue x i, ZMod.intCast_eq_intCast_iff_dvd_sub]
  exact (dvd_neg.mpr h').trans (by ring_nf; exact dvd_rfl)

/-! ### Bounds on `D` -/

/-- Canonical: `0 ≤ D`. -/
theorem fbcInt_nonneg (x : (i : Fin ℓ) → ZMod (B.q i)) : 0 ≤ B.fbcInt x :=
  Finset.sum_nonneg fun i _ => by positivity

/-- Canonical: `D ≤ ℓ·(Q − 1)`. -/
theorem fbcInt_le (x : (i : Fin ℓ) → ZMod (B.q i)) :
    B.fbcInt x ≤ ℓ * ((B.prod : ℤ) - 1) := by
  unfold fbcInt
  calc ∑ i, ((x i * B.hatInv i).val : ℤ) * B.hat i ≤ ∑ _i : Fin ℓ, ((B.prod : ℤ) - 1) := by
        refine Finset.sum_le_sum fun i _ => ?_
        have h1 : ((x i * B.hatInv i).val : ℤ) + 1 ≤ B.q i := by
          have := ZMod.val_lt (x i * B.hatInv i); omega
        have h2 : (1 : ℤ) ≤ B.hat i := by have := B.hat_pos i; omega
        have h3 : ((B.q i : ℤ)) * B.hat i = B.prod := by exact_mod_cast B.q_mul_hat i
        nlinarith
    _ = ℓ * ((B.prod : ℤ) - 1) := by simp; ring

/-- Centred: `−ℓ·Q ≤ 2·D ≤ ℓ·Q` (each term lies in `(−Q/2, Q/2]`). -/
theorem fbcIntC_bounds (x : (i : Fin ℓ) → ZMod (B.q i)) :
    -(ℓ * (B.prod : ℤ)) ≤ 2 * B.fbcIntC x ∧ 2 * B.fbcIntC x ≤ ℓ * B.prod := by
  unfold fbcIntC
  rw [Finset.mul_sum]
  have hterm : ∀ i, -(B.prod : ℤ) ≤ 2 * ((x i * B.hatInv i).valMinAbs * B.hat i) ∧
      2 * ((x i * B.hatInv i).valMinAbs * B.hat i) ≤ B.prod := by
    intro i
    have hv := ZMod.valMinAbs_mem_Ioc (x i * B.hatInv i)
    simp only [Set.mem_Ioc] at hv
    have h2 : (0 : ℤ) ≤ B.hat i := by positivity
    have h3 : ((B.q i : ℤ)) * B.hat i = B.prod := by exact_mod_cast B.q_mul_hat i
    constructor <;> nlinarith [hv.1, hv.2]
  constructor
  · calc -(ℓ * (B.prod : ℤ)) = ∑ _i : Fin ℓ, -(B.prod : ℤ) := by simp
      _ ≤ _ := Finset.sum_le_sum fun i _ => (hterm i).1
  · calc _ ≤ ∑ _i : Fin ℓ, (B.prod : ℤ) := Finset.sum_le_sum fun i _ => (hterm i).2
      _ = ℓ * B.prod := by simp

theorem two_mul_abs_fbcIntC_le (x : (i : Fin ℓ) → ZMod (B.q i)) :
    2 * |B.fbcIntC x| ≤ ℓ * B.prod := by
  obtain ⟨h1, h2⟩ := B.fbcIntC_bounds x
  have := abs_le.mpr ⟨h1, h2⟩
  rwa [abs_mul, abs_two] at this

/-- Centred, `ℓ > 0`: the lower bound is strict, `−ℓ·Q < 2·D`. -/
theorem fbcIntC_lower_strict (hℓ : 0 < ℓ) (x : (i : Fin ℓ) → ZMod (B.q i)) :
    -(ℓ * (B.prod : ℤ)) < 2 * B.fbcIntC x := by
  unfold fbcIntC
  rw [Finset.mul_sum]
  calc -(ℓ * (B.prod : ℤ)) = ∑ _i : Fin ℓ, -(B.prod : ℤ) := by simp
    _ < _ := by
      refine Finset.sum_lt_sum_of_nonempty ⟨⟨0, hℓ⟩, mem_univ _⟩ fun i _ => ?_
      have hv := ZMod.valMinAbs_mem_Ioc (x i * B.hatInv i)
      simp only [Set.mem_Ioc] at hv
      have h2 : (0 : ℤ) < B.hat i := by exact_mod_cast B.hat_pos i
      have h3 : ((B.q i : ℤ)) * B.hat i = B.prod := by exact_mod_cast B.q_mul_hat i
      nlinarith [hv.1]

/-! ### The overflow `u` -/

/-- The canonical overflow `u = (D − lift x) / Q`. -/
def fbcOverflow (x : (i : Fin ℓ) → ZMod (B.q i)) : ℤ := (B.fbcInt x - B.lift x) / B.prod

/-- The centred overflow `u = (D_C − liftC x) / Q`. -/
def fbcOverflowC (x : (i : Fin ℓ) → ZMod (B.q i)) : ℤ := (B.fbcIntC x - B.liftC x) / B.prod

theorem fbcInt_eq (x : (i : Fin ℓ) → ZMod (B.q i)) :
    B.fbcInt x = B.lift x + B.fbcOverflow x * B.prod := by
  have := Int.ediv_mul_cancel (B.prod_dvd_fbcInt_sub x _ (B.lift_residue x))
  unfold fbcOverflow; linarith

theorem fbcIntC_eq (x : (i : Fin ℓ) → ZMod (B.q i)) :
    B.fbcIntC x = B.liftC x + B.fbcOverflowC x * B.prod := by
  have := Int.ediv_mul_cancel (B.prod_dvd_fbcIntC_sub x _ (B.liftC_residue x))
  unfold fbcOverflowC; linarith

/-- **Canonical fast base conversion, exact characterisation.** For `ℓ > 0` source limbs,
`FastBConv(x; B → p)` is the residue vector of the integer `x̃ + u·Q`, where `x̃ = lift x ∈ [0, Q)`
is the canonical representative of `x` and `u = fbcOverflow x` satisfies `0 ≤ u < ℓ`; `u` does
not depend on the target moduli. -/
theorem fastBConv_spec (hℓ : 0 < ℓ) {m : ℕ} (p : Fin m → ℕ) (x : (i : Fin ℓ) → ZMod (B.q i)) :
    (∀ j, B.fastBConv p x j = ((B.lift x + B.fbcOverflow x * B.prod : ℤ) : ZMod (p j))) ∧
      0 ≤ B.fbcOverflow x ∧ B.fbcOverflow x < ℓ := by
  have hQ : (0 : ℤ) < B.prod := by exact_mod_cast B.prod_pos
  have he := B.fbcInt_eq x
  have hlo := B.fbcInt_nonneg x
  have hhi := B.fbcInt_le x
  have hl : ((B.lift x : ℕ) : ℤ) < B.prod := by exact_mod_cast B.lift_lt x
  have hl0 : (0 : ℤ) ≤ (B.lift x : ℕ) := by positivity
  have hℓ' : (1 : ℤ) ≤ ℓ := by exact_mod_cast hℓ
  refine ⟨fun j => by rw [fastBConv_eq_intCast, ← he], ?_, ?_⟩
  · by_contra h
    push Not at h
    have : B.fbcOverflow x * B.prod ≤ -(B.prod : ℤ) := by nlinarith
    linarith
  · by_contra h
    push Not at h
    have : (ℓ : ℤ) * B.prod ≤ B.fbcOverflow x * B.prod := by nlinarith
    nlinarith

/-- **Centred fast base conversion, exact characterisation.** `FastBConvC(x; B → p)` is the
residue vector of `x̄ + u·Q`, where `x̄ = liftC x ∈ (−Q/2, Q/2]` is the centred representative
and `u = fbcOverflowC x` satisfies `2·|u| ≤ ℓ`, i.e. `|u| ≤ ⌊ℓ/2⌋`. No hypothesis on `ℓ`. -/
theorem fastBConvC_spec {m : ℕ} (p : Fin m → ℕ) (x : (i : Fin ℓ) → ZMod (B.q i)) :
    (∀ j, B.fastBConvC p x j = ((B.liftC x + B.fbcOverflowC x * B.prod : ℤ) : ZMod (p j))) ∧
      2 * |B.fbcOverflowC x| ≤ ℓ := by
  have hQ : (0 : ℤ) < B.prod := by exact_mod_cast B.prod_pos
  have he := B.fbcIntC_eq x
  obtain ⟨hlo, hhi⟩ := B.fbcIntC_bounds x
  obtain ⟨hc1, hc2⟩ := B.liftC_bounds x
  refine ⟨fun j => by rw [fastBConvC_eq_intCast, ← he], ?_⟩
  -- `2uQ = 2D − 2x̄ ∈ (−(ℓ+1)Q, (ℓ+1)Q)`, so `|2u| < ℓ + 1`.
  set u := B.fbcOverflowC x
  have h1 : 2 * u * B.prod < (ℓ + 1) * B.prod := by nlinarith
  have h1' : 2 * u < ℓ + 1 := lt_of_mul_lt_mul_right h1 hQ.le
  have h2' : -((ℓ : ℤ) + 1) < 2 * u ∨ (ℓ = 0 ∧ -1 ≤ 2 * u) := by
    rcases Nat.eq_zero_or_pos ℓ with h0 | hpos
    · right
      refine ⟨h0, ?_⟩
      have : -(B.prod : ℤ) ≤ 2 * u * B.prod := by
        nlinarith
      have : (-1 : ℤ) * B.prod ≤ 2 * u * B.prod := by linarith
      exact le_of_mul_le_mul_right this hQ
    · left
      have hs := B.fbcIntC_lower_strict hpos x
      have : -((ℓ : ℤ) + 1) * B.prod < 2 * u * B.prod := by nlinarith
      exact lt_of_mul_lt_mul_right this hQ.le
  rcases abs_cases u with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;> omega

/-- Centred terms with the canonical representative: `FastBConvC(x)` is the residue vector of
`x̃ + u·Q` with `x̃ = lift x ∈ [0, Q)` and `−ℓ − 2 < 2u ≤ ℓ`. -/
theorem fastBConvC_spec_lift {m : ℕ} (p : Fin m → ℕ) (x : (i : Fin ℓ) → ZMod (B.q i)) :
    ∃ u : ℤ, (∀ j, B.fastBConvC p x j = ((B.lift x + u * B.prod : ℤ) : ZMod (p j))) ∧
      -(ℓ : ℤ) - 2 < 2 * u ∧ 2 * u ≤ ℓ := by
  have hQ : (0 : ℤ) < B.prod := by exact_mod_cast B.prod_pos
  have hd := B.prod_dvd_fbcIntC_sub x _ (B.lift_residue x)
  set u := (B.fbcIntC x - B.lift x) / B.prod
  have he : B.fbcIntC x = B.lift x + u * B.prod := by
    have := Int.ediv_mul_cancel hd; linarith
  obtain ⟨hlo, hhi⟩ := B.fbcIntC_bounds x
  have hl : ((B.lift x : ℕ) : ℤ) < B.prod := by exact_mod_cast B.lift_lt x
  have hl0 : (0 : ℤ) ≤ (B.lift x : ℕ) := by positivity
  refine ⟨u, fun j => by rw [fastBConvC_eq_intCast, ← he], ?_, ?_⟩
  · have : (-(ℓ : ℤ) - 2) * B.prod < 2 * u * B.prod := by nlinarith
    exact lt_of_mul_lt_mul_right this hQ.le
  · have : 2 * u * B.prod ≤ ℓ * B.prod := by nlinarith
    exact le_of_mul_le_mul_right this hQ

/-- HPS 2018: the canonical overflow is `u = ⌊Σᵢ yᵢ / qᵢ⌋` with `yᵢ = [xᵢ·q̃ᵢ]_{qᵢ} ∈ [0, qᵢ)`. -/
theorem fbcOverflow_eq_floor (x : (i : Fin ℓ) → ZMod (B.q i)) :
    B.fbcOverflow x = ⌊∑ i, ((x i * B.hatInv i).val : ℚ) / B.q i⌋ := by
  have hQ : (0 : ℚ) < B.prod := by exact_mod_cast B.prod_pos
  have hsum : ∑ i, ((x i * B.hatInv i).val : ℚ) / B.q i = (B.fbcInt x : ℚ) / B.prod := by
    rw [eq_div_iff hQ.ne', Finset.sum_mul]
    simp only [fbcInt, Int.cast_sum, Int.cast_mul, Int.cast_natCast]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hq : (B.q i : ℚ) ≠ 0 := by exact_mod_cast (B.pos i).ne'
    have h3 : ((B.q i : ℚ)) * B.hat i = B.prod := by exact_mod_cast B.q_mul_hat i
    rw [← h3]; field_simp
  rw [hsum, B.fbcInt_eq x]
  symm
  rw [Int.floor_eq_iff]
  have hl : ((B.lift x : ℕ) : ℚ) < B.prod := by exact_mod_cast B.lift_lt x
  have hl0 : (0 : ℚ) ≤ (B.lift x : ℕ) := by positivity
  simp only [Int.cast_add, Int.cast_mul, Int.cast_natCast]
  rw [add_div, mul_div_cancel_right₀ _ hQ.ne']
  constructor
  · have : (0 : ℚ) ≤ (B.lift x : ℚ) / B.prod := by positivity
    linarith
  · have : (B.lift x : ℚ) / B.prod < 1 := (div_lt_one hQ).mpr hl
    linarith

end Basis
end FHE.RNS
