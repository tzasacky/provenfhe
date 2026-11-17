import FHE.RNS.BaseConv

/-!
# FHE.RNS.ModDown — exact RNS division by the last prime, BGV modulus switch, ModDown by `P`

All algorithms here are instances of one per-limb step. Given residues `xᵢ` of an integer `X`
modulo `qᵢ`, a divisor `P` coprime to every `qᵢ`, and a *correction* `d` with `P ∣ X + d`, the
residues of the exact quotient `(X + d)/P` are

  `(xᵢ + [d]_{qᵢ}) · P⁻¹ mod qᵢ`                                  (`modDownWith_spec`).

Sign convention: we write the correction as `+d` (so `P·y = X + d`) to match `divq_core` and the
textbook definitions `Challenge.Source.bgvModSwitchComp` and the textbook rescaling `(c − [c]_q) / q`. The algorithms are
choices of `d`:

| algorithm | `P` | `d` | bound | extra |
|---|---|---|---|---|
| `rescale` | `q_ℓ` | `−[X]_{q_ℓ}` centred | `|d| ≤ ⌊q_ℓ/2⌋` | |
| `rescaleFloor` | `q_ℓ` | `−[X]_{q_ℓ}` in `[0,q_ℓ)` | `−q_ℓ < d ≤ 0` | `y = ⌊X/q_ℓ⌋` exactly |
| `bgvModSwitch t` | `q_ℓ` | `t·[−X·t⁻¹]_{q_ℓ}` centred | `|d| ≤ t·⌊q_ℓ/2⌋` | `y ≡ q_ℓ⁻¹·X (mod t)` |
| `modDown` (canonical FastBConv) | `P` | `−FastBConv([X]_P)` | `−k(P−1) ≤ d ≤ 0` | `y = ⌊X/P⌋ − u`, `0 ≤ u < k` |
| `modDownC` (centred FastBConv) | `P` | `−FastBConvC([X]_P)` | `2|d| ≤ k·P` | |
| `bgvModDown t` (canonical) | `P` | `−t·FastBConv([X·t⁻¹]_P)` | `−t·k(P−1) ≤ d ≤ 0` | `y ≡ P⁻¹·X (mod t)` |
| `bgvModDownC t` (centred) | `P` | `t·FastBConvC([−X·t⁻¹]_P)` | `2|d| ≤ t·k·P` | `y ≡ P⁻¹·X (mod t)` |

Every statement holds for **every** integer `X` with the given residues, not only for the
canonical or centred representative: the noise analysis can take `X` to be whatever integer lift
it is tracking (e.g. a coefficient of `c₀ + s·c₁` before reduction).
-/

namespace FHE.RNS

open Finset

/-- **Exact division in one limb.** If `P ∣ Z` and `P` is a unit mod `n`, then
`[Z]_n · P⁻¹ = [Z / P]_n`. -/
theorem intCast_mul_inv_eq_div {n P : ℕ} (hcop : Nat.Coprime P n) {Z : ℤ} (hZ : (P : ℤ) ∣ Z) :
    (Z : ZMod n) * (P : ZMod n)⁻¹ = ((Z / P : ℤ) : ZMod n) := by
  obtain ⟨w, rfl⟩ := hZ
  rcases Nat.eq_zero_or_pos P with h0 | hP
  · subst h0
    have : Nat.Coprime 0 n := hcop
    rw [Nat.coprime_zero_left] at this
    subst this
    exact Subsingleton.elim _ _
  rw [Int.mul_ediv_cancel_left _ (by exact_mod_cast hP.ne')]
  push_cast
  rw [mul_comm, ← mul_assoc, mul_comm _ (P : ZMod n), ZMod.coe_mul_inv_eq_one P hcop, one_mul]

/-- Message bookkeeping mod `t`: if `P·y = X + t·e` and `gcd(t, P) = 1` then
`y ≡ P⁻¹·X (mod t)`. -/
theorem intCast_eq_mul_inv_of_mul_eq {t P : ℕ} (htP : Nat.Coprime t P) {y X e : ℤ}
    (h : (P : ℤ) * y = X + t * e) : (y : ZMod t) = (X : ZMod t) * (P : ZMod t)⁻¹ := by
  have h1 := congrArg (Int.cast : ℤ → ZMod t) h
  simp only [Int.cast_mul, Int.cast_add, Int.cast_natCast, ZMod.natCast_self, zero_mul,
    add_zero] at h1
  rw [← h1, mul_comm (P : ZMod t), mul_assoc, ZMod.coe_mul_inv_eq_one _ htP.symm, mul_one]

/-! ### The generic per-limb step -/

namespace Basis

variable {ℓ : ℕ} (C : Basis ℓ)

/-- `(xᵢ + dᵢ) · P⁻¹ mod qᵢ` for every limb. -/
def modDownWith (P : ℕ) (x d : (i : Fin ℓ) → ZMod (C.q i)) : (i : Fin ℓ) → ZMod (C.q i) :=
  fun i => (x i + d i) * (P : ZMod (C.q i))⁻¹

/-- **Generic exact division.** If `X` has residues `x`, the correction residues are those of an
integer `d` with `P ∣ X + d`, and `P` is coprime to every `qᵢ`, then the output is the residue
vector of the exact quotient `(X + d) / P`. -/
theorem modDownWith_spec {P : ℕ} (hcop : ∀ i, Nat.Coprime P (C.q i))
    {x dr : (i : Fin ℓ) → ZMod (C.q i)} {X d : ℤ} (hX : ∀ i, (X : ZMod (C.q i)) = x i)
    (hd : ∀ i, (d : ZMod (C.q i)) = dr i) (hdiv : (P : ℤ) ∣ X + d) (i : Fin ℓ) :
    C.modDownWith P x dr i = (((X + d) / P : ℤ) : ZMod (C.q i)) := by
  rw [modDownWith, ← hX i, ← hd i, ← Int.cast_add]
  exact intCast_mul_inv_eq_div (hcop i) hdiv

/-! ### Rescaling / modulus switching by the last modulus -/

variable {ℓ : ℕ} (B : Basis (ℓ + 1))

/-- Drop the last limb and divide by `q_ℓ`, with correction `d`:
`yᵢ = (xᵢ + [d]_{qᵢ}) · q_ℓ⁻¹ mod qᵢ` for `i < ℓ`. -/
def rescaleWith (x : (i : Fin (ℓ + 1)) → ZMod (B.q i)) (d : ℤ) :
    (i : Fin ℓ) → ZMod (B.dropLast.q i) :=
  B.dropLast.modDownWith B.last (fun i => x i.castSucc) (fun i => (d : ZMod (B.dropLast.q i)))

/-- Rescale (division by the last prime): correction
`d = −[x_ℓ]` with the centred representative `[x_ℓ] ∈ (−q_ℓ/2, q_ℓ/2]`. -/
def rescale (x : (i : Fin (ℓ + 1)) → ZMod (B.q i)) : (i : Fin ℓ) → ZMod (B.dropLast.q i) :=
  B.rescaleWith x (-(x (Fin.last ℓ)).valMinAbs)

/-- Rescale with the canonical representative `[x_ℓ] ∈ [0, q_ℓ)`: floor division. -/
def rescaleFloor (x : (i : Fin (ℓ + 1)) → ZMod (B.q i)) : (i : Fin ℓ) → ZMod (B.dropLast.q i) :=
  B.rescaleWith x (-((x (Fin.last ℓ)).val : ℤ))

/-- Rescale with the half-offset representative `[x_ℓ + ⌊q_ℓ/2⌋]_{q_ℓ} − ⌊q_ℓ/2⌋ ∈
[−⌊q_ℓ/2⌋, q_ℓ − 1 − ⌊q_ℓ/2⌋]` (the form that adds and subtracts `qLastHalf`). Agrees with `rescale` when `q_ℓ` is odd. -/
def rescaleHalf (x : (i : Fin (ℓ + 1)) → ZMod (B.q i)) : (i : Fin ℓ) → ZMod (B.dropLast.q i) :=
  B.rescaleWith x (-(((x (Fin.last ℓ) + ((B.last / 2 : ℕ) : ZMod B.last)).val : ℤ) - (B.last / 2 : ℕ)))

/-- t-corrected BGV modulus switching: correction `d = t · [−x_ℓ · t⁻¹]_{q_ℓ}` (centred), so that
`d ≡ −X (mod q_ℓ)` and `d ≡ 0 (mod t)`. Same `d` as `Challenge.Source.bgvModSwitchComp`. -/
def bgvModSwitch (t : ℕ) (x : (i : Fin (ℓ + 1)) → ZMod (B.q i)) :
    (i : Fin ℓ) → ZMod (B.dropLast.q i) :=
  B.rescaleWith x ((t : ℤ) * ((-x (Fin.last ℓ)) * (t : ZMod B.last)⁻¹).valMinAbs)

/-- Residues of `X` on the full basis restrict to residues on `dropLast`. -/
theorem residues_dropLast {x : (i : Fin (ℓ + 1)) → ZMod (B.q i)} {X : ℤ}
    (hX : ∀ i, (X : ZMod (B.q i)) = x i) (i : Fin ℓ) :
    (X : ZMod (B.dropLast.q i)) = x i.castSucc := hX i.castSucc

/-- **Generic rescale.** For any integer `X` with residues `x` and any correction `d ≡ −x_ℓ
(mod q_ℓ)`: `q_ℓ ∣ X + d` and the output is the residue vector of `(X + d) / q_ℓ`. -/
theorem rescaleWith_spec {x : (i : Fin (ℓ + 1)) → ZMod (B.q i)} {X : ℤ}
    (hX : ∀ i, (X : ZMod (B.q i)) = x i) {d : ℤ}
    (hd : (d : ZMod B.last) = -x (Fin.last ℓ)) :
    ∃ y : ℤ, (∀ i, B.rescaleWith x d i = (y : ZMod (B.dropLast.q i))) ∧
      (B.last : ℤ) * y = X + d := by
  have hdiv : (B.last : ℤ) ∣ X + d := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]; push_cast; rw [hX, hd]; ring
  refine ⟨(X + d) / B.last, fun i => ?_, Int.mul_ediv_cancel' hdiv⟩
  exact B.dropLast.modDownWith_spec (fun i => B.last_coprime i) (B.residues_dropLast hX)
    (fun _ => rfl) hdiv i

/-- **Rescale, exact.** For every integer `X` with residues `x`, the output is the residue
vector of the integer `y` with `q_ℓ · y = X − [X]_{q_ℓ}`, `[X]_{q_ℓ} = valMinAbs x_ℓ ∈ (−q_ℓ/2,
q_ℓ/2]`. Hence `|y − X/q_ℓ| ≤ 1/2` (`rescale_error`). -/
theorem rescale_spec {x : (i : Fin (ℓ + 1)) → ZMod (B.q i)} {X : ℤ}
    (hX : ∀ i, (X : ZMod (B.q i)) = x i) :
    ∃ y : ℤ, (∀ i, B.rescale x i = (y : ZMod (B.dropLast.q i))) ∧
      (B.last : ℤ) * y = X - (x (Fin.last ℓ)).valMinAbs ∧
      |(x (Fin.last ℓ)).valMinAbs| ≤ ((B.last / 2 : ℕ) : ℤ) ∧
      -(B.last : ℤ) < 2 * (x (Fin.last ℓ)).valMinAbs ∧ 2 * (x (Fin.last ℓ)).valMinAbs ≤ B.last := by
  obtain ⟨y, hy, hq⟩ := B.rescaleWith_spec hX (d := -(x (Fin.last ℓ)).valMinAbs)
    (by simp)
  have hv := ZMod.valMinAbs_mem_Ioc (x (Fin.last ℓ))
  simp only [Set.mem_Ioc] at hv
  refine ⟨y, hy, by rw [hq]; ring, ?_, by linarith [hv.1], by linarith [hv.2]⟩
  rw [Int.abs_eq_natAbs]; exact_mod_cast ZMod.natAbs_valMinAbs_le _

/-- The rescale error over `ℚ`: `−1/2 ≤ y − X/q_ℓ < 1/2`. -/
theorem rescale_error {x : (i : Fin (ℓ + 1)) → ZMod (B.q i)} {X : ℤ}
    (hX : ∀ i, (X : ZMod (B.q i)) = x i) :
    ∃ y : ℤ, (∀ i, B.rescale x i = (y : ZMod (B.dropLast.q i))) ∧
      -1/2 ≤ (y : ℚ) - X / B.last ∧ (y : ℚ) - X / B.last < 1/2 := by
  obtain ⟨y, hy, hq, -, h1, h2⟩ := B.rescale_spec hX
  have hl : (0 : ℚ) < B.last := by exact_mod_cast B.pos _
  refine ⟨y, hy, ?_, ?_⟩
  all_goals
    set v := (x (Fin.last ℓ)).valMinAbs
    have hq' : (X : ℚ) = B.last * y + v := by
      have : ((B.last : ℤ) : ℚ) * y = X - v := by exact_mod_cast hq
      push_cast at this; linarith
    have hX' : (X : ℚ) / B.last = y + v / B.last := by
      rw [hq', add_div, mul_div_cancel_left₀ _ hl.ne']
    have h1' : -(B.last : ℚ) < 2 * v := by exact_mod_cast h1
    have h2' : (2 : ℚ) * v ≤ B.last := by exact_mod_cast h2
    have hv1 : (v : ℚ) / B.last ≤ 1 / 2 := by rw [div_le_iff₀ hl]; linarith
    have hv2 : -1 / 2 < (v : ℚ) / B.last := by rw [lt_div_iff₀ hl]; linarith
    rw [hX']
  · linarith
  · linarith

/-- **Floor rescale, exact.** For every integer `X` with residues `x`, `rescaleFloor x` is the
residue vector of `⌊X / q_ℓ⌋` (`Int.ediv` with positive divisor). -/
theorem rescaleFloor_spec {x : (i : Fin (ℓ + 1)) → ZMod (B.q i)} {X : ℤ}
    (hX : ∀ i, (X : ZMod (B.q i)) = x i) (i : Fin ℓ) :
    B.rescaleFloor x i = ((X / B.last : ℤ) : ZMod (B.dropLast.q i)) := by
  obtain ⟨y, hy, hq⟩ := B.rescaleWith_spec hX (d := -((x (Fin.last ℓ)).val : ℤ))
    (by push_cast; rw [ZMod.natCast_zmod_val])
  rw [rescaleFloor, hy i]
  congr 1
  -- `val x_ℓ = X mod q_ℓ`
  have hv : ((x (Fin.last ℓ)).val : ℤ) = X % B.last := by
    rw [← hX (Fin.last ℓ), ZMod.val_intCast]
  have hl : (0 : ℤ) < B.last := by exact_mod_cast B.pos _
  rw [hv] at hq
  have := Int.emod_add_mul_ediv X B.last
  have : (B.last : ℤ) * (y - X / B.last) = 0 := by linarith
  rcases mul_eq_zero.mp this with h | h
  · exact absurd h hl.ne'
  · linarith

/-- The half-offset representative is a lift of `x_ℓ` with `|r| ≤ ⌊q_ℓ/2⌋`. -/
theorem halfLift_spec (z : ZMod B.last) :
    let r : ℤ := ((z + ((B.last / 2 : ℕ) : ZMod B.last)).val : ℤ) - (B.last / 2 : ℕ)
    (r : ZMod B.last) = z ∧ |r| ≤ ((B.last / 2 : ℕ) : ℤ) ∧
      -((B.last / 2 : ℕ) : ℤ) ≤ r ∧ r < (B.last : ℤ) - (B.last / 2 : ℕ) := by
  intro r
  have hv := ZMod.val_lt (z + ((B.last / 2 : ℕ) : ZMod B.last))
  have h2 : 2 * (B.last / 2) ≤ B.last := Nat.mul_div_le _ _
  refine ⟨by simp only [r, Int.cast_sub, Int.cast_natCast, ZMod.natCast_zmod_val, add_sub_cancel_right], ?_, by simp only [r]; omega, by simp only [r]; omega⟩
  rw [abs_le]; constructor <;> simp only [r] <;> omega

/-- **Half-offset rescale, exact.** Output = residues of `y` with `q_ℓ·y = X − r`,
`−⌊q_ℓ/2⌋ ≤ r < q_ℓ − ⌊q_ℓ/2⌋`. -/
theorem rescaleHalf_spec {x : (i : Fin (ℓ + 1)) → ZMod (B.q i)} {X : ℤ}
    (hX : ∀ i, (X : ZMod (B.q i)) = x i) :
    ∃ y r : ℤ, (∀ i, B.rescaleHalf x i = (y : ZMod (B.dropLast.q i))) ∧
      (B.last : ℤ) * y = X - r ∧ |r| ≤ ((B.last / 2 : ℕ) : ℤ) := by
  obtain ⟨hr, hb, -⟩ := B.halfLift_spec (x (Fin.last ℓ))
  obtain ⟨y, hy, hq⟩ := B.rescaleWith_spec hX
    (d := -(((x (Fin.last ℓ) + ((B.last / 2 : ℕ) : ZMod B.last)).val : ℤ) - (B.last / 2 : ℕ)))
    (by rw [Int.cast_neg, hr])
  exact ⟨y, _, hy, by rw [hq]; ring, hb⟩

/-- For odd `q_ℓ` the half-offset lift is the centred lift, so `rescaleHalf = rescale`. -/
theorem rescaleHalf_eq_rescale (hodd : B.last % 2 = 1) (x : (i : Fin (ℓ + 1)) → ZMod (B.q i)) :
    B.rescaleHalf x = B.rescale x := by
  obtain ⟨hr, -, h1, h2⟩ := B.halfLift_spec (x (Fin.last ℓ))
  have hv : (x (Fin.last ℓ)).valMinAbs =
      ((x (Fin.last ℓ) + ((B.last / 2 : ℕ) : ZMod B.last)).val : ℤ) - (B.last / 2 : ℕ) := by
    rw [ZMod.valMinAbs_spec]
    refine ⟨hr.symm, ?_⟩
    simp only [Set.mem_Ioc]
    have : (2 : ℤ) * ((B.last / 2 : ℕ) : ℤ) + 1 = B.last := by
      have := Nat.div_add_mod B.last 2; rw [hodd] at this; exact_mod_cast this
    generalize ((x (Fin.last ℓ) + ((B.last / 2 : ℕ) : ZMod B.last)).val : ℤ) = v at *
    generalize ((B.last / 2 : ℕ) : ℤ) = h at *
    generalize ((B.last : ℕ) : ℤ) = q at *
    constructor <;> omega
  rw [rescaleHalf, rescale, hv]

/-- **BGV modulus switch, exact.** For `t` coprime to `q_ℓ` and every integer `X` with residues
`x`: the output is the residue vector of `y` with `q_ℓ · y = X + t·w`, where
`w = [−x_ℓ · t⁻¹]_{q_ℓ}` (centred, `|w| ≤ ⌊q_ℓ/2⌋`), and `y ≡ q_ℓ⁻¹ · X (mod t)`. -/
theorem bgvModSwitch_spec {t : ℕ} (ht : Nat.Coprime t B.last)
    {x : (i : Fin (ℓ + 1)) → ZMod (B.q i)} {X : ℤ} (hX : ∀ i, (X : ZMod (B.q i)) = x i) :
    ∃ y : ℤ, (∀ i, B.bgvModSwitch t x i = (y : ZMod (B.dropLast.q i))) ∧
      (B.last : ℤ) * y = X + t * ((-x (Fin.last ℓ)) * (t : ZMod B.last)⁻¹).valMinAbs ∧
      |((-x (Fin.last ℓ)) * (t : ZMod B.last)⁻¹).valMinAbs| ≤ ((B.last / 2 : ℕ) : ℤ) ∧
      (y : ZMod t) = (X : ZMod t) * (B.last : ZMod t)⁻¹ := by
  obtain ⟨y, hy, hq⟩ := B.rescaleWith_spec hX
    (d := (t : ℤ) * ((-x (Fin.last ℓ)) * (t : ZMod B.last)⁻¹).valMinAbs) (by
      push_cast; rw [mul_left_comm, ZMod.coe_mul_inv_eq_one t ht, mul_one])
  refine ⟨y, hy, hq, ?_, ?_⟩
  · rw [Int.abs_eq_natAbs]; exact_mod_cast ZMod.natAbs_valMinAbs_le _
  · exact intCast_eq_mul_inv_of_mul_eq ht hq

/-- t-corrected BGV modulus switching with the *canonical* lift `w = [−x_ℓ·t⁻¹]_{q_ℓ} ∈ [0, q_ℓ)`
(the canonical-lift form: `x_ℓ · it` with no half-offset, broadcast to the other limbs, times
`t`, added). Not the same `d` as `Challenge.Source.bgvModSwitchComp`. -/
def bgvModSwitchCanon (t : ℕ) (x : (i : Fin (ℓ + 1)) → ZMod (B.q i)) :
    (i : Fin ℓ) → ZMod (B.dropLast.q i) :=
  B.rescaleWith x ((t : ℤ) * (((-x (Fin.last ℓ)) * (t : ZMod B.last)⁻¹).val : ℤ))

/-- **BGV modulus switch with canonical lift, exact.** Output = residues of `y` with
`q_ℓ · y = X + t·w`, `0 ≤ w < q_ℓ`, and `y ≡ q_ℓ⁻¹ · X (mod t)`. -/
theorem bgvModSwitchCanon_spec {t : ℕ} (ht : Nat.Coprime t B.last)
    {x : (i : Fin (ℓ + 1)) → ZMod (B.q i)} {X : ℤ} (hX : ∀ i, (X : ZMod (B.q i)) = x i) :
    ∃ y : ℤ, (∀ i, B.bgvModSwitchCanon t x i = (y : ZMod (B.dropLast.q i))) ∧
      (B.last : ℤ) * y = X + t * (((-x (Fin.last ℓ)) * (t : ZMod B.last)⁻¹).val : ℤ) ∧
      (((-x (Fin.last ℓ)) * (t : ZMod B.last)⁻¹).val : ℤ) < B.last ∧
      (y : ZMod t) = (X : ZMod t) * (B.last : ZMod t)⁻¹ := by
  obtain ⟨y, hy, hq⟩ := B.rescaleWith_spec hX
    (d := (t : ℤ) * (((-x (Fin.last ℓ)) * (t : ZMod B.last)⁻¹).val : ℤ)) (by
      push_cast; rw [ZMod.natCast_zmod_val, mul_left_comm, ZMod.coe_mul_inv_eq_one t ht, mul_one])
  refine ⟨y, hy, hq, by exact_mod_cast ZMod.val_lt _, intCast_eq_mul_inv_of_mul_eq ht hq⟩

end Basis

/-! ### ModDown by a special modulus `P` (hybrid key switching) -/

namespace Basis

variable {ℓ k : ℕ} (C : Basis ℓ) (Bp : Basis k)

/-- ModDown (BEHZ / HPS / Han–Ki; OpenFHE `ApproxModDown`): from residues `xq` of `X` on `C`
and `xp` on the special basis `Bp` (product `P`), compute
`yᵢ = (xqᵢ − FastBConv(xp; Bp → C)ᵢ) · P⁻¹ mod qᵢ` (canonical FastBConv). -/
def modDown (xq : (i : Fin ℓ) → ZMod (C.q i)) (xp : (j : Fin k) → ZMod (Bp.q j)) :
    (i : Fin ℓ) → ZMod (C.q i) :=
  C.modDownWith Bp.prod xq (fun i => -Bp.fastBConv C.q xp i)

/-- ModDown with centred FastBConv. -/
def modDownC (xq : (i : Fin ℓ) → ZMod (C.q i)) (xp : (j : Fin k) → ZMod (Bp.q j)) :
    (i : Fin ℓ) → ZMod (C.q i) :=
  C.modDownWith Bp.prod xq (fun i => -Bp.fastBConvC C.q xp i)

/-- BGV ModDown (canonical): subtract `t · FastBConv([xp · t⁻¹]_P; Bp → C)`. -/
def bgvModDown (t : ℕ) (xq : (i : Fin ℓ) → ZMod (C.q i)) (xp : (j : Fin k) → ZMod (Bp.q j)) :
    (i : Fin ℓ) → ZMod (C.q i) :=
  C.modDownWith Bp.prod xq
    (fun i => -((t : ZMod (C.q i)) * Bp.fastBConv C.q (fun j => xp j * (t : ZMod (Bp.q j))⁻¹) i))

/-- BGV ModDown (centred): add `t · FastBConvC([−xp · t⁻¹]_P; Bp → C)`. -/
def bgvModDownC (t : ℕ) (xq : (i : Fin ℓ) → ZMod (C.q i)) (xp : (j : Fin k) → ZMod (Bp.q j)) :
    (i : Fin ℓ) → ZMod (C.q i) :=
  C.modDownWith Bp.prod xq
    (fun i => (t : ZMod (C.q i)) * Bp.fastBConvC C.q (fun j => -xp j * (t : ZMod (Bp.q j))⁻¹) i)

/-- Coprimality of `P = ∏ pⱼ` with `qᵢ` from coprimality of the moduli. -/
theorem prod_coprime_of {n : ℕ} (h : ∀ j, Nat.Coprime (Bp.q j) n) : Nat.Coprime Bp.prod n :=
  Nat.coprime_prod_left_iff.mpr fun j _ => h j

/-- An integer `D` with `D ≡ x̂ⱼ (mod pⱼ)` for all `j`, where `X ≡ x̂ⱼ`, satisfies `P ∣ X − D`. -/
theorem prod_dvd_sub_of {xp : (j : Fin k) → ZMod (Bp.q j)} {X D : ℤ}
    (hX : ∀ j, (X : ZMod (Bp.q j)) = xp j) (hD : ∀ j, (D : ZMod (Bp.q j)) = xp j) :
    (Bp.prod : ℤ) ∣ X - D :=
  Bp.prod_dvd_sub_of_residues fun j => by rw [hX, hD]

variable {C Bp}

/-- **ModDown, canonical, exact.** Let `P = Bp.prod`, coprime to every `qᵢ`. For every integer
`X` with residues `xq` on `C` and `xp` on `Bp`, `modDown xq xp` is the residue vector of the
integer `y` with `P · y = X − D`, where `D = Bp.fbcInt xp ∈ [0, k·(P−1)]` is the FastBConv
integer; equivalently `y = ⌊X/P⌋ − u` with `u = Bp.fbcOverflow xp`, `0 ≤ u < k` (`k > 0`). -/
theorem modDown_spec (hcop : ∀ i, Nat.Coprime Bp.prod (C.q i))
    {xq : (i : Fin ℓ) → ZMod (C.q i)} {xp : (j : Fin k) → ZMod (Bp.q j)} {X : ℤ}
    (hXq : ∀ i, (X : ZMod (C.q i)) = xq i) (hXp : ∀ j, (X : ZMod (Bp.q j)) = xp j) :
    ∃ y : ℤ, (∀ i, C.modDown Bp xq xp i = (y : ZMod (C.q i))) ∧
      (Bp.prod : ℤ) * y = X - Bp.fbcInt xp ∧
      0 ≤ Bp.fbcInt xp ∧ Bp.fbcInt xp ≤ k * ((Bp.prod : ℤ) - 1) ∧
      y = X / Bp.prod - Bp.fbcOverflow xp := by
  have hdiv : (Bp.prod : ℤ) ∣ X + -Bp.fbcInt xp := by
    rw [← sub_eq_add_neg]; exact Bp.prod_dvd_sub_of hXp (Bp.fbcInt_residue xp)
  have hP : (0 : ℤ) < Bp.prod := by exact_mod_cast Bp.prod_pos
  refine ⟨(X + -Bp.fbcInt xp) / Bp.prod, fun i => ?_, ?_, Bp.fbcInt_nonneg xp, Bp.fbcInt_le xp, ?_⟩
  · exact C.modDownWith_spec hcop hXq (fun i => by rw [Bp.fastBConv_eq_intCast]; push_cast; rfl)
      hdiv i
  · rw [Int.mul_ediv_cancel' hdiv]; ring
  · -- `lift xp = X mod P`
    have hl : ((Bp.lift xp : ℕ) : ℤ) = X % Bp.prod := by
      have h1 := Bp.prod_dvd_sub_of hXp (Bp.lift_residue xp)
      have h2 : (0 : ℤ) ≤ (Bp.lift xp : ℕ) := by positivity
      have h3 : ((Bp.lift xp : ℕ) : ℤ) < Bp.prod := by exact_mod_cast Bp.lift_lt xp
      rw [← Int.emod_emod_of_dvd X (dvd_refl _), Int.emod_emod_of_dvd _ (dvd_refl _)]
      have := Int.emod_eq_emod_iff_emod_sub_eq_zero.mpr (Int.emod_eq_zero_of_dvd h1)
      rw [Int.emod_eq_of_lt h2 h3] at this
      exact this.symm
    have he := Bp.fbcInt_eq xp
    rw [hl] at he
    have := Int.emod_add_mul_ediv X Bp.prod
    have hdv : X + -Bp.fbcInt xp = (Bp.prod : ℤ) * (X / Bp.prod - Bp.fbcOverflow xp) := by
      rw [he]; linarith
    rw [hdv, Int.mul_ediv_cancel_left _ hP.ne']

/-- **ModDown, centred, exact.** As `modDown_spec` with `P · y = X − D`, `2·|D| ≤ k·P`, i.e.
`|y − X/P| ≤ k/2`. -/
theorem modDownC_spec (hcop : ∀ i, Nat.Coprime Bp.prod (C.q i))
    {xq : (i : Fin ℓ) → ZMod (C.q i)} {xp : (j : Fin k) → ZMod (Bp.q j)} {X : ℤ}
    (hXq : ∀ i, (X : ZMod (C.q i)) = xq i) (hXp : ∀ j, (X : ZMod (Bp.q j)) = xp j) :
    ∃ y : ℤ, (∀ i, C.modDownC Bp xq xp i = (y : ZMod (C.q i))) ∧
      (Bp.prod : ℤ) * y = X - Bp.fbcIntC xp ∧ 2 * |Bp.fbcIntC xp| ≤ k * Bp.prod := by
  have hdiv : (Bp.prod : ℤ) ∣ X + -Bp.fbcIntC xp := by
    rw [← sub_eq_add_neg]; exact Bp.prod_dvd_sub_of hXp (Bp.fbcIntC_residue xp)
  refine ⟨(X + -Bp.fbcIntC xp) / Bp.prod, fun i => ?_, ?_, Bp.two_mul_abs_fbcIntC_le xp⟩
  · exact C.modDownWith_spec hcop hXq (fun i => by rw [Bp.fastBConvC_eq_intCast]; push_cast; rfl)
      hdiv i
  · rw [Int.mul_ediv_cancel' hdiv]; ring

/-- **BGV ModDown, canonical, exact.** For `t` coprime to every `pⱼ`: output = residues of `y`
with `P · y = X − t·D'`, `D' = Bp.fbcInt (xp·t⁻¹) ∈ [0, k·(P−1)]`, and `y ≡ P⁻¹·X (mod t)`. -/
theorem bgvModDown_spec {t : ℕ} (ht : ∀ j, Nat.Coprime t (Bp.q j))
    (hcop : ∀ i, Nat.Coprime Bp.prod (C.q i))
    {xq : (i : Fin ℓ) → ZMod (C.q i)} {xp : (j : Fin k) → ZMod (Bp.q j)} {X : ℤ}
    (hXq : ∀ i, (X : ZMod (C.q i)) = xq i) (hXp : ∀ j, (X : ZMod (Bp.q j)) = xp j) :
    ∃ y : ℤ, (∀ i, C.bgvModDown Bp t xq xp i = (y : ZMod (C.q i))) ∧
      (Bp.prod : ℤ) * y = X - t * Bp.fbcInt (fun j => xp j * (t : ZMod (Bp.q j))⁻¹) ∧
      0 ≤ Bp.fbcInt (fun j => xp j * (t : ZMod (Bp.q j))⁻¹) ∧
      Bp.fbcInt (fun j => xp j * (t : ZMod (Bp.q j))⁻¹) ≤ k * ((Bp.prod : ℤ) - 1) ∧
      (y : ZMod t) = (X : ZMod t) * (Bp.prod : ZMod t)⁻¹ := by
  set D := Bp.fbcInt (fun j => xp j * (t : ZMod (Bp.q j))⁻¹)
  have hdiv : (Bp.prod : ℤ) ∣ X + -(t * D) := by
    rw [← sub_eq_add_neg]
    refine Bp.prod_dvd_sub_of hXp fun j => ?_
    push_cast
    rw [Bp.fbcInt_residue, mul_comm, mul_assoc, mul_comm _ (t : ZMod (Bp.q j)),
      ZMod.coe_mul_inv_eq_one _ (ht j), mul_one]
  have hq : (Bp.prod : ℤ) * ((X + -(t * D)) / Bp.prod) = X - t * D := by
    rw [Int.mul_ediv_cancel' hdiv]; ring
  refine ⟨(X + -(t * D)) / Bp.prod, fun i => ?_, hq, Bp.fbcInt_nonneg _, Bp.fbcInt_le _, ?_⟩
  · exact C.modDownWith_spec hcop hXq
      (fun i => by rw [Bp.fastBConv_eq_intCast]; push_cast; rfl) hdiv i
  · have htP : Nat.Coprime t Bp.prod := Nat.coprime_prod_right_iff.mpr fun j _ => ht j
    exact intCast_eq_mul_inv_of_mul_eq htP (e := -D) (by rw [hq]; ring)

/-- **BGV ModDown, centred, exact.** For `t` coprime to every `pⱼ`: output = residues of `y` with
`P · y = X + t·D'`, `D' = Bp.fbcIntC (−xp·t⁻¹)`, `2·|D'| ≤ k·P`, and `y ≡ P⁻¹·X (mod t)`. -/
theorem bgvModDownC_spec {t : ℕ} (ht : ∀ j, Nat.Coprime t (Bp.q j))
    (hcop : ∀ i, Nat.Coprime Bp.prod (C.q i))
    {xq : (i : Fin ℓ) → ZMod (C.q i)} {xp : (j : Fin k) → ZMod (Bp.q j)} {X : ℤ}
    (hXq : ∀ i, (X : ZMod (C.q i)) = xq i) (hXp : ∀ j, (X : ZMod (Bp.q j)) = xp j) :
    ∃ y : ℤ, (∀ i, C.bgvModDownC Bp t xq xp i = (y : ZMod (C.q i))) ∧
      (Bp.prod : ℤ) * y = X + t * Bp.fbcIntC (fun j => -xp j * (t : ZMod (Bp.q j))⁻¹) ∧
      2 * |Bp.fbcIntC (fun j => -xp j * (t : ZMod (Bp.q j))⁻¹)| ≤ k * Bp.prod ∧
      (y : ZMod t) = (X : ZMod t) * (Bp.prod : ZMod t)⁻¹ := by
  set D := Bp.fbcIntC (fun j => -xp j * (t : ZMod (Bp.q j))⁻¹)
  have hdiv : (Bp.prod : ℤ) ∣ X + t * D := by
    rw [← sub_neg_eq_add]
    refine Bp.prod_dvd_sub_of hXp fun j => ?_
    push_cast
    rw [Bp.fbcIntC_residue, mul_left_comm, ZMod.coe_mul_inv_eq_one _ (ht j)]
    ring
  have hq : (Bp.prod : ℤ) * ((X + t * D) / Bp.prod) = X + t * D := Int.mul_ediv_cancel' hdiv
  refine ⟨(X + t * D) / Bp.prod, fun i => ?_, hq, Bp.two_mul_abs_fbcIntC_le _, ?_⟩
  · exact C.modDownWith_spec hcop hXq
      (fun i => by rw [Bp.fastBConvC_eq_intCast]; push_cast; rfl) hdiv i
  · have htP : Nat.Coprime t Bp.prod := Nat.coprime_prod_right_iff.mpr fun j _ => ht j
    exact intCast_eq_mul_inv_of_mul_eq htP hq

end Basis
end FHE.RNS
