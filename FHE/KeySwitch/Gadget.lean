import FHE.RNS.Poly

/-!
# FHE.KeySwitch.Gadget — the RNS gadget of hybrid key switching

Hybrid key switching (Han–Ki 2019; Kim–Polyakov–Zucca 2021; OpenFHE `KeySwitchHYBRID`) splits
the `ℓ` ciphertext limbs `q₀, …, q_{ℓ-1}` (product `Q`) into `dnum` *digits*: disjoint groups of
limbs with products `Q₀, …, Q_{dnum-1}`, `∏ⱼ Qⱼ = Q`. With the special modulus `P` the gadget
vector is

  `gⱼ = P · Q̂ⱼ · [Q̂ⱼ⁻¹]_{Qⱼ}  (mod Q·P)`,   `Q̂ⱼ = ∏_{j' ≠ j} Q_{j'} = Q / Qⱼ`.

**Gadget identity** (`gadget_sum_dvd`, `gadget_poly`): for *any* integers `Dⱼ` with
`Dⱼ ≡ X (mod Qⱼ)`,

  `Σⱼ Dⱼ · gⱼ ≡ P · X  (mod Q·P)`.

ModUp of digit `j` by fast base conversion produces `Dⱼ = [X]_{Qⱼ} + Qⱼ·uⱼ` with an unknown
overflow `uⱼ` (`FHE.RNS.Basis.fastBConvCPoly_spec`). The identity reads `Dⱼ` only modulo `Qⱼ`,
so the overflow term `Qⱼ·uⱼ·gⱼ = Q·P·uⱼ·[Q̂ⱼ⁻¹]` vanishes **exactly** modulo `Q·P`: it costs
nothing in correctness. It enters the noise only through the size `‖Dⱼ‖∞`, which multiplies the
key noise (`FHE.KeySwitch.Hybrid`).

The digit moduli form an RNS basis themselves (`Digits.basis`), so the identity is
`Basis.prod_dvd_sum_sub` for that basis, multiplied by `P`.
-/

namespace FHE.KeySwitch

open Finset Spec Spec.NPoly FHE.RNS Validation.Ring Validation.Scheme

/-! ### Small polynomial helpers -/

section Helpers
variable {N : ℕ}

theorem coeff_natCast_mul' (n : ℕ) (a : IntPoly N) (c : Fin N) :
    ((n : IntPoly N) * a).coeff c = (n : ℤ) * a.coeff c := by
  rw [natCast_def, coeff_const_mul]

theorem coeff_intCast_mul' (n : ℤ) (a : IntPoly N) (c : Fin N) :
    ((n : IntPoly N) * a).coeff c = n * a.coeff c := by
  rw [intCast_def, coeff_const_mul]; rfl

theorem coeff_sum' [NeZero N] {R : Type} [CommRing R] {ι : Type} (s : Finset ι)
    (f : ι → NPoly R N) (c : Fin N) : (∑ j ∈ s, f j).coeff c = ∑ j ∈ s, (f j).coeff c := by
  classical
  induction s using Finset.induction_on with
  | empty => rfl
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, coeff_add', ih]

theorem ofInt_sum [NeZero N] (q : ℕ) {ι : Type} (s : Finset ι) (f : ι → IntPoly N) :
    ofInt q (∑ j ∈ s, f j) = ∑ j ∈ s, ofInt q (f j) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ofInt_zero q
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, ofInt_add, ih]

theorem ofInt_natCast [NeZero N] (q n : ℕ) : ofInt q (n : IntPoly N) = (n : Poly q N) := by
  ext c; simp [ofInt, natCast_def]

theorem ofInt_intCast [NeZero N] (q : ℕ) (n : ℤ) : ofInt q (n : IntPoly N) = (n : Poly q N) := by
  ext c; simp [ofInt, intCast_def]

theorem abs_valMinAbs_le' {q : ℕ} [NeZero q] (z : ZMod q) :
    |(z.valMinAbs : ℤ)| ≤ ((q / 2 : ℕ) : ℤ) := by
  rw [Int.abs_eq_natAbs]; exact_mod_cast ZMod.natAbs_valMinAbs_le z

theorem two_mul_half_le' (q : ℕ) : 2 * ((q / 2 : ℕ) : ℤ) ≤ q := by
  have := Nat.mul_div_le q 2; omega

end Helpers

/-- A partition of the limbs `Fin ℓ` into `dnum` digits: digit `j` has `size j` limbs, its
`r`-th limb is `emb j r`, and every limb lies in exactly one digit. -/
structure Digits (ℓ : ℕ) where
  dnum : ℕ
  size : Fin dnum → ℕ
  emb : (j : Fin dnum) → Fin (size j) → Fin ℓ
  bij : Function.Bijective (fun p : (Σ j : Fin dnum, Fin (size j)) => emb p.1 p.2)

namespace Digits

variable {ℓ : ℕ} (Dg : Digits ℓ)

theorem emb_injective (j : Fin Dg.dnum) : Function.Injective (Dg.emb j) := by
  intro r r' h
  have := Dg.bij.1 (a₁ := ⟨j, r⟩) (a₂ := ⟨j, r'⟩) h
  simpa using this

theorem emb_ne {j j' : Fin Dg.dnum} (h : j ≠ j') (r : Fin (Dg.size j)) (r' : Fin (Dg.size j')) :
    Dg.emb j r ≠ Dg.emb j' r' := by
  intro he
  have := Dg.bij.1 (a₁ := ⟨j, r⟩) (a₂ := ⟨j', r'⟩) he
  exact h (congrArg Sigma.fst this)

theorem exists_emb (i : Fin ℓ) : ∃ j r, Dg.emb j r = i := by
  obtain ⟨⟨j, r⟩, h⟩ := Dg.bij.2 i
  exact ⟨j, r, h⟩

/-- The `j`-th digit as an RNS basis (a sub-basis of `C`). -/
def sub (C : Basis ℓ) (j : Fin Dg.dnum) : Basis (Dg.size j) :=
  C.restrict (Dg.emb j) (Dg.emb_injective j)

/-- The digit moduli `Qⱼ = ∏_{r} q_{emb j r}`, as an RNS basis. -/
def basis (C : Basis ℓ) : Basis Dg.dnum where
  q j := (Dg.sub C j).prod
  pos j := (Dg.sub C j).prod_pos
  coprime j j' h := by
    show Nat.Coprime (∏ r, C.q (Dg.emb j r)) (∏ r', C.q (Dg.emb j' r'))
    exact Nat.Coprime.prod_left fun r _ => Nat.Coprime.prod_right fun r' _ =>
      C.coprime (Dg.emb_ne h r r')

theorem basis_q (C : Basis ℓ) (j : Fin Dg.dnum) : (Dg.basis C).q j = (Dg.sub C j).prod := rfl

/-- `∏ⱼ Qⱼ = Q`. -/
theorem basis_prod (C : Basis ℓ) : (Dg.basis C).prod = C.prod := by
  show ∏ j, ∏ r, C.q (Dg.emb j r) = ∏ i, C.q i
  rw [← Fintype.prod_sigma (fun p : (Σ j : Fin Dg.dnum, Fin (Dg.size j)) => C.q (Dg.emb p.1 p.2))]
  exact Fintype.prod_bijective _ Dg.bij _ _ fun _ => rfl

/-- Each limb of digit `j` divides `Qⱼ`. -/
theorem q_dvd_digit (C : Basis ℓ) (j : Fin Dg.dnum) (r : Fin (Dg.size j)) :
    C.q (Dg.emb j r) ∣ (Dg.basis C).q j :=
  (Dg.sub C j).q_dvd_prod r

/-- Single digit: all limbs together (`dnum = 1`, no decomposition beyond ModUp). -/
def single (ℓ : ℕ) : Digits ℓ where
  dnum := 1
  size _ := ℓ
  emb _ r := r
  bij := ⟨fun ⟨j, r⟩ ⟨j', r'⟩ h => by
      obtain rfl : j = j' := Subsingleton.elim _ _
      simp only at h; subst h; rfl,
    fun i => ⟨⟨0, i⟩, rfl⟩⟩

end Digits

/-! ### The gadget vector -/

variable {ℓ : ℕ}

/-- The integer gadget entry `gⱼ = P · Q̂ⱼ · [Q̂ⱼ⁻¹]_{Qⱼ}` (canonical representative of the
inverse). Any representative of it modulo `Q·P` would do. -/
def gadget (Dg : Digits ℓ) (C : Basis ℓ) (P : ℕ) (j : Fin Dg.dnum) : ℤ :=
  (P : ℤ) * (Dg.basis C).hat j * ((Dg.basis C).hatInv j).val

/-- **Gadget identity.** For any integers `Dⱼ ≡ X (mod Qⱼ)` (e.g. ModUp outputs, whatever their
fast-base-conversion overflow), `Q·P ∣ Σⱼ Dⱼ·gⱼ − P·X`. -/
theorem gadget_sum_dvd (Dg : Digits ℓ) (C : Basis ℓ) (P : ℕ) (X : ℤ) (D : Fin Dg.dnum → ℤ)
    (hD : ∀ j, (D j : ZMod ((Dg.basis C).q j)) = (X : ZMod ((Dg.basis C).q j))) :
    ((C.prod * P : ℕ) : ℤ) ∣ (∑ j, D j * gadget Dg C P j) - P * X := by
  set B := Dg.basis C
  have h := B.prod_dvd_sum_sub (fun j => (X : ZMod (B.q j))) X (fun _ => rfl)
    (fun j => D j * ((B.hatInv j).val : ℤ)) (fun j => by
      push_cast; rw [hD j, ZMod.natCast_zmod_val])
  rw [Dg.basis_prod] at h
  have : (∑ j, D j * gadget Dg C P j) - P * X =
      (P : ℤ) * ((∑ j, D j * ((B.hatInv j).val : ℤ) * B.hat j) - X) := by
    rw [mul_sub, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [gadget]; ring
  rw [this, Nat.cast_mul, mul_comm (C.prod : ℤ)]
  exact mul_dvd_mul_left _ h

/-- Every coefficient of `Z` divisible by `M` iff `Z ≡ 0` in `Poly M N`. -/
theorem ofInt_eq_zero_iff {N M : ℕ} (Z : IntPoly N) :
    ofInt M Z = 0 ↔ ∀ c, (M : ℤ) ∣ Z.coeff c := by
  constructor
  · intro h c
    have := congrArg (fun p => p.coeff c) h
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp this
  · intro h; ext c
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr (h c)

/-- **Gadget identity, polynomials.** For integer polynomials `Dⱼ` congruent to `X` modulo `Qⱼ`
coefficientwise, `Σⱼ gⱼ·Dⱼ ≡ P·X (mod Q·P)`. -/
theorem gadget_poly {N : ℕ} [NeZero N] (Dg : Digits ℓ) (C : Basis ℓ) (P : ℕ) (X : IntPoly N)
    (D : Fin Dg.dnum → IntPoly N)
    (hD : ∀ j c, ((Dg.basis C).q j : ℤ) ∣ (D j).coeff c - X.coeff c) :
    ofInt (C.prod * P) (∑ j, (gadget Dg C P j : IntPoly N) * D j - (P : IntPoly N) * X) = 0 := by
  rw [ofInt_eq_zero_iff]
  intro c
  have hc : (∑ j, (gadget Dg C P j : IntPoly N) * D j - (P : IntPoly N) * X).coeff c =
      (∑ j, (D j).coeff c * gadget Dg C P j) - P * X.coeff c := by
    rw [coeff_sub', coeff_natCast_mul', coeff_sum']
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [coeff_intCast_mul', mul_comm]
  rw [hc]
  exact gadget_sum_dvd Dg C P _ _ fun j =>
    (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mpr (by
      have := hD j c
      rw [← dvd_neg, neg_sub] at this; exact this)

/-- **Residues of the gadget**: `gⱼ ≡ P (mod q)` for every limb `q` of digit `j`, and
`gⱼ ≡ 0 (mod q)` for every limb of another digit (and trivially `gⱼ ≡ 0 (mod P)`), so by CRT
`gⱼ` is determined modulo `Q·P` by these residues.

Using top-level keys at a lower level. Keys generated once at the top level `L` (modulo
`Q_L·P`), cut to the first `(lay.sizes ℓ).length` of them and read modulo `Q_ℓ·P` at level
`ℓ ≤ L`, are valid level-`ℓ` gadget keys, for the same secret and target and with the same noise
bound, under these hypotheses
(`Challenge.Budget.gadgetKeys_restrict`, proved in `Validation/Budget/Restrict.lean`):

1. the layout restricts, `Spec.Budget.restrictsTo lay L ℓ = true`: it is usable at level `L` and
   the digits of level `ℓ` are the top-level digits cut down to the first `ℓ` limbs (then the
   top-level gadget has the same residues on the limbs of level `ℓ`, by the theorem below;
   `Challenge.Budget.gadgetFactor_restrict`);
2. for BGV only, `2·(⌊B/t⌋·t) < Q_ℓ·P`, with `B` the key noise bound (the error must stay a
   multiple of `t` when reduced modulo `Q_ℓ·P`). BFV needs no size condition.

Neither hypothesis can be dropped: `Challenge.Budget.gadgetKeys_restrict_needs_restrictsTo` and
`Challenge.Budget.gadgetKeys_restrict_needs_size_bgv` are closed instances where the conclusion
fails without the first, respectively the second. `Challenge.Certify.certify?` checks both
(`Spec.Certify.layoutOK?`: hypothesis 1 at every level of the chain; `Spec.Certify.keysRestrict?`:
hypothesis 2 at the smallest modulus `q₀·P`, hence at every level:
`Validation.Budget.keysRestrict?_level`) and returns no certificate otherwise. -/
theorem gadget_residue (Dg : Digits ℓ) (C : Basis ℓ) (P : ℕ) (j j' : Fin Dg.dnum)
    (r : Fin (Dg.size j')) :
    ((gadget Dg C P j : ℤ) : ZMod (C.q (Dg.emb j' r))) = if j' = j then (P : ZMod _) else 0 := by
  have hq := Dg.q_dvd_digit C j' r
  unfold gadget
  split_ifs with h
  · subst h
    have hdiv : (((Dg.basis C).q j' : ℕ) : ℤ) ∣
        ((Dg.basis C).hat j' : ℤ) * (((Dg.basis C).hatInv j').val : ℤ) - 1 := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      push_cast
      rw [ZMod.natCast_zmod_val, (Dg.basis C).hat_mul_hatInv, sub_self]
    have hdiv' := (Int.natCast_dvd_natCast.mpr hq).trans hdiv
    have h1 : ((((Dg.basis C).hat j' : ℤ) * (((Dg.basis C).hatInv j').val : ℤ) : ℤ) :
        ZMod (C.q (Dg.emb j' r))) = 1 := by
      rw [← sub_eq_zero, ← Int.cast_one, ← Int.cast_sub, ZMod.intCast_zmod_eq_zero_iff_dvd]
      exact hdiv'
    push_cast at h1 ⊢
    rw [mul_assoc, h1, mul_one]
  · have h0 : (((Dg.basis C).hat j : ℕ) : ZMod (C.q (Dg.emb j' r))) = 0 :=
      (ZMod.natCast_eq_zero_iff _ _).mpr (hq.trans ((Dg.basis C).q_dvd_hat h))
    push_cast
    rw [h0, mul_zero, zero_mul]

end FHE.KeySwitch
