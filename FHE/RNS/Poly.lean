import FHE.RNS.ModDown
import Validation.Scheme.Basic

/-!
# FHE.RNS.Poly — RNS algorithms on polynomials, coefficient by coefficient

An RNS polynomial over a basis `B` is one `Poly qᵢ N` per limb (`RNSPoly B N`). `toRNS X` is the
RNS form of an integer polynomial, `combine` is CRT reconstruction into `Poly Q N`. Every
algorithm of `FHE.RNS.ModDown` / `FHE.RNS.BaseConv` acts coefficient by coefficient; this file
restates the exact characterisations in the forms the noise proofs consume:

* `combine_toRNS`, `centered_combine_toRNS` — the bridge `Π Poly qᵢ N ↔ Poly Q N ↔ IntPoly N`;
* `fastBConvCPoly_spec` / `fastBConvPoly_spec` — ModUp: `FastBConv(a) = [ā + Q·u]` with
  `2‖u‖∞ ≤ ℓ` (centred) or `0 ≤ uₖ < ℓ` (canonical);
* `rescalePoly_toRNS`, `bgvModSwitchPoly_toRNS` — RNS rescale / BGV modulus switch compute
  *exactly* the textbook integer formulas (the textbook rescaling `(c − [c]_q) / q` and
  `bgvModSwitchComp`);
* `modDownPoly_spec`, `modDownCPoly_spec`, `bgvModDownCPoly_spec` — ModDown by `P` in the
  `divq_core` shape `P · yₖ = Xₖ + dₖ` with a bound on `‖d‖∞`.
-/

namespace FHE.RNS

open Spec Spec.NPoly Validation.Scheme Validation.Ring

variable {N : ℕ}

/-- `‖d‖∞` from a coefficient bound of the form `2·|dₖ| ≤ M`. -/
theorem two_mul_normInf_le {d : IntPoly N} {M : ℕ} (h : ∀ c, 2 * |d.coeff c| ≤ M) :
    2 * normInf d ≤ M := by
  have : normInf d ≤ M / 2 := by
    rw [normInf_le_iff]; intro c
    rw [Int.natCast_ediv, Nat.cast_ofNat]
    have := h c; omega
  omega

/-- An RNS polynomial: one residue polynomial per limb. -/
abbrev RNSPoly {ℓ : ℕ} (B : Basis ℓ) (N : ℕ) := (i : Fin ℓ) → Poly (B.q i) N

namespace Basis

variable {ℓ : ℕ} (B : Basis ℓ)

/-- The residue vector of coefficient `k`. -/
def coeffVec (a : RNSPoly B N) (k : Fin N) : (i : Fin ℓ) → ZMod (B.q i) := fun i => (a i).coeff k

/-- RNS form of an integer polynomial. -/
def toRNS (X : IntPoly N) : RNSPoly B N := fun i => ofInt (B.q i) X

/-- CRT reconstruction, coefficient by coefficient. -/
def combine (a : RNSPoly B N) : Poly B.prod N := ⟨fun k => B.reconstruct (B.coeffVec a k)⟩

/-- Apply a per-coefficient residue map. -/
def mapCoeff {m : ℕ} {p : Fin m → ℕ}
    (f : ((i : Fin ℓ) → ZMod (B.q i)) → (j : Fin m) → ZMod (p j)) (a : RNSPoly B N) :
    (j : Fin m) → Poly (p j) N :=
  fun j => ⟨fun k => f (B.coeffVec a k) j⟩

theorem coeffVec_toRNS (X : IntPoly N) (k : Fin N) (i : Fin ℓ) :
    B.coeffVec (B.toRNS X) k i = (X.coeff k : ZMod (B.q i)) := rfl

theorem combine_toRNS (X : IntPoly N) : B.combine (B.toRNS X) = ofInt B.prod X := by
  ext k
  exact (B.intCast_eq_reconstruct (fun i => B.coeffVec_toRNS X k i)).symm

/-- If `2·|Xₖ| < Q` for every coefficient, the centred lift of the CRT combination is `X`. -/
theorem centered_combine_toRNS (X : IntPoly N) (h : ∀ k, 2 * |X.coeff k| < B.prod) :
    centered (B.combine (B.toRNS X)) = X := by
  rw [combine_toRNS]; exact centered_ofInt X (by exact_mod_cast h)

/-- Every RNS polynomial is the RNS form of the centred lift of its combination. -/
theorem toRNS_centered_combine (a : RNSPoly B N) : B.toRNS (centered (B.combine a)) = a := by
  funext i; ext k
  show ((((B.reconstruct (B.coeffVec a k)).valMinAbs : ℤ)) : ZMod (B.q i)) = (a i).coeff k
  exact B.liftC_residue _ i

theorem toRNS_add (X Y : IntPoly N) : B.toRNS (X + Y) = B.toRNS X + B.toRNS Y := by
  funext i; exact ofInt_add (q := B.q i) X Y

theorem toRNS_sub (X Y : IntPoly N) : B.toRNS (X - Y) = B.toRNS X - B.toRNS Y := by
  funext i; exact ofInt_sub (q := B.q i) X Y

theorem toRNS_mul (X Y : IntPoly N) : B.toRNS (X * Y) = B.toRNS X * B.toRNS Y := by
  funext i; exact ofInt_mul (q := B.q i) X Y

/-- Adding a multiple of `Q` does not change the RNS form: with `toRNS_centered_combine`, ModUp's
output and its source limbs are together the RNS form of the single polynomial `ā + Q·u`. -/
theorem toRNS_add_smul_prod (X u : IntPoly N) : B.toRNS (X + (B.prod : ℤ) • u) = B.toRNS X := by
  funext i; ext k
  show (((X.coeff k + (B.prod : ℤ) * u.coeff k : ℤ)) : ZMod (B.q i)) = (X.coeff k : ZMod (B.q i))
  rw [Int.cast_add, Int.cast_mul, Int.cast_natCast,
    (ZMod.natCast_eq_zero_iff _ _).mpr (B.q_dvd_prod i), zero_mul, add_zero]

theorem toRNS_injective_mod {X Y : IntPoly N} (h : B.toRNS X = B.toRNS Y) (k : Fin N) :
    (B.prod : ℤ) ∣ X.coeff k - Y.coeff k :=
  B.prod_dvd_sub_of_residues fun i => congrArg (fun a => (a i).coeff k) h

/-! ### Fast base conversion (ModUp) -/

/-- Canonical fast base conversion of an RNS polynomial. -/
def fastBConvPoly {m : ℕ} (p : Fin m → ℕ) (a : RNSPoly B N) : (j : Fin m) → Poly (p j) N :=
  B.mapCoeff (B.fastBConv p) a

/-- Centred fast base conversion of an RNS polynomial. -/
def fastBConvCPoly {m : ℕ} (p : Fin m → ℕ) (a : RNSPoly B N) : (j : Fin m) → Poly (p j) N :=
  B.mapCoeff (B.fastBConvC p) a

/-- **ModUp, centred.** `FastBConvC(a; B → p)` is the reduction mod each `pⱼ` of
`ā + Q·u`, where `ā = centered (combine a)` is the centred lift of `a` (coefficients in
`(−Q/2, Q/2]`) and `2·‖u‖∞ ≤ ℓ`. -/
theorem fastBConvCPoly_spec {m : ℕ} (p : Fin m → ℕ) (a : RNSPoly B N) :
    ∃ u : IntPoly N,
      (∀ j, B.fastBConvCPoly p a j = ofInt (p j) (centered (B.combine a) + (B.prod : ℤ) • u)) ∧
      2 * normInf u ≤ ℓ := by
  refine ⟨⟨fun k => B.fbcOverflowC (B.coeffVec a k)⟩, fun j => ?_, ?_⟩
  · ext k
    exact ((B.fastBConvC_spec p (B.coeffVec a k)).1 j).trans (by simp [liftC, combine]; ring)
  · have : normInf (⟨fun k => B.fbcOverflowC (B.coeffVec a k)⟩ : IntPoly N) ≤ ℓ / 2 := by
      rw [normInf_le_iff]
      intro k
      have := (B.fastBConvC_spec p (B.coeffVec a k)).2
      push_cast; omega
    omega

/-- **ModUp, canonical.** For `ℓ > 0`, `FastBConv(a; B → p)` is the reduction mod each `pⱼ` of
`ã + Q·u`, where `ã` has the canonical coefficients `[aₖ] ∈ [0, Q)` and `0 ≤ uₖ < ℓ`. -/
theorem fastBConvPoly_spec (hℓ : 0 < ℓ) {m : ℕ} (p : Fin m → ℕ) (a : RNSPoly B N) :
    ∃ u : IntPoly N,
      (∀ j, B.fastBConvPoly p a j =
        ofInt (p j) ⟨fun k => (((B.combine a).coeff k).val : ℤ) + B.prod * u.coeff k⟩) ∧
      ∀ k, 0 ≤ u.coeff k ∧ u.coeff k < ℓ := by
  refine ⟨⟨fun k => B.fbcOverflow (B.coeffVec a k)⟩, fun j => ?_, fun k => ?_⟩
  · ext k
    exact ((B.fastBConv_spec hℓ p (B.coeffVec a k)).1 j).trans (by simp [lift, combine]; ring_nf)
  · exact (B.fastBConv_spec hℓ p (B.coeffVec a k)).2

/-! ### Rescale and BGV modulus switching by the last modulus -/

section Rescale
variable {ℓ : ℕ} (B : Basis (ℓ + 1))

/-- Rescale (centred division by the last prime) of an RNS polynomial. -/
def rescalePoly (a : RNSPoly B N) : RNSPoly B.dropLast N :=
  B.mapCoeff (p := B.dropLast.q) B.rescale a

/-- t-corrected BGV modulus switch of an RNS polynomial. -/
def bgvModSwitchPoly (t : ℕ) (a : RNSPoly B N) : RNSPoly B.dropLast N :=
  B.mapCoeff (p := B.dropLast.q) (B.bgvModSwitch t) a

/-- **RNS rescale = textbook rescale.** On the RNS form of any integer polynomial `X`, rescale
computes the RNS form of `(Xₖ − [Xₖ]_{q_ℓ}) / q_ℓ` (centred remainder) — the body of
the textbook rescaling `(X − [X]_{q_ℓ}) / q_ℓ`. -/
theorem rescalePoly_toRNS (X : IntPoly N) :
    B.rescalePoly (B.toRNS X) = B.dropLast.toRNS
      ⟨fun k => (X.coeff k - ((X.coeff k : ZMod B.last)).valMinAbs) / B.last⟩ := by
  funext i; ext k
  obtain ⟨y, hy, hq⟩ := B.rescaleWith_spec (x := B.coeffVec (B.toRNS X) k) (X := X.coeff k)
    (fun _ => rfl) (d := -((X.coeff k : ZMod B.last)).valMinAbs) (by simp; rfl)
  have hl : (B.last : ℤ) ≠ 0 := by exact_mod_cast (B.pos _).ne'
  have : y = (X.coeff k - ((X.coeff k : ZMod B.last)).valMinAbs) / B.last := by
    rw [sub_eq_add_neg, ← hq, Int.mul_ediv_cancel_left _ hl]
  exact (hy i).trans (by rw [this]; rfl)

/-- **RNS BGV modulus switch = textbook BGV modulus switch.** For `gcd(t, q_ℓ) = 1`, on the RNS
form of any integer polynomial `X`, the output is the RNS form of
`(Xₖ + t·[−Xₖ·t⁻¹]_{q_ℓ}) / q_ℓ` — the body of `Challenge.Source.bgvModSwitchComp t q_ℓ X`. -/
theorem bgvModSwitchPoly_toRNS {t : ℕ} (ht : Nat.Coprime t B.last) (X : IntPoly N) :
    B.bgvModSwitchPoly t (B.toRNS X) = B.dropLast.toRNS
      ⟨fun k => (X.coeff k + (t : ℤ) *
        ((((-(X.coeff k) : ℤ) : ZMod B.last) * (t : ZMod B.last)⁻¹).valMinAbs)) / B.last⟩ := by
  funext i; ext k
  obtain ⟨y, hy, hq, -⟩ := B.bgvModSwitch_spec ht (x := B.coeffVec (B.toRNS X) k)
    (X := X.coeff k) (fun _ => rfl)
  have hl : (B.last : ℤ) ≠ 0 := by exact_mod_cast (B.pos _).ne'
  have hneg : -B.coeffVec (B.toRNS X) k (Fin.last ℓ) = (((-(X.coeff k) : ℤ) : ZMod B.last)) := by
    simp [coeffVec_toRNS]
  rw [hneg] at hq
  have : y = (X.coeff k + (t : ℤ) *
      ((((-(X.coeff k) : ℤ) : ZMod B.last) * (t : ZMod B.last)⁻¹).valMinAbs)) / B.last := by
    rw [← hq, Int.mul_ediv_cancel_left _ hl]
  exact (hy i).trans (by rw [this]; rfl)

end Rescale

/-! ### ModDown by a special modulus `P` -/

section ModDown
variable {ℓ k : ℕ} (C : Basis ℓ) (Bp : Basis k)

/-- ModDown of an RNS polynomial over `C ∪ Bp`, given as its two halves. -/
def modDownPoly (aq : RNSPoly C N) (ap : RNSPoly Bp N) : RNSPoly C N :=
  fun i => ⟨fun c => C.modDown Bp (C.coeffVec aq c) (Bp.coeffVec ap c) i⟩

/-- Centred ModDown of an RNS polynomial. -/
def modDownCPoly (aq : RNSPoly C N) (ap : RNSPoly Bp N) : RNSPoly C N :=
  fun i => ⟨fun c => C.modDownC Bp (C.coeffVec aq c) (Bp.coeffVec ap c) i⟩

/-- Centred BGV ModDown of an RNS polynomial. -/
def bgvModDownCPoly (t : ℕ) (aq : RNSPoly C N) (ap : RNSPoly Bp N) : RNSPoly C N :=
  fun i => ⟨fun c => C.bgvModDownC Bp t (C.coeffVec aq c) (Bp.coeffVec ap c) i⟩

variable {C Bp}

/-- **ModDown (canonical) on polynomials.** For every integer polynomial `X` (with `P` coprime
to every `qᵢ`), ModDown of its RNS form is the RNS form of `y` with
`P · yₖ = Xₖ + dₖ`, `−k·(P−1) ≤ dₖ ≤ 0`, so `‖d‖∞ ≤ k·(P−1)`. -/
theorem modDownPoly_spec (hcop : ∀ i, Nat.Coprime Bp.prod (C.q i)) (X : IntPoly N) :
    ∃ y d : IntPoly N, C.modDownPoly Bp (C.toRNS X) (Bp.toRNS X) = C.toRNS y ∧
      (∀ c, (Bp.prod : ℤ) * y.coeff c = X.coeff c + d.coeff c) ∧
      (∀ c, d.coeff c ≤ 0) ∧ normInf d ≤ k * (Bp.prod - 1) := by
  have h := fun c => modDown_spec hcop (xq := C.coeffVec (C.toRNS X) c)
    (xp := Bp.coeffVec (Bp.toRNS X) c) (X := X.coeff c) (fun _ => rfl) (fun _ => rfl)
  choose y hy hq h0 h1 _ using h
  refine ⟨⟨y⟩, ⟨fun c => -Bp.fbcInt (Bp.coeffVec (Bp.toRNS X) c)⟩, ?_, fun c => ?_,
    fun c => by simp only [neg_nonpos]; exact h0 c, ?_⟩
  · funext i; ext c; exact hy c i
  · simp only; rw [hq c]; ring
  · rw [normInf_le_iff]; intro c
    simp only [abs_neg, abs_of_nonneg (h0 c)]
    have hP := Bp.prod_pos
    rw [Nat.cast_mul, Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr hP.ne'), Nat.cast_one]
    exact h1 c

/-- **ModDown (centred) on polynomials.** As `modDownPoly_spec`, with `2·‖d‖∞ ≤ k·P`. -/
theorem modDownCPoly_spec (hcop : ∀ i, Nat.Coprime Bp.prod (C.q i)) (X : IntPoly N) :
    ∃ y d : IntPoly N, C.modDownCPoly Bp (C.toRNS X) (Bp.toRNS X) = C.toRNS y ∧
      (∀ c, (Bp.prod : ℤ) * y.coeff c = X.coeff c + d.coeff c) ∧
      2 * normInf d ≤ k * Bp.prod := by
  have h := fun c => modDownC_spec hcop (xq := C.coeffVec (C.toRNS X) c)
    (xp := Bp.coeffVec (Bp.toRNS X) c) (X := X.coeff c) (fun _ => rfl) (fun _ => rfl)
  choose y hy hq hb using h
  refine ⟨⟨y⟩, ⟨fun c => -Bp.fbcIntC (Bp.coeffVec (Bp.toRNS X) c)⟩, ?_, fun c => ?_, ?_⟩
  · funext i; ext c; exact hy c i
  · simp only; rw [hq c]; ring
  · exact two_mul_normInf_le fun c => by
      show 2 * |-_| ≤ _
      rw [abs_neg, Nat.cast_mul]; exact hb c

/-- **BGV ModDown (centred) on polynomials.** For `t` coprime to every `pⱼ` and `P` coprime to
every `qᵢ`: ModDown of the RNS form of `X` is the RNS form of `y` with `P · yₖ = Xₖ + t·eₖ`,
`2·‖e‖∞ ≤ k·P`, and `y ≡ P⁻¹·X (mod t)`. -/
theorem bgvModDownCPoly_spec {t : ℕ} (ht : ∀ j, Nat.Coprime t (Bp.q j))
    (hcop : ∀ i, Nat.Coprime Bp.prod (C.q i)) (X : IntPoly N) :
    ∃ y e : IntPoly N, C.bgvModDownCPoly Bp t (C.toRNS X) (Bp.toRNS X) = C.toRNS y ∧
      (∀ c, (Bp.prod : ℤ) * y.coeff c = X.coeff c + t * e.coeff c) ∧
      2 * normInf e ≤ k * Bp.prod ∧
      ofInt t y = (Bp.prod : ZMod t)⁻¹ • ofInt t X := by
  have h := fun c => bgvModDownC_spec ht hcop (xq := C.coeffVec (C.toRNS X) c)
    (xp := Bp.coeffVec (Bp.toRNS X) c) (X := X.coeff c) (fun _ => rfl) (fun _ => rfl)
  choose y hy hq hb hm using h
  refine ⟨⟨y⟩, ⟨fun c => Bp.fbcIntC (fun j => -Bp.coeffVec (Bp.toRNS X) c j *
    (t : ZMod (Bp.q j))⁻¹)⟩, ?_, hq, ?_, ?_⟩
  · funext i; ext c; exact hy c i
  · exact two_mul_normInf_le fun c => by rw [Nat.cast_mul]; exact hb c
  · ext c
    simp only [coeff_ofInt, coeff_smul']
    rw [hm c, mul_comm]

end ModDown

end Basis
end FHE.RNS
