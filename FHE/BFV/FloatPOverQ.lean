import FHE.BFV.FloatScalar
import FHE.BFV.MulPOverQLeveled

/-!
# FHE.BFV.FloatPOverQ — the slack of the P-over-Q multiplication with sums within the tolerances

`Challenge.BFVMul.Fl.poverqMul S` (the P-over-Q multiplication of `Challenge.BFVMul.POverQ` with
the two truncated sums taken from `S : Fl.Sums`) is proved, for every `S` with `Fl.SumsOK S`, to
multiply integer representatives of bounded size and to round within a bounded distance, under
`floatAuxOK?` and for an auxiliary basis of at most `k` moduli:

* `poverqMul_lifted`: with `Aᵢ = liftAF S qs aᵢ` (the representative the tolerant base switch
  lifts to, `2·F·|A| ≤ Q·(F + 2w)`), `Wᵢ = liftWF S qs ps bᵢ` (the tolerant switch of `S/Q` modulo
  `P`), `Bᵢ = liftBF S qs ps bᵢ = (Q·Wᵢ − Sᵢ)/P`, and `X` the integers the tolerant scaling
  computes, the hypotheses of `Challenge.BFVMul.stepOK_mul_lifted` hold with `e`, `rho` those of
  `Spec.BudgetBFV.poverqSlack t N Q P k (doubleSw k) (doubleSr ps)`.

The scalar facts about the tolerant base switch and scaling are those of `FHE.BFV.FloatScalar`;
the fast conversion is integer arithmetic and is as in `FHE.BFV.MulPOverQ`. Neither the flag `ok`
of the slack nor `1 ≤ k` is used. The general lemmas (`*_fl`, `abs_coeff_mul_scaled`, `lift_le`)
are reused by `FHE.BFV.FloatLeveled`.
-/

namespace FHE.BFV.FloatPOverQ
open Spec NPoly Scheme Challenge.BFVMul Challenge.BFVMul.HPS Challenge.BFVMul.POverQ
open Validation.Ring Validation.Scheme Validation.Source
open FHE.RNS FHE.BFV.MulHPS FHE.BFV.MulPOverQ Spec.BudgetBFV

/-! ### The side conditions -/

theorem floatDen_pos : 0 < floatDen := by unfold floatDen; positivity

theorem doubleSw_mono {m k : ℕ} (h : m ≤ k) : doubleSw m ≤ doubleSw k :=
  Nat.mul_le_mul h (Nat.add_le_add_right h 5)

/-- The definition of the locked `floatBasisOK`, by `rfl`. -/
theorem floatBasisOK_def (ms : List ℕ) :
    floatBasisOK ms =
      (decide (ms.length ≤ 128) && ms.all fun m => decide (1 ≤ m) && decide (m < 2 ^ 60)) :=
  rfl

theorem floatBasisOK_sublist {l₁ l₂ : List ℕ} (h : l₁.Sublist l₂)
    (h2 : floatBasisOK l₂ = true) : floatBasisOK l₁ = true := by
  simp only [floatBasisOK_def, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h2 ⊢
  exact ⟨h.length_le.trans h2.1, fun m hm => h2.2 m (h.subset hm)⟩

/-- The definition of the locked `floatAuxOK?`, by `rfl`. -/
theorem floatAuxOK_def (qs ps : List ℕ) :
    floatAuxOK? qs ps =
      (floatBasisOK qs && floatBasisOK ps &&
        (qs ++ ps).all (fun m => decide (3 ≤ m) && decide (m % 2 = 1)) &&
        decide ((qs ++ ps).Pairwise Nat.Coprime)) :=
  rfl

theorem floatAuxOK_imp {qs ps : List ℕ} (h : floatAuxOK? qs ps = true) :
    floatBasisOK qs = true ∧ floatBasisOK ps = true ∧ (∀ m ∈ qs ++ ps, 0 < m) ∧
      (qs ++ ps).Pairwise Nat.Coprime := by
  simp only [floatAuxOK_def, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq,
    and_assoc] at h
  obtain ⟨h1, h2, h3, h4⟩ := h
  exact ⟨h1, h2, fun m hm => by have := (h3 m hm).1; omega, h4⟩

/-! ### Arithmetic -/

/-- A product of two polynomials with coefficients bounded after scaling:
`c₁·|aⱼ| ≤ α`, `c₂·|bⱼ| ≤ β` give `c₁·c₂·|(a·b)ᵢ| ≤ N·α·β`. -/
theorem abs_coeff_mul_scaled {N : ℕ} (a b : IntPoly N) (c1 c2 α β : ℤ) (hc1 : 0 < c1)
    (hc2 : 0 < c2) (ha : ∀ j, c1 * |a.coeff j| ≤ α) (hb : ∀ j, c2 * |b.coeff j| ≤ β)
    (i : Fin N) : c1 * c2 * |(a * b).coeff i| ≤ N * α * β := by
  have hα : 0 ≤ α := le_trans (mul_nonneg hc1.le (abs_nonneg _)) (ha i)
  have hβ : 0 ≤ β := le_trans (mul_nonneg hc2.le (abs_nonneg _)) (hb i)
  have h := abs_coeff_mul_le_N a b (α / c1) (β / c2)
    (fun j => (Int.le_ediv_iff_mul_le hc1).mpr (by rw [mul_comm]; exact ha j))
    (fun j => (Int.le_ediv_iff_mul_le hc2).mpr (by rw [mul_comm]; exact hb j)) i
  have h1 : α / c1 * c1 ≤ α := Int.ediv_mul_le _ hc1.ne'
  have h2 : β / c2 * c2 ≤ β := Int.ediv_mul_le _ hc2.ne'
  have h3 : 0 ≤ α / c1 := Int.ediv_nonneg hα hc1.le
  have h4 : 0 ≤ β / c2 := Int.ediv_nonneg hβ hc2.le
  have h5 : (α / c1 * c1) * (β / c2 * c2) ≤ α * β :=
    mul_le_mul h1 h2 (mul_nonneg h4 hc2.le) hα
  have h6 := mul_le_mul_of_nonneg_left h (mul_nonneg hc1.le hc2.le)
  have h7 := mul_le_mul_of_nonneg_left h5 (Nat.cast_nonneg (α := ℤ) N)
  linarith

/-- From `2·F·P·z ≤ Q·P·(F + 2w) + 2·F·k·Q` and `e ≥ 2Qw/F + 2kQ/P`: `2·z ≤ Q + e`. -/
theorem lift_le (F Q P k w e : ℕ) (hF : 0 < F) (hP : 0 < P)
    (he : 2 * Q * w * P + 2 * k * Q * F ≤ e * (F * P)) (z : ℤ)
    (h : 2 * (F : ℤ) * (P * z) ≤ (Q : ℤ) * (P * ((F : ℤ) + 2 * w)) + 2 * F * (k * Q)) :
    2 * z ≤ (Q : ℤ) + e := by
  have he' : (2 : ℤ) * Q * w * P + 2 * k * Q * F ≤ e * (F * P) := by exact_mod_cast he
  have hFP : (0 : ℤ) < (F : ℤ) * P := by exact_mod_cast Nat.mul_pos hF hP
  have h6 : (F : ℤ) * P * (2 * z) ≤ (F : ℤ) * P * ((Q : ℤ) + e) := by linarith
  exact le_of_mul_le_mul_left h6 hFP

/-- `round_combo` with tolerances: from `Q·T' = P·T + E`, a scaling within `1/2 + r/F`
(`2·F·|P·x − t·T'| ≤ P·(F + 2r)`), `F·|E| ≤ N·Q·(F + 2w)·k·Q` and
`c ≥ 2r/F + 2tNkQ(F + 2w)/(P·F)`: `2·|Q·x − t·T| ≤ Q·(1 + c)`. -/
theorem round_final_tol (F Q P t N k c w r : ℕ) (x T' T E : ℤ) (hF : 0 < F) (hP : 0 < P)
    (h1 : (Q : ℤ) * T' = P * T + E)
    (h2 : 2 * (F : ℤ) * |(P : ℤ) * x - t * T'| ≤ (P : ℤ) * ((F : ℤ) + 2 * r))
    (hE : (F : ℤ) * |E| ≤ (N : ℤ) * ((Q : ℤ) * ((F : ℤ) + 2 * w)) * (k * Q))
    (hc : 2 * r * P + 2 * t * N * k * Q * (F + 2 * w) ≤ c * (P * F)) :
    2 * |(Q : ℤ) * x - t * T| ≤ (Q : ℤ) * ((1 + c : ℕ) : ℤ) := by
  have hc' : (2 : ℤ) * r * P + 2 * t * N * k * Q * (F + 2 * w) ≤ c * (P * F) := by
    exact_mod_cast hc
  have hPF : (0 : ℤ) < (P : ℤ) * F := by exact_mod_cast Nat.mul_pos hP hF
  have hPz : (0 : ℤ) < P := by exact_mod_cast hP
  have e : (P : ℤ) * (Q * x - t * T) = Q * (P * x - t * T') + t * E := by
    linear_combination (t : ℤ) * h1
  have h4 : |(P : ℤ) * (Q * x - t * T)| ≤ Q * |(P : ℤ) * x - t * T'| + t * |E| := by
    rw [e]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg (α := ℤ) Q),
      abs_of_nonneg (Nat.cast_nonneg (α := ℤ) t)]
  rw [abs_mul, abs_of_pos hPz] at h4
  have a0 := mul_le_mul_of_nonneg_left h4 (by positivity : (0 : ℤ) ≤ 2 * (F : ℤ))
  have a1 := mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg (α := ℤ) Q)
  have a2 := mul_le_mul_of_nonneg_left hE (by positivity : (0 : ℤ) ≤ 2 * (t : ℤ))
  have a3 := mul_le_mul_of_nonneg_left hc' (Nat.cast_nonneg (α := ℤ) Q)
  have h6 : (P : ℤ) * F * (2 * |(Q : ℤ) * x - t * T|) ≤
      (P : ℤ) * F * ((Q : ℤ) * ((1 + c : ℕ) : ℤ)) := by
    push_cast
    linarith
  exact le_of_mul_le_mul_left h6 hPF

/-! ### The slack -/

theorem slack_e_tol (t N Q P k w r : ℕ) (hP : 0 < P) :
    2 * Q * w * P + 2 * k * Q * floatDen ≤ (poverqSlack t N Q P k w r).e * (floatDen * P) :=
  le_ceilDiv_mul (2 * Q * w * P + 2 * k * Q * floatDen) (floatDen * P)
    (Nat.mul_pos floatDen_pos hP)

theorem slack_rho_tol (t N Q P k w r : ℕ) (hP : 0 < P) :
    ∃ c : ℕ, (poverqSlack t N Q P k w r).rho = 1 + c ∧
      2 * r * P + 2 * t * N * k * Q * (floatDen + 2 * w) ≤ c * (P * floatDen) :=
  ⟨ceilDiv (2 * r * P + 2 * t * N * k * Q * (floatDen + 2 * w)) (P * floatDen), rfl,
    le_ceilDiv_mul _ _ (Nat.mul_pos hP floatDen_pos)⟩

/-! ### The representative `B`, with a tolerant switch -/

/-- `W`: the representative the tolerant switch from `ps` lifts `S/Q` modulo `P` to. -/
def wValF (S : Fl.Sums) (qs ps : List ℕ) (x : ℤ) : ℤ :=
  FloatScalar.switchVal S ps (w0Val qs ps x)

/-- `B = (Q·W − S)/P`. -/
def bValF (S : Fl.Sums) (qs ps : List ℕ) (x : ℤ) : ℤ :=
  (qs.prod * wValF S qs ps x - sVal qs ps.prod x) / ps.prod

/-- `Q·W = P·B + S`. -/
theorem bValF_spec (S : Fl.Sums) (qs ps : List ℕ) (hpos : ∀ m ∈ qs ++ ps, 0 < m)
    (hcop : (qs ++ ps).Pairwise Nat.Coprime) (x : ℤ) :
    (qs.prod : ℤ) * wValF S qs ps x = ps.prod * bValF S qs ps x + sVal qs ps.prod x := by
  have hposp : ∀ p ∈ ps, 0 < p := fun p hp => hpos p (List.mem_append_right _ hp)
  have hcopp : ps.Pairwise Nat.Coprime := (List.pairwise_append.mp hcop).2.1
  have hP : 0 < ps.prod := prod_pos' ps hposp
  have hQP := coprime_prod_prod qs ps hcop
  have h1 : (ps.prod : ℤ) ∣ wValF S qs ps x - w0Val qs ps x :=
    FloatScalar.switchVal_dvd S ps hposp hcopp _
  have h2 := invMod_mul_modEq _ _ hP hQP
  have h3 : (ps.prod : ℤ) ∣ qs.prod * wValF S qs ps x - sVal qs ps.prod x := by
    obtain ⟨u, hu⟩ := h1
    obtain ⟨v, hv⟩ := (Int.modEq_iff_dvd.mp h2.symm)
    refine ⟨qs.prod * u + sVal qs ps.prod x * v, ?_⟩
    have e : wValF S qs ps x = w0Val qs ps x + ps.prod * u := by linarith
    rw [e]
    unfold w0Val
    linear_combination sVal qs ps.prod x * hv
  unfold bValF
  have := Int.mul_ediv_cancel' h3
  linarith

/-- `B ≡ x (mod Q)`. -/
theorem bValF_dvd (S : Fl.Sums) (qs ps : List ℕ) (hpos : ∀ m ∈ qs ++ ps, 0 < m)
    (hcop : (qs ++ ps).Pairwise Nat.Coprime) (x : ℤ) :
    (qs.prod : ℤ) ∣ bValF S qs ps x - x := by
  have hposq : ∀ q ∈ qs, 0 < q := fun q hq => hpos q (List.mem_append_left _ hq)
  have hcopq : qs.Pairwise Nat.Coprime := (List.pairwise_append.mp hcop).1
  have hQP : IsCoprime (qs.prod : ℤ) (ps.prod : ℤ) :=
    Nat.isCoprime_iff_coprime.mpr (coprime_prod_prod qs ps hcop)
  have h1 := bValF_spec S qs ps hpos hcop x
  obtain ⟨u, hu⟩ := sVal_dvd qs hposq hcopq ps.prod x
  have h2 : (qs.prod : ℤ) ∣ (ps.prod : ℤ) * (bValF S qs ps x - x) :=
    ⟨wValF S qs ps x - u, by linear_combination -h1 - hu⟩
  exact hQP.dvd_of_dvd_mul_left h2

/-- `2·F·P·|B| ≤ Q·P·(F + 2w) + 2·F·k·Q`, for every `w` at least the tolerance of the switch
from `ps`. -/
theorem bValF_bound (S : Fl.Sums) (hS : Fl.SumsOK S) (qs ps : List ℕ)
    (hpos : ∀ m ∈ qs ++ ps, 0 < m) (hcop : (qs ++ ps).Pairwise Nat.Coprime)
    (hfb : floatBasisOK ps = true) (w : ℕ) (hw : doubleSw ps.length ≤ w) (x : ℤ) :
    2 * (floatDen : ℤ) * ((ps.prod : ℤ) * |bValF S qs ps x|) ≤
      (qs.prod : ℤ) * ((ps.prod : ℤ) * ((floatDen : ℤ) + 2 * w)) +
        2 * floatDen * (qs.length * (qs.prod : ℤ)) := by
  have hposq : ∀ q ∈ qs, 0 < q := fun q hq => hpos q (List.mem_append_left _ hq)
  have hposp : ∀ p ∈ ps, 0 < p := fun p hp => hpos p (List.mem_append_right _ hp)
  have hcopp : ps.Pairwise Nat.Coprime := (List.pairwise_append.mp hcop).2.1
  have hP : (0 : ℤ) < ps.prod := by exact_mod_cast prod_pos' ps hposp
  have hw' : (doubleSw ps.length : ℤ) ≤ w := by exact_mod_cast hw
  have h1 := bValF_spec S qs ps hpos hcop x
  obtain ⟨h2, h3⟩ := sVal_bounds qs hposq ps.prod x
  have hb : 2 * (floatDen : ℤ) * |wValF S qs ps x| ≤
      (ps.prod : ℤ) * ((floatDen : ℤ) + 2 * (doubleSw ps.length : ℤ)) :=
    FloatScalar.switchVal_bound S hS ps hposp hcopp hfb _
  have e : (ps.prod : ℤ) * bValF S qs ps x = qs.prod * wValF S qs ps x - sVal qs ps.prod x := by
    linarith
  have h4 : (ps.prod : ℤ) * |bValF S qs ps x| ≤
      qs.prod * |wValF S qs ps x| + sVal qs ps.prod x := by
    have e1 : (ps.prod : ℤ) * |bValF S qs ps x| = |(ps.prod : ℤ) * bValF S qs ps x| := by
      rw [abs_mul, abs_of_pos hP]
    rw [e1, e]
    refine (abs_sub _ _).trans ?_
    rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg (α := ℤ) qs.prod), abs_of_nonneg h2]
  have a0 := mul_le_mul_of_nonneg_left h4 (by positivity : (0 : ℤ) ≤ 2 * (floatDen : ℤ))
  have a1 := mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg (α := ℤ) qs.prod)
  have a2 := mul_le_mul_of_nonneg_left hw'
    (by positivity : (0 : ℤ) ≤ 2 * ((qs.prod : ℤ) * ps.prod))
  have a3 := mul_le_mul_of_nonneg_left h3 (by positivity : (0 : ℤ) ≤ 2 * (floatDen : ℤ))
  linarith

/-! ### Polynomials -/

variable {N : ℕ}

/-- Operand 1 as the algorithm multiplies it: the representative the tolerant switch lifts to. -/
def liftAF (S : Fl.Sums) (qs : List ℕ) (a : IntPoly N) : IntPoly N :=
  ⟨fun i => FloatScalar.switchVal S qs (a.coeff i)⟩

/-- Operand 2 after the scaling by `P/Q`: `W`. -/
def liftWF (S : Fl.Sums) (qs ps : List ℕ) (b : IntPoly N) : IntPoly N :=
  ⟨fun i => wValF S qs ps (b.coeff i)⟩

/-- Operand 2 as the algorithm multiplies it: `B = (Q·W − S)/P`. -/
def liftBF (S : Fl.Sums) (qs ps : List ℕ) (b : IntPoly N) : IntPoly N :=
  ⟨fun i => bValF S qs ps (b.coeff i)⟩

/-- The tolerant base switch of the limbs of `a` gives the limbs of `b`, where `b` has the
switched values as coefficients. -/
theorem switchBasis_toLimbs_fl (S : Fl.Sums) (qs ps : List ℕ) (a b : IntPoly N)
    (h : ∀ i, FloatScalar.switchVal S qs (a.coeff i) = b.coeff i) :
    Fl.switchBasis S qs ps (toLimbs qs a) = toLimbs ps b := by
  unfold Fl.switchBasis
  rw [toLimbs_eq ps]
  refine List.map_congr_left fun p _ => ?_
  ext i
  show Fl.switch1 S qs (residues (toLimbs qs a) i) p = b.coeff i % p
  rw [residues_toLimbs, FloatScalar.switch1_eq, h]

/-- **Tolerant extension**: the limbs modulo `qs ++ ps` of `liftAF`. -/
theorem expand_toLimbs_fl (S : Fl.Sums) (qs ps : List ℕ) (hpos : ∀ q ∈ qs, 0 < q)
    (hcop : qs.Pairwise Nat.Coprime) (a : IntPoly N) :
    Fl.expand S qs ps (toLimbs qs a) = toLimbs (qs ++ ps) (liftAF S qs a) := by
  unfold Fl.expand
  rw [switchBasis_toLimbs_fl S qs ps a (liftAF S qs a) (fun _ => rfl)]
  have e : toLimbs (qs ++ ps) (liftAF S qs a) =
      toLimbs qs (liftAF S qs a) ++ toLimbs ps (liftAF S qs a) := List.map_append
  rw [e]
  congr 1
  refine (toLimbs_congr qs _ _ fun q hq i => ?_).symm
  exact dvd_trans (by exact_mod_cast List.dvd_prod hq)
    (FloatScalar.switchVal_dvd S qs hpos hcop _)

theorem fastExpand_def_fl (S : Fl.Sums) (qs ps ql : List ℕ) (x : List (IntPoly N)) :
    Fl.fastExpand S qs ps ql x =
      Fl.switchBasis S ps ql (fastScale qs ps x) ++ fastScale qs ps x := rfl

/-- **The fast expansion with a tolerant switch**: the limbs modulo `ql ++ ps` of `liftWF`. -/
theorem fastExpand_toLimbs_fl (S : Fl.Sums) (qs ps ql : List ℕ) (hpos : ∀ m ∈ qs ++ ps, 0 < m)
    (hcop : (qs ++ ps).Pairwise Nat.Coprime) (b : IntPoly N) :
    Fl.fastExpand S qs ps ql (toLimbs qs b) = toLimbs (ql ++ ps) (liftWF S qs ps b) := by
  have hposp : ∀ p ∈ ps, 0 < p := fun p hp => hpos p (List.mem_append_right _ hp)
  have hcopp : ps.Pairwise Nat.Coprime := (List.pairwise_append.mp hcop).2.1
  have h1 : fastScale qs ps (toLimbs qs b) =
      toLimbs ps (⟨fun i => w0Val qs ps (b.coeff i)⟩ : IntPoly N) := by
    unfold fastScale
    rw [toLimbs_eq]
    refine List.map_congr_left fun p hp => ?_
    ext i
    show approx1 qs (negPDigits qs ps.prod (residues (toLimbs qs b) i)) p = _
    rw [residues_toLimbs, negPDigits_map, approx1_eq qs ps hpos hcop _ p hp]
  have h2 : toLimbs ps (⟨fun i => w0Val qs ps (b.coeff i)⟩ : IntPoly N) =
      toLimbs ps (liftWF S qs ps b) :=
    (toLimbs_congr ps _ _ fun p hp i =>
      dvd_trans (by exact_mod_cast List.dvd_prod hp)
        (FloatScalar.switchVal_dvd S ps hposp hcopp _)).symm
  have e : toLimbs (ql ++ ps) (liftWF S qs ps b) =
      toLimbs ql (liftWF S qs ps b) ++ toLimbs ps (liftWF S qs ps b) := List.map_append
  have h3 : Fl.switchBasis S ps ql
      (toLimbs ps (⟨fun i => w0Val qs ps (b.coeff i)⟩ : IntPoly N)) =
      toLimbs ql (liftWF S qs ps b) :=
    switchBasis_toLimbs_fl S ps ql _ _ fun _ => rfl
  rw [fastExpand_def_fl, h1, h3, h2, e]

/-- **Tolerant scale and round**, any input and output bases: the limbs modulo `outs` of an
integer polynomial `X` with `2·F·|I·X − t·T| ≤ I·(F + 2·doubleSr ins)` coefficientwise. -/
theorem scaleRoundOut_toLimbs_fl (S : Fl.Sums) (hS : Fl.SumsOK S) (t : ℕ) (ins outs : List ℕ)
    (hpos : ∀ m ∈ ins ++ outs, 0 < m) (hcop : (ins ++ outs).Pairwise Nat.Coprime)
    (hfb : floatBasisOK ins = true) (T : IntPoly N) :
    ∃ X : IntPoly N,
      Fl.scaleRoundOut S t ins outs (toLimbs ins T) (toLimbs outs T) = toLimbs outs X ∧
      ∀ i, 2 * (floatDen : ℤ) * |(ins.prod : ℤ) * X.coeff i - t * T.coeff i| ≤
        (ins.prod : ℤ) * ((floatDen : ℤ) + 2 * (doubleSr ins : ℤ)) := by
  choose R hR1 hR2 using fun i : Fin N =>
    FloatScalar.scale1_tol S hS t ins outs hpos hcop hfb (T.coeff i)
  refine ⟨⟨R⟩, ?_, hR2⟩
  unfold Fl.scaleRoundOut
  apply List.ext_getElem
  · simp [toLimbs_eq]
  · intro n h1 h2
    have hn : n < outs.length := by simpa [toLimbs_eq] using h2
    simp only [List.getElem_zipWith, toLimbs_eq, List.getElem_map]
    ext i
    show Fl.scale1 S t ins outs (residues (toLimbs ins T) i) outs[n] (T.coeff i % outs[n]) =
      R i % outs[n]
    rw [residues_toLimbs]
    exact hR1 i ⟨n, hn⟩

/-- The excess term of one product: `2·F·|(A·S)ᵢ| ≤ N·Q_l·(F + 2w)·k·Q`, for every `w` at least
the tolerance of the switch from `ql` (`ql = qs` for `Fl.poverqMul`). -/
theorem abs_coeff_liftAF_mul_liftS (S : Fl.Sums) (hS : Fl.SumsOK S) (ql qs ps : List ℕ)
    (hposl : ∀ q ∈ ql, 0 < q) (hcopl : ql.Pairwise Nat.Coprime) (hfb : floatBasisOK ql = true)
    (hposq : ∀ q ∈ qs, 0 < q) (w : ℕ) (hw : doubleSw ql.length ≤ w) (a b : IntPoly N)
    (i : Fin N) :
    2 * (floatDen : ℤ) * |(liftAF S ql a * liftS qs ps b).coeff i| ≤
      (N : ℤ) * ((ql.prod : ℤ) * ((floatDen : ℤ) + 2 * w)) * (qs.length * (qs.prod : ℤ)) := by
  have hF : (0 : ℤ) < 2 * (floatDen : ℤ) := by
    have : (0 : ℤ) < floatDen := by exact_mod_cast floatDen_pos
    linarith
  have hw' : (doubleSw ql.length : ℤ) ≤ w := by exact_mod_cast hw
  have h := abs_coeff_mul_scaled (liftAF S ql a) (liftS qs ps b) (2 * (floatDen : ℤ)) 1
    ((ql.prod : ℤ) * ((floatDen : ℤ) + 2 * w)) (qs.length * (qs.prod : ℤ)) hF one_pos
    (fun j => by
      have h1 : 2 * (floatDen : ℤ) * |FloatScalar.switchVal S ql (a.coeff j)| ≤ _ :=
        FloatScalar.switchVal_bound S hS ql hposl hcopl hfb (a.coeff j)
      have h2 := mul_le_mul_of_nonneg_left hw'
        (by positivity : (0 : ℤ) ≤ 2 * (ql.prod : ℤ))
      show 2 * (floatDen : ℤ) * |FloatScalar.switchVal S ql (a.coeff j)| ≤ _
      linarith)
    (fun j => by
      obtain ⟨h1, h2⟩ := sVal_bounds qs hposq ps.prod (b.coeff j)
      show 1 * |sVal qs ps.prod (b.coeff j)| ≤ _
      rw [one_mul, abs_of_nonneg h1]
      exact h2) i
  linarith

/-! ### The theorem -/

/-- **The P-over-Q multiplication with sums within the tolerances multiplies representatives of
bounded size and rounds within a bounded distance**: the hypotheses of
`Challenge.BFVMul.stepOK_mul_lifted` at `Q = qs.prod`, with the slack
`Spec.BudgetBFV.poverqSlack t N Q P k (doubleSw k) (doubleSr ps)`, `k = qs.length`, for an
auxiliary basis of at most `k` moduli. -/
theorem poverqMul_lifted (S : Fl.Sums) (hS : Fl.SumsOK S) (t : ℕ) (qs ps : List ℕ)
    (haux : floatAuxOK? qs ps = true) (hlen : ps.length ≤ qs.length)
    (c d : List (IntPoly N)) (hc : c.length = 2) (hd : d.length = 2) :
    ∃ A B X : List (IntPoly N), X.length = 3 ∧
      A.map (ofInt qs.prod) = c.map (ofInt qs.prod) ∧
      B.map (ofInt qs.prod) = d.map (ofInt qs.prod) ∧
      (∀ p ∈ A, 2 * normInf p ≤ qs.prod +
        (poverqSlack t N qs.prod ps.prod qs.length (doubleSw qs.length) (doubleSr ps)).e) ∧
      (∀ p ∈ B, 2 * normInf p ≤ qs.prod +
        (poverqSlack t N qs.prod ps.prod qs.length (doubleSw qs.length) (doubleSr ps)).e) ∧
      (∀ (j : ℕ) (i : Fin N),
        2 * |(qs.prod : ℤ) * (X.getD j 0).coeff i -
            (t : ℤ) * ((Challenge.Source.tensor A B).getD j 0).coeff i|
          ≤ (qs.prod : ℤ) *
            (poverqSlack t N qs.prod ps.prod qs.length (doubleSw qs.length) (doubleSr ps)).rho) ∧
      (Fl.poverqMul S t qs ps c d).map (ofInt qs.prod) = X.map (ofInt qs.prod) := by
  obtain ⟨hfq, hfp, hpos, hcop⟩ := floatAuxOK_imp haux
  have hposq : ∀ q ∈ qs, 0 < q := fun q hq => hpos q (List.mem_append_left _ hq)
  have hposp : ∀ p ∈ ps, 0 < p := fun p hp => hpos p (List.mem_append_right _ hp)
  have hcopq : qs.Pairwise Nat.Coprime := (List.pairwise_append.mp hcop).1
  have hpos' : ∀ m ∈ ps ++ qs, 0 < m := fun m hm => hpos m (by
    rcases List.mem_append.mp hm with h | h
    · exact List.mem_append_right _ h
    · exact List.mem_append_left _ h)
  have hQ : 0 < qs.prod := prod_pos' qs hposq
  have hP : 0 < ps.prod := prod_pos' ps hposp
  have hF := floatDen_pos
  have hFz : (0 : ℤ) < floatDen := by exact_mod_cast hF
  have hww := doubleSw_mono hlen
  obtain ⟨a₀, a₁, rfl⟩ := List.length_eq_two.mp hc
  obtain ⟨b₀, b₁, rfl⟩ := List.length_eq_two.mp hd
  have he := slack_e_tol t N qs.prod ps.prod qs.length (doubleSw qs.length) (doubleSr ps) hP
  obtain ⟨cc, hrho, hcc⟩ :=
    slack_rho_tol t N qs.prod ps.prod qs.length (doubleSw qs.length) (doubleSr ps) hP
  rw [hrho]
  generalize (poverqSlack t N qs.prod ps.prod qs.length (doubleSw qs.length) (doubleSr ps)).e = e
    at he ⊢
  -- sizes of the representatives
  have hAn : ∀ a : IntPoly N, 2 * normInf (liftAF S qs a) ≤ qs.prod + e := fun a =>
    two_normInf_le _ _ fun i => by
      have h1 : 2 * (floatDen : ℤ) * |FloatScalar.switchVal S qs (a.coeff i)| ≤ _ :=
        FloatScalar.switchVal_bound S hS qs hposq hcopq hfq (a.coeff i)
      show 2 * |FloatScalar.switchVal S qs (a.coeff i)| ≤ ((qs.prod + e : ℕ) : ℤ)
      rw [Nat.cast_add]
      refine lift_le _ _ _ _ _ _ hF hP he _ ?_
      have h2 := mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg (α := ℤ) ps.prod)
      have h3 : (0 : ℤ) ≤ 2 * (floatDen : ℤ) * (qs.length * (qs.prod : ℤ)) := by positivity
      linarith
  have hBn : ∀ b : IntPoly N, 2 * normInf (liftBF S qs ps b) ≤ qs.prod + e := fun b =>
    two_normInf_le _ _ fun i => by
      show 2 * |bValF S qs ps (b.coeff i)| ≤ ((qs.prod + e : ℕ) : ℤ)
      rw [Nat.cast_add]
      exact lift_le _ _ _ _ _ _ hF hP he _
        (bValF_bound S hS qs ps hpos hcop hfp _ hww (b.coeff i))
  -- the rounding of one product, coefficient by coefficient
  have hW : ∀ (b : IntPoly N) (i : Fin N), (qs.prod : ℤ) * (liftWF S qs ps b).coeff i =
      (ps.prod : ℤ) * (liftBF S qs ps b).coeff i + (liftS qs ps b).coeff i := fun b i =>
    bValF_spec S qs ps hpos hcop (b.coeff i)
  have hE1 := abs_coeff_liftAF_mul_liftS (N := N) S hS qs qs ps hposq hcopq hfq hposq
    (doubleSw qs.length) le_rfl
  -- what the algorithm computes
  have hstep : ∀ T : IntPoly N, ∃ X : IntPoly N,
      reconstruct qs (Fl.scaleRoundOut S t ps qs ((toLimbs (qs ++ ps) T).drop qs.length)
        ((toLimbs (qs ++ ps) T).take qs.length)) = modPoly qs.prod X ∧
      ∀ i, 2 * (floatDen : ℤ) * |(ps.prod : ℤ) * X.coeff i - t * T.coeff i| ≤
        (ps.prod : ℤ) * ((floatDen : ℤ) + 2 * (doubleSr ps : ℤ)) := fun T => by
    obtain ⟨X, hX, hXb⟩ :=
      scaleRoundOut_toLimbs_fl S hS t ps qs hpos' (pairwise_swap qs ps hcop) hfp T
    refine ⟨X, ?_, hXb⟩
    have e : toLimbs (qs ++ ps) T = toLimbs qs T ++ toLimbs ps T := List.map_append
    have hl : (toLimbs qs T).length = qs.length := List.length_map _
    rw [e, List.take_left' hl, List.drop_left' hl, hX, reconstruct_toLimbs qs hposq hcopq]
  have hmul : Fl.poverqMul S t qs ps [a₀, a₁] [b₀, b₁] =
      (Challenge.Source.tensor [liftAF S qs a₀, liftAF S qs a₁]
        [liftWF S qs ps b₀, liftWF S qs ps b₁]).map fun T =>
        reconstruct qs (Fl.scaleRoundOut S t ps qs ((toLimbs (qs ++ ps) T).drop qs.length)
          ((toLimbs (qs ++ ps) T).take qs.length)) := by
    unfold Fl.poverqMul
    simp only [List.map_cons, List.map_nil, expand_toLimbs_fl S qs ps hposq hcopq,
      fastExpand_toLimbs_fl S qs ps qs hpos hcop, tensor_toLimbs, List.map_map]
    rfl
  rw [source_tensor_two] at hmul
  obtain ⟨X₀, hX₀, hb₀⟩ := hstep (liftAF S qs a₀ * liftWF S qs ps b₀)
  obtain ⟨X₁, hX₁, hb₁⟩ :=
    hstep (liftAF S qs a₀ * liftWF S qs ps b₁ + liftAF S qs a₁ * liftWF S qs ps b₀)
  obtain ⟨X₂, hX₂, hb₂⟩ := hstep (liftAF S qs a₁ * liftWF S qs ps b₁)
  refine ⟨[liftAF S qs a₀, liftAF S qs a₁], [liftBF S qs ps b₀, liftBF S qs ps b₁],
    [X₀, X₁, X₂], rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [List.map_cons, List.map_nil]
    rw [ofInt_eq_of_dvd _ (liftAF S qs a₀) a₀ fun i =>
        FloatScalar.switchVal_dvd S qs hposq hcopq _,
      ofInt_eq_of_dvd _ (liftAF S qs a₁) a₁ fun i =>
        FloatScalar.switchVal_dvd S qs hposq hcopq _]
  · simp only [List.map_cons, List.map_nil]
    rw [ofInt_eq_of_dvd _ (liftBF S qs ps b₀) b₀ fun i => bValF_dvd S qs ps hpos hcop _,
      ofInt_eq_of_dvd _ (liftBF S qs ps b₁) b₁ fun i => bValF_dvd S qs ps hpos hcop _]
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl <;> exact hAn _
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl <;> exact hBn _
  · intro j i
    rcases j with _ | _ | _ | j
    · show 2 * |(qs.prod : ℤ) * X₀.coeff i -
        (t : ℤ) * (liftAF S qs a₀ * liftBF S qs ps b₀).coeff i| ≤ _
      refine round_final_tol _ _ _ _ N qs.length cc (doubleSw qs.length) (doubleSr ps) _ _ _ _
        hF hP (coeff_mul_combo _ _ _ _ _ _ (hW b₀) i) (hb₀ i) ?_ hcc
      have := hE1 a₀ b₀ i
      have := mul_nonneg hFz.le (abs_nonneg ((liftAF S qs a₀ * liftS qs ps b₀).coeff i))
      linarith
    · show 2 * |(qs.prod : ℤ) * X₁.coeff i -
        (t : ℤ) * (liftAF S qs a₀ * liftBF S qs ps b₁ +
          liftAF S qs a₁ * liftBF S qs ps b₀).coeff i| ≤ _
      refine round_final_tol _ _ _ _ N qs.length cc (doubleSw qs.length) (doubleSr ps) _ _ _
        ((liftAF S qs a₀ * liftS qs ps b₁).coeff i + (liftAF S qs a₁ * liftS qs ps b₀).coeff i)
        hF hP ?_ (hb₁ i) ?_ hcc
      · rw [coeff_add', coeff_add', mul_add, mul_add,
          coeff_mul_combo _ _ _ _ _ _ (hW b₁) i, coeff_mul_combo _ _ _ _ _ _ (hW b₀) i]
        ring
      · have h1 := hE1 a₀ b₁ i
        have h2 := hE1 a₁ b₀ i
        have h3 := mul_le_mul_of_nonneg_left
          (abs_add_le ((liftAF S qs a₀ * liftS qs ps b₁).coeff i)
            ((liftAF S qs a₁ * liftS qs ps b₀).coeff i)) hFz.le
        linarith
    · show 2 * |(qs.prod : ℤ) * X₂.coeff i -
        (t : ℤ) * (liftAF S qs a₁ * liftBF S qs ps b₁).coeff i| ≤ _
      refine round_final_tol _ _ _ _ N qs.length cc (doubleSw qs.length) (doubleSr ps) _ _ _ _
        hF hP (coeff_mul_combo _ _ _ _ _ _ (hW b₁) i) (hb₂ i) ?_ hcc
      have := hE1 a₁ b₁ i
      have := mul_nonneg hFz.le (abs_nonneg ((liftAF S qs a₁ * liftS qs ps b₁).coeff i))
      linarith
    · show 2 * |(qs.prod : ℤ) * (0 : IntPoly N).coeff i - (t : ℤ) * (0 : IntPoly N).coeff i| ≤ _
      simp only [coeff_zero', mul_zero, sub_zero, abs_zero]
      positivity
  · rw [hmul]
    simp only [List.map_cons, List.map_nil, hX₀, hX₁, hX₂, ofInt_modPoly]

end FHE.BFV.FloatPOverQ
