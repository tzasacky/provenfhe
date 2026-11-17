import FHE.BFV.FloatScalar
import FHE.BFV.MulPOverQ

/-!
# FHE.BFV.FloatHPS — HPS multiplication with sums within the tolerances

`Challenge.BFVMul.Fl.hpsMul S` (HPS multiplication with the two truncated sums taken from `S`),
for every `S` with `Fl.SumsOK S`, multiplies representatives of bounded size and rounds within a
bounded distance:

* `hpsMul_lifted'`: with `A = c.map (lift S qs)`, `B = d.map (lift S qs)` (`lift` applies
  `FloatScalar.switchVal` coefficientwise), there is `X` with `A ≡ c`, `B ≡ d (mod Q)`,
  `2·‖Aᵢ‖∞, 2·‖Bᵢ‖∞ ≤ Q + e`, `2·|Q·Xⱼ − t·(A ⊗ B)ⱼ| ≤ Q·rho` and `Fl.hpsMul … ≡ X (mod Q)`, where
  `⟨e, rho, ok⟩ = hpsSlack t N Q P (doubleSw k) (doubleSw |ps|) (doubleSr qs)` and `ok = true`;
* `hpsMul_lifted`: the same with `A`, `B` existential (the hypotheses of
  `Challenge.BFVMul.stepOK_mul_lifted`).

Since both operands are lifted by the same map, `c = d` gives `A = B`: the hypotheses of
`Challenge.BFVMul.stepOK_square_lifted`.

The argument: the extension gives the residues modulo `qs ++ ps` of `A` (`expand_toLimbs`); the
limb-wise tensor gives the residues of the integer tensor `T = A ⊗ B` (`MulHPS.tensor_toLimbs`);
the scaling gives the residues modulo `ps` of some `R` with `|R − t·T/Q| ≤ 1/2 + r/2⁵³`
(`FloatScalar.scale1_tol`); the switch back gives the residues modulo `qs` of a representative of
`R` modulo `P` within `P/2 + P·wr/2⁵³`, which is `R` itself because the side condition `ok` makes
`2·2⁵³·|R| ≤ P·(2⁵³ − 2wr) − 2⁵³` (`scaled_small`, `switch_back`).
-/

namespace FHE.BFV.FloatHPS
open Spec NPoly Scheme Challenge.BFVMul Challenge.BFVMul.HPS Spec.BudgetBFV
open Validation.Ring Validation.Scheme Validation.Source
open FHE.BFV.MulHPS

variable {N : ℕ}

/-! ### The side conditions and the slack, by `rfl` -/

theorem floatAuxOK_def (qs ps : List ℕ) :
    floatAuxOK? qs ps =
      (floatBasisOK qs && floatBasisOK ps &&
        (qs ++ ps).all (fun m => decide (3 ≤ m) && decide (m % 2 = 1)) &&
        decide ((qs ++ ps).Pairwise Nat.Coprime)) :=
  rfl

theorem floatAuxOK_iff (qs ps : List ℕ) :
    floatAuxOK? qs ps = true ↔
      floatBasisOK qs = true ∧ floatBasisOK ps = true ∧
        (∀ m ∈ qs ++ ps, 3 ≤ m ∧ m % 2 = 1) ∧ (qs ++ ps).Pairwise Nat.Coprime := by
  simp only [floatAuxOK_def, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, and_assoc]

theorem hpsSlack_e (t N Q R w wr r : ℕ) :
    (hpsSlack t N Q R w wr r).e = ceilDiv (2 * Q * w) floatDen :=
  rfl

theorem hpsSlack_rho (t N Q R w wr r : ℕ) :
    (hpsSlack t N Q R w wr r).rho = 1 + ceilDiv (2 * r) floatDen :=
  rfl

theorem hpsSlack_ok (t N Q R w wr r : ℕ) :
    (hpsSlack t N Q R w wr r).ok =
      (decide (t * N * Q * (floatDen + 2 * w) ^ 2 + 2 * floatDen ^ 2 + 2 * r * floatDen ≤
          R * (floatDen - 2 * wr) * floatDen) && decide (2 * w < floatDen)) :=
  rfl

/-- The side condition of `hpsSlack`, over `ℤ`. -/
theorem hpsSlack_ok_int (t N Q R w wr r : ℕ) (h : (hpsSlack t N Q R w wr r).ok = true) :
    2 * (wr : ℤ) < floatDen ∧
      (t : ℤ) * N * Q * ((floatDen : ℤ) + 2 * w) ^ 2 + 2 * (floatDen : ℤ) ^ 2 +
        2 * r * floatDen ≤ (R : ℤ) * ((floatDen : ℤ) - 2 * wr) * floatDen := by
  rw [hpsSlack_ok, Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at h
  obtain ⟨h1, -⟩ := h
  have hF := FloatScalar.floatDen_pos
  have hlt : 2 * wr < floatDen := by
    by_contra hge
    have h0 : floatDen - 2 * wr = 0 := by omega
    rw [h0, Nat.mul_zero, Nat.zero_mul] at h1
    have : 0 < 2 * floatDen ^ 2 := by positivity
    omega
  refine ⟨by exact_mod_cast hlt, ?_⟩
  have hc : ((floatDen - 2 * wr : ℕ) : ℤ) = (floatDen : ℤ) - 2 * wr := by omega
  rw [← hc]
  exact_mod_cast h1

/-! ### Arithmetic -/

/-- A scaled value is far inside the centred range of `P`:
from `2F·|Q·R − t·T| ≤ Q·(F + 2r)`, `2F²·|T| ≤ N·(Q·(F + 2w))²` and the side condition,
`2F·|R| ≤ P·(F − 2wr) − F`. -/
theorem scaled_small (Q F t Nn w wr r Pm R T : ℤ) (hQ : 0 < Q) (hF : 0 < F) (ht : 0 ≤ t)
    (h2 : 2 * F * |Q * R - t * T| ≤ Q * (F + 2 * r))
    (h3 : 2 * F ^ 2 * |T| ≤ Nn * (Q * (F + 2 * w)) ^ 2)
    (h4 : t * Nn * Q * (F + 2 * w) ^ 2 + 2 * F ^ 2 + 2 * r * F ≤ Pm * (F - 2 * wr) * F) :
    2 * F * |R| ≤ Pm * (F - 2 * wr) - F := by
  have h1 : Q * |R| ≤ |Q * R - t * T| + t * |T| := by
    have e : Q * |R| = |Q * R| := by rw [abs_mul, abs_of_pos hQ]
    have e2 : t * |T| = |t * T| := by rw [abs_mul, abs_of_nonneg ht]
    rw [e, e2]
    have := abs_add_le (Q * R - t * T) (t * T)
    simpa using this
  have a1 : 2 * F ^ 2 * (Q * |R|) ≤ 2 * F ^ 2 * (|Q * R - t * T| + t * |T|) :=
    mul_le_mul_of_nonneg_left h1 (by positivity)
  have a2 : F * (2 * F * |Q * R - t * T|) ≤ F * (Q * (F + 2 * r)) :=
    mul_le_mul_of_nonneg_left h2 hF.le
  have a3 : t * (2 * F ^ 2 * |T|) ≤ t * (Nn * (Q * (F + 2 * w)) ^ 2) :=
    mul_le_mul_of_nonneg_left h3 ht
  have a4 : Q * (t * Nn * Q * (F + 2 * w) ^ 2 + 2 * F ^ 2 + 2 * r * F) ≤
      Q * (Pm * (F - 2 * wr) * F) := mul_le_mul_of_nonneg_left h4 hQ.le
  have a5 : (Q * F) * (2 * F * |R|) ≤ (Q * F) * (Pm * (F - 2 * wr) - F) := by
    have e1 : (Q * F) * (2 * F * |R|) = 2 * F ^ 2 * (Q * |R|) := by ring
    have e2 : 2 * F ^ 2 * (|Q * R - t * T| + t * |T|) =
        F * (2 * F * |Q * R - t * T|) + t * (2 * F ^ 2 * |T|) := by ring
    have e3 : F * (Q * (F + 2 * r)) + t * (Nn * (Q * (F + 2 * w)) ^ 2) =
        Q * (t * Nn * Q * (F + 2 * w) ^ 2 + 2 * F ^ 2 + 2 * r * F) - Q * F ^ 2 := by ring
    have e4 : (Q * F) * (Pm * (F - 2 * wr) - F) = Q * (Pm * (F - 2 * wr) * F) - Q * F ^ 2 := by
      ring
    rw [e1, e4]
    linarith
  exact le_of_mul_le_mul_left a5 (mul_pos hQ hF)

/-- Two integers congruent modulo `P`, one within `P·(F + 2wr)/(2F)` and the other within
`(P·(F − 2wr) − F)/(2F)`, are equal. -/
theorem eq_of_small (Pm F wr V R : ℤ) (hF : 0 < F) (hd : Pm ∣ V - R)
    (hV : 2 * F * |V| ≤ Pm * (F + 2 * wr)) (hR : 2 * F * |R| ≤ Pm * (F - 2 * wr) - F) :
    V = R := by
  have h1 : |V - R| ≤ |V| + |R| := abs_sub _ _
  have h2 : 2 * F * |V - R| ≤ 2 * F * (|V| + |R|) :=
    mul_le_mul_of_nonneg_left h1 (by positivity)
  have h3 : (2 * F) * |V - R| < (2 * F) * Pm := by
    have e : (2 * F) * Pm = Pm * (F + 2 * wr) + Pm * (F - 2 * wr) := by ring
    rw [e]
    linarith
  have hlt : |V - R| < Pm := lt_of_mul_lt_mul_left h3 (by positivity)
  have := Int.eq_zero_of_abs_lt_dvd hd hlt
  omega

/-- From `2F·|x| ≤ Q·(F + 2w)` and `2w ≤ c·F`: `2·|x| ≤ Q·(1 + c)`. -/
theorem two_abs_le_of_tol (Q F w c x : ℤ) (hQ : 0 ≤ Q) (hF : 0 < F) (hc : 2 * w ≤ c * F)
    (h : 2 * F * |x| ≤ Q * (F + 2 * w)) : 2 * |x| ≤ Q * (1 + c) := by
  have h1 : Q * (2 * w) ≤ Q * (c * F) := mul_le_mul_of_nonneg_left hc hQ
  have h2 : F * (2 * |x|) ≤ F * (Q * (1 + c)) := by
    have e1 : F * (2 * |x|) = 2 * F * |x| := by ring
    have e2 : F * (Q * (1 + c)) = Q * F + Q * (c * F) := by ring
    have e3 : Q * (F + 2 * w) = Q * F + Q * (2 * w) := by ring
    rw [e1, e2]
    linarith
  exact le_of_mul_le_mul_left h2 hF

/-! ### Polynomials -/

/-- An operand as the algorithm multiplies it: the representative `FloatScalar.switchVal`. -/
def lift (S : Fl.Sums) (qs : List ℕ) (a : IntPoly N) : IntPoly N :=
  ⟨fun i => FloatScalar.switchVal S qs (a.coeff i)⟩

/-- The base switch of the limbs of `a` gives the limbs of `b`, where `b` has the switched
values as coefficients. -/
theorem switchBasis_toLimbs (S : Fl.Sums) (qs ps : List ℕ) (a b : IntPoly N)
    (h : ∀ i, FloatScalar.switchVal S qs (a.coeff i) = b.coeff i) :
    Fl.switchBasis S qs ps (toLimbs qs a) = toLimbs ps b := by
  unfold Fl.switchBasis
  rw [toLimbs_eq ps]
  refine List.map_congr_left fun p _ => ?_
  ext i
  show Fl.switch1 S qs (residues (toLimbs qs a) i) p = b.coeff i % p
  rw [residues_toLimbs, FloatScalar.switch1_eq, h]

/-- **Base extension**: the limbs modulo `qs ++ ps` of `lift`. -/
theorem expand_toLimbs (S : Fl.Sums) (qs ps : List ℕ) (hpos : ∀ q ∈ qs, 0 < q)
    (hcop : qs.Pairwise Nat.Coprime) (a : IntPoly N) :
    Fl.expand S qs ps (toLimbs qs a) = toLimbs (qs ++ ps) (lift S qs a) := by
  unfold Fl.expand
  rw [switchBasis_toLimbs S qs ps a (lift S qs a) (fun _ => rfl)]
  have e : toLimbs (qs ++ ps) (lift S qs a) =
      toLimbs qs (lift S qs a) ++ toLimbs ps (lift S qs a) := List.map_append
  rw [e]
  congr 1
  refine (MulPOverQ.toLimbs_congr qs _ _ fun q hq i => ?_).symm
  exact dvd_trans (by exact_mod_cast List.dvd_prod hq) (FloatScalar.switchVal_dvd S qs hpos hcop _)

/-- **Scale and round**: the limbs modulo `ps` of a polynomial within `1/2 + r/2⁵³` of `t·T/Q`,
coefficient by coefficient. -/
theorem scaleRound_toLimbs (S : Fl.Sums) (hS : Fl.SumsOK S) (t : ℕ) (qs ps : List ℕ)
    (hpos : ∀ m ∈ qs ++ ps, 0 < m) (hcop : (qs ++ ps).Pairwise Nat.Coprime)
    (hfb : floatBasisOK qs = true) (T : IntPoly N) :
    ∃ R : IntPoly N,
      Fl.scaleRound S t qs ps (toLimbs (qs ++ ps) T) = toLimbs ps R ∧
      ∀ i, 2 * (floatDen : ℤ) * |(qs.prod : ℤ) * R.coeff i - t * T.coeff i| ≤
        (qs.prod : ℤ) * ((floatDen : ℤ) + 2 * (doubleSr qs : ℤ)) := by
  choose R hR1 hR2 using fun i : Fin N =>
    FloatScalar.scale1_tol S hS t qs ps hpos hcop hfb (T.coeff i)
  refine ⟨⟨R⟩, ?_, hR2⟩
  unfold Fl.scaleRound
  have e : toLimbs (qs ++ ps) T = toLimbs qs T ++ toLimbs ps T := List.map_append
  have hl : (toLimbs qs T).length = qs.length := List.length_map _
  rw [e, List.take_left' hl, List.drop_left' hl]
  apply List.ext_getElem
  · simp [toLimbs_eq]
  · intro n h1 h2
    have hn : n < ps.length := by simpa [toLimbs_eq] using h2
    simp only [List.getElem_zipWith, toLimbs_eq, List.getElem_map]
    ext i
    show Fl.scale1 S t qs ps (residues (toLimbs qs T) i) ps[n] (T.coeff i % ps[n]) =
      R i % ps[n]
    rw [residues_toLimbs]
    exact hR1 i ⟨n, hn⟩

/-- **One component of the result**: scaling, switching back and reconstructing the limbs of an
integer polynomial `T` of bounded size gives, modulo `Q`, a polynomial within
`rho/2` of `t·T/Q`. -/
theorem component (S : Fl.Sums) (hS : Fl.SumsOK S) (t : ℕ) (qs ps : List ℕ)
    (hpos : ∀ m ∈ qs ++ ps, 0 < m) (hcop : (qs ++ ps).Pairwise Nat.Coprime)
    (hfq : floatBasisOK qs = true) (hfp : floatBasisOK ps = true)
    (hok : (hpsSlack t N qs.prod ps.prod (doubleSw qs.length) (doubleSw ps.length)
      (doubleSr qs)).ok = true)
    (T : IntPoly N)
    (hT : ∀ i, 2 * (floatDen : ℤ) ^ 2 * |T.coeff i| ≤
      (N : ℤ) * ((qs.prod : ℤ) * ((floatDen : ℤ) + 2 * (doubleSw qs.length : ℤ))) ^ 2) :
    ∃ X : IntPoly N,
      (∀ i, 2 * |(qs.prod : ℤ) * X.coeff i - (t : ℤ) * T.coeff i| ≤
        (qs.prod : ℤ) * ((hpsSlack t N qs.prod ps.prod (doubleSw qs.length) (doubleSw ps.length)
          (doubleSr qs)).rho : ℤ)) ∧
      ofInt qs.prod (reconstruct qs (Fl.switchBasis S ps qs
        (Fl.scaleRound S t qs ps (toLimbs (qs ++ ps) T)))) = ofInt qs.prod X := by
  have hposq : ∀ q ∈ qs, 0 < q := fun q hq => hpos q (List.mem_append_left _ hq)
  have hposp : ∀ p ∈ ps, 0 < p := fun p hp => hpos p (List.mem_append_right _ hp)
  have hcopq : qs.Pairwise Nat.Coprime := (List.pairwise_append.mp hcop).1
  have hcopp : ps.Pairwise Nat.Coprime := (List.pairwise_append.mp hcop).2.1
  have hQ : (0 : ℤ) < (qs.prod : ℤ) := by exact_mod_cast prod_pos' qs hposq
  have hF : (0 : ℤ) < (floatDen : ℤ) := by exact_mod_cast FloatScalar.floatDen_pos
  obtain ⟨hwr, hsize⟩ := hpsSlack_ok_int _ _ _ _ _ _ _ hok
  obtain ⟨R, hR1, hR2⟩ := scaleRound_toLimbs S hS t qs ps hpos hcop hfq T
  refine ⟨R, fun i => ?_, ?_⟩
  · rw [hpsSlack_rho]
    have hc : (2 : ℤ) * (doubleSr qs : ℤ) ≤ (ceilDiv (2 * doubleSr qs) floatDen : ℤ) * floatDen := by
      exact_mod_cast MulPOverQ.le_ceilDiv_mul (2 * doubleSr qs) floatDen FloatScalar.floatDen_pos
    have := two_abs_le_of_tol _ _ _ _ _ hQ.le hF hc (hR2 i)
    rw [Nat.cast_add, Nat.cast_one]
    exact this
  · have hsw : ∀ i, FloatScalar.switchVal S ps (R.coeff i) = R.coeff i := fun i =>
      eq_of_small _ _ _ _ _ hF (FloatScalar.switchVal_dvd S ps hposp hcopp _)
        (FloatScalar.switchVal_bound S hS ps hposp hcopp hfp _)
        (scaled_small _ _ _ _ _ _ _ _ _ _ hQ hF (by positivity) (hR2 i) (hT i) hsize)
    rw [hR1, switchBasis_toLimbs S ps qs R R hsw, reconstruct_toLimbs qs hposq hcopq,
      ofInt_modPoly]

/-- The size of a product of two lifts. -/
theorem abs_coeff_mul_le (Q F w : ℤ) (hF : 0 < F) (a b : IntPoly N)
    (ha : ∀ i, 2 * F * |a.coeff i| ≤ Q * (F + 2 * w))
    (hb : ∀ i, 2 * F * |b.coeff i| ≤ Q * (F + 2 * w)) (i : Fin N) :
    4 * F ^ 2 * |(a * b).coeff i| ≤ (N : ℤ) * (Q * (F + 2 * w)) ^ 2 := by
  have h2F : (0 : ℤ) < 2 * F := by positivity
  have hle : ∀ x : ℤ, 2 * F * x ≤ Q * (F + 2 * w) → x ≤ Q * (F + 2 * w) / (2 * F) := fun x hx =>
    Int.le_ediv_of_mul_le h2F (by linarith)
  have h := abs_coeff_mul_le_N a b _ _ (fun j => hle _ (ha j)) (fun j => hle _ (hb j)) i
  have hd0 : 0 ≤ Q * (F + 2 * w) / (2 * F) := (abs_nonneg _).trans (hle _ (ha i))
  have hd1 : Q * (F + 2 * w) / (2 * F) * (2 * F) ≤ Q * (F + 2 * w) :=
    Int.ediv_mul_le _ h2F.ne'
  generalize Q * (F + 2 * w) / (2 * F) = D at h hd0 hd1
  generalize Q * (F + 2 * w) = M at hd1 ⊢
  have hsq : (D * (2 * F)) ^ 2 ≤ M ^ 2 := pow_le_pow_left₀ (by positivity) hd1 2
  have h1 : 4 * F ^ 2 * |(a * b).coeff i| ≤ 4 * F ^ 2 * ((N : ℤ) * D * D) :=
    mul_le_mul_of_nonneg_left h (by positivity)
  have h3 : (N : ℤ) * (D * (2 * F)) ^ 2 ≤ (N : ℤ) * M ^ 2 :=
    mul_le_mul_of_nonneg_left hsq (by positivity)
  have e : 4 * F ^ 2 * ((N : ℤ) * D * D) = (N : ℤ) * (D * (2 * F)) ^ 2 := by ring
  linarith

/-! ### The theorem -/

/-- **HPS multiplication with sums within the tolerances multiplies representatives of bounded
size and rounds within a bounded distance**: with the lifts `c.map (lift S qs)`,
`d.map (lift S qs)`, the hypotheses of `Challenge.BFVMul.stepOK_mul_lifted` (and, for `c = d`,
of `stepOK_square_lifted`) at `Q = qs.prod`, with the slack
`hpsSlack t N Q P (doubleSw k) (doubleSw |ps|) (doubleSr qs)`. -/
theorem hpsMul_lifted' (S : Fl.Sums) (hS : Fl.SumsOK S) (t : ℕ) (qs ps : List ℕ)
    (haux : floatAuxOK? qs ps = true)
    (hok : (hpsSlack t N qs.prod ps.prod (doubleSw qs.length) (doubleSw ps.length)
      (doubleSr qs)).ok = true)
    (c d : List (IntPoly N)) (hc : c.length = 2) (hd : d.length = 2) :
    ∃ X : List (IntPoly N), X.length = 3 ∧
      (c.map (lift S qs)).map (ofInt qs.prod) = c.map (ofInt qs.prod) ∧
      (d.map (lift S qs)).map (ofInt qs.prod) = d.map (ofInt qs.prod) ∧
      (∀ p ∈ c.map (lift S qs), 2 * normInf p ≤
        qs.prod + (hpsSlack t N qs.prod ps.prod (doubleSw qs.length) (doubleSw ps.length)
          (doubleSr qs)).e) ∧
      (∀ p ∈ d.map (lift S qs), 2 * normInf p ≤
        qs.prod + (hpsSlack t N qs.prod ps.prod (doubleSw qs.length) (doubleSw ps.length)
          (doubleSr qs)).e) ∧
      (∀ (j : ℕ) (i : Fin N),
        2 * |(qs.prod : ℤ) * (X.getD j 0).coeff i -
            (t : ℤ) * ((Challenge.Source.tensor (c.map (lift S qs))
              (d.map (lift S qs))).getD j 0).coeff i|
          ≤ (qs.prod : ℤ) * (hpsSlack t N qs.prod ps.prod (doubleSw qs.length)
              (doubleSw ps.length) (doubleSr qs)).rho) ∧
      (Fl.hpsMul S t qs ps c d).map (ofInt qs.prod) = X.map (ofInt qs.prod) := by
  obtain ⟨hfq, hfp, hm, hcop⟩ := (floatAuxOK_iff qs ps).mp haux
  have hpos : ∀ m ∈ qs ++ ps, 0 < m := fun m h => by have := (hm m h).1; omega
  have hposq : ∀ q ∈ qs, 0 < q := fun q hq => hpos q (List.mem_append_left _ hq)
  have hcopq : qs.Pairwise Nat.Coprime := (List.pairwise_append.mp hcop).1
  have hQ : (0 : ℤ) < (qs.prod : ℤ) := by exact_mod_cast prod_pos' qs hposq
  have hF : (0 : ℤ) < (floatDen : ℤ) := by exact_mod_cast FloatScalar.floatDen_pos
  obtain ⟨a₀, a₁, rfl⟩ := List.length_eq_two.mp hc
  obtain ⟨b₀, b₁, rfl⟩ := List.length_eq_two.mp hd
  -- sizes of the representatives
  have hsz : ∀ (a : IntPoly N) (i : Fin N), 2 * (floatDen : ℤ) * |(lift S qs a).coeff i| ≤
      (qs.prod : ℤ) * ((floatDen : ℤ) + 2 * (doubleSw qs.length : ℤ)) := fun a i =>
    FloatScalar.switchVal_bound S hS qs hposq hcopq hfq (a.coeff i)
  have hn : ∀ a : IntPoly N, 2 * normInf (lift S qs a) ≤
      qs.prod + (hpsSlack t N qs.prod ps.prod (doubleSw qs.length) (doubleSw ps.length)
        (doubleSr qs)).e := fun a =>
    MulPOverQ.two_normInf_le _ _ fun i => by
      rw [hpsSlack_e]
      have hc : (2 : ℤ) * ((qs.prod : ℤ) * (doubleSw qs.length : ℤ)) ≤
          (ceilDiv (2 * qs.prod * doubleSw qs.length) floatDen : ℤ) * floatDen := by
        have := MulPOverQ.le_ceilDiv_mul (2 * qs.prod * doubleSw qs.length) floatDen
          FloatScalar.floatDen_pos
        have h' : (2 : ℤ) * qs.prod * doubleSw qs.length ≤
            (ceilDiv (2 * qs.prod * doubleSw qs.length) floatDen : ℤ) * floatDen := by
          exact_mod_cast this
        linarith
      have h1 := hsz a i
      have h2 : (floatDen : ℤ) * (2 * |(lift S qs a).coeff i|) ≤
          (floatDen : ℤ) * ((qs.prod : ℤ) +
            (ceilDiv (2 * qs.prod * doubleSw qs.length) floatDen : ℤ)) := by
        have e1 : (floatDen : ℤ) * (2 * |(lift S qs a).coeff i|) =
            2 * (floatDen : ℤ) * |(lift S qs a).coeff i| := by ring
        rw [e1]
        linarith
      have := le_of_mul_le_mul_left h2 hF
      rw [Nat.cast_add]
      exact this
  have hcg : ∀ a : IntPoly N, ofInt qs.prod (lift S qs a) = ofInt qs.prod a := fun a =>
    MulPOverQ.ofInt_eq_of_dvd _ (lift S qs a) a fun i =>
      FloatScalar.switchVal_dvd S qs hposq hcopq _
  -- sizes of the tensor components
  have hmul := fun a b : IntPoly N =>
    abs_coeff_mul_le (N := N) (qs.prod : ℤ) (floatDen : ℤ) (doubleSw qs.length : ℤ) hF
      (lift S qs a) (lift S qs b) (hsz a) (hsz b)
  have hMnn : (0 : ℤ) ≤ (N : ℤ) *
      ((qs.prod : ℤ) * ((floatDen : ℤ) + 2 * (doubleSw qs.length : ℤ))) ^ 2 := by positivity
  have hcomp := component S hS t qs ps hpos hcop hfq hfp hok
  obtain ⟨X0, hr0, ho0⟩ := hcomp (lift S qs a₀ * lift S qs b₀) fun i => by
    have := hmul a₀ b₀ i
    have := abs_nonneg ((lift S qs a₀ * lift S qs b₀).coeff i)
    nlinarith [sq_nonneg (floatDen : ℤ)]
  obtain ⟨X1, hr1, ho1⟩ := hcomp (lift S qs a₀ * lift S qs b₁ + lift S qs a₁ * lift S qs b₀)
    fun i => by
      rw [coeff_add']
      have h1 := hmul a₀ b₁ i
      have h2 := hmul a₁ b₀ i
      have h3 := abs_add_le ((lift S qs a₀ * lift S qs b₁).coeff i)
        ((lift S qs a₁ * lift S qs b₀).coeff i)
      have h4 := mul_le_mul_of_nonneg_left h3
        (show (0 : ℤ) ≤ 2 * (floatDen : ℤ) ^ 2 by positivity)
      linarith
  obtain ⟨X2, hr2, ho2⟩ := hcomp (lift S qs a₁ * lift S qs b₁) fun i => by
    have := hmul a₁ b₁ i
    have := abs_nonneg ((lift S qs a₁ * lift S qs b₁).coeff i)
    nlinarith [sq_nonneg (floatDen : ℤ)]
  refine ⟨[X0, X1, X2], rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [List.map_cons, List.map_nil, hcg]
  · simp only [List.map_cons, List.map_nil, hcg]
  · intro p hp
    simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl <;> exact hn _
  · intro p hp
    simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl <;> exact hn _
  · intro j i
    rcases j with _ | _ | _ | j
    · exact hr0 i
    · exact hr1 i
    · exact hr2 i
    · show 2 * |(qs.prod : ℤ) * (0 : IntPoly N).coeff i - (t : ℤ) * (0 : IntPoly N).coeff i| ≤ _
      simp only [coeff_zero', mul_zero, sub_zero, abs_zero]
      positivity
  · unfold Fl.hpsMul
    simp only [List.map_cons, List.map_nil, expand_toLimbs S qs ps hposq hcopq, tensor_toLimbs,
      source_tensor_two, ho0, ho1, ho2]

/-- `hpsMul_lifted'` with the representatives existential: the hypotheses of
`Challenge.BFVMul.stepOK_mul_lifted`, in the form of `MulPOverQ.poverqMul_lifted`. -/
theorem hpsMul_lifted (S : Fl.Sums) (hS : Fl.SumsOK S) (t : ℕ) (qs ps : List ℕ)
    (haux : floatAuxOK? qs ps = true)
    (hok : (hpsSlack t N qs.prod ps.prod (doubleSw qs.length) (doubleSw ps.length)
      (doubleSr qs)).ok = true)
    (c d : List (IntPoly N)) (hc : c.length = 2) (hd : d.length = 2) :
    ∃ A B X : List (IntPoly N), X.length = 3 ∧
      A.map (ofInt qs.prod) = c.map (ofInt qs.prod) ∧
      B.map (ofInt qs.prod) = d.map (ofInt qs.prod) ∧
      (∀ p ∈ A, 2 * normInf p ≤
        qs.prod + (hpsSlack t N qs.prod ps.prod (doubleSw qs.length) (doubleSw ps.length)
          (doubleSr qs)).e) ∧
      (∀ p ∈ B, 2 * normInf p ≤
        qs.prod + (hpsSlack t N qs.prod ps.prod (doubleSw qs.length) (doubleSw ps.length)
          (doubleSr qs)).e) ∧
      (∀ (j : ℕ) (i : Fin N),
        2 * |(qs.prod : ℤ) * (X.getD j 0).coeff i -
            (t : ℤ) * ((Challenge.Source.tensor A B).getD j 0).coeff i|
          ≤ (qs.prod : ℤ) * (hpsSlack t N qs.prod ps.prod (doubleSw qs.length)
              (doubleSw ps.length) (doubleSr qs)).rho) ∧
      (Fl.hpsMul S t qs ps c d).map (ofInt qs.prod) = X.map (ofInt qs.prod) := by
  obtain ⟨X, h⟩ := hpsMul_lifted' S hS t qs ps haux hok c d hc hd
  exact ⟨_, _, X, h⟩

/-- The squaring form: one list of representatives on both sides of the tensor product (the
hypotheses of `Challenge.BFVMul.stepOK_square_lifted`). -/
theorem hpsSquare_lifted (S : Fl.Sums) (hS : Fl.SumsOK S) (t : ℕ) (qs ps : List ℕ)
    (haux : floatAuxOK? qs ps = true)
    (hok : (hpsSlack t N qs.prod ps.prod (doubleSw qs.length) (doubleSw ps.length)
      (doubleSr qs)).ok = true)
    (c : List (IntPoly N)) (hc : c.length = 2) :
    ∃ A X : List (IntPoly N), X.length = 3 ∧
      A.map (ofInt qs.prod) = c.map (ofInt qs.prod) ∧
      (∀ p ∈ A, 2 * normInf p ≤
        qs.prod + (hpsSlack t N qs.prod ps.prod (doubleSw qs.length) (doubleSw ps.length)
          (doubleSr qs)).e) ∧
      (∀ (j : ℕ) (i : Fin N),
        2 * |(qs.prod : ℤ) * (X.getD j 0).coeff i -
            (t : ℤ) * ((Challenge.Source.tensor A A).getD j 0).coeff i|
          ≤ (qs.prod : ℤ) * (hpsSlack t N qs.prod ps.prod (doubleSw qs.length)
              (doubleSw ps.length) (doubleSr qs)).rho) ∧
      (Fl.hpsMul S t qs ps c c).map (ofInt qs.prod) = X.map (ofInt qs.prod) := by
  obtain ⟨X, hX, hA, -, hAn, -, hround, hout⟩ := hpsMul_lifted' S hS t qs ps haux hok c c hc hc
  exact ⟨_, X, hX, hA, hAn, hround, hout⟩

end FHE.BFV.FloatHPS
