import Challenge.Families.FloatTol
import FHE.BFV.FloatHPS
import FHE.BFV.FloatLeveled

/-!
# Validation.Families.FloatTolCore — the HPS-family integer facts at any summation tolerance

The lemmas of `FHE.BFV.FloatScalar`, `FloatHPS`, `FloatPOverQ`, `FloatLeveled` that use the
tolerance hypothesis `Fl.SumsOK S`, restated and re-proved for `Challenge.Families.SumsOK' tw tr S`
with arbitrary tolerance functions `tw : ℕ → ℕ`, `tr : List ℕ → ℕ` (suffix `T`). The proofs are
those of the FHE files with `doubleSw`, `doubleSr` replaced by `tw`, `tr`; the lemmas that do not
use the tolerance are reused from the FHE files. One place uses more than the tolerance bounds:
OpenFHE's `doubleSw` is monotone (`FHE.BFV.FloatPOverQ.doubleSw_mono`), used to charge the
switches from `P`, `Q_l`, `P_l` at the tolerance of `k` moduli; here that is the hypothesis
`hw : ∀ m ≤ k, tw m ≤ tw k` of `poverqMul_liftedT`, `leveledMul_liftedT`. Locked definitions
are read through local `rfl` equations, never unfolded by name.
-/

namespace Validation.Families.FloatTol
open Challenge.Families

section scalar
open FHE.BFV
open Spec NPoly Scheme Challenge.BFVMul Challenge.BFVMul.HPS Spec.BudgetBFV
open FHE.BFV.MulHPS FHE.BFV.FloatScalar

/-- `HPS.theta`, by `rfl`. -/
theorem theta_eqT (t : ℕ) (qs ps : List ℕ) :
    HPS.theta t qs ps = qs.map fun q => (t : ℤ) * ps.prod * invMod (qs.prod * ps.prod / q) q :=
  rfl

/-- **The switched representative is within `Q/2 + Q·tw k/2⁵³`.** -/
theorem switchVal_boundT (tw : ℕ → ℕ) (tr : List ℕ → ℕ) (S : Fl.Sums) (hS : SumsOK' tw tr S) (qs : List ℕ)
    (hpos : ∀ q ∈ qs, 0 < q) (hcop : qs.Pairwise Nat.Coprime) (hfb : floatBasisOK qs = true)
    (X : ℤ) :
    2 * (floatDen : ℤ) * |switchVal S qs X| ≤
      (qs.prod : ℤ) * ((floatDen : ℤ) + 2 * (tw qs.length : ℤ)) := by
  have _ := hcop
  have hQ : 0 < qs.prod := prod_pos' qs hpos
  have hred : Fl.Reduced qs (qs.map fun q : ℕ => X % q * invMod (qs.prod / q) q % q) :=
    reduced_map qs _ fun q hq =>
      have hq' : (0 : ℤ) < (q : ℤ) := by exact_mod_cast hpos q hq
      ⟨Int.emod_nonneg _ hq'.ne', Int.emod_lt_of_pos _ hq'⟩
  obtain ⟨s, hs1, hs2⟩ := hS.1 qs _ hfb hred
  rw [exactSw_map] at hs2
  refine floor_core qs.prod (tw qs.length) hQ _ _ s _ hs1 hs2 ?_
  rw [cast_sum_hat qs qs.prod (fun q hq => ⟨hpos q hq, List.dvd_prod hq⟩)]
  ring

/-- **Scaling with a tolerant fractional sum**: from the residues of any integer `T` modulo
`qs ++ ps`, `Fl.scale1 S` computes the residues modulo every `pⱼ` of one integer `R` with
`2·2⁵³·|Q·R − t·T| ≤ Q·(2⁵³ + 2·tr qs)`. -/
theorem scale1_tolT (tw : ℕ → ℕ) (tr : List ℕ → ℕ) (S : Fl.Sums) (hS : SumsOK' tw tr S) (t : ℕ) (qs ps : List ℕ)
    (hpos : ∀ m ∈ qs ++ ps, 0 < m) (hcop : (qs ++ ps).Pairwise Nat.Coprime)
    (hfb : floatBasisOK qs = true) (T : ℤ) :
    ∃ R : ℤ,
      (∀ j : Fin ps.length,
        Fl.scale1 S t qs ps (qs.map fun q : ℕ => T % q) ps[j.1] (T % ps[j.1]) = R % ps[j.1]) ∧
      2 * (floatDen : ℤ) * |(qs.prod : ℤ) * R - t * T| ≤
        (qs.prod : ℤ) * ((floatDen : ℤ) + 2 * (tr qs : ℤ)) := by
  have hposq : ∀ q ∈ qs, 0 < q := fun q hq => hpos q (List.mem_append_left _ hq)
  have hQ : 0 < qs.prod := prod_pos' qs hposq
  obtain ⟨I, hI⟩ := scale_decomp t qs ps hpos hcop T
  have hred1 : Fl.Reduced qs (Fl.fracNums t qs ps) := by
    rw [fracNums_eq]
    exact reduced_map qs _ fun q hq =>
      have hq' : (0 : ℤ) < (q : ℤ) := by exact_mod_cast hposq q hq
      ⟨Int.emod_nonneg _ hq'.ne', Int.emod_lt_of_pos _ hq'⟩
  have hred2 : Fl.Reduced qs (qs.map fun q : ℕ => T % q) :=
    reduced_map qs _ fun q hq =>
      have hq' : (0 : ℤ) < (q : ℤ) := by exact_mod_cast hposq q hq
      ⟨Int.emod_nonneg _ hq'.ne', Int.emod_lt_of_pos _ hq'⟩
  obtain ⟨s, hs1, hs2⟩ := hS.2 qs _ _ hfb hred1 hred2
  refine ⟨I + S.sr qs (Fl.fracNums t qs ps) (qs.map fun q : ℕ => T % q), fun j => ?_, ?_⟩
  · have h := scale1_eq t qs ps hpos hcop T j
    rw [hI, roundDiv_mul_add _ _ _ hQ] at h
    have hz : List.zipWith
        (fun (θ : ℤ × ℕ) xi => xi * (θ.1 % θ.2) * ((qs.prod / θ.2 : ℕ) : ℤ))
        ((theta t qs ps).zip qs) (qs.map fun q : ℕ => T % q) =
        qs.map fun q : ℕ =>
          T % q * ((t : ℤ) * ps.prod * invMod (qs.prod * ps.prod / q) q % q) *
            ((qs.prod / q : ℕ) : ℤ) := by
      rw [theta_eqT]
      simp only [map_zip_self, zipWith_map_map]
    rw [scale1_fl, h, hz]
    have h2 : ((I + roundDiv (qs.map fun q : ℕ =>
          T % q * ((t : ℤ) * ps.prod * invMod (qs.prod * ps.prod / q) q % q) *
            ((qs.prod / q : ℕ) : ℤ)).sum qs.prod) % (ps[j.1] : ℤ) -
        roundDiv (qs.map fun q : ℕ =>
          T % q * ((t : ℤ) * ps.prod * invMod (qs.prod * ps.prod / q) q % q) *
            ((qs.prod / q : ℕ) : ℤ)).sum qs.prod +
        S.sr qs (Fl.fracNums t qs ps) (qs.map fun q : ℕ => T % q)) ≡
        I + S.sr qs (Fl.fracNums t qs ps) (qs.map fun q : ℕ => T % q) [ZMOD (ps[j.1] : ℤ)] := by
      have := ((Int.mod_modEq (I + roundDiv (qs.map fun q : ℕ =>
          T % q * ((t : ℤ) * ps.prod * invMod (qs.prod * ps.prod / q) q % q) *
            ((qs.prod / q : ℕ) : ℤ)).sum qs.prod) (ps[j.1] : ℤ)).sub_right
          (roundDiv (qs.map fun q : ℕ =>
          T % q * ((t : ℤ) * ps.prod * invMod (qs.prod * ps.prod / q) q % q) *
            ((qs.prod / q : ℕ) : ℤ)).sum qs.prod)).add_right
          (S.sr qs (Fl.fracNums t qs ps) (qs.map fun q : ℕ => T % q))
      rwa [add_sub_cancel_right] at this
    exact h2.eq
  · rw [fracNums_eq, exactSr_map] at hs2
    have hc := floor_core qs.prod (tr qs) hQ
      (qs.map fun q : ℕ => T % q * ((t : ℤ) * ps.prod * invMod (qs.prod * ps.prod / q) q % q) *
        ((qs.prod / q : ℕ) : ℤ)).sum _ s _ hs1 hs2 (by
        rw [cast_sum_hat qs qs.prod (fun q hq => ⟨hposq q hq, List.dvd_prod hq⟩)
          (fun q : ℕ => T % q * ((t : ℤ) * ps.prod * invMod (qs.prod * ps.prod / q) q % q))]
        simp only [Int.cast_mul]
        ring)
    have e : (qs.prod : ℤ) * (I + S.sr qs (Fl.fracNums t qs ps) (qs.map fun q : ℕ => T % q)) -
        t * T = -((qs.map fun q : ℕ =>
          T % q * ((t : ℤ) * ps.prod * invMod (qs.prod * ps.prod / q) q % q) *
            ((qs.prod / q : ℕ) : ℤ)).sum -
          S.sr qs (Fl.fracNums t qs ps) (qs.map fun q : ℕ => T % q) * qs.prod) := by
      rw [hI]
      ring
    rw [e, abs_neg]
    exact hc

end scalar

section hps
open FHE.BFV
open Spec NPoly Scheme Challenge.BFVMul Challenge.BFVMul.HPS Spec.BudgetBFV
open Validation.Ring Validation.Scheme Validation.Source
open FHE.BFV.MulHPS FHE.BFV.FloatHPS
variable {N : ℕ}

/-- `Fl.scaleRound`, by `rfl`. -/
theorem scaleRound_eqT (S : Fl.Sums) (t : ℕ) (qs ps : List ℕ) (x : List (IntPoly N)) :
    Fl.scaleRound S t qs ps x = List.zipWith
      (fun p xp =>
        (⟨fun i => Fl.scale1 S t qs ps (HPS.residues (x.take qs.length) i) p (xp.coeff i)⟩ :
          IntPoly N))
      ps (x.drop qs.length) := rfl

/-- `Fl.hpsMul`, by `rfl`. -/
theorem hpsMul_eqT (S : Fl.Sums) (t : ℕ) (qs ps : List ℕ) (c d : List (IntPoly N)) :
    Fl.hpsMul S t qs ps c d =
      (HPS.tensor (qs ++ ps) (c.map fun a => Fl.expand S qs ps (HPS.toLimbs qs a))
        (d.map fun a => Fl.expand S qs ps (HPS.toLimbs qs a))).map fun x =>
        HPS.reconstruct qs (Fl.switchBasis S ps qs (Fl.scaleRound S t qs ps x)) := rfl

/-- **Scale and round**: the limbs modulo `ps` of a polynomial within `1/2 + r/2⁵³` of `t·T/Q`,
coefficient by coefficient. -/
theorem scaleRound_toLimbsT (tw : ℕ → ℕ) (tr : List ℕ → ℕ) (S : Fl.Sums) (hS : SumsOK' tw tr S) (t : ℕ) (qs ps : List ℕ)
    (hpos : ∀ m ∈ qs ++ ps, 0 < m) (hcop : (qs ++ ps).Pairwise Nat.Coprime)
    (hfb : floatBasisOK qs = true) (T : IntPoly N) :
    ∃ R : IntPoly N,
      Fl.scaleRound S t qs ps (toLimbs (qs ++ ps) T) = toLimbs ps R ∧
      ∀ i, 2 * (floatDen : ℤ) * |(qs.prod : ℤ) * R.coeff i - t * T.coeff i| ≤
        (qs.prod : ℤ) * ((floatDen : ℤ) + 2 * (tr qs : ℤ)) := by
  choose R hR1 hR2 using fun i : Fin N =>
    scale1_tolT tw tr S hS t qs ps hpos hcop hfb (T.coeff i)
  refine ⟨⟨R⟩, ?_, hR2⟩
  rw [scaleRound_eqT]
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
theorem componentT (tw : ℕ → ℕ) (tr : List ℕ → ℕ) (S : Fl.Sums) (hS : SumsOK' tw tr S) (t : ℕ) (qs ps : List ℕ)
    (hpos : ∀ m ∈ qs ++ ps, 0 < m) (hcop : (qs ++ ps).Pairwise Nat.Coprime)
    (hfq : floatBasisOK qs = true) (hfp : floatBasisOK ps = true)
    (hok : (hpsSlack t N qs.prod ps.prod (tw qs.length) (tw ps.length)
      (tr qs)).ok = true)
    (T : IntPoly N)
    (hT : ∀ i, 2 * (floatDen : ℤ) ^ 2 * |T.coeff i| ≤
      (N : ℤ) * ((qs.prod : ℤ) * ((floatDen : ℤ) + 2 * (tw qs.length : ℤ))) ^ 2) :
    ∃ X : IntPoly N,
      (∀ i, 2 * |(qs.prod : ℤ) * X.coeff i - (t : ℤ) * T.coeff i| ≤
        (qs.prod : ℤ) * ((hpsSlack t N qs.prod ps.prod (tw qs.length) (tw ps.length)
          (tr qs)).rho : ℤ)) ∧
      ofInt qs.prod (reconstruct qs (Fl.switchBasis S ps qs
        (Fl.scaleRound S t qs ps (toLimbs (qs ++ ps) T)))) = ofInt qs.prod X := by
  have hposq : ∀ q ∈ qs, 0 < q := fun q hq => hpos q (List.mem_append_left _ hq)
  have hposp : ∀ p ∈ ps, 0 < p := fun p hp => hpos p (List.mem_append_right _ hp)
  have hcopq : qs.Pairwise Nat.Coprime := (List.pairwise_append.mp hcop).1
  have hcopp : ps.Pairwise Nat.Coprime := (List.pairwise_append.mp hcop).2.1
  have hQ : (0 : ℤ) < (qs.prod : ℤ) := by exact_mod_cast prod_pos' qs hposq
  have hF : (0 : ℤ) < (floatDen : ℤ) := by exact_mod_cast FloatScalar.floatDen_pos
  obtain ⟨hwr, hsize⟩ := hpsSlack_ok_int _ _ _ _ _ _ _ hok
  obtain ⟨R, hR1, hR2⟩ := scaleRound_toLimbsT tw tr S hS t qs ps hpos hcop hfq T
  refine ⟨R, fun i => ?_, ?_⟩
  · rw [hpsSlack_rho]
    have hc : (2 : ℤ) * (tr qs : ℤ) ≤ (ceilDiv (2 * tr qs) floatDen : ℤ) * floatDen := by
      exact_mod_cast MulPOverQ.le_ceilDiv_mul (2 * tr qs) floatDen FloatScalar.floatDen_pos
    have := two_abs_le_of_tol _ _ _ _ _ hQ.le hF hc (hR2 i)
    rw [Nat.cast_add, Nat.cast_one]
    exact this
  · have hsw : ∀ i, FloatScalar.switchVal S ps (R.coeff i) = R.coeff i := fun i =>
      eq_of_small _ _ _ _ _ hF (FloatScalar.switchVal_dvd S ps hposp hcopp _)
        (switchVal_boundT tw tr S hS ps hposp hcopp hfp _)
        (scaled_small _ _ _ _ _ _ _ _ _ _ hQ hF (by positivity) (hR2 i) (hT i) hsize)
    rw [hR1, switchBasis_toLimbs S ps qs R R hsw, reconstruct_toLimbs qs hposq hcopq,
      ofInt_modPoly]

/-- **HPS multiplication with sums within the tolerances multiplies representatives of bounded
size and rounds within a bounded distance**: with the lifts `c.map (lift S qs)`,
`d.map (lift S qs)`, the hypotheses of `Challenge.BFVMul.stepOK_mul_lifted` (and, for `c = d`,
of `stepOK_square_lifted`) at `Q = qs.prod`, with the slack
`hpsSlack t N Q P (tw k) (tw |ps|) (tr qs)`. -/
theorem hpsMul_liftedT (tw : ℕ → ℕ) (tr : List ℕ → ℕ) (S : Fl.Sums) (hS : SumsOK' tw tr S) (t : ℕ) (qs ps : List ℕ)
    (haux : floatAuxOK? qs ps = true)
    (hok : (hpsSlack t N qs.prod ps.prod (tw qs.length) (tw ps.length)
      (tr qs)).ok = true)
    (c d : List (IntPoly N)) (hc : c.length = 2) (hd : d.length = 2) :
    ∃ X : List (IntPoly N), X.length = 3 ∧
      (c.map (lift S qs)).map (ofInt qs.prod) = c.map (ofInt qs.prod) ∧
      (d.map (lift S qs)).map (ofInt qs.prod) = d.map (ofInt qs.prod) ∧
      (∀ p ∈ c.map (lift S qs), 2 * normInf p ≤
        qs.prod + (hpsSlack t N qs.prod ps.prod (tw qs.length) (tw ps.length)
          (tr qs)).e) ∧
      (∀ p ∈ d.map (lift S qs), 2 * normInf p ≤
        qs.prod + (hpsSlack t N qs.prod ps.prod (tw qs.length) (tw ps.length)
          (tr qs)).e) ∧
      (∀ (j : ℕ) (i : Fin N),
        2 * |(qs.prod : ℤ) * (X.getD j 0).coeff i -
            (t : ℤ) * ((Challenge.Source.tensor (c.map (lift S qs))
              (d.map (lift S qs))).getD j 0).coeff i|
          ≤ (qs.prod : ℤ) * (hpsSlack t N qs.prod ps.prod (tw qs.length)
              (tw ps.length) (tr qs)).rho) ∧
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
      (qs.prod : ℤ) * ((floatDen : ℤ) + 2 * (tw qs.length : ℤ)) := fun a i =>
    switchVal_boundT tw tr S hS qs hposq hcopq hfq (a.coeff i)
  have hn : ∀ a : IntPoly N, 2 * normInf (lift S qs a) ≤
      qs.prod + (hpsSlack t N qs.prod ps.prod (tw qs.length) (tw ps.length)
        (tr qs)).e := fun a =>
    MulPOverQ.two_normInf_le _ _ fun i => by
      rw [hpsSlack_e]
      have hc : (2 : ℤ) * ((qs.prod : ℤ) * (tw qs.length : ℤ)) ≤
          (ceilDiv (2 * qs.prod * tw qs.length) floatDen : ℤ) * floatDen := by
        have := MulPOverQ.le_ceilDiv_mul (2 * qs.prod * tw qs.length) floatDen
          FloatScalar.floatDen_pos
        have h' : (2 : ℤ) * qs.prod * tw qs.length ≤
            (ceilDiv (2 * qs.prod * tw qs.length) floatDen : ℤ) * floatDen := by
          exact_mod_cast this
        linarith
      have h1 := hsz a i
      have h2 : (floatDen : ℤ) * (2 * |(lift S qs a).coeff i|) ≤
          (floatDen : ℤ) * ((qs.prod : ℤ) +
            (ceilDiv (2 * qs.prod * tw qs.length) floatDen : ℤ)) := by
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
    abs_coeff_mul_le (N := N) (qs.prod : ℤ) (floatDen : ℤ) (tw qs.length : ℤ) hF
      (lift S qs a) (lift S qs b) (hsz a) (hsz b)
  have hMnn : (0 : ℤ) ≤ (N : ℤ) *
      ((qs.prod : ℤ) * ((floatDen : ℤ) + 2 * (tw qs.length : ℤ))) ^ 2 := by positivity
  have hcomp := componentT tw tr S hS t qs ps hpos hcop hfq hfp hok
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
  · rw [hpsMul_eqT]
    simp only [List.map_cons, List.map_nil, expand_toLimbs S qs ps hposq hcopq, tensor_toLimbs,
      source_tensor_two, ho0, ho1, ho2]

end hps

section poverq
open FHE.BFV
open Spec NPoly Scheme Challenge.BFVMul Challenge.BFVMul.HPS Challenge.BFVMul.POverQ
open Validation.Ring Validation.Scheme Validation.Source
open FHE.RNS FHE.BFV.MulHPS FHE.BFV.MulPOverQ Spec.BudgetBFV FHE.BFV.FloatPOverQ

/-- `Fl.scaleRoundOut`, by `rfl`. -/
theorem scaleRoundOut_eqT {N : ℕ} (S : Fl.Sums) (t : ℕ) (ins outs : List ℕ)
    (xin xout : List (IntPoly N)) :
    Fl.scaleRoundOut S t ins outs xin xout = List.zipWith
      (fun o xo =>
        (⟨fun i => Fl.scale1 S t ins outs (HPS.residues xin i) o (xo.coeff i)⟩ : IntPoly N))
      outs xout := rfl

/-- `Fl.poverqMul`, by `rfl`. -/
theorem poverqMul_eqT {N : ℕ} (S : Fl.Sums) (t : ℕ) (qs ps : List ℕ) (c d : List (IntPoly N)) :
    Fl.poverqMul S t qs ps c d =
      (HPS.tensor (qs ++ ps) (c.map fun x => Fl.expand S qs ps (HPS.toLimbs qs x))
        (d.map fun x => Fl.fastExpand S qs ps qs (HPS.toLimbs qs x))).map fun x =>
        HPS.reconstruct qs (Fl.scaleRoundOut S t ps qs (x.drop qs.length) (x.take qs.length)) :=
  rfl

/-- `2·F·P·|B| ≤ Q·P·(F + 2w) + 2·F·k·Q`, for every `w` at least the tolerance of the switch
from `ps`. -/
theorem bValF_boundT (tw : ℕ → ℕ) (tr : List ℕ → ℕ) (S : Fl.Sums) (hS : SumsOK' tw tr S) (qs ps : List ℕ)
    (hpos : ∀ m ∈ qs ++ ps, 0 < m) (hcop : (qs ++ ps).Pairwise Nat.Coprime)
    (hfb : floatBasisOK ps = true) (w : ℕ) (hw : tw ps.length ≤ w) (x : ℤ) :
    2 * (floatDen : ℤ) * ((ps.prod : ℤ) * |bValF S qs ps x|) ≤
      (qs.prod : ℤ) * ((ps.prod : ℤ) * ((floatDen : ℤ) + 2 * w)) +
        2 * floatDen * (qs.length * (qs.prod : ℤ)) := by
  have hposq : ∀ q ∈ qs, 0 < q := fun q hq => hpos q (List.mem_append_left _ hq)
  have hposp : ∀ p ∈ ps, 0 < p := fun p hp => hpos p (List.mem_append_right _ hp)
  have hcopp : ps.Pairwise Nat.Coprime := (List.pairwise_append.mp hcop).2.1
  have hP : (0 : ℤ) < ps.prod := by exact_mod_cast prod_pos' ps hposp
  have hw' : (tw ps.length : ℤ) ≤ w := by exact_mod_cast hw
  have h1 := bValF_spec S qs ps hpos hcop x
  obtain ⟨h2, h3⟩ := sVal_bounds qs hposq ps.prod x
  have hb : 2 * (floatDen : ℤ) * |wValF S qs ps x| ≤
      (ps.prod : ℤ) * ((floatDen : ℤ) + 2 * (tw ps.length : ℤ)) :=
    switchVal_boundT tw tr S hS ps hposp hcopp hfb _
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

variable {N : ℕ}

/-- **Tolerant scale and round**, any input and output bases: the limbs modulo `outs` of an
integer polynomial `X` with `2·F·|I·X − t·T| ≤ I·(F + 2·tr ins)` coefficientwise. -/
theorem scaleRoundOut_toLimbsT (tw : ℕ → ℕ) (tr : List ℕ → ℕ) (S : Fl.Sums) (hS : SumsOK' tw tr S) (t : ℕ) (ins outs : List ℕ)
    (hpos : ∀ m ∈ ins ++ outs, 0 < m) (hcop : (ins ++ outs).Pairwise Nat.Coprime)
    (hfb : floatBasisOK ins = true) (T : IntPoly N) :
    ∃ X : IntPoly N,
      Fl.scaleRoundOut S t ins outs (toLimbs ins T) (toLimbs outs T) = toLimbs outs X ∧
      ∀ i, 2 * (floatDen : ℤ) * |(ins.prod : ℤ) * X.coeff i - t * T.coeff i| ≤
        (ins.prod : ℤ) * ((floatDen : ℤ) + 2 * (tr ins : ℤ)) := by
  choose R hR1 hR2 using fun i : Fin N =>
    scale1_tolT tw tr S hS t ins outs hpos hcop hfb (T.coeff i)
  refine ⟨⟨R⟩, ?_, hR2⟩
  rw [scaleRoundOut_eqT]
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
theorem abs_coeff_liftAF_mul_liftST (tw : ℕ → ℕ) (tr : List ℕ → ℕ) (S : Fl.Sums) (hS : SumsOK' tw tr S) (ql qs ps : List ℕ)
    (hposl : ∀ q ∈ ql, 0 < q) (hcopl : ql.Pairwise Nat.Coprime) (hfb : floatBasisOK ql = true)
    (hposq : ∀ q ∈ qs, 0 < q) (w : ℕ) (hw : tw ql.length ≤ w) (a b : IntPoly N)
    (i : Fin N) :
    2 * (floatDen : ℤ) * |(liftAF S ql a * liftS qs ps b).coeff i| ≤
      (N : ℤ) * ((ql.prod : ℤ) * ((floatDen : ℤ) + 2 * w)) * (qs.length * (qs.prod : ℤ)) := by
  have hF : (0 : ℤ) < 2 * (floatDen : ℤ) := by
    have : (0 : ℤ) < floatDen := by exact_mod_cast floatDen_pos
    linarith
  have hw' : (tw ql.length : ℤ) ≤ w := by exact_mod_cast hw
  have h := abs_coeff_mul_scaled (liftAF S ql a) (liftS qs ps b) (2 * (floatDen : ℤ)) 1
    ((ql.prod : ℤ) * ((floatDen : ℤ) + 2 * w)) (qs.length * (qs.prod : ℤ)) hF one_pos
    (fun j => by
      have h1 : 2 * (floatDen : ℤ) * |FloatScalar.switchVal S ql (a.coeff j)| ≤ _ :=
        switchVal_boundT tw tr S hS ql hposl hcopl hfb (a.coeff j)
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

/-- **The P-over-Q multiplication with sums within the tolerances multiplies representatives of
bounded size and rounds within a bounded distance**: the hypotheses of
`Challenge.BFVMul.stepOK_mul_lifted` at `Q = qs.prod`, with the slack
`Spec.BudgetBFV.poverqSlack t N Q P k (tw k) (tr ps)`, `k = qs.length`, for an
auxiliary basis of at most `k` moduli. -/
theorem poverqMul_liftedT (tw : ℕ → ℕ) (tr : List ℕ → ℕ) (S : Fl.Sums) (hS : SumsOK' tw tr S) (t : ℕ) (qs ps : List ℕ)
    (haux : floatAuxOK? qs ps = true) (hlen : ps.length ≤ qs.length)
    (hw : ∀ m ≤ qs.length, tw m ≤ tw qs.length)
    (c d : List (IntPoly N)) (hc : c.length = 2) (hd : d.length = 2) :
    ∃ A B X : List (IntPoly N), X.length = 3 ∧
      A.map (ofInt qs.prod) = c.map (ofInt qs.prod) ∧
      B.map (ofInt qs.prod) = d.map (ofInt qs.prod) ∧
      (∀ p ∈ A, 2 * normInf p ≤ qs.prod +
        (poverqSlack t N qs.prod ps.prod qs.length (tw qs.length) (tr ps)).e) ∧
      (∀ p ∈ B, 2 * normInf p ≤ qs.prod +
        (poverqSlack t N qs.prod ps.prod qs.length (tw qs.length) (tr ps)).e) ∧
      (∀ (j : ℕ) (i : Fin N),
        2 * |(qs.prod : ℤ) * (X.getD j 0).coeff i -
            (t : ℤ) * ((Challenge.Source.tensor A B).getD j 0).coeff i|
          ≤ (qs.prod : ℤ) *
            (poverqSlack t N qs.prod ps.prod qs.length (tw qs.length) (tr ps)).rho) ∧
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
  have hww := hw _ hlen
  obtain ⟨a₀, a₁, rfl⟩ := List.length_eq_two.mp hc
  obtain ⟨b₀, b₁, rfl⟩ := List.length_eq_two.mp hd
  have he := slack_e_tol t N qs.prod ps.prod qs.length (tw qs.length) (tr ps) hP
  obtain ⟨cc, hrho, hcc⟩ :=
    slack_rho_tol t N qs.prod ps.prod qs.length (tw qs.length) (tr ps) hP
  rw [hrho]
  generalize (poverqSlack t N qs.prod ps.prod qs.length (tw qs.length) (tr ps)).e = e
    at he ⊢
  -- sizes of the representatives
  have hAn : ∀ a : IntPoly N, 2 * normInf (liftAF S qs a) ≤ qs.prod + e := fun a =>
    two_normInf_le _ _ fun i => by
      have h1 : 2 * (floatDen : ℤ) * |FloatScalar.switchVal S qs (a.coeff i)| ≤ _ :=
        switchVal_boundT tw tr S hS qs hposq hcopq hfq (a.coeff i)
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
        (bValF_boundT tw tr S hS qs ps hpos hcop hfp _ hww (b.coeff i))
  -- the rounding of one product, coefficient by coefficient
  have hW : ∀ (b : IntPoly N) (i : Fin N), (qs.prod : ℤ) * (liftWF S qs ps b).coeff i =
      (ps.prod : ℤ) * (liftBF S qs ps b).coeff i + (liftS qs ps b).coeff i := fun b i =>
    bValF_spec S qs ps hpos hcop (b.coeff i)
  have hE1 := abs_coeff_liftAF_mul_liftST (N := N) tw tr S hS qs qs ps hposq hcopq hfq hposq
    (tw qs.length) le_rfl
  -- what the algorithm computes
  have hstep : ∀ T : IntPoly N, ∃ X : IntPoly N,
      reconstruct qs (Fl.scaleRoundOut S t ps qs ((toLimbs (qs ++ ps) T).drop qs.length)
        ((toLimbs (qs ++ ps) T).take qs.length)) = modPoly qs.prod X ∧
      ∀ i, 2 * (floatDen : ℤ) * |(ps.prod : ℤ) * X.coeff i - t * T.coeff i| ≤
        (ps.prod : ℤ) * ((floatDen : ℤ) + 2 * (tr ps : ℤ)) := fun T => by
    obtain ⟨X, hX, hXb⟩ :=
      scaleRoundOut_toLimbsT tw tr S hS t ps qs hpos' (pairwise_swap qs ps hcop) hfp T
    refine ⟨X, ?_, hXb⟩
    have e : toLimbs (qs ++ ps) T = toLimbs qs T ++ toLimbs ps T := List.map_append
    have hl : (toLimbs qs T).length = qs.length := List.length_map _
    rw [e, List.take_left' hl, List.drop_left' hl, hX, reconstruct_toLimbs qs hposq hcopq]
  have hmul : Fl.poverqMul S t qs ps [a₀, a₁] [b₀, b₁] =
      (Challenge.Source.tensor [liftAF S qs a₀, liftAF S qs a₁]
        [liftWF S qs ps b₀, liftWF S qs ps b₁]).map fun T =>
        reconstruct qs (Fl.scaleRoundOut S t ps qs ((toLimbs (qs ++ ps) T).drop qs.length)
          ((toLimbs (qs ++ ps) T).take qs.length)) := by
    rw [poverqMul_eqT]
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
      refine round_final_tol _ _ _ _ N qs.length cc (tw qs.length) (tr ps) _ _ _ _
        hF hP (coeff_mul_combo _ _ _ _ _ _ (hW b₀) i) (hb₀ i) ?_ hcc
      have := hE1 a₀ b₀ i
      have := mul_nonneg hFz.le (abs_nonneg ((liftAF S qs a₀ * liftS qs ps b₀).coeff i))
      linarith
    · show 2 * |(qs.prod : ℤ) * X₁.coeff i -
        (t : ℤ) * (liftAF S qs a₀ * liftBF S qs ps b₁ +
          liftAF S qs a₁ * liftBF S qs ps b₀).coeff i| ≤ _
      refine round_final_tol _ _ _ _ N qs.length cc (tw qs.length) (tr ps) _ _ _
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
      refine round_final_tol _ _ _ _ N qs.length cc (tw qs.length) (tr ps) _ _ _ _
        hF hP (coeff_mul_combo _ _ _ _ _ _ (hW b₁) i) (hb₂ i) ?_ hcc
      have := hE1 a₁ b₁ i
      have := mul_nonneg hFz.le (abs_nonneg ((liftAF S qs a₁ * liftS qs ps b₁).coeff i))
      linarith
    · show 2 * |(qs.prod : ℤ) * (0 : IntPoly N).coeff i - (t : ℤ) * (0 : IntPoly N).coeff i| ≤ _
      simp only [coeff_zero', mul_zero, sub_zero, abs_zero]
      positivity
  · rw [hmul]
    simp only [List.map_cons, List.map_nil, hX₀, hX₁, hX₂, ofInt_modPoly]

end poverq

section leveled
open FHE.BFV
open Spec NPoly Scheme Challenge.BFVMul Challenge.BFVMul.HPS Challenge.BFVMul.POverQ
open Validation.Ring Validation.Scheme Validation.Source
open FHE.RNS FHE.BFV.MulHPS FHE.BFV.MulPOverQ FHE.BFV.FloatPOverQ Spec.BudgetBFV FHE.BFV.FloatLeveled
variable {N : ℕ}

/-- **Operand 1 of the leveled multiplication**: the tolerant scaling down from `Q` to `Q_l`
followed by the tolerant extension to `P_l` gives the limbs of a polynomial `A'` with
`2·F·|A'| ≤ Q_l·(F + 2w)`; with `Rho` the error of the scaling down
(`2·F·|Rho| ≤ D·(F + 2·tr (qs.drop l))`), `Af = D·A' − Rho ≡ a (mod Q)`. -/
theorem scaleDown_expandT (tw : ℕ → ℕ) (tr : List ℕ → ℕ) (S : Fl.Sums) (hS : SumsOK' tw tr S) (qs pl : List ℕ) (l : ℕ)
    (hposq : ∀ q ∈ qs, 0 < q) (hcopq : qs.Pairwise Nat.Coprime) (hfq : floatBasisOK qs = true)
    (w : ℕ) (hw : tw (qs.take l).length ≤ w) (a : IntPoly N) :
    ∃ A' Rho Af : IntPoly N,
      Fl.expand S (qs.take l) pl (Fl.scaleRoundOut S 1 (qs.drop l) (qs.take l)
        ((toLimbs qs a).drop l) ((toLimbs qs a).take l)) = toLimbs (qs.take l ++ pl) A' ∧
      (∀ i, 2 * (floatDen : ℤ) * |A'.coeff i| ≤
        ((qs.take l).prod : ℤ) * ((floatDen : ℤ) + 2 * w)) ∧
      (∀ i, 2 * (floatDen : ℤ) * |Rho.coeff i| ≤
        ((qs.drop l).prod : ℤ) * ((floatDen : ℤ) + 2 * (tr (qs.drop l) : ℤ))) ∧
      (∀ i, Af.coeff i = ((qs.drop l).prod : ℤ) * A'.coeff i - Rho.coeff i) ∧
      (∀ i, (qs.prod : ℤ) ∣ Af.coeff i - a.coeff i) := by
  have hposl : ∀ q ∈ qs.take l, 0 < q := fun q hq => hposq q (List.mem_of_mem_take hq)
  have hcopl : (qs.take l).Pairwise Nat.Coprime := hcopq.sublist (List.take_sublist _ _)
  have hfl : floatBasisOK (qs.take l) = true := floatBasisOK_sublist (List.take_sublist _ _) hfq
  have hfd : floatBasisOK (qs.drop l) = true := floatBasisOK_sublist (List.drop_sublist _ _) hfq
  have hposdl : ∀ m ∈ qs.drop l ++ qs.take l, 0 < m := fun m hm => hposq m (by
    rcases List.mem_append.mp hm with h | h
    · exact List.mem_of_mem_drop h
    · exact List.mem_of_mem_take h)
  have hcopdl : (qs.drop l ++ qs.take l).Pairwise Nat.Coprime :=
    pairwise_swap _ _ (by rw [List.take_append_drop]; exact hcopq)
  have hQDz : ((qs.take l).prod : ℤ) * (qs.drop l).prod = qs.prod := by
    exact_mod_cast prod_take_mul_drop qs l
  have hw' : (tw (qs.take l).length : ℤ) ≤ w := by exact_mod_cast hw
  obtain ⟨X, hX, hXb⟩ :=
    scaleRoundOut_toLimbsT tw tr S hS 1 (qs.drop l) (qs.take l) hposdl hcopdl hfd a
  refine ⟨liftAF S (qs.take l) X,
    ⟨fun i => ((qs.drop l).prod : ℤ) * X.coeff i - a.coeff i⟩,
    ⟨fun i => ((qs.drop l).prod : ℤ) * (liftAF S (qs.take l) X).coeff i -
      (((qs.drop l).prod : ℤ) * X.coeff i - a.coeff i)⟩, ?_, ?_, ?_, fun _ => rfl, ?_⟩
  · have e1 : (toLimbs qs a).drop l = toLimbs (qs.drop l) a := List.map_drop.symm
    have e2 : (toLimbs qs a).take l = toLimbs (qs.take l) a := List.map_take.symm
    rw [e1, e2, hX, expand_toLimbs_fl S _ _ hposl hcopl]
  · intro i
    have h1 : 2 * (floatDen : ℤ) * |FloatScalar.switchVal S (qs.take l) (X.coeff i)| ≤ _ :=
      switchVal_boundT tw tr S hS (qs.take l) hposl hcopl hfl (X.coeff i)
    have h2 := mul_le_mul_of_nonneg_left hw'
      (by positivity : (0 : ℤ) ≤ 2 * ((qs.take l).prod : ℤ))
    show 2 * (floatDen : ℤ) * |FloatScalar.switchVal S (qs.take l) (X.coeff i)| ≤ _
    linarith
  · intro i
    have h := hXb i
    simp only [Nat.cast_one, one_mul] at h
    exact h
  · intro i
    obtain ⟨u, hu⟩ := FloatScalar.switchVal_dvd S (qs.take l) hposl hcopl (X.coeff i)
    refine ⟨u, ?_⟩
    show ((qs.drop l).prod : ℤ) * FloatScalar.switchVal S (qs.take l) (X.coeff i) -
        (((qs.drop l).prod : ℤ) * X.coeff i - a.coeff i) - a.coeff i = _
    rw [← hQDz]
    linear_combination ((qs.drop l).prod : ℤ) * hu

/-- The scaling-down term of one product:
`(2·F)·(2·F·P_l)·|(Rho·B)ᵢ| ≤ N·β·(Q·P_l·(F + 2w) + 2·F·k·Q)` for `2·F·|Rho| ≤ β`. -/
theorem abs_coeff_mul_liftBFT (tw : ℕ → ℕ) (tr : List ℕ → ℕ) (S : Fl.Sums) (hS : SumsOK' tw tr S) (Rho : IntPoly N) (β : ℤ)
    (hR : ∀ j, 2 * (floatDen : ℤ) * |Rho.coeff j| ≤ β) (qs pl : List ℕ)
    (hpos : ∀ m ∈ qs ++ pl, 0 < m) (hcop : (qs ++ pl).Pairwise Nat.Coprime)
    (hfb : floatBasisOK pl = true) (w : ℕ) (hw : tw pl.length ≤ w) (b : IntPoly N)
    (i : Fin N) :
    2 * (floatDen : ℤ) * (2 * (floatDen : ℤ) * pl.prod) * |(Rho * liftBF S qs pl b).coeff i| ≤
      (N : ℤ) * β * ((qs.prod : ℤ) * ((pl.prod : ℤ) * ((floatDen : ℤ) + 2 * w)) +
        2 * floatDen * (qs.length * (qs.prod : ℤ))) := by
  have hFz : (0 : ℤ) < floatDen := by exact_mod_cast floatDen_pos
  have hF : (0 : ℤ) < 2 * (floatDen : ℤ) := by linarith
  have hP : (0 : ℤ) < pl.prod := by
    exact_mod_cast prod_pos' pl fun p hp => hpos p (List.mem_append_right _ hp)
  exact abs_coeff_mul_scaled Rho (liftBF S qs pl b) (2 * (floatDen : ℤ))
    (2 * (floatDen : ℤ) * pl.prod) β _ hF (mul_pos hF hP) hR
    (fun j => by
      have := bValF_boundT tw tr S hS qs pl hpos hcop hfb w hw (b.coeff j)
      show 2 * (floatDen : ℤ) * pl.prod * |bValF S qs pl (b.coeff j)| ≤ _
      linarith) i

/-- **The leveled P-over-Q multiplication with sums within the tolerances multiplies
representatives of bounded size and rounds within a bounded distance**: the hypotheses of
`Challenge.BFVMul.stepOK_mul_lifted` at `Q = qs.prod`, with the slack
`Spec.BudgetBFV.leveledSlack t N Q Q_l P_l k (tw k) (tr (qs.drop l)) (tr P_l)`,
`k = qs.length`, `l = k − drop`, `Q_l`, `P_l` the first `l` limbs of `qs`, `ps`. -/
theorem leveledMul_liftedT (tw : ℕ → ℕ) (tr : List ℕ → ℕ) (S : Fl.Sums) (hS : SumsOK' tw tr S) (t : ℕ) (qs ps : List ℕ) (drop : ℕ)
    (haux : floatAuxOK? qs (ps.take (qs.length - drop)) = true)
    (hw : ∀ m ≤ qs.length, tw m ≤ tw qs.length)
    (c d : List (IntPoly N)) (hc : c.length = 2) (hd : d.length = 2) :
    ∃ A B X : List (IntPoly N), X.length = 3 ∧
      A.map (ofInt qs.prod) = c.map (ofInt qs.prod) ∧
      B.map (ofInt qs.prod) = d.map (ofInt qs.prod) ∧
      (∀ p ∈ A, 2 * normInf p ≤ qs.prod +
        (leveledSlack t N qs.prod (qs.take (qs.length - drop)).prod
          (ps.take (qs.length - drop)).prod qs.length (tw qs.length)
          (tr (qs.drop (qs.length - drop)))
          (tr (ps.take (qs.length - drop)))).e) ∧
      (∀ p ∈ B, 2 * normInf p ≤ qs.prod +
        (leveledSlack t N qs.prod (qs.take (qs.length - drop)).prod
          (ps.take (qs.length - drop)).prod qs.length (tw qs.length)
          (tr (qs.drop (qs.length - drop)))
          (tr (ps.take (qs.length - drop)))).e) ∧
      (∀ (j : ℕ) (i : Fin N),
        2 * |(qs.prod : ℤ) * (X.getD j 0).coeff i -
            (t : ℤ) * ((Challenge.Source.tensor A B).getD j 0).coeff i|
          ≤ (qs.prod : ℤ) *
            (leveledSlack t N qs.prod (qs.take (qs.length - drop)).prod
              (ps.take (qs.length - drop)).prod qs.length (tw qs.length)
              (tr (qs.drop (qs.length - drop)))
              (tr (ps.take (qs.length - drop)))).rho) ∧
      (Fl.leveledMul S t qs ps drop c d).map (ofInt qs.prod) = X.map (ofInt qs.prod) := by
  obtain ⟨a₀, a₁, rfl⟩ := List.length_eq_two.mp hc
  obtain ⟨b₀, b₁, rfl⟩ := List.length_eq_two.mp hd
  have hdef : Fl.leveledMul S t qs ps drop [a₀, a₁] [b₀, b₁] =
      (HPS.tensor (qs.take (qs.length - drop) ++ ps.take (qs.length - drop))
        [Fl.expand S (qs.take (qs.length - drop)) (ps.take (qs.length - drop))
            (Fl.scaleRoundOut S 1 (qs.drop (qs.length - drop)) (qs.take (qs.length - drop))
              ((toLimbs qs a₀).drop (qs.length - drop)) ((toLimbs qs a₀).take (qs.length - drop))),
          Fl.expand S (qs.take (qs.length - drop)) (ps.take (qs.length - drop))
            (Fl.scaleRoundOut S 1 (qs.drop (qs.length - drop)) (qs.take (qs.length - drop))
              ((toLimbs qs a₁).drop (qs.length - drop)) ((toLimbs qs a₁).take (qs.length - drop)))]
        [Fl.fastExpand S qs (ps.take (qs.length - drop)) (qs.take (qs.length - drop))
            (toLimbs qs b₀),
          Fl.fastExpand S qs (ps.take (qs.length - drop)) (qs.take (qs.length - drop))
            (toLimbs qs b₁)]).map fun x =>
        reconstruct qs (expandQlHat qs (qs.take (qs.length - drop))
          (Fl.scaleRoundOut S t (ps.take (qs.length - drop)) (qs.take (qs.length - drop))
            (x.drop (qs.take (qs.length - drop)).length)
            (x.take (qs.take (qs.length - drop)).length))) := rfl
  rw [hdef]
  clear hdef
  obtain ⟨hfq, hfp, hpos, hcop⟩ := floatAuxOK_imp haux
  have hpll : (ps.take (qs.length - drop)).length ≤ qs.length :=
    (List.length_take_le _ _).trans (Nat.sub_le _ _)
  clear haux
  generalize qs.length - drop = l at hfp hpos hcop hpll ⊢
  generalize ps.take l = pl at hfp hpos hcop hpll ⊢
  have hposq : ∀ q ∈ qs, 0 < q := fun q hq => hpos q (List.mem_append_left _ hq)
  have hposp : ∀ p ∈ pl, 0 < p := fun p hp => hpos p (List.mem_append_right _ hp)
  have hcopq : qs.Pairwise Nat.Coprime := (List.pairwise_append.mp hcop).1
  have hposl : ∀ q ∈ qs.take l, 0 < q := fun q hq => hposq q (List.mem_of_mem_take hq)
  have hcopl : (qs.take l).Pairwise Nat.Coprime := hcopq.sublist (List.take_sublist _ _)
  have hcoplp : (qs.take l ++ pl).Pairwise Nat.Coprime := pairwise_append_take l hcop
  have hpospl : ∀ m ∈ pl ++ qs.take l, 0 < m := fun m hm => hpos m (by
    rcases List.mem_append.mp hm with h | h
    · exact List.mem_append_right _ h
    · exact List.mem_append_left _ (List.mem_of_mem_take h))
  have hP : 0 < pl.prod := prod_pos' pl hposp
  have hQl : 0 < (qs.take l).prod := prod_pos' _ hposl
  have hQD := prod_take_mul_drop qs l
  have hD : qs.prod / (qs.take l).prod = (qs.drop l).prod := by
    rw [← hQD, Nat.mul_div_cancel_left _ hQl]
  have hQDz : ((qs.take l).prod : ℤ) * (qs.drop l).prod = qs.prod := by exact_mod_cast hQD
  have hF := floatDen_pos
  have hFz : (0 : ℤ) < floatDen := by exact_mod_cast hF
  have hwl : tw (qs.take l).length ≤ tw qs.length :=
    hw _ (List.length_take_le' _ _)
  have hwp : tw pl.length ≤ tw qs.length := hw _ hpll
  obtain ⟨he1, he2⟩ := leveledSlack_e_tol t N qs.prod (qs.take l).prod pl.prod qs.length
    (tw qs.length) (tr (qs.drop l)) (tr pl) hP
  have hrho := leveledSlack_rho_tol t N qs.prod (qs.take l).prod pl.prod qs.length
    (tw qs.length) (tr (qs.drop l)) (tr pl) hP
  rw [hD] at he1 hrho
  generalize (leveledSlack t N qs.prod (qs.take l).prod pl.prod qs.length
    (tw qs.length) (tr (qs.drop l)) (tr pl)).e = e at he1 he2 ⊢
  generalize (leveledSlack t N qs.prod (qs.take l).prod pl.prod qs.length
    (tw qs.length) (tr (qs.drop l)) (tr pl)).rho = rho at hrho ⊢
  -- operand 1
  obtain ⟨A₀, R₀, F₀, hA₀, hA₀b, hR₀b, hF₀, hF₀d⟩ :=
    scaleDown_expandT tw tr S hS qs pl l hposq hcopq hfq _ hwl a₀
  obtain ⟨A₁, R₁, F₁, hA₁, hA₁b, hR₁b, hF₁, hF₁d⟩ :=
    scaleDown_expandT tw tr S hS qs pl l hposq hcopq hfq _ hwl a₁
  have hAn : ∀ A' R Af : IntPoly N,
      (∀ i, 2 * (floatDen : ℤ) * |A'.coeff i| ≤
        ((qs.take l).prod : ℤ) * ((floatDen : ℤ) + 2 * (tw qs.length : ℕ))) →
      (∀ i, 2 * (floatDen : ℤ) * |R.coeff i| ≤
        ((qs.drop l).prod : ℤ) * ((floatDen : ℤ) + 2 * (tr (qs.drop l) : ℤ))) →
      (∀ i, Af.coeff i = ((qs.drop l).prod : ℤ) * A'.coeff i - R.coeff i) →
      2 * normInf Af ≤ qs.prod + e := fun A' R Af h1 h2 h3 =>
    two_normInf_le _ _ fun i => by
      have he1' : ((qs.drop l).prod : ℤ) * ((floatDen : ℤ) + 2 * (tr (qs.drop l) : ℤ)) +
          2 * qs.prod * (tw qs.length : ℕ) ≤ e * floatDen := by exact_mod_cast he1
      have h4 := abs_sub (((qs.drop l).prod : ℤ) * A'.coeff i) (R.coeff i)
      rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg (α := ℤ) (qs.drop l).prod)] at h4
      have h5 := mul_le_mul_of_nonneg_left (h1 i) (Nat.cast_nonneg (α := ℤ) (qs.drop l).prod)
      have h6 : ((qs.drop l).prod : ℤ) *
          (((qs.take l).prod : ℤ) * ((floatDen : ℤ) + 2 * (tw qs.length : ℕ))) =
          qs.prod * ((floatDen : ℤ) + 2 * (tw qs.length : ℕ)) := by
        rw [← hQDz]; ring
      have h7 := mul_le_mul_of_nonneg_left h4 (by positivity : (0 : ℤ) ≤ 2 * (floatDen : ℤ))
      have h8 := h2 i
      rw [h3 i, Nat.cast_add]
      have h9 : (floatDen : ℤ) * (2 * |((qs.drop l).prod : ℤ) * A'.coeff i - R.coeff i|) ≤
          (floatDen : ℤ) * ((qs.prod : ℤ) + e) := by linarith
      exact le_of_mul_le_mul_left h9 hFz
  have hBn : ∀ b : IntPoly N, 2 * normInf (liftBF S qs pl b) ≤ qs.prod + e := fun b =>
    two_normInf_le _ _ fun i => by
      show 2 * |bValF S qs pl (b.coeff i)| ≤ ((qs.prod + e : ℕ) : ℤ)
      rw [Nat.cast_add]
      exact lift_le _ _ _ _ _ _ hF hP he2 _
        (bValF_boundT tw tr S hS qs pl hpos hcop hfp _ hwp (b.coeff i))
  -- the error terms of one product
  have hW : ∀ (b : IntPoly N) (i : Fin N), (qs.prod : ℤ) * (liftWF S qs pl b).coeff i =
      (pl.prod : ℤ) * (liftBF S qs pl b).coeff i + (liftS qs pl b).coeff i := fun b i =>
    bValF_spec S qs pl hpos hcop (b.coeff i)
  have hE1 : ∀ (A' : IntPoly N), (∀ i, 2 * (floatDen : ℤ) * |A'.coeff i| ≤
        ((qs.take l).prod : ℤ) * ((floatDen : ℤ) + 2 * (tw qs.length : ℕ))) →
      ∀ (b : IntPoly N) (i : Fin N),
      2 * (floatDen : ℤ) * |(A' * liftS qs pl b).coeff i| ≤
        (N : ℤ) * (((qs.take l).prod : ℤ) * ((floatDen : ℤ) + 2 * (tw qs.length : ℕ))) *
          (qs.length * (qs.prod : ℤ)) := fun A' h b i =>
    abs_coeff_mul_liftS A' _ h qs pl hposq b i
  have hE2 : ∀ (R : IntPoly N), (∀ i, 2 * (floatDen : ℤ) * |R.coeff i| ≤
        ((qs.drop l).prod : ℤ) * ((floatDen : ℤ) + 2 * (tr (qs.drop l) : ℤ))) →
      ∀ (b : IntPoly N) (i : Fin N),
      2 * (2 * (floatDen : ℤ) * floatDen * pl.prod * |(R * liftBF S qs pl b).coeff i|) ≤
        (N : ℤ) * (((qs.drop l).prod : ℤ) * ((floatDen : ℤ) + 2 * (tr (qs.drop l) : ℕ))) *
          ((qs.prod : ℤ) * ((pl.prod : ℤ) * ((floatDen : ℤ) + 2 * (tw qs.length : ℕ))) +
            2 * floatDen * (qs.length * (qs.prod : ℤ))) := fun R h b i => by
    have := abs_coeff_mul_liftBFT tw tr S hS R _ h qs pl hpos hcop hfp _ hwp b i
    linarith
  -- what the algorithm computes
  have hstep : ∀ T : IntPoly N, ∃ Y : IntPoly N,
      reconstruct qs (expandQlHat qs (qs.take l) (Fl.scaleRoundOut S t pl (qs.take l)
        ((toLimbs (qs.take l ++ pl) T).drop (qs.take l).length)
        ((toLimbs (qs.take l ++ pl) T).take (qs.take l).length))) =
        modPoly qs.prod (⟨fun i => ((qs.drop l).prod : ℤ) * Y.coeff i⟩ : IntPoly N) ∧
      ∀ i, 2 * (floatDen : ℤ) * |(pl.prod : ℤ) * Y.coeff i - t * T.coeff i| ≤
        (pl.prod : ℤ) * ((floatDen : ℤ) + 2 * (tr pl : ℤ)) := fun T => by
    obtain ⟨Y, hY, hYb⟩ :=
      scaleRoundOut_toLimbsT tw tr S hS t pl (qs.take l) hpospl (pairwise_swap _ _ hcoplp) hfp T
    refine ⟨Y, ?_, hYb⟩
    have e : toLimbs (qs.take l ++ pl) T = toLimbs (qs.take l) T ++ toLimbs pl T :=
      List.map_append
    have hl : (toLimbs (qs.take l) T).length = (qs.take l).length := List.length_map _
    rw [e, List.take_left' hl, List.drop_left' hl, hY, expandQlHat_toLimbs qs l hposq,
      reconstruct_toLimbs qs hposq hcopq]
  simp only [hA₀, hA₁, fastExpand_toLimbs_fl S qs pl (qs.take l) hpos hcop, tensor_toLimbs,
    List.map_map]
  rw [source_tensor_two]
  obtain ⟨Y₀, hY₀, hb₀⟩ := hstep (A₀ * liftWF S qs pl b₀)
  obtain ⟨Y₁, hY₁, hb₁⟩ := hstep (A₀ * liftWF S qs pl b₁ + A₁ * liftWF S qs pl b₀)
  obtain ⟨Y₂, hY₂, hb₂⟩ := hstep (A₁ * liftWF S qs pl b₁)
  refine ⟨[F₀, F₁], [liftBF S qs pl b₀, liftBF S qs pl b₁],
    [⟨fun i => ((qs.drop l).prod : ℤ) * Y₀.coeff i⟩,
      ⟨fun i => ((qs.drop l).prod : ℤ) * Y₁.coeff i⟩,
      ⟨fun i => ((qs.drop l).prod : ℤ) * Y₂.coeff i⟩], rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [List.map_cons, List.map_nil]
    rw [ofInt_eq_of_dvd _ F₀ a₀ hF₀d, ofInt_eq_of_dvd _ F₁ a₁ hF₁d]
  · simp only [List.map_cons, List.map_nil]
    rw [ofInt_eq_of_dvd _ (liftBF S qs pl b₀) b₀ fun i => bValF_dvd S qs pl hpos hcop _,
      ofInt_eq_of_dvd _ (liftBF S qs pl b₁) b₁ fun i => bValF_dvd S qs pl hpos hcop _]
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · exact hAn A₀ R₀ _ hA₀b hR₀b hF₀
    · exact hAn A₁ R₁ _ hA₁b hR₁b hF₁
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl <;> exact hBn _
  · intro j i
    rcases j with _ | _ | _ | j
    · show 2 * |(qs.prod : ℤ) * (((qs.drop l).prod : ℤ) * Y₀.coeff i) -
        (t : ℤ) * (F₀ * liftBF S qs pl b₀).coeff i| ≤ _
      refine leveled_final_tol _ _ (qs.take l).prod _ _ _ N qs.length rho (tw qs.length)
        (tr (qs.drop l)) (tr pl) _ _ _ _ _ _ hF hP (hb₀ i)
        (coeff_mul_combo _ _ _ _ _ _ (hW b₀) i)
        (coeff_mul_combo_left _ _ _ _ _ hF₀ i) ?_ ?_ hrho
      · have := hE1 A₀ hA₀b b₀ i
        have := mul_nonneg hFz.le (abs_nonneg ((A₀ * liftS qs pl b₀).coeff i))
        linarith
      · have := hE2 R₀ hR₀b b₀ i
        have : (0 : ℤ) ≤ 2 * (floatDen : ℤ) * floatDen * pl.prod *
            |(R₀ * liftBF S qs pl b₀).coeff i| := by positivity
        push_cast at *
        linarith
    · show 2 * |(qs.prod : ℤ) * (((qs.drop l).prod : ℤ) * Y₁.coeff i) -
        (t : ℤ) * (F₀ * liftBF S qs pl b₁ + F₁ * liftBF S qs pl b₀).coeff i| ≤ _
      refine leveled_final_tol _ _ (qs.take l).prod _ _ _ N qs.length rho (tw qs.length)
        (tr (qs.drop l)) (tr pl) _ _
        ((A₀ * liftBF S qs pl b₁).coeff i + (A₁ * liftBF S qs pl b₀).coeff i) _
        ((A₀ * liftS qs pl b₁).coeff i + (A₁ * liftS qs pl b₀).coeff i)
        ((R₀ * liftBF S qs pl b₁).coeff i + (R₁ * liftBF S qs pl b₀).coeff i)
        hF hP (hb₁ i) ?_ ?_ ?_ ?_ hrho
      · rw [coeff_add', mul_add,
          coeff_mul_combo _ _ _ _ _ _ (hW b₁) i, coeff_mul_combo _ _ _ _ _ _ (hW b₀) i]
        ring
      · rw [coeff_add', coeff_mul_combo_left _ _ _ _ _ hF₀ i,
          coeff_mul_combo_left _ _ _ _ _ hF₁ i]
        ring
      · have h1 := hE1 A₀ hA₀b b₁ i
        have h2 := hE1 A₁ hA₁b b₀ i
        have h3 := mul_le_mul_of_nonneg_left
          (abs_add_le ((A₀ * liftS qs pl b₁).coeff i) ((A₁ * liftS qs pl b₀).coeff i)) hFz.le
        linarith
      · have h1 := hE2 R₀ hR₀b b₁ i
        have h2 := hE2 R₁ hR₁b b₀ i
        have h3 := mul_le_mul_of_nonneg_left
          (abs_add_le ((R₀ * liftBF S qs pl b₁).coeff i) ((R₁ * liftBF S qs pl b₀).coeff i))
          (by positivity : (0 : ℤ) ≤ 2 * (floatDen : ℤ) * floatDen * pl.prod)
        push_cast at *
        linarith
    · show 2 * |(qs.prod : ℤ) * (((qs.drop l).prod : ℤ) * Y₂.coeff i) -
        (t : ℤ) * (F₁ * liftBF S qs pl b₁).coeff i| ≤ _
      refine leveled_final_tol _ _ (qs.take l).prod _ _ _ N qs.length rho (tw qs.length)
        (tr (qs.drop l)) (tr pl) _ _ _ _ _ _ hF hP (hb₂ i)
        (coeff_mul_combo _ _ _ _ _ _ (hW b₁) i)
        (coeff_mul_combo_left _ _ _ _ _ hF₁ i) ?_ ?_ hrho
      · have := hE1 A₁ hA₁b b₁ i
        have := mul_nonneg hFz.le (abs_nonneg ((A₁ * liftS qs pl b₁).coeff i))
        linarith
      · have := hE2 R₁ hR₁b b₁ i
        have : (0 : ℤ) ≤ 2 * (floatDen : ℤ) * floatDen * pl.prod *
            |(R₁ * liftBF S qs pl b₁).coeff i| := by positivity
        push_cast at *
        linarith
    · show 2 * |(qs.prod : ℤ) * (0 : IntPoly N).coeff i - (t : ℤ) * (0 : IntPoly N).coeff i| ≤ _
      simp only [coeff_zero', mul_zero, sub_zero, abs_zero]
      positivity
  · simp only [List.map_cons, List.map_nil, Function.comp_apply, hY₀, hY₁, hY₂, ofInt_modPoly]

end leveled

end Validation.Families.FloatTol
