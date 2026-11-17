import FHE.BFV.FloatPOverQ

/-!
# FHE.BFV.FloatLeveled — the slack of the leveled P-over-Q multiplication with sums within the tolerances

`Challenge.BFVMul.Fl.leveledMul S` (OpenFHE `HPSPOVERQLEVELED` with `drop` limbs dropped
internally, the truncated sums taken from `S : Fl.Sums`), for every `S` with `Fl.SumsOK S`, under
`floatAuxOK? qs (ps.take l)`. With `l = k − drop`, `Q_l`, `P_l` the first `l` limbs of `qs`, `ps`,
`D = ∏ qs.drop l = Q/Q_l`, `F = 2⁵³`, `w = doubleSw k`, `r1 = doubleSr (qs.drop l)`,
`r = doubleSr P_l`:

* operand 1 is scaled down to an integer `a'` with `2·F·|D·a' − a| ≤ D·(F + 2·r1)` and lifted by
  the tolerant switch from `Q_l` to `A' ≡ a' (mod Q_l)`, `2·F·|A'| ≤ Q_l·(F + 2w)`; the
  representative multiplied is `A = D·A' − (D·a' − a) ≡ a (mod Q)`;
* operand 2 is `W`, `B = (Q·W − S)/P_l` as in `FHE.BFV.FloatPOverQ` with `P_l` for `P`;
* the result is `D·Y` with `2·F·|P_l·Y − t·(A' ⊗ W)| ≤ P_l·(F + 2r)`.

`leveledMul_lifted`: these satisfy the hypotheses of `Challenge.BFVMul.stepOK_mul_lifted` with
`e`, `rho` those of `Spec.BudgetBFV.leveledSlack t N Q Q_l P_l k w r1 r`. Neither the flag `ok`
of the slack nor a condition on `drop` is used.
-/

namespace FHE.BFV.FloatLeveled
open Spec NPoly Scheme Challenge.BFVMul Challenge.BFVMul.HPS Challenge.BFVMul.POverQ
open Validation.Ring Validation.Scheme Validation.Source
open FHE.RNS FHE.BFV.MulHPS FHE.BFV.MulPOverQ FHE.BFV.FloatPOverQ Spec.BudgetBFV

/-! ### The final inequality -/

/-- From the scaling `2·F·|P·y − t·T'| ≤ P·(F + 2r)`, the fast-conversion identity
`Q·T' = P·T'' + E₁` and the scaling-down identity `T = D·T'' − E₂`: `2·|Q·D·y − t·T| ≤ Q·rho`. -/
theorem leveled_final_tol (F Q Ql D Pl t N k rho w r1 r : ℕ) (y T' T'' T E1 E2 : ℤ)
    (hF : 0 < F) (hPl : 0 < Pl)
    (h1 : 2 * (F : ℤ) * |(Pl : ℤ) * y - t * T'| ≤ (Pl : ℤ) * ((F : ℤ) + 2 * r))
    (h2 : (Q : ℤ) * T' = Pl * T'' + E1) (h3 : T = D * T'' - E2)
    (hE1 : (F : ℤ) * |E1| ≤ (N : ℤ) * ((Ql : ℤ) * ((F : ℤ) + 2 * w)) * (k * Q))
    (hE2 : 2 * (F : ℤ) * F * Pl * |E2| ≤
      (N : ℤ) * ((D : ℤ) * ((F : ℤ) + 2 * r1)) *
        ((Q : ℤ) * ((Pl : ℤ) * ((F : ℤ) + 2 * w)) + 2 * F * (k * Q)))
    (hrho : D * (F + 2 * r) * F * Pl +
        t * N * D * ((F + 2 * r1) * (Pl * (F + 2 * w) + 2 * k * F) +
          2 * k * Ql * (F + 2 * w) * F) ≤ rho * (F * F * Pl)) :
    2 * |(Q : ℤ) * (D * y) - t * T| ≤ (Q : ℤ) * rho := by
  have hP : (0 : ℤ) < Pl := by exact_mod_cast hPl
  have hFFP : (0 : ℤ) < (F : ℤ) * F * Pl := by
    exact_mod_cast Nat.mul_pos (Nat.mul_pos hF hF) hPl
  have hrho' : (D : ℤ) * (F + 2 * r) * F * Pl +
      t * N * D * ((F + 2 * r1) * (Pl * (F + 2 * w) + 2 * k * F) +
        2 * k * Ql * (F + 2 * w) * F) ≤ rho * (F * F * Pl) := by exact_mod_cast hrho
  have e : (Pl : ℤ) * ((Q : ℤ) * (D * y) - t * T) =
      D * t * E1 + Q * D * (Pl * y - t * T') + t * Pl * E2 := by
    rw [h3]; linear_combination ((D : ℤ) * t) * h2
  have h4 : |(Pl : ℤ) * ((Q : ℤ) * (D * y) - t * T)| ≤
      D * t * |E1| + Q * D * |(Pl : ℤ) * y - t * T'| + t * Pl * |E2| := by
    rw [e]
    refine (abs_add_three _ _ _).trans ?_
    rw [abs_mul ((D : ℤ) * t) E1, abs_mul ((Q : ℤ) * D) _, abs_mul ((t : ℤ) * Pl) E2,
      abs_of_nonneg (by positivity : (0 : ℤ) ≤ (D : ℤ) * t),
      abs_of_nonneg (by positivity : (0 : ℤ) ≤ (Q : ℤ) * D),
      abs_of_nonneg (by positivity : (0 : ℤ) ≤ (t : ℤ) * Pl)]
  rw [abs_mul, abs_of_pos hP] at h4
  have a0 := mul_le_mul_of_nonneg_left h4 (by positivity : (0 : ℤ) ≤ 2 * (F : ℤ) * F)
  have a1 := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℤ) ≤ (Q : ℤ) * D * F)
  have a2 := mul_le_mul_of_nonneg_left hE1 (by positivity : (0 : ℤ) ≤ 2 * (F : ℤ) * D * t)
  have a3 := mul_le_mul_of_nonneg_left hE2 (Nat.cast_nonneg (α := ℤ) t)
  have a4 := mul_le_mul_of_nonneg_left hrho' (Nat.cast_nonneg (α := ℤ) Q)
  have h6 : (F : ℤ) * F * Pl * (2 * |(Q : ℤ) * (D * y) - t * T|) ≤
      (F : ℤ) * F * Pl * ((Q : ℤ) * rho) := by linarith
  exact le_of_mul_le_mul_left h6 hFFP

/-! ### The slack -/

theorem leveledSlack_e_tol (t N Q Ql Pl k w r1 r : ℕ) (hPl : 0 < Pl) :
    Q / Ql * (floatDen + 2 * r1) + 2 * Q * w ≤
        (leveledSlack t N Q Ql Pl k w r1 r).e * floatDen ∧
      2 * Q * w * Pl + 2 * k * Q * floatDen ≤
        (leveledSlack t N Q Ql Pl k w r1 r).e * (floatDen * Pl) := by
  have hF := floatDen_pos
  have h1 := le_ceilDiv_mul (Q / Ql * (floatDen + 2 * r1) + 2 * Q * w) floatDen hF
  have h2 := le_ceilDiv_mul (2 * Q * w * Pl + 2 * k * Q * floatDen) (floatDen * Pl)
    (Nat.mul_pos hF hPl)
  show Q / Ql * (floatDen + 2 * r1) + 2 * Q * w ≤
      max (ceilDiv (Q / Ql * (floatDen + 2 * r1) + 2 * Q * w) floatDen)
        (ceilDiv (2 * Q * w * Pl + 2 * k * Q * floatDen) (floatDen * Pl)) * floatDen ∧
    2 * Q * w * Pl + 2 * k * Q * floatDen ≤
      max (ceilDiv (Q / Ql * (floatDen + 2 * r1) + 2 * Q * w) floatDen)
        (ceilDiv (2 * Q * w * Pl + 2 * k * Q * floatDen) (floatDen * Pl)) * (floatDen * Pl)
  exact ⟨h1.trans (Nat.mul_le_mul_right _ (le_max_left _ _)),
    h2.trans (Nat.mul_le_mul_right _ (le_max_right _ _))⟩

theorem leveledSlack_rho_tol (t N Q Ql Pl k w r1 r : ℕ) (hPl : 0 < Pl) :
    Q / Ql * (floatDen + 2 * r) * floatDen * Pl +
        t * N * (Q / Ql) * ((floatDen + 2 * r1) * (Pl * (floatDen + 2 * w) + 2 * k * floatDen) +
          2 * k * Ql * (floatDen + 2 * w) * floatDen) ≤
      (leveledSlack t N Q Ql Pl k w r1 r).rho * (floatDen * floatDen * Pl) :=
  le_ceilDiv_mul _ _ (Nat.mul_pos (Nat.mul_pos floatDen_pos floatDen_pos) hPl)

/-! ### Polynomials -/

variable {N : ℕ}

/-- **Operand 1 of the leveled multiplication**: the tolerant scaling down from `Q` to `Q_l`
followed by the tolerant extension to `P_l` gives the limbs of a polynomial `A'` with
`2·F·|A'| ≤ Q_l·(F + 2w)`; with `Rho` the error of the scaling down
(`2·F·|Rho| ≤ D·(F + 2·doubleSr (qs.drop l))`), `Af = D·A' − Rho ≡ a (mod Q)`. -/
theorem scaleDown_expand (S : Fl.Sums) (hS : Fl.SumsOK S) (qs pl : List ℕ) (l : ℕ)
    (hposq : ∀ q ∈ qs, 0 < q) (hcopq : qs.Pairwise Nat.Coprime) (hfq : floatBasisOK qs = true)
    (w : ℕ) (hw : doubleSw (qs.take l).length ≤ w) (a : IntPoly N) :
    ∃ A' Rho Af : IntPoly N,
      Fl.expand S (qs.take l) pl (Fl.scaleRoundOut S 1 (qs.drop l) (qs.take l)
        ((toLimbs qs a).drop l) ((toLimbs qs a).take l)) = toLimbs (qs.take l ++ pl) A' ∧
      (∀ i, 2 * (floatDen : ℤ) * |A'.coeff i| ≤
        ((qs.take l).prod : ℤ) * ((floatDen : ℤ) + 2 * w)) ∧
      (∀ i, 2 * (floatDen : ℤ) * |Rho.coeff i| ≤
        ((qs.drop l).prod : ℤ) * ((floatDen : ℤ) + 2 * (doubleSr (qs.drop l) : ℤ))) ∧
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
  have hw' : (doubleSw (qs.take l).length : ℤ) ≤ w := by exact_mod_cast hw
  obtain ⟨X, hX, hXb⟩ :=
    scaleRoundOut_toLimbs_fl S hS 1 (qs.drop l) (qs.take l) hposdl hcopdl hfd a
  refine ⟨liftAF S (qs.take l) X,
    ⟨fun i => ((qs.drop l).prod : ℤ) * X.coeff i - a.coeff i⟩,
    ⟨fun i => ((qs.drop l).prod : ℤ) * (liftAF S (qs.take l) X).coeff i -
      (((qs.drop l).prod : ℤ) * X.coeff i - a.coeff i)⟩, ?_, ?_, ?_, fun _ => rfl, ?_⟩
  · have e1 : (toLimbs qs a).drop l = toLimbs (qs.drop l) a := List.map_drop.symm
    have e2 : (toLimbs qs a).take l = toLimbs (qs.take l) a := List.map_take.symm
    rw [e1, e2, hX, expand_toLimbs_fl S _ _ hposl hcopl]
  · intro i
    have h1 : 2 * (floatDen : ℤ) * |FloatScalar.switchVal S (qs.take l) (X.coeff i)| ≤ _ :=
      FloatScalar.switchVal_bound S hS (qs.take l) hposl hcopl hfl (X.coeff i)
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

/-- The excess term of one product: `2·F·|(A'·S)ᵢ| ≤ N·α·k·Q` for `2·F·|A'| ≤ α`. -/
theorem abs_coeff_mul_liftS (A : IntPoly N) (α : ℤ)
    (hA : ∀ j, 2 * (floatDen : ℤ) * |A.coeff j| ≤ α) (qs ps : List ℕ)
    (hposq : ∀ q ∈ qs, 0 < q) (b : IntPoly N) (i : Fin N) :
    2 * (floatDen : ℤ) * |(A * liftS qs ps b).coeff i| ≤
      (N : ℤ) * α * (qs.length * (qs.prod : ℤ)) := by
  have hF : (0 : ℤ) < 2 * (floatDen : ℤ) := by
    have : (0 : ℤ) < floatDen := by exact_mod_cast floatDen_pos
    linarith
  have h := abs_coeff_mul_scaled A (liftS qs ps b) (2 * (floatDen : ℤ)) 1 α
    (qs.length * (qs.prod : ℤ)) hF one_pos hA
    (fun j => by
      obtain ⟨h1, h2⟩ := sVal_bounds qs hposq ps.prod (b.coeff j)
      show 1 * |sVal qs ps.prod (b.coeff j)| ≤ _
      rw [one_mul, abs_of_nonneg h1]
      exact h2) i
  linarith

/-- The scaling-down term of one product:
`(2·F)·(2·F·P_l)·|(Rho·B)ᵢ| ≤ N·β·(Q·P_l·(F + 2w) + 2·F·k·Q)` for `2·F·|Rho| ≤ β`. -/
theorem abs_coeff_mul_liftBF (S : Fl.Sums) (hS : Fl.SumsOK S) (Rho : IntPoly N) (β : ℤ)
    (hR : ∀ j, 2 * (floatDen : ℤ) * |Rho.coeff j| ≤ β) (qs pl : List ℕ)
    (hpos : ∀ m ∈ qs ++ pl, 0 < m) (hcop : (qs ++ pl).Pairwise Nat.Coprime)
    (hfb : floatBasisOK pl = true) (w : ℕ) (hw : doubleSw pl.length ≤ w) (b : IntPoly N)
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
      have := bValF_bound S hS qs pl hpos hcop hfb w hw (b.coeff j)
      show 2 * (floatDen : ℤ) * pl.prod * |bValF S qs pl (b.coeff j)| ≤ _
      linarith) i

/-! ### The theorem -/

/-- **The leveled P-over-Q multiplication with sums within the tolerances multiplies
representatives of bounded size and rounds within a bounded distance**: the hypotheses of
`Challenge.BFVMul.stepOK_mul_lifted` at `Q = qs.prod`, with the slack
`Spec.BudgetBFV.leveledSlack t N Q Q_l P_l k (doubleSw k) (doubleSr (qs.drop l)) (doubleSr P_l)`,
`k = qs.length`, `l = k − drop`, `Q_l`, `P_l` the first `l` limbs of `qs`, `ps`. -/
theorem leveledMul_lifted (S : Fl.Sums) (hS : Fl.SumsOK S) (t : ℕ) (qs ps : List ℕ) (drop : ℕ)
    (haux : floatAuxOK? qs (ps.take (qs.length - drop)) = true)
    (c d : List (IntPoly N)) (hc : c.length = 2) (hd : d.length = 2) :
    ∃ A B X : List (IntPoly N), X.length = 3 ∧
      A.map (ofInt qs.prod) = c.map (ofInt qs.prod) ∧
      B.map (ofInt qs.prod) = d.map (ofInt qs.prod) ∧
      (∀ p ∈ A, 2 * normInf p ≤ qs.prod +
        (leveledSlack t N qs.prod (qs.take (qs.length - drop)).prod
          (ps.take (qs.length - drop)).prod qs.length (doubleSw qs.length)
          (doubleSr (qs.drop (qs.length - drop)))
          (doubleSr (ps.take (qs.length - drop)))).e) ∧
      (∀ p ∈ B, 2 * normInf p ≤ qs.prod +
        (leveledSlack t N qs.prod (qs.take (qs.length - drop)).prod
          (ps.take (qs.length - drop)).prod qs.length (doubleSw qs.length)
          (doubleSr (qs.drop (qs.length - drop)))
          (doubleSr (ps.take (qs.length - drop)))).e) ∧
      (∀ (j : ℕ) (i : Fin N),
        2 * |(qs.prod : ℤ) * (X.getD j 0).coeff i -
            (t : ℤ) * ((Challenge.Source.tensor A B).getD j 0).coeff i|
          ≤ (qs.prod : ℤ) *
            (leveledSlack t N qs.prod (qs.take (qs.length - drop)).prod
              (ps.take (qs.length - drop)).prod qs.length (doubleSw qs.length)
              (doubleSr (qs.drop (qs.length - drop)))
              (doubleSr (ps.take (qs.length - drop)))).rho) ∧
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
  have hwl : doubleSw (qs.take l).length ≤ doubleSw qs.length :=
    doubleSw_mono (List.length_take_le' _ _)
  have hwp : doubleSw pl.length ≤ doubleSw qs.length := doubleSw_mono hpll
  obtain ⟨he1, he2⟩ := leveledSlack_e_tol t N qs.prod (qs.take l).prod pl.prod qs.length
    (doubleSw qs.length) (doubleSr (qs.drop l)) (doubleSr pl) hP
  have hrho := leveledSlack_rho_tol t N qs.prod (qs.take l).prod pl.prod qs.length
    (doubleSw qs.length) (doubleSr (qs.drop l)) (doubleSr pl) hP
  rw [hD] at he1 hrho
  generalize (leveledSlack t N qs.prod (qs.take l).prod pl.prod qs.length
    (doubleSw qs.length) (doubleSr (qs.drop l)) (doubleSr pl)).e = e at he1 he2 ⊢
  generalize (leveledSlack t N qs.prod (qs.take l).prod pl.prod qs.length
    (doubleSw qs.length) (doubleSr (qs.drop l)) (doubleSr pl)).rho = rho at hrho ⊢
  -- operand 1
  obtain ⟨A₀, R₀, F₀, hA₀, hA₀b, hR₀b, hF₀, hF₀d⟩ :=
    scaleDown_expand S hS qs pl l hposq hcopq hfq _ hwl a₀
  obtain ⟨A₁, R₁, F₁, hA₁, hA₁b, hR₁b, hF₁, hF₁d⟩ :=
    scaleDown_expand S hS qs pl l hposq hcopq hfq _ hwl a₁
  have hAn : ∀ A' R Af : IntPoly N,
      (∀ i, 2 * (floatDen : ℤ) * |A'.coeff i| ≤
        ((qs.take l).prod : ℤ) * ((floatDen : ℤ) + 2 * (doubleSw qs.length : ℕ))) →
      (∀ i, 2 * (floatDen : ℤ) * |R.coeff i| ≤
        ((qs.drop l).prod : ℤ) * ((floatDen : ℤ) + 2 * (doubleSr (qs.drop l) : ℤ))) →
      (∀ i, Af.coeff i = ((qs.drop l).prod : ℤ) * A'.coeff i - R.coeff i) →
      2 * normInf Af ≤ qs.prod + e := fun A' R Af h1 h2 h3 =>
    two_normInf_le _ _ fun i => by
      have he1' : ((qs.drop l).prod : ℤ) * ((floatDen : ℤ) + 2 * (doubleSr (qs.drop l) : ℤ)) +
          2 * qs.prod * (doubleSw qs.length : ℕ) ≤ e * floatDen := by exact_mod_cast he1
      have h4 := abs_sub (((qs.drop l).prod : ℤ) * A'.coeff i) (R.coeff i)
      rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg (α := ℤ) (qs.drop l).prod)] at h4
      have h5 := mul_le_mul_of_nonneg_left (h1 i) (Nat.cast_nonneg (α := ℤ) (qs.drop l).prod)
      have h6 : ((qs.drop l).prod : ℤ) *
          (((qs.take l).prod : ℤ) * ((floatDen : ℤ) + 2 * (doubleSw qs.length : ℕ))) =
          qs.prod * ((floatDen : ℤ) + 2 * (doubleSw qs.length : ℕ)) := by
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
        (bValF_bound S hS qs pl hpos hcop hfp _ hwp (b.coeff i))
  -- the error terms of one product
  have hW : ∀ (b : IntPoly N) (i : Fin N), (qs.prod : ℤ) * (liftWF S qs pl b).coeff i =
      (pl.prod : ℤ) * (liftBF S qs pl b).coeff i + (liftS qs pl b).coeff i := fun b i =>
    bValF_spec S qs pl hpos hcop (b.coeff i)
  have hE1 : ∀ (A' : IntPoly N), (∀ i, 2 * (floatDen : ℤ) * |A'.coeff i| ≤
        ((qs.take l).prod : ℤ) * ((floatDen : ℤ) + 2 * (doubleSw qs.length : ℕ))) →
      ∀ (b : IntPoly N) (i : Fin N),
      2 * (floatDen : ℤ) * |(A' * liftS qs pl b).coeff i| ≤
        (N : ℤ) * (((qs.take l).prod : ℤ) * ((floatDen : ℤ) + 2 * (doubleSw qs.length : ℕ))) *
          (qs.length * (qs.prod : ℤ)) := fun A' h b i =>
    abs_coeff_mul_liftS A' _ h qs pl hposq b i
  have hE2 : ∀ (R : IntPoly N), (∀ i, 2 * (floatDen : ℤ) * |R.coeff i| ≤
        ((qs.drop l).prod : ℤ) * ((floatDen : ℤ) + 2 * (doubleSr (qs.drop l) : ℤ))) →
      ∀ (b : IntPoly N) (i : Fin N),
      2 * (2 * (floatDen : ℤ) * floatDen * pl.prod * |(R * liftBF S qs pl b).coeff i|) ≤
        (N : ℤ) * (((qs.drop l).prod : ℤ) * ((floatDen : ℤ) + 2 * (doubleSr (qs.drop l) : ℕ))) *
          ((qs.prod : ℤ) * ((pl.prod : ℤ) * ((floatDen : ℤ) + 2 * (doubleSw qs.length : ℕ))) +
            2 * floatDen * (qs.length * (qs.prod : ℤ))) := fun R h b i => by
    have := abs_coeff_mul_liftBF S hS R _ h qs pl hpos hcop hfp _ hwp b i
    linarith
  -- what the algorithm computes
  have hstep : ∀ T : IntPoly N, ∃ Y : IntPoly N,
      reconstruct qs (expandQlHat qs (qs.take l) (Fl.scaleRoundOut S t pl (qs.take l)
        ((toLimbs (qs.take l ++ pl) T).drop (qs.take l).length)
        ((toLimbs (qs.take l ++ pl) T).take (qs.take l).length))) =
        modPoly qs.prod (⟨fun i => ((qs.drop l).prod : ℤ) * Y.coeff i⟩ : IntPoly N) ∧
      ∀ i, 2 * (floatDen : ℤ) * |(pl.prod : ℤ) * Y.coeff i - t * T.coeff i| ≤
        (pl.prod : ℤ) * ((floatDen : ℤ) + 2 * (doubleSr pl : ℤ)) := fun T => by
    obtain ⟨Y, hY, hYb⟩ :=
      scaleRoundOut_toLimbs_fl S hS t pl (qs.take l) hpospl (pairwise_swap _ _ hcoplp) hfp T
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
      refine leveled_final_tol _ _ (qs.take l).prod _ _ _ N qs.length rho (doubleSw qs.length)
        (doubleSr (qs.drop l)) (doubleSr pl) _ _ _ _ _ _ hF hP (hb₀ i)
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
      refine leveled_final_tol _ _ (qs.take l).prod _ _ _ N qs.length rho (doubleSw qs.length)
        (doubleSr (qs.drop l)) (doubleSr pl) _ _
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
      refine leveled_final_tol _ _ (qs.take l).prod _ _ _ N qs.length rho (doubleSw qs.length)
        (doubleSr (qs.drop l)) (doubleSr pl) _ _ _ _ _ _ hF hP (hb₂ i)
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

end FHE.BFV.FloatLeveled
