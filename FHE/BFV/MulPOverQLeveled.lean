import FHE.BFV.MulPOverQ

/-!
# FHE.BFV.MulPOverQLeveled — the slack of the idealised leveled P-over-Q multiplication

`Challenge.BFVMul.leveledMul` (OpenFHE `HPSPOVERQLEVELED` with `drop` limbs dropped internally)
under `leveledAuxOK?` (positive, pairwise coprime moduli). With `l = k − drop`, `Q_l`, `P_l` the
first `l` limbs of `qs`, `ps`, and `D = ∏ qs.drop l = Q/Q_l`:

* `leveledMul_eq`: the result is, coefficient by coefficient modulo `Q`,
  `D·⌊t·(A' ⊗ W)ⱼ/P_l⌉`, where `A'ᵢ = liftAl qs l aᵢ` (the representative in `[-Q_l/2, Q_l/2)`
  of `⌊aᵢ/D⌉`) and `Wᵢ = liftW qs P_l bᵢ`;
* `leveledMul_lifted`: with `Aᵢ = D·A'ᵢ − (D·⌊aᵢ/D⌉ − aᵢ)` (`liftAfull`) and
  `Bᵢ = liftB qs P_l bᵢ`, the hypotheses of `Challenge.BFVMul.stepOK_mul_lifted` hold with `e`,
  `rho` those of `Spec.BudgetBFV.leveledSlack t N Q Q_l P_l k 0 0 0`:
  `e = max D ⌈2kQ/P_l⌉`, `rho = ⌈D + t·N·D·(1 + 2k/P_l + 2k·Q_l/P_l)⌉`.
-/

namespace FHE.BFV.MulPOverQ
open Spec NPoly Scheme Challenge.BFVMul Challenge.BFVMul.HPS Challenge.BFVMul.POverQ
open Validation.Ring Validation.Scheme Validation.Source
open FHE.RNS FHE.BFV.MulHPS

/-! ### Lists -/

theorem prod_take_mul_drop (qs : List ℕ) (l : ℕ) :
    (qs.take l).prod * (qs.drop l).prod = qs.prod := by
  rw [← List.prod_append, List.take_append_drop]

theorem pairwise_append_take {qs ps : List ℕ} (l : ℕ)
    (hcop : (qs ++ ps).Pairwise Nat.Coprime) : (qs.take l ++ ps).Pairwise Nat.Coprime := by
  obtain ⟨h1, h2, h3⟩ := List.pairwise_append.mp hcop
  exact List.pairwise_append.mpr
    ⟨h1.sublist (List.take_sublist _ _), h2, fun q hq p hp => h3 q (List.mem_of_mem_take hq) p hp⟩

/-! ### The final inequality -/

/-- From the rounding `2·|P·y − t·T'| ≤ P`, the fast-conversion identity `Q·T' = P·T'' + E₁` and
the scaling-down identity `T = D·T'' − E₂`: `2·|Q·D·y − t·T| ≤ Q·rho`. -/
theorem leveled_final (Q Ql D Pl t N k rho : ℕ) (y T' T'' T E1 E2 : ℤ) (hPl : 0 < Pl)
    (h1 : 2 * |(Pl : ℤ) * y - t * T'| ≤ Pl) (h2 : (Q : ℤ) * T' = Pl * T'' + E1)
    (h3 : T = D * T'' - E2) (hE1 : |E1| ≤ (N : ℤ) * Ql * k * Q)
    (hE2 : 2 * (Pl : ℤ) * |E2| ≤ (N : ℤ) * D * (Pl * Q + 2 * k * Q))
    (hrho : D * Pl + t * N * D * (Pl + 2 * k + 2 * k * Ql) ≤ rho * Pl) :
    2 * |(Q : ℤ) * (D * y) - t * T| ≤ (Q : ℤ) * rho := by
  have hP : (0 : ℤ) < Pl := by exact_mod_cast hPl
  have hrho' : (D : ℤ) * Pl + t * N * D * (Pl + 2 * k + 2 * k * Ql) ≤ rho * Pl := by
    exact_mod_cast hrho
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
  have a1 : (D : ℤ) * t * |E1| ≤ D * t * ((N : ℤ) * Ql * k * Q) :=
    mul_le_mul_of_nonneg_left hE1 (by positivity)
  have a2 : (Q : ℤ) * D * (2 * |(Pl : ℤ) * y - t * T'|) ≤ Q * D * Pl :=
    mul_le_mul_of_nonneg_left h1 (by positivity)
  have a3 : (t : ℤ) * (2 * (Pl : ℤ) * |E2|) ≤ t * ((N : ℤ) * D * (Pl * Q + 2 * k * Q)) :=
    mul_le_mul_of_nonneg_left hE2 (by positivity)
  have a4 : (Q : ℤ) * ((D : ℤ) * Pl + t * N * D * (Pl + 2 * k + 2 * k * Ql)) ≤ Q * (rho * Pl) :=
    mul_le_mul_of_nonneg_left hrho' (by positivity)
  have h6 : (Pl : ℤ) * (2 * |(Q : ℤ) * (D * y) - t * T|) ≤ Pl * ((Q : ℤ) * rho) := by nlinarith
  exact le_of_mul_le_mul_left h6 hP

/-! ### The slack -/

theorem leveledSlack_e (t N Q Ql Pl k : ℕ) (hPl : 0 < Pl) :
    Q / Ql ≤ (BudgetBFV.leveledSlack t N Q Ql Pl k 0 0 0).e ∧
      2 * k * Q ≤ (BudgetBFV.leveledSlack t N Q Ql Pl k 0 0 0).e * Pl := by
  have hF : 0 < BudgetBFV.floatDen := by unfold BudgetBFV.floatDen; positivity
  have h1 := le_ceilDiv_mul (Q / Ql * (BudgetBFV.floatDen + 2 * 0) + 2 * Q * 0)
    BudgetBFV.floatDen hF
  have h2 := le_ceilDiv_mul (2 * Q * 0 * Pl + 2 * k * Q * BudgetBFV.floatDen)
    (BudgetBFV.floatDen * Pl) (Nat.mul_pos hF hPl)
  show Q / Ql ≤ max (BudgetBFV.ceilDiv (Q / Ql * (BudgetBFV.floatDen + 2 * 0) + 2 * Q * 0)
      BudgetBFV.floatDen)
      (BudgetBFV.ceilDiv (2 * Q * 0 * Pl + 2 * k * Q * BudgetBFV.floatDen)
        (BudgetBFV.floatDen * Pl)) ∧
    2 * k * Q ≤ max (BudgetBFV.ceilDiv (Q / Ql * (BudgetBFV.floatDen + 2 * 0) + 2 * Q * 0)
      BudgetBFV.floatDen)
      (BudgetBFV.ceilDiv (2 * Q * 0 * Pl + 2 * k * Q * BudgetBFV.floatDen)
        (BudgetBFV.floatDen * Pl)) * Pl
  generalize BudgetBFV.ceilDiv (Q / Ql * (BudgetBFV.floatDen + 2 * 0) + 2 * Q * 0)
    BudgetBFV.floatDen = c1 at h1 ⊢
  generalize BudgetBFV.ceilDiv (2 * Q * 0 * Pl + 2 * k * Q * BudgetBFV.floatDen)
    (BudgetBFV.floatDen * Pl) = c2 at h2 ⊢
  constructor
  · refine le_trans ?_ (le_max_left _ _)
    refine Nat.le_of_mul_le_mul_right ?_ hF
    calc Q / Ql * BudgetBFV.floatDen = Q / Ql * (BudgetBFV.floatDen + 2 * 0) + 2 * Q * 0 := by ring
      _ ≤ c1 * BudgetBFV.floatDen := h1
  · refine le_trans ?_ (Nat.mul_le_mul_right _ (le_max_right _ _))
    refine Nat.le_of_mul_le_mul_right ?_ hF
    calc 2 * k * Q * BudgetBFV.floatDen = 2 * Q * 0 * Pl + 2 * k * Q * BudgetBFV.floatDen := by ring
      _ ≤ c2 * (BudgetBFV.floatDen * Pl) := h2
      _ = c2 * Pl * BudgetBFV.floatDen := by ring

theorem leveledSlack_rho (t N Q Ql Pl k : ℕ) (hPl : 0 < Pl) :
    Q / Ql * Pl + t * N * (Q / Ql) * (Pl + 2 * k + 2 * k * Ql) ≤
      (BudgetBFV.leveledSlack t N Q Ql Pl k 0 0 0).rho * Pl := by
  have hF : 0 < BudgetBFV.floatDen := by unfold BudgetBFV.floatDen; positivity
  have hFF : 0 < BudgetBFV.floatDen * BudgetBFV.floatDen := Nat.mul_pos hF hF
  have h := le_ceilDiv_mul
    (Q / Ql * (BudgetBFV.floatDen + 2 * 0) * BudgetBFV.floatDen * Pl +
      t * N * (Q / Ql) * ((BudgetBFV.floatDen + 2 * 0) *
          (Pl * (BudgetBFV.floatDen + 2 * 0) + 2 * k * BudgetBFV.floatDen) +
        2 * k * Ql * (BudgetBFV.floatDen + 2 * 0) * BudgetBFV.floatDen))
    (BudgetBFV.floatDen * BudgetBFV.floatDen * Pl) (Nat.mul_pos hFF hPl)
  show _ ≤ BudgetBFV.ceilDiv
    (Q / Ql * (BudgetBFV.floatDen + 2 * 0) * BudgetBFV.floatDen * Pl +
      t * N * (Q / Ql) * ((BudgetBFV.floatDen + 2 * 0) *
          (Pl * (BudgetBFV.floatDen + 2 * 0) + 2 * k * BudgetBFV.floatDen) +
        2 * k * Ql * (BudgetBFV.floatDen + 2 * 0) * BudgetBFV.floatDen))
    (BudgetBFV.floatDen * BudgetBFV.floatDen * Pl) * Pl
  generalize BudgetBFV.ceilDiv _ _ = c at h ⊢
  refine Nat.le_of_mul_le_mul_right ?_ hFF
  calc (Q / Ql * Pl + t * N * (Q / Ql) * (Pl + 2 * k + 2 * k * Ql)) *
        (BudgetBFV.floatDen * BudgetBFV.floatDen) =
      Q / Ql * (BudgetBFV.floatDen + 2 * 0) * BudgetBFV.floatDen * Pl +
      t * N * (Q / Ql) * ((BudgetBFV.floatDen + 2 * 0) *
          (Pl * (BudgetBFV.floatDen + 2 * 0) + 2 * k * BudgetBFV.floatDen) +
        2 * k * Ql * (BudgetBFV.floatDen + 2 * 0) * BudgetBFV.floatDen) := by ring
    _ ≤ c * (BudgetBFV.floatDen * BudgetBFV.floatDen * Pl) := h
    _ = c * Pl * (BudgetBFV.floatDen * BudgetBFV.floatDen) := by ring

/-! ### Polynomials -/

variable {N : ℕ}

/-- Operand 1 scaled down to `Q_l`: the representative in `[-Q_l/2, Q_l/2)` of `⌊a/D⌉`,
`D = ∏ qs.drop l`. -/
def liftAl (qs : List ℕ) (l : ℕ) (a : IntPoly N) : IntPoly N :=
  liftA (qs.take l) (Challenge.BFV.scaleRound 1 (qs.drop l).prod a)

/-- The rounding error of the scaling down, times `D`: `D·⌊a/D⌉ − a`. -/
def liftRho (qs : List ℕ) (l : ℕ) (a : IntPoly N) : IntPoly N :=
  ⟨fun i => ((qs.drop l).prod : ℤ) *
    (Challenge.BFV.scaleRound 1 (qs.drop l).prod a).coeff i - a.coeff i⟩

/-- Operand 1 as the leveled algorithm multiplies it: `D·A' − (D·⌊a/D⌉ − a)`. -/
def liftAfull (qs : List ℕ) (l : ℕ) (a : IntPoly N) : IntPoly N :=
  ⟨fun i => ((qs.drop l).prod : ℤ) * (liftAl qs l a).coeff i - (liftRho qs l a).coeff i⟩

/-- `ExpandCRTBasisQlHat`: the limbs modulo `qs` of `D·Y`. -/
theorem expandQlHat_toLimbs (qs : List ℕ) (l : ℕ) (hpos : ∀ q ∈ qs, 0 < q) (Y : IntPoly N) :
    expandQlHat qs (qs.take l) (toLimbs (qs.take l) Y) =
      toLimbs qs (⟨fun i => ((qs.drop l).prod : ℤ) * Y.coeff i⟩ : IntPoly N) := by
  have hQl : 0 < (qs.take l).prod := prod_pos' _ fun q hq => hpos q (List.mem_of_mem_take hq)
  have hD : qs.prod / (qs.take l).prod = (qs.drop l).prod := by
    rw [← prod_take_mul_drop qs l, Nat.mul_div_cancel_left _ hQl]
  have hdrop : qs.drop (qs.take l).length = qs.drop l := by
    rw [List.length_take]
    rcases Nat.le_total l qs.length with h | h
    · rw [Nat.min_eq_left h]
    · rw [Nat.min_eq_right h, List.drop_of_length_le (le_refl _), List.drop_of_length_le h]
  have hsplit : ∀ Z : IntPoly N,
      toLimbs qs Z = toLimbs (qs.take l) Z ++ toLimbs (qs.drop l) Z := fun Z => by
    show qs.map _ = (qs.take l).map _ ++ (qs.drop l).map _
    rw [← List.map_append, List.take_append_drop]
  unfold expandQlHat
  rw [hD, hdrop, hsplit]
  congr 1
  · rw [toLimbs_eq, zipWith_map_self]
    refine List.map_congr_left fun q _ => ?_
    ext i
    show Y.coeff i % q * (((qs.drop l).prod % q : ℕ) : ℤ) % q = ((qs.drop l).prod : ℤ) * Y.coeff i % q
    rw [Int.natCast_mod, mul_comm ((qs.drop l).prod : ℤ)]
    exact (Int.ModEq.mul (Int.mod_modEq _ _) (Int.mod_modEq _ _))
  · rw [toLimbs_eq]
    refine List.map_congr_left fun q hq => ?_
    ext i
    show (0 : ℤ) = ((qs.drop l).prod : ℤ) * Y.coeff i % q
    have hd : (q : ℤ) ∣ ((qs.drop l).prod : ℤ) := by exact_mod_cast List.dvd_prod hq
    exact (Int.emod_eq_zero_of_dvd (Dvd.dvd.mul_right hd _)).symm

/-- The definition of the locked `leveledAuxOK?`, by `rfl` (no equation lemma of the locked
definition is realised here). -/
theorem leveledAuxOK_def (t N : ℕ) (qs ps : List ℕ) (drop : ℕ) :
    leveledAuxOK? t N qs ps drop =
      ((qs ++ ps.take (qs.length - drop)).all (fun m => decide (0 < m)) &&
        decide ((qs ++ ps.take (qs.length - drop)).Pairwise Nat.Coprime)) :=
  rfl

theorem leveledAuxOK_iff (t N : ℕ) (qs ps : List ℕ) (drop : ℕ) :
    leveledAuxOK? t N qs ps drop = true ↔
      (∀ m ∈ qs ++ ps.take (qs.length - drop), 0 < m) ∧
        (qs ++ ps.take (qs.length - drop)).Pairwise Nat.Coprime := by
  simp only [leveledAuxOK_def, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq]

/-- **What `leveledMul` computes**: `D·⌊t·(A' ⊗ W)ⱼ/P_l⌉ mod Q`. -/
theorem leveledMul_eq (t : ℕ) (qs ps : List ℕ) (drop : ℕ)
    (haux : leveledAuxOK? t N qs ps drop = true) (a₀ a₁ b₀ b₁ : IntPoly N) :
    leveledMul t qs ps drop [a₀, a₁] [b₀, b₁] =
      (Challenge.Source.tensor
        [liftAl qs (qs.length - drop) a₀, liftAl qs (qs.length - drop) a₁]
        [liftW qs (ps.take (qs.length - drop)) b₀, liftW qs (ps.take (qs.length - drop)) b₁]).map
        fun T => modPoly qs.prod (⟨fun i => ((qs.drop (qs.length - drop)).prod : ℤ) *
          (Challenge.BFV.scaleRound t (ps.take (qs.length - drop)).prod T).coeff i⟩ :
            IntPoly N) := by
  obtain ⟨hpos, hcop⟩ := (leveledAuxOK_iff t N qs ps drop).mp haux
  unfold leveledMul
  dsimp only
  generalize qs.length - drop = l at hpos hcop ⊢
  generalize hpl : ps.take l = pl at hpos hcop ⊢
  have hposq : ∀ q ∈ qs, 0 < q := fun q hq => hpos q (List.mem_append_left _ hq)
  have hcopq : qs.Pairwise Nat.Coprime := (List.pairwise_append.mp hcop).1
  have hposl : ∀ q ∈ qs.take l, 0 < q := fun q hq => hposq q (List.mem_of_mem_take hq)
  have hcopl : (qs.take l).Pairwise Nat.Coprime := hcopq.sublist (List.take_sublist _ _)
  -- the bases of the two scalings
  have hposdl : ∀ m ∈ qs.drop l ++ qs.take l, 0 < m := fun m hm => hposq m (by
    rcases List.mem_append.mp hm with h | h
    · exact List.mem_of_mem_drop h
    · exact List.mem_of_mem_take h)
  have hcopdl : (qs.drop l ++ qs.take l).Pairwise Nat.Coprime :=
    pairwise_swap _ _ (by rw [List.take_append_drop]; exact hcopq)
  have hcoplp : (qs.take l ++ pl).Pairwise Nat.Coprime := pairwise_append_take l hcop
  have hpospl : ∀ m ∈ pl ++ qs.take l, 0 < m := fun m hm => hpos m (by
    rcases List.mem_append.mp hm with h | h
    · exact List.mem_append_right _ h
    · exact List.mem_append_left _ (List.mem_of_mem_take h))
  have hA : ∀ a : IntPoly N,
      expand (qs.take l) pl (scaleRoundOut 1 (qs.drop l) (qs.take l)
        ((toLimbs qs a).drop l) ((toLimbs qs a).take l)) =
      toLimbs (qs.take l ++ pl) (liftAl qs l a) := fun a => by
    have e1 : (toLimbs qs a).drop l = toLimbs (qs.drop l) a := List.map_drop.symm
    have e2 : (toLimbs qs a).take l = toLimbs (qs.take l) a := List.map_take.symm
    rw [e1, e2, scaleRoundOut_toLimbs 1 _ _ hposdl hcopdl, expand_toLimbs' _ _ hposl hcopl]
    rfl
  simp only [List.map_cons, List.map_nil, hA, fastExpand_toLimbs qs pl (qs.take l) hpos hcop,
    tensor_toLimbs, List.map_map]
  refine List.map_congr_left fun T _ => ?_
  have e : toLimbs (qs.take l ++ pl) T = toLimbs (qs.take l) T ++ toLimbs pl T := List.map_append
  have hl : (toLimbs (qs.take l) T).length = (qs.take l).length := List.length_map _
  show reconstruct qs (expandQlHat qs (qs.take l) (scaleRoundOut t pl (qs.take l)
    ((toLimbs (qs.take l ++ pl) T).drop (qs.take l).length)
    ((toLimbs (qs.take l ++ pl) T).take (qs.take l).length))) = _
  rw [e, List.take_left' hl, List.drop_left' hl,
    scaleRoundOut_toLimbs t pl _ hpospl (pairwise_swap _ _ hcoplp),
    expandQlHat_toLimbs qs l hposq, reconstruct_toLimbs qs hposq hcopq]

/-- Linearity of the negacyclic product in its first argument, coefficient by coefficient: from
`a = D·a' − r` coefficientwise, `a·b = D·(a'·b) − r·b`. -/
theorem coeff_mul_combo_left (a a' r b : IntPoly N) (D : ℤ)
    (h : ∀ i, a.coeff i = D * a'.coeff i - r.coeff i) (k : Fin N) :
    (a * b).coeff k = D * (a' * b).coeff k - (r * b).coeff k := by
  simp only [coeff_mul', Finset.mul_sum]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs
  · rw [h i]; ring
  · rw [h i]; ring

/-- The rounding error of the scaling down: `2·|D·⌊a/D⌉ − a| ≤ D`. -/
theorem two_abs_liftRho_le (qs : List ℕ) (l : ℕ) (hD : 0 < (qs.drop l).prod) (a : IntPoly N)
    (i : Fin N) : 2 * |(liftRho qs l a).coeff i| ≤ ((qs.drop l).prod : ℤ) := by
  have h := Validation.BFV.two_abs_roundDiv_sub_le (((1 : ℕ) : ℤ) * a.coeff i) _ hD
  have e : (liftRho qs l a).coeff i = ((qs.drop l).prod : ℤ) *
      roundDiv (((1 : ℕ) : ℤ) * a.coeff i) (qs.drop l).prod - ((1 : ℕ) : ℤ) * a.coeff i := by
    conv_rhs => rw [show ∀ u v : ℤ, u - ((1 : ℕ) : ℤ) * v = u - v from fun u v => by
      rw [Nat.cast_one, one_mul]]
    rfl
  rw [e]
  exact h

/-- The scaling-down term of one product: `4·P_l·|(ρ·B)ᵢ| ≤ N·D·(P_l·Q + 2kQ)`. -/
theorem abs_coeff_liftRho_mul_liftB (qs pl : List ℕ) (l : ℕ) (hpos : ∀ m ∈ qs ++ pl, 0 < m)
    (hcop : (qs ++ pl).Pairwise Nat.Coprime) (a b : IntPoly N) (i : Fin N) :
    4 * (pl.prod : ℤ) * |(liftRho qs l a * liftB qs pl b).coeff i| ≤
      (N : ℤ) * (qs.drop l).prod * ((pl.prod : ℤ) * qs.prod + 2 * qs.length * qs.prod) := by
  have hposq : ∀ q ∈ qs, 0 < q := fun q hq => hpos q (List.mem_append_left _ hq)
  have hposp : ∀ p ∈ pl, 0 < p := fun p hp => hpos p (List.mem_append_right _ hp)
  have hP : (0 : ℤ) < pl.prod := by exact_mod_cast prod_pos' pl hposp
  have hD : 0 < (qs.drop l).prod := prod_pos' _ fun q hq => hposq q (List.mem_of_mem_drop hq)
  set R : ℤ := (pl.prod : ℤ) * qs.prod + 2 * qs.length * qs.prod with hR
  have hR0 : 0 ≤ R := by positivity
  have hM0 : 0 ≤ R / (2 * pl.prod) := Int.ediv_nonneg hR0 (by positivity)
  have hM : R / (2 * (pl.prod : ℤ)) * (2 * pl.prod) ≤ R := Int.ediv_mul_le _ (by positivity)
  have h := abs_coeff_mul_le_N (liftRho qs l a) (liftB qs pl b)
    (((qs.drop l).prod / 2 : ℕ) : ℤ) (R / (2 * pl.prod))
    (fun j => Validation.BFV.abs_le_half (two_abs_liftRho_le qs l hD a j))
    (fun j => by
      have := bVal_bound qs pl hpos hcop (b.coeff j)
      show |bVal qs pl (b.coeff j)| ≤ _
      rw [Int.le_ediv_iff_mul_le (by positivity)]
      linarith) i
  have hhalf : 2 * (((qs.drop l).prod / 2 : ℕ) : ℤ) ≤ (qs.drop l).prod := two_mul_half_le _
  have h2 : (2 * (((qs.drop l).prod / 2 : ℕ) : ℤ)) * (R / (2 * (pl.prod : ℤ)) * (2 * pl.prod)) ≤
      ((qs.drop l).prod : ℤ) * R :=
    mul_le_mul hhalf hM (by positivity) (by positivity)
  have h3 : 4 * (pl.prod : ℤ) * ((N : ℤ) * (((qs.drop l).prod / 2 : ℕ) : ℤ) *
      (R / (2 * pl.prod))) ≤ (N : ℤ) * (((qs.drop l).prod : ℤ) * R) := by
    have := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℤ) ≤ (N : ℤ))
    linarith
  have h4 := mul_le_mul_of_nonneg_left h (by positivity : (0 : ℤ) ≤ 4 * (pl.prod : ℤ))
  linarith

/-- **The idealised leveled P-over-Q multiplication multiplies representatives of bounded size
and rounds within a bounded distance**: the hypotheses of
`Challenge.BFVMul.stepOK_mul_lifted` at `Q = qs.prod`, with the slack
`Spec.BudgetBFV.leveledSlack t N Q Q_l P_l k 0 0 0`, `k = qs.length`, `Q_l`, `P_l` the first
`k − drop` limbs of `qs`, `ps`. -/
theorem leveledMul_lifted (t : ℕ) (qs ps : List ℕ) (drop : ℕ)
    (haux : leveledAuxOK? t N qs ps drop = true)
    (c d : List (IntPoly N)) (hc : c.length = 2) (hd : d.length = 2) :
    ∃ A B X : List (IntPoly N), X.length = 3 ∧
      A.map (ofInt qs.prod) = c.map (ofInt qs.prod) ∧
      B.map (ofInt qs.prod) = d.map (ofInt qs.prod) ∧
      (∀ p ∈ A, 2 * normInf p ≤ qs.prod +
        (BudgetBFV.leveledSlack t N qs.prod (qs.take (qs.length - drop)).prod
          (ps.take (qs.length - drop)).prod qs.length 0 0 0).e) ∧
      (∀ p ∈ B, 2 * normInf p ≤ qs.prod +
        (BudgetBFV.leveledSlack t N qs.prod (qs.take (qs.length - drop)).prod
          (ps.take (qs.length - drop)).prod qs.length 0 0 0).e) ∧
      (∀ (j : ℕ) (i : Fin N),
        2 * |(qs.prod : ℤ) * (X.getD j 0).coeff i -
            (t : ℤ) * ((Challenge.Source.tensor A B).getD j 0).coeff i|
          ≤ (qs.prod : ℤ) *
            (BudgetBFV.leveledSlack t N qs.prod (qs.take (qs.length - drop)).prod
              (ps.take (qs.length - drop)).prod qs.length 0 0 0).rho) ∧
      (leveledMul t qs ps drop c d).map (ofInt qs.prod) = X.map (ofInt qs.prod) := by
  obtain ⟨a₀, a₁, rfl⟩ := List.length_eq_two.mp hc
  obtain ⟨b₀, b₁, rfl⟩ := List.length_eq_two.mp hd
  have hmul := leveledMul_eq t qs ps drop haux a₀ a₁ b₀ b₁
  obtain ⟨hpos, hcop⟩ := (leveledAuxOK_iff t N qs ps drop).mp haux
  generalize qs.length - drop = l at hpos hcop hmul ⊢
  generalize ps.take l = pl at hpos hcop hmul ⊢
  have hposq : ∀ q ∈ qs, 0 < q := fun q hq => hpos q (List.mem_append_left _ hq)
  have hposp : ∀ p ∈ pl, 0 < p := fun p hp => hpos p (List.mem_append_right _ hp)
  have hcopq : qs.Pairwise Nat.Coprime := (List.pairwise_append.mp hcop).1
  have hposl : ∀ q ∈ qs.take l, 0 < q := fun q hq => hposq q (List.mem_of_mem_take hq)
  have hcopl : (qs.take l).Pairwise Nat.Coprime := hcopq.sublist (List.take_sublist _ _)
  have hQ : 0 < qs.prod := prod_pos' qs hposq
  have hP : 0 < pl.prod := prod_pos' pl hposp
  have hQl : 0 < (qs.take l).prod := prod_pos' _ hposl
  have hDpos : 0 < (qs.drop l).prod :=
    prod_pos' _ fun q hq => hposq q (List.mem_of_mem_drop hq)
  have hQD := prod_take_mul_drop qs l
  have hD : qs.prod / (qs.take l).prod = (qs.drop l).prod := by
    rw [← hQD, Nat.mul_div_cancel_left _ hQl]
  have hQDz : ((qs.take l).prod : ℤ) * (qs.drop l).prod = qs.prod := by exact_mod_cast hQD
  obtain ⟨he1, he2⟩ := leveledSlack_e t N qs.prod (qs.take l).prod pl.prod qs.length hP
  have hrho := leveledSlack_rho t N qs.prod (qs.take l).prod pl.prod qs.length hP
  rw [hD] at he1 hrho
  generalize (BudgetBFV.leveledSlack t N qs.prod (qs.take l).prod pl.prod qs.length 0 0 0).e = e
    at he1 he2 ⊢
  generalize (BudgetBFV.leveledSlack t N qs.prod (qs.take l).prod pl.prod qs.length 0 0 0).rho
    = rho at hrho ⊢
  -- the representatives
  have hAl : ∀ (a : IntPoly N) (i : Fin N), 2 * |(liftAl qs l a).coeff i| ≤ ((qs.take l).prod : ℤ) :=
    fun a i => by
      obtain ⟨h1, h2⟩ := switchVal_bounds (qs.take l) hQl
        ((Challenge.BFV.scaleRound 1 (qs.drop l).prod a).coeff i)
      show 2 * |switchVal (qs.take l) _| ≤ _
      rcases abs_cases (switchVal (qs.take l)
        ((Challenge.BFV.scaleRound 1 (qs.drop l).prod a).coeff i)) with ⟨e', _⟩ | ⟨e', _⟩ <;>
        rw [e'] <;> omega
  have hAn : ∀ a : IntPoly N, 2 * normInf (liftAfull qs l a) ≤ qs.prod + e := fun a =>
    two_normInf_le _ _ fun i => by
      have h1 := hAl a i
      have h2 := two_abs_liftRho_le qs l hDpos a i
      have he1' : ((qs.drop l).prod : ℤ) ≤ e := by exact_mod_cast he1
      have h3 : ((qs.drop l).prod : ℤ) * (2 * |(liftAl qs l a).coeff i|) ≤
          (qs.drop l).prod * (qs.take l).prod := mul_le_mul_of_nonneg_left h1 (by positivity)
      have h4 := abs_sub ((qs.drop l).prod * (liftAl qs l a).coeff i) ((liftRho qs l a).coeff i)
      rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℤ) ≤ ((qs.drop l).prod : ℤ))] at h4
      show 2 * |((qs.drop l).prod : ℤ) * (liftAl qs l a).coeff i - (liftRho qs l a).coeff i| ≤
        ((qs.prod + e : ℕ) : ℤ)
      rw [Nat.cast_add]
      linarith
  have hAc : ∀ a : IntPoly N, ofInt qs.prod (liftAfull qs l a) = ofInt qs.prod a := fun a =>
    ofInt_eq_of_dvd _ _ _ fun i => by
      obtain ⟨u, hu⟩ := switchVal_dvd (qs.take l) hposl hcopl
        ((Challenge.BFV.scaleRound 1 (qs.drop l).prod a).coeff i)
      refine ⟨u, ?_⟩
      show ((qs.drop l).prod : ℤ) * switchVal (qs.take l)
          ((Challenge.BFV.scaleRound 1 (qs.drop l).prod a).coeff i) -
        (((qs.drop l).prod : ℤ) * (Challenge.BFV.scaleRound 1 (qs.drop l).prod a).coeff i -
          a.coeff i) - a.coeff i = _
      rw [← hQDz]
      linear_combination ((qs.drop l).prod : ℤ) * hu
  have hBn : ∀ b : IntPoly N, 2 * normInf (liftB qs pl b) ≤ qs.prod + e := fun b =>
    two_normInf_le _ _ fun i => by
      have h1 := bVal_bound qs pl hpos hcop (b.coeff i)
      show 2 * |bVal qs pl (b.coeff i)| ≤ ((qs.prod + e : ℕ) : ℤ)
      have he' : (2 : ℤ) * qs.length * qs.prod ≤ e * pl.prod := by exact_mod_cast he2
      have hP' : (0 : ℤ) < pl.prod := by exact_mod_cast hP
      rw [Nat.cast_add]
      have h2 : 2 * |bVal qs pl (b.coeff i)| * (pl.prod : ℤ) ≤ ((qs.prod : ℤ) + e) * pl.prod := by
        linarith
      exact le_of_mul_le_mul_right h2 hP'
  -- the three error terms of one product
  have hW : ∀ (b : IntPoly N) (i : Fin N), (qs.prod : ℤ) * (liftW qs pl b).coeff i =
      (pl.prod : ℤ) * (liftB qs pl b).coeff i + (liftS qs pl b).coeff i := fun b i =>
    bVal_spec qs pl hpos hcop (b.coeff i)
  have hAf : ∀ (a : IntPoly N) (i : Fin N), (liftAfull qs l a).coeff i =
      ((qs.drop l).prod : ℤ) * (liftAl qs l a).coeff i - (liftRho qs l a).coeff i := fun _ _ => rfl
  have hhalf : 2 * (((qs.take l).prod / 2 : ℕ) : ℤ) ≤ (qs.take l).prod := two_mul_half_le _
  have hnn : (0 : ℤ) ≤ (N : ℤ) * (qs.length * (qs.prod : ℤ)) := by positivity
  have hE1 : ∀ (a b : IntPoly N) (i : Fin N), 2 * |(liftAl qs l a * liftS qs pl b).coeff i| ≤
      (N : ℤ) * (qs.take l).prod * qs.length * qs.prod := fun a b i => by
    have := abs_coeff_liftA_mul_liftS (qs.take l) qs pl hposl hposq
      (Challenge.BFV.scaleRound 1 (qs.drop l).prod a) b i
    have h' : |(liftAl qs l a * liftS qs pl b).coeff i| ≤
        (N : ℤ) * (((qs.take l).prod / 2 : ℕ) : ℤ) * (qs.length * (qs.prod : ℤ)) := this
    nlinarith [mul_le_mul_of_nonneg_left hhalf hnn]
  have hE2 := abs_coeff_liftRho_mul_liftB (N := N) qs pl l hpos hcop
  have hE1nn : (0 : ℤ) ≤ (N : ℤ) * (qs.take l).prod * qs.length * qs.prod := by positivity
  have hE2nn : (0 : ℤ) ≤ (N : ℤ) * (qs.drop l).prod *
      ((pl.prod : ℤ) * qs.prod + 2 * qs.length * qs.prod) := by positivity
  have hPz : (0 : ℤ) < pl.prod := by exact_mod_cast hP
  refine ⟨[liftAfull qs l a₀, liftAfull qs l a₁], [liftB qs pl b₀, liftB qs pl b₁],
    (Challenge.Source.tensor [liftAl qs l a₀, liftAl qs l a₁]
      [liftW qs pl b₀, liftW qs pl b₁]).map fun T =>
        (⟨fun i => ((qs.drop l).prod : ℤ) *
          (Challenge.BFV.scaleRound t pl.prod T).coeff i⟩ : IntPoly N),
    rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [List.map_cons, List.map_nil, hAc]
  · simp only [List.map_cons, List.map_nil]
    rw [ofInt_eq_of_dvd _ (liftB qs pl b₀) b₀ fun i => bVal_dvd qs pl hpos hcop _,
      ofInt_eq_of_dvd _ (liftB qs pl b₁) b₁ fun i => bVal_dvd qs pl hpos hcop _]
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl <;> exact hAn _
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl <;> exact hBn _
  · intro j i
    rcases j with _ | _ | _ | j
    · show 2 * |(qs.prod : ℤ) * (((qs.drop l).prod : ℤ) *
          roundDiv (t * (liftAl qs l a₀ * liftW qs pl b₀).coeff i) pl.prod) -
        (t : ℤ) * (liftAfull qs l a₀ * liftB qs pl b₀).coeff i| ≤ _
      refine leveled_final _ (qs.take l).prod _ _ _ N qs.length rho _ _ _ _ _ _ hP
        (Validation.BFV.two_abs_roundDiv_sub_le _ _ hP)
        (coeff_mul_combo _ _ _ _ _ _ (hW b₀) i)
        (coeff_mul_combo_left _ _ _ _ _ (hAf a₀) i) ?_ ?_ hrho
      · have := hE1 a₀ b₀ i
        have := abs_nonneg ((liftAl qs l a₀ * liftS qs pl b₀).coeff i)
        linarith
      · have := hE2 a₀ b₀ i
        have := abs_nonneg ((liftRho qs l a₀ * liftB qs pl b₀).coeff i)
        nlinarith
    · show 2 * |(qs.prod : ℤ) * (((qs.drop l).prod : ℤ) *
          roundDiv (t * (liftAl qs l a₀ * liftW qs pl b₁ + liftAl qs l a₁ * liftW qs pl b₀).coeff i)
            pl.prod) -
        (t : ℤ) * (liftAfull qs l a₀ * liftB qs pl b₁ +
          liftAfull qs l a₁ * liftB qs pl b₀).coeff i| ≤ _
      refine leveled_final _ (qs.take l).prod _ _ _ N qs.length rho _ _
        ((liftAl qs l a₀ * liftB qs pl b₁).coeff i + (liftAl qs l a₁ * liftB qs pl b₀).coeff i) _
        ((liftAl qs l a₀ * liftS qs pl b₁).coeff i + (liftAl qs l a₁ * liftS qs pl b₀).coeff i)
        ((liftRho qs l a₀ * liftB qs pl b₁).coeff i + (liftRho qs l a₁ * liftB qs pl b₀).coeff i)
        hP (Validation.BFV.two_abs_roundDiv_sub_le _ _ hP) ?_ ?_ ?_ ?_ hrho
      · rw [coeff_add', mul_add,
          coeff_mul_combo _ _ _ _ _ _ (hW b₁) i, coeff_mul_combo _ _ _ _ _ _ (hW b₀) i]
        ring
      · rw [coeff_add', coeff_mul_combo_left _ _ _ _ _ (hAf a₀) i,
          coeff_mul_combo_left _ _ _ _ _ (hAf a₁) i]
        ring
      · have h1 := hE1 a₀ b₁ i
        have h2 := hE1 a₁ b₀ i
        have := abs_add_le ((liftAl qs l a₀ * liftS qs pl b₁).coeff i)
          ((liftAl qs l a₁ * liftS qs pl b₀).coeff i)
        linarith
      · have h1 := hE2 a₀ b₁ i
        have h2 := hE2 a₁ b₀ i
        have h3 := abs_add_le ((liftRho qs l a₀ * liftB qs pl b₁).coeff i)
          ((liftRho qs l a₁ * liftB qs pl b₀).coeff i)
        have h4 := mul_le_mul_of_nonneg_left h3 (by positivity : (0 : ℤ) ≤ 4 * (pl.prod : ℤ))
        linarith
    · show 2 * |(qs.prod : ℤ) * (((qs.drop l).prod : ℤ) *
          roundDiv (t * (liftAl qs l a₁ * liftW qs pl b₁).coeff i) pl.prod) -
        (t : ℤ) * (liftAfull qs l a₁ * liftB qs pl b₁).coeff i| ≤ _
      refine leveled_final _ (qs.take l).prod _ _ _ N qs.length rho _ _ _ _ _ _ hP
        (Validation.BFV.two_abs_roundDiv_sub_le _ _ hP)
        (coeff_mul_combo _ _ _ _ _ _ (hW b₁) i)
        (coeff_mul_combo_left _ _ _ _ _ (hAf a₁) i) ?_ ?_ hrho
      · have := hE1 a₁ b₁ i
        have := abs_nonneg ((liftAl qs l a₁ * liftS qs pl b₁).coeff i)
        linarith
      · have := hE2 a₁ b₁ i
        have := abs_nonneg ((liftRho qs l a₁ * liftB qs pl b₁).coeff i)
        nlinarith
    · show 2 * |(qs.prod : ℤ) * (0 : IntPoly N).coeff i - (t : ℤ) * (0 : IntPoly N).coeff i| ≤ _
      simp only [coeff_zero', mul_zero, sub_zero, abs_zero]
      positivity
  · rw [hmul, List.map_map, List.map_map]
    exact List.map_congr_left fun T _ => ofInt_modPoly _ _

end FHE.BFV.MulPOverQ
