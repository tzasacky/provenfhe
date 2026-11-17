import Challenge.BFVMul.BEHZWord
import FHE.BFV.MulBEHZ

/-!
# FHE.BFV.MulBEHZWord — the Shenoy–Kumaresan correction of BEHZ is at least `−q`

The facts behind `Challenge.BFVMul.behz_sk_alpha_ge` (proved in
`Validation/BFVMul/BEHZWord.lean`):

* `floor_tensor_small`: every coefficient `F` of the fast floor of the integer tensor product of
  the lifts satisfies `2·|F| ≤ B·R` whenever `t·N·Q·(m̃ + 2(k−1))² + 2k·m̃² ≤ m̃²·B·R` (the
  argument of `FHE.BFV.MulBEHZ.behzMul_eq`, for any `R`);
* `skAlpha_ge`: when Shenoy–Kumaresan is exact, `B·α = Σⱼ zⱼ·B̂ⱼ − F ≥ −F`, so `|F| ≤ q·B`
  gives `α ≥ −q`;
* `skAlpha1_eq`: the locked `BEHZ.skAlpha1` on the residues of `F` is `skAlpha bs msk F`.
-/

namespace FHE.BFV.MulBEHZ
open Spec NPoly Scheme Challenge.BFVMul Challenge.BFVMul.HPS Challenge.BFVMul.BEHZ
open Validation.Ring Validation.Scheme Validation.Source
open FHE.RNS FHE.BFV.MulHPS

variable {N : ℕ}

theorem behzWordOK_iff (t N : ℕ) (qs bs : List ℕ) (msk mt : ℕ) :
    behzWordOK? t N qs bs msk mt = true ↔
      floatBasisOK qs = true ∧ floatBasisOK (bs ++ [msk]) = true ∧
        (∀ b ∈ bs ++ [msk], mt < b) ∧
        ∀ q ∈ qs, t * N * qs.prod * (mt + 2 * (qs.length - 1)) ^ 2 + 2 * qs.length * mt ^ 2 ≤
          mt ^ 2 * bs.prod * (2 * q) := by
  unfold behzWordOK?
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, and_assoc]

/-- `skAlpha1` on the residues of `F` is `skAlpha bs msk F`. -/
theorem skAlpha1_eq (bs : List ℕ) (msk : ℕ) (F : ℤ) :
    skAlpha1 bs msk (bs.map fun b : ℕ => F % b) (F % msk) = skAlpha bs msk F := by
  have hm : convSum bs (bs.map fun b : ℕ => F % b * invMod (bs.prod / b) b % b) msk % msk =
      skZ bs F % msk := convSum_map bs _ msk
  unfold skAlpha1 skAlpha
  simp only [digits_map, hm]

/-- **The correction is at least `−q`** when Shenoy–Kumaresan is exact and `|F| ≤ q·B`. -/
theorem skAlpha_ge (bs : List ℕ) (hpos : ∀ b ∈ bs, 0 < b) (hcop : bs.Pairwise Nat.Coprime)
    (msk : ℕ) (hmsk : 0 < msk) (hcm : Nat.Coprime bs.prod msk) (F : ℤ)
    (hF : 2 * |F| ≤ (bs.prod : ℤ) * ((msk : ℤ) - 1 - 2 * bs.length)) (q : ℕ)
    (hFq : 2 * |F| ≤ (bs.prod : ℤ) * (2 * q)) :
    -(q : ℤ) ≤ skAlpha bs msk F := by
  have h := skVal_eq_self bs hpos hcop msk hmsk hcm F hF
  unfold skVal at h
  have hz : 0 ≤ skZ bs F := (crtTerms_bounds bs hpos fun b => F % b * invMod (bs.prod / b) b).1
  have hB : (0 : ℤ) < bs.prod := by exact_mod_cast prod_pos' bs hpos
  have hFa : -|F| ≤ F := neg_abs_le F
  have hFle : F ≤ |F| := le_abs_self F
  by_contra hlt
  have h1 : skAlpha bs msk F + 1 ≤ -(q : ℤ) := by omega
  have h2 : (skAlpha bs msk F + 1) * (bs.prod : ℤ) ≤ -(q : ℤ) * bs.prod :=
    mul_le_mul_of_nonneg_right h1 hB.le
  linarith

/-- **The fast floor of the tensor product of the lifts is small**: under the coprimality and
`m̃` conditions of `behzAuxOK?` and the size inequality with any `R`, `2·|F| ≤ B·R` for every
coefficient `F` of the fast floor of every component. -/
theorem floor_tensor_small (t : ℕ) (qs : List ℕ) (Bp R mt : ℕ) (hposq : ∀ q ∈ qs, 0 < q)
    (hcopq : qs.Pairwise Nat.Coprime) (hmt : 0 < mt) (heven : mt % 2 = 0)
    (hQmt : Nat.Coprime qs.prod mt)
    (hsize : t * N * qs.prod * (mt + 2 * (qs.length - 1)) ^ 2 + 2 * qs.length * mt ^ 2 ≤
      mt ^ 2 * Bp * R)
    (a₀ a₁ b₀ b₁ : IntPoly N)
    (T : IntPoly N) (hT : T ∈ Challenge.Source.tensor [smmrPoly qs mt a₀, smmrPoly qs mt a₁]
      [smmrPoly qs mt b₀, smmrPoly qs mt b₁]) (i : Fin N) :
    2 * |(floorPoly t qs T).coeff i| ≤ (Bp : ℤ) * R := by
  have hQ : 0 < qs.prod := prod_pos' qs hposq
  have hmt' : (0 : ℤ) < 2 * mt := by exact_mod_cast (by omega : 0 < 2 * mt)
  obtain ⟨W, hW⟩ : ∃ W : ℤ, W = (qs.prod : ℤ) * ((mt + 2 * (qs.length - 1) : ℕ) : ℤ) := ⟨_, rfl⟩
  have hW0 : 0 ≤ W := by rw [hW]; positivity
  have hMa0 : 0 ≤ W / (2 * mt) := Int.ediv_nonneg hW0 hmt'.le
  have hMa : 2 * (mt : ℤ) * (W / (2 * mt)) ≤ W := Int.mul_ediv_self_le hmt'.ne'
  have hlift : ∀ (a : IntPoly N) (i : Fin N), |(smmrPoly qs mt a).coeff i| ≤ W / (2 * mt) := by
    intro a i
    rw [Int.le_ediv_iff_mul_le hmt', hW]
    have := smmrPoly_bound qs hposq mt hmt heven hQmt a i
    linarith
  have hb : |T.coeff i| ≤ 2 * (N * (W / (2 * mt)) * (W / (2 * mt))) := by
    have hnn : (0 : ℤ) ≤ N * (W / (2 * mt)) * (W / (2 * mt)) := by positivity
    have hm : ∀ a b : IntPoly N, |(smmrPoly qs mt a * smmrPoly qs mt b).coeff i| ≤
        N * (W / (2 * mt)) * (W / (2 * mt)) := fun a b =>
      abs_coeff_mul_le_N _ _ _ _ (hlift a) (hlift b) i
    simp only [source_tensor_two, List.mem_cons, List.not_mem_nil, or_false] at hT
    rcases hT with rfl | rfl | rfl
    · linarith [hm a₀ b₀]
    · rw [coeff_add']
      have := abs_add_le ((smmrPoly qs mt a₀ * smmrPoly qs mt b₁).coeff i)
        ((smmrPoly qs mt a₁ * smmrPoly qs mt b₀).coeff i)
      linarith [hm a₀ b₁, hm a₁ b₀]
    · linarith [hm a₁ b₁]
  obtain ⟨h1, h2⟩ := floorVal_bounds t qs hposq hcopq (T.coeff i)
  exact floor_small t N qs.prod qs.length (qs.length - 1) R mt Bp hQ hmt
    hsize (T.coeff i) (W / (2 * mt)) (floorVal t qs (T.coeff i)) hMa0 (hW ▸ hMa) hb h1 h2

/-- `Challenge.BFVMul.behz_sk_alpha_ge`. -/
theorem behz_sk_alpha_ge' (t : ℕ) (qs bs : List ℕ) (msk mt : ℕ)
    (haux : behzAuxOK? t N qs bs msk mt = true) (hword : behzWordOK? t N qs bs msk mt = true)
    (c d : List (IntPoly N)) (hc : c.length = 2) (hd : d.length = 2) :
    ∀ x ∈ HPS.tensor (qs ++ (bs ++ [msk]))
        (c.map fun a => BEHZ.extend qs (bs ++ [msk]) mt (HPS.toLimbs qs a))
        (d.map fun a => BEHZ.extend qs (bs ++ [msk]) mt (HPS.toLimbs qs a)),
      ∀ (i : Fin N), ∀ q ∈ qs,
        -(q : ℤ) ≤ BEHZ.skAlpha1 bs msk
          (HPS.residues ((BEHZ.floorq t qs (bs ++ [msk]) x).take bs.length) i)
          (((BEHZ.floorq t qs (bs ++ [msk]) x).getD bs.length 0).coeff i) := by
  obtain ⟨hpos, hcop, hcmt, hmsk, hsize, -, hgcd, hmt, heven⟩ :=
    (behzAuxOK_iff t N qs bs msk mt).mp haux
  obtain ⟨-, -, -, hwq⟩ := (behzWordOK_iff t N qs bs msk mt).mp hword
  rw [List.append_assoc] at hpos hcop hcmt
  have hposq : ∀ q ∈ qs, 0 < q := fun q hq => hpos q (List.mem_append_left _ hq)
  have hposk : ∀ b ∈ bs ++ [msk], 0 < b := fun b hb => hpos b (List.mem_append_right _ hb)
  have hposb : ∀ b ∈ bs, 0 < b := fun b hb => hposk b (List.mem_append_left _ hb)
  have hmsk0 : 0 < msk := hposk msk (by simp)
  have hcopq : qs.Pairwise Nat.Coprime := (List.pairwise_append.mp hcop).1
  have hcopk : (bs ++ [msk]).Pairwise Nat.Coprime := (List.pairwise_append.mp hcop).2.1
  have hcopqk : ∀ q ∈ qs, ∀ b ∈ bs ++ [msk], Nat.Coprime q b :=
    (List.pairwise_append.mp hcop).2.2
  have hcopb : bs.Pairwise Nat.Coprime := (List.pairwise_append.mp hcopk).1
  have hcopbm : Nat.Coprime bs.prod msk :=
    prod_coprime msk bs fun b hb => (List.pairwise_append.mp hcopk).2.2 b hb msk (by simp)
  have hQmt : Nat.Coprime qs.prod mt := Nat.Coprime.symm hgcd
  obtain ⟨R, hR⟩ : ∃ R : ℕ, msk = R + 1 + 2 * bs.length := ⟨msk - 1 - 2 * bs.length, by omega⟩
  have hRsub : msk - 1 - 2 * bs.length = R := by omega
  rw [hRsub] at hsize
  have eR : ((msk : ℤ) - 1 - 2 * bs.length) = R := by rw [hR]; push_cast; ring
  obtain ⟨a₀, a₁, rfl⟩ := List.length_eq_two.mp hc
  obtain ⟨b₀, b₁, rfl⟩ := List.length_eq_two.mp hd
  intro x hx i q hq
  simp only [List.map_cons, List.map_nil,
    extend_toLimbs qs (bs ++ [msk]) mt hposq hcopq hmt hQmt
      (fun b hb => ⟨hposk b hb, hcmt b (List.mem_append_right _ hb)⟩),
    tensor_toLimbs] at hx
  obtain ⟨T, hT, rfl⟩ := List.mem_map.mp hx
  rw [floorq_toLimbs t qs (bs ++ [msk]) hposq hcopq
      (fun b hb => ⟨hposk b hb, fun q hq => hcopqk q hq b hb⟩)]
  set F := floorPoly t qs T with hFdef
  have e : toLimbs (bs ++ [msk]) F = toLimbs bs F ++ [modPoly msk F] := by
    simp [toLimbs_eq]
  have hl : (toLimbs bs F).length = bs.length := List.length_map _
  have hg : (toLimbs bs F ++ [modPoly msk F]).getD bs.length 0 = modPoly msk F := by
    rw [← hl]; simp
  rw [e, List.take_left' hl, hg, residues_toLimbs]
  show -(q : ℤ) ≤ skAlpha1 bs msk (bs.map fun b : ℕ => F.coeff i % b) (F.coeff i % msk)
  rw [skAlpha1_eq]
  have hF1 := floor_tensor_small t qs bs.prod R mt hposq hcopq hmt heven hQmt hsize
    a₀ a₁ b₀ b₁ T hT i
  have hF2 := floor_tensor_small t qs bs.prod (2 * q) mt hposq hcopq hmt heven hQmt (hwq q hq)
    a₀ a₁ b₀ b₁ T hT i
  have e2 : ((2 * q : ℕ) : ℤ) = 2 * (q : ℤ) := by push_cast; ring
  rw [e2] at hF2
  exact skAlpha_ge bs hposb hcopb msk hmsk0 hcopbm _ (eR ▸ hF1) q hF2

end FHE.BFV.MulBEHZ
