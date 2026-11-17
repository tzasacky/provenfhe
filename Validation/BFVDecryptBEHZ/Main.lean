import Validation.BFVDecryptBEHZ.Shoup
import Validation.BFVDecrypt
import Validation.BFVDecryptLow

/-!
# Validation.BFVDecryptBEHZ.Main — the BEHZ routine: exact up to `L/γ`, and under the margin
-/

namespace Validation.BFVDecryptBEHZ
open Spec Spec.DecryptBFV Spec.DecryptBFVLow Spec.DecryptBFVBEHZ Spec.Scheme NPoly
  Challenge.BFVDecryptBEHZ
open Validation.BFVDecryptLow (subFast_of_le addFast_of_lt mulFast_of_lt)

theorem paramsB {t : ℕ} {qs : List ℕ} (hp : behzParamsOK? t qs = true) :
    2 ≤ t ∧ t * gamma < 2 ^ 63 ∧ 1 ≤ qs.length ∧
      (∀ q ∈ qs, 3 ≤ q ∧ q % 2 = 1 ∧ q < 2 ^ 60 ∧ Nat.Coprime q t) ∧ qs.Pairwise Nat.Coprime := by
  simp only [behzParamsOK?, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hp
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := hp
  exact ⟨h1, h2, h3, fun q h => ⟨(h4 q h).1.1.1, (h4 q h).1.1.2, (h4 q h).1.2, (h4 q h).2⟩, h5⟩

theorem behzParamsOK?_t_lt (t : ℕ) (qs : List ℕ) (h : behzParamsOK? t qs = true) : t < 2 ^ 37 := by
  have := (paramsB h).2.1
  unfold gamma at this
  by_contra hc
  push Not at hc
  have : 2 ^ 37 * 2 ^ 26 ≤ t * 2 ^ 26 := Nat.mul_le_mul_right _ hc
  norm_num at this
  omega

/-- The accumulation loop is the sum modulo `m`. -/
theorem fold_modAdd (m : ℕ) (hm : m < 2 ^ 63) (f : ℕ → ℕ) :
    ∀ n, (∀ i < n, f i < m) → (List.range n).foldl (fun s i => modAddFastEq s (f i) m) 0 =
      ((List.range n).map f).sum % m
  | 0, _ => by simp
  | n + 1, hf' => by
    have hf : ∀ i < n, f i < m := fun i hi => hf' i (by omega)
    rw [List.range_succ, List.foldl_append, fold_modAdd m hm f n hf, List.foldl_cons,
      List.foldl_nil, List.map_append, List.sum_append, List.map_singleton, List.sum_singleton]
    have h2 := hf' n (by omega)
    set S := ((List.range n).map f).sum
    have h1 := Nat.mod_lt S (show 0 < m by omega)
    unfold modAddFastEq
    simp only
    rw [addFast_of_lt (by omega)]
    have e : (S + f n) % m = (S % m + f n) % m := by rw [Nat.add_mod, Nat.mod_eq_of_lt h2]
    rw [e]
    split_ifs with h
    · rw [subFast_of_le h (by omega), Nat.mod_eq_sub_mod h,
        Nat.mod_eq_of_lt (a := S % m + f n - m) (by omega)]
    · rw [Nat.mod_eq_of_lt (a := S % m + f n) (by omega)]

theorem range_map_getD (qs : List ℕ) (g : ℕ → ℕ) :
    (List.range qs.length).map (fun i => g (qs.getD i 0)) = qs.map g := by
  apply List.ext_getElem
  · simp
  intro i h1 h2
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa using h1)]

theorem coprime_mem {l : List ℕ} (hco : l.Pairwise Nat.Coprime) {a b : ℕ} (ha : a ∈ l)
    (hb : b ∈ l) (hne : a ≠ b) : Nat.Coprime a b :=
  Validation.BFVDecrypt.coprime_of_mem hco ha hb hne

/-- The CRT step: `S = Σ_q y_q·(Q/q) ≡ tγ·x (mod Q)` where `y_q ≡ x·tγ·(Q/q)⁻¹ (mod q)`. -/
theorem crt_behz (t : ℕ) (qs : List ℕ) (hq : ∀ q ∈ qs, 3 ≤ q) (hco : qs.Pairwise Nat.Coprime)
    (x : ℕ) :
    (qs.map fun q => x % q * tgammaQHatInvModq t qs q % q * (qs.prod / q)).sum ≡
      t * gamma * x [MOD qs.prod] := by
  have hnd := Validation.BFVDecrypt.nodup_of_coprime hco (fun q h => by have := hq q h; omega)
  have h := (Nat.modEq_list_map_prod_iff (s := id) (l := qs)
    (a := (qs.map fun q => x % q * tgammaQHatInvModq t qs q % q * (qs.prod / q)).sum)
    (b := t * gamma * x) (by exact hco)).mpr
  rw [List.map_id] at h
  apply h
  intro q0 hq0
  simp only [id]
  have hq03 := hq q0 hq0
  have hs := Validation.BFVDecrypt.sum_modEq_single
    (f := fun q => x % q * tgammaQHatInvModq t qs q % q * (qs.prod / q))
    (q0 := q0) qs hnd (by
      intro q hqm hne
      have hd := Validation.BFVDecrypt.dvd_prod_div hnd hq0 hqm (Ne.symm hne)
        (by have := hq q hqm; omega)
      exact (Nat.modEq_zero_iff_dvd.mpr (Dvd.dvd.mul_left hd _)))
  rw [ite_eq_left_iff.mpr (fun h => absurd hq0 h)] at hs
  refine hs.trans ?_
  have hcop : Nat.Coprime (qs.prod / q0) q0 := by
    have e : qs.prod / q0 = (qs.erase q0).prod := by
      rw [← List.prod_erase hq0, Nat.mul_div_cancel_left _ (by omega)]
    rw [e]
    apply Nat.Coprime.symm
    apply Nat.coprime_list_prod_right_iff.mpr
    intro b hb
    have hb' := List.mem_of_mem_erase hb
    have hne : b ≠ q0 := fun h => by
      subst h
      exact (List.Nodup.not_mem_erase hnd) hb
    exact coprime_mem hco hq0 hb' (Ne.symm hne)
  have : NeZero q0 := ⟨by omega⟩
  rw [← ZMod.natCast_eq_natCast_iff]
  unfold tgammaQHatInvModq invMod
  simp only [Nat.cast_mul, ZMod.natCast_mod, ZMod.natCast_zmod_val]
  have hu := ZMod.coe_mul_inv_eq_one _ hcop
  linear_combination ((x : ZMod q0) * (gamma : ZMod q0) * (t : ZMod q0)) * hu

/-- The final rounding `(s + (s & (γ − 1))) >> 26` is `⌊(2s + γ)/(2γ)⌋`. -/
theorem final_round (s : ℕ) (hs : s < 2 ^ 63) :
    rshift (addFast s (s &&& (gamma - 1))) 26 = (2 * s + gamma) / (2 * gamma) := by
  have hg : gamma = 2 ^ 26 := rfl
  have hm := Nat.mod_lt s (show 0 < 2 ^ 26 by norm_num)
  rw [hg, Nat.and_two_pow_sub_one_eq_mod, addFast_of_lt (by omega)]
  unfold rshift
  norm_num
  omega

/-- One word of the sum, in `ZMod (tγ)`, times `Q`. -/
theorem term_zmod (t : ℕ) (qs : List ℕ) (M : ℕ) (hM : M = t * gamma) (htg : 2 ≤ M)
    (htg' : M < 2 ^ 63) (q : ℕ) (hqm : q ∈ qs) (hq2 : q % 2 = 1) (hqt : Nat.Coprime q t) (x : ℕ) :
    (qs.prod : ZMod M) *
      (((x % q * tgammaQHatInvModq t qs q % q * negInvqModtgamma t q % M : ℕ)) : ZMod M) =
      -(((x % q * tgammaQHatInvModq t qs q % q * (qs.prod / q) : ℕ)) : ZMod M) := by
  have hTG : tgamma t = M := by rw [hM]; exact mulFast_of_lt (by omega)
  have hcop : Nat.Coprime q M := by
    rw [hM]
    apply Nat.Coprime.mul_right hqt
    unfold gamma
    exact Nat.Coprime.pow_right _ (Nat.coprime_two_right.mpr (by rw [Nat.odd_iff]; exact hq2))
  have hQ : qs.prod = q * (qs.prod / q) := (Nat.mul_div_cancel' (List.dvd_prod hqm)).symm
  have : NeZero M := ⟨by omega⟩
  unfold negInvqModtgamma invMod
  rw [hTG, subFast_of_le (by omega) (by omega)]
  simp only [Nat.cast_mul, ZMod.natCast_mod, ZMod.natCast_zmod_val]
  rw [Nat.cast_sub (by omega), ZMod.natCast_self, Nat.cast_one, zero_sub]
  conv_lhs => rw [hQ]
  push_cast
  have hu : (q : ZMod M) * (q : ZMod M)⁻¹ = 1 := ZMod.coe_mul_inv_eq_one q hcop
  linear_combination (-(((x % q * tgammaQHatInvModq t qs q % q : ℕ) : ZMod M)) *
    ((qs.prod / q : ℕ) : ZMod M)) * hu

/-- Sums of terms related termwise by `c·fᵢ = −gᵢ` in `ZMod M`. -/
theorem sum_zmod (M : ℕ) (c : ZMod M) (f g : ℕ → ℕ) : ∀ l : List ℕ,
    (∀ q ∈ l, c * (f q : ZMod M) = -(g q : ZMod M)) →
    c * (((l.map f).sum : ℕ) : ZMod M) = -(((l.map g).sum : ℕ) : ZMod M)
  | [], _ => by simp
  | q :: l, hl => by
    have ih := sum_zmod M c f g l (fun r hr => hl r (List.mem_cons_of_mem _ hr))
    simp only [List.map_cons, List.sum_cons, Nat.cast_add, mul_add, neg_add]
    rw [ih, hl q List.mem_cons_self]

theorem sum_lt_len_mul {α : Type} (f : α → ℕ) (Q : ℕ) :
    ∀ l : List α, l ≠ [] → (∀ a ∈ l, f a < Q) → (l.map f).sum < l.length * Q
  | [], h, _ => absurd rfl h
  | [a], _, hf => by simpa using hf a List.mem_cons_self
  | a :: b :: l, _, hf => by
    have ih := sum_lt_len_mul f Q (b :: l) (List.cons_ne_nil _ _)
      (fun c hc => hf c (List.mem_cons_of_mem _ hc))
    have ha := hf a List.mem_cons_self
    simp only [List.map_cons, List.sum_cons, List.length_cons] at ih ⊢
    nlinarith

/-- The rounding by `γ` under the margin, isolated. -/
theorem round_gamma (Q G L h k D S X : ℤ) (hQ : 0 < Q) (hG : 0 < G) (hS0 : 0 ≤ S) (hSL : S < L * Q)
    (hQh : Q * h = X - S) (hX : X = G * (Q * k) + G * D)
    (hk : 2 * G * |D| + 2 * L * Q < G * Q) : (2 * h + G) / (2 * G) = k := by
  have hGD : G * D ≤ G * |D| := mul_le_mul_of_nonneg_left (le_abs_self D) hG.le
  have hGD' : -(G * |D|) ≤ G * D := by
    have := mul_le_mul_of_nonneg_left (neg_abs_le D) hG.le; linarith
  have hL0 : 0 ≤ L * Q := le_trans hS0 hSL.le
  have e1 : Q * (2 * h + G) = 2 * (G * (Q * k)) + 2 * (G * D) - 2 * S + G * Q := by
    rw [mul_add, show Q * (2 * h) = 2 * (Q * h) by ring, hQh, hX]; ring
  have e2 : Q * ((k + 1) * (2 * G)) = 2 * (G * (Q * k)) + 2 * (G * Q) := by ring
  have e3 : Q * (k * (2 * G)) = 2 * (G * (Q * k)) := by ring
  have hup : 2 * h + G < (k + 1) * (2 * G) := by
    have : Q * (2 * h + G) < Q * ((k + 1) * (2 * G)) := by rw [e1, e2]; linarith
    exact lt_of_mul_lt_mul_left this hQ.le
  have hlo : k * (2 * G) ≤ 2 * h + G := by
    have : Q * (k * (2 * G)) < Q * (2 * h + G) := by rw [e1, e3]; linarith
    exact (lt_of_mul_lt_mul_left this hQ.le).le
  have h2G : (0 : ℤ) < 2 * G := by linarith
  apply le_antisymm
  · have := (Int.ediv_lt_iff_lt_mul h2G).mpr hup; omega
  · exact (Int.le_ediv_iff_mul_le h2G).mpr hlo

theorem behz1_exact (t : ℕ) (qs : List ℕ) (hp : behzParamsOK? t qs = true) (x : ℕ)
    (hx : x < qs.prod) (k : ℤ)
    (hk : 2 * gamma * |(t : ℤ) * x - qs.prod * k| + 2 * qs.length * qs.prod < gamma * qs.prod) :
    ((behz1 t qs (residues qs x) : ℕ) : ZMod t) = (k : ZMod t) ∧ behz1 t qs (residues qs x) ≤ t := by
  obtain ⟨ht, htg, hL, hq, hco⟩ := paramsB hp
  have hg : gamma = 2 ^ 26 := rfl
  obtain ⟨tg, htgd⟩ : ∃ tg, tg = t * gamma := ⟨_, rfl⟩
  have htg2 : 2 ≤ tg := by rw [htgd, hg]; nlinarith
  have hTG : tgamma t = tg := by rw [htgd]; exact mulFast_of_lt (by omega)
  set Q := qs.prod with hQd
  have hQ : 0 < Q := List.prod_pos fun q h => by have := (hq q h).1; omega
  -- the words
  set g : ℕ → ℕ := fun q => x % q * tgammaQHatInvModq t qs q % q * negInvqModtgamma t q % tg
    with hgd
  have hlen : (residues qs x).length = qs.length := by unfold residues; simp
  have hfold : (List.range (residues qs x).length).foldl (fun s i =>
      modAddFastEq s (modMulFastConst (modMulFastConst ((residues qs x).getD i 0)
        (tgammaQHatInvModq t qs (qs.getD i 0)) (qs.getD i 0)
        (prepModMulConst (tgammaQHatInvModq t qs (qs.getD i 0)) (qs.getD i 0)))
        (negInvqModtgamma t (qs.getD i 0)) (tgamma t)
        (prepModMulConst (negInvqModtgamma t (qs.getD i 0)) (tgamma t))) (tgamma t)) 0 =
      (qs.map g).sum % tg := by
    rw [hlen, hTG]
    have hfi : ∀ i < qs.length,
        modMulFastConst (modMulFastConst ((residues qs x).getD i 0)
          (tgammaQHatInvModq t qs (qs.getD i 0)) (qs.getD i 0)
          (prepModMulConst (tgammaQHatInvModq t qs (qs.getD i 0)) (qs.getD i 0)))
          (negInvqModtgamma t (qs.getD i 0)) tg
          (prepModMulConst (negInvqModtgamma t (qs.getD i 0)) tg) = g (qs.getD i 0) := by
      intro i hi
      have hgi : qs.getD i 0 = qs[i] := by simp [List.getD_eq_getElem?_getD, hi]
      have hxi : (residues qs x).getD i 0 = x % qs[i] := by
        unfold residues; simp [List.getD_eq_getElem?_getD, hi]
      rw [hxi, hgi]
      obtain ⟨hq3, _, hq60, _⟩ := hq qs[i] (List.getElem_mem hi)
      have hb1 : tgammaQHatInvModq t qs qs[i] < qs[i] := by
        unfold tgammaQHatInvModq; exact Nat.mod_lt _ (by omega)
      rw [modMulFastConst_spec _ _ _ (by have := Nat.mod_lt x (show 0 < qs[i] by omega); omega)
        hb1 (by omega) (by omega)]
      have hb2 : negInvqModtgamma t qs[i] < tg := by
        unfold negInvqModtgamma; rw [hTG]; exact Nat.mod_lt _ (by omega)
      have hy := Nat.mod_lt (x % qs[i] * tgammaQHatInvModq t qs qs[i]) (show 0 < qs[i] by omega)
      rw [modMulFastConst_spec _ _ _ (by omega) hb2 htg2 (by omega)]
    have hF := fold_modAdd tg (by omega) (fun i => modMulFastConst (modMulFastConst
        ((residues qs x).getD i 0) (tgammaQHatInvModq t qs (qs.getD i 0)) (qs.getD i 0)
        (prepModMulConst (tgammaQHatInvModq t qs (qs.getD i 0)) (qs.getD i 0)))
        (negInvqModtgamma t (qs.getD i 0)) tg
        (prepModMulConst (negInvqModtgamma t (qs.getD i 0)) tg)) qs.length
      (fun i hi => by rw [hfi i hi]; exact Nat.mod_lt _ (by omega))
    refine hF.trans ?_
    have hm : (List.range qs.length).map (fun i => modMulFastConst (modMulFastConst
        ((residues qs x).getD i 0) (tgammaQHatInvModq t qs (qs.getD i 0)) (qs.getD i 0)
        (prepModMulConst (tgammaQHatInvModq t qs (qs.getD i 0)) (qs.getD i 0)))
        (negInvqModtgamma t (qs.getD i 0)) tg
        (prepModMulConst (negInvqModtgamma t (qs.getD i 0)) tg)) =
        (List.range qs.length).map (fun i => g (qs.getD i 0)) :=
      List.map_congr_left (fun i hi => hfi i (List.mem_range.mp hi))
    rw [hm, range_map_getD qs g]
  have hb : behz1 t qs (residues qs x) =
      rshift (addFast ((qs.map g).sum % tg) (((qs.map g).sum % tg) &&& (gamma - 1))) 26 := by
    unfold behz1
    simp only
    rw [hfold]
  set sN := (qs.map g).sum % tg with hsNd
  have hsN : sN < tg := Nat.mod_lt _ (by omega)
  rw [hb, final_round sN (by omega)]
  -- the CRT sum
  set S := (qs.map fun q => x % q * tgammaQHatInvModq t qs q % q * (qs.prod / q)).sum with hSd
  have hcrt := crt_behz t qs (fun q h => (hq q h).1) hco x
  obtain ⟨h, hh⟩ := (Nat.modEq_iff_dvd.mp hcrt)
  have hS : S < qs.length * Q := by
    have := sum_lt_len_mul (fun q => x % q * tgammaQHatInvModq t qs q % q * (qs.prod / q)) Q qs
      (List.ne_nil_of_length_pos hL) (fun q hqm => by
        have hq3 := (hq q hqm).1
        have h1 := Nat.mod_lt (x % q * tgammaQHatInvModq t qs q) (show 0 < q by omega)
        have hQq : q * (Q / q) = Q := Nat.mul_div_cancel' (List.dvd_prod hqm)
        have hpos : 0 < Q / q := Nat.pos_of_ne_zero (by intro h0; rw [h0] at hQq; omega)
        calc x % q * tgammaQHatInvModq t qs q % q * (qs.prod / q) < q * (Q / q) :=
              Nat.mul_lt_mul_of_pos_right h1 hpos
          _ = Q := hQq)
    exact this
  -- in `ZMod (tγ)`: `Q·sN = −S = Q·h`
  have : NeZero tg := ⟨by omega⟩
  have hcopQ : Nat.Coprime Q tg := by
    rw [hQd]
    apply Nat.coprime_list_prod_left_iff.mpr
    intro q hqm
    rw [htgd]
    apply Nat.Coprime.mul_right (hq q hqm).2.2.2
    rw [hg]
    exact Nat.Coprime.pow_right _ (Nat.coprime_two_right.mpr (by
      rw [Nat.odd_iff]; exact (hq q hqm).2.1))
  have hzm := sum_zmod tg (Q : ZMod tg) g
    (fun q => x % q * tgammaQHatInvModq t qs q % q * (qs.prod / q)) qs
    (fun q hqm => term_zmod t qs tg htgd htg2 (by omega) q hqm (hq q hqm).2.1 (hq q hqm).2.2.2 x)
  have hh' : ((t * gamma * x : ℕ) : ℤ) - (S : ℤ) = (Q : ℤ) * h := hh
  have hQh : (Q : ZMod tg) * ((h : ℤ) : ZMod tg) = -((S : ℕ) : ZMod tg) := by
    have e := congrArg (Int.cast : ℤ → ZMod tg) hh'
    simp only [Int.cast_sub, Int.cast_mul, Int.cast_natCast] at e
    have h0 : ((t * gamma * x : ℕ) : ZMod tg) = 0 := by
      rw [Nat.cast_mul, ← htgd, ZMod.natCast_self, zero_mul]
    rw [h0, zero_sub] at e
    rw [← e]
  have hsh : ((sN : ℤ) : ZMod tg) = ((h : ℤ) : ZMod tg) := by
    have hu : IsUnit (Q : ZMod tg) := (ZMod.unitOfCoprime Q hcopQ).isUnit
    apply hu.mul_left_cancel
    rw [Int.cast_natCast, hsNd, ZMod.natCast_mod, hzm, hQh]
  obtain ⟨n, hn⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp hsh
  -- the rounding of `h` by `γ`
  have hQ0 : (0 : ℤ) < Q := by exact_mod_cast hQ
  have hG : (gamma : ℤ) = 2 ^ 26 := by rw [hg]; norm_num
  have hG0 : (0 : ℤ) < gamma := by rw [hG]; norm_num
  set D : ℤ := (t : ℤ) * x - Q * k with hD
  have hS0 : (0 : ℤ) ≤ S := by positivity
  have hSL : (S : ℤ) < qs.length * Q := by exact_mod_cast hS
  have hhQ : (Q : ℤ) * h = t * gamma * x - S := by
    rw [Nat.cast_mul, Nat.cast_mul] at hh'; linarith
  have hk' : 2 * (gamma : ℤ) * |D| + 2 * qs.length * Q < gamma * Q := hk
  have hround : (2 * h + gamma) / (2 * gamma) = k :=
    round_gamma Q gamma qs.length h k D S (t * gamma * x) hQ0 hG0 hS0 hSL hhQ (by rw [hD]; ring) hk'
  -- `out = (2·sN + γ)/(2γ) = k + t·(−n)`
  have htgI : (tg : ℤ) = t * gamma := by rw [htgd]; push_cast; ring
  have hsN' : (sN : ℤ) = h + t * gamma * (-n) := by
    have : (h : ℤ) - sN = tg * n := by
      linarith [hn]
    rw [htgI] at this; linarith
  have hout : (((2 * sN + gamma) / (2 * gamma) : ℕ) : ℤ) = k + t * (-n) := by
    rw [Int.natCast_div]
    push_cast
    rw [hsN', show 2 * (h + t * gamma * -n) + (gamma : ℤ) = (2 * h + gamma) + (2 * gamma) * (t * -n) by
      ring, Int.add_mul_ediv_left _ _ (by omega), hround]
  constructor
  · rw [show (((2 * sN + gamma) / (2 * gamma) : ℕ) : ZMod t) =
        ((((2 * sN + gamma) / (2 * gamma) : ℕ) : ℤ) : ZMod t) from (Int.cast_natCast _).symm, hout]
    push_cast
    simp
  · have hs : sN < t * gamma := htgd ▸ hsN
    have e : 2 * gamma * (t + 1) = 2 * (t * gamma) + 2 * gamma := by ring
    have h1 : 2 * sN + gamma < (t + 1) * (2 * gamma) := by rw [mul_comm (t + 1), e]; omega
    have h2 : (2 * sN + gamma) / (2 * gamma) < t + 1 :=
      (Nat.div_lt_iff_lt_mul (by unfold gamma; norm_num)).mpr h1
    omega


/-- The invariant noise of a phase within `B` of `⌊Q/t⌋·m`. -/
theorem noise_int (t Q B x m : ℕ) (ht : 1 ≤ t) (hQ : 0 < Q) (hm : m < t)
    (hnoise : (((x : ℤ) - (Q / t * m : ℕ) : ℤ) : ZMod Q).valMinAbs.natAbs ≤ B) :
    ∃ j : ℤ, |(t : ℤ) * x - Q * (m + t * j)| ≤ (t * B + Q % t * (t - 1) : ℕ) := by
  haveI : NeZero Q := ⟨hQ.ne'⟩
  set e0 := (((x : ℤ) - (Q / t * m : ℕ) : ℤ) : ZMod Q).valMinAbs with he0
  have hcast : ((e0 : ℤ) : ZMod Q) = (((x : ℤ) - (Q / t * m : ℕ) : ℤ) : ZMod Q) :=
    ZMod.coe_valMinAbs _
  obtain ⟨j, hj⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp hcast
  have hdiv : (Q : ℤ) = t * (Q / t : ℕ) + (Q % t : ℕ) := by
    exact_mod_cast (Nat.div_add_mod Q t).symm
  refine ⟨j, ?_⟩
  have htx : (t : ℤ) * x - Q * (m + t * j) = (t : ℤ) * e0 - (Q % t : ℕ) * m := by
    have : (x : ℤ) = (Q / t * m : ℕ) + e0 + Q * j := by linarith
    rw [this, Nat.cast_mul]
    have : (t : ℤ) * (Q / t : ℕ) = Q - (Q % t : ℕ) := by rw [hdiv]; ring
    linear_combination (m : ℤ) * this
  rw [htx]
  have he : |e0| ≤ B := by
    have : (e0.natAbs : ℤ) ≤ B := by exact_mod_cast hnoise
    rwa [Int.natCast_natAbs] at this
  have hmt : (m : ℤ) ≤ t - 1 := by omega
  calc |(t : ℤ) * e0 - (Q % t : ℕ) * m| ≤ |(t : ℤ) * e0| + |((Q % t : ℕ) : ℤ) * m| := abs_sub _ _
    _ = t * |e0| + (Q % t : ℕ) * m := by
        rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : (0 : ℤ) ≤ t),
          abs_of_nonneg (by positivity : (0 : ℤ) ≤ (Q % t : ℕ)),
          abs_of_nonneg (by positivity : (0 : ℤ) ≤ m)]
    _ ≤ t * B + (Q % t : ℕ) * (t - 1) := by
        have := mul_le_mul_of_nonneg_left he (by positivity : (0 : ℤ) ≤ t)
        have := mul_le_mul_of_nonneg_left hmt (by positivity : (0 : ℤ) ≤ (Q % t : ℕ))
        linarith
    _ = ((t * B + Q % t * (t - 1) : ℕ) : ℤ) := by
        push_cast [Nat.cast_sub (show 1 ≤ t by omega)]; ring

theorem behz1_correct (t : ℕ) (qs : List ℕ) (hp : behzParamsOK? t qs = true) (B : ℕ)
    (hB : decBEHZOK? t qs B = true) (x m : ℕ) (hm : m < t) (hx : x < qs.prod)
    (hnoise : (((x : ℤ) - (qs.prod / t * m : ℕ) : ℤ) : ZMod qs.prod).valMinAbs.natAbs ≤ B) :
    ((behz1 t qs (residues qs x) : ℕ) : ZMod t) = (m : ZMod t) ∧ behz1 t qs (residues qs x) ≤ t := by
  obtain ⟨ht, _, _, hq, _⟩ := paramsB hp
  have hQ : 0 < qs.prod := List.prod_pos fun q h => by have := (hq q h).1; omega
  obtain ⟨j, hj⟩ := noise_int t qs.prod B x m (by omega) hQ hm hnoise
  have hB' : 2 * gamma * (t * B + qs.prod % t * (t - 1)) + 2 * qs.length * qs.prod <
      gamma * qs.prod := by simpa [decBEHZOK?] using hB
  have hk : 2 * (gamma : ℤ) * |(t : ℤ) * x - qs.prod * (m + t * j)| +
      2 * qs.length * qs.prod < gamma * qs.prod := by
    have hG : (0 : ℤ) ≤ gamma := by positivity
    have := mul_le_mul_of_nonneg_left hj (show (0 : ℤ) ≤ 2 * gamma by positivity)
    have hB'' : ((2 * gamma * (t * B + qs.prod % t * (t - 1)) + 2 * qs.length * qs.prod : ℕ) : ℤ) <
      ((gamma * qs.prod : ℕ) : ℤ) := by exact_mod_cast hB'
    push_cast at hB'' this ⊢
    linarith
  obtain ⟨h1, h2⟩ := behz1_exact t qs hp x hx (m + t * j) hk
  refine ⟨?_, h2⟩
  rw [h1]; push_cast; simp

theorem bfvDecryptBEHZ_correct (t : ℕ) (qs : List ℕ) (hp : behzParamsOK? t qs = true) {N : ℕ}
    (s : IntPoly N) (ct : List (Poly qs.prod N)) (m : Poly t N) (B : ℕ)
    (hnoise : normInf (centered (phase (ofInt qs.prod s) ct -
      ofInt qs.prod ⟨fun i => ((qs.prod / t * (m.coeff i).val : ℕ) : ℤ)⟩)) ≤ B)
    (hB : decBEHZOK? t qs B = true) (i : Fin N) :
    (((bfvDecryptBEHZ t qs s ct).coeff i : ℕ) : ZMod t) = m.coeff i ∧
      (bfvDecryptBEHZ t qs s ct).coeff i ≤ t := by
  obtain ⟨ht2, _, _, hq, _⟩ := paramsB hp
  have hQ : 0 < qs.prod := List.prod_pos fun q h => by have := (hq q h).1; omega
  haveI : NeZero qs.prod := ⟨hQ.ne'⟩
  haveI : NeZero t := ⟨by omega⟩
  set x := ((phase (ofInt qs.prod s) ct).coeff i).val with hxd
  have hx : x < qs.prod := ZMod.val_lt _
  have hm : (m.coeff i).val < t := ZMod.val_lt _
  set D : Poly qs.prod N := phase (ofInt qs.prod s) ct -
      ofInt qs.prod ⟨fun i => ((qs.prod / t * (m.coeff i).val : ℕ) : ℤ)⟩ with hD
  have hco := Validation.Scheme.abs_coeff_le_normInf (centered D) i
  have hn : (((x : ℤ) - (qs.prod / t * (m.coeff i).val : ℕ) : ℤ) : ZMod qs.prod).valMinAbs.natAbs
      ≤ B := by
    have e : (((x : ℤ) - (qs.prod / t * (m.coeff i).val : ℕ) : ℤ) : ZMod qs.prod) = D.coeff i := by
      show _ = (phase (ofInt qs.prod s) ct).coeff i - (((qs.prod / t * (m.coeff i).val : ℕ) : ℤ) :
        ZMod qs.prod)
      rw [Int.cast_sub, Int.cast_natCast, hxd, ZMod.natCast_zmod_val]
    rw [e]
    have h3 : |(D.coeff i).valMinAbs| ≤ (B : ℤ) := hco.trans (by exact_mod_cast hnoise)
    rw [Int.abs_eq_natAbs] at h3
    exact_mod_cast h3
  obtain ⟨h1, h2⟩ := behz1_correct t qs hp B hB x (m.coeff i).val hm hx hn
  refine ⟨?_, h2⟩
  have e : (bfvDecryptBEHZ t qs s ct).coeff i = behz1 t qs (residues qs x) := rfl
  rw [e, h1, ZMod.natCast_zmod_val]

theorem behzMargin_needed :
    behzParamsOK? 2 qsPinB = true ∧
      Challenge.BFV.decOK 2 qsPinB.prod ((qsPinB.prod / 2 - qsPinB.prod % 2) / 2 - 1) = true ∧
      roundDiv (2 * -(((qsPinB.prod / 2 - qsPinB.prod % 2) / 2 - 1 : ℕ) : ℤ)) qsPinB.prod = 0 ∧
      behz1 2 qsPinB (residues qsPinB
        (qsPinB.prod - ((qsPinB.prod / 2 - qsPinB.prod % 2) / 2 - 1))) = 1 ∧
      decBEHZOK? 2 qsPinB ((qsPinB.prod / 2 - qsPinB.prod % 2) / 2 - 1) = false := by
  decide +kernel

end Validation.BFVDecryptBEHZ
