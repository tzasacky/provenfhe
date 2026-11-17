import Validation.BFVDecryptLow.Words

/-!
# Validation.BFVDecryptLow.Drop — the drops: exact, and their noise
-/

namespace Validation.BFVDecryptLow
open Spec.DecryptBFV Spec.DecryptBFVLow Challenge.BFVDecryptLow

theorem paramsLow {t : ℕ} {qs : List ℕ} {ℓ : ℕ} (hp : decLowParamsOK? t qs ℓ = true) :
    2 ≤ t ∧ 1 ≤ ℓ ∧ ℓ ≤ qs.length ∧ (∀ q ∈ qs, 3 ≤ q ∧ q % 2 = 1 ∧ q < 2 ^ 60) ∧
      qs.Pairwise Nat.Coprime ∧ 2 * t < qs.headD 0 := by
  simp only [decLowParamsOK?, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hp
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := hp
  exact ⟨h1, h2, h3, fun q h => ⟨(h4 q h).1.1, (h4 q h).1.2, (h4 q h).2⟩, h5, h6⟩

/-- `|centredOf q w| ≤ q/2` for `w < q`. -/
theorem centredOf_abs {q w : ℕ} (hw : w < q) : |centredOf q w| ≤ (q / 2 : ℕ) := by
  unfold centredOf
  split_ifs with h
  · rw [abs_of_neg (by omega)]; omega
  · rw [abs_of_nonneg (by omega)]; omega

/-- `centredOf q (X mod q) ≡ X (mod q)`. -/
theorem centredOf_dvd (q : ℕ) (hq : 0 < q) (X : ℤ) :
    (q : ℤ) ∣ X - centredOf q (X % (q : ℤ)).toNat := by
  have h0 : 0 ≤ X % (q : ℤ) := Int.emod_nonneg _ (by omega)
  have hc : ((X % (q : ℤ)).toNat : ℤ) = X % q := Int.toNat_of_nonneg h0
  unfold centredOf
  split_ifs with h
  · rw [hc]
    exact ⟨X / q + 1, by have := Int.emod_add_ediv_mul X q; linarith⟩
  · rw [hc]
    exact ⟨X / q, by have := Int.emod_add_ediv_mul X q; linarith⟩

theorem toNat_emod_lt {X : ℤ} {q : ℕ} (hq : 0 < q) : (X % (q : ℤ)).toNat < q := by
  have h0 : 0 ≤ X % (q : ℤ) := Int.emod_nonneg _ (by omega)
  have h1 : X % (q : ℤ) < q := Int.emod_lt_of_pos _ (by omega)
  omega

/-! ### Lists -/

theorem residuesZ_def (qs : List ℕ) (X : ℤ) :
    residuesZ qs X = qs.map fun q : ℕ => (X % (q : ℤ)).toNat := rfl

theorem residuesZ_length (qs : List ℕ) (X : ℤ) : (residuesZ qs X).length = qs.length := by
  rw [residuesZ_def, List.length_map]

theorem scaleDown_nil (X : ℤ) : scaleDown [] X = X := rfl

theorem take_succ_eq {qs : List ℕ} {n : ℕ} (hn : n < qs.length) :
    qs.take (n + 1) = qs.take n ++ [qs[n]] := by
  rw [List.take_add_one, List.getElem?_eq_getElem hn]; rfl

theorem residuesZ_take_succ {qs : List ℕ} {n : ℕ} (hn : n < qs.length) (Y : ℤ) :
    residuesZ (qs.take (n + 1)) Y = residuesZ (qs.take n) Y ++ [(Y % (qs[n] : ℤ)).toNat] := by
  rw [residuesZ_def, residuesZ_def, take_succ_eq hn, List.map_append]; rfl

theorem dropRev_succ {qs : List ℕ} {n : ℕ} (hn : n < qs.length) (h1 : 1 ≤ n) :
    ((qs.take (n + 1)).drop 1).reverse = qs[n] :: ((qs.take n).drop 1).reverse := by
  rw [take_succ_eq hn, List.drop_append_of_le_length (by simp; omega), List.reverse_append]
  rfl

/-- One step of the loop of `dropAll`. -/
theorem dropAll_step (qs xs : List ℕ) (h2 : 2 ≤ xs.length) (hL : xs.length ≤ qs.length) :
    dropAll qs xs = dropAll qs (dropLastElementAndScale qs (qs.length - xs.length) xs) := by
  have hlen : (dropLastElementAndScale qs (qs.length - xs.length) xs).length = xs.length - 1 := by
    unfold dropLastElementAndScale; simp
  unfold dropAll
  rw [hlen]
  obtain ⟨m, hm⟩ : ∃ m, xs.length - 1 = m + 1 := ⟨xs.length - 2, by omega⟩
  rw [hm, show m + 1 - 1 = m by omega, List.range_succ_eq_map, List.foldl_cons,
    List.foldl_map]
  congr 1
  funext ys l
  congr 1
  omega

/-- One drop: the residues of `Y` on `n + 1` limbs become those of `(Y − [Y]_{qₙ})/qₙ` on `n`. -/
theorem drop_one (qs : List ℕ) (hq : ∀ q ∈ qs, 3 ≤ q ∧ q < 2 ^ 60) (hco : qs.Pairwise Nat.Coprime)
    (n : ℕ) (hn : n < qs.length) (h1 : 1 ≤ n) (Y : ℤ) :
    dropLastElementAndScale qs (qs.length - (n + 1)) (residuesZ (qs.take (n + 1)) Y) =
      residuesZ (qs.take n) ((Y - centredOf qs[n] (Y % (qs[n] : ℤ)).toNat) / qs[n]) := by
  have hqn := hq qs[n] (List.getElem_mem hn)
  have hlen : (residuesZ (qs.take (n + 1)) Y).length = n + 1 := by
    rw [residuesZ_length]; simp; omega
  rw [residuesZ_take_succ hn]
  unfold dropLastElementAndScale
  simp only [List.length_append, List.length_singleton, List.dropLast_concat,
    List.getLastD_concat]
  have hlen2 : (residuesZ (qs.take n) Y).length = n := by rw [residuesZ_length]; simp; omega
  rw [hlen2, show n + 1 - 1 = n by omega]
  have hgd : qs.getD n 0 = qs[n] := by simp [List.getD_eq_getElem?_getD, hn]
  rw [hgd]
  set ql := qs[n] with hql
  set c := centredOf ql (Y % (ql : ℤ)).toNat
  apply List.ext_getElem
  · simp only [List.length_mapIdx, residuesZ_length]
  intro i hi1 hi2
  rw [List.getElem_mapIdx]
  simp only [residuesZ_def, List.getElem_map, List.getElem_take]
  have hi : i < n := by simp only [List.length_mapIdx, residuesZ_length] at hi1; simp at hi1; omega
  have hin : i < qs.length := by omega
  have hgi : qs.getD i 0 = qs[i] := by simp [List.getD_eq_getElem?_getD, hin]
  rw [hgi]
  set qi := qs[i] with hqi
  have hqi' := hq qi (List.getElem_mem hin)
  have hcop : Nat.Coprime ql qi := by
    have := List.pairwise_iff_getElem.mp hco i n hin hn hi
    exact this.symm
  -- the switched last residue
  have hlast : (Y % (ql : ℤ)).toNat < ql := toNat_emod_lt (by omega)
  obtain ⟨hsw, hswlt⟩ := switchModulus_spec ql qi (Y % (ql : ℤ)).toNat (by omega) (by omega)
    (by omega) (by omega) (Or.inl hlast)
  have hxi : (Y % (qi : ℤ)).toNat < qi := toNat_emod_lt (by omega)
  -- the inverse
  have hinv : qlInvModq qs (qs.length - (n + 1)) i = ((ql : ZMod qi)⁻¹).val := by
    unfold qlInvModq invMod
    rw [show qs.length - (qs.length - (n + 1) + 1) = n by omega, hgi]
    simp [List.getD_eq_getElem?_getD, hn, hql]
  rw [hinv]
  have : NeZero qi := ⟨by omega⟩
  set sw := switchModulus ql qi (Y % (ql : ℤ)).toNat
  set Z := (Y - c) / (ql : ℤ)
  have hZ : (ql : ℤ) * Z = Y - c := Int.mul_ediv_cancel' (centredOf_dvd ql (by omega) Y)
  have hlt : ((Y % (qi : ℤ)).toNat + (qi - sw)) % qi * ((ql : ZMod qi)⁻¹).val % qi < qi :=
    Nat.mod_lt _ (by omega)
  have key : ((((Y % (qi : ℤ)).toNat + (qi - sw)) % qi * ((ql : ZMod qi)⁻¹).val % qi : ℕ) :
      ZMod qi) = ((Z : ℤ) : ZMod qi) := by
    rw [ZMod.natCast_mod, Nat.cast_mul, ZMod.natCast_mod, Nat.cast_add, Nat.cast_sub hswlt.le,
      ZMod.natCast_self, ZMod.natCast_zmod_val]
    have h1 : (((Y % (qi : ℤ)).toNat : ℕ) : ZMod qi) = ((Y : ℤ) : ZMod qi) := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg (Int.emod_nonneg _ (by omega)),
        ZMod.intCast_mod]
    have h2 : ((sw : ℕ) : ZMod qi) = ((c : ℤ) : ZMod qi) := by
      rw [← Int.cast_natCast, hsw, ZMod.intCast_mod]
    rw [h1, h2, zero_sub, ← sub_eq_add_neg]
    have h3 : ((Y : ℤ) : ZMod qi) - ((c : ℤ) : ZMod qi) = (ql : ZMod qi) * ((Z : ℤ) : ZMod qi) := by
      rw [← Int.cast_sub, ← hZ, Int.cast_mul, Int.cast_natCast]
    rw [h3, mul_comm, ← mul_assoc, mul_comm _ (ql : ZMod qi), ZMod.coe_mul_inv_eq_one ql hcop, one_mul]
  have hv := ZMod.val_intCast (n := qi) Z
  rw [← key, ZMod.val_natCast, Nat.mod_eq_of_lt hlt] at hv
  omega

end Validation.BFVDecryptLow

namespace Validation.BFVDecryptLow
open Spec.DecryptBFV Spec.DecryptBFVLow Challenge.BFVDecryptLow

theorem dropAll_res (qs : List ℕ) (hq : ∀ q ∈ qs, 3 ≤ q ∧ q < 2 ^ 60)
    (hco : qs.Pairwise Nat.Coprime) :
    ∀ n, 1 ≤ n → n ≤ qs.length → ∀ Y : ℤ, dropAll qs (residuesZ (qs.take n) Y) =
      [(scaleDown ((qs.take n).drop 1).reverse Y % (qs.headD 0 : ℤ)).toNat]
  | 0, h, _, _ => absurd h (by omega)
  | 1, _, hL, Y => by
    obtain ⟨a, l, rfl⟩ : ∃ a l, qs = a :: l := by
      cases qs with
      | nil => simp at hL
      | cons a l => exact ⟨a, l, rfl⟩
    rfl
  | n + 2, _, hL, Y => by
    have hlen : (residuesZ (qs.take (n + 2)) Y).length = n + 2 := by
      rw [residuesZ_length]; simp; omega
    rw [dropAll_step qs _ (by omega) (by omega), hlen,
      drop_one qs hq hco (n + 1) (by omega) (by omega) Y,
      dropAll_res qs hq hco (n + 1) (by omega) (by omega),
      dropRev_succ (n := n + 1) (by omega) (by omega)]
    rfl

theorem decBoundRev_succ (t q : ℕ) (l : List ℕ) (hl : l ≠ []) (V : ℕ) :
    Spec.Decrypt.decBoundRev t (q :: l) V = Spec.Decrypt.decBoundRev t l ((V + t * (q / 2)) / q) := by
  obtain ⟨a, r, rfl⟩ := List.exists_cons_of_ne_nil hl
  rfl

theorem noise_res (t : ℕ) (qs : List ℕ) (hq : ∀ q ∈ qs, 3 ≤ q ∧ q < 2 ^ 60) :
    ∀ n, 1 ≤ n → n ≤ qs.length → ∀ (X k v : ℤ) (V : ℕ),
      (t : ℤ) * X = ((qs.take n).prod : ℤ) * k + v → |v| ≤ V →
      ∃ v' : ℤ, (t : ℤ) * scaleDown ((qs.take n).drop 1).reverse X = (qs.headD 0 : ℤ) * k + v' ∧
        |v'| ≤ Spec.Decrypt.decBoundRev t (qs.take n).reverse V
  | 0, h, _, _, _, _, _, _, _ => absurd h (by omega)
  | 1, _, hL, X, k, v, V, h, hv => by
    obtain ⟨a, l, rfl⟩ : ∃ a l, qs = a :: l := by
      cases qs with
      | nil => simp at hL
      | cons a l => exact ⟨a, l, rfl⟩
    refine ⟨v, ?_, hv⟩
    show (t : ℤ) * scaleDown [] X = (a : ℤ) * k + v
    rw [scaleDown_nil]; simpa using h
  | n + 2, _, hL, X, k, v, V, h, hv => by
    have hn : n + 1 < qs.length := by omega
    set q := qs[n + 1] with hqd
    have hq3 := (hq q (List.getElem_mem hn)).1
    set c := centredOf q (X % (q : ℤ)).toNat with hc
    set X' := (X - c) / (q : ℤ) with hX'
    have hZ : (q : ℤ) * X' = X - c := Int.mul_ediv_cancel' (centredOf_dvd q (by omega) X)
    have hcb : |c| ≤ (q / 2 : ℕ) := centredOf_abs (toNat_emod_lt (by omega))
    have hprod : ((qs.take (n + 2)).prod : ℤ) = ((qs.take (n + 1)).prod : ℤ) * q := by
      rw [take_succ_eq hn, List.prod_append]; simp [hqd]
    set P := ((qs.take (n + 1)).prod : ℤ)
    set v' := (t : ℤ) * X' - P * k with hv'
    have hqv : (q : ℤ) * v' = v - t * c := by
      rw [hv', mul_sub, ← mul_assoc, mul_comm (q : ℤ) t, mul_assoc, hZ]
      rw [hprod] at h
      linarith
    have hbound : |v'| ≤ (((V + t * (q / 2)) / q : ℕ) : ℤ) := by
      rw [Int.natCast_div, Int.le_ediv_iff_mul_le (by omega)]
      have h1 : |(q : ℤ) * v'| ≤ V + t * (q / 2 : ℕ) := by
        rw [hqv]
        calc |v - t * c| ≤ |v| + |(t : ℤ) * c| := abs_sub _ _
          _ = |v| + t * |c| := by rw [abs_mul, abs_of_nonneg (by omega : (0 : ℤ) ≤ t)]
          _ ≤ V + t * (q / 2 : ℕ) := by
            have := mul_le_mul_of_nonneg_left hcb (by omega : (0 : ℤ) ≤ t)
            linarith
      rw [abs_mul, abs_of_pos (by omega : (0 : ℤ) < q)] at h1
      push_cast at h1 ⊢
      linarith
    obtain ⟨w, hw1, hw2⟩ := noise_res t qs hq (n + 1) (by omega) (by omega) X' k v' _
      (by rw [hv']; ring) hbound
    refine ⟨w, ?_, ?_⟩
    · rw [dropRev_succ (n := n + 1) hn (by omega)]
      exact hw1
    · rw [take_succ_eq hn, List.reverse_append]
      show |w| ≤ Spec.Decrypt.decBoundRev t (q :: (qs.take (n + 1)).reverse) V
      rw [decBoundRev_succ _ _ _ (List.ne_nil_of_length_pos (by simp; omega))]
      exact hw2

theorem dropAll_spec (t : ℕ) (qs : List ℕ) (ℓ : ℕ) (hp : decLowParamsOK? t qs ℓ = true) (X : ℤ) :
    dropAll qs (residuesZ (qs.take ℓ) X) =
      [(scaleDown ((qs.take ℓ).drop 1).reverse X % (qs.headD 0 : ℤ)).toNat] := by
  obtain ⟨_, h1, hL, hq, hco, _⟩ := paramsLow hp
  exact dropAll_res qs (fun q h => ⟨(hq q h).1, (hq q h).2.2⟩) hco ℓ h1 hL X

theorem dropAll_noise (t : ℕ) (qs : List ℕ) (ℓ : ℕ) (hp : decLowParamsOK? t qs ℓ = true)
    (X k v : ℤ) (V : ℕ) (h : (t : ℤ) * X = ((qs.take ℓ).prod : ℤ) * k + v) (hv : |v| ≤ V) :
    ∃ v' : ℤ, (t : ℤ) * scaleDown ((qs.take ℓ).drop 1).reverse X = (qs.headD 0 : ℤ) * k + v' ∧
      |v'| ≤ Spec.Decrypt.decBoundRev t (qs.take ℓ).reverse V := by
  obtain ⟨_, h1, hL, hq, _, _⟩ := paramsLow hp
  exact noise_res t qs (fun q h => ⟨(hq q h).1, (hq q h).2.2⟩) ℓ h1 hL X k v V h hv

end Validation.BFVDecryptLow
