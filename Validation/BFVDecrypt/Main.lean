import Validation.BFVDecrypt.Odd

/-!
# Validation.BFVDecrypt.Main — one coefficient: exactness and correctness under the margin
-/

namespace Validation.BFVDecrypt
open Spec.Float Spec.DecryptBFV Spec.Scheme FHE.Float Challenge.BFVDecrypt

/-! ### Small facts -/

theorem isPow2_eq {t : ℕ} (h : isPow2 t = true) : t = 2 ^ t.log2 := by
  simp only [isPow2, Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at h
  obtain ⟨h0, hand⟩ := h
  have hle := Nat.log2_self_le h0
  have hlt : t < 2 ^ (t.log2 + 1) := Nat.lt_log2_self
  by_contra hne
  have h1 : 2 ^ t.log2 ≤ t - 1 := by omega
  have hb1 : (t - 1).testBit t.log2 = true :=
    Nat.testBit_of_two_pow_le_and_two_pow_add_one_gt h1 (by omega)
  have hb0 : t.testBit t.log2 = true := Nat.testBit_log2 h0
  have : (t &&& (t - 1)).testBit t.log2 = true := by rw [Nat.testBit_and, hb0, hb1]; rfl
  rw [hand] at this
  simp at this

theorem and_mask {t : ℕ} (h : isPow2 t = true) (n : ℕ) : n &&& (t - 1) = n % t := by
  rw [isPow2_eq h, Nat.and_two_pow_sub_one_eq_mod]

theorem roundDiv_eq (a : ℤ) (b : ℕ) (hb : 0 < b) : roundDiv a b = ⌊(a : ℚ) / b + 1 / 2⌋ := by
  unfold roundDiv
  have e : (a : ℚ) / b + 1 / 2 = (((2 * a + b : ℤ) : ℚ) / ((2 * b : ℕ) : ℚ)) := by
    have : (b : ℚ) ≠ 0 := by exact_mod_cast hb.ne'
    push_cast; field_simp
  rw [e, Rat.floor_intCast_div_natCast]
  push_cast; rfl

theorem truncU64_of_nonneg {v : ℚ} (h : 0 ≤ v) : (truncU64 v : ℤ) = ⌊v⌋ := by
  unfold truncU64; rw [if_pos h, Int.toNat_of_nonneg (Int.floor_nonneg.mpr h)]

theorem caps_sum_lt {t : ℕ} {qs : List ℕ} (hp : decParamsOK? t qs = true) :
    (caps qs).sum < 2 ^ 52 := by
  have hs := Nat.size_le.mpr (show qs.length < 2 ^ 8 by have := (params hp).2.2.2.1; omega)
  have hs' : sizeQMSB qs ≤ 8 := hs
  obtain ⟨_, h60, hh⟩ := qMSB_facts hp
  cases hsp : pathSplit qs
  · have := caps_sum_nonsplit hp hsp
    have h51 : qMSB qs + sizeQMSB qs < 52 := by
      simpa [pathSplit] using hsp
    have : 2 ^ (sizeQMSB qs + qMSB qs) ≤ 2 ^ 52 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  · have := caps_sum_split hp hsp
    have : 3 * 2 ^ (sizeQMSB qs + qMSBHf qs) ≤ 3 * 2 ^ 38 :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) (by omega))
    omega

/-! ### The limbs -/

theorem zip_flatMap (t : ℕ) (qs : List ℕ) (x : ℕ) : ∀ L : List ℕ,
    (L.zip (L.map fun q => x % q)).flatMap (fun p => wspec t qs p.1 p.2) =
      L.flatMap fun q => wspec t qs q (x % q)
  | [] => rfl
  | q :: L => by simp [List.flatMap_cons, zip_flatMap t qs x L]

theorem spec_residues (t : ℕ) (qs : List ℕ) (x : ℕ) :
    spec t qs (residues qs x) = qs.flatMap fun q => wspec t qs q (x % q) := by
  unfold spec residues
  exact zip_flatMap t qs x qs

theorem reduced_residues (t : ℕ) (qs : List ℕ) (hp : decParamsOK? t qs = true) (x : ℕ) :
    Reduced qs (residues qs x) := by
  have hq := (params hp).2.2.2.2.1
  unfold Reduced residues
  have key : ∀ L : List ℕ, (∀ q ∈ L, 3 ≤ q) → List.Forall₂ (fun x q => x < q) (L.map (x % ·)) L := by
    intro L
    induction L with
    | nil => intro _; exact List.Forall₂.nil
    | cons q l ih =>
      intro h
      exact List.Forall₂.cons (Nat.mod_lt _ (by have := h q List.mem_cons_self; omega))
        (ih fun a ha => h a (List.mem_cons_of_mem _ ha))
  exact key qs fun q h => (hq q h).1

theorem limbs_value {t : ℕ} {qs : List ℕ} (hp : decParamsOK? t qs = true) (x : ℕ) :
    ∀ L : List ℕ, (∀ q ∈ L, q ∈ qs) →
      ∃ I0 : ℕ, (I0 : ZMod t) =
          (((L.flatMap fun q => wspec t qs q (x % q)).map fun d => d.1 * d.2.1).sum : ℕ) ∧
        (L.map fun q => ((x % q : ℕ) : ℚ) * (theta t qs q : ℚ) / q).sum =
          I0 + ((L.flatMap fun q => wspec t qs q (x % q)).map val).sum
  | [], _ => ⟨0, by simp, by simp⟩
  | q :: L, hL => by
    obtain ⟨I1, h1, h1'⟩ := limbs_value hp x L fun a ha => hL a (List.mem_cons_of_mem _ ha)
    have hq := hL q List.mem_cons_self
    have hq3 := ((params hp).2.2.2.2.1 q hq).1
    obtain ⟨I2, h2, h2'⟩ := limb_value hp q (x % q) hq (Nat.mod_lt _ (by omega))
    refine ⟨I2 + I1, ?_, ?_⟩
    · simp only [List.flatMap_cons, List.map_append, List.sum_append]
      rw [Nat.cast_add, Nat.cast_add, h1, h2]
    · simp only [List.flatMap_cons, List.map_append, List.sum_append, List.map_cons,
        List.sum_cons]
      rw [h1', h2']; push_cast; ring

/-- The decision quantity: `t·x/Q + t·k = I0 + exactFrac` with `I0 ≡ intSum (mod t)`. -/
theorem value_split (A : Arith) {t : ℕ} {qs : List ℕ} (hp : decParamsOK? t qs = true) (x : ℕ) :
    ∃ (I0 : ℕ) (k : ℤ),
      (I0 : ZMod t) = (intSum t qs (allWords qs (tables A t qs) (residues qs x)) : ZMod t) ∧
      (t : ℚ) * x / qs.prod + t * k = I0 + exactFrac t qs (residues qs x) := by
  obtain ⟨k, hk⟩ := crt_value hp x
  obtain ⟨I0, hI, hv⟩ := limbs_value hp x qs fun q h => h
  refine ⟨I0, k, ?_, ?_⟩
  · rw [hI, intSum_value A hp (reduced_residues t qs hp x), spec_residues]
    rw [Nat.cast_list_sum, Nat.cast_list_sum, List.map_map, List.map_map]
    congr 1
    apply List.map_congr_left
    intro d _
    simp only [Function.comp]
    unfold eprod; split <;> simp [ZMod.natCast_mod]
  · rw [← hk, hv, exactFrac_eq, spec_residues]

/-! ### Exactness -/

theorem foldl_add_sum {β : Type} (g : β → ℚ) :
    ∀ (L : List β) (s : ℚ), L.foldl (fun s w => s + g w) s = s + (L.map g).sum
  | [], s => by simp
  | w :: L, s => by
    simp only [List.foldl_cons, List.map_cons, List.sum_cons]
    rw [foldl_add_sum g L]; ring

theorem floatSum_exact (start : ℚ) (t : ℕ) (qs xs : List ℕ) :
    floatSum Spec.Float.exact start (allWords qs (tables Spec.Float.exact t qs) xs) =
      start + exactFrac t qs xs := by
  unfold floatSum exactFrac
  exact foldl_add_sum (fun (w : ℕ × ℕ × ℚ) => (w.1 : ℚ) * w.2.2) _ start

theorem zmod_of_int_eq {t : ℕ} {c : ℤ} {r j : ℤ} (h : c = r + t * j) :
    (c : ZMod t) = (r : ZMod t) := by
  rw [h]; push_cast; simp

theorem dvd_of_zmod {t a b : ℕ} (h : (a : ZMod t) = (b : ZMod t)) : ∃ j : ℤ, (b : ℤ) - a = t * j := by
  have := (ZMod.natCast_eq_natCast_iff _ _ _).mp h
  exact (Nat.modEq_iff_dvd.mp this)

/-- `Challenge.BFVDecrypt.decrypt1_exact`. -/
theorem decrypt1_exact (t : ℕ) (qs : List ℕ) (hp : decParamsOK? t qs = true) (x : ℕ)
    (hx : x < qs.prod) :
    ((decrypt1 exactD t qs (tables Spec.Float.exact t qs) (residues qs x) : ℕ) : ZMod t) =
        ((roundDiv (t * x) qs.prod : ℤ) : ZMod t) ∧
      decrypt1 exactD t qs (tables Spec.Float.exact t qs) (residues qs x) ≤ t ∧
      (isPow2 t = true → decrypt1 exactD t qs (tables Spec.Float.exact t qs) (residues qs x) < t) := by
  obtain ⟨ht2, _, _, _, hq, _⟩ := params hp
  have hQ : 0 < qs.prod := List.prod_pos fun q h => by have := (hq q h).1; omega
  have hxr := reduced_residues t qs hp x
  obtain ⟨I0, k, hI, hv⟩ := value_split Spec.Float.exact hp x
  set I := intSum t qs (allWords qs (tables Spec.Float.exact t qs) (residues qs x)) with hIdef
  set F := exactFrac t qs (residues qs x) with hF
  obtain ⟨j, hj⟩ := dvd_of_zmod hI
  have hIlt : I < 2 ^ 63 := by
    rw [hIdef, intSum_value _ hp hxr]; exact eprod_sum_lt hp hxr
  obtain ⟨hF0, hFc⟩ := exactFrac_bounds hp hxr
  have hcs : (((caps qs).sum : ℕ) : ℚ) < 2 ^ 52 := by exact_mod_cast caps_sum_lt hp
  have hrd : roundDiv ((t * x : ℕ) : ℤ) qs.prod = ⌊(t : ℚ) * x / qs.prod + 1 / 2⌋ := by
    rw [roundDiv_eq _ _ hQ]; push_cast; rfl
  have hY : ⌊(I0 : ℚ) + F + 1 / 2⌋ = roundDiv ((t * x : ℕ) : ℤ) qs.prod + t * k := by
    rw [hrd, ← hv, show (t : ℚ) * x / qs.prod + t * k + 1 / 2 =
      (t : ℚ) * x / qs.prod + 1 / 2 + ((t * k : ℤ) : ℚ) by push_cast; ring, Int.floor_add_intCast]
  have hcast : ((roundDiv (t * x) qs.prod : ℤ) : ZMod t) =
      ((roundDiv ((t * x : ℕ) : ℤ) qs.prod : ℤ) : ZMod t) := by push_cast; rfl
  rw [hcast]
  unfold decrypt1
  by_cases h2 : isPow2 t = true
  · simp only [h2, if_true]
    have hfs : floatSum exactD.base (1 / 2)
        (allWords qs (tables Spec.Float.exact t qs) (residues qs x)) = 1 / 2 + F :=
      floatSum_exact _ _ _ _
    rw [hfs, ← hIdef]
    have hfs0 : (0 : ℚ) ≤ 1 / 2 + F := by linarith
    have hZ := truncU64_of_nonneg hfs0
    set Z := truncU64 (1 / 2 + F) with hZdef
    have hZlt : Z < 2 ^ 53 := by
      have : (Z : ℤ) ≤ 2 ^ 53 - 1 := by
        rw [hZ]; apply Int.le_of_lt_add_one; rw [Int.floor_lt]; push_cast; linarith
      omega
    have hadd : addFast I Z = I + Z := Nat.mod_eq_of_lt (by omega)
    rw [hadd, and_mask h2]
    have ht0 : 0 < t := by omega
    refine ⟨?_, (Nat.mod_lt _ ht0).le, fun _ => Nat.mod_lt _ ht0⟩
    have hfl : ⌊(I0 : ℚ) + F + 1 / 2⌋ = (I0 : ℤ) + ⌊1 / 2 + F⌋ := by
      rw [show (I0 : ℚ) + F + 1 / 2 = 1 / 2 + F + ((I0 : ℤ) : ℚ) by push_cast; ring,
        Int.floor_add_intCast, add_comm]
    have key : (((I + Z : ℕ)) : ℤ) = roundDiv ((t * x : ℕ) : ℤ) qs.prod + t * (k + j) := by
      push_cast
      rw [hZ]
      have : (I : ℤ) = I0 + t * j := by linarith
      rw [this, mul_add]
      rw [hfl] at hY
      push_cast at hY
      linarith
    rw [ZMod.natCast_mod, ← Int.cast_natCast, zmod_of_int_eq key]
  · have h2' : isPow2 t = false := by simpa using h2
    simp only [h2', Bool.false_eq_true, if_false]
    have ht0 : (0 : ℚ) < t := by exact_mod_cast (show 0 < t by omega)
    have hG : floatSumInt exactD t qs (allWords qs (tables Spec.Float.exact t qs) (residues qs x))
        = F + I := by
      show floatSum exactD.base 0 _ + (I : ℚ) = F + I
      rw [show floatSum exactD.base 0
        (allWords qs (tables Spec.Float.exact t qs) (residues qs x)) = 0 + F from
          floatSum_exact _ _ _ _, zero_add]
    rw [hG]
    set G : ℚ := F + I with hGdef
    have hG0 : 0 ≤ G := by have : (0 : ℚ) ≤ I := Nat.cast_nonneg _; linarith
    have hq : (quot exactD t G : ℤ) = ⌊G / t⌋ := by
      show (truncU64 (G * (1 / (t : ℚ))) : ℤ) = _
      rw [truncU64_of_nonneg (by positivity), mul_one_div]
    set q := quot exactD t G with hqdef
    have hred : reduced exactD t G = G - t * q := rfl
    have hq1 : (t : ℚ) * q ≤ G := by
      have : ((q : ℤ) : ℚ) ≤ G / t := by rw [hq]; exact Int.floor_le _
      push_cast at this
      rw [le_div_iff₀ ht0] at this; linarith
    have hq2 : G < (t : ℚ) * q + t := by
      have : G / t < ((q : ℤ) : ℚ) + 1 := by rw [hq]; exact Int.lt_floor_add_one _
      push_cast at this
      rw [div_lt_iff₀ ht0] at this; linarith
    have hw : exactD.base.add (reduced exactD t G) (1 / 2) = G - t * q + 1 / 2 := by
      rw [hred]; rfl
    rw [hw]
    have hw0 : (0 : ℚ) ≤ G - t * q + 1 / 2 := by linarith
    have hc := truncU64_of_nonneg hw0
    set c := truncU64 (G - t * q + 1 / 2) with hcdef
    have hct : c ≤ t := by
      have : (c : ℤ) ≤ t := by
        rw [hc]; apply Int.le_of_lt_add_one; rw [Int.floor_lt]; push_cast; linarith
      omega
    refine ⟨?_, hct, fun h => absurd h (by simp [h2'])⟩
    have hfl : ⌊G - t * q + 1 / 2⌋ = ⌊(I0 : ℚ) + F + 1 / 2⌋ + t * (j - q) := by
      have : G - t * q + 1 / 2 = (I0 : ℚ) + F + 1 / 2 + ((t * (j - q) : ℤ) : ℚ) := by
        rw [hGdef]
        have : (I : ℚ) = I0 + t * j := by exact_mod_cast (show (I : ℤ) = I0 + t * j by linarith)
        rw [this]; push_cast; ring
      rw [this, Int.floor_add_intCast]
    have key : (c : ℤ) = roundDiv ((t * x : ℕ) : ℤ) qs.prod + t * (k + j - q) := by
      rw [hc, hfl, hY]; ring
    rw [← Int.cast_natCast, zmod_of_int_eq key]

end Validation.BFVDecrypt
