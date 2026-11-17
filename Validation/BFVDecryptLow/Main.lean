import Validation.BFVDecryptLow.Float
import Validation.BFVDecrypt
import Validation.Scheme.Basic

/-!
# Validation.BFVDecryptLow.Main — the rounding step, one coefficient, the polynomial, the pins
-/

namespace Validation.BFVDecryptLow
open Spec Spec.Float Spec.DecryptBFV Spec.DecryptBFVLow Spec.Scheme NPoly Challenge.BFVDecryptLow
  FHE.Float

/-- One rounding with a value `z` within `ε` of `t·x/q + 1/2`, and `t·x/q` within `d` of the
integer `K`, `d + ε < 1/2`: the cast returns `K`. -/
theorem round_core {z ε : ℚ} {t q x : ℕ} {K : ℤ} (hz : |z - ((t : ℚ) * x / q + 1 / 2)| ≤ ε)
    (hz0 : 0 ≤ z) (hK : |(t : ℚ) * x / q - K| + ε < 1 / 2) : (truncU64 z : ℤ) = K := by
  rw [Validation.BFVDecrypt.truncU64_of_nonneg hz0]
  have h1 := abs_le.mp hz
  have h2 := abs_le.mp (le_refl |(t : ℚ) * x / q - K|)
  rw [Int.floor_eq_iff]
  constructor <;> linarith [abs_nonneg ((t : ℚ) * x / q - K)]

/-- The rounding step for an arithmetic whose rounding of every `x' ≤ q₀/2` is within `ε`: the
centred value `[x]_{q₀}` with `|t·[x] − q₀·k| / q₀ + ε < 1/2` gives `c ≡ k (mod t)`, `c < t`. -/
theorem vec_round (A : Arith) (t q0 x : ℕ) (k : ℤ) (ε : ℚ) (ht : 2 ≤ t) (htq : 2 * t < q0)
    (hq : q0 < 2 ^ 60) (hq1 : q0 % 2 = 1) (hx : x < q0)
    (hz : ∀ x' : ℕ, x' ≤ q0 / 2 →
      |A.mulAdd (1 / 2) (A.ofNat t) (A.div (A.ofNat x') (A.ofNat q0)) - ((t : ℚ) * x' / q0 + 1 / 2)|
        ≤ ε ∧ 0 ≤ A.mulAdd (1 / 2) (A.ofNat t) (A.div (A.ofNat x') (A.ofNat q0)))
    (hk : |((((t : ℤ) * centredOf q0 x - (q0 : ℤ) * k : ℤ)) : ℚ)| / (q0 : ℚ) + ε < 1 / 2) :
    let c := switchModulus q0 t (multiplyAndRoundVec A t q0 x)
    (c : ZMod t) = (k : ZMod t) ∧ c < t := by
  intro c
  have hq0 : (0 : ℚ) < q0 := by exact_mod_cast (show 0 < q0 by omega)
  have htQ : (0 : ℚ) ≤ t := by positivity
  have hε : 0 ≤ ε := le_trans (abs_nonneg _) (hz 0 (Nat.zero_le _)).1
  -- the rational form of the margin
  have hcl : ∀ (x' : ℕ) (K : ℤ), (t : ℤ) * x' - q0 * K = (t : ℤ) * centredOf q0 x - q0 * k ∨
      (t : ℤ) * x' - q0 * K = -((t : ℤ) * centredOf q0 x - q0 * k) →
      |(t : ℚ) * x' / q0 - K| + ε < 1 / 2 := by
    intro x' K h
    have e : (t : ℚ) * x' / q0 - K = (((t : ℤ) * x' - q0 * K : ℤ) : ℚ) / q0 := by
      push_cast; field_simp
    rw [e, abs_div, abs_of_pos hq0]
    rcases h with h | h
    · rw [h]; exact hk
    · rw [h, Int.cast_neg, abs_neg]; exact hk
  -- the bound `K ≤ t/2 + 1/2` from the margin
  have hKb : ∀ (x' : ℕ) (K : ℤ), x' ≤ q0 / 2 → |(t : ℚ) * x' / q0 - K| + ε < 1 / 2 →
      0 ≤ K ∧ 2 * K ≤ t + 1 := by
    intro x' K hx' h
    have h1 := abs_le.mp (le_refl |(t : ℚ) * x' / q0 - K|)
    have hab := abs_nonneg ((t : ℚ) * x' / q0 - K)
    have hx'q : (t : ℚ) * x' / q0 ≤ t / 2 := by
      rw [div_le_iff₀ hq0]
      have : (2 * x' : ℚ) ≤ q0 := by exact_mod_cast (show 2 * x' ≤ q0 by omega)
      nlinarith
    have hx0 : 0 ≤ (t : ℚ) * x' / q0 := by positivity
    have hlo : (K : ℚ) > -1 := by
      have := (abs_le.mp (le_refl |(t : ℚ) * x' / q0 - K|))
      have := le_abs_self ((t : ℚ) * x' / q0 - K); linarith
    have hhi : (2 * K : ℚ) < t + 2 := by
      have := neg_abs_le ((t : ℚ) * x' / q0 - K); linarith
    constructor
    · have : (-1 : ℤ) < K := by exact_mod_cast hlo
      omega
    · have : 2 * K < (t : ℤ) + 2 := by exact_mod_cast hhi
      omega
  unfold c multiplyAndRoundVec
  have hr : rshift q0 1 = q0 / 2 := by unfold rshift; norm_num
  rw [hr]
  split_ifs with hneg
  · -- negative branch: `x' = q0 − x`, `K = −k`
    have hx'e : subFast q0 x = q0 - x := Validation.BFVDecryptLow.subFast_of_le hx.le (by omega)
    rw [hx'e]
    have hx' : q0 - x ≤ q0 / 2 := by omega
    have hc : centredOf q0 x = (x : ℤ) - q0 := by unfold centredOf; rw [if_pos hneg]
    have hK := hcl (q0 - x) (-k) (Or.inr (by rw [hc]; push_cast [Nat.cast_sub hx.le]; ring))
    obtain ⟨hz1, hz0⟩ := hz (q0 - x) hx'
    have hMR : (multiplyAndRound A (q0 - x) t q0 : ℤ) = -k := round_core hz1 hz0 hK
    obtain ⟨hK0, hKt⟩ := hKb (q0 - x) (-k) hx' hK
    set M := multiplyAndRound A (q0 - x) t q0
    rw [Validation.BFVDecryptLow.subFast_of_le (show M ≤ q0 by omega) (by omega)]
    have hv : q0 - M < q0 ∨ (q0 - M = q0 ∧ 2 * t < q0) := by
      rcases Nat.eq_zero_or_pos M with h0 | h0
      · right; exact ⟨by omega, htq⟩
      · left; omega
    obtain ⟨h1, h2⟩ := switchModulus_spec q0 t (q0 - M) (by omega) (by omega) ht (by omega) hv
    refine ⟨?_, h2⟩
    have hc' : centredOf q0 (q0 - M) = -(M : ℤ) := by
      unfold centredOf
      rw [if_pos (by omega)]
      push_cast [Nat.cast_sub (show M ≤ q0 by omega)]; ring
    rw [hc'] at h1
    have : ((switchModulus q0 t (q0 - M) : ℕ) : ZMod t) = ((-(M : ℤ) % t : ℤ) : ZMod t) := by
      rw [← h1, Int.cast_natCast]
    rw [this, ZMod.intCast_mod, hMR, neg_neg]
  · -- positive branch: `x' = x`, `K = k`
    have hx' : x ≤ q0 / 2 := by omega
    have hc : centredOf q0 x = x := by unfold centredOf; rw [if_neg hneg]
    have hK := hcl x k (Or.inl (by rw [hc]))
    obtain ⟨hz1, hz0⟩ := hz x hx'
    have hMR : (multiplyAndRound A x t q0 : ℤ) = k := round_core hz1 hz0 hK
    obtain ⟨hK0, hKt⟩ := hKb x k hx' hK
    set M := multiplyAndRound A x t q0
    rw [Nat.mod_eq_of_lt (show M < q0 by omega)]
    obtain ⟨h1, h2⟩ := switchModulus_spec q0 t M (by omega) (by omega) ht (by omega)
      (Or.inl (by omega))
    refine ⟨?_, h2⟩
    have hc' : centredOf q0 M = (M : ℤ) := by
      unfold centredOf; rw [if_neg (by omega)]
    rw [hc'] at h1
    have : ((switchModulus q0 t M : ℕ) : ZMod t) = (((M : ℤ) % t : ℤ) : ZMod t) := by
      rw [← h1, Int.cast_natCast]
    rw [this, ZMod.intCast_mod, hMR]

theorem roundStep_exact (t : ℕ) (qs : List ℕ) (ℓ : ℕ) (hp : decLowParamsOK? t qs ℓ = true) (x : ℕ)
    (hx : x < qs.headD 0) (k : ℤ)
    (hk : 2 * |(t : ℤ) * centredOf (qs.headD 0) x - (qs.headD 0 : ℤ) * k| < qs.headD 0) :
    let c := switchModulus (qs.headD 0) t (multiplyAndRoundVec Spec.Float.exact t (qs.headD 0) x)
    (c : ZMod t) = (k : ZMod t) ∧ c < t := by
  obtain ⟨ht, h1, hL, hq, _, htq⟩ := paramsLow hp
  obtain ⟨a, l, rfl⟩ : ∃ a l, qs = a :: l := by
    cases qs with
    | nil => simp at hL; omega
    | cons a l => exact ⟨a, l, rfl⟩
  have ha := hq a List.mem_cons_self
  simp only [List.headD_cons] at hx hk htq ⊢
  apply vec_round Spec.Float.exact t a x k 0 ht htq ha.2.2 ha.2.1 hx
  · intro x' _
    refine ⟨?_, by simp [Spec.Float.exact]; positivity⟩
    simp only [Spec.Float.exact]
    rw [show (1 / 2 : ℚ) + t * (x' / a) - (t * x' / a + 1 / 2) = 0 by ring, abs_zero]
  · have hq0 : (0 : ℚ) < a := by exact_mod_cast (show 0 < a by omega)
    rw [add_zero, div_lt_iff₀ hq0]
    have : (2 * |(t : ℤ) * centredOf a x - a * k| : ℚ) < a := by exact_mod_cast hk
    push_cast at this ⊢
    linarith

theorem decLow_unpack {t : ℕ} {qs : List ℕ} {ℓ B : ℕ} (h : decLowOK? t qs ℓ B = true) :
    (2 * lowNoise t qs ℓ B : ℚ) + 2 * (qs.headD 0 : ℚ) * lowErr t < qs.headD 0 := by
  simpa [decLowOK?] using h

theorem residues_eq (qs : List ℕ) (x : ℕ) : residues qs x = residuesZ qs (x : ℤ) := by
  rw [residuesZ_def]
  unfold residues
  apply List.map_congr_left
  intro q _
  rw [← Int.natCast_mod, Int.toNat_natCast]

theorem decLow1_correct (A : ArithD) (hA : ConformsD A) (t : ℕ) (qs : List ℕ) (ℓ : ℕ)
    (hp : decLowParamsOK? t qs ℓ = true) (B : ℕ) (hB : decLowOK? t qs ℓ B = true) (x m : ℕ)
    (hm : m < t) (hx : x < (qs.take ℓ).prod)
    (hnoise : (((x : ℤ) - ((qs.take ℓ).prod / t * m : ℕ) : ℤ) :
      ZMod (qs.take ℓ).prod).valMinAbs.natAbs ≤ B) :
    let c := decLow1 A.base t qs (residues (qs.take ℓ) x)
    (c : ZMod t) = (m : ZMod t) ∧ c < t ∧
      (dropAll qs (residues (qs.take ℓ) x)).headD 0 < qs.headD 0 := by
  intro c
  obtain ⟨ht, h1, hL, hq, hco, htq⟩ := paramsLow hp
  obtain ⟨a, l, hqs⟩ : ∃ a l, qs = a :: l := by
    cases qs with
    | nil => simp at hL; omega
    | cons a l => exact ⟨a, l, rfl⟩
  have ha := hq a (by rw [hqs]; exact List.mem_cons_self)
  have hq0 : qs.headD 0 = a := by rw [hqs]; rfl
  set Q := (qs.take ℓ).prod with hQd
  have hQ : 0 < Q := List.prod_pos fun q h => by
    have := (hq q (List.mem_of_mem_take h)).1; omega
  haveI : NeZero Q := ⟨hQ.ne'⟩
  -- the noise: `t·x = Q·(m + t·j) + (t·e − r·m)`
  set e0 := (((x : ℤ) - (Q / t * m : ℕ) : ℤ) : ZMod Q).valMinAbs with he0
  have hcast : ((e0 : ℤ) : ZMod Q) = (((x : ℤ) - (Q / t * m : ℕ) : ℤ) : ZMod Q) :=
    ZMod.coe_valMinAbs _
  obtain ⟨j, hj⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp hcast
  have hdiv : (Q : ℤ) = t * (Q / t : ℕ) + (Q % t : ℕ) := by
    exact_mod_cast (Nat.div_add_mod Q t).symm
  set v : ℤ := (t : ℤ) * e0 - (Q % t : ℕ) * m
  have htx : (t : ℤ) * x = (Q : ℤ) * (m + t * j) + v := by
    have : (x : ℤ) = (Q / t * m : ℕ) + e0 + Q * j := by linarith
    rw [this, Nat.cast_mul]
    have : (t : ℤ) * (Q / t : ℕ) = Q - (Q % t : ℕ) := by rw [hdiv]; ring
    linear_combination (m : ℤ) * this
  have hv : |v| ≤ (t * B + Q % t * (t - 1) : ℕ) := by
    have he : |e0| ≤ B := by
      have : (e0.natAbs : ℤ) ≤ B := by exact_mod_cast hnoise
      rwa [Int.natCast_natAbs] at this
    have hmt : (m : ℤ) ≤ t - 1 := by omega
    calc |v| ≤ |(t : ℤ) * e0| + |((Q % t : ℕ) : ℤ) * m| := abs_sub _ _
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
  -- the drops
  obtain ⟨v', hv'1, hv'2⟩ := dropAll_noise t qs ℓ hp x (m + t * j) v _ htx hv
  have hres := residues_eq (qs.take ℓ) x
  have hd := dropAll_spec t qs ℓ hp x
  rw [← hres] at hd
  set Y := scaleDown ((qs.take ℓ).drop 1).reverse x
  set y0 := (Y % (qs.headD 0 : ℤ)).toNat with hy0
  have hy0lt : y0 < a := by rw [hy0, hq0]; exact toNat_emod_lt (by omega)
  have hhead : (dropAll qs (residues (qs.take ℓ) x)).headD 0 = y0 := by rw [hd]; rfl
  refine ⟨?_, ?_, by rw [hhead, hq0]; exact hy0lt⟩ <;>
  · -- the rounding step
    have hcen : ∃ j' : ℤ, centredOf a y0 = Y - a * j' := by
      have hY : (y0 : ℤ) = Y % a := by
        rw [hy0, hq0, Int.toNat_of_nonneg (Int.emod_nonneg _ (by omega))]
      unfold centredOf
      split_ifs
      · exact ⟨Y / a + 1, by rw [hY]; have := Int.emod_add_ediv_mul Y a; linarith⟩
      · exact ⟨Y / a, by rw [hY]; have := Int.emod_add_ediv_mul Y a; linarith⟩
    obtain ⟨j', hj'⟩ := hcen
    set k' := m + t * j - t * j' with hk'
    have hkey : (t : ℤ) * centredOf a y0 - a * k' = v' := by
      rw [hj', hk']; rw [hq0] at hv'1; linear_combination hv'1
    have hlow := decLow_unpack hB
    rw [hq0] at hlow
    have hV : (|v'| : ℚ) ≤ lowNoise t qs ℓ B := by
      have : |v'| ≤ (lowNoise t qs ℓ B : ℤ) := hv'2
      exact_mod_cast this
    have hqa : (0 : ℚ) < a := by exact_mod_cast (show 0 < a by omega)
    have hmarg : |((((t : ℤ) * centredOf a y0 - (a : ℤ) * k' : ℤ)) : ℚ)| / (a : ℚ) + lowErr t <
        1 / 2 := by
      rw [hkey, div_add' _ _ _ hqa.ne', div_lt_iff₀ hqa]
      push_cast
      linarith
    have hround := vec_round A.base t a y0 k' (lowErr t) ht (by rw [← hq0]; exact htq) ha.2.2
      ha.2.1 hy0lt (fun x' hx' => by
        obtain ⟨e1, e2, _⟩ := Validation.BFVDecryptLow.multiplyAndRound_err A hA t a x' ht
          (by omega) ha.1 ha.2.2 hx'
        exact ⟨e1, e2⟩) hmarg
    have hc : c = switchModulus a t (multiplyAndRoundVec A.base t a y0) := by
      show decLow1 A.base t qs (residues (qs.take ℓ) x) = _
      unfold decLow1
      rw [hhead, show qs.getD 0 0 = a by rw [hqs]; rfl]
    first
    | (rw [hc]; exact hround.2)
    | (rw [hc, hround.1, hk']; push_cast; simp)

theorem bfvDecryptLow_correct (A : ArithD) (hA : ConformsD A) (t : ℕ) (qs : List ℕ) (ℓ : ℕ)
    (hp : decLowParamsOK? t qs ℓ = true) {N : ℕ} (s : IntPoly N)
    (ct : List (Poly (qs.take ℓ).prod N)) (m : Poly t N) (B : ℕ)
    (hnoise : normInf (centered (phase (ofInt (qs.take ℓ).prod s) ct -
      ofInt (qs.take ℓ).prod ⟨fun i => (((qs.take ℓ).prod / t * (m.coeff i).val : ℕ) : ℤ)⟩)) ≤ B)
    (hB : decLowOK? t qs ℓ B = true) (i : Fin N) :
    (((bfvDecryptLow A t qs ℓ s ct).coeff i : ℕ) : ZMod t) = m.coeff i ∧
      (bfvDecryptLow A t qs ℓ s ct).coeff i < t := by
  obtain ⟨ht2, _, _, hq, _, _⟩ := paramsLow hp
  have hQ : 0 < (qs.take ℓ).prod := List.prod_pos fun q h => by
    have := (hq q (List.mem_of_mem_take h)).1; omega
  haveI : NeZero (qs.take ℓ).prod := ⟨hQ.ne'⟩
  haveI : NeZero t := ⟨by omega⟩
  have hx : ((phase (ofInt (qs.take ℓ).prod s) ct).coeff i).val < (qs.take ℓ).prod := ZMod.val_lt _
  have hm : (m.coeff i).val < t := ZMod.val_lt _
  have hco := Validation.Scheme.abs_coeff_le_normInf (centered (phase (ofInt (qs.take ℓ).prod s) ct -
      ofInt (qs.take ℓ).prod ⟨fun i => (((qs.take ℓ).prod / t * (m.coeff i).val : ℕ) : ℤ)⟩)) i
  have hn : (((((phase (ofInt (qs.take ℓ).prod s) ct).coeff i).val : ℤ) -
      ((qs.take ℓ).prod / t * (m.coeff i).val : ℕ) : ℤ) :
        ZMod (qs.take ℓ).prod).valMinAbs.natAbs ≤ B := by
    have e : (((((phase (ofInt (qs.take ℓ).prod s) ct).coeff i).val : ℤ) -
        ((qs.take ℓ).prod / t * (m.coeff i).val : ℕ) : ℤ) : ZMod (qs.take ℓ).prod) =
        (phase (ofInt (qs.take ℓ).prod s) ct -
          ofInt (qs.take ℓ).prod ⟨fun i => (((qs.take ℓ).prod / t * (m.coeff i).val : ℕ) : ℤ)⟩).coeff i := by
      show _ = (phase (ofInt (qs.take ℓ).prod s) ct).coeff i -
        ((((qs.take ℓ).prod / t * (m.coeff i).val : ℕ) : ℤ) : ZMod (qs.take ℓ).prod)
      rw [Int.cast_sub, Int.cast_natCast, ZMod.natCast_zmod_val]
    rw [e]
    have h3 := hco.trans (show _ ≤ (B : ℤ) by exact_mod_cast hnoise)
    rw [Int.abs_eq_natAbs] at h3
    exact_mod_cast h3
  obtain ⟨h1, h2, _⟩ := decLow1_correct A hA t qs ℓ hp B hB _ (m.coeff i).val hm hx hn
  refine ⟨?_, h2⟩
  show ((decLow1 A.base t qs (residues (qs.take ℓ)
    ((phase (ofInt (qs.take ℓ).prod s) ct).coeff i).val) : ℕ) : ZMod t) = _
  rw [h1, ZMod.natCast_zmod_val]

theorem decLowOK?_t_lt (t : ℕ) (qs : List ℕ) (ℓ B : ℕ) (hq : 1 ≤ qs.headD 0)
    (h : decLowOK? t qs ℓ B = true) : t < 2 ^ 51 := by
  have h1 := decLow_unpack h
  have hq' : (1 : ℚ) ≤ qs.headD 0 := by exact_mod_cast hq
  have h0 : (0 : ℚ) ≤ lowNoise t qs ℓ B := by positivity
  have h2 : lowErr t < 1 / 2 := by
    by_contra hc
    push Not at hc
    nlinarith
  unfold lowErr u at h2
  by_contra hc
  push Not at hc
  have : (2 : ℚ) ^ 51 ≤ t := by exact_mod_cast hc
  nlinarith

theorem lowMargin_needed :
    decLowParamsOK? 2 qsPin 1 = true ∧
      Challenge.BFV.decOK 2 (2 ^ 59 - 55) ((2 ^ 59 - 55 - 5) / 4) = true ∧
      roundDiv (2 * ((2 ^ 59 - 55 - 5) / 4 : ℕ)) (2 ^ 59 - 55) = 0 ∧
      decLow1 Spec.Float.exact 2 qsPin [(2 ^ 59 - 55 - 5) / 4] = 0 ∧
      decLow1 Challenge.BFVDecrypt.advD.base 2 qsPin [(2 ^ 59 - 55 - 5) / 4] = 1 ∧
      decLowOK? 2 qsPin 1 ((2 ^ 59 - 55 - 5) / 4) = false := by
  decide +kernel

end Validation.BFVDecryptLow
