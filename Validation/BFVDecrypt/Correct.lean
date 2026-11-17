import Validation.BFVDecrypt.Main

/-!
# Validation.BFVDecrypt.Correct — one coefficient under the margin
-/

namespace Validation.BFVDecrypt
open Spec.Float Spec.DecryptBFV Spec.Scheme FHE.Float Challenge.BFVDecrypt

/-- The noise makes `t·x/Q` close to `m + t·j`. -/
theorem noise_close (t Q B x m : ℕ) (ht : 0 < t) (hQ : 0 < Q) (hm : m < t)
    (hnoise : (((x : ℤ) - (Q / t * m : ℕ) : ℤ) : ZMod Q).valMinAbs.natAbs ≤ B) :
    ∃ j : ℤ, |(t : ℚ) * x / Q - (m + t * j)| ≤ ((t * B + Q % t * (t - 1) : ℕ) : ℚ) / Q := by
  set e0 := (((x : ℤ) - (Q / t * m : ℕ) : ℤ) : ZMod Q).valMinAbs with he0
  haveI : NeZero Q := ⟨hQ.ne'⟩
  have hcast : ((e0 : ℤ) : ZMod Q) = (((x : ℤ) - (Q / t * m : ℕ) : ℤ) : ZMod Q) :=
    ZMod.coe_valMinAbs _
  have hd : (Q : ℤ) ∣ ((x : ℤ) - (Q / t * m : ℕ)) - e0 :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp hcast
  obtain ⟨j, hj⟩ := hd
  refine ⟨j, ?_⟩
  have hQQ : (0 : ℚ) < Q := by exact_mod_cast hQ
  have hdiv : (Q : ℤ) = t * (Q / t : ℕ) + (Q % t : ℕ) := by exact_mod_cast (Nat.div_add_mod Q t).symm
  have hxq : (x : ℚ) = ((Q / t * m : ℕ) : ℚ) + (e0 : ℚ) + (Q : ℚ) * (j : ℚ) := by
    have : (x : ℤ) = (Q / t * m : ℕ) + e0 + Q * j := by linarith
    have h2 := congrArg (Int.cast : ℤ → ℚ) this
    simp only [Int.cast_add, Int.cast_mul, Int.cast_natCast] at h2
    exact h2
  have hQq : (Q : ℚ) = t * (Q / t : ℕ) + (Q % t : ℕ) := by exact_mod_cast hdiv
  have key : (t : ℚ) * x / Q - (m + t * j) = ((t : ℚ) * e0 - (Q % t : ℕ) * m) / Q := by
    rw [hxq]
    have hQ0 : (Q : ℚ) ≠ 0 := hQQ.ne'
    rw [div_sub' hQ0, div_left_inj' hQ0]
    rw [Nat.cast_mul]
    have e : (t : ℚ) * (Q / t : ℕ) = Q - (Q % t : ℕ) := by rw [hQq]; ring
    rw [show (t : ℚ) * (((Q / t : ℕ) : ℚ) * m + e0 + Q * j) =
      t * ((Q / t : ℕ) : ℚ) * m + t * e0 + t * Q * j by ring, e]
    ring
  rw [key, abs_div, abs_of_pos hQQ]
  apply div_le_div_of_nonneg_right _ hQQ.le
  have he : |(e0 : ℚ)| ≤ B := by
    have : (e0.natAbs : ℚ) ≤ B := by exact_mod_cast hnoise
    rwa [Nat.cast_natAbs, Int.cast_abs] at this
  have hr0 : (0 : ℚ) ≤ (Q % t : ℕ) := Nat.cast_nonneg _
  have hmq : (m : ℚ) ≤ t - 1 := by
    have : m ≤ t - 1 := by omega
    have h := (Nat.cast_le (α := ℚ)).mpr this
    rwa [Nat.cast_sub (by omega), Nat.cast_one] at h
  have hm0 : (0 : ℚ) ≤ m := Nat.cast_nonneg _
  calc |(t : ℚ) * e0 - (Q % t : ℕ) * m| ≤ |(t : ℚ) * e0| + |((Q % t : ℕ) : ℚ) * m| := abs_sub _ _
    _ = t * |(e0 : ℚ)| + (Q % t : ℕ) * m := by
        rw [abs_mul, abs_of_pos (by exact_mod_cast ht), abs_of_nonneg (mul_nonneg hr0 hm0)]
    _ ≤ t * B + (Q % t : ℕ) * (t - 1) := by
        have : (t : ℚ) * |(e0 : ℚ)| ≤ t * B := mul_le_mul_of_nonneg_left he (by positivity)
        have : ((Q % t : ℕ) : ℚ) * m ≤ (Q % t : ℕ) * (t - 1) := mul_le_mul_of_nonneg_left hmq hr0
        linarith
    _ = ((t * B + Q % t * (t - 1) : ℕ) : ℚ) := by
        rw [Nat.cast_add, Nat.cast_mul, Nat.cast_mul, Nat.cast_sub (by omega), Nat.cast_one]

theorem decLib_unpack {t : ℕ} {qs : List ℕ} {B : ℕ} (h : decLibOK? t qs B = true) :
    let η2 : ℚ := ((2 * (t * B + qs.prod % t * (t - 1)) : ℕ) : ℚ)
    η2 + 2 * qs.prod * (delta t qs + 1 / 2 ^ 64) < qs.prod ∧
      (isPow2 t = true ∨ (floatMax t qs ≤ 2 ^ 52 ∧ η2 + 2 * qs.prod * overshoot t qs < 2 * qs.prod)) := by
  simp only [decLibOK?, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
  exact h

theorem floor_eq_of_close {v : ℚ} {Z : ℤ} {ε : ℚ} (h : |v - (Z + 1 / 2)| ≤ ε) (hε : ε < 1 / 2) :
    ⌊v⌋ = Z := by
  have h' := abs_le.mp h
  rw [Int.floor_eq_iff]
  constructor <;> linarith

/-- The final `+ 0.5` and the cast. -/
theorem final_step (A : ArithD) (hA : ConformsD A) (r : ℚ) (Z : ℤ) (η δ ρ : ℚ) (t : ℕ)
    (ht50 : t < 2 ^ 50) (hZ0 : 0 ≤ Z) (hZt : Z ≤ t) (hrZ : |r - Z| ≤ ρ + η)
    (hρδ : ρ + u * (t + 3) ≤ δ) (hmarg : η + (δ + 1 / 2 ^ 64) < 1 / 2) (hη0 : 0 ≤ η)
    (hρ0 : 0 ≤ ρ) :
    0 ≤ A.base.add r (1 / 2) ∧ A.base.add r (1 / 2) < 2 ^ 64 ∧
      (truncU64 (A.base.add r (1 / 2)) : ℤ) = Z := by
  have hu := u_pos
  have hrZ' := abs_le.mp hrZ
  have hZ0' : (0 : ℚ) ≤ Z := by exact_mod_cast hZ0
  have hZt' : (Z : ℚ) ≤ t := by exact_mod_cast hZt
  have ht' : (t : ℚ) < 2 ^ 50 := by exact_mod_cast ht50
  have hu3 : 0 ≤ u * (t + 3) := by positivity
  have hlow : 1 / 2 ^ 64 ≤ r + 1 / 2 := by linarith
  have hup : r + 1 / 2 ≤ t + 1 := by linarith
  have hin : InRange (r + 1 / 2) := inRange_of_bounds
    (by linarith [show (1 : ℚ) / 2 ^ 128 ≤ 1 / 2 ^ 64 by norm_num])
    (by linarith [show (2 : ℚ) ^ 50 + 1 ≤ 2 ^ 128 by norm_num])
  have hw := rounds_abs (hA.base.add r (1 / 2) hin)
  have hpos : (0 : ℚ) < r + 1 / 2 := lt_of_lt_of_le (by positivity) hlow
  rw [abs_of_pos hpos] at hw
  have hwu : u * (r + 1 / 2) ≤ u * (t + 3) := mul_le_mul_of_nonneg_left (by linarith) hu.le
  have hw' := abs_le.mp hw
  have hwZ : |A.base.add r (1 / 2) - (Z + 1 / 2)| ≤ η + δ := by
    rw [abs_le]; constructor <;> linarith
  have hfl : ⌊A.base.add r (1 / 2)⌋ = Z :=
    floor_eq_of_close hwZ (by linarith [show (0 : ℚ) ≤ 1 / 2 ^ 64 by positivity])
  have hwZ' := abs_le.mp hwZ
  have hw0 : 0 ≤ A.base.add r (1 / 2) := by linarith
  refine ⟨hw0, by linarith [show (2 : ℚ) ^ 50 + 2 ≤ 2 ^ 64 by norm_num], ?_⟩
  rw [truncU64_of_nonneg hw0, hfl]

/-- `Challenge.BFVDecrypt.decrypt1_correct`. -/
theorem decrypt1_correct (A : ArithD) (hA : ConformsD A) (t : ℕ) (qs : List ℕ)
    (hp : decParamsOK? t qs = true) (B : ℕ) (hB : decLibOK? t qs B = true) (x m : ℕ) (hm : m < t)
    (hx : x < qs.prod)
    (hnoise : (((x : ℤ) - (qs.prod / t * m : ℕ) : ℤ) : ZMod qs.prod).valMinAbs.natAbs ≤ B) :
    let c := decrypt1 A t qs (tables A.base t qs) (residues qs x)
    (c : ZMod t) = (m : ZMod t) ∧ c ≤ t ∧ (isPow2 t = true → c < t) ∧
      (isPow2 t = false →
        0 ≤ A.base.add (reduced A t (floatSumInt A t qs (allWords qs (tables A.base t qs)
              (residues qs x)))) (1 / 2) ∧
        A.base.add (reduced A t (floatSumInt A t qs (allWords qs (tables A.base t qs)
              (residues qs x)))) (1 / 2) < 2 ^ 64) := by
  intro c
  obtain ⟨ht2, ht50, _, _, hq, _⟩ := params hp
  have ht0 : 0 < t := by omega
  have htQ : (0 : ℚ) < t := by exact_mod_cast ht0
  have hQ : 0 < qs.prod := List.prod_pos fun q h => by have := (hq q h).1; omega
  have hQQ : (0 : ℚ) < qs.prod := by exact_mod_cast hQ
  have hxr := reduced_residues t qs hp x
  set Q := qs.prod with hQdef
  set η : ℚ := ((t * B + Q % t * (t - 1) : ℕ) : ℚ) / Q with hη
  have hη0 : 0 ≤ η := by positivity
  obtain ⟨hL1, hL2⟩ := decLib_unpack hB
  have hη2 : ((2 * (t * B + Q % t * (t - 1)) : ℕ) : ℚ) = 2 * Q * η := by
    rw [hη]; push_cast; field_simp
  rw [hη2] at hL1 hL2
  have hmarg : η + (delta t qs + 1 / 2 ^ 64) < 1 / 2 := by
    have : 2 * Q * (η + (delta t qs + 1 / 2 ^ 64)) < 2 * Q * (1 / 2) := by linarith
    exact lt_of_mul_lt_mul_left this (by positivity)
  have hδ0 : 0 ≤ delta t qs := by
    unfold delta; split
    · exact sumErr_nonneg _ _ (by norm_num)
    · have := sumErr_nonneg 0 (caps qs) le_rfl
      have : 0 ≤ u * ((floatMax t qs : ℚ) + 2 * t + 8) := mul_nonneg u_pos.le (by positivity)
      positivity
  have hδ : delta t qs ≤ 1 / 2 := by linarith [show (0 : ℚ) ≤ 1 / 2 ^ 64 by positivity]
  obtain ⟨Mi, hMi⟩ := noise_close t Q B x m ht0 hQ hm hnoise
  rw [← hη] at hMi
  have hMi' := abs_le.mp hMi
  obtain ⟨I0, k, hI, hv⟩ := value_split A.base hp x
  set I := intSum t qs (allWords qs (tables A.base t qs) (residues qs x)) with hIdef
  set F := exactFrac t qs (residues qs x) with hF
  obtain ⟨j, hj⟩ := dvd_of_zmod hI
  have hIlt : I < 2 ^ 63 := by
    rw [hIdef, intSum_value _ hp hxr]; exact eprod_sum_lt hp hxr
  obtain ⟨hF0, hFc⟩ := exactFrac_bounds hp hxr
  have hcs : (((caps qs).sum : ℕ) : ℚ) < 2 ^ 52 := by exact_mod_cast caps_sum_lt hp
  have hIj : (I : ℚ) = I0 + t * j := by
    have : (I : ℤ) = I0 + t * j := by linarith
    have h2 := congrArg (Int.cast : ℤ → ℚ) this
    simp only [Int.cast_add, Int.cast_mul, Int.cast_natCast] at h2
    exact h2
  have hmZ : ∀ z : ℤ, z = m + t * Mi → (z : ZMod t) = (m : ZMod t) := by
    intro z hz
    have := zmod_of_int_eq (t := t) (c := z) (r := m) (j := Mi) hz
    rw [this]; push_cast; rfl
  show (c : ZMod t) = (m : ZMod t) ∧ c ≤ t ∧ (isPow2 t = true → c < t) ∧ _
  unfold c decrypt1
  by_cases h2 : isPow2 t = true
  · simp only [h2, if_true]
    obtain ⟨e1, e2, e3⟩ := floatSum_err_pow2 A hA t qs (residues qs x) hp hxr h2 hδ
    set fs := floatSum A.base (1 / 2) (allWords qs (tables A.base t qs) (residues qs x)) with hfs
    -- F is close to the integer Z
    set Z : ℤ := m + t * Mi + t * k - I0 with hZ
    have hFZ : |F - Z| ≤ η := by
      have : F - Z = (t : ℚ) * x / Q - (m + t * Mi) := by
        rw [hZ]; push_cast; linarith
      rw [this]; exact hMi
    have hclose : |fs - (Z + 1 / 2)| ≤ η + delta t qs := by
      have := abs_le.mp e1; have := abs_le.mp hFZ
      rw [abs_le]; constructor <;> linarith
    have hfl : ⌊fs⌋ = Z := floor_eq_of_close hclose (by linarith [show (0:ℚ) ≤ 1 / 2 ^ 64 by positivity])
    have hZ0 : (truncU64 fs : ℤ) = Z := by rw [truncU64_of_nonneg e2, hfl]
    have hZlt : truncU64 fs < 2 ^ 53 := by
      have : (truncU64 fs : ℤ) ≤ 2 ^ 53 - 1 := by
        rw [truncU64_of_nonneg e2]; apply Int.le_of_lt_add_one; rw [Int.floor_lt]; push_cast
        have := abs_le.mp e1; linarith
      omega
    have hadd : addFast I (truncU64 fs) = I + truncU64 fs := Nat.mod_eq_of_lt (by omega)
    rw [hadd, and_mask h2]
    refine ⟨?_, (Nat.mod_lt _ ht0).le, fun _ => Nat.mod_lt _ ht0, fun h => absurd h (by simp [h2])⟩
    rw [ZMod.natCast_mod]
    have key : (((I + truncU64 fs : ℕ)) : ℤ) = m + t * (Mi + k + j) := by
      push_cast; rw [hZ0, hZ]; linarith
    rw [← Int.cast_natCast, zmod_of_int_eq key]; push_cast; rfl
  · have h2' : isPow2 t = false := by simpa using h2
    simp only [h2', Bool.false_eq_true, if_false]
    obtain ⟨hF52, hov⟩ := hL2.resolve_left h2
    obtain ⟨r1, r2, r3, r4, r5⟩ := reduced_err_odd A hA t qs (residues qs x) hp hxr h2' hδ hF52
    set f := floatSumInt A t qs (allWords qs (tables A.base t qs) (residues qs x)) with hf
    set q := quot A t f with hqd
    set r := reduced A t f with hr
    set ρ := sumErr 0 (caps qs) + u * ((floatMax t qs : ℚ) + t + 2) + 1 / 2 ^ 127 with hρ
    set e : ℚ := F + I - t * q with he
    have hov' : η + overshoot t qs < 1 := by
      have : 2 * Q * (η + overshoot t qs) < 2 * Q * 1 := by linarith
      exact lt_of_mul_lt_mul_left this (by positivity)
    set Z : ℤ := m + t * Mi + t * k + t * j - t * q with hZ
    have heZ : |e - Z| ≤ η := by
      have : e - Z = (t : ℚ) * x / Q - (m + t * Mi) := by
        rw [he, hZ, hIj]; push_cast; linarith
      rw [this]; exact hMi
    have heZ' := abs_le.mp heZ
    have hZ0 : 0 ≤ Z := by
      have : (-1 : ℚ) < Z := by linarith
      exact_mod_cast (show (-1 : ℤ) < Z by exact_mod_cast this)
    have hZt : Z ≤ t := by
      have : (Z : ℚ) < t + 1 := by linarith
      have : Z < (t : ℤ) + 1 := by exact_mod_cast this
      omega
    -- ρ ≤ δ − u(t+2) − (small)
    have hu := u_pos
    have hρδ : ρ + u * (t + 3) ≤ delta t qs := by
      rw [hρ, delta_odd h2']
      have : (1 : ℚ) / 2 ^ 127 ≤ 1 / 2 ^ 120 := by norm_num
      nlinarith
    have hrZ : |r - Z| ≤ ρ + η := by
      have := abs_le.mp r1; rw [abs_le]; constructor <;> linarith
    have hrZ' := abs_le.mp hrZ
    have hu3 : 0 ≤ u * (t + 3) := by positivity
    obtain ⟨hw0, hw64, hc⟩ := final_step A hA r Z η (delta t qs) ρ t ht50 hZ0 hZt hrZ hρδ hmarg
      hη0 ((abs_nonneg _).trans r1)
    set w := A.base.add r (1 / 2) with hwd
    refine ⟨?_, by omega, fun h => h.elim, fun _ => ⟨hw0, hw64⟩⟩
    have key : (truncU64 w : ℤ) = m + t * (Mi + k + j - q) := by rw [hc, hZ]; ring
    rw [← Int.cast_natCast, zmod_of_int_eq key]; push_cast; rfl

end Validation.BFVDecrypt
