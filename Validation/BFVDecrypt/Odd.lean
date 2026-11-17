import Validation.BFVDecrypt.Int
import Validation.BFVDecrypt.Float

/-!
# Validation.BFVDecrypt.Odd — the non-power-of-two reduction in binary64
-/

namespace Validation.BFVDecrypt
open Spec.Float Spec.DecryptBFV FHE.Float Challenge.BFVDecrypt

theorem rounds_abs {x y : ℚ} (h : Rounds x y) : |y - x| ≤ u * |x| := by
  obtain ⟨δ, hδ, rfl⟩ := h
  have e : x * (1 + δ) - x = δ * x := by ring
  rw [e, abs_mul]
  exact mul_le_mul_of_nonneg_right hδ (abs_nonneg _)

theorem prod_bounds {a b : ℚ} (ha : |a| ≤ u) (hb : |b| ≤ u) :
    1 - 3 * u ≤ (1 + a) * (1 + b) ∧ (1 + a) * (1 + b) ≤ 1 + 3 * u ∧ 0 ≤ (1 + a) * (1 + b) := by
  have hu := u_pos
  have hu1 : u ≤ 1 / 2 ^ 53 := le_of_eq rfl
  have hab : |a * b| ≤ u * u := by
    rw [abs_mul]; exact mul_le_mul ha hb (abs_nonneg _) hu.le
  have h1 := abs_le.mp ha
  have h2 := abs_le.mp hb
  have h3 := abs_le.mp hab
  have h4 : u * u ≤ u := by nlinarith
  have e : (1 + a) * (1 + b) = 1 + a + b + a * b := by ring
  rw [e]
  refine ⟨by linarith, by linarith, by linarith⟩

theorem intSum_le_intMax (A : Arith) {t : ℕ} {qs xs : List ℕ} (hp : decParamsOK? t qs = true)
    (hx : Reduced qs xs) : intSum t qs (allWords qs (tables A t qs) xs) ≤ intMax t qs := by
  rw [intSum_value A hp hx]
  have ht : 0 < t := by have := (params hp).1; omega
  unfold intMax
  rw [← caps_eq t qs xs hx.length_eq, List.map_map]
  apply List.sum_le_sum
  intro d hd
  simp only [Function.comp, eprod]
  have h1 := (spec_dok hp hx d hd).1
  have h2 := spec_int_lt ht d hd
  split
  · have := Nat.mod_lt (d.1 * d.2.1) ht; omega
  · exact Nat.mul_le_mul (by unfold cap at *; omega) (by omega)

theorem exactFrac_bounds {t : ℕ} {qs xs : List ℕ} (hp : decParamsOK? t qs = true)
    (hx : Reduced qs xs) :
    0 ≤ exactFrac t qs xs ∧ exactFrac t qs xs ≤ (((caps qs).sum : ℕ) : ℚ) := by
  rw [exactFrac_eq, ← caps_eq t qs xs hx.length_eq]
  refine ⟨List.sum_nonneg fun v hv => ?_, ?_⟩
  · obtain ⟨d, _, rfl⟩ := List.mem_map.mp hv; exact val_nonneg d
  · have := sum_map_le (spec t qs xs) val (fun d => ((cap d : ℕ) : ℚ))
      (fun d hd => val_le_cap d (spec_dok hp hx d hd))
    have e : (((spec t qs xs).map cap).sum : ℚ) =
        ((spec t qs xs).map fun d => ((cap d : ℕ) : ℚ)).sum := by
      push_cast [List.map_map]; rfl
    rw [e]; exact this

theorem delta_odd {t : ℕ} {qs : List ℕ} (h2 : isPow2 t = false) :
    delta t qs = sumErr 0 (caps qs) + u * ((floatMax t qs : ℚ) + 2 * t + 8) + 1 / 2 ^ 120 := by
  simp [delta, h2]

theorem u_small : u ≤ 1 / 2 ^ 53 := le_of_eq rfl

/-- Stage 1: `f = fl(s + I)`. -/
theorem stage_f (A : Arith) (hA : Conforms A) (s I F σ M : ℚ) (hs0 : 0 ≤ s)
    (hslow : s = 0 ∨ 1 / 2 ^ 63 ≤ s) (hI : I = 0 ∨ 1 ≤ I) (hsF : |s - F| ≤ σ) (hF0 : 0 ≤ F)
    (hσ : σ ≤ 1 / 2) (hM : F + I + 2 ≤ M) (hM52 : M ≤ 2 ^ 52) :
    0 ≤ A.add s I ∧ A.add s I ≤ M ∧ |A.add s I - (F + I)| ≤ σ + u * M ∧
      (A.add s I = 0 ∨ 1 / 2 ^ 64 ≤ A.add s I) := by
  have hu := u_pos
  have hu1 := u_small
  have hI0 : 0 ≤ I := by rcases hI with h | h <;> linarith
  have hsF' := abs_le.mp hsF
  have hsI0 : 0 ≤ s + I := by linarith
  have hsIM : s + I ≤ M - 1 := by linarith
  have hlow : s + I = 0 ∨ 1 / 2 ^ 63 ≤ s + I := by
    rcases hslow with h0 | h0
    · rcases hI with h1 | h1
      · left; rw [h0, h1]; ring
      · right; linarith [show (1 : ℚ) / 2 ^ 63 ≤ 1 by norm_num]
    · right; linarith
  have hin : InRange (s + I) := by
    rcases hlow with h | h
    · left; exact h
    · exact inRange_of_bounds (by linarith [show (1 : ℚ) / 2 ^ 128 ≤ 1 / 2 ^ 63 by norm_num])
        (by linarith [show (2 : ℚ) ^ 52 ≤ 2 ^ 128 by norm_num])
  obtain ⟨δ, hδ, he⟩ := hA.add s I hin
  have hδ' := abs_le.mp hδ
  have huM : u * M ≤ 1 / 2 := by
    have : u * M ≤ 1 / 2 ^ 53 * 2 ^ 52 := mul_le_mul hu1 hM52 (by linarith) (by norm_num)
    linarith [show (1 : ℚ) / 2 ^ 53 * 2 ^ 52 = 1 / 2 by norm_num]
  have hp : 0 ≤ 1 + δ := by linarith [show u ≤ 1 by linarith [show (1 : ℚ) / 2 ^ 53 ≤ 1 by norm_num]]
  rw [he]
  have hdev : |(s + I) * (1 + δ) - (s + I)| ≤ u * (s + I) := by
    rw [show (s + I) * (1 + δ) - (s + I) = δ * (s + I) by ring, abs_mul, abs_of_nonneg hsI0]
    exact mul_le_mul_of_nonneg_right hδ hsI0
  have hdev' := abs_le.mp hdev
  have hus : u * (s + I) ≤ u * M := mul_le_mul_of_nonneg_left (by linarith) hu.le
  refine ⟨mul_nonneg hsI0 hp, by linarith, ?_, ?_⟩
  · rw [abs_le]; constructor <;> linarith
  · rcases hlow with h | h
    · left; rw [h, zero_mul]
    · right
      have : 1 / 2 ^ 63 * (1 - u) ≤ (s + I) * (1 + δ) :=
        mul_le_mul h (by linarith) (by linarith [show (1 : ℚ) / 2 ^ 53 ≤ 1 by norm_num]) hsI0
      have : (1 : ℚ) / 2 ^ 64 ≤ 1 / 2 ^ 63 * (1 - u) := by
        have : 1 / 2 ^ 63 * (1 - 1 / 2 ^ 53) ≤ 1 / 2 ^ 63 * (1 - u) :=
          mul_le_mul_of_nonneg_left (by linarith) (by norm_num)
        linarith [show (1 : ℚ) / 2 ^ 64 ≤ 1 / 2 ^ 63 * (1 - 1 / 2 ^ 53) by norm_num]
      linarith

/-- Stage 2: the quotient `static_cast<uint64_t>(f * tInv)`. -/
theorem stage_q (A : ArithD) (hA : ConformsD A) (t : ℕ) (ht2 : 2 ≤ t) (ht50 : t < 2 ^ 50)
    (f M : ℚ) (hf0 : 0 ≤ f) (hfM : f ≤ M) (hM52 : M ≤ 2 ^ 52)
    (hflow : f = 0 ∨ 1 / 2 ^ 64 ≤ f) :
    0 ≤ A.base.mul f (A.base.div 1 (A.base.ofNat t)) ∧
      A.base.mul f (A.base.div 1 (A.base.ofNat t)) < 2 ^ 64 ∧
      (t : ℚ) * quot A t f ≤ f * (1 + 3 * u) ∧ f * (1 - 3 * u) - t < (t : ℚ) * quot A t f ∧
      quot A t f ≤ 2 ^ 53 := by
  have hu := u_pos
  have hu1 := u_small
  have hu1' : u ≤ 1 := by linarith [show (1 : ℚ) / 2 ^ 53 ≤ 1 by norm_num]
  have ht0 : (0 : ℚ) < t := by exact_mod_cast (show 0 < t by omega)
  have ht1 : (2 : ℚ) ≤ t := by exact_mod_cast ht2
  have htQ : (t : ℚ) < 2 ^ 50 := by exact_mod_cast ht50
  have hoft : A.base.ofNat t = t := hA.ofNatExact t (by omega)
  have hinv : InRange (1 / (t : ℚ)) := inRange_of_bounds
    (by rw [div_le_div_iff₀ (by positivity) ht0]; linarith [show (2 : ℚ) ^ 50 ≤ 2 ^ 128 by norm_num])
    (by rw [div_le_iff₀ ht0]; linarith)
  obtain ⟨d2, hd2, hdiv⟩ := hA.base.div 1 t (by positivity) hinv
  have hd2' := abs_le.mp hd2
  set tInv := A.base.div 1 (A.base.ofNat t) with htInv
  have htI : tInv = 1 / t * (1 + d2) := by rw [htInv, hoft]; exact hdiv
  have hit0 : 0 ≤ 1 / (t : ℚ) := by positivity
  have hit : 1 / (t : ℚ) ≤ 1 / 2 := by
    rw [div_le_div_iff₀ ht0 (by norm_num)]; linarith
  have hit50 : (1 : ℚ) / 2 ^ 50 ≤ 1 / t := by
    rw [div_le_div_iff₀ (by positivity) ht0]; linarith
  have htI1 : 1 / 2 ^ 51 ≤ tInv := by
    rw [htI]
    have : 1 / 2 ^ 50 * (1 - u) ≤ 1 / t * (1 + d2) :=
      mul_le_mul hit50 (by linarith) (by linarith) hit0
    have : (1 : ℚ) / 2 ^ 51 ≤ 1 / 2 ^ 50 * (1 - u) := by
      have : 1 / 2 ^ 50 * (1 - 1 / 2 ^ 53) ≤ 1 / 2 ^ 50 * (1 - u) :=
        mul_le_mul_of_nonneg_left (by linarith) (by norm_num)
      linarith [show (1 : ℚ) / 2 ^ 51 ≤ 1 / 2 ^ 50 * (1 - 1 / 2 ^ 53) by norm_num]
    linarith
  have htI2 : tInv ≤ 1 := by
    rw [htI]
    have : 1 / t * (1 + d2) ≤ 1 / 2 * 2 := mul_le_mul hit (by linarith) (by linarith) (by norm_num)
    linarith
  have hfy : InRange (f * tInv) := by
    rcases hflow with h0 | h0
    · left; rw [h0, zero_mul]
    · refine inRange_of_bounds ?_ ?_
      · have : 1 / 2 ^ 64 * (1 / 2 ^ 51) ≤ f * tInv :=
          mul_le_mul h0 htI1 (by positivity) hf0
        linarith [show (1 : ℚ) / 2 ^ 128 ≤ 1 / 2 ^ 64 * (1 / 2 ^ 51) by norm_num]
      · have : f * tInv ≤ M * 1 := mul_le_mul hfM htI2 (by linarith) (by linarith)
        linarith [show (2 : ℚ) ^ 52 ≤ 2 ^ 128 by norm_num]
  obtain ⟨d3, hd3, hmul⟩ := hA.base.mul f tInv hfy
  set y := A.base.mul f tInv with hy
  have hyv : y = f / t * ((1 + d2) * (1 + d3)) := by
    rw [hmul, htI]; ring
  obtain ⟨hpl, hph, hp0⟩ := prod_bounds hd2 hd3
  have hft0 : 0 ≤ f / t := by positivity
  have hftM : f / t ≤ M := by
    rw [div_le_iff₀ ht0]; nlinarith
  have hy0 : 0 ≤ y := by rw [hyv]; positivity
  have hyle : y ≤ f / t * (1 + 3 * u) := by
    rw [hyv]; exact mul_le_mul_of_nonneg_left hph hft0
  have hyge : f / t * (1 - 3 * u) ≤ y := by
    rw [hyv]; exact mul_le_mul_of_nonneg_left hpl hft0
  have hy53 : y ≤ 2 ^ 53 := by
    have : f / t * (1 + 3 * u) ≤ 2 ^ 52 * 2 :=
      mul_le_mul (hftM.trans hM52) (by linarith) (by linarith) (by norm_num)
    linarith
  have hqy : ((quot A t f : ℕ) : ℚ) = ⌊y⌋ := by
    unfold quot truncU64
    rw [← htInv, ← hy, if_pos hy0]
    have : 0 ≤ ⌊y⌋ := Int.floor_nonneg.mpr hy0
    rw [← Int.cast_natCast, Int.toNat_of_nonneg this]
  have hq1 : ((quot A t f : ℕ) : ℚ) ≤ y := by rw [hqy]; exact Int.floor_le y
  have hq2 : y - 1 < ((quot A t f : ℕ) : ℚ) := by rw [hqy]; exact Int.sub_one_lt_floor y
  refine ⟨hy0, by linarith, ?_, ?_, ?_⟩
  · have := mul_le_mul_of_nonneg_left (hq1.trans hyle) ht0.le
    rwa [show (t : ℚ) * (f / t * (1 + 3 * u)) = f * (1 + 3 * u) by field_simp] at this
  · have h3 : f / t * (1 - 3 * u) - 1 < ((quot A t f : ℕ) : ℚ) := by linarith
    have := mul_lt_mul_of_pos_left h3 ht0
    rw [mul_sub, show (t : ℚ) * (f / t * (1 - 3 * u)) = f * (1 - 3 * u) by field_simp] at this
    linarith
  · have : ((quot A t f : ℕ) : ℚ) ≤ 2 ^ 53 := by linarith
    exact_mod_cast this

/-- Stage 3: `f −= td * q`, in either compiled form. -/
theorem stage_r (A : ArithD) (hA : ConformsD A) (t q : ℕ) (f B : ℚ) (htq : t * q ≤ 2 ^ 53)
    (ht : t ≤ 2 ^ 53) (hq : q ≤ 2 ^ 53) (hB : |f - t * q| ≤ B) (hB2 : B ≤ 2 ^ 100) :
    |A.mulSub f (A.base.ofNat t) (A.base.ofNat q) - (f - t * q)| ≤ u * B + 1 / 2 ^ 127 := by
  have hu := u_pos
  rw [hA.ofNatExact t ht, hA.ofNatExact q hq]
  have gen : ∀ r : ℚ, (InRange (f - t * q) → Rounds (f - t * q) r) →
      (|f - t * q| < 1 / 2 ^ 128 → |r| ≤ 1 / 2 ^ 128) →
      |r - (f - t * q)| ≤ u * B + 1 / 2 ^ 127 := by
    intro r h1 h2
    by_cases hsm : |f - t * q| < 1 / 2 ^ 128
    · have := h2 hsm
      have : |r - (f - t * q)| ≤ |r| + |f - t * q| := abs_sub _ _
      have : 0 ≤ u * B := mul_nonneg hu.le ((abs_nonneg _).trans hB)
      linarith [show (1 : ℚ) / 2 ^ 128 + 1 / 2 ^ 128 = 1 / 2 ^ 127 by norm_num]
    · push_neg at hsm
      have hin : InRange (f - t * q) :=
        Or.inr ⟨hsm, by linarith [show (2 : ℚ) ^ 100 ≤ 2 ^ 128 by norm_num]⟩
      have := rounds_abs (h1 hin)
      have : u * |f - t * q| ≤ u * B := mul_le_mul_of_nonneg_left hB hu.le
      linarith [show (0 : ℚ) ≤ 1 / 2 ^ 127 by positivity]
  rcases hA.mulSub f t q with h | h
  · rw [h, hA.mulExact t q htq]; push_cast
    exact gen _ (hA.sub f _) (hA.subSmall f _)
  · rw [h]
    exact gen _ (hA.fnma _ _ f) (hA.fnmaSmall _ _ f)

theorem intSum_cases (n : ℕ) : (n : ℚ) = 0 ∨ 1 ≤ (n : ℚ) := by
  rcases Nat.eq_zero_or_pos n with h | h
  · left; rw [h]; simp
  · right; exact_mod_cast h

/-- `Challenge.BFVDecrypt.reduced_err_odd`. -/
theorem reduced_err_odd (A : ArithD) (hA : ConformsD A) (t : ℕ) (qs xs : List ℕ)
    (hp : decParamsOK? t qs = true) (hx : Reduced qs xs) (h2 : isPow2 t = false)
    (hδ : delta t qs ≤ 1 / 2) (hF : floatMax t qs ≤ 2 ^ 52) :
    let ws := allWords qs (tables A.base t qs) xs
    let f := floatSumInt A t qs ws
    let e : ℚ := exactFrac t qs xs + intSum t qs ws - t * quot A t f
    |reduced A t f - e| ≤ sumErr 0 (caps qs) + u * ((floatMax t qs : ℚ) + t + 2) + 1 / 2 ^ 127 ∧
      -overshoot t qs ≤ e ∧ e ≤ t + overshoot t qs ∧
      0 ≤ A.base.mul f (A.base.div 1 (A.base.ofNat t)) ∧
      A.base.mul f (A.base.div 1 (A.base.ofNat t)) < 2 ^ 64 := by
  intro ws f e
  have hu := u_pos
  have hu1 := u_small
  obtain ⟨ht2, ht50, _, _, _, _⟩ := params hp
  have hσ0 : 0 ≤ sumErr 0 (caps qs) := sumErr_nonneg 0 _ le_rfl
  have hM52 : (floatMax t qs : ℚ) ≤ 2 ^ 52 := by exact_mod_cast hF
  have hσ1 : sumErr 0 (caps qs) ≤ 1 / 2 := by
    rw [delta_odd h2] at hδ
    have : 0 ≤ u * ((floatMax t qs : ℚ) + 2 * t + 8) := by positivity
    have : (0 : ℚ) ≤ 1 / 2 ^ 120 := by positivity
    linarith
  obtain ⟨k1, k2, k3⟩ := sum_err A.base hA.base t qs xs hp hx 0 (Or.inl rfl) (by linarith)
  obtain ⟨hF0, hFc⟩ := exactFrac_bounds hp hx
  have hIm : (intSum t qs ws : ℚ) ≤ intMax t qs := by
    exact_mod_cast intSum_le_intMax A.base hp hx
  have hMdef : (floatMax t qs : ℚ) = (((caps qs).sum : ℕ) : ℚ) + (intMax t qs : ℚ) + 2 := by
    unfold floatMax; push_cast; ring
  have hI53 : intSum t qs ws ≤ 2 ^ 53 := by
    have : (intSum t qs ws : ℚ) ≤ 2 ^ 53 := by linarith
    exact_mod_cast this
  have hf : f = A.base.add (floatSum A.base 0 ws) (intSum t qs ws : ℚ) := by
    show A.base.add (floatSum A.base 0 ws) (A.base.ofNat (intSum t qs ws)) = _
    rw [hA.ofNatExact _ hI53]
  obtain ⟨f0, fM, fX, flow⟩ := stage_f A.base hA.base (floatSum A.base 0 ws) (intSum t qs ws)
    (exactFrac t qs xs) (sumErr 0 (caps qs)) (floatMax t qs) k2 k3 (intSum_cases _)
    (by simpa using k1) hF0 hσ1 (by linarith) hM52
  rw [← hf] at f0 fM fX flow
  obtain ⟨y0, y64, tq1, tq2, q53⟩ := stage_q A hA t ht2 ht50 f (floatMax t qs) f0 fM hM52 flow
  set M : ℚ := (floatMax t qs : ℚ) with hMdef'
  set q := quot A t f with hq
  have huM : u * M ≤ 1 / 2 := by
    have : u * M ≤ 1 / 2 ^ 53 * 2 ^ 52 := mul_le_mul hu1 hM52 (by positivity) (by norm_num)
    linarith [show (1 : ℚ) / 2 ^ 53 * 2 ^ 52 = 1 / 2 by norm_num]
  have huf : u * f ≤ u * M := mul_le_mul_of_nonneg_left fM hu.le
  have huf0 : 0 ≤ u * f := mul_nonneg hu.le f0
  have e1 : f * (1 + 3 * u) = f + 3 * (u * f) := by ring
  have e2 : f * (1 - 3 * u) = f - 3 * (u * f) := by ring
  rw [e1] at tq1
  rw [e2] at tq2
  have htq53 : t * q ≤ 2 ^ 53 := by
    have : (t : ℚ) * q ≤ 2 ^ 53 := by linarith
    exact_mod_cast this
  have hftq1 : -(3 * (u * M)) ≤ f - t * q := by linarith
  have hftq2 : f - t * q ≤ t + 3 * (u * M) := by linarith
  have hB : |f - t * q| ≤ t + 3 * (u * M) := by
    rw [abs_le]; constructor <;> linarith
  have htQ : (t : ℚ) ≤ 2 ^ 50 := by exact_mod_cast ht50.le
  have hr := stage_r A hA t q f (t + 3 * (u * M)) htq53 (by omega) q53 hB (by linarith)
  have hred : reduced A t f = A.mulSub f (A.base.ofNat t) (A.base.ofNat q) := rfl
  rw [← hred] at hr
  have hov : overshoot t qs = sumErr 0 (caps qs) + 4 * (u * M) := by
    unfold overshoot; ring
  have he : e = exactFrac t qs xs + intSum t qs ws - t * q := rfl
  have hX := abs_le.mp fX
  have hr' := abs_le.mp hr
  have hut : u * (t + 3 * (u * M)) = u * t + 3 * u * (u * M) := by ring
  have hu2 : 3 * u * (u * M) ≤ 2 * u := by nlinarith
  have hut2 : u * ((M : ℚ) + t + 2) = u * M + u * t + 2 * u := by ring
  refine ⟨?_, ?_, ?_, y0, y64⟩
  · rw [abs_le, he, hut2]
    rw [hut] at hr'
    constructor <;> linarith
  · rw [hov, he]; linarith
  · rw [hov, he]; linarith

end Validation.BFVDecrypt
