import Challenge.BFVMul.BEHZ
import FHE.BFV.MulHPS

/-!
# FHE.BFV.MulBEHZ — the BEHZ multiplication, component by component, on integers

`Challenge.BFVMul.behzMul` (limb by limb: small Montgomery extension, limb-wise tensor product,
fast RNS floor, Shenoy–Kumaresan conversion) is related to plain integer arithmetic, under the
side condition `behzAuxOK?`:

* `behzLift qs mt c`: the integer representatives the algorithm multiplies,
  `A = (c″ + Q·r)/m̃` coefficient by coefficient (`smmrVal`). `behzLift_congr`: `A ≡ c (mod Q)`;
  `behzLift_norm`: `2·‖A‖∞ ≤ Q + ⌈2(k−1)·Q/m̃⌉`.
* `behzFloor t qs A B`: the fast floor `F = (t·T − S)/Q` of the integer tensor product
  (`floorVal`). `behzFloor_round`: `2·|Q·F − t·T| ≤ Q·2k` (indeed `Q·F − t·T ∈ [−k·Q, 0]`).
* `behzMul_eq`: `behzMul … c d = F mod Q` (representatives in `[0, Q)`);
  `behzMul_congr`: the same after `ofInt Q`.
* `behzMul_lifted`: the four facts together, in the shape of the hypotheses of
  `Challenge.BFVMul.stepOK_mul_lifted`.

The scalar facts, on the residues of one integer: `smmrq1_eq` (the limb the small Montgomery
reduction computes is the residue of `smmrVal`), `smmrVal_dvd`, `smmrVal_bounds`; `floor1_eq`,
`floorVal_bounds`; `sk1_eq`, `skVal_eq_self` (Shenoy–Kumaresan is exact when
`2·|F| ≤ B·(msk − 1 − 2m)`). The CRT core is `FHE.BFV.MulHPS.crt_dvd`.
-/

namespace FHE.BFV.MulBEHZ
open Spec NPoly Scheme Challenge.BFVMul Challenge.BFVMul.HPS Challenge.BFVMul.BEHZ
open Validation.Ring Validation.Scheme Validation.Source
open FHE.RNS FHE.BFV.MulHPS

/-! ### Lists and congruences -/

theorem sum_map_modEq' {α : Type} (n : ℤ) (l : List α) (f g : α → ℤ)
    (h : ∀ a ∈ l, f a ≡ g a [ZMOD n]) : (l.map f).sum ≡ (l.map g).sum [ZMOD n] := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simpa using Int.ModEq.add (h a List.mem_cons_self)
      (ih fun b hb => h b (List.mem_cons_of_mem _ hb))

/-- A sum of CRT terms `(g q mod q)·(Q/q)` lies in `[0, k·Q]`. -/
theorem crtTerms_bounds (qs : List ℕ) (hpos : ∀ q ∈ qs, 0 < q) (g : ℕ → ℤ) :
    0 ≤ (qs.map fun q : ℕ => g q % q * ((qs.prod / q : ℕ) : ℤ)).sum ∧
      (qs.map fun q : ℕ => g q % q * ((qs.prod / q : ℕ) : ℤ)).sum ≤ qs.length * (qs.prod : ℤ) := by
  have hterm : ∀ q ∈ qs, 0 ≤ g q % q * ((qs.prod / q : ℕ) : ℤ) ∧
      g q % q * ((qs.prod / q : ℕ) : ℤ) ≤ (qs.prod : ℤ) := by
    intro q hq
    have hq0 : (0 : ℤ) < q := by exact_mod_cast hpos q hq
    have h1 := Int.emod_nonneg (g q) hq0.ne'
    have h2 := Int.emod_lt_of_pos (g q) hq0
    have h3 : (0 : ℤ) ≤ ((qs.prod / q : ℕ) : ℤ) := by positivity
    have h4 : (q : ℤ) * ((qs.prod / q : ℕ) : ℤ) = qs.prod := by
      exact_mod_cast Nat.mul_div_cancel' (List.dvd_prod hq)
    refine ⟨mul_nonneg h1 h3, ?_⟩
    rw [← h4]
    exact mul_le_mul_of_nonneg_right h2.le h3
  constructor
  · exact List.sum_nonneg fun x hx => by
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hx
      exact (hterm q hq).1
  · have := List.sum_le_length_nsmul (qs.map fun q : ℕ => g q % q * ((qs.prod / q : ℕ) : ℤ))
      (qs.prod : ℤ) fun x hx => by
        obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hx
        exact (hterm q hq).2
    simpa using this

/-- `a·a⁻¹ ≡ 1 (mod m)` for coprime `a`, `m`. -/
theorem mul_invMod_modEq (a m : ℕ) (hm : 0 < m) (h : Nat.Coprime a m) :
    (a : ℤ) * invMod a m ≡ 1 [ZMOD m] := by
  rw [← ZMod.intCast_eq_intCast_iff]
  push_cast
  rw [cast_invMod _ _ hm]
  exact ZMod.coe_mul_inv_eq_one a h

/-- A factor coprime to the modulus cancels. -/
theorem modEq_cancel (a m : ℕ) (h : Nat.Coprime a m) (x y : ℤ)
    (hxy : (a : ℤ) * x ≡ a * y [ZMOD m]) : x ≡ y [ZMOD m] := by
  rw [Int.modEq_iff_dvd] at hxy ⊢
  have hc : IsCoprime (m : ℤ) (a : ℤ) := (Nat.isCoprime_iff_coprime.mpr h).symm
  refine hc.dvd_of_dvd_mul_right ?_
  convert hxy using 1
  ring

theorem coprime_prod (a : ℕ) (qs : List ℕ) (h : ∀ q ∈ qs, Nat.Coprime a q) :
    Nat.Coprime a qs.prod := Nat.coprime_list_prod_right_iff.mpr h

theorem prod_coprime (a : ℕ) (qs : List ℕ) (h : ∀ q ∈ qs, Nat.Coprime q a) :
    Nat.Coprime qs.prod a := Nat.coprime_list_prod_left_iff.mpr h

/-! ### Fast base conversion -/

/-- The twisted digit `[X·[c·(Q/q)⁻¹]_q]_q`. -/
def tw (c : ℕ) (qs : List ℕ) (X : ℤ) (q : ℕ) : ℤ :=
  X % q * ((c : ℤ) * invMod (qs.prod / q) q % q) % q

/-- The fast base conversion of `c·X`: `Σ_q [X·c·(Q/q)⁻¹]_q·(Q/q)`, congruent to `c·X` modulo `Q`
and in `[0, k·Q]`. -/
def fastSum (c : ℕ) (qs : List ℕ) (X : ℤ) : ℤ :=
  (qs.map fun q : ℕ => tw c qs X q * ((qs.prod / q : ℕ) : ℤ)).sum

theorem twist_map (c : ℕ) (qs : List ℕ) (X : ℤ) :
    twist c qs (qs.map fun q : ℕ => X % q) = qs.map (tw c qs X) :=
  zipWith_map_self _ _ _

theorem convSum_map (qs : List ℕ) (g : ℕ → ℤ) (m : ℕ) :
    convSum qs (qs.map g) m ≡ (qs.map fun q : ℕ => g q * ((qs.prod / q : ℕ) : ℤ)).sum
      [ZMOD m] := by
  unfold convSum
  rw [zipWith_map_self]
  refine sum_map_modEq _ _ _ _ fun q => Int.ModEq.mul_left _ ?_
  rw [Int.natCast_mod]
  exact Int.mod_modEq _ _

theorem fastSum_dvd (c : ℕ) (qs : List ℕ) (hpos : ∀ q ∈ qs, 0 < q)
    (hcop : qs.Pairwise Nat.Coprime) (X : ℤ) : (qs.prod : ℤ) ∣ fastSum c qs X - c * X :=
  crt_dvd qs hpos hcop (c * X) (tw c qs X) fun q hq => by
    unfold tw
    rw [ZMod.intCast_mod, Int.cast_mul, ZMod.intCast_mod, ZMod.intCast_mod, Int.cast_mul,
      cast_invMod _ _ (hpos q hq)]
    push_cast
    ring

theorem fastSum_bounds (c : ℕ) (qs : List ℕ) (hpos : ∀ q ∈ qs, 0 < q) (X : ℤ) :
    0 ≤ fastSum c qs X ∧ fastSum c qs X ≤ qs.length * (qs.prod : ℤ) :=
  crtTerms_bounds qs hpos fun q => X % q * ((c : ℤ) * invMod (qs.prod / q) q % q)

/-! ### Small Montgomery reduction -/

/-- `r = [−c″·Q⁻¹]_{m̃}` in `[−m̃/2, m̃/2)`. -/
def smmrR (qs : List ℕ) (mt : ℕ) (X : ℤ) : ℤ :=
  if ((mt / 2 : ℕ) : ℤ) ≤
      fastSum mt qs X % mt * (((mt - 1 : ℕ) : ℤ) * invMod qs.prod mt % mt) % mt then
    fastSum mt qs X % mt * (((mt - 1 : ℕ) : ℤ) * invMod qs.prod mt % mt) % mt - mt
  else fastSum mt qs X % mt * (((mt - 1 : ℕ) : ℤ) * invMod qs.prod mt % mt) % mt

/-- The integer whose residues the small Montgomery reduction computes: `(c″ + Q·r)/m̃`. -/
def smmrVal (qs : List ℕ) (mt : ℕ) (X : ℤ) : ℤ :=
  (fastSum mt qs X + qs.prod * smmrR qs mt X) / mt

theorem mtRem_eq (qs : List ℕ) (mt : ℕ) (X : ℤ) :
    mtRem qs mt (qs.map (tw mt qs X)) = smmrR qs mt X := by
  have h : convSum qs (qs.map (tw mt qs X)) mt % mt = fastSum mt qs X % mt :=
    convSum_map qs _ mt
  unfold mtRem smmrR
  simp only [h]

theorem smmrR_bounds (qs : List ℕ) (mt : ℕ) (hmt : 0 < mt) (heven : mt % 2 = 0) (X : ℤ) :
    -(mt : ℤ) ≤ 2 * smmrR qs mt X ∧ 2 * smmrR qs mt X ≤ mt - 2 := by
  have hmt' : (0 : ℤ) < mt := by exact_mod_cast hmt
  unfold smmrR
  generalize fastSum mt qs X % mt * (((mt - 1 : ℕ) : ℤ) * invMod qs.prod mt % mt) = w
  have h1 := Int.emod_nonneg w hmt'.ne'
  have h2 := Int.emod_lt_of_pos w hmt'
  have h3 : (2 : ℤ) * ((mt / 2 : ℕ) : ℤ) = mt := by omega
  split_ifs with h <;> constructor <;> omega

theorem smmrR_dvd (qs : List ℕ) (mt : ℕ) (hmt : 0 < mt) (hcop : Nat.Coprime qs.prod mt)
    (X : ℤ) : (mt : ℤ) ∣ fastSum mt qs X + qs.prod * smmrR qs mt X := by
  have : NeZero mt := ⟨hmt.ne'⟩
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  have hinv : ((qs.prod : ℕ) : ZMod mt) * ((qs.prod : ℕ) : ZMod mt)⁻¹ = 1 :=
    ZMod.coe_mul_inv_eq_one _ hcop
  have hm1 : (((mt - 1 : ℕ) : ℤ) : ZMod mt) = -1 := by
    have : ((mt - 1 : ℕ) : ℤ) = (mt : ℤ) - 1 := by omega
    rw [this]
    simp
  have hr : ((smmrR qs mt X : ℤ) : ZMod mt) =
      (fastSum mt qs X : ZMod mt) * (-1 * ((qs.prod : ℕ) : ZMod mt)⁻¹) := by
    unfold smmrR
    split_ifs
    · rw [Int.cast_sub, Int.cast_natCast, ZMod.natCast_self, sub_zero, ZMod.intCast_mod,
        Int.cast_mul, ZMod.intCast_mod, ZMod.intCast_mod, Int.cast_mul, hm1,
        cast_invMod _ _ hmt]
    · rw [ZMod.intCast_mod, Int.cast_mul, ZMod.intCast_mod, ZMod.intCast_mod, Int.cast_mul, hm1,
        cast_invMod _ _ hmt]
  rw [Int.cast_add, Int.cast_mul, hr, Int.cast_natCast]
  linear_combination (-(fastSum mt qs X : ZMod mt)) * hinv

theorem smmrVal_mul (qs : List ℕ) (mt : ℕ) (hmt : 0 < mt) (hcop : Nat.Coprime qs.prod mt)
    (X : ℤ) : (mt : ℤ) * smmrVal qs mt X = fastSum mt qs X + qs.prod * smmrR qs mt X :=
  Int.mul_ediv_cancel' (smmrR_dvd qs mt hmt hcop X)

/-- The small Montgomery reduction returns a representative of `X` modulo `Q`. -/
theorem smmrVal_dvd (qs : List ℕ) (hpos : ∀ q ∈ qs, 0 < q) (hcopq : qs.Pairwise Nat.Coprime)
    (mt : ℕ) (hmt : 0 < mt) (hcop : Nat.Coprime qs.prod mt) (X : ℤ) :
    (qs.prod : ℤ) ∣ smmrVal qs mt X - X := by
  have hc : IsCoprime (qs.prod : ℤ) (mt : ℤ) := Nat.isCoprime_iff_coprime.mpr hcop
  refine hc.dvd_of_dvd_mul_left ?_
  have e : (mt : ℤ) * (smmrVal qs mt X - X) =
      (fastSum mt qs X - mt * X) + qs.prod * smmrR qs mt X := by
    rw [mul_sub, smmrVal_mul qs mt hmt hcop]
    ring
  rw [e]
  exact dvd_add (fastSum_dvd mt qs hpos hcopq X) (Dvd.intro _ rfl)

/-- `−Q·m̃ ≤ 2·m̃·A ≤ Q·(m̃ + 2(k−1))`. -/
theorem smmrVal_bounds (qs : List ℕ) (hpos : ∀ q ∈ qs, 0 < q) (mt : ℕ) (hmt : 0 < mt)
    (heven : mt % 2 = 0) (hcop : Nat.Coprime qs.prod mt) (X : ℤ) :
    2 * ((mt : ℤ) * |smmrVal qs mt X|) ≤ qs.prod * ((mt + 2 * (qs.length - 1) : ℕ) : ℤ) := by
  have hQ : (0 : ℤ) < qs.prod := by exact_mod_cast prod_pos' qs hpos
  have hmt' : (0 : ℤ) < mt := by exact_mod_cast hmt
  obtain ⟨hr1, hr2⟩ := smmrR_bounds qs mt hmt heven X
  obtain ⟨hs1, hs2⟩ := fastSum_bounds mt qs hpos X
  have hm := smmrVal_mul qs mt hmt hcop X
  have e : (mt : ℤ) * |smmrVal qs mt X| = |(mt : ℤ) * smmrVal qs mt X| := by
    rw [abs_mul, abs_of_pos hmt']
  rw [e, hm]
  have hk : qs.length = 0 ∨ ((qs.length - 1 : ℕ) : ℤ) = (qs.length : ℤ) - 1 := by omega
  have hk0 : (0 : ℤ) ≤ ((qs.length - 1 : ℕ) : ℤ) := by positivity
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  have hq1 : -((qs.prod : ℤ) * mt) ≤ 2 * (qs.prod * smmrR qs mt X) := by nlinarith
  have hq2 : 2 * ((qs.prod : ℤ) * smmrR qs mt X) ≤ qs.prod * (mt - 2) := by nlinarith
  have hk1 : (0 : ℤ) ≤ qs.prod * ((qs.length - 1 : ℕ) : ℤ) := by positivity
  rcases hk with hk | hk
  · rw [hk, Nat.cast_zero, zero_mul] at hs2
    rcases abs_cases (fastSum mt qs X + qs.prod * smmrR qs mt X) with ⟨h, _⟩ | ⟨h, _⟩ <;>
      rw [h] <;> nlinarith
  · rw [hk]
    rcases abs_cases (fastSum mt qs X + qs.prod * smmrR qs mt X) with ⟨h, _⟩ | ⟨h, _⟩ <;>
      rw [h] <;> nlinarith

/-- `smmrq1` on the residues of `X` is `smmrVal qs mt X mod b`. -/
theorem smmrq1_eq (qs : List ℕ) (mt : ℕ) (hmt : 0 < mt) (hcop : Nat.Coprime qs.prod mt)
    (b : ℕ) (hb : 0 < b) (hcb : Nat.Coprime mt b) (X : ℤ) :
    smmrq1 qs mt (qs.map fun q : ℕ => X % q) b = smmrVal qs mt X % b := by
  unfold smmrq1
  simp only [twist_map, mtRem_eq]
  refine modEq_cancel mt b hcb _ _ ?_
  rw [smmrVal_mul qs mt hmt hcop]
  have h1 : convSum qs (qs.map (tw mt qs X)) b % b ≡ fastSum mt qs X [ZMOD b] :=
    (Int.mod_modEq _ _).trans (convSum_map qs _ b)
  have h2 : (((qs.prod % b : ℕ) : ℤ)) ≡ qs.prod [ZMOD b] := by
    rw [Int.natCast_mod]; exact Int.mod_modEq _ _
  have h3 := mul_invMod_modEq mt b hb hcb
  have e : (mt : ℤ) * ((convSum qs (qs.map (tw mt qs X)) b % b +
      smmrR qs mt X * ((qs.prod % b : ℕ) : ℤ)) * invMod mt b) =
      (convSum qs (qs.map (tw mt qs X)) b % b + smmrR qs mt X * ((qs.prod % b : ℕ) : ℤ)) *
        ((mt : ℤ) * invMod mt b) := by ring
  rw [e]
  have := ((h1.add (Int.ModEq.mul_left (smmrR qs mt X) h2)).mul h3)
  rw [mul_one] at this
  refine this.trans ?_
  rw [mul_comm (smmrR qs mt X)]

/-! ### Fast floor -/

/-- The integer whose residues the fast floor computes: `(t·T − S)/Q = ⌊t·T/Q⌋ − v`. -/
def floorVal (t : ℕ) (qs : List ℕ) (T : ℤ) : ℤ := (t * T - fastSum t qs T) / qs.prod

theorem floorVal_mul (t : ℕ) (qs : List ℕ) (hpos : ∀ q ∈ qs, 0 < q)
    (hcop : qs.Pairwise Nat.Coprime) (T : ℤ) :
    (qs.prod : ℤ) * floorVal t qs T = t * T - fastSum t qs T := by
  refine Int.mul_ediv_cancel' ?_
  have := fastSum_dvd t qs hpos hcop T
  rw [← dvd_neg] at this
  convert this using 1
  ring

/-- `Q·F − t·T ∈ [−k·Q, 0]`. -/
theorem floorVal_bounds (t : ℕ) (qs : List ℕ) (hpos : ∀ q ∈ qs, 0 < q)
    (hcop : qs.Pairwise Nat.Coprime) (T : ℤ) :
    -(qs.length * (qs.prod : ℤ)) ≤ qs.prod * floorVal t qs T - t * T ∧
      (qs.prod : ℤ) * floorVal t qs T - t * T ≤ 0 := by
  obtain ⟨h1, h2⟩ := fastSum_bounds t qs hpos T
  rw [floorVal_mul t qs hpos hcop]
  constructor <;> linarith

/-- `floor1` on the residues of `T` is `floorVal t qs T mod b`. -/
theorem floor1_eq (t : ℕ) (qs : List ℕ) (hpos : ∀ q ∈ qs, 0 < q)
    (hcop : qs.Pairwise Nat.Coprime) (b : ℕ) (hb : 0 < b) (hcb : ∀ q ∈ qs, Nat.Coprime q b)
    (T : ℤ) :
    floor1 t qs (qs.map fun q : ℕ => T % q) b (T % b) = floorVal t qs T % b := by
  unfold floor1
  simp only [twist_map, zipWith_map_self]
  have hQb : Nat.Coprime qs.prod b := prod_coprime b qs hcb
  refine modEq_cancel qs.prod b hQb _ _ ?_
  rw [floorVal_mul t qs hpos hcop, mul_sub]
  refine Int.ModEq.sub ?_ ?_
  · have h3 := mul_invMod_modEq qs.prod b hb hQb
    have h4 : (t : ℤ) * invMod qs.prod b % b ≡ t * invMod qs.prod b [ZMOD b] := Int.mod_modEq _ _
    have h5 : T % b ≡ T [ZMOD b] := Int.mod_modEq _ _
    have := (h5.mul h4).mul_left (qs.prod : ℤ)
    refine this.trans ?_
    have e : (qs.prod : ℤ) * (T * (t * invMod qs.prod b)) =
        t * T * (qs.prod * invMod qs.prod b) := by ring
    rw [e]
    simpa using Int.ModEq.mul_left ((t : ℤ) * T) h3
  · rw [← List.sum_map_mul_left]
    unfold fastSum
    refine sum_map_modEq' _ _ _ _ fun q hq => ?_
    have h3 := mul_invMod_modEq q b hb (hcb q hq)
    have h4 : (qs.prod : ℤ) = q * ((qs.prod / q : ℕ) : ℤ) := by
      exact_mod_cast (Nat.mul_div_cancel' (List.dvd_prod hq)).symm
    have e : (qs.prod : ℤ) * (tw t qs T q * invMod q b) =
        tw t qs T q * ((qs.prod / q : ℕ) : ℤ) * (q * invMod q b) := by
      conv_lhs => rw [h4]
      ring
    rw [e]
    simpa using Int.ModEq.mul_left (tw t qs T q * ((qs.prod / q : ℕ) : ℤ)) h3

/-! ### Shenoy–Kumaresan -/

/-- The CRT sum `Σ_b [F·(B/b)⁻¹]_b·(B/b)`, congruent to `F` modulo `B` and in `[0, m·B]`. -/
def skZ (bs : List ℕ) (F : ℤ) : ℤ :=
  (bs.map fun b : ℕ => (F % b * invMod (bs.prod / b) b % b) * ((bs.prod / b : ℕ) : ℤ)).sum

/-- `α = [(Z − F)·B⁻¹]_{msk}`, read as `α − msk` above `⌊msk/2⌋`. -/
def skAlpha (bs : List ℕ) (msk : ℕ) (F : ℤ) : ℤ :=
  if ((msk / 2 : ℕ) : ℤ) < (skZ bs F % msk - F % msk) * invMod bs.prod msk % msk then
    (skZ bs F % msk - F % msk) * invMod bs.prod msk % msk - msk
  else (skZ bs F % msk - F % msk) * invMod bs.prod msk % msk

/-- The integer whose residues the Shenoy–Kumaresan conversion computes: `Z − α·B`. -/
def skVal (bs : List ℕ) (msk : ℕ) (F : ℤ) : ℤ := skZ bs F - skAlpha bs msk F * bs.prod

/-- `sk1` on the residues of `F` is `skVal bs msk F mod q`. -/
theorem sk1_eq (bs : List ℕ) (msk : ℕ) (F : ℤ) (q : ℕ) :
    sk1 bs msk (bs.map fun b : ℕ => F % b) (F % msk) q = skVal bs msk F % q := by
  have hZ : ∀ m : ℕ, convSum bs (bs.map fun b : ℕ => F % b * invMod (bs.prod / b) b % b) m ≡
      skZ bs F [ZMOD m] := fun m => convSum_map bs _ m
  have hm : convSum bs (bs.map fun b : ℕ => F % b * invMod (bs.prod / b) b % b) msk % msk =
      skZ bs F % msk := hZ msk
  unfold sk1 skVal skAlpha
  simp only [digits_map, hm]
  refine Int.ModEq.sub (hZ q) (Int.ModEq.mul_left _ ?_)
  rw [Int.natCast_mod]
  exact Int.mod_modEq _ _

/-- **Shenoy–Kumaresan is exact** on values with `2·|F| ≤ B·(msk − 1 − 2m)`. -/
theorem skVal_eq_self (bs : List ℕ) (hpos : ∀ b ∈ bs, 0 < b) (hcop : bs.Pairwise Nat.Coprime)
    (msk : ℕ) (hmsk : 0 < msk) (hcm : Nat.Coprime bs.prod msk) (F : ℤ)
    (hF : 2 * |F| ≤ (bs.prod : ℤ) * ((msk : ℤ) - 1 - 2 * bs.length)) :
    skVal bs msk F = F := by
  have hB : (0 : ℤ) < bs.prod := by exact_mod_cast prod_pos' bs hpos
  have hmsk' : (0 : ℤ) < msk := by exact_mod_cast hmsk
  obtain ⟨a, ha⟩ := crtSum_dvd bs hpos hcop F
  change skZ bs F - F = bs.prod * a at ha
  obtain ⟨hz1, hz2⟩ : 0 ≤ skZ bs F ∧ skZ bs F ≤ bs.length * (bs.prod : ℤ) :=
    crtTerms_bounds bs hpos fun b => F % b * invMod (bs.prod / b) b
  -- `|a|` is small
  have ha2 : 2 * |a| ≤ (msk : ℤ) - 1 := by
    have h1 : (bs.prod : ℤ) * |a| = |skZ bs F - F| := by rw [ha, abs_mul, abs_of_pos hB]
    have h2 : |skZ bs F - F| ≤ bs.length * (bs.prod : ℤ) + |F| := by
      have := abs_sub (skZ bs F) F
      rw [abs_of_nonneg hz1] at this
      linarith
    have h3 : (bs.prod : ℤ) * (2 * |a|) ≤ bs.prod * ((msk : ℤ) - 1) := by nlinarith
    exact le_of_mul_le_mul_left h3 hB
  -- the computed `α` is `a`
  have hα : skAlpha bs msk F = a := by
    have hmod : (skZ bs F % msk - F % msk) * invMod bs.prod msk % msk ≡ a [ZMOD msk] := by
      refine (Int.mod_modEq _ _).trans ?_
      have h1 : skZ bs F % msk - F % msk ≡ bs.prod * a [ZMOD msk] := by
        rw [← ha]
        exact (Int.mod_modEq _ _).sub (Int.mod_modEq _ _)
      have h3 := mul_invMod_modEq bs.prod msk hmsk hcm
      have := h1.mul_right (invMod bs.prod msk)
      refine this.trans ?_
      have e : (bs.prod : ℤ) * a * invMod bs.prod msk = a * (bs.prod * invMod bs.prod msk) := by
        ring
      rw [e]
      simpa using Int.ModEq.mul_left a h3
    have hd : (msk : ℤ) ∣ skAlpha bs msk F - a := by
      unfold skAlpha
      split_ifs
      · have h2 := dvd_sub (Int.modEq_iff_dvd.mp hmod.symm) (dvd_refl (msk : ℤ))
        convert h2 using 1
        ring
      · exact Int.modEq_iff_dvd.mp hmod.symm
    have hlt : |skAlpha bs msk F - a| < (msk : ℤ) := by
      have h1 := Int.emod_nonneg ((skZ bs F % msk - F % msk) * invMod bs.prod msk) hmsk'.ne'
      have h2 := Int.emod_lt_of_pos ((skZ bs F % msk - F % msk) * invMod bs.prod msk) hmsk'
      have h3 := abs_le.mp (show |a| ≤ ((msk : ℤ) - 1) / 2 by omega)
      unfold skAlpha
      rw [abs_lt]
      split_ifs with h <;> constructor <;> omega
    have := Int.eq_zero_of_abs_lt_dvd hd hlt
    omega
  unfold skVal
  rw [hα]
  linarith

/-! ### Polynomials -/

variable {N : ℕ}

/-- The representative the small Montgomery reduction lifts a component to. -/
def smmrPoly (qs : List ℕ) (mt : ℕ) (a : IntPoly N) : IntPoly N :=
  ⟨fun i => smmrVal qs mt (a.coeff i)⟩

/-- The fast floor of an integer polynomial. -/
def floorPoly (t : ℕ) (qs : List ℕ) (T : IntPoly N) : IntPoly N :=
  ⟨fun i => floorVal t qs (T.coeff i)⟩

/-- **Extension**: the limbs modulo `qs ++ bsk` of the lifted representative. -/
theorem extend_toLimbs (qs bsk : List ℕ) (mt : ℕ) (hpos : ∀ q ∈ qs, 0 < q)
    (hcopq : qs.Pairwise Nat.Coprime) (hmt : 0 < mt) (hcop : Nat.Coprime qs.prod mt)
    (hb : ∀ b ∈ bsk, 0 < b ∧ Nat.Coprime mt b) (a : IntPoly N) :
    extend qs bsk mt (toLimbs qs a) = toLimbs (qs ++ bsk) (smmrPoly qs mt a) := by
  unfold extend smmrq
  rw [toLimbs_eq (qs ++ bsk), List.map_append]
  congr 1
  · rw [toLimbs_eq]
    refine List.map_congr_left fun q hq => ?_
    apply modPoly_congr
    ext i
    show ((a.coeff i : ℤ) : ZMod q) = ((smmrVal qs mt (a.coeff i) : ℤ) : ZMod q)
    rw [ZMod.intCast_eq_intCast_iff_dvd_sub]
    exact dvd_trans (by exact_mod_cast List.dvd_prod hq)
      (smmrVal_dvd qs hpos hcopq mt hmt hcop _)
  · refine List.map_congr_left fun b hb' => ?_
    ext i
    show smmrq1 qs mt (residues (toLimbs qs a) i) b = smmrVal qs mt (a.coeff i) % b
    rw [residues_toLimbs]
    exact smmrq1_eq qs mt hmt hcop b (hb b hb').1 (hb b hb').2 _

/-- **Fast floor**: the limbs modulo `bsk` of `floorPoly`. -/
theorem floorq_toLimbs (t : ℕ) (qs bsk : List ℕ) (hpos : ∀ q ∈ qs, 0 < q)
    (hcop : qs.Pairwise Nat.Coprime) (hb : ∀ b ∈ bsk, 0 < b ∧ ∀ q ∈ qs, Nat.Coprime q b)
    (T : IntPoly N) :
    floorq t qs bsk (toLimbs (qs ++ bsk) T) = toLimbs bsk (floorPoly t qs T) := by
  unfold floorq
  have e : toLimbs (qs ++ bsk) T = toLimbs qs T ++ toLimbs bsk T := List.map_append
  have hl : (toLimbs qs T).length = qs.length := List.length_map _
  rw [e, List.take_left' hl, List.drop_left' hl]
  apply List.ext_getElem
  · simp [toLimbs_eq]
  · intro n h1 h2
    have hn : n < bsk.length := by simpa [toLimbs_eq] using h2
    simp only [List.getElem_zipWith, toLimbs_eq, List.getElem_map]
    ext i
    show floor1 t qs (residues (toLimbs qs T) i) bsk[n] (T.coeff i % bsk[n]) =
      floorVal t qs (T.coeff i) % bsk[n]
    rw [residues_toLimbs]
    exact floor1_eq t qs hpos hcop _ (hb _ (List.getElem_mem hn)).1
      (hb _ (List.getElem_mem hn)).2 _

/-- **Shenoy–Kumaresan**: the limbs modulo `qs` of the converted values. -/
theorem convSK_toLimbs (qs bs : List ℕ) (msk : ℕ) (F G : IntPoly N)
    (h : ∀ i, skVal bs msk (F.coeff i) = G.coeff i) :
    convSK qs bs msk (toLimbs (bs ++ [msk]) F) = toLimbs qs G := by
  unfold convSK
  have e : toLimbs (bs ++ [msk]) F = toLimbs bs F ++ [modPoly msk F] := by
    simp [toLimbs_eq]
  have hl : (toLimbs bs F).length = bs.length := List.length_map _
  have hg : (toLimbs bs F ++ [modPoly msk F]).getD bs.length 0 = modPoly msk F := by
    rw [← hl]; simp
  rw [e, List.take_left' hl, hg, toLimbs_eq qs]
  refine List.map_congr_left fun q _ => ?_
  ext i
  show sk1 bs msk (residues (toLimbs bs F) i) (F.coeff i % msk) q = G.coeff i % q
  rw [residues_toLimbs, ← h i]
  exact sk1_eq bs msk _ q

/-! ### The side condition -/

/-- The definition of the locked `behzAuxOK?`, by `rfl` (no equation lemma of the locked
definition is realised here). -/
theorem behzAuxOK_def (t N : ℕ) (qs bs : List ℕ) (msk mt : ℕ) :
    behzAuxOK? t N qs bs msk mt =
      ((qs ++ bs ++ [msk]).all (fun m => decide (0 < m)) &&
        decide ((qs ++ bs ++ [msk]).Pairwise Nat.Coprime) &&
        (qs ++ bs ++ [msk]).all (fun m => decide (Nat.Coprime mt m)) &&
        decide (2 * bs.length + 1 ≤ msk) &&
        (BudgetBFV.behzSlack t N qs.prod bs.prod msk qs.length bs.length mt).ok) :=
  rfl

theorem behzAuxOK_iff (t N : ℕ) (qs bs : List ℕ) (msk mt : ℕ) :
    behzAuxOK? t N qs bs msk mt = true ↔
      (∀ m ∈ qs ++ bs ++ [msk], 0 < m) ∧ (qs ++ bs ++ [msk]).Pairwise Nat.Coprime ∧
        (∀ m ∈ qs ++ bs ++ [msk], Nat.Coprime mt m) ∧ 2 * bs.length + 1 ≤ msk ∧
        t * N * qs.prod * (mt + 2 * (qs.length - 1)) ^ 2 + 2 * qs.length * mt ^ 2 ≤
          mt ^ 2 * bs.prod * (msk - 1 - 2 * bs.length) ∧
        2 * (qs.length - 1) ≤ mt ∧ Nat.gcd mt qs.prod = 1 ∧ 0 < mt ∧ mt % 2 = 0 := by
  simp only [behzAuxOK_def, BudgetBFV.behzSlack, Bool.and_eq_true, List.all_eq_true,
    decide_eq_true_eq, beq_iff_eq, and_assoc]

/-- The fast floor of a tensor coefficient is small enough for Shenoy–Kumaresan. -/
theorem floor_small (t N Q k k1 R mt B : ℕ) (hQ : 0 < Q) (hmt : 0 < mt)
    (hsize : t * N * Q * (mt + 2 * k1) ^ 2 + 2 * k * mt ^ 2 ≤ mt ^ 2 * B * R)
    (Tc Ma F : ℤ) (hMa0 : 0 ≤ Ma) (hMa : 2 * mt * Ma ≤ Q * ((mt + 2 * k1 : ℕ) : ℤ))
    (hT : |Tc| ≤ 2 * (N * Ma * Ma))
    (hF1 : -(k * (Q : ℤ)) ≤ Q * F - t * Tc) (hF2 : (Q : ℤ) * F - t * Tc ≤ 0) :
    2 * |F| ≤ (B : ℤ) * R := by
  have hQ' : (0 : ℤ) < Q := by exact_mod_cast hQ
  have hmt' : (0 : ℤ) < mt := by exact_mod_cast hmt
  have hsz : (t : ℤ) * N * Q * (mt + 2 * k1) ^ 2 + 2 * k * mt ^ 2 ≤ mt ^ 2 * B * R := by
    exact_mod_cast hsize
  have h1 : (Q : ℤ) * |F| ≤ t * |Tc| + k * Q := by
    have e : (Q : ℤ) * |F| = |(Q : ℤ) * F| := by rw [abs_mul, abs_of_pos hQ']
    have e2 : (t : ℤ) * |Tc| = |(t : ℤ) * Tc| := by
      rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℤ) ≤ t)]
    rw [e, e2]
    have h := abs_add_le ((Q : ℤ) * F - t * Tc) (t * Tc)
    have h' : |(Q : ℤ) * F - t * Tc| ≤ k * Q := by
      rw [abs_le]; constructor <;> linarith
    have e3 : (Q : ℤ) * F - t * Tc + t * Tc = Q * F := by ring
    rw [e3] at h
    linarith
  have h2 : (t : ℤ) * |Tc| ≤ t * (2 * (N * Ma * Ma)) :=
    mul_le_mul_of_nonneg_left hT (by positivity)
  have hMa' : 2 * (mt : ℤ) * Ma ≤ Q * (mt + 2 * k1) := by
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using hMa
  have h3 : (2 * mt * Ma) * (2 * mt * Ma) ≤
      ((Q : ℤ) * (mt + 2 * k1)) * ((Q : ℤ) * (mt + 2 * k1)) :=
    mul_self_le_mul_self (by positivity) hMa'
  have h4 : (4 * (t : ℤ) * N) * ((2 * mt * Ma) * (2 * mt * Ma)) ≤
      (4 * (t : ℤ) * N) * (((Q : ℤ) * (mt + 2 * k1)) * ((Q : ℤ) * (mt + 2 * k1))) :=
    mul_le_mul_of_nonneg_left h3 (by positivity)
  have h5 : (8 * (mt : ℤ) ^ 2) * ((Q : ℤ) * |F|) ≤ (8 * (mt : ℤ) ^ 2) * (t * |Tc| + k * Q) :=
    mul_le_mul_of_nonneg_left h1 (by positivity)
  have h6 : (8 * (mt : ℤ) ^ 2) * ((t : ℤ) * |Tc|) ≤
      (8 * (mt : ℤ) ^ 2) * (t * (2 * (N * Ma * Ma))) :=
    mul_le_mul_of_nonneg_left h2 (by positivity)
  have h7 : (4 * (Q : ℤ)) * ((t : ℤ) * N * Q * (mt + 2 * k1) ^ 2 + 2 * k * mt ^ 2) ≤
      (4 * (Q : ℤ)) * (mt ^ 2 * B * R) := mul_le_mul_of_nonneg_left hsz (by positivity)
  have h8 : (4 * (mt : ℤ) ^ 2 * Q) * (2 * |F|) ≤ (4 * (mt : ℤ) ^ 2 * Q) * ((B : ℤ) * R) := by
    linear_combination h4 + h5 + h6 + h7
  exact le_of_mul_le_mul_left h8 (by positivity)

/-! ### The component-level theorem -/

/-- The integer representatives `behzMul` multiplies: the small Montgomery lift of every
component. -/
def behzLift (qs : List ℕ) (mt : ℕ) (c : List (IntPoly N)) : List (IntPoly N) :=
  c.map (smmrPoly qs mt)

/-- The integer polynomials `behzMul` computes modulo `Q`: the fast floor of every component of
the integer tensor product of the lifts. -/
def behzFloor (t : ℕ) (qs : List ℕ) (A B : List (IntPoly N)) : List (IntPoly N) :=
  (Challenge.Source.tensor A B).map (floorPoly t qs)

/-- The lifts are representatives of the operand's components modulo `Q`. -/
theorem behzLift_congr (qs : List ℕ) (hpos : ∀ q ∈ qs, 0 < q) (hcopq : qs.Pairwise Nat.Coprime)
    (mt : ℕ) (hmt : 0 < mt) (hcop : Nat.Coprime qs.prod mt) (c : List (IntPoly N)) :
    (behzLift qs mt c).map (ofInt qs.prod) = c.map (ofInt qs.prod) := by
  unfold behzLift
  rw [List.map_map]
  refine List.map_congr_left fun a _ => ?_
  ext i
  show ((smmrVal qs mt (a.coeff i) : ℤ) : ZMod qs.prod) = ((a.coeff i : ℤ) : ZMod qs.prod)
  symm
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub]
  exact smmrVal_dvd qs hpos hcopq mt hmt hcop _

/-- `2·m̃·|A| ≤ Q·(m̃ + 2(k−1))`, coefficient by coefficient. -/
theorem smmrPoly_bound (qs : List ℕ) (hpos : ∀ q ∈ qs, 0 < q) (mt : ℕ) (hmt : 0 < mt)
    (heven : mt % 2 = 0) (hcop : Nat.Coprime qs.prod mt) (a : IntPoly N) (i : Fin N) :
    2 * ((mt : ℤ) * |(smmrPoly qs mt a).coeff i|) ≤
      qs.prod * ((mt + 2 * (qs.length - 1) : ℕ) : ℤ) :=
  smmrVal_bounds qs hpos mt hmt heven hcop _

/-- **The lift excess**: `2·‖A‖∞ ≤ Q + ⌈2(k−1)·Q/m̃⌉`. -/
theorem smmrPoly_norm (qs : List ℕ) (hpos : ∀ q ∈ qs, 0 < q) (mt : ℕ) (hmt : 0 < mt)
    (heven : mt % 2 = 0) (hcop : Nat.Coprime qs.prod mt) (a : IntPoly N) :
    2 * normInf (smmrPoly qs mt a) ≤
      qs.prod + BudgetBFV.ceilDiv (2 * (qs.length - 1) * qs.prod) mt := by
  have hle : normInf (smmrPoly qs mt a) ≤
      (qs.prod + BudgetBFV.ceilDiv (2 * (qs.length - 1) * qs.prod) mt) / 2 := by
    rw [normInf_le_iff]
    intro i
    have h := smmrPoly_bound qs hpos mt hmt heven hcop a i
    rw [← Int.natCast_natAbs] at h ⊢
    have h' : 2 * (mt * ((smmrPoly qs mt a).coeff i).natAbs) ≤
        qs.prod * (mt + 2 * (qs.length - 1)) := by exact_mod_cast h
    generalize ((smmrPoly qs mt a).coeff i).natAbs = n at h' ⊢
    have hn : 2 * n ≤ qs.prod + BudgetBFV.ceilDiv (2 * (qs.length - 1) * qs.prod) mt := by
      unfold BudgetBFV.ceilDiv
      rcases Nat.le_total (2 * n) qs.prod with hq | hq
      · exact le_trans hq (Nat.le_add_right _ _)
      · have h1 : (2 * n - qs.prod) * mt ≤ 2 * (qs.length - 1) * qs.prod := by
          rw [Nat.sub_mul]
          have : 2 * n * mt ≤ qs.prod * mt + 2 * (qs.length - 1) * qs.prod := by nlinarith
          omega
        have h2 : 2 * n - qs.prod ≤ 2 * (qs.length - 1) * qs.prod / mt :=
          (Nat.le_div_iff_mul_le hmt).mpr h1
        have h3 : 2 * (qs.length - 1) * qs.prod / mt ≤
            (2 * (qs.length - 1) * qs.prod + mt - 1) / mt :=
          Nat.div_le_div_right (by omega)
        omega
    exact_mod_cast (show n ≤ _ by omega)
  omega

/-- **The rounding slack**: `2·|Q·F − t·T| ≤ Q·2k` for every coefficient of every component. -/
theorem behzFloor_round (t : ℕ) (qs : List ℕ) (hpos : ∀ q ∈ qs, 0 < q)
    (hcop : qs.Pairwise Nat.Coprime) (A B : List (IntPoly N)) (j : ℕ) (i : Fin N) :
    2 * |(qs.prod : ℤ) * ((behzFloor t qs A B).getD j 0).coeff i -
        (t : ℤ) * ((Challenge.Source.tensor A B).getD j 0).coeff i| ≤
      (qs.prod : ℤ) * ((2 * qs.length : ℕ) : ℤ) := by
  unfold behzFloor
  generalize Challenge.Source.tensor A B = L
  have hQ : (0 : ℤ) < qs.prod := by exact_mod_cast prod_pos' qs hpos
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases L[j]? with
  | none =>
    simp only [Option.map_none, Option.getD_none, coeff_zero', mul_zero, sub_zero, abs_zero]
    positivity
  | some T =>
    simp only [Option.map_some, Option.getD_some]
    obtain ⟨h1, h2⟩ := floorVal_bounds t qs hpos hcop (T.coeff i)
    show 2 * |(qs.prod : ℤ) * floorVal t qs (T.coeff i) - (t : ℤ) * T.coeff i| ≤ _
    rw [Nat.cast_mul, Nat.cast_ofNat, abs_of_nonpos h2]
    linarith

/-- **BEHZ multiplication computes the fast floor of the tensor product of the lifts**, with
representatives in `[0, Q)`. -/
theorem behzMul_eq (t : ℕ) (qs bs : List ℕ) (msk mt : ℕ)
    (haux : behzAuxOK? t N qs bs msk mt = true)
    (c d : List (IntPoly N)) (hc : c.length = 2) (hd : d.length = 2) :
    behzMul t qs bs msk mt c d =
      (behzFloor t qs (behzLift qs mt c) (behzLift qs mt d)).map (modPoly qs.prod) := by
  obtain ⟨hpos, hcop, hcmt, hmsk, hsize, -, hgcd, hmt, heven⟩ :=
    (behzAuxOK_iff t N qs bs msk mt).mp haux
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
  have hQ : 0 < qs.prod := prod_pos' qs hposq
  obtain ⟨R, hR⟩ : ∃ R : ℕ, msk = R + 1 + 2 * bs.length := ⟨msk - 1 - 2 * bs.length, by omega⟩
  have hRsub : msk - 1 - 2 * bs.length = R := by omega
  rw [hRsub] at hsize
  obtain ⟨a₀, a₁, rfl⟩ := List.length_eq_two.mp hc
  obtain ⟨b₀, b₁, rfl⟩ := List.length_eq_two.mp hd
  unfold behzMul behzFloor behzLift
  simp only [List.map_cons, List.map_nil,
    extend_toLimbs qs (bs ++ [msk]) mt hposq hcopq hmt hQmt
      (fun b hb => ⟨hposk b hb, hcmt b (List.mem_append_right _ hb)⟩),
    tensor_toLimbs, List.map_map]
  refine List.map_congr_left fun T hT => ?_
  -- the size of the tensor coefficients
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
  have hb : ∀ i, |T.coeff i| ≤ 2 * (N * (W / (2 * mt)) * (W / (2 * mt))) := by
    intro i
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
  have hsmall : ∀ i, 2 * |(floorPoly t qs T).coeff i| ≤
      (bs.prod : ℤ) * ((msk : ℤ) - 1 - 2 * bs.length) := by
    intro i
    obtain ⟨h1, h2⟩ := floorVal_bounds t qs hposq hcopq (T.coeff i)
    have := floor_small t N qs.prod qs.length (qs.length - 1) R mt bs.prod hQ hmt
      hsize (T.coeff i) (W / (2 * mt)) (floorVal t qs (T.coeff i)) hMa0 (hW ▸ hMa) (hb i) h1 h2
    have e : ((msk : ℤ) - 1 - 2 * bs.length) = R := by rw [hR]; push_cast; ring
    rw [e]
    exact this
  show reconstruct qs (convSK qs bs msk (floorq t qs (bs ++ [msk])
      (toLimbs (qs ++ (bs ++ [msk])) T))) = modPoly qs.prod (floorPoly t qs T)
  rw [floorq_toLimbs t qs (bs ++ [msk]) hposq hcopq
      (fun b hb => ⟨hposk b hb, fun q hq => hcopqk q hq b hb⟩),
    convSK_toLimbs qs bs msk _ (floorPoly t qs T)
      (fun i => skVal_eq_self bs hposb hcopb msk hmsk0 hcopbm _ (hsmall i)),
    reconstruct_toLimbs qs hposq hcopq]

/-- `behzMul_eq` modulo `Q`. -/
theorem behzMul_congr (t : ℕ) (qs bs : List ℕ) (msk mt : ℕ)
    (haux : behzAuxOK? t N qs bs msk mt = true)
    (c d : List (IntPoly N)) (hc : c.length = 2) (hd : d.length = 2) :
    (behzMul t qs bs msk mt c d).map (ofInt qs.prod) =
      (behzFloor t qs (behzLift qs mt c) (behzLift qs mt d)).map (ofInt qs.prod) := by
  rw [behzMul_eq t qs bs msk mt haux c d hc hd, List.map_map]
  exact List.map_congr_left fun a _ => ofInt_modPoly _ _

/-- **BEHZ multiplication, component by component** (the hypotheses of
`Challenge.BFVMul.stepOK_mul_lifted`). Under `behzAuxOK?`, for two-component operands `c`, `d`
there are integer representatives `A`, `B` of their components modulo `Q` with
`2·‖Aᵢ‖∞, 2·‖Bᵢ‖∞ ≤ Q + e`, `e = ⌈2(k−1)·Q/m̃⌉`, and integer polynomials `X₀, X₁, X₂` with
`2·|Q·Xⱼ − t·(A ⊗ B)ⱼ| ≤ Q·2k` coefficientwise, to which the result of `behzMul` is congruent
modulo `Q`. (`e` and `2k` are the fields of `Spec.BudgetBFV.behzSlack`; the witnesses are
`behzLift` and `behzFloor`.) -/
theorem behzMul_lifted (t : ℕ) (qs bs : List ℕ) (msk mt : ℕ)
    (haux : behzAuxOK? t N qs bs msk mt = true)
    (c d : List (IntPoly N)) (hc : c.length = 2) (hd : d.length = 2) :
    ∃ A B X : List (IntPoly N), A.length = 2 ∧ B.length = 2 ∧ X.length = 3 ∧
      A.map (ofInt qs.prod) = c.map (ofInt qs.prod) ∧
      B.map (ofInt qs.prod) = d.map (ofInt qs.prod) ∧
      (∀ p ∈ A, 2 * normInf p ≤ qs.prod +
        (BudgetBFV.behzSlack t N qs.prod bs.prod msk qs.length bs.length mt).e) ∧
      (∀ p ∈ B, 2 * normInf p ≤ qs.prod +
        (BudgetBFV.behzSlack t N qs.prod bs.prod msk qs.length bs.length mt).e) ∧
      (∀ (j : ℕ) (i : Fin N),
        2 * |(qs.prod : ℤ) * (X.getD j 0).coeff i -
            (t : ℤ) * ((Challenge.Source.tensor A B).getD j 0).coeff i| ≤
          (qs.prod : ℤ) *
            ((BudgetBFV.behzSlack t N qs.prod bs.prod msk qs.length bs.length mt).rho : ℕ)) ∧
      (behzMul t qs bs msk mt c d).map (ofInt qs.prod) = X.map (ofInt qs.prod) := by
  obtain ⟨hpos, hcop, -, -, -, -, hgcd, hmt, heven⟩ := (behzAuxOK_iff t N qs bs msk mt).mp haux
  rw [List.append_assoc] at hpos hcop
  have hposq : ∀ q ∈ qs, 0 < q := fun q hq => hpos q (List.mem_append_left _ hq)
  have hcopq : qs.Pairwise Nat.Coprime := (List.pairwise_append.mp hcop).1
  have hQmt : Nat.Coprime qs.prod mt := Nat.Coprime.symm hgcd
  have hnorm : ∀ (l : List (IntPoly N)), ∀ p ∈ behzLift qs mt l, 2 * normInf p ≤ qs.prod +
      (BudgetBFV.behzSlack t N qs.prod bs.prod msk qs.length bs.length mt).e := by
    intro l p hp
    obtain ⟨a, -, rfl⟩ := List.mem_map.mp hp
    exact smmrPoly_norm qs hposq mt hmt heven hQmt a
  refine ⟨behzLift qs mt c, behzLift qs mt d,
    behzFloor t qs (behzLift qs mt c) (behzLift qs mt d), by simp [behzLift, hc],
    by simp [behzLift, hd], ?_, behzLift_congr qs hposq hcopq mt hmt hQmt c,
    behzLift_congr qs hposq hcopq mt hmt hQmt d, hnorm c, hnorm d,
    behzFloor_round t qs hposq hcopq _ _, behzMul_congr t qs bs msk mt haux c d hc hd⟩
  obtain ⟨a₀, a₁, rfl⟩ := List.length_eq_two.mp hc
  obtain ⟨b₀, b₁, rfl⟩ := List.length_eq_two.mp hd
  rfl

end FHE.BFV.MulBEHZ
