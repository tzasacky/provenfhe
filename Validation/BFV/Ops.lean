import Validation.BFV.Core

/-!
# Validation.BFV.Ops — BFV noise of the linear operations, modulus switching, and decryption

Phase-level lemmas, one per rule of `Challenge.BFV.refBoundBFV` (all but `mul`/`square`, which
are in `Validation.BFV.Mul`), and the decryption condition. `r = Q % t` throughout.
-/

namespace Validation.BFV
open Spec NPoly Scheme
open Validation.Ring Validation.Scheme Validation.Source

variable {N : ℕ}

/-! ### Helpers -/

/-- The representatives in `[0, t)` of a plaintext, as an integer polynomial. -/
def lift {t : ℕ} (m : Poly t N) : IntPoly N := ⟨fun i => ((m.coeff i).val : ℤ)⟩

@[simp] theorem coeff_lift {t : ℕ} (m : Poly t N) (i : Fin N) :
    (lift m).coeff i = ((m.coeff i).val : ℤ) := rfl

theorem ofInt_lift {t : ℕ} (ht : 0 < t) (m : Poly t N) : ofInt t (lift m) = m := by
  have : NeZero t := ⟨ht.ne'⟩
  ext i
  simp only [coeff_ofInt, coeff_lift, Int.cast_natCast]
  exact ZMod.natCast_zmod_val _

theorem lift_nonneg {t : ℕ} (m : Poly t N) (i : Fin N) : 0 ≤ (lift m).coeff i := by
  simp

theorem lift_lt {t : ℕ} (ht : 0 < t) (m : Poly t N) (i : Fin N) : (lift m).coeff i < t := by
  have : NeZero t := ⟨ht.ne'⟩
  simp only [coeff_lift]
  exact_mod_cast ZMod.val_lt (m.coeff i)

theorem abs_lift_le {t : ℕ} (ht : 0 < t) (m : Poly t N) (i : Fin N) :
    |(lift m).coeff i| ≤ (t : ℤ) - 1 := by
  rw [abs_of_nonneg (lift_nonneg m i)]
  have := lift_lt ht m i
  linarith

/-- `noiseLe_elim` in the shape `noiseLe_intro` consumes. -/
theorem noiseLe_elim' {t B Q : ℕ} {φ : Poly Q N} {m : Poly t N} (h : NoiseLe t B φ m) :
    ∃ e : IntPoly N, (∀ i, |e.coeff i| ≤ B) ∧
      φ = ofInt Q (⟨fun i => ((Q / t : ℕ) : ℤ) * (lift m).coeff i⟩ + e) := by
  obtain ⟨e, he, hφ⟩ := noiseLe_elim h
  refine ⟨e, he, ?_⟩
  rw [hφ]
  ext i
  simp [scaled]

theorem automorph_scale (g : ℕ) (c : ℤ) (a : IntPoly N) :
    automorph g (⟨fun i => c * a.coeff i⟩ : IntPoly N) = ⟨fun i => c * (automorph g a).coeff i⟩ := by
  ext k
  simp only [coeff_automorph', Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> simp

theorem scale_eq_const_mul (c : ℤ) (a : IntPoly N) :
    (⟨fun i => c * a.coeff i⟩ : IntPoly N) = const c * a := by
  ext i; rw [coeff_const_mul]

/-- Rounding step of BFV decryption under the sharp hypothesis. -/
theorem roundDiv_bfv' (t Q B : ℕ) (mv : ℕ) (hm : mv < t) (e j : ℤ) (he : |e| ≤ B)
    (hB : 2 * (t * B + Q % t * (t - 1)) < Q) :
    roundDiv (t * (((Q / t * mv : ℕ) : ℤ) + e + Q * j)) Q = mv + t * j := by
  unfold roundDiv
  have hdiv := Nat.div_add_mod Q t
  obtain ⟨u, rfl⟩ : ∃ u, t = u + 1 := ⟨t - 1, by omega⟩
  rw [Nat.add_sub_cancel] at hB
  set D := Q / (u + 1)
  set r := Q % (u + 1)
  have hBz : 2 * (((u : ℤ) + 1) * B + r * u) < Q := by exact_mod_cast hB
  have hD : ((u : ℤ) + 1) * D = Q - r := by
    have : (((u + 1) * D + r : ℕ) : ℤ) = Q := by exact_mod_cast hdiv
    push_cast at this; linarith
  have hmz : (mv : ℤ) ≤ u := by exact_mod_cast Nat.lt_succ_iff.mp hm
  have hm0 : (0 : ℤ) ≤ mv := by positivity
  have hr0 : (0 : ℤ) ≤ r := by positivity
  have hu0 : (0 : ℤ) ≤ u := by positivity
  have hB0 : (0 : ℤ) ≤ B := by positivity
  have hQ : (0 : ℤ) < Q := by nlinarith
  obtain ⟨he1, he2⟩ := abs_le.mp he
  have hrm : (r : ℤ) * mv ≤ r * u := mul_le_mul_of_nonneg_left hmz hr0
  have hrm0 : (0 : ℤ) ≤ r * mv := mul_nonneg hr0 hm0
  have hte1 : -(((u : ℤ) + 1) * B) ≤ ((u : ℤ) + 1) * e := by nlinarith
  have hte2 : ((u : ℤ) + 1) * e ≤ ((u : ℤ) + 1) * B := by nlinarith
  set X : ℤ := Q - 2 * r * mv + 2 * ((u : ℤ) + 1) * e with hXdef
  have hX0 : 0 ≤ X := by rw [hXdef]; nlinarith
  have hX1 : X < 2 * Q := by rw [hXdef]; nlinarith
  have heq : 2 * (((u + 1 : ℕ) : ℤ) * (((D * mv : ℕ) : ℤ) + e + Q * j)) + Q
      = X + 2 * Q * (mv + ((u + 1 : ℕ) : ℤ) * j) := by
    push_cast
    have : ((u : ℤ) + 1) * (D * mv) = (Q - r) * mv := by rw [← mul_assoc, hD]
    rw [hXdef]
    linear_combination 2 * this
  rw [heq, Int.add_mul_ediv_left _ _ (by positivity), Int.ediv_eq_zero_of_lt hX0 hX1, zero_add]

/-- The integer arithmetic of BFV modulus switching, one coefficient. -/
theorem modSwitch_arith (t Q' q B E v : ℕ) (ht : 0 < t) (hq : 0 < q) (hv : v < t)
    (e δ Φ k X : ℤ) (he : |e| ≤ B) (hδ : |δ| ≤ ((q * E : ℕ) : ℤ))
    (hΦ : Φ = ((Q' * q / t * v : ℕ) : ℤ) + e + ((Q' * q : ℕ) : ℤ) * k)
    (hX : (q : ℤ) * X = Φ + δ) :
    |X - ((Q' / t * v : ℕ) : ℤ) - Q' * k| ≤ ((B / q + E + Q' % t : ℕ) : ℤ) := by
  have h1 := Nat.div_add_mod (Q' * q) t
  have h2 := Nat.div_add_mod Q' t
  have hle : q * (Q' / t) ≤ Q' * q / t := by
    rw [Nat.le_div_iff_mul_le ht]
    calc q * (Q' / t) * t = q * (Q' / t * t) := by ring
      _ ≤ q * Q' := Nat.mul_le_mul_left _ (Nat.div_mul_le_self _ _)
      _ = Q' * q := by ring
  have h3 := Nat.div_add_mod B q
  have h4 := Nat.mod_lt B hq
  set D := Q' * q / t
  set r := Q' * q % t
  set D' := Q' / t
  set r' := Q' % t
  set Bq := B / q
  set Br := B % q
  have h1z : (t : ℤ) * D + r = Q' * q := by exact_mod_cast h1
  have h2z : (t : ℤ) * D' + r' = Q' := by exact_mod_cast h2
  have h3z : (q : ℤ) * Bq + Br = B := by exact_mod_cast h3
  have h4z : (Br : ℤ) < q := by exact_mod_cast h4
  have hlez : (q : ℤ) * D' ≤ D := by exact_mod_cast hle
  have hvz : (v : ℤ) ≤ t := by exact_mod_cast hv.le
  have hv0 : (0 : ℤ) ≤ v := by positivity
  have hr0 : (0 : ℤ) ≤ r := by positivity
  have hqz : (0 : ℤ) < q := by exact_mod_cast hq
  obtain ⟨c, hc⟩ : ∃ c : ℤ, c = D - q * D' := ⟨_, rfl⟩
  have hc0 : 0 ≤ c := by linarith
  have hct : c * t = q * r' - r := by
    rw [hc]; linear_combination h1z - (q : ℤ) * h2z
  have hcv0 : 0 ≤ c * v := mul_nonneg hc0 hv0
  have hcv : c * v ≤ q * r' := by
    have : c * v ≤ c * t := mul_le_mul_of_nonneg_left hvz hc0
    linarith
  obtain ⟨Y, hY⟩ : ∃ Y : ℤ, Y = X - ((D' * v : ℕ) : ℤ) - Q' * k := ⟨_, rfl⟩
  have hqY : (q : ℤ) * Y = e + δ + c * v := by
    rw [hY, hc]; push_cast
    rw [hΦ] at hX; push_cast at hX
    linear_combination hX
  obtain ⟨he1, he2⟩ := abs_le.mp he
  obtain ⟨hd1, hd2⟩ := abs_le.mp hδ
  rw [← hY]
  push_cast at hd1 hd2 ⊢
  rw [abs_le]
  constructor
  · by_contra hcon
    rw [not_le] at hcon
    have : (q : ℤ) * Y ≤ q * (-(Bq + E + r') - 1) :=
      mul_le_mul_of_nonneg_left (by linarith) hqz.le
    nlinarith
  · by_contra hcon
    rw [not_le] at hcon
    have : (q : ℤ) * (Bq + E + r' + 1) ≤ q * Y :=
      mul_le_mul_of_nonneg_left (by linarith) hqz.le
    nlinarith

theorem noiseLe_mono' {t B B' Q : ℕ} {φ : Poly Q N} {m : Poly t N} (h : NoiseLe t B φ m)
    (hB : B ≤ B') : NoiseLe t B' φ m := le_trans h hB

/-- Adding `Δ·P + δ` for an integer polynomial `P` with `‖P‖∞ ≤ b`. -/
theorem noiseLe_addInt {t B b E Q : ℕ} (ht : 0 < t) (hQ : 0 < Q) {φ : Poly Q N}
    {m : Poly t N} (P δ : IntPoly N) (h : NoiseLe t B φ m) (hP : ∀ i, |P.coeff i| ≤ b)
    (hδ : ∀ i, |δ.coeff i| ≤ E) :
    NoiseLe t (B + Q % t * ((b + t - 1) / t) + E)
      (φ + ofInt Q ⟨fun i => ((Q / t : ℕ) : ℤ) * P.coeff i⟩ + ofInt Q δ) (m + ofInt t P) := by
  obtain ⟨e, he, hφ⟩ := noiseLe_elim' h
  refine noiseLe_mono' (noiseLe_intro ht hQ (lift m + P) (e + δ) ((b + t - 1) / t) (B + E)
    ?_ ?_ ?_ ?_) (le_of_eq (by ring))
  · rw [hφ]; ext i; simp; ring
  · rw [ofInt_add, ofInt_lift ht]
  · intro i
    have h0 := lift_nonneg m i
    have h1 := lift_lt ht m i
    obtain ⟨hp1, hp2⟩ := abs_le.mp (hP i)
    have hd := Nat.div_add_mod (b + t - 1) t
    have hmod := Nat.mod_lt (b + t - 1) ht
    have hsub := Nat.sub_add_cancel (show 1 ≤ b + t by omega)
    generalize (b + t - 1) / t = κ at hd ⊢
    generalize (b + t - 1) % t = ρ at hd hmod
    generalize b + t - 1 = w at hd hsub
    have hk1 : b ≤ κ * t := by nlinarith
    have hk2 : b + t ≤ (κ + 1) * t := by nlinarith
    have hk1z : (b : ℤ) ≤ ((κ * t : ℕ) : ℤ) := by exact_mod_cast hk1
    have hk2z : (b : ℤ) + t ≤ (((κ + 1) * t : ℕ) : ℤ) := by exact_mod_cast hk2
    rw [coeff_add']
    constructor <;> linarith
  · intro i
    rw [coeff_add']; push_cast
    exact (abs_add_le _ _).trans (add_le_add (he i) (hδ i))

/-! ### The rules -/

/-- Decryption: noise `B` with `2·(t·B + r·(t−1)) < Q` decrypts to `m`. -/
theorem decrypt_of_noiseLe {t B Q : ℕ} (ht : 0 < t) {φ : Poly Q N} {m : Poly t N}
    (h : NoiseLe t B φ m) (hB : 2 * (t * B + Q % t * (t - 1)) < Q) :
    (⟨fun i => (roundDiv (t * (centered φ).coeff i) Q : ZMod t)⟩ : Poly t N) = m := by
  have : NeZero t := ⟨ht.ne'⟩
  obtain ⟨e, he, hφ⟩ := noiseLe_elim h
  ext i
  simp only [coeff_centered]
  rw [hφ]
  simp only [coeff_ofInt, coeff_add', scaled]
  set v : ℤ := ((Q / t * (m.coeff i).val : ℕ) : ℤ) + e.coeff i
  obtain ⟨j, hj⟩ := exists_eq_add_mul_of_cast_eq (Q := Q)
    (a := ((v : ZMod Q)).valMinAbs) (b := v) (ZMod.coe_valMinAbs _)
  rw [hj, roundDiv_bfv' t Q B _ (ZMod.val_lt _) _ _ (he i) hB]
  push_cast
  rw [ZMod.natCast_self, zero_mul, add_zero, ZMod.natCast_zmod_val]

theorem noiseLe_mono {t B B' Q : ℕ} {φ : Poly Q N} {m : Poly t N} (h : NoiseLe t B φ m)
    (hB : B ≤ B') : NoiseLe t B' φ m := noiseLe_mono' h hB

theorem noiseLe_add {t B₁ B₂ Q : ℕ} (ht : 0 < t) (hQ : 0 < Q) {φ₁ φ₂ : Poly Q N}
    {m₁ m₂ : Poly t N} (h₁ : NoiseLe t B₁ φ₁ m₁) (h₂ : NoiseLe t B₂ φ₂ m₂) :
    NoiseLe t (B₁ + B₂ + Q % t) (φ₁ + φ₂) (m₁ + m₂) := by
  obtain ⟨e₁, he₁, hφ₁⟩ := noiseLe_elim' h₁
  obtain ⟨e₂, he₂, hφ₂⟩ := noiseLe_elim' h₂
  refine noiseLe_mono' (noiseLe_intro ht hQ (lift m₁ + lift m₂) (e₁ + e₂) 1 (B₁ + B₂)
    ?_ ?_ ?_ ?_) (le_of_eq (by ring))
  · rw [hφ₁, hφ₂]; ext i; simp; ring
  · rw [ofInt_add, ofInt_lift ht, ofInt_lift ht]
  · intro i
    have := lift_nonneg m₁ i
    have := lift_nonneg m₂ i
    have := lift_lt ht m₁ i
    have := lift_lt ht m₂ i
    rw [coeff_add']; push_cast
    constructor <;> linarith
  · intro i
    rw [coeff_add']; push_cast
    exact (abs_add_le _ _).trans (add_le_add (he₁ i) (he₂ i))

theorem noiseLe_sub {t B₁ B₂ Q : ℕ} (ht : 0 < t) (hQ : 0 < Q) {φ₁ φ₂ : Poly Q N}
    {m₁ m₂ : Poly t N} (h₁ : NoiseLe t B₁ φ₁ m₁) (h₂ : NoiseLe t B₂ φ₂ m₂) :
    NoiseLe t (B₁ + B₂ + Q % t) (φ₁ - φ₂) (m₁ - m₂) := by
  obtain ⟨e₁, he₁, hφ₁⟩ := noiseLe_elim' h₁
  obtain ⟨e₂, he₂, hφ₂⟩ := noiseLe_elim' h₂
  refine noiseLe_mono' (noiseLe_intro ht hQ (lift m₁ - lift m₂) (e₁ - e₂) 1 (B₁ + B₂)
    ?_ ?_ ?_ ?_) (le_of_eq (by ring))
  · rw [hφ₁, hφ₂]; ext i; simp; ring
  · rw [ofInt_sub, ofInt_lift ht, ofInt_lift ht]
  · intro i
    have := lift_nonneg m₁ i
    have := lift_nonneg m₂ i
    have := lift_lt ht m₁ i
    have := lift_lt ht m₂ i
    rw [coeff_sub']; push_cast
    constructor <;> linarith
  · intro i
    rw [coeff_sub']; push_cast
    exact (abs_sub _ _).trans (add_le_add (he₁ i) (he₂ i))

theorem noiseLe_addPlain {t B b E Q : ℕ} (ht : 0 < t) (hQ : 0 < Q) {φ p : Poly Q N}
    {m mp : Poly t N} (δ : IntPoly N) (h : NoiseLe t B φ m) (hp : PlainLe t b p mp)
    (hδ : normInf δ ≤ E) :
    NoiseLe t (B + Q % t * ((b + t - 1) / t) + E)
      (φ + ((Q / t : ℕ) : ZMod Q) • p + ofInt Q δ) (m + mp) := by
  obtain ⟨hmp, hpb⟩ := hp
  have key := noiseLe_addInt (E := E) ht hQ (centered p) δ h hpb ((normInf_le_iff _ _).mp hδ)
  rw [hmp] at key
  have e1 : ((Q / t : ℕ) : ZMod Q) • p
      = ofInt Q ⟨fun i => ((Q / t : ℕ) : ℤ) * (centered p).coeff i⟩ := by
    ext i
    simp only [coeff_smul', coeff_ofInt, coeff_centered]
    rw [Int.cast_mul, ZMod.coe_valMinAbs, Int.cast_natCast]
  rw [e1]; exact key

theorem noiseLe_subPlain {t B b E Q : ℕ} (ht : 0 < t) (hQ : 0 < Q) {φ p : Poly Q N}
    {m mp : Poly t N} (δ : IntPoly N) (h : NoiseLe t B φ m) (hp : PlainLe t b p mp)
    (hδ : normInf δ ≤ E) :
    NoiseLe t (B + Q % t * ((b + t - 1) / t) + E)
      (φ - ((Q / t : ℕ) : ZMod Q) • p + ofInt Q δ) (m - mp) := by
  obtain ⟨hmp, hpb⟩ := hp
  have key := noiseLe_addInt (E := E) ht hQ (-centered p) δ h
    (fun i => by rw [coeff_neg', abs_neg]; exact hpb i) ((normInf_le_iff _ _).mp hδ)
  rw [ofInt_neg, hmp] at key
  have e1 : φ - ((Q / t : ℕ) : ZMod Q) • p
      = φ + ofInt Q ⟨fun i => ((Q / t : ℕ) : ℤ) * (-centered p).coeff i⟩ := by
    ext i
    simp only [coeff_sub', coeff_add', coeff_smul', coeff_ofInt, coeff_neg', coeff_centered]
    rw [Int.cast_mul, Int.cast_neg, ZMod.coe_valMinAbs, Int.cast_natCast]
    ring
  have e2 : m - mp = m + -mp := by
    ext i; simp [sub_eq_add_neg]
  rw [e1, e2]; exact key

theorem noiseLe_mulPlain {t B b Q : ℕ} (ht : 0 < t) (hQ : 0 < Q) {φ p : Poly Q N}
    {m mp : Poly t N} (h : NoiseLe t B φ m) (hp : PlainLe t b p mp) :
    NoiseLe t (N * b * (B + Q % t)) (φ * p) (m * mp) := by
  obtain ⟨hmp, hpb⟩ := hp
  obtain ⟨e, he, hφ⟩ := noiseLe_elim' h
  refine noiseLe_mono' (noiseLe_intro ht hQ (lift m * centered p) (e * centered p) (N * b)
    (N * B * b) ?_ ?_ ?_ ?_) (le_of_eq (by ring))
  · rw [hφ]
    conv_lhs => rw [← ofInt_centered p]
    rw [← ofInt_mul]
    congr 1
    rw [scale_eq_const_mul, scale_eq_const_mul]
    apply eq_of_neZero; intro; ring
  · rw [ofInt_mul, ofInt_lift ht, hmp]
  · intro i
    have hb := abs_coeff_mul_le_N (lift m) (centered p) ((t : ℤ) - 1) b (abs_lift_le ht m) hpb i
    obtain ⟨h1, h2⟩ := abs_le.mp hb
    have htz : (1 : ℤ) ≤ t := by exact_mod_cast ht
    have hNb : (0 : ℤ) ≤ (N : ℤ) * b := by positivity
    push_cast
    constructor <;> nlinarith
  · intro i
    have := abs_coeff_mul_le_N e (centered p) B b he hpb i
    push_cast
    exact this

theorem noiseLe_mulConst {t B Q : ℕ} (ht : 0 < t) (hQ : 0 < Q) {φ : Poly Q N} {m : Poly t N}
    (c : ℤ) (h : NoiseLe t B φ m) :
    NoiseLe t (c.natAbs * (B + Q % t)) ((c : ZMod Q) • φ) ((c : ZMod t) • m) := by
  obtain ⟨e, he, hφ⟩ := noiseLe_elim' h
  refine noiseLe_mono' (noiseLe_intro ht hQ ⟨fun i => c * (lift m).coeff i⟩
    ⟨fun i => c * e.coeff i⟩ c.natAbs (c.natAbs * B) ?_ ?_ ?_ ?_) (le_of_eq (by ring))
  · rw [hφ]; ext i; simp; ring
  · conv_rhs => rw [← ofInt_lift ht m]
    ext i; simp
  · intro i
    have h0 := lift_nonneg m i
    have h1 := lift_lt ht m i
    have hc : |c * (lift m).coeff i| ≤ |c| * ((t : ℤ) - 1) := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (abs_lift_le ht m i) (abs_nonneg _)
    obtain ⟨h2, h3⟩ := abs_le.mp hc
    have hc0 := abs_nonneg c
    have htz : (1 : ℤ) ≤ t := by exact_mod_cast ht
    push_cast
    constructor <;> nlinarith
  · intro i
    show |c * e.coeff i| ≤ ((c.natAbs * B : ℕ) : ℤ)
    push_cast
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (he i) (abs_nonneg _)

theorem noiseLe_automorph {t B Q : ℕ} (ht : 0 < t) (hQ : 0 < Q) (hN : ∃ k, N = 2 ^ k)
    {g : ℕ} (hg : g % 2 = 1) {φ : Poly Q N} {m : Poly t N} (h : NoiseLe t B φ m) :
    NoiseLe t (B + Q % t) (automorph g φ) (automorph g m) := by
  obtain ⟨e, he, hφ⟩ := noiseLe_elim' h
  refine noiseLe_mono' (noiseLe_intro ht hQ (automorph g (lift m)) (automorph g e) 1 B
    ?_ ?_ ?_ ?_) (le_of_eq (by ring))
  · rw [hφ, ← ofInt_automorph, automorph_add, automorph_scale]
  · rw [ofInt_automorph, ofInt_lift ht]
  · intro i
    have hb := abs_coeff_automorph_le hN hg (lift m) ((t : ℤ) - 1) (abs_lift_le ht m) i
    obtain ⟨h1, h2⟩ := abs_le.mp hb
    push_cast
    constructor <;> linarith
  · exact abs_coeff_automorph_le hN hg e B he

theorem noiseLe_keySwitch {t B E Q : ℕ} (hQ : 0 < Q) {φ : Poly Q N} {m : Poly t N}
    (e : IntPoly N) (h : NoiseLe t B φ m) (he : normInf e ≤ E) :
    NoiseLe t (B + E) (φ + ofInt Q e) m := by
  obtain ⟨e₀, he₀, hφ⟩ := noiseLe_elim h
  refine noiseLe_of_eq hQ (e₀ + e) ?_ ?_
  · rw [hφ]; ext i; simp; ring
  · intro i
    rw [coeff_add']; push_cast
    exact (abs_add_le _ _).trans (add_le_add (he₀ i) ((normInf_le_iff _ _).mp he i))

/-- Modulus switching from `Q = Q' · q` to `Q'`: exact division of the centred phase plus a
correction `δ`. -/
theorem noiseLe_modSwitch {t B E Q' q : ℕ} (ht : 0 < t) (hQ' : 0 < Q') (hq : 0 < q)
    {φ : Poly (Q' * q) N} {m : Poly t N} (δ : IntPoly N) (h : NoiseLe t B φ m)
    (hδ : normInf δ ≤ q * E) (hdvd : ∀ j, (q : ℤ) ∣ (centered φ).coeff j + δ.coeff j) :
    NoiseLe t (B / q + E + Q' % t)
      (ofInt Q' ⟨fun j => ((centered φ).coeff j + δ.coeff j) / q⟩) m := by
  have : NeZero t := ⟨ht.ne'⟩
  obtain ⟨e, he, hφ⟩ := noiseLe_elim h
  have hrep : ∀ j, ∃ k : ℤ, (centered φ).coeff j =
      ((Q' * q / t * (m.coeff j).val : ℕ) : ℤ) + e.coeff j + ((Q' * q : ℕ) : ℤ) * k := by
    intro j
    apply exists_eq_add_mul_of_cast_eq (Q := Q' * q)
    rw [coeff_centered, ZMod.coe_valMinAbs]
    conv_lhs => rw [hφ]
    simp [scaled]
  choose k hk using hrep
  have hX : ∀ j, (q : ℤ) * (((centered φ).coeff j + δ.coeff j) / q)
      = (centered φ).coeff j + δ.coeff j := fun j => Int.mul_ediv_cancel' (hdvd j)
  refine noiseLe_of_eq hQ' ⟨fun j => ((centered φ).coeff j + δ.coeff j) / q
    - ((Q' / t * (m.coeff j).val : ℕ) : ℤ) - Q' * k j⟩ ?_ ?_
  · ext j
    simp [scaled]
  · intro j
    exact modSwitch_arith t Q' q B E _ ht hq (ZMod.val_lt _) (e.coeff j) (δ.coeff j) _ (k j) _
      (he j) ((normInf_le_iff _ _).mp hδ j) (hk j) (hX j)

end Validation.BFV
