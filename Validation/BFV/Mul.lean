import Validation.BFV.Core

/-!
# Validation.BFV.Mul — BFV noise of the scale-invariant product

The phase-level lemma behind the `mul`/`square` rule of `Challenge.BFV.refBoundBFV`: any `X`
meeting the multiplication contract of `Spec.TraceBFV` has noise at most `mulBound`.
-/

namespace Validation.BFV
open Spec NPoly Scheme Challenge.BFV
open Validation.Ring Validation.Scheme Validation.Source

variable {N : ℕ}

/-- Coefficients of an integer constant times a polynomial. -/
theorem coeff_intCast_mul [NeZero N] (c : ℤ) (p : IntPoly N) (i : Fin N) :
    ((c : IntPoly N) * p).coeff i = c * p.coeff i := by
  rw [intCast_def, Int.cast_id]
  exact coeff_const_mul c p i

/-- Coefficient-wise scalar multiplication is multiplication by the constant. -/
theorem smul_eq_intCast_mul [NeZero N] (c : ℤ) (p : IntPoly N) :
    c • p = (c : IntPoly N) * p := by
  ext i
  rw [coeff_intCast_mul]
  rfl

theorem abs_natCast_mul_le (c : ℕ) {x b : ℤ} (h : |x| ≤ b) : |(c : ℤ) * x| ≤ c * b := by
  rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℤ) ≤ (c : ℤ))]
  exact mul_le_mul_of_nonneg_left h (by positivity)

/-- `2·|[x]_Q| ≤ Q`. -/
theorem two_abs_valMinAbs_le {Q : ℕ} (hQ : 0 < Q) (x : ZMod Q) : 2 * |x.valMinAbs| ≤ (Q : ℤ) := by
  haveI : NeZero Q := ⟨hQ.ne'⟩
  have h := ZMod.natAbs_valMinAbs_le x
  have h' : (x.valMinAbs.natAbs : ℤ) ≤ ((Q / 2 : ℕ) : ℤ) := by exact_mod_cast h
  rw [Int.natCast_natAbs] at h'
  have h2 : ((Q / 2 : ℕ) : ℤ) * 2 ≤ Q := by exact_mod_cast Nat.div_mul_le_self Q 2
  linarith

/-- The centred lift of a phase with noise at most `B` is `Δ·m̃ + e + Q·l` with `‖e‖∞ ≤ B` and
`‖l‖∞ ≤ 1`. -/
theorem noiseLe_lift {t B Q : ℕ} (ht : 0 < t) (hQ : 0 < Q) {φ : Poly Q N} {m : Poly t N}
    (h : NoiseLe t B φ m) :
    ∃ e l : IntPoly N, (∀ i, |e.coeff i| ≤ B) ∧ (∀ i, |l.coeff i| ≤ 1) ∧
      ∀ i, (centered φ).coeff i =
        ((Q / t : ℕ) : ℤ) * ((m.coeff i).val : ℤ) + e.coeff i + (Q : ℤ) * l.coeff i := by
  haveI : NeZero t := ⟨ht.ne'⟩
  have hQz : (0 : ℤ) < Q := by exact_mod_cast hQ
  have key : ∀ i, ∃ j : ℤ, |j| ≤ 1 ∧ (centered φ).coeff i =
      ((Q / t : ℕ) : ℤ) * ((m.coeff i).val : ℤ) +
        (centered (φ - ofInt Q (scaled t Q m))).coeff i + (Q : ℤ) * j := by
    intro i
    have hcast : (((centered φ).coeff i : ℤ) : ZMod Q) =
        ((((Q / t : ℕ) : ℤ) * ((m.coeff i).val : ℤ) +
          (centered (φ - ofInt Q (scaled t Q m))).coeff i : ℤ) : ZMod Q) := by
      simp only [coeff_centered, Int.cast_add, ZMod.coe_valMinAbs, coeff_sub', coeff_ofInt,
        scaled]
      push_cast
      ring
    obtain ⟨j, hj⟩ := exists_eq_add_mul_of_cast_eq hcast
    refine ⟨j, ?_, hj⟩
    have h1 := two_abs_valMinAbs_le hQ (φ.coeff i)
    have h2 := two_abs_valMinAbs_le hQ ((φ - ofInt Q (scaled t Q m)).coeff i)
    simp only [coeff_centered] at hj
    have hs0 : (0 : ℤ) ≤ ((Q / t : ℕ) : ℤ) * ((m.coeff i).val : ℤ) := by positivity
    have hs1 : ((Q / t : ℕ) : ℤ) * ((m.coeff i).val : ℤ) < Q := by
      have hv : (m.coeff i).val < t := ZMod.val_lt _
      have : Q / t * (m.coeff i).val < Q := by
        rcases Nat.eq_zero_or_pos (Q / t) with h0 | h0
        · rw [h0]; simpa using hQ
        · have := Nat.div_mul_le_self Q t
          nlinarith
      exact_mod_cast this
    have a1 := neg_abs_le (φ.coeff i).valMinAbs
    have a2 := le_abs_self (φ.coeff i).valMinAbs
    have a3 := neg_abs_le ((φ - ofInt Q (scaled t Q m)).coeff i).valMinAbs
    have a4 := le_abs_self ((φ - ofInt Q (scaled t Q m)).coeff i).valMinAbs
    rw [abs_le]
    constructor
    · by_contra hc
      have hc' : j ≤ -2 := by omega
      have : (Q : ℤ) * j ≤ Q * (-2) := mul_le_mul_of_nonneg_left hc' hQz.le
      linarith
    · by_contra hc
      have hc' : 2 ≤ j := by omega
      have : (Q : ℤ) * 2 ≤ Q * j := mul_le_mul_of_nonneg_left hc' hQz.le
      linarith
  choose l hl1 hl2 using key
  exact ⟨_, ⟨l⟩, (normInf_le_iff _ _).mp h, hl1, hl2⟩

/-- The algebra of the scale-invariant product, in any commutative ring. -/
theorem mul_alg {A : Type} [CommRing A] (Δ t r Q X D m₁ m₂ e₁ e₂ κ₁ κ₂ : A)
    (hQ : Δ * t + r = Q)
    (hX : Q * X = t * ((Δ * m₁ + e₁ + Q * κ₁) * (Δ * m₂ + e₂ + Q * κ₂)) + D) :
    ∃ Z : A, Q * Z = D - r * (Δ * (m₁ * m₂)) - r * (m₁ * e₂ + m₂ * e₁) + t * (e₁ * e₂) ∧
      X = Δ * (m₁ * m₂) +
          (m₁ * e₂ + m₂ * e₁ + Z - r * (κ₁ * m₂ + κ₂ * m₁) + t * (κ₁ * e₂ + κ₂ * e₁)) +
          Q * (κ₁ * m₂ + κ₂ * m₁ + t * (κ₁ * κ₂)) := by
  refine ⟨X - (Δ * (m₁ * m₂) + (m₁ * e₂ + m₂ * e₁) +
    t * (κ₁ * (Δ * m₂ + e₂) + κ₂ * (Δ * m₁ + e₁)) + t * Q * (κ₁ * κ₂)), ?_, ?_⟩
  · linear_combination hX + (Δ * (m₁ * m₂) + m₁ * e₂ + m₂ * e₁) * hQ
  · linear_combination (κ₁ * m₂ + κ₂ * m₁) * hQ

theorem noiseLe_mul {t B₁ B₂ K R Q : ℕ} (ht : 0 < t) (hQ : 0 < Q) {φ₁ φ₂ : Poly Q N}
    {m₁ m₂ : Poly t N} (k₁ k₂ X D : IntPoly N)
    (h₁ : NoiseLe t B₁ φ₁ m₁) (h₂ : NoiseLe t B₂ φ₂ m₂)
    (hk₁ : normInf k₁ ≤ K) (hk₂ : normInf k₂ ≤ K) (hD : 2 * normInf D ≤ Q * R)
    (hX : (Q : ℤ) • X =
      (t : ℤ) • ((centered φ₁ + (Q : ℤ) • k₁) * (centered φ₂ + (Q : ℤ) • k₂)) + D) :
    NoiseLe t (mulBound N t Q K R B₁ B₂) (ofInt Q X) (m₁ * m₂) := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    unfold NoiseLe
    rw [normInf_le_iff]
    intro i; exact i.elim0
  haveI : NeZero N := ⟨hN.ne'⟩
  haveI : NeZero t := ⟨ht.ne'⟩
  have hQz : (0 : ℤ) < Q := by exact_mod_cast hQ
  obtain ⟨e₁, l₁, he₁, hl₁, hΦ₁⟩ := noiseLe_lift ht hQ h₁
  obtain ⟨e₂, l₂, he₂, hl₂, hΦ₂⟩ := noiseLe_lift ht hQ h₂
  obtain ⟨Mn, hMn⟩ : ∃ Mn, Mn = t - 1 := ⟨_, rfl⟩
  have hMt : Mn + 1 = t := by omega
  obtain ⟨mt₁, hmt₁d⟩ : ∃ p : IntPoly N, p = ⟨fun i => ((m₁.coeff i).val : ℤ)⟩ := ⟨_, rfl⟩
  obtain ⟨mt₂, hmt₂d⟩ : ∃ p : IntPoly N, p = ⟨fun i => ((m₂.coeff i).val : ℤ)⟩ := ⟨_, rfl⟩
  have hc₁ : ∀ i, mt₁.coeff i = ((m₁.coeff i).val : ℤ) := fun i => by rw [hmt₁d]
  have hc₂ : ∀ i, mt₂.coeff i = ((m₂.coeff i).val : ℤ) := fun i => by rw [hmt₂d]
  have hmt₁ : ∀ i, |mt₁.coeff i| ≤ (Mn : ℤ) := by
    intro i
    rw [hc₁, abs_of_nonneg (by positivity)]
    have : (m₁.coeff i).val < t := ZMod.val_lt _
    exact_mod_cast (by omega : (m₁.coeff i).val ≤ Mn)
  have hmt₂ : ∀ i, |mt₂.coeff i| ≤ (Mn : ℤ) := by
    intro i
    rw [hc₂, abs_of_nonneg (by positivity)]
    have : (m₂.coeff i).val < t := ZMod.val_lt _
    exact_mod_cast (by omega : (m₂.coeff i).val ≤ Mn)
  have hκ₁ : ∀ i, |(l₁ + k₁).coeff i| ≤ ((K + 1 : ℕ) : ℤ) := by
    intro i
    have a := hl₁ i
    have b := (normInf_le_iff _ _).mp hk₁ i
    rw [coeff_add']; push_cast
    exact (abs_add_le _ _).trans (by linarith)
  have hκ₂ : ∀ i, |(l₂ + k₂).coeff i| ≤ ((K + 1 : ℕ) : ℤ) := by
    intro i
    have a := hl₂ i
    have b := (normInf_le_iff _ _).mp hk₂ i
    rw [coeff_add']; push_cast
    exact (abs_add_le _ _).trans (by linarith)
  have hΨ₁ : centered φ₁ + (Q : ℤ) • k₁ =
      (((Q / t : ℕ) : ℤ) : IntPoly N) * mt₁ + e₁ + ((Q : ℤ) : IntPoly N) * (l₁ + k₁) := by
    rw [smul_eq_intCast_mul]
    ext i
    simp only [coeff_add', coeff_intCast_mul, hΦ₁ i, hc₁]
    ring
  have hΨ₂ : centered φ₂ + (Q : ℤ) • k₂ =
      (((Q / t : ℕ) : ℤ) : IntPoly N) * mt₂ + e₂ + ((Q : ℤ) : IntPoly N) * (l₂ + k₂) := by
    rw [smul_eq_intCast_mul]
    ext i
    simp only [coeff_add', coeff_intCast_mul, hΦ₂ i, hc₂]
    ring
  have hQd : (((Q / t : ℕ) : ℤ) : IntPoly N) * ((t : ℤ) : IntPoly N) +
      (((Q % t : ℕ) : ℤ) : IntPoly N) = ((Q : ℤ) : IntPoly N) := by
    rw [← Int.cast_mul, ← Int.cast_add]
    congr 1
    exact_mod_cast Nat.div_add_mod' Q t
  rw [hΨ₁, hΨ₂, smul_eq_intCast_mul, smul_eq_intCast_mul] at hX
  obtain ⟨Z, hA, hB⟩ := mul_alg _ _ _ _ X D mt₁ mt₂ e₁ e₂ (l₁ + k₁) (l₂ + k₂) hQd hX
  generalize l₁ + k₁ = κ₁ at hκ₁ hA hB
  generalize l₂ + k₂ = κ₂ at hκ₂ hA hB
  -- the bound on `Z`
  have hZ : ∀ i, |Z.coeff i| ≤ (((Q * R + 2 * N * (Q % t * (Q / t) * Mn * Mn +
      Q % t * Mn * (B₁ + B₂) + t * B₁ * B₂)) / (2 * Q) : ℕ) : ℤ) := by
    intro i
    have ha := congrArg (fun p => p.coeff i) hA
    simp only [coeff_add', coeff_sub', coeff_intCast_mul] at ha
    have p1 := abs_natCast_mul_le (Q % t) (abs_natCast_mul_le (Q / t)
      (abs_coeff_mul_le_N mt₁ mt₂ Mn Mn hmt₁ hmt₂ i))
    have p2 := abs_natCast_mul_le (Q % t) (abs_coeff_mul_le_N mt₁ e₂ Mn B₂ hmt₁ he₂ i)
    have p3 := abs_natCast_mul_le (Q % t) (abs_coeff_mul_le_N mt₂ e₁ Mn B₁ hmt₂ he₁ i)
    have p4 := abs_natCast_mul_le t (abs_coeff_mul_le_N e₁ e₂ B₁ B₂ he₁ he₂ i)
    have p5 := abs_coeff_le_normInf D i
    have p6 : (2 * (normInf D : ℤ)) ≤ Q * R := by exact_mod_cast hD
    have hz : (Q : ℤ) * |Z.coeff i| = |(Q : ℤ) * Z.coeff i| := by
      rw [abs_mul, abs_of_nonneg hQz.le]
    rw [abs_le] at p1 p2 p3 p4 p5
    have hz2 : |(Q : ℤ) * Z.coeff i| ≤ (normInf D : ℤ) +
        (Q % t : ℕ) * ((Q / t : ℕ) * (N * Mn * Mn))
        + (Q % t : ℕ) * (N * Mn * B₂) + (Q % t : ℕ) * (N * Mn * B₁) + t * (N * B₁ * B₂) := by
      rw [ha, abs_le]
      constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2, p4.1, p4.2, p5.1, p5.2]
    have hnat : (Z.coeff i).natAbs * (2 * Q) ≤ Q * R + 2 * N * (Q % t * (Q / t) * Mn * Mn +
        Q % t * Mn * (B₁ + B₂) + t * B₁ * B₂) := by
      zify
      push_cast at hz2
      linarith [hz, hz2, p6]
    rw [← Int.natCast_natAbs]
    exact_mod_cast (Nat.le_div_iff_mul_le (by omega)).mpr hnat
  have hbound : mulBound N t Q K R B₁ B₂ =
      (N * Mn * B₂ + N * Mn * B₁ + (Q * R + 2 * N * (Q % t * (Q / t) * Mn * Mn +
        Q % t * Mn * (B₁ + B₂) + t * B₁ * B₂)) / (2 * Q) +
        Q % t * (N * (K + 1) * Mn + N * (K + 1) * Mn) +
        t * (N * (K + 1) * B₂ + N * (K + 1) * B₁)) + Q % t * (N * Mn) := by
    show N * (B₁ + B₂) * (t * (K + 1) + (t - 1)) + Q % t * N * (t - 1) * (2 * (K + 1) + 1) +
      (Q * R + 2 * N * (Q % t * (Q / t) * (t - 1) * (t - 1) + Q % t * (t - 1) * (B₁ + B₂) +
        t * B₁ * B₂)) / (2 * Q) = _
    rw [← hMn]
    ring
  rw [hbound]
  refine noiseLe_intro ht hQ (mt₁ * mt₂)
    (mt₁ * e₂ + mt₂ * e₁ + Z - (((Q % t : ℕ) : ℤ) : IntPoly N) * (κ₁ * mt₂ + κ₂ * mt₁) +
      ((t : ℤ) : IntPoly N) * (κ₁ * e₂ + κ₂ * e₁)) (N * Mn) _ ?_ ?_ ?_ ?_
  · ext i
    have hb := congrArg (fun p => p.coeff i) hB
    simp only [coeff_add', coeff_sub', coeff_intCast_mul] at hb
    simp only [coeff_ofInt, coeff_add', coeff_sub', coeff_intCast_mul]
    rw [hb]
    push_cast
    rw [ZMod.natCast_self]
    ring
  · rw [ofInt_mul]
    congr 1
    · ext i; rw [coeff_ofInt, hc₁]; simp
    · ext i; rw [coeff_ofInt, hc₂]; simp
  · intro i
    have p := abs_coeff_mul_le_N mt₁ mt₂ Mn Mn hmt₁ hmt₂ i
    rw [abs_le] at p
    have hNn : (0 : ℤ) ≤ (N : ℤ) * Mn := by positivity
    have hMM : (N : ℤ) * Mn * Mn ≤ N * Mn * t := by
      apply mul_le_mul_of_nonneg_left _ hNn
      exact_mod_cast (by omega : Mn ≤ t)
    have ht' : (0 : ℤ) < t := by exact_mod_cast ht
    push_cast
    constructor <;> linarith [p.1, p.2]
  · intro i
    simp only [coeff_add', coeff_sub', coeff_intCast_mul]
    have q1 := abs_coeff_mul_le_N mt₁ e₂ Mn B₂ hmt₁ he₂ i
    have q2 := abs_coeff_mul_le_N mt₂ e₁ Mn B₁ hmt₂ he₁ i
    have q3 := hZ i
    have q4 := abs_natCast_mul_le (Q % t) ((abs_add_le _ _).trans (add_le_add
      (abs_coeff_mul_le_N κ₁ mt₂ _ Mn hκ₁ hmt₂ i) (abs_coeff_mul_le_N κ₂ mt₁ _ Mn hκ₂ hmt₁ i)))
    have q5 := abs_natCast_mul_le t ((abs_add_le _ _).trans (add_le_add
      (abs_coeff_mul_le_N κ₁ e₂ _ B₂ hκ₁ he₂ i) (abs_coeff_mul_le_N κ₂ e₁ _ B₁ hκ₂ he₁ i)))
    rw [abs_le] at q1 q2 q3 q4 q5
    push_cast at q3 q4 q5 ⊢
    rw [abs_le]
    constructor <;> linarith [q1.1, q1.2, q2.1, q2.2, q3.1, q3.2, q4.1, q4.2, q5.1, q5.2]

end Validation.BFV
