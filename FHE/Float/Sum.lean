import Challenge.BFVMul.Float

/-!
# FHE.Float.Sum — rounding-error analysis of OpenFHE's two binary64 sums

For every arithmetic conforming to the standard model (`Spec.Float.Conforms`):

* `nuSw_err`: `Fl.nuSw` (the overflow sum of `SwitchCRTBasis`) is within `k·(k+5)·2⁻⁵³` of
  `1/2 + Σ yᵢ/qᵢ`;
* `nuSr_err`: `Fl.nuSr` (the fractional sum of `ScaleAndRound`) is within
  `(k+6)·(1 + Σ mᵢ)·2⁻⁵³` of `1/2 + Σ xᵢ·nᵢ/mᵢ`;

and both are at least `1/4` (so the casts that truncate them are defined).

The analysis is the textbook one (Higham, *Accuracy and Stability of Numerical Algorithms*,
ch. 3–4), kept explicit:

* `Approx e v x`: `x = v·ρ` with `|ρ − 1| ≤ e` — a computed quantity with relative error `e`.
  Closed under products, quotients and one more rounding (`Approx.mul`, `Approx.div`,
  `Approx.rounds`); the error parameters are concrete rationals (`eInv`, …, `eta4`, `eta5`).
* `fold_err`: a recursive summation `s ← (s + τ)·(1 + δ)`, `|δ| ≤ u`, whose terms `τ` have
  absolute error at most `η·cap`, accumulates at most
  `(1 + 2nu)·Σ (η(1+u)·cap + u·B)`, `B` a bound on the exact sum.
* `sw_step`, `sr_step`: one loop iteration of each sum has that form, with or without
  contraction of `s += a*b` into a fused multiply-add; every exact result is shown to lie in
  the window `Spec.Float.InRange` in which the model promises a relative error.
-/

namespace FHE.Float
open Spec.Float Challenge.BFVMul

/-! ### Relative error -/

/-- `x = v·ρ` with `|ρ − 1| ≤ e`. -/
def Approx (e v x : ℚ) : Prop := ∃ ρ : ℚ, |ρ - 1| ≤ e ∧ x = v * ρ

theorem Approx.mono {e e' v x : ℚ} (h : Approx e v x) (he : e ≤ e') : Approx e' v x := by
  obtain ⟨ρ, h1, h2⟩ := h
  exact ⟨ρ, h1.trans he, h2⟩

theorem approx_refl (v : ℚ) : Approx 0 v v := ⟨1, by simp, by ring⟩

theorem approx_of_rounds {v x : ℚ} (h : Rounds v x) : Approx u v x := by
  obtain ⟨δ, h1, h2⟩ := h
  exact ⟨1 + δ, by simpa using h1, h2⟩

theorem Approx.mul {a b v w x y : ℚ} (h1 : Approx a v x) (h2 : Approx b w y) :
    Approx (a + b + a * b) (v * w) (x * y) := by
  obtain ⟨ρ, hρ, rfl⟩ := h1
  obtain ⟨σ, hσ, rfl⟩ := h2
  refine ⟨ρ * σ, ?_, by ring⟩
  have ha : 0 ≤ a := (abs_nonneg _).trans hρ
  have e : ρ * σ - 1 = (ρ - 1) + (σ - 1) + (ρ - 1) * (σ - 1) := by ring
  rw [e]
  calc |(ρ - 1) + (σ - 1) + (ρ - 1) * (σ - 1)|
      ≤ |ρ - 1| + |σ - 1| + |(ρ - 1) * (σ - 1)| := abs_add_three _ _ _
    _ ≤ a + b + a * b := by
        rw [abs_mul]
        exact add_le_add (add_le_add hρ hσ) (mul_le_mul hρ hσ (abs_nonneg _) ha)

theorem Approx.rounds {a v x z : ℚ} (h : Approx a v x) (hr : Rounds x z) :
    Approx (a + u + a * u) v z := by
  obtain ⟨δ, hδ, rfl⟩ := hr
  have := h.mul (⟨1 + δ, by simpa using hδ, by ring⟩ : Approx u 1 (1 + δ))
  rwa [mul_one] at this

theorem Approx.inv {b w y : ℚ} (h : Approx b w y) (hb : b < 1) :
    Approx (b / (1 - b)) (1 / w) (1 / y) := by
  obtain ⟨σ, hσ, rfl⟩ := h
  have h1 := abs_le.mp hσ
  have hσpos : 0 < σ := by linarith
  refine ⟨1 / σ, ?_, by rw [one_div, one_div, one_div, mul_inv]⟩
  have e : 1 / σ - 1 = (1 - σ) / σ := by field_simp
  rw [e, abs_div, abs_of_pos hσpos, abs_sub_comm]
  exact div_le_div₀ ((abs_nonneg _).trans hσ) hσ (by linarith) (by linarith)

theorem Approx.div {a b v w x y : ℚ} (h1 : Approx a v x) (h2 : Approx b w y) (hb : b < 1) :
    Approx (a + b / (1 - b) + a * (b / (1 - b))) (v / w) (x / y) := by
  have := h1.mul (h2.inv hb)
  rwa [mul_one_div, mul_one_div] at this

theorem Approx.eq_zero {e x : ℚ} (h : Approx e 0 x) : x = 0 := by
  obtain ⟨ρ, _, rfl⟩ := h
  simp

/-- With relative error at most `1/2`, a positive value is approximated within a factor 2. -/
theorem Approx.bounds {e v x : ℚ} (h : Approx e v x) (he : e ≤ 1 / 2) (hv : 0 ≤ v) :
    v / 2 ≤ x ∧ x ≤ 2 * v := by
  obtain ⟨ρ, hρ, rfl⟩ := h
  have h1 := abs_le.mp (hρ.trans he)
  constructor
  · nlinarith [h1.1]
  · nlinarith [h1.2]

theorem Approx.abs_sub_le {e v x : ℚ} (h : Approx e v x) (hv : 0 ≤ v) : |x - v| ≤ e * v := by
  obtain ⟨ρ, hρ, rfl⟩ := h
  have e' : v * ρ - v = v * (ρ - 1) := by ring
  rw [e', abs_mul, abs_of_nonneg hv, mul_comm]
  exact mul_le_mul_of_nonneg_right hρ hv

/-- A positive quantity between `2⁻¹²⁸` and `2¹²⁸` is in the window of the model. -/
theorem inRange_of_bounds {x : ℚ} (h1 : 1 / 2 ^ 128 ≤ x) (h2 : x ≤ 2 ^ 128) : InRange x := by
  have hx : 0 ≤ x := le_trans (by positivity) h1
  exact Or.inr (by rw [abs_of_nonneg hx]; exact ⟨h1, h2⟩)

/-- An approximation (relative error at most `1/2`) of zero or of a value in `[2⁻¹²⁷, 2¹²⁷]` is
in the window of the model. -/
theorem Approx.inRange {e v x : ℚ} (h : Approx e v x) (he : e ≤ 1 / 2)
    (hv : v = 0 ∨ (1 / 2 ^ 127 ≤ v ∧ v ≤ 2 ^ 127)) : InRange x := by
  rcases hv with rfl | ⟨h1, h2⟩
  · exact Or.inl h.eq_zero
  · have hv0 : 0 ≤ v := le_trans (by positivity) h1
    obtain ⟨b1, b2⟩ := h.bounds he hv0
    refine inRange_of_bounds ?_ ?_
    · have : (1 : ℚ) / 2 ^ 128 = 1 / 2 ^ 127 / 2 := by norm_num
      rw [this]
      linarith
    · have : (2 : ℚ) ^ 128 = 2 * 2 ^ 127 := by norm_num
      rw [this]
      linarith

/-! ### The error parameters -/

/-- Relative error of `1/fl(m)` against `1/m`. -/
def eInv : ℚ := u / (1 - u)
/-- Relative error of an entry of `qInv`: `fl(1/fl(q))`. -/
def e2 : ℚ := eInv + u + eInv * u
/-- Relative error of the exact product `fl(y)·qInv`. -/
def e3 : ℚ := u + e2 + u * e2
/-- Relative error of a term of the overflow sum (four roundings). -/
def eta4 : ℚ := e3 + u + e3 * u
/-- Relative error of the exact quotient `fl(n)/fl(m)`. -/
def f0 : ℚ := u + eInv + u * eInv
/-- Relative error of an entry of a `…Frac` table. -/
def f1 : ℚ := f0 + u + f0 * u
/-- Relative error of the exact product `Frac·fl(x)`. -/
def f2 : ℚ := f1 + u + f1 * u
/-- Relative error of a term of the scaling sum (five roundings). -/
def eta5 : ℚ := f2 + u + f2 * u

theorem u_pos : 0 < u := by unfold u; positivity
theorem u_lt : u < 1 := by unfold u; norm_num

theorem eInv_bound : 0 ≤ eInv ∧ eInv ≤ 1 / 2 := by unfold eInv u; norm_num
theorem e2_bound : 0 ≤ e2 ∧ e2 ≤ 1 / 2 := by unfold e2 eInv u; norm_num
theorem e3_bound : 0 ≤ e3 ∧ e3 ≤ 1 / 2 := by unfold e3 e2 eInv u; norm_num
theorem eta4_bound : 0 ≤ eta4 ∧ eta4 ≤ 1 / 2 ∧ eta4 * (1 + u) ≤ 33 / 8 * u := by
  unfold eta4 e3 e2 eInv u; norm_num
theorem f0_bound : 0 ≤ f0 ∧ f0 ≤ 1 / 2 := by unfold f0 eInv u; norm_num
theorem f1_bound : 0 ≤ f1 ∧ f1 ≤ 1 / 2 := by unfold f1 f0 eInv u; norm_num
theorem f2_bound : 0 ≤ f2 ∧ f2 ≤ 1 / 2 := by unfold f2 f1 f0 eInv u; norm_num
theorem eta5_bound : 0 ≤ eta5 ∧ eta5 ≤ 1 / 2 ∧ eta5 * (1 + u) ≤ 21 / 4 * u := by
  unfold eta5 f2 f1 f0 eInv u; norm_num

/-! ### Recursive summation -/

/-- **Accumulated error of a recursive summation.** `step s a = (s + τ)·(1 + δ)` with `|δ| ≤ u`
and a nonnegative term `τ` within `η·cap a` of its exact value `val a ∈ [0, cap a]`, whenever
`1/4 ≤ s ≤ W`. From a state `s` approximating `S` after `j` steps with error at most
`(1 + 2ju)·G`: after the steps of `l`, the error is at most
`(1 + 2(j+|l|)u)·(G + Σ (η(1+u)·cap + u·B))`, `B` any bound on the exact sum; and the state
stays at least `(1 − (j+|l|)u)/2`. -/
theorem fold_err {α : Type} (step : ℚ → α → ℚ) (val cap : α → ℚ) (η B W : ℚ) (hη : 0 ≤ η)
    (hB : 0 ≤ B) :
    ∀ (l : List α) (s S G : ℚ) (j : ℕ),
      (∀ a ∈ l, 0 ≤ val a ∧ val a ≤ cap a) →
      (∀ a ∈ l, ∀ s : ℚ, 1 / 4 ≤ s → s ≤ W →
        ∃ τ δ : ℚ, |δ| ≤ u ∧ 0 ≤ τ ∧ |τ - val a| ≤ η * cap a ∧ step s a = (s + τ) * (1 + δ)) →
      j + l.length ≤ 2 ^ 16 →
      0 ≤ G → |s - S| ≤ (1 + 2 * j * u) * G → (1 - j * u) / 2 ≤ s →
      S + (l.map val).sum ≤ B →
      B + 2 * (G + (l.map fun a => η * (1 + u) * cap a + u * B).sum) ≤ W →
      |l.foldl step s - (S + (l.map val).sum)| ≤
          (1 + 2 * ((j + l.length : ℕ) : ℚ) * u) *
            (G + (l.map fun a => η * (1 + u) * cap a + u * B).sum) ∧
        (1 - ((j + l.length : ℕ) : ℚ) * u) / 2 ≤ l.foldl step s := by
  intro l
  induction l with
  | nil =>
    intro s S G j _ _ _ _ hE hs _ _
    simpa using ⟨hE, hs⟩
  | cons a l ih =>
    intro s S G j hval hstep hj hG hE hs hSB hW
    have hu := u_pos
    have hva := hval a List.mem_cons_self
    have hca : 0 ≤ cap a := hva.1.trans hva.2
    have hsum0 : 0 ≤ (l.map val).sum :=
      List.sum_nonneg fun x hx => by
        obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hx
        exact (hval b (List.mem_cons_of_mem _ hb)).1
    have hg0 : 0 ≤ (l.map fun a => η * (1 + u) * cap a + u * B).sum :=
      List.sum_nonneg fun x hx => by
        obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hx
        have := hval b (List.mem_cons_of_mem _ hb)
        have hcb : 0 ≤ cap b := this.1.trans this.2
        positivity
    have hga : 0 ≤ η * (1 + u) * cap a + u * B := by positivity
    simp only [List.map_cons, List.sum_cons, List.length_cons] at hSB hW hj ⊢
    -- `j·u` is small
    have hjle : (j : ℚ) ≤ 2 ^ 16 := by
      have : j ≤ 2 ^ 16 := by omega
      exact_mod_cast this
    have hju : (j : ℚ) * u ≤ 1 / 2 ^ 37 := by
      have : (j : ℚ) * u ≤ 2 ^ 16 * u := mul_le_mul_of_nonneg_right hjle hu.le
      have e : (2 : ℚ) ^ 16 * u = 1 / 2 ^ 37 := by unfold u; norm_num
      linarith
    have hj0 : (0 : ℚ) ≤ j := Nat.cast_nonneg j
    have hju0 : 0 ≤ (j : ℚ) * u := mul_nonneg hj0 hu.le
    -- the state is in the range where the step is known
    have hs14 : 1 / 4 ≤ s := by
      have : (1 : ℚ) / 2 ^ 37 ≤ 1 / 2 := by norm_num
      linarith
    have hEabs := abs_le.mp hE
    have hfac : 1 + 2 * (j : ℚ) * u ≤ 2 := by
      have : (1 : ℚ) / 2 ^ 37 ≤ 1 / 2 := by norm_num
      linarith
    have hEG : (1 + 2 * (j : ℚ) * u) * G ≤ 2 * G := mul_le_mul_of_nonneg_right hfac hG
    have hsW : s ≤ W := by linarith
    obtain ⟨τ, δ, hδ, hτ0, hτ, hst⟩ := hstep a List.mem_cons_self s hs14 hsW
    have hδ' := abs_le.mp hδ
    have hτ' := abs_le.mp hτ
    -- the new state
    have hs0 : 0 ≤ s := le_trans (by norm_num) hs14
    have hsτ0 : 0 ≤ s + τ := add_nonneg hs0 hτ0
    have hnew1 : |(s + τ) * (1 + δ) - (S + val a)| ≤
        (1 + 2 * ((j + 1 : ℕ) : ℚ) * u) * (G + (η * (1 + u) * cap a + u * B)) := by
      set E := (1 + 2 * (j : ℚ) * u) * G with hEdef
      have hE0 : 0 ≤ E := by positivity
      have hsτ : s + τ ≤ B + E + η * cap a := by linarith
      have hprod : |δ * (s + τ)| ≤ u * (B + E + η * cap a) := by
        rw [abs_mul, abs_of_nonneg hsτ0]
        exact mul_le_mul hδ hsτ hsτ0 hu.le
      have e : (s + τ) * (1 + δ) - (S + val a) = (s - S) + (τ - val a) + δ * (s + τ) := by ring
      have h1 : |(s + τ) * (1 + δ) - (S + val a)| ≤
          (1 + u) * E + (η * (1 + u) * cap a + u * B) := by
        rw [e]
        calc |(s - S) + (τ - val a) + δ * (s + τ)|
            ≤ |s - S| + |τ - val a| + |δ * (s + τ)| := abs_add_three _ _ _
          _ ≤ E + η * cap a + u * (B + E + η * cap a) := add_le_add (add_le_add hE hτ) hprod
          _ = (1 + u) * E + (η * (1 + u) * cap a + u * B) := by ring
      have hkey : (1 + u) * (1 + 2 * (j : ℚ) * u) ≤ 1 + 2 * ((j + 1 : ℕ) : ℚ) * u := by
        push_cast
        have : 2 * ((j : ℚ) * u) * u ≤ u := by
          have : 2 * ((j : ℚ) * u) ≤ 1 := by
            have : (1 : ℚ) / 2 ^ 37 ≤ 1 / 2 := by norm_num
            linarith
          nlinarith
        nlinarith
      have hE' : (1 + u) * E ≤ (1 + 2 * ((j + 1 : ℕ) : ℚ) * u) * G := by
        rw [hEdef, ← mul_assoc]
        exact mul_le_mul_of_nonneg_right hkey hG
      have hone : 1 ≤ 1 + 2 * ((j + 1 : ℕ) : ℚ) * u := by
        have : (0 : ℚ) ≤ ((j + 1 : ℕ) : ℚ) := Nat.cast_nonneg _
        nlinarith
      have hg' : η * (1 + u) * cap a + u * B ≤
          (1 + 2 * ((j + 1 : ℕ) : ℚ) * u) * (η * (1 + u) * cap a + u * B) :=
        le_mul_of_one_le_left hga hone
      have hsplit : (1 + 2 * ((j + 1 : ℕ) : ℚ) * u) * (G + (η * (1 + u) * cap a + u * B)) =
          (1 + 2 * ((j + 1 : ℕ) : ℚ) * u) * G +
            (1 + 2 * ((j + 1 : ℕ) : ℚ) * u) * (η * (1 + u) * cap a + u * B) := mul_add _ _ _
      rw [hsplit]
      linarith
    have hnew2 : (1 - ((j + 1 : ℕ) : ℚ) * u) / 2 ≤ (s + τ) * (1 + δ) := by
      have h1 : s * (1 - u) ≤ (s + τ) * (1 + δ) := by
        have : (s + τ) * (1 - u) ≤ (s + τ) * (1 + δ) :=
          mul_le_mul_of_nonneg_left (by linarith) hsτ0
        have : s * (1 - u) ≤ (s + τ) * (1 - u) :=
          mul_le_mul_of_nonneg_right (by linarith) (by linarith [u_lt])
        linarith
      have h2 : (1 - (j : ℚ) * u) / 2 * (1 - u) ≤ s * (1 - u) :=
        mul_le_mul_of_nonneg_right hs (by linarith [u_lt])
      push_cast
      nlinarith
    have := ih ((s + τ) * (1 + δ)) (S + val a) (G + (η * (1 + u) * cap a + u * B)) (j + 1)
      (fun b hb => hval b (List.mem_cons_of_mem _ hb))
      (fun b hb => hstep b (List.mem_cons_of_mem _ hb))
      (by omega) (by positivity) hnew1 hnew2 (by linarith) (by linarith)
    rw [List.foldl_cons, hst]
    have e1 : j + (l.length + 1) = j + 1 + l.length := by omega
    rw [e1]
    have e2 : S + (val a + (l.map val).sum) = S + val a + (l.map val).sum := by ring
    have e3 : G + (η * (1 + u) * cap a + u * B +
        (l.map fun a => η * (1 + u) * cap a + u * B).sum) =
        G + (η * (1 + u) * cap a + u * B) +
          (l.map fun a => η * (1 + u) * cap a + u * B).sum := by ring
    rw [e2, e3]
    exact this

/-! ### One loop iteration -/

theorem cast_toNat {y : ℤ} (hy : 0 ≤ y) : ((y.toNat : ℕ) : ℚ) = (y : ℚ) := by
  have : ((y.toNat : ℕ) : ℤ) = y := Int.toNat_of_nonneg hy
  exact_mod_cast this

theorem toNat_lt {y : ℤ} {q : ℕ} (hy : y < q) (hq : q < 2 ^ 64) : y.toNat < 2 ^ 64 := by omega

theorem one_div_pow_le {m : ℕ} (hm1 : 1 ≤ m) (hm : m < 2 ^ 64) :
    (1 : ℚ) / 2 ^ 127 ≤ 1 / (m : ℚ) ∧ 1 / (m : ℚ) ≤ 1 := by
  have h1 : (1 : ℚ) ≤ m := by exact_mod_cast hm1
  have h2 : (m : ℚ) ≤ 2 ^ 127 := by
    have : (m : ℚ) < 2 ^ 64 := by exact_mod_cast hm
    have : (2 : ℚ) ^ 64 ≤ 2 ^ 127 := by norm_num
    linarith
  exact ⟨one_div_le_one_div_of_le (by linarith) h2, by rw [div_le_one (by linarith)]; exact h1⟩

/-- The last operation of an iteration, in either compiled form: from a term `c·b` whose exact
product and whose rounded product both approximate `v ∈ [0, 2¹²⁶]` with relative error
`η ≤ 1/2`. -/
theorem mulAdd_step (A : Arith) (hA : Conforms A) (η v c b s : ℚ) (hη : η ≤ 1 / 2)
    (hv0 : 0 ≤ v) (hv : v ≤ 2 ^ 126) (h1 : Approx η v (c * b)) (h2 : Approx η v (A.mul c b))
    (hs : 1 / 4 ≤ s) (hsW : s ≤ 2 ^ 100) :
    ∃ τ δ : ℚ, |δ| ≤ u ∧ 0 ≤ τ ∧ |τ - v| ≤ η * v ∧ A.mulAdd s c b = (s + τ) * (1 + δ) := by
  have key : ∀ τ : ℚ, Approx η v τ → 0 ≤ τ ∧ |τ - v| ≤ η * v ∧ InRange (s + τ) := by
    intro τ h
    obtain ⟨b1, b2⟩ := h.bounds hη hv0
    have hτ0 : 0 ≤ τ := le_trans (by positivity) b1
    refine ⟨hτ0, h.abs_sub_le hv0, inRange_of_bounds ?_ ?_⟩
    · have : (1 : ℚ) / 2 ^ 128 ≤ 1 / 4 := by norm_num
      linarith
    · have : (2 : ℚ) ^ 100 + 2 * 2 ^ 126 ≤ 2 ^ 128 := by norm_num
      linarith
  rcases hA.mulAdd s c b with h | h
  · obtain ⟨t0, t1, t2⟩ := key _ h2
    obtain ⟨δ, hδ, e⟩ := hA.add s (A.mul c b) t2
    exact ⟨A.mul c b, δ, hδ, t0, t1, by rw [h, e]⟩
  · obtain ⟨t0, t1, t2⟩ := key _ h1
    obtain ⟨δ, hδ, e⟩ := hA.fma c b s (by rwa [add_comm])
    exact ⟨c * b, δ, hδ, t0, t1, by rw [h, e, add_comm]⟩

/-- One iteration of the overflow sum of `SwitchCRTBasis`: `nu += fl(y) * qInv`. -/
theorem sw_step (A : Arith) (hA : Conforms A) (q : ℕ) (y : ℤ) (hq1 : 1 ≤ q) (hq : q < 2 ^ 64)
    (hy0 : 0 ≤ y) (hy : y < q) (s : ℚ) (hs : 1 / 4 ≤ s) (hsW : s ≤ 2 ^ 100) :
    ∃ τ δ : ℚ, |δ| ≤ u ∧ 0 ≤ τ ∧ |τ - (y : ℚ) / (q : ℚ)| ≤ eta4 * 1 ∧
      A.mulAdd s (A.ofNat y.toNat) (Fl.qInv A q) = (s + τ) * (1 + δ) := by
  have hqQ : (1 : ℚ) ≤ q := by exact_mod_cast hq1
  have hyQ0 : (0 : ℚ) ≤ y := by exact_mod_cast hy0
  have hyQ : (y : ℚ) < q := by exact_mod_cast hy
  obtain ⟨hq127, hq1'⟩ := one_div_pow_le hq1 hq
  -- the table entry
  have ha : Approx u q (A.ofNat q) := approx_of_rounds (hA.ofNat q hq)
  have ha0 : A.ofNat q ≠ 0 := by
    have := (ha.bounds (by unfold u; norm_num) (by linarith)).1
    intro h
    rw [h] at this
    linarith
  have h1a : Approx eInv (1 / (q : ℚ)) (1 / A.ofNat q) := by
    have := (approx_refl 1).div ha u_lt
    refine this.mono (le_of_eq ?_)
    unfold eInv
    ring
  have hin1 : InRange (1 / A.ofNat q) := h1a.inRange eInv_bound.2 (Or.inr ⟨hq127, by linarith⟩)
  have hb : Approx e2 (1 / (q : ℚ)) (Fl.qInv A q) := h1a.rounds (hA.div 1 _ ha0 hin1)
  -- the term
  have hc : Approx u y (A.ofNat y.toNat) := by
    have := approx_of_rounds (hA.ofNat y.toNat (toNat_lt hy hq))
    rwa [cast_toNat hy0] at this
  have hcb : Approx e3 ((y : ℚ) / (q : ℚ)) (A.ofNat y.toNat * Fl.qInv A q) := by
    have := hc.mul hb
    rwa [mul_one_div] at this
  have hv0 : (0 : ℚ) ≤ (y : ℚ) / (q : ℚ) := div_nonneg hyQ0 (by linarith)
  have hv1 : (y : ℚ) / (q : ℚ) ≤ 1 := by rw [div_le_one (by linarith)]; exact hyQ.le
  have hvr : (y : ℚ) / (q : ℚ) = 0 ∨
      ((1 : ℚ) / 2 ^ 127 ≤ (y : ℚ) / (q : ℚ) ∧ (y : ℚ) / (q : ℚ) ≤ 2 ^ 127) := by
    rcases eq_or_lt_of_le hy0 with h | h
    · left; rw [← h]; simp
    · right
      have hy1 : (1 : ℚ) ≤ y := by exact_mod_cast h
      refine ⟨hq127.trans ?_, hv1.trans (by norm_num)⟩
      exact div_le_div_of_nonneg_right hy1 (by linarith)
  have hin2 : InRange (A.ofNat y.toNat * Fl.qInv A q) := hcb.inRange e3_bound.2 hvr
  have hm : Approx eta4 ((y : ℚ) / (q : ℚ)) (A.mul (A.ofNat y.toNat) (Fl.qInv A q)) :=
    hcb.rounds (hA.mul _ _ hin2)
  have hcb' : Approx eta4 ((y : ℚ) / (q : ℚ)) (A.ofNat y.toNat * Fl.qInv A q) := by
    refine hcb.mono ?_
    have := e3_bound.1
    unfold eta4
    nlinarith [u_pos]
  obtain ⟨τ, δ, hδ, hτ0, hτ, e⟩ := mulAdd_step A hA eta4 _ _ _ s eta4_bound.2.1 hv0
    (hv1.trans (by norm_num)) hcb' hm hs hsW
  refine ⟨τ, δ, hδ, hτ0, hτ.trans ?_, e⟩
  exact mul_le_mul_of_nonneg_left hv1 eta4_bound.1

/-- One iteration of the fractional sum of `ScaleAndRound`: `nu += Frac * fl(x)`. -/
theorem sr_step (A : Arith) (hA : Conforms A) (m : ℕ) (n x : ℤ) (hm1 : 1 ≤ m) (hm : m < 2 ^ 64)
    (hn0 : 0 ≤ n) (hn : n < m) (hx0 : 0 ≤ x) (hx : x < m) (s : ℚ) (hs : 1 / 4 ≤ s)
    (hsW : s ≤ 2 ^ 100) :
    ∃ τ δ : ℚ, |δ| ≤ u ∧ 0 ≤ τ ∧ |τ - (x : ℚ) * (n : ℚ) / (m : ℚ)| ≤ eta5 * (m : ℚ) ∧
      A.mulAdd s (Fl.frac A n.toNat m) (A.ofNat x.toNat) = (s + τ) * (1 + δ) := by
  have hmQ : (1 : ℚ) ≤ m := by exact_mod_cast hm1
  have hmQ' : (m : ℚ) < 2 ^ 64 := by exact_mod_cast hm
  have hnQ0 : (0 : ℚ) ≤ n := by exact_mod_cast hn0
  have hnQ : (n : ℚ) < m := by exact_mod_cast hn
  have hxQ0 : (0 : ℚ) ≤ x := by exact_mod_cast hx0
  have hxQ : (x : ℚ) < m := by exact_mod_cast hx
  obtain ⟨hm127, hm1'⟩ := one_div_pow_le hm1 hm
  -- the table entry
  have ham : Approx u m (A.ofNat m) := approx_of_rounds (hA.ofNat m hm)
  have ham0 : A.ofNat m ≠ 0 := by
    have := (ham.bounds (by unfold u; norm_num) (by linarith)).1
    intro h
    rw [h] at this
    linarith
  have han : Approx u n (A.ofNat n.toNat) := by
    have := approx_of_rounds (hA.ofNat n.toNat (toNat_lt hn hm))
    rwa [cast_toNat hn0] at this
  have hq0 : Approx f0 ((n : ℚ) / (m : ℚ)) (A.ofNat n.toNat / A.ofNat m) := by
    have := han.div ham u_lt
    refine this.mono (le_of_eq ?_)
    unfold f0 eInv
    ring
  have hf0 : (0 : ℚ) ≤ (n : ℚ) / (m : ℚ) := div_nonneg hnQ0 (by linarith)
  have hf1 : (n : ℚ) / (m : ℚ) ≤ 1 := by rw [div_le_one (by linarith)]; exact hnQ.le
  have hfr : (n : ℚ) / (m : ℚ) = 0 ∨
      ((1 : ℚ) / 2 ^ 127 ≤ (n : ℚ) / (m : ℚ) ∧ (n : ℚ) / (m : ℚ) ≤ 2 ^ 127) := by
    rcases eq_or_lt_of_le hn0 with h | h
    · left; rw [← h]; simp
    · right
      have hn1 : (1 : ℚ) ≤ n := by exact_mod_cast h
      refine ⟨hm127.trans ?_, hf1.trans (by norm_num)⟩
      exact div_le_div_of_nonneg_right hn1 (by linarith)
  have hin1 : InRange (A.ofNat n.toNat / A.ofNat m) := hq0.inRange f0_bound.2 hfr
  have hF : Approx f1 ((n : ℚ) / (m : ℚ)) (Fl.frac A n.toNat m) :=
    hq0.rounds (hA.div _ _ ham0 hin1)
  -- the term
  have hcx : Approx u x (A.ofNat x.toNat) := by
    have := approx_of_rounds (hA.ofNat x.toNat (toNat_lt hx hm))
    rwa [cast_toNat hx0] at this
  have hval : (n : ℚ) / (m : ℚ) * (x : ℚ) = (x : ℚ) * (n : ℚ) / (m : ℚ) := by ring
  have hFx : Approx f2 ((x : ℚ) * (n : ℚ) / (m : ℚ))
      (Fl.frac A n.toNat m * A.ofNat x.toNat) := by
    have := hF.mul hcx
    rwa [hval] at this
  have hv0 : (0 : ℚ) ≤ (x : ℚ) * (n : ℚ) / (m : ℚ) := by
    rw [← hval]; exact mul_nonneg hf0 hxQ0
  have hvm : (x : ℚ) * (n : ℚ) / (m : ℚ) ≤ m := by
    rw [← hval]
    calc (n : ℚ) / (m : ℚ) * (x : ℚ) ≤ 1 * (m : ℚ) := mul_le_mul hf1 hxQ.le hxQ0 (by norm_num)
      _ = m := one_mul _
  have h64 : (2 : ℚ) ^ 64 ≤ 2 ^ 126 := by norm_num
  have hvr : (x : ℚ) * (n : ℚ) / (m : ℚ) = 0 ∨
      ((1 : ℚ) / 2 ^ 127 ≤ (x : ℚ) * (n : ℚ) / (m : ℚ) ∧
        (x : ℚ) * (n : ℚ) / (m : ℚ) ≤ 2 ^ 127) := by
    rcases hfr with h | ⟨h1, _⟩
    · left; rw [← hval, h, zero_mul]
    · rcases eq_or_lt_of_le hx0 with h | h
      · left; rw [← h]; simp
      · right
        have hx1 : (1 : ℚ) ≤ x := by exact_mod_cast h
        have h127 : (2 : ℚ) ^ 126 ≤ 2 ^ 127 := by norm_num
        refine ⟨?_, by linarith⟩
        rw [← hval]
        calc (1 : ℚ) / 2 ^ 127 = 1 / 2 ^ 127 * 1 := (mul_one _).symm
          _ ≤ (n : ℚ) / (m : ℚ) * (x : ℚ) := mul_le_mul h1 hx1 (by norm_num) hf0
  have hin2 : InRange (Fl.frac A n.toNat m * A.ofNat x.toNat) := hFx.inRange f2_bound.2 hvr
  have hm' : Approx eta5 ((x : ℚ) * (n : ℚ) / (m : ℚ))
      (A.mul (Fl.frac A n.toNat m) (A.ofNat x.toNat)) := hFx.rounds (hA.mul _ _ hin2)
  have hFx' : Approx eta5 ((x : ℚ) * (n : ℚ) / (m : ℚ))
      (Fl.frac A n.toNat m * A.ofNat x.toNat) := by
    refine hFx.mono ?_
    have := f2_bound.1
    unfold eta5
    nlinarith [u_pos]
  obtain ⟨τ, δ, hδ, hτ0, hτ, e⟩ := mulAdd_step A hA eta5 _ _ _ s eta5_bound.2.1 hv0
    (by linarith) hFx' hm' hs hsW
  refine ⟨τ, δ, hδ, hτ0, hτ.trans ?_, e⟩
  exact mul_le_mul_of_nonneg_left hvm eta5_bound.1

/-! ### The two sums -/

theorem sum_map_affine {α : Type} (l : List α) (f : α → ℚ) (c d : ℚ) :
    (l.map fun a => c * f a + d).sum = c * (l.map f).sum + l.length * d := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, ih]
    push_cast
    ring

theorem sum_map_le {α : Type} (l : List α) (f g : α → ℚ) (h : ∀ a ∈ l, f a ≤ g a) :
    (l.map f).sum ≤ (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    exact add_le_add (h a List.mem_cons_self) (ih fun b hb => h b (List.mem_cons_of_mem _ hb))

theorem sum_map_const {α : Type} (l : List α) (c : ℚ) :
    (l.map fun _ => c).sum = l.length * c := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, ih]
    push_cast
    ring

/-- **The overflow sum**: over at most `2¹⁶` pairs (modulus `q ∈ [1, 2⁶⁴)`, digit `y ∈ [0, q)`),
the computed sum is within `n·(n+5)·u` of `1/2 + Σ y/q`, and at least `1/4`. -/
theorem nuSw_err (A : Arith) (hA : Conforms A) (l : List (ℕ × ℤ)) (hlen : l.length ≤ 2 ^ 16)
    (hl : ∀ p ∈ l, 1 ≤ p.1 ∧ p.1 < 2 ^ 64 ∧ 0 ≤ p.2 ∧ p.2 < (p.1 : ℤ)) :
    |l.foldl (fun s p => A.mulAdd s (A.ofNat p.2.toNat) (Fl.qInv A p.1)) (1 / 2) -
        (1 / 2 + (l.map fun p => (p.2 : ℚ) / (p.1 : ℚ)).sum)| ≤
      (l.length : ℚ) * ((l.length : ℚ) + 5) * u ∧
    1 / 4 ≤ l.foldl (fun s p => A.mulAdd s (A.ofNat p.2.toNat) (Fl.qInv A p.1)) (1 / 2) ∧
    (l.map fun p => (p.2 : ℚ) / (p.1 : ℚ)).sum ≤ (l.length : ℚ) := by
  have hu := u_pos
  have hn0 : (0 : ℚ) ≤ (l.length : ℚ) := Nat.cast_nonneg _
  have hn : (l.length : ℚ) ≤ 2 ^ 16 := by exact_mod_cast hlen
  have hnu : (l.length : ℚ) * u ≤ 1 / 2 ^ 37 := by
    have : (l.length : ℚ) * u ≤ 2 ^ 16 * u := mul_le_mul_of_nonneg_right hn hu.le
    have e : (2 : ℚ) ^ 16 * u = 1 / 2 ^ 37 := by unfold u; norm_num
    linarith
  have hnu0 : 0 ≤ (l.length : ℚ) * u := mul_nonneg hn0 hu.le
  have hval : ∀ p ∈ l, (0 : ℚ) ≤ (p.2 : ℚ) / (p.1 : ℚ) ∧ (p.2 : ℚ) / (p.1 : ℚ) ≤ 1 := by
    intro p hp
    obtain ⟨h1, _, h3, h4⟩ := hl p hp
    have h1' : (1 : ℚ) ≤ p.1 := by exact_mod_cast h1
    have h3' : (0 : ℚ) ≤ p.2 := by exact_mod_cast h3
    have h4' : (p.2 : ℚ) < p.1 := by exact_mod_cast h4
    exact ⟨div_nonneg h3' (by linarith), by rw [div_le_one (by linarith)]; exact h4'.le⟩
  have hsum : (l.map fun p => (p.2 : ℚ) / (p.1 : ℚ)).sum ≤ l.length := by
    have := sum_map_le l _ (fun _ => (1 : ℚ)) fun p hp => (hval p hp).2
    rwa [sum_map_const, mul_one] at this
  have hG : (l.map fun _ : ℕ × ℤ => eta4 * (1 + u) * 1 + u * (1 / 2 + (l.length : ℚ))).sum =
      l.length * (eta4 * (1 + u) * 1 + u * (1 / 2 + (l.length : ℚ))) := sum_map_const _ _
  have h17 : (l.length : ℚ) + 37 / 8 ≤ 2 ^ 17 := by
    have : (2 : ℚ) ^ 16 + 37 / 8 ≤ 2 ^ 17 := by norm_num
    linarith
  have h2 : (l.length : ℚ) * u * ((l.length : ℚ) + 37 / 8) ≤ 1 / 2 ^ 37 * 2 ^ 17 :=
    mul_le_mul hnu h17 (by linarith) (by norm_num)
  have h3 : (1 : ℚ) / 2 ^ 37 * 2 ^ 17 ≤ 3 / 16 := by norm_num
  have hGle : (l.length : ℚ) * (eta4 * (1 + u) * 1 + u * (1 / 2 + (l.length : ℚ))) ≤
      (l.length : ℚ) * (u * ((l.length : ℚ) + 37 / 8)) := by
    refine mul_le_mul_of_nonneg_left ?_ hn0
    have := eta4_bound.2.2
    linarith
  have key := fold_err (fun s (p : ℕ × ℤ) => A.mulAdd s (A.ofNat p.2.toNat) (Fl.qInv A p.1))
    (fun p => (p.2 : ℚ) / (p.1 : ℚ)) (fun _ => 1) eta4 (1 / 2 + (l.length : ℚ)) (2 ^ 100)
    eta4_bound.1 (by linarith) l (1 / 2) (1 / 2) 0 0 hval
    (fun p hp s hs hsW => by
      obtain ⟨h1, h2, h3, h4⟩ := hl p hp
      exact sw_step A hA p.1 p.2 h1 h2 h3 h4 s hs hsW)
    (by simpa using hlen) le_rfl (by simp) (by simp) (by linarith)
    (by
      rw [hG]
      have : (1 : ℚ) / 2 + 2 ^ 16 + 2 * (0 + 1) ≤ 2 ^ 100 := by norm_num
      nlinarith)
  rw [hG] at key
  simp only [zero_add] at key
  obtain ⟨k1, k2⟩ := key
  refine ⟨k1.trans ?_, ?_, hsum⟩
  · -- (1 + 2nu)·n·u·(n + 37/8) ≤ n·(n+5)·u
    have h1 : (1 + 2 * (l.length : ℚ) * u) * ((l.length : ℚ) + 37 / 8) ≤ (l.length : ℚ) + 5 := by
      nlinarith
    have hfac : 0 ≤ 1 + 2 * (l.length : ℚ) * u := by nlinarith
    calc (1 + 2 * (l.length : ℚ) * u) *
          ((l.length : ℚ) * (eta4 * (1 + u) * 1 + u * (1 / 2 + (l.length : ℚ))))
        ≤ (1 + 2 * (l.length : ℚ) * u) * ((l.length : ℚ) * (u * ((l.length : ℚ) + 37 / 8))) :=
          mul_le_mul_of_nonneg_left hGle hfac
      _ = (l.length : ℚ) * u * ((1 + 2 * (l.length : ℚ) * u) * ((l.length : ℚ) + 37 / 8)) := by
          ring
      _ ≤ (l.length : ℚ) * u * ((l.length : ℚ) + 5) := mul_le_mul_of_nonneg_left h1 hnu0
      _ = (l.length : ℚ) * ((l.length : ℚ) + 5) * u := by ring
  · have : (1 : ℚ) / 2 ^ 37 ≤ 1 / 2 := by norm_num
    linarith

/-- **The scaling sum**: over at most `2¹⁶` triples (modulus `m ∈ [1, 2⁶⁴)`, numerator
`n ∈ [0, m)`, residue `x ∈ [0, m)`), the computed sum is within `(k+6)·(1 + Σ m)·u` of
`1/2 + Σ x·n/m`, and at least `1/4`. -/
theorem nuSr_err (A : Arith) (hA : Conforms A) (l : List ((ℕ × ℤ) × ℤ))
    (hlen : l.length ≤ 2 ^ 16)
    (hl : ∀ p ∈ l, 1 ≤ p.1.1 ∧ p.1.1 < 2 ^ 64 ∧ (0 ≤ p.1.2 ∧ p.1.2 < (p.1.1 : ℤ)) ∧
      0 ≤ p.2 ∧ p.2 < (p.1.1 : ℤ)) :
    |l.foldl (fun s p => A.mulAdd s (Fl.frac A p.1.2.toNat p.1.1) (A.ofNat p.2.toNat)) (1 / 2) -
        (1 / 2 + (l.map fun p => (p.2 : ℚ) * (p.1.2 : ℚ) / (p.1.1 : ℚ)).sum)| ≤
      ((l.length : ℚ) + 6) * (1 + (l.map fun p => (p.1.1 : ℚ)).sum) * u ∧
    1 / 4 ≤ l.foldl
      (fun s p => A.mulAdd s (Fl.frac A p.1.2.toNat p.1.1) (A.ofNat p.2.toNat)) (1 / 2) ∧
    (l.map fun p => (p.2 : ℚ) * (p.1.2 : ℚ) / (p.1.1 : ℚ)).sum ≤
      (l.map fun p => (p.1.1 : ℚ)).sum ∧
    (l.map fun p => (p.1.1 : ℚ)).sum ≤ (l.length : ℚ) * 2 ^ 64 := by
  have hu := u_pos
  set M : ℚ := (l.map fun p => (p.1.1 : ℚ)).sum with hM
  have hn0 : (0 : ℚ) ≤ (l.length : ℚ) := Nat.cast_nonneg _
  have hn : (l.length : ℚ) ≤ 2 ^ 16 := by exact_mod_cast hlen
  have hnu : (l.length : ℚ) * u ≤ 1 / 2 ^ 37 := by
    have : (l.length : ℚ) * u ≤ 2 ^ 16 * u := mul_le_mul_of_nonneg_right hn hu.le
    have e : (2 : ℚ) ^ 16 * u = 1 / 2 ^ 37 := by unfold u; norm_num
    linarith
  have hnu0 : 0 ≤ (l.length : ℚ) * u := mul_nonneg hn0 hu.le
  have hval : ∀ p ∈ l, (0 : ℚ) ≤ (p.2 : ℚ) * (p.1.2 : ℚ) / (p.1.1 : ℚ) ∧
      (p.2 : ℚ) * (p.1.2 : ℚ) / (p.1.1 : ℚ) ≤ (p.1.1 : ℚ) := by
    intro p hp
    obtain ⟨h1, _, ⟨h3, h4⟩, h5, h6⟩ := hl p hp
    have h1' : (1 : ℚ) ≤ p.1.1 := by exact_mod_cast h1
    have h3' : (0 : ℚ) ≤ p.1.2 := by exact_mod_cast h3
    have h4' : (p.1.2 : ℚ) < p.1.1 := by exact_mod_cast h4
    have h5' : (0 : ℚ) ≤ p.2 := by exact_mod_cast h5
    have h6' : (p.2 : ℚ) < p.1.1 := by exact_mod_cast h6
    refine ⟨div_nonneg (mul_nonneg h5' h3') (by linarith), ?_⟩
    rw [div_le_iff₀ (by linarith)]
    exact mul_le_mul h6'.le h4'.le h3' (by linarith)
  have hsum : (l.map fun p => (p.2 : ℚ) * (p.1.2 : ℚ) / (p.1.1 : ℚ)).sum ≤ M :=
    sum_map_le l _ _ fun p hp => (hval p hp).2
  have hM0 : 0 ≤ M := List.sum_nonneg fun x hx => by
    obtain ⟨b, _, rfl⟩ := List.mem_map.mp hx
    exact Nat.cast_nonneg _
  have hMle : M ≤ (l.length : ℚ) * 2 ^ 64 := by
    have := sum_map_le l (fun p => (p.1.1 : ℚ)) (fun _ => (2 : ℚ) ^ 64) fun p hp => by
      have := (hl p hp).2.1
      have : (p.1.1 : ℚ) < 2 ^ 64 := by exact_mod_cast this
      exact this.le
    rwa [sum_map_const] at this
  have hM80 : M ≤ 2 ^ 80 := by
    have : (l.length : ℚ) * 2 ^ 64 ≤ 2 ^ 16 * 2 ^ 64 :=
      mul_le_mul_of_nonneg_right hn (by positivity)
    have e : (2 : ℚ) ^ 16 * 2 ^ 64 = 2 ^ 80 := by norm_num
    linarith
  have hG : (l.map fun p : (ℕ × ℤ) × ℤ =>
        eta5 * (1 + u) * (p.1.1 : ℚ) + u * (1 / 2 + M)).sum =
      eta5 * (1 + u) * M + l.length * (u * (1 / 2 + M)) := sum_map_affine l _ _ _
  have hGle : eta5 * (1 + u) * M + (l.length : ℚ) * (u * (1 / 2 + M)) ≤
      u * (((l.length : ℚ) + 21 / 4) * (M + 1)) := by
    have h1 : eta5 * (1 + u) * M ≤ 21 / 4 * u * M :=
      mul_le_mul_of_nonneg_right eta5_bound.2.2 hM0
    have h2 : 0 ≤ u * (l.length : ℚ) := mul_nonneg hu.le hn0
    nlinarith
  have h17 : (l.length : ℚ) + 21 / 4 ≤ 2 ^ 17 := by
    have : (2 : ℚ) ^ 16 + 21 / 4 ≤ 2 ^ 17 := by norm_num
    linarith
  have hGsmall : u * (((l.length : ℚ) + 21 / 4) * (M + 1)) ≤ 2 ^ 46 := by
    have h2 : ((l.length : ℚ) + 21 / 4) * (M + 1) ≤ 2 ^ 17 * (2 ^ 80 + 1) :=
      mul_le_mul h17 (by linarith) (by linarith) (by norm_num)
    have h3 : u * (((l.length : ℚ) + 21 / 4) * (M + 1)) ≤ u * (2 ^ 17 * (2 ^ 80 + 1)) :=
      mul_le_mul_of_nonneg_left h2 hu.le
    have h4 : u * (2 ^ 17 * (2 ^ 80 + 1)) ≤ 2 ^ 46 := by unfold u; norm_num
    linarith
  have key := fold_err
    (fun s (p : (ℕ × ℤ) × ℤ) => A.mulAdd s (Fl.frac A p.1.2.toNat p.1.1) (A.ofNat p.2.toNat))
    (fun p => (p.2 : ℚ) * (p.1.2 : ℚ) / (p.1.1 : ℚ)) (fun p => (p.1.1 : ℚ)) eta5 (1 / 2 + M)
    (2 ^ 100) eta5_bound.1 (by linarith) l (1 / 2) (1 / 2) 0 0 hval
    (fun p hp s hs hsW => by
      obtain ⟨h1, h2, ⟨h3, h4⟩, h5, h6⟩ := hl p hp
      exact sr_step A hA p.1.1 p.1.2 p.2 h1 h2 h3 h4 h5 h6 s hs hsW)
    (by simpa using hlen) le_rfl (by simp) (by simp) (by linarith)
    (by
      rw [hG]
      have : (1 : ℚ) / 2 + 2 ^ 80 + 2 * (0 + 2 ^ 46) ≤ 2 ^ 100 := by norm_num
      linarith)
  rw [hG] at key
  simp only [zero_add] at key
  obtain ⟨k1, k2⟩ := key
  refine ⟨k1.trans ?_, ?_, hsum, hMle⟩
  · have h2 : (l.length : ℚ) * u * ((l.length : ℚ) + 21 / 4) ≤ 1 / 2 ^ 37 * 2 ^ 17 :=
      mul_le_mul hnu h17 (by linarith) (by norm_num)
    have h3 : (1 : ℚ) / 2 ^ 37 * 2 ^ 17 ≤ 3 / 8 := by norm_num
    have h1 : (1 + 2 * (l.length : ℚ) * u) * ((l.length : ℚ) + 21 / 4) ≤ (l.length : ℚ) + 6 := by
      nlinarith
    have hfac : 0 ≤ 1 + 2 * (l.length : ℚ) * u := by nlinarith
    calc (1 + 2 * (l.length : ℚ) * u) *
          (eta5 * (1 + u) * M + (l.length : ℚ) * (u * (1 / 2 + M)))
        ≤ (1 + 2 * (l.length : ℚ) * u) * (u * (((l.length : ℚ) + 21 / 4) * (M + 1))) :=
          mul_le_mul_of_nonneg_left hGle hfac
      _ = u * (M + 1) * ((1 + 2 * (l.length : ℚ) * u) * ((l.length : ℚ) + 21 / 4)) := by ring
      _ ≤ u * (M + 1) * ((l.length : ℚ) + 6) :=
          mul_le_mul_of_nonneg_left h1 (mul_nonneg hu.le (by linarith))
      _ = ((l.length : ℚ) + 6) * (1 + M) * u := by ring
  · have : (1 : ℚ) / 2 ^ 37 ≤ 1 / 2 := by norm_num
    linarith

end FHE.Float
