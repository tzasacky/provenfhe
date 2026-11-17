import FHE.KeySwitch.Gadget

/-!
# FHE.KeySwitch.Core — the integer heart of hybrid key switching

Everything about hybrid key switching that is not RNS bookkeeping happens on integer
polynomials, and is stated here independently of how the ModUp lifts `Dⱼ` and the ModDown
outputs were computed:

* `ks_core` — **exact phase equation.** If
  - `Σⱼ gⱼ·Dⱼ ≡ P·X (mod Q·P)` (the gadget identity, `gadget_poly`),
  - each key pair satisfies `Kbⱼ + Kaⱼ·s ≡ gⱼ·T + eⱼ (mod Q·P)`,
  - ModDown returned `y₀, y₁` with `P·y₀ = Σⱼ Dⱼ·Kbⱼ + t·f₀` and `P·y₁ = Σⱼ Dⱼ·Kaⱼ + t·f₁`
    (exact integer equations; `t = 1` for the plain ModDown),

  then `y₀ + y₁·s ≡ X·T + err (mod Q)` with the *exact* error
  `P·err = Σⱼ Dⱼ·eⱼ + t·(f₀ + f₁·s)`.
* `ks_core_dvd` — if `t ∣ eⱼ` (BGV keys) and `gcd(t, P) = 1`, then `t ∣ err`.
* `ks_core_bound` — `2P·‖err‖∞ ≤ N·B_k·Σⱼ Mⱼ + t·F·(1 + N·B_s)` whenever `2‖Dⱼ‖∞ ≤ Mⱼ`,
  `‖eⱼ‖∞ ≤ B_k`, `2‖fᵢ‖∞ ≤ F`, `‖s‖∞ ≤ B_s`.

No size condition (`2·|·| < Q·P` or similar) is needed anywhere: all statements are exact
integer equations and congruences, so nothing can wrap around.
-/

namespace FHE.KeySwitch

open Finset Spec Spec.NPoly FHE.RNS Validation.Ring Validation.Scheme

variable {N : ℕ}

/-- **Exact phase equation of hybrid key switching** (integer level). -/
theorem ks_core [NeZero N] {Q P t : ℕ} (hP : 0 < P) {dnum : ℕ} (G : Fin dnum → ℤ)
    (D Kb Ka e : Fin dnum → IntPoly N) (X T s y0 y1 f0 f1 : IntPoly N)
    (hgad : ofInt (Q * P) (∑ j, (G j : IntPoly N) * D j - (P : IntPoly N) * X) = 0)
    (hkey : ∀ j, ofInt (Q * P) (Kb j + Ka j * s - (G j : IntPoly N) * T - e j) = 0)
    (h0 : ∀ c, (P : ℤ) * y0.coeff c = (∑ j, D j * Kb j).coeff c + t * f0.coeff c)
    (h1 : ∀ c, (P : ℤ) * y1.coeff c = (∑ j, D j * Ka j).coeff c + t * f1.coeff c) :
    ∃ err : IntPoly N, ofInt Q (y0 + y1 * s) = ofInt Q (X * T + err) ∧
      ∀ c, (P : ℤ) * err.coeff c = (∑ j, D j * e j).coeff c + t * (f0 + f1 * s).coeff c := by
  set W : IntPoly N := ∑ j, D j * e j + (t : IntPoly N) * (f0 + f1 * s) with hW
  have hY0 : (P : IntPoly N) * y0 = ∑ j, D j * Kb j + (t : IntPoly N) * f0 := by
    ext c; rw [coeff_natCast_mul', h0, coeff_add', coeff_natCast_mul']
  have hY1 : (P : IntPoly N) * y1 = ∑ j, D j * Ka j + (t : IntPoly N) * f1 := by
    ext c; rw [coeff_natCast_mul', h1, coeff_add', coeff_natCast_mul']
  have e1 : ∀ j, D j * (Kb j + Ka j * s - (G j : IntPoly N) * T - e j) =
      D j * Kb j + (D j * Ka j) * s - ((G j : IntPoly N) * D j) * T - D j * e j := by
    intro j; ring
  have hsum : ∑ j, D j * (Kb j + Ka j * s - (G j : IntPoly N) * T - e j) =
      ∑ j, D j * Kb j + (∑ j, D j * Ka j) * s - (∑ j, (G j : IntPoly N) * D j) * T -
        ∑ j, D j * e j := by
    simp only [e1, Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_mul]
  have key : (P : IntPoly N) * (y0 + y1 * s - X * T) - W =
      (∑ j, (G j : IntPoly N) * D j - (P : IntPoly N) * X) * T +
        ∑ j, D j * (Kb j + Ka j * s - (G j : IntPoly N) * T - e j) := by
    rw [hsum, hW]
    linear_combination hY0 + s * hY1
  have hz : ofInt (Q * P) ((P : IntPoly N) * (y0 + y1 * s - X * T) - W) = 0 := by
    rw [key, ofInt_add, ofInt_mul, hgad, zero_mul, zero_add, ofInt_sum]
    exact Finset.sum_eq_zero fun j _ => by rw [ofInt_mul, hkey j, mul_zero]
  rw [ofInt_eq_zero_iff] at hz
  have hPz : (P : ℤ) ≠ 0 := by exact_mod_cast hP.ne'
  have hWc : ∀ c, W.coeff c = (∑ j, D j * e j).coeff c + t * (f0 + f1 * s).coeff c := by
    intro c; rw [hW, coeff_add', coeff_natCast_mul']
  have hPW : ∀ c, (P : ℤ) ∣ W.coeff c := by
    intro c
    have h := hz c
    rw [coeff_sub', coeff_natCast_mul'] at h
    have h2 : (P : ℤ) ∣ (P : ℤ) * (y0 + y1 * s - X * T).coeff c - W.coeff c :=
      (dvd_mul_left (P : ℤ) Q).trans (by exact_mod_cast h)
    have h3 := (dvd_mul_right (P : ℤ) ((y0 + y1 * s - X * T).coeff c)).sub h2
    simpa using h3
  refine ⟨⟨fun c => W.coeff c / P⟩, ?_, fun c => ?_⟩
  · ext c
    rw [coeff_ofInt, coeff_ofInt, ZMod.intCast_eq_intCast_iff_dvd_sub]
    have h := hz c
    rw [coeff_sub', coeff_natCast_mul'] at h
    have hm : ((Q * P : ℕ) : ℤ) ∣
        ((X * T + ⟨fun c => W.coeff c / P⟩).coeff c - (y0 + y1 * s).coeff c) * P := by
      have e2 : ((X * T + ⟨fun c => W.coeff c / P⟩ : IntPoly N).coeff c - (y0 + y1 * s).coeff c)
          * P = -((P : ℤ) * (y0 + y1 * s - X * T).coeff c - W.coeff c) := by
        rw [coeff_add', coeff_sub']
        have := Int.ediv_mul_cancel (hPW c)
        simp only at this ⊢
        rw [mul_comm _ (P : ℤ)]
        linear_combination this
      rw [e2, dvd_neg]; exact h
    rw [Nat.cast_mul] at hm
    exact (mul_dvd_mul_iff_right hPz).mp hm
  · show (P : ℤ) * (W.coeff c / P) = _
    rw [Int.mul_ediv_cancel' (hPW c), hWc]

/-- **`t` divides the key-switching error** when it divides every key error and is coprime
to `P`. -/
theorem ks_core_dvd [NeZero N] {P t : ℕ} (htP : Nat.Coprime t P) {dnum : ℕ}
    (D e : Fin dnum → IntPoly N) (s f0 f1 err : IntPoly N)
    (he : ∀ j c, (t : ℤ) ∣ (e j).coeff c)
    (herr : ∀ c, (P : ℤ) * err.coeff c = (∑ j, D j * e j).coeff c + t * (f0 + f1 * s).coeff c)
    (c : Fin N) : (t : ℤ) ∣ err.coeff c := by
  have hE : ofInt t (∑ j, D j * e j) = 0 := by
    rw [ofInt_sum]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [ofInt_mul, (ofInt_eq_zero_iff (e j)).mpr (he j), mul_zero]
  have h1 : (t : ℤ) ∣ err.coeff c * P := by
    rw [mul_comm, herr c]
    exact ((ofInt_eq_zero_iff _).mp hE c).add (dvd_mul_right _ _)
  exact (Nat.isCoprime_iff_coprime.mpr htP).dvd_of_dvd_mul_right h1

/-- The explicit worst-case bound: `(N·B_k·Σⱼ Mⱼ + t·F·(1 + N·B_s)) / (2P)` (floor). -/
def ksBound (N Bk Bs t F P : ℕ) {dnum : ℕ} (M : Fin dnum → ℕ) : ℕ :=
  (N * Bk * ∑ j, M j + t * F * (1 + N * Bs)) / (2 * P)

/-- **The noise bound** from the exact error equation. -/
theorem ks_core_bound [NeZero N] {P t F Bk Bs : ℕ} (hP : 0 < P) {dnum : ℕ}
    (D e : Fin dnum → IntPoly N) (M : Fin dnum → ℕ) (s f0 f1 err : IntPoly N)
    (hD : ∀ j, 2 * normInf (D j) ≤ M j) (he : ∀ j, normInf (e j) ≤ Bk)
    (hs : normInf s ≤ Bs) (hf0 : 2 * normInf f0 ≤ F) (hf1 : 2 * normInf f1 ≤ F)
    (herr : ∀ c, (P : ℤ) * err.coeff c = (∑ j, D j * e j).coeff c + t * (f0 + f1 * s).coeff c) :
    normInf err ≤ ksBound N Bk Bs t F P M := by
  rw [normInf_le_iff]
  intro c
  -- the key-noise term
  have hE : 2 * |(∑ j, D j * e j).coeff c| ≤ (N : ℤ) * Bk * ∑ j, (M j : ℤ) := by
    rw [coeff_sum']
    calc 2 * |∑ j, (D j * e j).coeff c| ≤ 2 * ∑ j, |(D j * e j).coeff c| := by
          gcongr; exact Finset.abs_sum_le_sum_abs _ _
      _ = ∑ j, 2 * |(D j * e j).coeff c| := Finset.mul_sum _ _ _
      _ ≤ ∑ j, (N : ℤ) * Bk * M j := Finset.sum_le_sum fun j _ => by
          have h := abs_coeff_mul_le_N (D j) (e j) (normInf (D j)) Bk
            (abs_coeff_le_normInf (D j)) (fun i => (abs_coeff_le_normInf (e j) i).trans
              (by exact_mod_cast he j)) c
          have hM : 2 * (normInf (D j) : ℤ) ≤ M j := by exact_mod_cast hD j
          have hNB : (0 : ℤ) ≤ N * Bk := by positivity
          nlinarith
      _ = (N : ℤ) * Bk * ∑ j, (M j : ℤ) := (Finset.mul_sum _ _ _).symm
  -- the ModDown term
  have hf0c : 2 * |f0.coeff c| ≤ F :=
    (mul_le_mul_of_nonneg_left (abs_coeff_le_normInf f0 c) (by norm_num)).trans
      (by exact_mod_cast hf0)
  have hf1s : 2 * |(f1 * s).coeff c| ≤ (N : ℤ) * F * Bs := by
    have h := abs_coeff_mul_le_N f1 s (normInf f1) Bs (abs_coeff_le_normInf f1)
      (fun i => (abs_coeff_le_normInf s i).trans (by exact_mod_cast hs)) c
    have hF : 2 * (normInf f1 : ℤ) ≤ F := by exact_mod_cast hf1
    have hNB : (0 : ℤ) ≤ N * Bs := by positivity
    nlinarith
  have hfs : 2 * |(f0 + f1 * s).coeff c| ≤ (F : ℤ) * (1 + N * Bs) := by
    rw [coeff_add']
    have := abs_add_le (f0.coeff c) ((f1 * s).coeff c)
    nlinarith
  have hPc : (2 * P : ℤ) * |err.coeff c| ≤
      (N : ℤ) * Bk * ∑ j, (M j : ℤ) + t * F * (1 + N * Bs) := by
    have h := herr c
    have h2 : (P : ℤ) * |err.coeff c| = |(∑ j, D j * e j).coeff c + t * (f0 + f1 * s).coeff c| := by
      rw [← h, abs_mul, abs_of_nonneg (by positivity : (0 : ℤ) ≤ P)]
    have h3 := abs_add_le ((∑ j, D j * e j).coeff c) (t * (f0 + f1 * s).coeff c)
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℤ) ≤ t)] at h3
    have ht : (0 : ℤ) ≤ t := by positivity
    have h4 : (t : ℤ) * (2 * |(f0 + f1 * s).coeff c|) ≤ t * (F * (1 + N * Bs)) :=
      mul_le_mul_of_nonneg_left hfs ht
    nlinarith
  unfold ksBound
  have h2P : (0 : ℤ) < 2 * P := by positivity
  rw [Int.natCast_div]
  push_cast
  rw [Int.le_ediv_iff_mul_le h2P]
  linarith

end FHE.KeySwitch
