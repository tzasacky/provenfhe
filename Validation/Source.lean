import Challenge.Source
import Validation.Scheme.Basic
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.FieldSimp

/-!
# Validation.Source — realizability pins of `Challenge.Source`
-/

namespace Validation.Source
open Spec NPoly Scheme Layout Source Correct Validation.Ring Validation.Scheme

/-! ### Unfolding `Encrypts` -/

theorem encrypts_bgv_iff (P : FullParams) (hk : P.src.kind = .bgv) (s : IntPoly P.src.N) (B : ℕ)
    (v : Val P.src) (ct : List (IntPoly P.src.N)) :
    Encrypts P s B v ct ↔ ct.length = v.parts ∧ ∃ m, v.msg = .exact m ∧
      BGVEncrypts P.src.t B (automorph v.key s) (ct.map (ofInt (P.src.modulus v.level))) m := by
  unfold Encrypts
  simp only [hk]
  cases h : v.msg with
  | exact m => simp [h]

theorem set_self {Pr : Params} (ρ : Env Pr) (d : Var) (v : Val Pr) : ρ.set d v d = some v := by
  simp [Env.set]

/-! ### Lists -/

theorem map_ofInt_zipWith {N : ℕ} (Q : ℕ) : ∀ (c d : List (IntPoly N)),
    (List.zipWith (· + ·) c d).map (ofInt Q) = List.zipWith (· + ·) (c.map (ofInt Q)) (d.map (ofInt Q))
  | [], _ => by simp
  | _ :: _, [] => by simp
  | a :: c, b :: d => by
      simp only [List.zipWith_cons_cons, List.map_cons, ofInt_add, map_ofInt_zipWith Q c d]

theorem modulus_pred (Pr : Params) (ℓ : ℕ) (h1 : 1 ≤ ℓ) (h2 : ℓ ≤ Pr.qs.length) :
    Pr.modulus ℓ = Pr.modulus (ℓ - 1) * Pr.qs[ℓ - 1]! := by
  unfold Params.modulus
  have hlt : ℓ - 1 < Pr.qs.length := by omega
  have := List.prod_take_succ Pr.qs (ℓ - 1) hlt
  rw [Nat.sub_add_cancel h1] at this
  rw [this]; simp [hlt]

theorem getD_eq (Pr : Params) (ℓ : ℕ) (h : ℓ < Pr.qs.length) : Pr.qs.getD ℓ 0 = Pr.qs[ℓ]! := by
  simp [List.getD_eq_getElem?_getD, h]

theorem qLast_facts (P : FullParams) (hP : SchemeParamsOK P) (ℓ : ℕ) (h : ℓ < P.src.qs.length) :
    Nat.Prime P.src.qs[ℓ]! ∧ Nat.Coprime P.src.t P.src.qs[ℓ]! := by
  have hmem : P.src.qs[ℓ]! ∈ P.src.qs := by simp [h]
  exact ⟨hP.prime _ hmem, hP.plaintext.2 _ hmem⟩

/-! ### Automorphisms -/

section Automorph
variable {R : Type} [CommRing R] {N : ℕ}

theorem mkQ_comp_eq {g : ℕ} (hg : g % 2 = 1) {p p' : Polynomial R} (h : mkQ R N p = mkQ R N p') :
    mkQ R N (p.comp (Polynomial.X ^ g)) = mkQ R N (p'.comp (Polynomial.X ^ g)) := by
  rw [Ideal.Quotient.eq, Ideal.mem_span_singleton] at h ⊢
  obtain ⟨c, hc⟩ := h
  have hodd : Odd g := Nat.odd_iff.mpr hg
  obtain ⟨c', hc'⟩ := Odd.add_dvd_pow_add_pow (Polynomial.X ^ N : Polynomial R) 1 hodd
  refine ⟨c' * c.comp (Polynomial.X ^ g), ?_⟩
  rw [← Polynomial.sub_comp, hc, Polynomial.mul_comp, Polynomial.add_comp, Polynomial.X_pow_comp,
    Polynomial.one_comp, ← pow_mul, mul_comm g N, pow_mul]
  rw [one_pow] at hc'
  rw [hc']; ring

theorem automorph_automorph {g : ℕ} (hg : g % 2 = 1) (k : ℕ) (a : NPoly R N) :
    automorph g (automorph k a) = automorph (k * g) a := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · exact eq_of_N_zero hN _ _
  apply toQuot_injective hN
  rw [toQuot_automorph, toQuot_automorph]
  have h1 : mkQ R N (toPolynomial (automorph k a)) =
      mkQ R N ((toPolynomial a).comp (Polynomial.X ^ k)) := by
    rw [← toQuot_def, toQuot_automorph]
  have := mkQ_comp_eq hg h1
  refine this.trans ?_
  rw [Polynomial.comp_assoc, Polynomial.X_pow_comp, ← pow_mul, mul_comm g k]

theorem automorph_mod (n : ℕ) (a : NPoly R N) : automorph (n % (2 * N)) a = automorph n a := by
  ext k
  simp only [coeff_automorph']
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod]

theorem automorph_add (g : ℕ) (a b : NPoly R N) :
    automorph g (a + b) = automorph g a + automorph g b := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · exact eq_of_N_zero hN _ _
  apply toQuot_injective hN
  rw [toQuot_add, toQuot_automorph, toQuot_automorph, toQuot_automorph, toPolynomial_add,
    Polynomial.add_comp, map_add]

theorem automorph_mul {g : ℕ} (hg : g % 2 = 1) (a b : NPoly R N) :
    automorph g (a * b) = automorph g a * automorph g b := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · exact eq_of_N_zero hN _ _
  apply toQuot_injective hN
  rw [toQuot_mul, toQuot_automorph, toQuot_automorph, toQuot_automorph]
  have h1 : mkQ R N (toPolynomial (a * b)) = mkQ R N (toPolynomial a * toPolynomial b) := by
    rw [← toQuot_def, toQuot_mul, map_mul]; rfl
  rw [mkQ_comp_eq hg h1, Polynomial.mul_comp, map_mul]

theorem automorph_zero (g : ℕ) : automorph g (0 : NPoly R N) = 0 := by
  ext k; simp [coeff_automorph']

theorem phase_automorph {q : ℕ} {g : ℕ} (hg : g % 2 = 1) (s : Poly q N) :
    ∀ cs : List (Poly q N), phase (automorph g s) (cs.map (automorph g)) = automorph g (phase s cs)
  | [] => by simp [phase, automorph_zero]
  | c :: cs => by
      simp only [List.map_cons, phase]
      rw [phase_automorph hg s cs, automorph_add, automorph_mul hg]

end Automorph

theorem coprime_of_pow2 {N g : ℕ} (hN : ∃ k, N = 2 ^ k) (hg : g % 2 = 1) : Nat.gcd N g = 1 := by
  obtain ⟨k, rfl⟩ := hN
  apply Nat.Coprime.pow_left
  rw [Nat.coprime_comm, Nat.coprime_two_right]
  exact Nat.odd_iff.mpr hg

theorem abs_coeff_automorph_le {N : ℕ} (hN : ∃ k, N = 2 ^ k) {g : ℕ} (hg : g % 2 = 1)
    (a : IntPoly N) (B : ℤ) (ha : ∀ i, |a.coeff i| ≤ B) (k : Fin N) :
    |(automorph g a).coeff k| ≤ B := by
  rw [coeff_automorph']
  have hB : 0 ≤ B := (abs_nonneg _).trans (ha k)
  by_cases h : ∃ i : Fin N, (i.val * g) % (2 * N) = k.val ∨ (i.val * g) % (2 * N) = k.val + N
  · obtain ⟨i0, hi0⟩ := h
    rw [Finset.sum_eq_single i0]
    · split_ifs
      · exact ha i0
      · rw [abs_neg]; exact ha i0
      · simpa using hB
    · intro j _ hj
      have hn : ¬ ((j.val * g) % (2 * N) = k.val ∨ (j.val * g) % (2 * N) = k.val + N) := by
        intro hjc
        apply hj
        have hm : ∀ x, x % (2 * N) % N = x % N := fun x =>
          Nat.mod_mod_of_dvd x (Dvd.intro_left 2 rfl)
        have e1 : (i0.val * g) % N = k.val := by
          rw [← hm]; rcases hi0 with h | h <;> rw [h] <;> simp [Nat.mod_eq_of_lt k.isLt]
        have e2 : (j.val * g) % N = k.val := by
          rw [← hm]; rcases hjc with h | h <;> rw [h] <;> simp [Nat.mod_eq_of_lt k.isLt]
        have hmod : j.val * g ≡ i0.val * g [MOD N] := by
          unfold Nat.ModEq; rw [e1, e2]
        have := Nat.ModEq.cancel_right_of_coprime (coprime_of_pow2 hN hg) hmod
        unfold Nat.ModEq at this
        rw [Nat.mod_eq_of_lt j.isLt, Nat.mod_eq_of_lt i0.isLt] at this
        exact Fin.ext this
      push Not at hn
      simp [hn.1, hn.2]
    · intro hh; exact absurd (Finset.mem_univ _) hh
  · push Not at h
    rw [Finset.sum_eq_zero]
    · simpa using hB
    · intro i _; simp [(h i).1, (h i).2]

/-- Automorphisms do not increase the ℓ¹ norm (for any `g`). -/
theorem sum_abs_automorph_le {N : ℕ} (g : ℕ) (a : IntPoly N) :
    ∑ k, |(automorph g a).coeff k| ≤ ∑ i, |a.coeff i| := by
  simp only [coeff_automorph']
  calc ∑ k : Fin N, |∑ i : Fin N, (if (i.val * g) % (2 * N) = k.val then a.coeff i
          else if (i.val * g) % (2 * N) = k.val + N then -a.coeff i else 0)|
      ≤ ∑ k : Fin N, ∑ i : Fin N, |(if (i.val * g) % (2 * N) = k.val then a.coeff i
          else if (i.val * g) % (2 * N) = k.val + N then -a.coeff i else 0)| :=
        Finset.sum_le_sum fun k _ => Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i : Fin N, ∑ k : Fin N, |(if (i.val * g) % (2 * N) = k.val then a.coeff i
          else if (i.val * g) % (2 * N) = k.val + N then -a.coeff i else 0)| := Finset.sum_comm
    _ ≤ ∑ i : Fin N, |a.coeff i| := by
        refine Finset.sum_le_sum fun i _ => ?_
        by_cases h : ∃ k : Fin N, (i.val * g) % (2 * N) = k.val ∨ (i.val * g) % (2 * N) = k.val + N
        · obtain ⟨k0, hk0⟩ := h
          rw [Finset.sum_eq_single k0]
          · split_ifs <;> simp
          · intro k _ hk
            have h1 : (i.val * g) % (2 * N) ≠ k.val := by
              intro h; apply hk; apply Fin.ext; have := k.isLt; have := k0.isLt; omega
            have h2 : (i.val * g) % (2 * N) ≠ k.val + N := by
              intro h; apply hk; apply Fin.ext; have := k.isLt; have := k0.isLt; omega
            simp [h1, h2]
          · intro hh; exact absurd (Finset.mem_univ _) hh
        · push Not at h
          rw [Finset.sum_eq_zero]
          · exact abs_nonneg _
          · intro k _; simp [(h k).1, (h k).2]

/-! ### The division step shared by modulus switching and rescaling -/

theorem coeff_natCast_mul {N : ℕ} (n : ℕ) (a : IntPoly N) (i : Fin N) [NeZero N] :
    ((n : IntPoly N) * a).coeff i = (n : ℤ) * a.coeff i := by
  rw [natCast_def, coeff_const_mul]

theorem divq_core {N : ℕ} (Q' q : ℕ) (sk c0 c1 E d0 d1 c0' c1' : IntPoly N)
    (hE : ofInt (Q' * q) (c0 + sk * c1) = ofInt (Q' * q) E)
    (h0 : ∀ i, (q : ℤ) * c0'.coeff i = c0.coeff i + d0.coeff i)
    (h1 : ∀ i, (q : ℤ) * c1'.coeff i = c1.coeff i + d1.coeff i) :
    ∃ e : IntPoly N, ofInt Q' (c0' + sk * c1') = ofInt Q' e ∧
      ∀ i, (q : ℤ) * e.coeff i = E.coeff i + d0.coeff i + (sk * d1).coeff i := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · exact ⟨0, eq_of_N_zero hN _ _, fun i => absurd i.isLt (by omega)⟩
  have : NeZero N := ⟨hN.ne'⟩
  have hK : ∀ i, ∃ j : ℤ, (c0 + sk * c1).coeff i = E.coeff i + ((Q' * q : ℕ) : ℤ) * j := by
    intro i
    have := congrArg (fun p => p.coeff i) hE
    simp only [coeff_ofInt] at this
    exact exists_eq_add_mul_of_cast_eq this
  choose K hK using hK
  let Kp : IntPoly N := ⟨K⟩
  refine ⟨c0' + sk * c1' - (Q' : IntPoly N) * Kp, ?_, ?_⟩
  · rw [ofInt_sub, ofInt_mul, natCast_def, ofInt_const]
    have : ((Q' : ℤ) : ZMod Q') = 0 := by simp
    rw [this]
    have hz : (const (0 : ZMod Q') : Poly Q' N) = 0 := by ext i; simp
    rw [hz, zero_mul, sub_zero]
  · have hc0 : (q : IntPoly N) * c0' = c0 + d0 := by
      ext i; rw [coeff_natCast_mul, h0, coeff_add']
    have hc1 : (q : IntPoly N) * c1' = c1 + d1 := by
      ext i; rw [coeff_natCast_mul, h1, coeff_add']
    have hW : c0 + sk * c1 = E + ((Q' * q : ℕ) : IntPoly N) * Kp := by
      ext i; rw [hK i, coeff_add', coeff_natCast_mul]
    have key : (q : IntPoly N) * (c0' + sk * c1' - (Q' : IntPoly N) * Kp) = E + d0 + sk * d1 := by
      push_cast at hW
      linear_combination hc0 + sk * hc1 + hW
    intro i
    have := congrArg (fun p => p.coeff i) key
    simp only [coeff_natCast_mul, coeff_add'] at this
    exact this

/-- The arithmetic of the noise bound after dividing by `q`. -/
theorem div_bound {α : Type} [CommRing α] [LinearOrder α] [IsStrictOrderedRing α]
    (q B b t S n h y E d0 X : α) (hq : 0 < q) (hqy : q * y = E + d0 + X) (hE : |E| ≤ B)
    (hd0 : |d0| ≤ t * h) (hX : |X| ≤ S * (t * h)) (hS0 : 0 ≤ S) (hS : S ≤ n) (h2 : 2 * h ≤ q)
    (hh : 0 ≤ h) (ht : 0 ≤ t) (hb : B < q * (b + 1)) : |y| < b + 1 + t * (1 + n) := by
  have h1 : q * |y| ≤ B + t * h + S * (t * h) := by
    rw [← abs_of_pos hq, ← abs_mul, hqy]
    calc |E + d0 + X| ≤ |E| + |d0| + |X| := abs_add_three _ _ _
      _ ≤ B + t * h + S * (t * h) := by gcongr
  have hth : 0 ≤ t * h := mul_nonneg ht hh
  have h3 : S * (t * h) ≤ n * (t * h) := mul_le_mul_of_nonneg_right hS hth
  have hn : 0 ≤ n := hS0.trans hS
  have h4 : 2 * (t * h) ≤ t * q := by nlinarith
  have h5 : 2 * (n * (t * h)) ≤ n * (t * q) := by nlinarith
  have h6 : q * |y| < q * (b + 1 + t * (1 + n)) := by nlinarith
  exact lt_of_mul_lt_mul_left h6 hq.le

theorem abs_valMinAbs_le {q : ℕ} [NeZero q] (z : ZMod q) : |(z.valMinAbs : ℤ)| ≤ ((q / 2 : ℕ) : ℤ) := by
  rw [Int.abs_eq_natAbs]; exact_mod_cast ZMod.natAbs_valMinAbs_le z

theorem two_mul_half_le (q : ℕ) : 2 * ((q / 2 : ℕ) : ℤ) ≤ q := by
  have := Nat.mul_div_le q 2; omega

/-! ### The pins -/

variable (P : FullParams)

/-- (BGV only: for BFV the sum's noise also picks up `Q mod t`.) -/
theorem step_add_bgv (hk : P.src.kind = .bgv) (s : IntPoly P.src.N) (ρ : Env P.src) (d a b : Var) (x y : Val P.src)
    (hx : ρ a = some x) (hy : ρ b = some y) (hlev : x.level = y.level) (hkey : x.key = y.key)
    (hparts : x.parts = y.parts)
    (ca cb : List (IntPoly P.src.N)) (B B' : ℕ)
    (hca : Encrypts P s B x ca) (hcb : Encrypts P s B' y cb)
    (hQ : 2 * (B + B') < P.src.modulus x.level) :
    ∃ ρ' v, step P.src ρ (.add d a b) = some ρ' ∧ ρ' d = some v ∧
      Encrypts P s (B + B') v (List.zipWith (· + ·) ca cb) := by
  rw [encrypts_bgv_iff P hk] at hca hcb
  obtain ⟨hla, m, hm, ha⟩ := hca
  obtain ⟨hlb, m', hm', hb⟩ := hcb
  refine ⟨ρ.set d { x with msg := .exact (m + m'), parts := max x.parts y.parts },
    { x with msg := .exact (m + m'), parts := max x.parts y.parts }, by simp [step, hx, hy, hlev, hkey, hk, hm, hm', Msg.lift₂], set_self _ _ _, ?_⟩
  rw [encrypts_bgv_iff P hk]
  refine ⟨by simp [List.length_zipWith, hla, hlb, hparts], _, rfl, ?_⟩
  rw [← hlev, ← hkey] at hb
  rw [map_ofInt_zipWith]
  exact bgvEncrypts_zipWith_add (by simp [hla, hlb, hparts]) ha hb hQ

theorem step_mul_bgv (hk : P.src.kind = .bgv) (s : IntPoly P.src.N) (ρ : Env P.src) (d a b : Var)
    (x y : Val P.src) (hx : ρ a = some x) (hy : ρ b = some y) (hlev : x.level = y.level)
    (hkey : x.key = y.key) (h2x : x.parts = 2) (h2y : y.parts = 2)
    (ca cb : List (IntPoly P.src.N)) (B B' : ℕ)
    (hca : Encrypts P s B x ca) (hcb : Encrypts P s B' y cb)
    (hQ : 2 * (P.src.N * B * B') < P.src.modulus x.level) :
    ∃ ρ' v, step P.src ρ (.mul d a b) = some ρ' ∧ ρ' d = some v ∧
      Encrypts P s (P.src.N * B * B') v (Challenge.Source.tensor ca cb) := by
  rw [encrypts_bgv_iff P hk] at hca hcb
  obtain ⟨hla, m, hm, ha⟩ := hca
  obtain ⟨hlb, m', hm', hb⟩ := hcb
  rw [h2x] at hla; rw [h2y] at hlb
  obtain ⟨c0, c1, rfl⟩ := List.length_eq_two.mp hla
  obtain ⟨d0, d1, rfl⟩ := List.length_eq_two.mp hlb
  refine ⟨ρ.set d { x with msg := .exact (m * m'), parts := x.parts + y.parts - 1, scale := x.scale * y.scale },
    { x with msg := .exact (m * m'), parts := x.parts + y.parts - 1, scale := x.scale * y.scale },
    by simp [step, hx, hy, hlev, hkey, h2x, h2y, hm, hm', Msg.lift₂], set_self _ _ _, ?_⟩
  rw [encrypts_bgv_iff P hk]
  have ht : Challenge.Source.tensor [c0, c1] [d0, d1] = [c0 * d0, c0 * d1 + c1 * d0, c1 * d1] := rfl
  rw [ht]
  refine ⟨by simp [h2x, h2y], _, rfl, ?_⟩
  rw [← hlev, ← hkey] at hb
  simp only [List.map_cons, List.map_nil] at ha hb
  have := bgvEncrypts_tensor ha hb hQ
  simpa [ofInt_mul, ofInt_add] using this

theorem step_automorph_bgv (hk : P.src.kind = .bgv) (hP : SchemeParamsOK P) (s : IntPoly P.src.N)
    (ρ : Env P.src) (d a : Var) (g : ℕ) (hg : g % 2 = 1) (x : Val P.src) (hx : ρ a = some x)
    (ca : List (IntPoly P.src.N)) (B : ℕ) (hca : Encrypts P s B x ca)
    (hQ : 2 * B < P.src.modulus x.level) :
    ∃ ρ' v, step P.src ρ (.automorph d a g) = some ρ' ∧ ρ' d = some v ∧
      Encrypts P s B v (ca.map (automorph g)) := by
  rw [encrypts_bgv_iff P hk] at hca
  obtain ⟨hla, m, hm, ha⟩ := hca
  refine ⟨ρ.set d { x with msg := .exact (automorph g m), key := (x.key * g) % (2 * P.src.N) },
    { x with msg := .exact (automorph g m), key := (x.key * g) % (2 * P.src.N) }, by simp [step, hx, hg, hm, Msg.lift₁], set_self _ _ _, ?_⟩
  rw [encrypts_bgv_iff P hk]
  refine ⟨by simp [hla], _, rfl, ?_⟩
  simp only
  set Q := P.src.modulus x.level
  set E := centeredPhase (automorph x.key s) (ca.map (ofInt Q))
  refine bgvEncrypts_of_phase (automorph g E) ?_ ?_ hQ ?_
  · have hmap : (ca.map (automorph g)).map (ofInt Q) = (ca.map (ofInt Q)).map (automorph g) := by
      simp only [List.map_map]
      congr 1; funext c; exact ofInt_automorph Q g c
    rw [hmap, automorph_mod, ← automorph_automorph hg, ofInt_automorph, phase_automorph hg,
      phase_eq_ofInt_centeredPhase, ofInt_automorph]
  · exact abs_coeff_automorph_le hP.N_pow2 hg E B (BGVEncrypts.bound ha)
  · rw [ofInt_automorph, BGVEncrypts.msg ha]

/-- t-corrected modulus switching multiplies the message by `q_last⁻¹ mod t`, which is what
`step` records. -/
theorem step_modSwitch_bgv (hk : P.src.kind = .bgv) (hP : SchemeParamsOK P) (s : IntPoly P.src.N)
    (hs : SecretOK P.secretBound s) (ρ : Env P.src) (d a : Var) (x : Val P.src) (hx : ρ a = some x)
    (hℓ : 2 ≤ x.level) (hℓL : x.level ≤ P.src.qs.length) (h2 : x.parts = 2)
    (ca : List (IntPoly P.src.N)) (B : ℕ) (hca : Encrypts P s B x ca)
    (hQ : 2 * (B / P.src.qs[x.level - 1]! + 1 + P.src.t * (1 + P.src.N * P.secretBound)) <
      P.src.modulus (x.level - 1)) :
    ∃ ρ' v, step P.src ρ (.modSwitch d a) = some ρ' ∧ ρ' d = some v ∧
      Encrypts P s (B / P.src.qs[x.level - 1]! + 1 + P.src.t * (1 + P.src.N * P.secretBound)) v
        (ca.map (Challenge.Source.bgvModSwitchComp P.src.t P.src.qs[x.level - 1]!)) := by
  rw [encrypts_bgv_iff P hk] at hca
  obtain ⟨hla, m, hm, ha⟩ := hca
  rw [h2] at hla
  obtain ⟨c0, c1, rfl⟩ := List.length_eq_two.mp hla
  have hlt : x.level - 1 < P.src.qs.length := by omega
  have hgetD : P.src.qs.getD (x.level - 1) 0 = P.src.qs[x.level - 1]! := getD_eq _ _ hlt
  obtain ⟨hqp, hcop⟩ := qLast_facts P hP (x.level - 1) hlt
  have hcop' := hcop
  have hQQ : P.src.modulus x.level = P.src.modulus (x.level - 1) * P.src.qs[x.level - 1]! :=
    modulus_pred _ _ (by omega) hℓL
  have hgetD2 : P.src.qs[x.level - 1]? = some P.src.qs[x.level - 1]! := by simp [hlt]
  generalize P.src.qs[x.level - 1]! = q at hgetD hgetD2 hqp hcop' hQ hQQ ⊢
  have hq0 : 0 < q := hqp.pos
  have : NeZero q := ⟨hq0.ne'⟩
  refine ⟨ρ.set d { x with msg := .exact ((q : ZMod P.src.t)⁻¹ • m), level := x.level - 1 },
    { x with msg := .exact ((q : ZMod P.src.t)⁻¹ • m), level := x.level - 1 },
    by simp [step, hx, hℓ, hk, hm, Msg.lift₁, hgetD2], set_self _ _ _, ?_⟩
  rw [encrypts_bgv_iff P hk]
  refine ⟨by simp [h2], _, rfl, ?_⟩
  simp only
  generalize hsk : automorph x.key s = sk at ha ⊢
  generalize P.src.modulus (x.level - 1) = Q' at hQ hQQ ⊢
  rw [hQQ] at ha
  have hE : ofInt (Q' * q) (c0 + sk * c1) = ofInt (Q' * q) (centeredPhase sk ([c0, c1].map (ofInt (Q' * q)))) := by
    rw [← phase_map_ofInt_two, phase_eq_ofInt_centeredPhase]
  set E := centeredPhase sk ([c0, c1].map (ofInt (Q' * q))) with hEdef
  let dl : IntPoly P.src.N → IntPoly P.src.N := fun c =>
    ⟨fun i => (P.src.t : ℤ) * ((((-(c.coeff i) : ℤ) : ZMod q) * (P.src.t : ZMod q)⁻¹).valMinAbs)⟩
  have hdiv : ∀ c : IntPoly P.src.N, ∀ i,
      (q : ℤ) * (Challenge.Source.bgvModSwitchComp P.src.t q c).coeff i = c.coeff i + (dl c).coeff i := by
    intro c i
    show (q : ℤ) * ((c.coeff i + (P.src.t : ℤ) * ((((-(c.coeff i) : ℤ) : ZMod q) * (P.src.t : ZMod q)⁻¹).valMinAbs)) / q) = _
    apply Int.mul_ediv_cancel'
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    have := ZMod.coe_mul_inv_eq_one P.src.t hcop'
    linear_combination (-(c.coeff i : ZMod q)) * this
  have hdl : ∀ c : IntPoly P.src.N, ∀ i, |(dl c).coeff i| ≤ (P.src.t : ℤ) * ((q / 2 : ℕ) : ℤ) := by
    intro c i
    show |(P.src.t : ℤ) * _| ≤ _
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℤ) ≤ P.src.t)]
    exact mul_le_mul_of_nonneg_left (abs_valMinAbs_le _) (by positivity)
  have hdlt : ∀ c : IntPoly P.src.N, ofInt P.src.t (dl c) = 0 := by
    intro c; ext i; simp [dl]
  obtain ⟨e, he, hqe⟩ := divq_core Q' q sk c0 c1 E (dl c0) (dl c1)
    (Challenge.Source.bgvModSwitchComp P.src.t q c0) (Challenge.Source.bgvModSwitchComp P.src.t q c1) hE
    (hdiv c0) (hdiv c1)
  have hS : (∑ j, |sk.coeff j|) ≤ (P.src.N : ℤ) * (P.secretBound : ℤ) := by
    rw [← hsk]
    exact (sum_abs_automorph_le _ _).trans (sum_abs_le s _ ((normInf_le_iff _ _).mp hs))
  refine bgvEncrypts_of_phase e ?_ ?_ hQ ?_
  · rw [show [c0, c1].map (Challenge.Source.bgvModSwitchComp P.src.t q) =
      [Challenge.Source.bgvModSwitchComp P.src.t q c0, Challenge.Source.bgvModSwitchComp P.src.t q c1] from rfl,
      phase_map_ofInt_two]
    exact he
  · intro i
    have hb : ((B : ℕ) : ℤ) < (q : ℤ) * (((B / q : ℕ) : ℤ) + 1) := by
      exact_mod_cast Nat.lt_mul_div_succ B hq0
    have := div_bound (q : ℤ) B (B / q : ℕ) P.src.t (∑ j, |sk.coeff j|) ((P.src.N : ℤ) * P.secretBound)
      ((q / 2 : ℕ) : ℤ) (e.coeff i) (E.coeff i) ((dl c0).coeff i) ((sk * dl c1).coeff i)
      (by exact_mod_cast hq0) (hqe i) (BGVEncrypts.bound ha i) (hdl c0 i)
      (abs_coeff_mul_le sk (dl c1) _ (hdl c1) i)
      (Finset.sum_nonneg fun _ _ => abs_nonneg _) hS (two_mul_half_le q) (by positivity)
      (by positivity) hb
    push_cast
    exact this.le
  · have hN : 0 < P.src.N ∨ P.src.N = 0 := by omega
    rcases hN with hN | hN
    swap
    · exact eq_of_N_zero hN _ _
    have : NeZero P.src.N := ⟨hN.ne'⟩
    ext i
    have h1 := congrArg (Int.cast : ℤ → ZMod P.src.t) (hqe i)
    have hx1 : (((dl c0).coeff i : ℤ) : ZMod P.src.t) = 0 := by
      have := congrArg (fun p => p.coeff i) (hdlt c0); simpa using this
    have hx2 : (((sk * dl c1).coeff i : ℤ) : ZMod P.src.t) = 0 := by
      have := congrArg (fun p => p.coeff i) (by rw [ofInt_mul, hdlt c1, mul_zero] :
        ofInt P.src.t (sk * dl c1) = 0)
      simpa using this
    have hmi : ((E.coeff i : ℤ) : ZMod P.src.t) = m.coeff i := by
      exact congrArg (fun p => p.coeff i) (BGVEncrypts.msg ha)
    push_cast at h1
    rw [hx1, hx2, hmi, add_zero, add_zero] at h1
    have hinv := ZMod.coe_mul_inv_eq_one q hcop'.symm
    simp only [coeff_ofInt, coeff_smul']
    rw [← h1]
    linear_combination (-((e.coeff i : ℤ) : ZMod P.src.t)) * hinv

/-! ## Levels, parts and keys of declared inputs -/

theorem step_modSwitch_level (P : Params) (ρ : Env P) (d a : Var) (x : Val P) (hx : ρ a = some x)
    (h : P.qs.length < x.level) : step P ρ (.modSwitch d a) = none := by
  have hnone : P.qs[x.level - 1]? = none := List.getElem?_eq_none (by omega)
  simp [step, hx, hnone]

theorem eval_badDecl (P : Params) (prog : Program) (msgs : Var → Msg P.t P.N) (d : Decl)
    (hd : d ∈ prog.inputs)
    (h : d.parts = 0 ∨ d.level = 0 ∨ P.qs.length < d.level ∨ d.key % 2 = 0 ∨ 2 * P.N ≤ d.key) :
    eval P prog msgs = none := by
  have hbad : d.ok P = false := by
    simp only [Decl.ok, decide_eq_false_iff_not]; omega
  have hall : (prog.inputs.all fun dcl => dcl.ok P) = false := by
    rw [List.all_eq_false]; exact ⟨d, hd, by simp [hbad]⟩
  simp [eval, hall]

private theorem guard_bind_some {p : Prop} [Decidable p] {α : Type} {f : Unit → Option α} {r : α}
    (h : (guard p : Option Unit).bind f = some r) : p ∧ f () = some r := by
  by_cases hp : p
  · simp only [guard, hp, ite_true] at h; exact ⟨hp, h⟩
  · simp [guard, hp] at h

theorem eval_input (P : Params) (prog : Program) (msgs : Var → Msg P.t P.N) (ρ : Env P)
    (h : eval P prog msgs = some ρ) (hbody : prog.body = []) (x : Var) (d : Decl)
    (hd : prog.inputs.find? (·.name = x) = some d) :
    ∃ v, ρ x = some v ∧ v.msg = msgs x ∧ v.parts = d.parts ∧ v.level = d.level ∧
      v.key = d.key ∧ v.scale = d.scale ∧
      1 ≤ v.parts ∧ 1 ≤ v.level ∧ v.level ≤ P.qs.length ∧ v.key % 2 = 1 ∧ v.key < 2 * P.N := by
  simp only [eval, hbody, List.foldlM_nil, Option.bind_eq_bind, Option.pure_def,
    Option.bind_some] at h
  obtain ⟨hall, h⟩ := guard_bind_some h
  obtain ⟨-, h⟩ := guard_bind_some h
  obtain ⟨-, h⟩ := guard_bind_some h
  cases h
  have hok : d.ok P = true := List.all_eq_true.mp hall d (List.mem_of_find?_eq_some hd)
  simp only [Decl.ok, decide_eq_true_eq] at hok
  exact ⟨_, by simp [initEnv, hd]; rfl, rfl, rfl, rfl, rfl, rfl, hok⟩

theorem eval_rotatedKeySwitch (P : Params) (g : ℕ) (hg : g % 2 = 1) (hg2 : g < 2 * P.N)
    (hL : 1 ≤ P.qs.length) (msgs : Var → Msg P.t P.N) (hfit : (msgs "a").fits P.kind = true) :
    ∃ ρ va vc, eval P (Challenge.Source.rotatedKeySwitchProg g) msgs = some ρ ∧ ρ "a" = some va ∧
      ρ "c" = some vc ∧ va.key = g ∧ vc.key = 1 ∧ vc.msg = msgs "a" ∧ vc.parts = 2 ∧
      vc.level = 1 := by
  have hok : Decl.ok P ⟨"a", 2, 1, 1, g⟩ = true := by
    simp only [Decl.ok, decide_eq_true_eq]; omega
  refine ⟨(initEnv P (Challenge.Source.rotatedKeySwitchProg g) msgs).set "c"
      ⟨msgs "a", 2, 1, 1, 1⟩, ⟨msgs "a", 2, 1, g, 1⟩, ⟨msgs "a", 2, 1, 1, 1⟩,
    ?_, ?_, ?_, rfl, rfl, rfl, rfl, rfl⟩
  · delta Challenge.Source.rotatedKeySwitchProg
    simp [eval, hok, hfit, step, initEnv, Env.set]
  · delta Challenge.Source.rotatedKeySwitchProg
    simp [initEnv, Env.set]
  · simp [Env.set]

theorem eval_mixedKeys (P : Params) (g : ℕ) (hg : g ≠ 1) (msgs : Var → Msg P.t P.N) :
    eval P { inputs := [⟨"a", 2, 1, 1, 1⟩, ⟨"b", 2, 1, 1, g⟩], body := [.add "c" "a" "b"],
             outputs := ["c"] } msgs = none := by
  have hg' : ¬ (1 = g) := fun h => hg h.symm
  simp [eval, step, initEnv, hg']

/-! ## Plaintexts and dropped limbs -/

section PlainDrop
variable {N : ℕ}

/-- The phase of integer components under an integer secret, before any reduction. -/
def intPhase (s : IntPoly N) : List (IntPoly N) → IntPoly N
  | [] => 0
  | c :: cs => c + s * intPhase s cs

theorem phase_map_ofInt (Q : ℕ) (s : IntPoly N) : ∀ ct : List (IntPoly N),
    phase (ofInt Q s) (ct.map (ofInt Q)) = ofInt Q (intPhase s ct)
  | [] => by simp [phase, intPhase, ofInt_zero]
  | c :: cs => by
      simp only [List.map_cons, phase, intPhase]
      rw [phase_map_ofInt Q s cs, ofInt_add, ofInt_mul]

theorem phase_singleton {q : ℕ} (s c : Poly q N) : phase s [c] = c := by
  simp only [phase]
  apply eq_of_neZero; intro; ring

/-- Reduction modulo a divisor factors through reduction modulo the multiple. -/
theorem ofInt_eq_of_dvd {Q Q' : ℕ} (hd : Q' ∣ Q) {a b : IntPoly N} (h : ofInt Q a = ofInt Q b) :
    ofInt Q' a = ofInt Q' b := by
  ext i
  have hi := congrArg (fun p => p.coeff i) h
  simp only [coeff_ofInt] at hi ⊢
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at hi ⊢
  exact (Int.natCast_dvd_natCast.mpr hd).trans hi

theorem modulus_sub_dvd (Pr : Params) (ℓ k : ℕ) : Pr.modulus (ℓ - k) ∣ Pr.modulus ℓ := by
  unfold Params.modulus
  have h : Pr.qs.take (ℓ - k) = (Pr.qs.take ℓ).take (ℓ - k) := by
    rw [List.take_take, Nat.min_eq_left (Nat.sub_le _ _)]
  rw [h]
  exact ⟨_, (List.prod_take_mul_prod_drop (Pr.qs.take ℓ) (ℓ - k)).symm⟩

/-- The phase at a lower level is the centred phase at the higher level, reduced. -/
theorem phase_drop (Pr : Params) (ℓ k : ℕ) (sk : IntPoly N) (ct : List (IntPoly N)) :
    phase (ofInt (Pr.modulus (ℓ - k)) sk) (ct.map (ofInt (Pr.modulus (ℓ - k)))) =
      ofInt (Pr.modulus (ℓ - k))
        (centered (phase (ofInt (Pr.modulus ℓ) sk) (ct.map (ofInt (Pr.modulus ℓ))))) := by
  rw [phase_map_ofInt]
  apply ofInt_eq_of_dvd (modulus_sub_dvd Pr ℓ k)
  rw [ofInt_centered, phase_map_ofInt]

/-! Unfolding equations of `padZip`, by `rfl`: unfolding the locked definition by name would add
its equation lemmas (`Challenge.Source.padZip.eq_*`) to this module, which the gate rejects. -/
theorem padZip_nil (f : IntPoly N → IntPoly N → IntPoly N) (bs : List (IntPoly N)) :
    Challenge.Source.padZip f [] bs = bs.map (f 0) := rfl
theorem padZip_cons_nil (f : IntPoly N → IntPoly N → IntPoly N) (a : IntPoly N)
    (as : List (IntPoly N)) :
    Challenge.Source.padZip f (a :: as) [] = (a :: as).map (fun a => f a 0) := rfl
theorem padZip_cons_cons (f : IntPoly N → IntPoly N → IntPoly N) (a b : IntPoly N)
    (as bs : List (IntPoly N)) :
    Challenge.Source.padZip f (a :: as) (b :: bs) = f a b :: Challenge.Source.padZip f as bs := rfl

theorem length_padZip (f : IntPoly N → IntPoly N → IntPoly N) : ∀ a b : List (IntPoly N),
    (Challenge.Source.padZip f a b).length = max a.length b.length
  | [], bs => by simp [padZip_nil]
  | a :: as, [] => by simp [padZip_cons_nil]
  | a :: as, b :: bs => by
      simp [padZip_cons_cons, length_padZip f as bs]

theorem phase_map_add_zero {q : ℕ} (s : Poly q N) : ∀ bs : List (IntPoly N),
    phase s ((bs.map ((0 : IntPoly N) + ·)).map (ofInt q)) = phase s (bs.map (ofInt q))
  | [] => rfl
  | b :: bs => by
      simp only [List.map_cons, phase]
      rw [phase_map_add_zero s bs, ofInt_add, ofInt_zero]
      apply eq_of_neZero; intro; ring

theorem phase_map_zero_add {q : ℕ} (s : Poly q N) : ∀ as : List (IntPoly N),
    phase s ((as.map (fun a => a + (0 : IntPoly N))).map (ofInt q)) = phase s (as.map (ofInt q))
  | [] => rfl
  | b :: bs => by
      simp only [List.map_cons, phase]
      rw [phase_map_zero_add s bs, ofInt_add, ofInt_zero]
      apply eq_of_neZero; intro; ring

theorem phase_map_zero_sub {q : ℕ} (s : Poly q N) : ∀ bs : List (IntPoly N),
    phase s ((bs.map ((0 : IntPoly N) - ·)).map (ofInt q)) = -phase s (bs.map (ofInt q))
  | [] => by
      simp only [List.map_nil, phase]
      apply eq_of_neZero; intro; ring
  | b :: bs => by
      simp only [List.map_cons, phase]
      rw [phase_map_zero_sub s bs, ofInt_sub, ofInt_zero]
      apply eq_of_neZero; intro; ring

theorem phase_map_sub_zero {q : ℕ} (s : Poly q N) : ∀ as : List (IntPoly N),
    phase s ((as.map (fun a => a - (0 : IntPoly N))).map (ofInt q)) = phase s (as.map (ofInt q))
  | [] => rfl
  | b :: bs => by
      simp only [List.map_cons, phase]
      rw [phase_map_sub_zero s bs, ofInt_sub, ofInt_zero]
      apply eq_of_neZero; intro; ring

/-- The phase of a padded componentwise sum is the sum of the phases. -/
theorem phase_padZip_add {q : ℕ} (s : Poly q N) : ∀ a b : List (IntPoly N),
    phase s ((Challenge.Source.padZip (· + ·) a b).map (ofInt q)) =
      phase s (a.map (ofInt q)) + phase s (b.map (ofInt q))
  | [], bs => by
      simp only [padZip_nil, phase_map_add_zero, List.map_nil, phase]
      apply eq_of_neZero; intro; ring
  | a :: as, [] => by
      rw [show Challenge.Source.padZip (· + ·) (a :: as) [] =
        (a :: as).map (fun a => a + (0 : IntPoly N)) from rfl, phase_map_zero_add]
      simp only [List.map_nil, phase]
      apply eq_of_neZero; intro; ring
  | a :: as, b :: bs => by
      simp only [padZip_cons_cons, List.map_cons, phase]
      rw [phase_padZip_add s as bs, ofInt_add]
      apply eq_of_neZero; intro; ring

/-- The phase of a padded componentwise difference is the difference of the phases. -/
theorem phase_padZip_sub {q : ℕ} (s : Poly q N) : ∀ a b : List (IntPoly N),
    phase s ((Challenge.Source.padZip (· - ·) a b).map (ofInt q)) =
      phase s (a.map (ofInt q)) - phase s (b.map (ofInt q))
  | [], bs => by
      simp only [padZip_nil, phase_map_zero_sub, List.map_nil, phase]
      apply eq_of_neZero; intro; ring
  | a :: as, [] => by
      rw [show Challenge.Source.padZip (· - ·) (a :: as) [] =
        (a :: as).map (fun a => a - (0 : IntPoly N)) from rfl, phase_map_sub_zero]
      simp only [List.map_nil, phase]
      apply eq_of_neZero; intro; ring
  | a :: as, b :: bs => by
      simp only [padZip_cons_cons, List.map_cons, phase]
      rw [phase_padZip_sub s as bs, ofInt_sub]
      apply eq_of_neZero; intro; ring

/-- Multiplying every component by `c` multiplies the phase by `c`. -/
theorem phase_map_mul {q : ℕ} (s : Poly q N) (c : IntPoly N) : ∀ a : List (IntPoly N),
    phase s ((a.map (c * ·)).map (ofInt q)) = phase s (a.map (ofInt q)) * ofInt q c
  | [] => by
      simp only [List.map_nil, phase]
      apply eq_of_neZero; intro; ring
  | a :: as => by
      simp only [List.map_cons, phase]
      rw [phase_map_mul s c as, ofInt_mul]
      apply eq_of_neZero; intro; ring

/-! Unfolding equations of `tensorParts`, by `rfl` (as for `padZip`). -/
theorem tensorParts_nil (ds : List (IntPoly N)) : Challenge.Source.tensorParts [] ds = [] := rfl
theorem tensorParts_cons (c : IntPoly N) (cs ds : List (IntPoly N)) :
    Challenge.Source.tensorParts (c :: cs) ds =
      Challenge.Source.padZip (· + ·) (ds.map (c * ·))
        (0 :: Challenge.Source.tensorParts cs ds) := rfl

theorem tensorParts_two (c₀ c₁ d₀ d₁ : IntPoly N) :
    Challenge.Source.tensorParts [c₀, c₁] [d₀, d₁] = Challenge.Source.tensor [c₀, c₁] [d₀, d₁] := by
  have ht : Challenge.Source.tensor [c₀, c₁] [d₀, d₁] =
      [c₀ * d₀, c₀ * d₁ + c₁ * d₀, c₁ * d₁] := rfl
  rw [ht]
  simp only [tensorParts_cons, tensorParts_nil, List.map_cons, List.map_nil, padZip_cons_cons,
    padZip_cons_nil, padZip_nil]
  have h0 : ∀ a : IntPoly N, a + 0 = a := fun a => by ext; simp
  have h0' : ∀ a : IntPoly N, 0 + a = a := fun a => by ext; simp
  simp only [h0, h0']

/-- With at least one component on each side, the tensor product has `p + p' − 1` components. -/
theorem length_tensorParts : ∀ (cs ds : List (IntPoly N)), 1 ≤ cs.length → 1 ≤ ds.length →
    (Challenge.Source.tensorParts cs ds).length = cs.length + ds.length - 1
  | [], _, h, _ => by simp at h
  | [c], ds, _, hd => by
      simp [tensorParts_cons, tensorParts_nil, length_padZip]; omega
  | c :: c' :: cs, ds, _, hd => by
      have ih := length_tensorParts (c' :: cs) ds (by simp) hd
      rw [tensorParts_cons, length_padZip, List.length_cons, ih]
      simp; omega

/-- The phase of the tensor product is the product of the phases. -/
theorem phase_tensorParts {q : ℕ} (s : Poly q N) : ∀ cs ds : List (IntPoly N),
    phase s ((Challenge.Source.tensorParts cs ds).map (ofInt q)) =
      phase s (cs.map (ofInt q)) * phase s (ds.map (ofInt q))
  | [], ds => by
      simp only [tensorParts_nil, List.map_nil, phase]
      apply eq_of_neZero; intro; ring
  | c :: cs, ds => by
      rw [tensorParts_cons, phase_padZip_add, phase_map_mul]
      simp only [List.map_cons, phase]
      rw [phase_tensorParts s cs ds, ofInt_zero]
      apply eq_of_neZero; intro; ring

/-- Multiplying every component by the integer `c` multiplies the phase by `c`. -/
theorem phase_map_zsmul {q : ℕ} (s : Poly q N) (c : ℤ) : ∀ a : List (IntPoly N),
    phase s ((a.map (c • ·)).map (ofInt q)) = (c : ZMod q) • phase s (a.map (ofInt q))
  | [] => by
      simp only [List.map_nil, phase]
      ext j; simp
  | a :: as => by
      simp only [List.map_cons, phase]
      rw [phase_map_zsmul s c as]
      have h : ofInt q (c • a) = (c : ZMod q) • ofInt q a := by ext j; simp
      rw [h]
      apply eq_of_neZero; intro
      rw [smul_eq_const_mul, smul_eq_const_mul, smul_eq_const_mul]; ring

end PlainDrop

theorem encrypts_plain_bgv (hk : P.src.kind = .bgv) (hP : SchemeParamsOK P) (s : IntPoly P.src.N)
    (v : Val P.src) (m : Poly P.src.t P.src.N) (hm : v.msg = .exact m) (h1 : v.parts = 1)
    (p : IntPoly P.src.N) (B : ℕ) (hp : ofInt P.src.t p = m) (hB : normInf p ≤ B)
    (hQ : 2 * B < P.src.modulus v.level) :
    Encrypts P s B v [p] := by
  rw [encrypts_bgv_iff P hk]
  refine ⟨by simp [h1], m, hm, ?_⟩
  refine bgvEncrypts_of_phase p ?_ ((normInf_le_iff p B).mp hB) hQ hp
  rw [List.map_cons, List.map_nil, phase_singleton]

theorem encrypts_plain_canonical (hk : P.src.kind = .bgv) (hP : SchemeParamsOK P)
    (s : IntPoly P.src.N) (v : Val P.src) (m : Poly P.src.t P.src.N) (hm : v.msg = .exact m)
    (h1 : v.parts = 1) (hQ : 2 * (P.src.t - 1) < P.src.modulus v.level) :
    Encrypts P s (P.src.t - 1) v [⟨fun i => ((m.coeff i).val : ℤ)⟩] := by
  have ht : 2 ≤ P.src.t := (hP.plaintext).1
  have : NeZero P.src.t := ⟨by omega⟩
  refine encrypts_plain_bgv P hk hP s v m hm h1 _ _ ?_ ?_ hQ
  · ext i
    show (((m.coeff i).val : ℤ) : ZMod P.src.t) = m.coeff i
    rw [Int.cast_natCast, ZMod.natCast_zmod_val]
  · rw [normInf_le_iff]
    intro i
    show |((m.coeff i).val : ℤ)| ≤ ((P.src.t - 1 : ℕ) : ℤ)
    have := ZMod.val_lt (m.coeff i)
    rw [abs_of_nonneg (Int.natCast_nonneg _)]
    exact_mod_cast (by omega : (m.coeff i).val ≤ P.src.t - 1)

theorem encrypts_plain_centred (hk : P.src.kind = .bgv) (hP : SchemeParamsOK P)
    (s : IntPoly P.src.N) (v : Val P.src) (m : Poly P.src.t P.src.N) (hm : v.msg = .exact m)
    (h1 : v.parts = 1) (hQ : 2 * (P.src.t / 2) < P.src.modulus v.level) :
    Encrypts P s (P.src.t / 2) v [centered m] := by
  have ht : 2 ≤ P.src.t := (hP.plaintext).1
  have : NeZero P.src.t := ⟨by omega⟩
  refine encrypts_plain_bgv P hk hP s v m hm h1 _ _ (ofInt_centered m) ?_ hQ
  rw [normInf_le_iff]
  intro i
  exact abs_valMinAbs_le _

theorem plain_canonical_exceeds_centred :
    ¬ BGVEncrypts 17 (17 / 2) (0 : IntPoly 1) [ofInt 65537 (⟨fun _ => 16⟩ : IntPoly 1)]
        (ofInt 17 (⟨fun _ => 16⟩ : IntPoly 1)) ∧
    BGVEncrypts 17 (17 - 1) (0 : IntPoly 1) [ofInt 65537 (⟨fun _ => 16⟩ : IntPoly 1)]
        (ofInt 17 (⟨fun _ => 16⟩ : IntPoly 1)) ∧
    BGVEncrypts 17 (17 / 2) (0 : IntPoly 1) [ofInt 65537 (⟨fun _ => -1⟩ : IntPoly 1)]
        (ofInt 17 (⟨fun _ => 16⟩ : IntPoly 1)) := by
  have hcp : centeredPhase (0 : IntPoly 1) [ofInt 65537 (⟨fun _ => 16⟩ : IntPoly 1)] =
      (⟨fun _ => 16⟩ : IntPoly 1) := by
    rw [centeredPhase, phase_singleton]
    apply centered_ofInt
    intro i
    show 2 * |(16 : ℤ)| < ((65537 : ℕ) : ℤ)
    norm_num
  refine ⟨fun h => ?_, ?_, ?_⟩
  · have hb := BGVEncrypts.bound h 0
    rw [hcp] at hb
    have hb' : |(16 : ℤ)| ≤ ((17 / 2 : ℕ) : ℤ) := hb
    norm_num at hb'
  · refine bgvEncrypts_of_phase _ (phase_singleton _ _) ?_ (by norm_num) rfl
    intro i
    show |(16 : ℤ)| ≤ ((17 - 1 : ℕ) : ℤ)
    norm_num
  · refine bgvEncrypts_of_phase (⟨fun _ => -1⟩ : IntPoly 1) (phase_singleton _ _) ?_
      (by norm_num) ?_
    · intro i
      show |(-1 : ℤ)| ≤ ((17 / 2 : ℕ) : ℤ)
      norm_num
    · ext i
      show (((-1 : ℤ)) : ZMod 17) = ((16 : ℤ) : ZMod 17)
      decide

theorem step_dropLimbs_bgv (hk : P.src.kind = .bgv) (s : IntPoly P.src.N)
    (ρ : Env P.src) (d a : Var) (k : ℕ) (x : Val P.src) (hx : ρ a = some x) (hkℓ : k < x.level)
    (ca : List (IntPoly P.src.N)) (B : ℕ) (hca : Encrypts P s B x ca)
    (hQ : 2 * B < P.src.modulus (x.level - k)) :
    ∃ ρ' v, step P.src ρ (.dropLimbs d a k) = some ρ' ∧ ρ' d = some v ∧
      v.level = x.level - k ∧ v.msg = x.msg ∧ Encrypts P s B v ca := by
  rw [encrypts_bgv_iff P hk] at hca
  obtain ⟨hla, m, hm, ha⟩ := hca
  refine ⟨ρ.set d { x with level := x.level - k }, { x with level := x.level - k },
    by simp [step, hx, hk, hkℓ], set_self _ _ _, rfl, rfl, ?_⟩
  rw [encrypts_bgv_iff P hk]
  refine ⟨hla, m, hm, ?_⟩
  exact bgvEncrypts_of_phase _ (phase_drop P.src x.level k _ ca) (BGVEncrypts.bound ha) hQ
    (BGVEncrypts.msg ha)

theorem step_dropLimbs_level (P : Params) (ρ : Env P) (d a : Var) (k : ℕ) (x : Val P)
    (hx : ρ a = some x) (h : x.level ≤ k) : step P ρ (.dropLimbs d a k) = none := by
  have : ¬ k < x.level := by omega
  simp [step, hx, this]

theorem step_addPlain_parts (P : Params) (ρ : Env P) (d a p : Var) (y : Val P)
    (hy : ρ p = some y) (h : y.parts ≠ 1) : step P ρ (.addPlain d a p) = none := by
  cases hx : ρ a <;> simp [step, hx, hy, h]

theorem step_mulPlain_msg (P : Params) (ρ ρ' : Env P) (d a p : Var) (x y : Val P)
    (m mp : Poly P.t P.N) (hx : ρ a = some x) (hy : ρ p = some y) (hm : x.msg = .exact m)
    (hmp : y.msg = .exact mp) (h : step P ρ (.mulPlain d a p) = some ρ') :
    ∃ v, ρ' d = some v ∧ v.msg = .exact (m * mp) ∧ v.parts = x.parts ∧ v.level = x.level ∧
      v.key = x.key := by
  simp only [step, hx, hy, hm, hmp, Msg.lift₂, Option.bind_eq_bind, Option.bind_some,
    Option.pure_def] at h
  obtain ⟨-, h⟩ := guard_bind_some h
  cases h
  exact ⟨_, set_self _ _ _, rfl, rfl, rfl, rfl⟩

end Validation.Source
