import Validation.Ring
import Spec.Scheme

/-!
# Validation.Scheme.Basic — helper lemmas for the `Spec.Scheme` pins

Coefficient lemmas for `ofInt`, `centered`, `normInf`; the infinity-norm bound of a negacyclic
product; `phase` of sums and products; and a criterion for `BGVEncrypts` in terms of an explicit
integer representative of the phase.
-/

namespace Validation.Scheme
open Spec NPoly Scheme Validation.Ring

variable {N : ℕ}

/-! ### Length zero -/

theorem eq_of_N_zero {R : Type} (h : N = 0) (a b : NPoly R N) : a = b := by
  subst h; ext i; exact i.elim0

/-- An identity of `NPoly`s holds as soon as it holds when `N ≠ 0`, where `NPoly R N` is a
commutative ring. -/
theorem eq_of_neZero {R : Type} {a b : NPoly R N} (h : NeZero N → a = b) : a = b := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · exact eq_of_N_zero hN a b
  · exact h ⟨hN.ne'⟩

/-! ### Coefficient-wise maps along ring homomorphisms -/

section Map
variable {R S : Type} [CommRing R] [CommRing S] (f : R →+* S)

@[simp] theorem coeff_npmap (a : NPoly R N) (i : Fin N) : (map f a).coeff i = f (a.coeff i) := rfl

theorem npmap_zero : map f (0 : NPoly R N) = 0 := by
  ext i; simp

theorem npmap_add (a b : NPoly R N) : map f (a + b) = map f a + map f b := by
  ext i; simp

theorem npmap_sub (a b : NPoly R N) : map f (a - b) = map f a - map f b := by
  ext i; simp

theorem npmap_neg (a : NPoly R N) : map f (-a) = -map f a := by
  ext i; simp

theorem npmap_smul (c : R) (a : NPoly R N) : map f (c • a) = f c • map f a := by
  ext i; simp

theorem npmap_const (c : R) : map f (const c : NPoly R N) = const (f c) := by
  ext i; simp only [coeff_npmap, coeff_const']; split_ifs <;> simp

theorem npmap_mul (a b : NPoly R N) : map f (a * b) = map f a * map f b := by
  ext k
  simp only [coeff_npmap, coeff_mul', map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> simp

theorem npmap_automorph (g : ℕ) (a : NPoly R N) :
    map f (automorph g a) = automorph g (map f a) := by
  ext k
  simp only [coeff_npmap, coeff_automorph', map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> simp

end Map

/-! ### `ofInt` is a ring homomorphism -/

section OfInt
variable (q : ℕ)

@[simp] theorem coeff_ofInt (a : IntPoly N) (i : Fin N) :
    (ofInt q a).coeff i = ((a.coeff i : ℤ) : ZMod q) := rfl

theorem ofInt_zero : ofInt q (0 : IntPoly N) = 0 := npmap_zero (Int.castRingHom (ZMod q))

theorem ofInt_add (a b : IntPoly N) : ofInt q (a + b) = ofInt q a + ofInt q b := npmap_add (Int.castRingHom (ZMod q)) a b

theorem ofInt_sub (a b : IntPoly N) : ofInt q (a - b) = ofInt q a - ofInt q b := npmap_sub (Int.castRingHom (ZMod q)) a b

theorem ofInt_neg (a : IntPoly N) : ofInt q (-a) = -ofInt q a := npmap_neg (Int.castRingHom (ZMod q)) a

theorem ofInt_mul (a b : IntPoly N) : ofInt q (a * b) = ofInt q a * ofInt q b := npmap_mul (Int.castRingHom (ZMod q)) a b

theorem ofInt_const (c : ℤ) : ofInt q (const c : IntPoly N) = const (c : ZMod q) := npmap_const (Int.castRingHom (ZMod q)) c

theorem ofInt_automorph (g : ℕ) (a : IntPoly N) :
    ofInt q (automorph g a) = automorph g (ofInt q a) := npmap_automorph (Int.castRingHom (ZMod q)) g a

end OfInt

/-! ### Constants -/

theorem coeff_const_mul {R : Type} [CommRing R] (c : R) (a : NPoly R N) (i : Fin N) :
    (const c * a).coeff i = c * a.coeff i := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN; exact i.elim0
  · haveI : NeZero N := ⟨hN.ne'⟩
    rw [← smul_eq_const_mul]; rfl

/-! ### Centered lifts -/

@[simp] theorem coeff_centered {q : ℕ} (a : Poly q N) (i : Fin N) :
    (centered a).coeff i = (a.coeff i).valMinAbs := rfl

theorem ofInt_centered {q : ℕ} (a : Poly q N) : ofInt q (centered a) = a := by
  ext i; exact ZMod.coe_valMinAbs _

/-- `valMinAbs` of an integer `v` with `2·|v| < Q` is `v` itself. -/
theorem valMinAbs_intCast_of_small {Q : ℕ} {v : ℤ} (h : 2 * |v| < Q) :
    ((v : ZMod Q)).valMinAbs = v := by
  have hv := abs_nonneg v
  have hQ : Q ≠ 0 := by rintro rfl; push_cast at h; linarith
  haveI : NeZero Q := ⟨hQ⟩
  rw [ZMod.valMinAbs_spec]
  have h1 := neg_abs_le v
  have h2 := le_abs_self v
  refine ⟨rfl, ?_, ?_⟩ <;> linarith

theorem centered_ofInt {Q : ℕ} (v : IntPoly N) (hv : ∀ i, 2 * |v.coeff i| < Q) :
    centered (ofInt Q v) = v := by
  ext i; exact valMinAbs_intCast_of_small (hv i)

theorem centered_zero {q : ℕ} : centered (0 : Poly q N) = 0 := by
  ext i; exact ZMod.valMinAbs_zero q

/-- Two integers are congruent modulo `Q` iff they have the same image in `ZMod Q`. -/
theorem exists_eq_add_mul_of_cast_eq {Q : ℕ} {a b : ℤ} (h : (a : ZMod Q) = (b : ZMod Q)) :
    ∃ j : ℤ, a = b + Q * j := by
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at h
  obtain ⟨j, hj⟩ := h
  exact ⟨-j, by linarith⟩

/-! ### Infinity norm -/

theorem normInf_le_iff (a : IntPoly N) (B : ℕ) : normInf a ≤ B ↔ ∀ i, |a.coeff i| ≤ B := by
  unfold normInf
  rw [Finset.sup_le_iff]
  simp only [Finset.mem_univ, true_implies]
  refine forall_congr' fun i => ?_
  rw [← Int.natCast_natAbs]
  exact_mod_cast Iff.rfl

theorem abs_coeff_le_normInf (a : IntPoly N) (i : Fin N) : |a.coeff i| ≤ (normInf a : ℤ) :=
  (normInf_le_iff a (normInf a)).mp le_rfl i

theorem normInf_zero : normInf (0 : IntPoly N) = 0 := by
  apply Nat.le_zero.mp
  rw [normInf_le_iff]
  intro i; simp

/-- `‖a * b‖∞ ≤ ‖a‖₁ · ‖b‖∞` for the negacyclic product. -/
theorem abs_coeff_mul_le (a b : IntPoly N) (M : ℤ) (hb : ∀ j, |b.coeff j| ≤ M) (k : Fin N) :
    |(a * b).coeff k| ≤ (∑ i, |a.coeff i|) * M := by
  rw [coeff_mul', Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  split_ifs <;> simp only [abs_neg, abs_mul] <;>
    exact mul_le_mul_of_nonneg_left (hb _) (abs_nonneg _)

theorem sum_abs_le (a : IntPoly N) (B : ℤ) (ha : ∀ i, |a.coeff i| ≤ B) :
    ∑ i, |a.coeff i| ≤ N * B := by
  calc ∑ i, |a.coeff i| ≤ ∑ _i : Fin N, B := Finset.sum_le_sum fun i _ => ha i
    _ = N * B := by simp

/-- `‖a * b‖∞ ≤ N · ‖a‖∞ · ‖b‖∞`. -/
theorem abs_coeff_mul_le_N (a b : IntPoly N) (B B' : ℤ) (ha : ∀ i, |a.coeff i| ≤ B)
    (hb : ∀ j, |b.coeff j| ≤ B') (k : Fin N) : |(a * b).coeff k| ≤ N * B * B' := by
  have hB' : 0 ≤ B' := by
    rcases Nat.eq_zero_or_pos N with hN | hN
    · subst hN; exact k.elim0
    · exact (abs_nonneg _).trans (hb ⟨0, hN⟩)
  calc |(a * b).coeff k| ≤ (∑ i, |a.coeff i|) * B' := abs_coeff_mul_le a b B' hb k
    _ ≤ (N * B) * B' := mul_le_mul_of_nonneg_right (sum_abs_le a B ha) hB'

/-! ### Phase -/

theorem phase_nil {q : ℕ} (s : Poly q N) : phase s [] = 0 := rfl

theorem phase_cons {q : ℕ} (s c : Poly q N) (cs : List (Poly q N)) :
    phase s (c :: cs) = c + s * phase s cs := rfl

theorem phase_two' {q : ℕ} (s c₀ c₁ : Poly q N) : phase s [c₀, c₁] = c₀ + s * c₁ := by
  simp only [phase]
  apply eq_of_neZero; intro; ring

theorem phase_three' {q : ℕ} (s c₀ c₁ c₂ : Poly q N) :
    phase s [c₀, c₁, c₂] = c₀ + s * c₁ + (s * s) * c₂ := by
  simp only [phase]
  apply eq_of_neZero; intro; ring

theorem phase_zipWith_add {q : ℕ} (s : Poly q N) : ∀ (c d : List (Poly q N)),
    c.length = d.length → phase s (List.zipWith (· + ·) c d) = phase s c + phase s d
  | [], [], _ => by
      apply eq_of_neZero; intro
      simp only [List.zipWith_nil_left, phase]; ring
  | c :: cs, d :: ds, h => by
      simp only [List.zipWith_cons_cons, phase]
      rw [phase_zipWith_add s cs ds (by simpa using h)]
      apply eq_of_neZero; intro; ring
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h

theorem phase_map_ofInt_two {Q : ℕ} (s c₀ c₁ : IntPoly N) :
    phase (ofInt Q s) ([c₀, c₁].map (ofInt Q)) = ofInt Q (c₀ + s * c₁) := by
  rw [List.map_cons, List.map_cons, List.map_nil, phase_two', ofInt_add, ofInt_mul]

/-! ### BGV -/

/-- `ct` BGV-encrypts `m` with noise `B` as soon as its phase is the reduction of an integer
polynomial `v` with `‖v‖∞ ≤ B < Q/2` and `v ≡ m (mod t)`. -/
theorem bgvEncrypts_of_phase {t B Q : ℕ} {s : IntPoly N} {ct : List (Poly Q N)} {m : Poly t N}
    (v : IntPoly N) (hph : phase (ofInt Q s) ct = ofInt Q v) (hv : ∀ i, |v.coeff i| ≤ B)
    (hQ : 2 * B < Q) (hm : ofInt t v = m) : BGVEncrypts t B s ct m := by
  have hc : centeredPhase s ct = v := by
    rw [centeredPhase, hph]
    apply centered_ofInt
    intro i
    have := hv i
    have hQ' : (2 * B : ℤ) < Q := by exact_mod_cast hQ
    linarith
  refine ⟨?_, ?_⟩
  · rw [bgvDecrypt, hc, hm]
  · rw [hc, normInf_le_iff]; exact hv

theorem phase_eq_ofInt_centeredPhase {Q : ℕ} (s : IntPoly N) (ct : List (Poly Q N)) :
    phase (ofInt Q s) ct = ofInt Q (centeredPhase s ct) :=
  (ofInt_centered _).symm

theorem BGVEncrypts.bound {t B Q : ℕ} {s : IntPoly N} {ct : List (Poly Q N)} {m : Poly t N}
    (h : BGVEncrypts t B s ct m) (i : Fin N) : |(centeredPhase s ct).coeff i| ≤ B :=
  (normInf_le_iff _ _).mp h.2 i

theorem BGVEncrypts.msg {t B Q : ℕ} {s : IntPoly N} {ct : List (Poly Q N)} {m : Poly t N}
    (h : BGVEncrypts t B s ct m) : ofInt t (centeredPhase s ct) = m := h.1

/-- Addition of BGV ciphertexts with the same number of components. -/
theorem bgvEncrypts_zipWith_add {t B B' Q : ℕ} {s : IntPoly N} {c d : List (Poly Q N)}
    {m m' : Poly t N} (hlen : c.length = d.length) (h : BGVEncrypts t B s c m)
    (h' : BGVEncrypts t B' s d m') (hQ : 2 * (B + B') < Q) :
    BGVEncrypts t (B + B') s (List.zipWith (· + ·) c d) (m + m') := by
  refine bgvEncrypts_of_phase (centeredPhase s c + centeredPhase s d) ?_ ?_ hQ ?_
  · rw [phase_zipWith_add _ c d hlen, phase_eq_ofInt_centeredPhase s c,
      phase_eq_ofInt_centeredPhase s d, ofInt_add]
  · intro i
    have h1 := (BGVEncrypts.bound h) i
    have h2 := (BGVEncrypts.bound h') i
    rw [coeff_add']
    push_cast
    exact (abs_add_le _ _).trans (add_le_add h1 h2)
  · rw [ofInt_add, (BGVEncrypts.msg h), (BGVEncrypts.msg h')]

/-- Tensoring of two-component BGV ciphertexts. -/
theorem bgvEncrypts_tensor {t B B' Q : ℕ} {s : IntPoly N} {c₀ c₁ d₀ d₁ : Poly Q N}
    {m m' : Poly t N} (h : BGVEncrypts t B s [c₀, c₁] m) (h' : BGVEncrypts t B' s [d₀, d₁] m')
    (hQ : 2 * (N * B * B') < Q) :
    BGVEncrypts t (N * B * B') s [c₀ * d₀, c₀ * d₁ + c₁ * d₀, c₁ * d₁] (m * m') := by
  refine bgvEncrypts_of_phase (centeredPhase s [c₀, c₁] * centeredPhase s [d₀, d₁]) ?_ ?_ hQ ?_
  · rw [ofInt_mul, ← phase_eq_ofInt_centeredPhase, ← phase_eq_ofInt_centeredPhase, phase_two',
      phase_two', phase_three']
    apply eq_of_neZero; intro; ring
  · intro i
    have := abs_coeff_mul_le_N _ _ (B : ℤ) (B' : ℤ) (BGVEncrypts.bound h) (BGVEncrypts.bound h') i
    push_cast
    exact this
  · rw [ofInt_mul, (BGVEncrypts.msg h), (BGVEncrypts.msg h')]

end Validation.Scheme
