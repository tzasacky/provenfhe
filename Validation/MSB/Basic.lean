import Challenge.MSB
import Validation.Source

/-!
# Validation.MSB.Basic — the t-reading of phases, decryption and noise

Proofs of the decryption and noise pins of `Challenge.MSB` (item 1).
-/

namespace Validation.MSB
open Spec NPoly Scheme Source Spec.MSB
open Validation.Ring Validation.Scheme

variable {N : ℕ}

/-- Reduction commutes with multiplication by an integer `t`. -/
theorem ofInt_smul (Q t : ℕ) (c : IntPoly N) :
    ofInt Q ((t : ℤ) • c) = (t : ZMod Q) • ofInt Q c := by
  ext i
  show (((t : ℤ) * c.coeff i : ℤ) : ZMod Q) = (t : ZMod Q) * ((c.coeff i : ℤ) : ZMod Q)
  push_cast; rfl

/-- **The phase of the t-reading is `t` times the phase.** -/
theorem phase_toLSB (t Q : ℕ) (s : Poly Q N) : ∀ ct : List (IntPoly N),
    phase s ((toLSB t ct).map (ofInt Q)) = (t : ZMod Q) • phase s (ct.map (ofInt Q))
  | [] => by
    show (0 : Poly Q N) = (t : ZMod Q) • 0
    ext i; show (0 : ZMod Q) = (t : ZMod Q) * 0; simp
  | c :: cs => by
    have ih := phase_toLSB t Q s cs
    show ofInt Q ((t : ℤ) • c) + s * phase s ((toLSB t cs).map (ofInt Q)) =
      (t : ZMod Q) • (ofInt Q c + s * phase s (cs.map (ofInt Q)))
    rw [ih, ofInt_smul]
    apply eq_of_neZero; intro
    simp only [smul_eq_const_mul]; ring

/-- `Trace.phaseAt` of the t-reading. -/
theorem phaseAt_toLSB (P : FullParams) (Q key : ℕ) (s : IntPoly P.src.N)
    (ct : List (IntPoly P.src.N)) :
    Trace.phaseAt P Q key s (toLSB P.src.t ct) = (P.src.t : ZMod Q) • Trace.phaseAt P Q key s ct :=
  phase_toLSB _ _ _ ct

theorem msbDecrypt_toLSB (t Q : ℕ) (s : IntPoly N) (ct : List (IntPoly N)) :
    msbDecrypt t s (ct.map (ofInt Q)) = bgvDecrypt t s ((toLSB t ct).map (ofInt Q)) := by
  show ofInt t (centered ((t : ZMod Q) • phase (ofInt Q s) (ct.map (ofInt Q)))) =
    ofInt t (centered (phase (ofInt Q s) ((toLSB t ct).map (ofInt Q))))
  rw [phase_toLSB]

theorem msbDecrypt_iff (t Q : ℕ) (s : IntPoly N) (ct : List (IntPoly N)) (m : Poly t N) :
    msbDecrypt t s (ct.map (ofInt Q)) = m ↔ bgvDecrypt t s ((toLSB t ct).map (ofInt Q)) = m := by
  rw [msbDecrypt_toLSB]

/-- `t · t⁻¹ = 1` modulo `Q` for `gcd(t, Q) = 1`, on polynomials. -/
theorem smul_inv_smul (t Q : ℕ) (hcop : Nat.Coprime t Q) (x : Poly Q N) :
    (t : ZMod Q) • ((t : ZMod Q)⁻¹ • x) = x := by
  ext i
  show (t : ZMod Q) * ((t : ZMod Q)⁻¹ * x.coeff i) = x.coeff i
  rw [← mul_assoc, ZMod.coe_mul_inv_eq_one t hcop, one_mul]

theorem inv_smul_smul (t Q : ℕ) (hcop : Nat.Coprime t Q) (x : Poly Q N) :
    (t : ZMod Q)⁻¹ • ((t : ZMod Q) • x) = x := by
  ext i
  show (t : ZMod Q)⁻¹ * ((t : ZMod Q) * x.coeff i) = x.coeff i
  rw [← mul_assoc, mul_comm ((t : ZMod Q)⁻¹), ZMod.coe_mul_inv_eq_one t hcop, one_mul]

theorem toLSB_encrypts_of_rep (t Q : ℕ) (hcop : Nat.Coprime t Q) (s : IntPoly N)
    (ct : List (IntPoly N)) (m : Poly t N) (p e : IntPoly N)
    (hφ : phase (ofInt Q s) (ct.map (ofInt Q)) = (t : ZMod Q)⁻¹ • ofInt Q p + ofInt Q e)
    (hp : ofInt t p = m) (hQ : 2 * (normInf p + t * normInf e) < Q) :
    BGVEncrypts t (normInf p + t * normInf e) s ((toLSB t ct).map (ofInt Q)) m := by
  -- the phase of the t-reading is `p + t·e`
  have hL : phase (ofInt Q s) ((toLSB t ct).map (ofInt Q)) = ofInt Q (p + (t : ℤ) • e) := by
    rw [phase_toLSB, hφ]
    ext i
    show (t : ZMod Q) * ((t : ZMod Q)⁻¹ * ((p.coeff i : ℤ) : ZMod Q) + ((e.coeff i : ℤ) : ZMod Q))
      = (((p.coeff i + (t : ℤ) * e.coeff i) : ℤ) : ZMod Q)
    have h1 := ZMod.coe_mul_inv_eq_one t hcop
    push_cast
    linear_combination ((p.coeff i : ℤ) : ZMod Q) * h1
  have hsmall : ∀ i, 2 * |(p + (t : ℤ) • e).coeff i| < Q := by
    intro i
    show 2 * |p.coeff i + (t : ℤ) * e.coeff i| < Q
    have h1 := abs_coeff_le_normInf p i
    have h2 := abs_coeff_le_normInf e i
    have h3 := abs_add_le (p.coeff i) ((t : ℤ) * e.coeff i)
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℤ) ≤ t)] at h3
    have h4 : (t : ℤ) * |e.coeff i| ≤ t * normInf e := mul_le_mul_of_nonneg_left h2 (by positivity)
    have h5 : ((2 * (normInf p + t * normInf e) : ℕ) : ℤ) < Q := by exact_mod_cast hQ
    push_cast at h5
    linarith
  have hc : centeredPhase s ((toLSB t ct).map (ofInt Q)) = p + (t : ℤ) • e := by
    show centered (phase (ofInt Q s) _) = _
    rw [hL, centered_ofInt _ hsmall]
  refine ⟨?_, ?_⟩
  · show ofInt t (centeredPhase s _) = m
    rw [hc, ofInt_add, ofInt_smul, ← hp]
    ext i
    show _ + ((t : ℕ) : ZMod t) * _ = _
    simp
  · rw [hc, normInf_le_iff]
    intro i
    show |p.coeff i + (t : ℤ) * e.coeff i| ≤ ((normInf p + t * normInf e : ℕ) : ℤ)
    have h1 := abs_coeff_le_normInf p i
    have h2 := abs_coeff_le_normInf e i
    have h3 := abs_add_le (p.coeff i) ((t : ℤ) * e.coeff i)
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℤ) ≤ t)] at h3
    have h4 : (t : ℤ) * |e.coeff i| ≤ t * normInf e := mul_le_mul_of_nonneg_left h2 (by positivity)
    push_cast
    linarith

theorem msbEncryptsRep_toLSB (t Q B : ℕ) (hcop : Nat.Coprime t Q) (hQ : 2 * B < Q)
    (s : IntPoly N) (ct : List (IntPoly N)) (m : Poly t N)
    (h : MSBEncryptsRep t B s (ct.map (ofInt Q)) m) :
    BGVEncrypts t B s ((toLSB t ct).map (ofInt Q)) m := by
  obtain ⟨p, e, hφ, hp, hB⟩ := h
  have h := toLSB_encrypts_of_rep t Q hcop s ct m p e hφ hp
    (lt_of_le_of_lt (Nat.mul_le_mul_left 2 hB) hQ)
  exact ⟨h.1, h.2.trans hB⟩

theorem msbEncrypts_toLSB (t Q B : ℕ) (ht : 0 < t) (hcop : Nat.Coprime t Q)
    (hQ : 2 * (t / 2 + t * B) < Q) (s : IntPoly N) (ct : List (IntPoly N)) (m : Poly t N)
    (h : MSBEncrypts t B s (ct.map (ofInt Q)) m) :
    BGVEncrypts t (t / 2 + t * B) s ((toLSB t ct).map (ofInt Q)) m := by
  haveI : NeZero t := ⟨ht.ne'⟩
  obtain ⟨-, hB⟩ := h
  set φ := phase (ofInt Q s) (ct.map (ofInt Q))
  set e := centered (φ - (t : ZMod Q)⁻¹ • ofInt Q (centered m))
  have hφ : φ = (t : ZMod Q)⁻¹ • ofInt Q (centered m) + ofInt Q e := by
    rw [ofInt_centered]; ext i; simp
  have hm : normInf (centered m) ≤ t / 2 := by
    rw [normInf_le_iff]; intro i
    exact Validation.Source.abs_valMinAbs_le _
  have hle : normInf (centered m) + t * normInf e ≤ t / 2 + t * B :=
    Nat.add_le_add hm (Nat.mul_le_mul_left _ hB)
  have h := toLSB_encrypts_of_rep t Q hcop s ct m (centered m) e hφ (ofInt_centered m)
    (lt_of_le_of_lt (Nat.mul_le_mul_left 2 hle) hQ)
  exact ⟨h.1, h.2.trans hle⟩

theorem toLSB_msbEncrypts (t Q B : ℕ) (ht : 0 < t) (hcop : Nat.Coprime t Q)
    (hQ : 2 * ((B + t / 2) / t) < Q) (s : IntPoly N) (ct : List (IntPoly N)) (m : Poly t N)
    (h : BGVEncrypts t B s ((toLSB t ct).map (ofInt Q)) m) :
    MSBEncrypts t ((B + t / 2) / t) s (ct.map (ofInt Q)) m := by
  haveI : NeZero t := ⟨ht.ne'⟩
  obtain ⟨hdec, hB⟩ := h
  set φ := phase (ofInt Q s) (ct.map (ofInt Q))
  set X := centeredPhase s ((toLSB t ct).map (ofInt Q)) with hXdef
  have hX : (t : ZMod Q) • φ = ofInt Q X := by
    rw [hXdef]; show _ = ofInt Q (centered _); rw [ofInt_centered, phase_toLSB]
  -- `X ≡ m̃ (mod t)`
  have hXm : ∀ i, (t : ℤ) ∣ X.coeff i - (centered m).coeff i := by
    intro i
    have h1 := congrArg (fun p => p.coeff i) hdec
    have h2 := congrArg (fun p => p.coeff i) (ofInt_centered m)
    simp only [coeff_ofInt] at h2
    change ((X.coeff i : ℤ) : ZMod t) = m.coeff i at h1
    rw [← ZMod.intCast_eq_intCast_iff_dvd_sub, h1, h2]
  choose k hk using hXm
  set e0 : IntPoly N := ⟨k⟩
  have hk' : ∀ i, X.coeff i = (centered m).coeff i + t * e0.coeff i := by
    intro i; have := hk i; show _ = _ + _ * k i; linarith
  have hφ : φ - (t : ZMod Q)⁻¹ • ofInt Q (centered m) = ofInt Q e0 := by
    have h1 : φ = (t : ZMod Q)⁻¹ • ofInt Q X := by rw [← hX, inv_smul_smul t Q hcop]
    rw [h1]
    ext i
    show (t : ZMod Q)⁻¹ * ((X.coeff i : ℤ) : ZMod Q) - (t : ZMod Q)⁻¹ * (((centered m).coeff i : ℤ) : ZMod Q)
      = ((k i : ℤ) : ZMod Q)
    rw [hk' i]
    have h2 := ZMod.coe_mul_inv_eq_one t hcop
    push_cast
    show _ = ((e0.coeff i : ℤ) : ZMod Q)
    linear_combination ((e0.coeff i : ℤ) : ZMod Q) * h2
  -- `|e0| ≤ ⌊(B + ⌊t/2⌋)/t⌋`
  have hbound : ∀ i, |e0.coeff i| ≤ (((B + t / 2) / t : ℕ) : ℤ) := by
    intro i
    have h1 : |X.coeff i| ≤ B := (abs_coeff_le_normInf X i).trans (by exact_mod_cast hB)
    have h2 : |(centered m).coeff i| ≤ ((t / 2 : ℕ) : ℤ) := Validation.Source.abs_valMinAbs_le _
    have h3 : (t : ℤ) * |e0.coeff i| ≤ ((B + t / 2 : ℕ) : ℤ) := by
      have : (t : ℤ) * e0.coeff i = X.coeff i - (centered m).coeff i := by rw [hk' i]; ring
      rw [← abs_of_nonneg (by positivity : (0 : ℤ) ≤ t), ← abs_mul, this, Nat.cast_add]
      have := abs_sub (X.coeff i) ((centered m).coeff i)
      linarith
    have h4 : t * (e0.coeff i).natAbs ≤ B + t / 2 := by
      have : ((t * (e0.coeff i).natAbs : ℕ) : ℤ) ≤ ((B + t / 2 : ℕ) : ℤ) := by
        rw [Nat.cast_mul, Int.natCast_natAbs]; exact h3
      exact_mod_cast this
    have h5 : (e0.coeff i).natAbs ≤ (B + t / 2) / t :=
      (Nat.le_div_iff_mul_le ht).mpr (by rw [mul_comm]; exact h4)
    rw [← Int.natCast_natAbs]; exact_mod_cast h5
  refine ⟨by rw [msbDecrypt_toLSB]; exact hdec, ?_⟩
  rw [hφ, centered_ofInt]
  · rw [normInf_le_iff]; exact hbound
  · intro i
    have := hbound i
    generalize (B + t / 2) / t = K at this hQ
    have h2 : ((2 * K : ℕ) : ℤ) < Q := by exact_mod_cast hQ
    push_cast at h2 ⊢
    linarith

end Validation.MSB
