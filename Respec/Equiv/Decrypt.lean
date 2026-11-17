import Respec.BGV
import Validation.Scheme.Basic

/-!
# Respec.Equiv.Decrypt — items 1 and 2: decryption and the BGV encryption invariant

Cross-check of the specification `A` (`Spec.Scheme`) against the independent re-specification `B`
(`Respec.BGV`); "A's `x`" and "B's `x`" are the corresponding definitions of each.

## Verdicts (all PROVED, no `sorry`)

* **Item 1, decryption: EQUAL.**
  `phase_eq` : B's phase `Σᵢ cᵢ·sⁱ` (a left fold over `zipIdx`) is A's Horner phase.
  `crit_eq` : B's critical quantity `crit` is A's `centeredPhase`.
  `decrypt_eq` : B's `decrypt` is A's `bgvDecrypt`, for every `t`, `Q`, `s`, ciphertext length.
  `wrong_ne` : B's deliberately wrong `decryptCanonicalWRONG` differs from A's `bgvDecrypt`
  (kernel-checked witness `N = 1`, `Q = 7`, `t = 2`, one-component ciphertext `[6]`).
* **Item 2, the invariant: A's `BGVEncrypts` is B's *decidable* `Encrypts`, not the existential
  form.** `bgvEncrypts_iff` : `BGVEncrypts t B s ct m ↔ Encrypts t s ct m B` (no side condition).
  `encrypts_imp_ex` : it implies B's existential `EncryptsEx` for either message lift.
  `ex_imp_encrypts` : the existential form implies it when `2B < Q` (B's claim, proved).
  `ex_not_imp` : without `2B < Q` the existential form does not (kernel witness: `N = 1`, `Q = 5`,
  `t = 2`, `B = 3`, phase `3 = 1 + 2·1`, message `1`, but A's/B's decryption gives `0`).
  Hence A's invariant has content for every `B` (it pins the message through the centred lift);
  `2B < Q` is needed only by theorems that *construct* `BGVEncrypts` from an integer
  representative (`Validation.Scheme.bgvEncrypts_of_phase` has it; audit in the report).
-/

namespace Respec.Equiv

open Spec Spec.NPoly Spec.Scheme Respec Respec.BGV Validation.Ring Validation.Scheme

variable {N : ℕ}

/-! ### Unfolding lemmas for A's definitions

Proved by `rfl` and used in `simp` sets instead of the definitions' names, so that no equation
lemma is generated in the `Spec` namespace from this directory. -/

theorem ofInt_unfold (q : ℕ) (a : IntPoly N) : ofInt q a = ⟨fun i => (a.coeff i : ZMod q)⟩ := rfl

theorem normInf_unfold (a : IntPoly N) :
    normInf a = Finset.univ.sup fun i => (a.coeff i).natAbs := rfl

theorem bgvEncrypts_unfold (t B : ℕ) {Q : ℕ} (s : IntPoly N) (ct : List (Poly Q N))
    (m : Poly t N) :
    BGVEncrypts t B s ct m ↔ (bgvDecrypt t s ct = m ∧ normInf (centeredPhase s ct) ≤ B) := Iff.rfl

/-! ### The phase -/

/-- The fold behind B's `phase`, with an accumulator and a starting exponent. -/
theorem foldl_zipIdx_phase [NeZero N] {Q : ℕ} (x : Poly Q N) :
    ∀ (cs : List (Poly Q N)) (n : ℕ) (acc : Poly Q N),
      List.foldl (· + ·) acc ((cs.zipIdx n).map fun ci => ci.1 * x ^ ci.2)
        = acc + x ^ n * Scheme.phase x cs
  | [], n, acc => by simp [Scheme.phase]
  | c :: cs, n, acc => by
      rw [List.zipIdx_cons, List.map_cons, List.foldl_cons, foldl_zipIdx_phase x cs (n + 1)]
      simp only [Scheme.phase]
      ring

/-- **B's phase is A's phase.** -/
theorem phase_eq {Q : ℕ} (s : IntPoly N) (ct : List (Poly Q N)) :
    BGV.phase s ct = Scheme.phase (ofInt Q s) ct := by
  apply eq_of_neZero; intro
  unfold BGV.phase
  simp only [psum_eq, pmul_eq, ppow_eq, red_eq]
  have h := foldl_zipIdx_phase (ofInt Q s) ct 0 0
  simp only [pow_zero, one_mul, zero_add] at h
  exact h

/-- **B's critical quantity is A's centred phase.** -/
theorem crit_eq {Q : ℕ} (s : IntPoly N) (ct : List (Poly Q N)) :
    crit s ct = centeredPhase s ct := by
  simp only [crit, liftC_eq, phase_eq, centeredPhase]

/-- **Item 1: B's decryption is A's decryption.** -/
theorem decrypt_eq (t : ℕ) {Q : ℕ} (s : IntPoly N) (ct : List (Poly Q N)) :
    BGV.decrypt t s ct = bgvDecrypt t s ct := by
  simp only [BGV.decrypt, red_eq, crit_eq, bgvDecrypt]

/-- **The canonical inner lift is wrong, and A does not use it**: a one-coefficient,
one-component ciphertext `[6]` modulo `7` (phase `6 ≡ −1`), `t = 2`. A decrypts to `1`
(`[−1]_2`), the canonical-lift decryption gives `0`. -/
theorem wrong_ne :
    decryptCanonicalWRONG 2 (0 : IntPoly 1) [(⟨fun _ => 6⟩ : Poly 7 1)]
      ≠ bgvDecrypt 2 (0 : IntPoly 1) [(⟨fun _ => 6⟩ : Poly 7 1)] := by
  intro h
  have h1 := congrArg (fun p : Poly 2 1 => p.coeff 0) h
  revert h1
  decide +kernel

/-! ### The invariant -/

/-- **Item 2: A's `BGVEncrypts` is exactly B's decidable `Encrypts`** (argument order differs). -/
theorem bgvEncrypts_iff (t B : ℕ) {Q : ℕ} (s : IntPoly N) (ct : List (Poly Q N)) (m : Poly t N) :
    BGVEncrypts t B s ct m ↔ Encrypts t s ct m B := by
  simp only [bgvEncrypts_unfold, Encrypts, bgvDecrypt, crit_eq]

theorem liftBy_cast (ml : Lift) {t : ℕ} [NeZero t] (m : Poly t N) : ofInt t (liftBy ml m) = m := by
  ext i
  simp only [liftBy, force_eq, ofInt_unfold]
  cases ml <;> simp [Lift.rep, ZMod.natCast_zmod_val]

/-- A's invariant implies B's existential one, for either lift of the message. -/
theorem encrypts_imp_ex (ml : Lift) (t B : ℕ) [NeZero t] {Q : ℕ} (s : IntPoly N) (ct : List (Poly Q N))
    (m : Poly t N) (h : BGVEncrypts t B s ct m) : EncryptsEx ml t s ct m B := by
  obtain ⟨hdec, hb⟩ := h
  -- `v ≡ m̃ (mod t)` coefficientwise
  have hd : ∀ i, (t : ℤ) ∣ (centeredPhase s ct).coeff i - (liftBy ml m).coeff i := by
    intro i
    rw [← ZMod.intCast_eq_intCast_iff_dvd_sub]
    have h1 := congrArg (fun p => p.coeff i) hdec
    have h2 := congrArg (fun p => p.coeff i) (liftBy_cast ml m)
    simp only [bgvDecrypt, ofInt_unfold] at h1 h2
    rw [h1, h2]
  refine ⟨⟨fun i => ((centeredPhase s ct).coeff i - (liftBy ml m).coeff i) / t⟩, ?_, ?_⟩
  · have hv : liftBy ml m + zscale t ⟨fun i => ((centeredPhase s ct).coeff i -
        (liftBy ml m).coeff i) / t⟩ = centeredPhase s ct := by
      ext i
      simp only [zscale_eq, coeff_add', coeff_smul']
      rw [Int.mul_ediv_cancel' (hd i)]; ring
    rw [hv, phase_eq]
    exact (ofInt_centered _).symm
  · have hv : liftBy ml m + zscale t ⟨fun i => ((centeredPhase s ct).coeff i -
        (liftBy ml m).coeff i) / t⟩ = centeredPhase s ct := by
      ext i
      simp only [zscale_eq, coeff_add', coeff_smul']
      rw [Int.mul_ediv_cancel' (hd i)]; ring
    rw [hv]; exact hb

/-- **B's equivalence claim, proved**: with `2B < Q` the existential form implies A's. -/
theorem ex_imp_encrypts (ml : Lift) (t B : ℕ) [NeZero t] {Q : ℕ} (s : IntPoly N) (ct : List (Poly Q N))
    (m : Poly t N) (hQ : 2 * B < Q) (h : EncryptsEx ml t s ct m B) : BGVEncrypts t B s ct m := by
  obtain ⟨e, hph, hb⟩ := h
  refine bgvEncrypts_of_phase (liftBy ml m + zscale t e) (by rw [← phase_eq]; exact hph)
    ((normInf_le_iff _ _).mp hb) hQ ?_
  rw [zscale_eq, ofInt_add, liftBy_cast]
  ext i
  simp [ofInt_unfold]

/-- **Without `2B < Q` the existential form says nothing about decryption**: `N = 1`, `Q = 5`,
`t = 2`, `B = 3`; the ciphertext `[3]` has phase `3 = 1 + 2·1` with `‖1 + 2·1‖ = 3 ≤ B`, so it
"encrypts" `1` existentially, but it decrypts (under A's and B's decryption) to `[3]_5 = −2 ≡ 0`. -/
theorem ex_not_imp :
    EncryptsEx .canonical 2 (0 : IntPoly 1) [(⟨fun _ => 3⟩ : Poly 5 1)] (⟨fun _ => 1⟩ : Poly 2 1) 3 ∧
      ¬ BGVEncrypts 2 3 (0 : IntPoly 1) [(⟨fun _ => 3⟩ : Poly 5 1)] (⟨fun _ => 1⟩ : Poly 2 1) := by
  constructor
  · refine ⟨⟨fun _ => 1⟩, ?_, ?_⟩
    · rw [phase_eq]
      ext i
      simp only [Scheme.phase, ofInt_unfold, liftBy, force_eq, zscale_eq]
      revert i; decide +kernel
    · simp only [liftBy, force_eq, zscale_eq]
      unfold normInf; decide +kernel
  · rintro ⟨h, -⟩
    have h1 := congrArg (fun p : Poly 2 1 => p.coeff 0) h
    revert h1
    decide +kernel

end Respec.Equiv
