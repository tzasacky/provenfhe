import Respec.Noise
import Respec.Equiv.Decrypt
import Spec.Encrypt
import Validation.FreshNoise.Basic

/-!
# Respec.Equiv.Encrypt — item 3: public-key encryption and the fresh-noise constants

In this module `A` is the specification (`Spec`, `Challenge`) and `B` the independent
re-specification (`Respec`); "A's `x`" and "B's `x`" are the corresponding definitions of each.

A's `Spec.Encrypt.encrypt t b a p u e₁ e₂` takes the **stored plaintext polynomial** `p`
(an integer polynomial; the message is `p mod t`) and A's `freshNoise t Bp ε = Bp + t·ε` takes a
declared bound `Bp` on `‖p‖∞`. B's `BGV.encrypt ml pk m u e0 e1` takes a message `m : Poly t N`
and a lift `ml : Lift` and adds `liftBy ml m`. **Convention of this file**: B's encryption of `m`
with lift `ml` is compared with A's encryption of the stored polynomial `p = liftBy ml m`
(`liftBy .canonical m = liftMsg m`, the `[0, t)` lift; `liftBy .centred m = centered m`), and B's
message bound `msgBound ml t` (`t − 1`, resp. `⌊t/2⌋`) is A's declared bound `Bp`.

## Verdicts (PROVED, no `sorry`)

* `liftMsg_eq`, `liftBy_centred_eq` : B's `liftBy .canonical` is A's `liftMsg`; B's
  `liftBy .centred` is `Spec.NPoly.centered`. `liftBy_stored` : for `0 < t`, `liftBy ml m`
  represents `m` and `‖liftBy ml m‖∞ ≤ msgBound ml t` (from A's `liftMsg_stored`,
  `centered_stored`).
* `pkGen_iff` : A's `PublicKeyOK t Q s e b a` holds **iff** `b ≡ (pkGen t s a e).b (mod Q)`:
  A's key relation is B's OpenFHE key `b = t·e − a·s` (B's `pkGenStd`, the HES18/SEAL key,
  satisfies it with `−e`: `pkGenStd_ok`).
* `encrypt_eq` : for **either lift** `ml`, A's `encrypt` of the stored polynomial `liftBy ml m`
  (integer representatives) reduced mod `Q` **is** B's `encrypt ml` of `m` for the public key
  `(b mod Q, a mod Q)`, component for component (A's `e₁, e₂` are B's `e0, e1`).
  `encrypt_eq_liftMsg`, `encrypt_eq_centered` : the two instances, with `liftMsg m` and
  `centered m` written out.
* `freshCrit_eq` : B's `freshCrit ml` is `liftBy ml m + t • freshError s e u e₁ e₂`, i.e. the
  integer of A's `phase_encrypt` at `p = liftBy ml m`.
* `freshBound_eq` : **constants reconcile exactly, for either lift**: B's
  `freshBound ml N t Bs Be Bu = msgBound ml t + t·(N·Be·Bu + Be + N·Be·Bs)` equals A's
  `freshNoise t (msgBound ml t) (worstError N Bs Be Bu Be Be)`. B's single `Be` is A's
  `Bk = B1 = B2`; B's `Bu` is A's `Bu`; B's message term `msgBound ml t` is A's declared
  plaintext bound `Bp`. `freshBound_centred_le` : B's centred constant is `≤` B's canonical one.
* `freshRule_of_A` : **B's `FreshRule ml`, for either lift, is a consequence of A's proved
  `encrypt_encrypts`** for `t ≥ 2` (B's rule asks only `0 < t`; `t = 1` is not covered here:
  A's theorem has the hypothesis `2 ≤ t`).

Not compared: A's statements for a stored polynomial that is not a lift of the message
(`Bp > t − 1`, the `FLEXIBLEAUTO` case of `Spec/Encrypt.lean`); B has no counterpart.
-/

namespace Respec.Equiv

open Spec Spec.NPoly Spec.Scheme Spec.Encrypt Respec Respec.BGV Respec.Noise Validation.Ring
  Validation.Scheme

variable {N : ℕ}

theorem liftMsg_eq {t : ℕ} (m : Poly t N) : liftBy .canonical m = liftMsg m := by
  ext i
  show (liftBy .canonical m).coeff i = ((m.coeff i).val : ℤ)
  simp [liftBy, Lift.rep]

theorem liftBy_centred_eq {t : ℕ} (m : Poly t N) : liftBy .centred m = centered m := by
  ext i
  rw [coeff_centered]
  simp [liftBy, Lift.rep]

/-- B's lift of a message is a stored plaintext for it, within B's message bound. -/
theorem liftBy_stored (ml : Lift) (t : ℕ) (ht : 0 < t) (m : Poly t N) :
    ofInt t (liftBy ml m) = m ∧ normInf (liftBy ml m) ≤ msgBound ml t := by
  cases ml with
  | canonical => rw [liftMsg_eq]; exact Validation.FreshNoise.liftMsg_stored t ht m
  | centred => rw [liftBy_centred_eq]; exact Validation.FreshNoise.centered_stored t ht m

/-- A's public-key relation is B's OpenFHE key generation. -/
theorem pkGen_iff (t Q : ℕ) (s e b a : IntPoly N) :
    PublicKeyOK t Q s e b a ↔ ofInt Q b = (pkGen (Q := Q) t s a e).b := by
  apply Iff.intro
  · intro h
    apply eq_of_neZero; intro
    have h' : ofInt Q (b + a * s) = ofInt Q ((t : ℤ) • e) := h
    simp only [ofInt_add, ofInt_mul, Validation.FreshNoise.ofInt_smul'] at h'
    simp only [pkGen, psub_eq, pmul_eq, psmul_eq, red_eq]
    simp only [smul_eq_const_mul, Int.cast_natCast] at h' ⊢
    linear_combination h'
  · intro h
    apply eq_of_neZero; intro
    show ofInt Q (b + a * s) = ofInt Q ((t : ℤ) • e)
    simp only [ofInt_add, ofInt_mul, Validation.FreshNoise.ofInt_smul', h]
    simp only [pkGen, psub_eq, pmul_eq, psmul_eq, red_eq]
    simp only [smul_eq_const_mul, Int.cast_natCast]
    ring

/-- The HES18/SEAL key `b = −(a·s + t·e)` satisfies A's relation with the error `−e`. -/
theorem pkGenStd_ok (t Q : ℕ) (s a e : IntPoly N) (b : IntPoly N)
    (hb : ofInt Q b = (pkGenStd (Q := Q) t s a e).b) : PublicKeyOK t Q s (-e) b a := by
  apply eq_of_neZero; intro
  show ofInt Q (b + a * s) = ofInt Q ((t : ℤ) • -e)
  simp only [ofInt_add, ofInt_mul, Validation.FreshNoise.ofInt_smul', ofInt_neg, hb]
  simp only [pkGenStd, pneg_eq, padd_eq, pmul_eq, psmul_eq, red_eq]
  simp only [smul_eq_const_mul, Int.cast_natCast]
  ring

/-- **A's encryption of the stored polynomial `liftBy ml m` is B's encryption of `m` with lift
`ml`**, component for component. -/
theorem encrypt_eq (ml : Lift) (t Q : ℕ) (b a u e₁ e₂ : IntPoly N) (m : Poly t N) :
    (Spec.Encrypt.encrypt t b a (liftBy ml m) u e₁ e₂).map (ofInt Q) =
      BGV.encrypt (Q := Q) ml ⟨ofInt Q b, ofInt Q a⟩ m u e₁ e₂ := by
  show [ofInt Q (b * u + (t : ℤ) • e₁ + liftBy ml m), ofInt Q (a * u + (t : ℤ) • e₂)] = _
  simp only [BGV.encrypt, embed, padd_eq,
    pmul_eq, psmul_eq, red_eq, ofInt_add, ofInt_mul, Validation.FreshNoise.ofInt_smul']
  have : ((t : ℤ) : ZMod Q) = ((t : ℕ) : ZMod Q) := by simp
  rw [this]

/-- The canonical instance: A's encryption of `liftMsg m` (packed encoding) is B's
`encrypt .canonical`. -/
theorem encrypt_eq_liftMsg (t Q : ℕ) (b a u e₁ e₂ : IntPoly N) (m : Poly t N) :
    (Spec.Encrypt.encrypt t b a (liftMsg m) u e₁ e₂).map (ofInt Q) =
      BGV.encrypt (Q := Q) .canonical ⟨ofInt Q b, ofInt Q a⟩ m u e₁ e₂ := by
  rw [← liftMsg_eq]; exact encrypt_eq .canonical t Q b a u e₁ e₂ m

/-- The centred instance: A's encryption of `centered m` is B's `encrypt .centred`. -/
theorem encrypt_eq_centered (t Q : ℕ) (b a u e₁ e₂ : IntPoly N) (m : Poly t N) :
    (Spec.Encrypt.encrypt t b a (centered m) u e₁ e₂).map (ofInt Q) =
      BGV.encrypt (Q := Q) .centred ⟨ofInt Q b, ofInt Q a⟩ m u e₁ e₂ := by
  rw [← liftBy_centred_eq]; exact encrypt_eq .centred t Q b a u e₁ e₂ m

/-- B's fresh critical quantity is `liftBy ml m + t·freshError` (A's `phase_encrypt` integer at
the stored polynomial `liftBy ml m`). -/
theorem freshCrit_eq (ml : Lift) {t : ℕ} (m : Poly t N) (s e u e₁ e₂ : IntPoly N) :
    freshCrit ml m s e u e₁ e₂ = liftBy ml m + (t : ℤ) • freshError s e u e₁ e₂ := by
  show _ = liftBy ml m + (t : ℤ) • (e * u + e₁ + e₂ * s)
  simp only [freshCrit, padd_eq, pmul_eq, zscale_eq]

/-- **The constants reconcile exactly**, for either lift: B's message bound is A's declared
plaintext bound. -/
theorem freshBound_eq (ml : Lift) (N t Bs Be Bu : ℕ) :
    freshBound ml N t Bs Be Bu = freshNoise t (msgBound ml t) (worstError N Bs Be Bu Be Be) := by
  unfold freshBound freshNoise worstError
  ring

/-- B's centred-message constant is no larger than B's canonical one (which is A's
`freshNoise t (t − 1) …`). -/
theorem freshBound_centred_le (N t Bs Be Bu : ℕ) :
    freshBound .centred N t Bs Be Bu ≤ freshNoise t (t - 1) (worstError N Bs Be Bu Be Be) := by
  have h := freshBound_eq .canonical N t Bs Be Bu
  simp only [msgBound] at h
  rw [← h]
  simp only [freshBound, msgBound]
  have : t / 2 ≤ t - 1 ∨ t = 0 := by omega
  rcases this with h | h
  · omega
  · subst h; simp

/-- **B's `FreshRule ml` (either lift, `t ≥ 2`) from A's proved `encrypt_encrypts`** applied to
the stored polynomial `liftBy ml m` with declared bound `msgBound ml t`. -/
theorem freshRule_of_A (ml : Lift) (N t Q : ℕ) (ht : 2 ≤ t) : FreshRule ml N t Q := by
  intro s a e u e0 e1 m Bs Be Bu _ _ hs he he0 he1 hu hQ
  haveI : NeZero t := ⟨by omega⟩
  -- an integer representative of B's public key
  set b : IntPoly N := (t : ℤ) • e - a * s
  have hb : ofInt Q b = (pkGen (Q := Q) t s a e).b := by
    apply eq_of_neZero; intro
    simp only [b, ofInt_sub, ofInt_mul, Validation.FreshNoise.ofInt_smul', pkGen, psub_eq, pmul_eq,
      psmul_eq, red_eq]
    have : ((t : ℤ) : ZMod Q) = ((t : ℕ) : ZMod Q) := by simp
    rw [this]
  have hpk : PublicKeyOK t Q s e b a := (pkGen_iff t Q s e b a).mpr hb
  have hct : BGV.encrypt (Q := Q) ml (pkGen t s a e) m u e0 e1 =
      (Spec.Encrypt.encrypt t b a (liftBy ml m) u e0 e1).map (ofInt Q) := by
    rw [encrypt_eq]
    congr 1
    show (⟨(pkGen (Q := Q) t s a e).b, (pkGen (Q := Q) t s a e).a⟩ : PublicKey Q N) = _
    rw [← hb]; simp [pkGen, red_eq]
  obtain ⟨hpm, hpB⟩ := liftBy_stored ml t (by omega) m
  have hε := Validation.FreshNoise.freshError_worst s e u e0 e1 Bs Be Bu Be Be hs he hu he0 he1
  have hQ' : 2 * freshNoise t (msgBound ml t) (worstError N Bs Be Bu Be Be) < Q := by
    rwa [← freshBound_eq]
  have henc := Validation.FreshNoise.encrypt_encrypts t Q _ _ ht s e b a (liftBy ml m) u e0 e1
    hpk hpB hε hQ'
  rw [← freshBound_eq, hpm] at henc
  refine ⟨?_, ?_⟩
  · rw [hct, crit_eq, freshCrit_eq]
    -- the centred phase is the integer `liftBy ml m + t·freshError`, which is small
    rw [centeredPhase, Validation.FreshNoise.phase_encrypt t Q s e b a _ u e0 e1 hpk]
    apply centered_ofInt
    intro i
    have h1 : |(liftBy ml m).coeff i| ≤ (msgBound ml t : ℤ) := (normInf_le_iff _ _).mp hpB i
    have h2 := (normInf_le_iff _ _).mp hε i
    have h3 : (liftBy ml m + (t : ℤ) • freshError s e u e0 e1).coeff i =
        (liftBy ml m).coeff i + (t : ℤ) * (freshError s e u e0 e1).coeff i := rfl
    rw [h3]
    have hQ'' : ((2 * freshNoise t (msgBound ml t) (worstError N Bs Be Bu Be Be) : ℕ) : ℤ) < Q := by
      exact_mod_cast hQ'
    have h4 : ((freshNoise t (msgBound ml t) (worstError N Bs Be Bu Be Be) : ℕ) : ℤ) =
        (msgBound ml t : ℤ) + t * (worstError N Bs Be Bu Be Be : ℕ) := by
      unfold freshNoise
      rw [Nat.cast_add, Nat.cast_mul]
    push_cast at hQ''
    rw [h4] at hQ''
    have h7 : |(t : ℤ) * (freshError s e u e0 e1).coeff i| ≤ t * (worstError N Bs Be Bu Be Be : ℕ) := by
      rw [abs_mul, abs_of_nonneg (Int.natCast_nonneg t)]
      exact mul_le_mul_of_nonneg_left h2 (Int.natCast_nonneg t)
    have := abs_add_le ((liftBy ml m).coeff i) ((t : ℤ) * (freshError s e u e0 e1).coeff i)
    linarith
  · rw [hct, ← bgvEncrypts_iff]; exact henc

end Respec.Equiv
