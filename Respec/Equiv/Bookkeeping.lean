import Respec.Equiv.KeySwitch
import Respec.Equiv.ModSwitch
import Spec.Decrypt
import FHE.KeySwitch.Order

/-!
# Respec.Equiv.Bookkeeping — items 8 and 9, and B's algorithm under A's key-switching theorem

In this module `A` is the specification (`Spec`, `Challenge`) and `B` the independent
re-specification (`Respec`); "A's `x`" and "B's `x`" are the corresponding definitions of each.

## Item 8: message-level bookkeeping (PROVED, EQUAL UP TO THE CONVENTION `msg_A = sf_B • msg_B`)

A's `Source.Val` carries the message the ciphertext *actually* decrypts to (scaling factors
folded in); B's `State` carries the user's message and a scaling factor `sf` separately. With
`transl st = st.sf • st.msg`:
* `transl_add` : B's `State.add` (equal `sf` required) ↦ A's `m₁ + m₂`;
* `transl_mul` : B's `State.mul` (`sf` multiply) ↦ A's `m₁ · m₂`; parts `p + p' − 1` =
  `(d₁+1) + (d₂+1) − 1` (`parts_mul`);
* `transl_mulConst` : B's `mulConstSF c` ↦ A's `(c mod t) • m`;
* `transl_automorph` : B's `automorphRaw g` ↦ A's `σ_g(m)`; keys `(key·g) mod 2N` on both sides
  (`key_automorph`);
* `transl_modSwitch` : `Respec.Equiv.state_modSwitch_translate` (ModSwitch.lean);
* `levelReduce`/`dropLimbs`: message and `sf` unchanged on both sides (definitional).
Rotation order: A's `Instr.automorph` then `Instr.keySwitch` (key target `σ_g(s)`, i.e. a key
*from* `σ_g(s)` *to* `s`) is SEAL's order and key (B's `evalAutomorphismSEAL`,
`galoisKeyGenSEAL`). OpenFHE's (`evalAutomorphismOF`: key from `s` to `σ_{g⁻¹}(s)`, switch, then
`σ_g`) is admitted by A's `FHE.KeySwitch.Order.openfhe_rotation_run` at the contract level, and
**`galoisKeyOF_valid`** (PROVED here) shows OpenFHE's key for `g` *is* an A-valid key for target
`galois g` under the secret `σ_{g⁻¹}(s)` (same norm), so A's key-switching theorem bounds its error.

## Item 9: decryption as OpenFHE does it (PROVED per step)

`switchPhase_eq` : A's `Spec.Decrypt.switchPhase` is A's textbook `bgvModSwitchComp`, hence
(`ModSwitch.modSwitchElt_eq`) B's `modSwitchElt (.ghs .centred)` applied to the one-component
ciphertext `[phase]`. So A's `bgvDecryptSwitched` is OpenFHE `PKEBGVRNS::Decrypt`'s
EVALUATION-format branch (bgvrns-pke.cpp:52-71: `DecryptCore`, then `ModReduce` of the *phase*
`b`, limb by limb, then `DecryptionCRTInterpolate` = centred reduction mod `q₀` then mod `t`,
poly-impl.h:574-583 / mubintvecnat.cpp:145-161). B's `ctL0` test follows the COEFFICIENT-format
branch (l.73-90: `ModReduce` of every *component*, then `DecryptCore`), which yields the same
message but a larger noise (`δ₁·s` terms). Both scale the message by `(q₁⋯q_{ℓ−1})⁻¹ mod t` = A's
`decScale` = OpenFHE's `scalingFactorInt` update (FLEXIBLEAUTO*).

## B's RNS key-switching algorithm under A's theorem (PROVED)

`bKeySwitch_canonical_bound`, `bKeySwitch_centred_bound` : for keys valid in A's sense, B's
`hybridKeySwitch` output satisfies A's proved correctness and noise bound
(`keySwitchBGVOpenFHE_spec`, `keySwitchBGV_spec`), read through B's own CRT (`ofRns`).
This is B's `KeySwitchRule` with A's constants (`ksBound`, which is `⌊ksAddedBound⌋` centred and
`≥` it canonical, see KsBound.lean), for A's key form (targets `s²`, `σ_g(s)`); B's rule for
B's own key generator and an arbitrary `sFrom` is open (`Rules.lean`, the `KeySwitchRule`
row).
-/

namespace Respec.Equiv

open Spec Spec.NPoly Spec.Scheme Spec.Source Respec Respec.BGV Validation.Ring Validation.Scheme
  FHE.KeySwitch

variable {N k l : ℕ}

/-! ### Item 8 -/

/-- B's state, read as the message A tracks. -/
def transl {t : ℕ} (st : State t N) : Poly t N := st.sf • st.msg

theorem transl_add {t : ℕ} (a b c : State t N) (h : a.add b = some c) :
    transl c = transl a + transl b := by
  unfold State.add at h
  split_ifs at h with hc
  cases h
  ext i; simp only [transl, coeff_smul', coeff_add', hc.2.1]; ring

theorem transl_mul {t : ℕ} [NeZero N] (a b c : State t N) (h : a.mul b = some c) :
    transl c = transl a * transl b := by
  unfold State.mul at h
  split_ifs at h with hc
  cases h
  simp only [transl, smul_eq_const_mul]
  have : const (a.sf * b.sf) = (const a.sf : NPoly (ZMod t) N) * const b.sf :=
    (constRingHom (R := ZMod t) (N := N)).map_mul _ _
  rw [this]; ring

theorem parts_mul {t : ℕ} (a b c : State t N) (h : a.mul b = some c) :
    c.deg + 1 = (a.deg + 1) + (b.deg + 1) - 1 := by
  unfold State.mul at h
  split_ifs at h with hc
  cases h; simp; omega

theorem transl_mulConst {t : ℕ} (c : ℤ) (a : State t N) :
    transl (a.mulConstSF c) = (c : ZMod t) • transl a := by
  ext i; simp only [transl, State.mulConstSF, coeff_smul']; ring

theorem automorph_smul' {t : ℕ} (g : ℕ) (c : ZMod t) (m : Poly t N) :
    NPoly.automorph g (c • m) = c • NPoly.automorph g m := by
  ext k
  simp only [coeff_automorph', coeff_smul', Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> ring

theorem transl_automorph {t : ℕ} (g : ℕ) (a : State t N) :
    transl (a.automorphRaw g) = NPoly.automorph g (transl a) := by
  simp only [transl, State.automorphRaw, automorph_smul']

theorem key_automorph {t : ℕ} (g : ℕ) (a : State t N) :
    (a.automorphRaw g).keyElt = (a.keyElt * g) % (2 * N) := by
  simp [State.automorphRaw, Nat.mul_comm]

/-- **OpenFHE's Galois key for `g` is an A-valid key for the target `galois g`**, under the
secret `σ_{g⁻¹}(s)`: OpenFHE's key relation `b + a·σ_{g⁻¹}(s) = f·s + e` is A's
`KeyValid … (σ_{g⁻¹}(s)) ⟨M, f, .galois g⟩` because `σ_g(σ_{g⁻¹}(s)) = s`. -/
theorem galoisKeyOF_valid (kind : Kind) (t B M : ℕ) (s : IntPoly N) (g ginv : ℕ)
    (hg : g % 2 = 1) (hinv : (ginv * g) % (2 * N) = 1) (f : Poly M N) (b a : Poly M N)
    (h : normInf (centered (b + a * ofInt M (NPoly.automorph ginv s) - f * ofInt M s)) ≤ B ∧
      (kind = .bgv → ∀ i, (t : ℤ) ∣ (centered (b + a * ofInt M (NPoly.automorph ginv s) -
        f * ofInt M s)).coeff i)) :
    KeyValid kind t B (NPoly.automorph ginv s) ⟨M, f, .galois g⟩ b a := by
  have e : (KeyTarget.galois g).eval (NPoly.automorph ginv s) = s := by
    show NPoly.automorph g (NPoly.automorph ginv s) = s
    rw [Validation.Source.automorph_automorph hg, ← Validation.Source.automorph_mod, hinv,
      FHE.KeySwitch.automorph_one]
  unfold KeyValid
  simp only [e]
  exact h

/-! ### Item 9 -/

theorem switchPhase_eq (t q : ℕ) (c : IntPoly N) :
    Spec.Decrypt.switchPhase t q c = Challenge.Source.bgvModSwitchComp t q c := rfl

/-- One round of A's switched decryption is B's `modSwitchElt (.ghs .centred)` of the phase. -/
theorem switchPhase_round (t q Q' : ℕ) (hq : 0 < q) (hQ' : 0 < Q') (hcop : Nat.Coprime t q)
    (c : IntPoly N) :
    ofInt Q' (Spec.Decrypt.switchPhase t q c) =
      modSwitchElt (.ghs .centred) t q Q' (ofInt (Q' * q) c) := by
  rw [switchPhase_eq]; exact modSwitchElt_eq t q Q' hq hQ' hcop c

/-! ### B's algorithm under A's theorem -/

theorem ofRns_toB (C : FHE.RNS.Basis k) (y : FHE.RNS.RNSPoly C N) :
    ofRns C.q (toB C y) = C.combine y := by
  ext j
  simp only [ofRns, force_eq, crt, fastBConvZ_all_canonical, FHE.RNS.Basis.combine,
    FHE.RNS.Basis.reconstruct_eq_intCast, FHE.RNS.Basis.fbcInt]
  rfl

theorem toB_ext (C : FHE.RNS.Basis k) (x : RnsPoly C.q N) (y : FHE.RNS.RNSPoly C N)
    (h : ∀ i, x.limb i = y i) : x = toB C y := by
  cases x; simp only [toB, RnsPoly.mk.injEq]; funext i; exact h i

/-- **B's canonical algorithm meets A's proved bound** (A-valid keys). -/
theorem bKeySwitch_canonical_bound [NeZero N] (Dg : Digits k) (C : FHE.RNS.Basis k)
    (Bp : FHE.RNS.Basis l) {t Bk Bs : ℕ} (ht : ∀ j, Nat.Coprime t (Bp.q j))
    (hcop : ∀ i, Nat.Coprime Bp.prod (C.q i)) (s : IntPoly N) (hs : normInf s ≤ Bs)
    (tgt : KeyTarget) (kb ka : Fin Dg.dnum → Poly (C.prod * Bp.prod) N)
    (hkey : ∀ j, KeyValid .bgv t Bk s (gadgetReq Dg C Bp tgt j) (kb j) (ka j))
    (a : FHE.RNS.RNSPoly C N) :
    ∃ e : IntPoly N,
      ofRns C.q (hybridKeySwitch .canonical (some t) C.q Bp.q (digOf Dg) (keyOfA Dg C Bp kb ka)
          (toB C a)).1 +
        ofRns C.q (hybridKeySwitch .canonical (some t) C.q Bp.q (digOf Dg) (keyOfA Dg C Bp kb ka)
          (toB C a)).2 * ofInt (Respec.Basis.prod C.q) s =
        ofRns C.q (toB C a) * ofInt (Respec.Basis.prod C.q) (tgt.eval s) +
          ofInt (Respec.Basis.prod C.q) e ∧
      (∀ c, (t : ℤ) ∣ e.coeff c) ∧
      normInf e ≤ ksBound N Bk Bs t (2 * (l * (Bp.prod - 1))) Bp.prod (canonWeight Dg C) := by
  obtain ⟨y0, y1, e, hout, heq, hdvd, hb⟩ :=
    keySwitchBGVOpenFHE_spec Dg C Bp ht hcop s hs tgt kb ka hkey a
  obtain ⟨h1, h2⟩ := keySwitch_openfhe_eq Dg C Bp t a kb ka
  refine ⟨e, ?_, hdvd, hb⟩
  have key : C.combine (C.toRNS y0) + C.combine (C.toRNS y1) * ofInt C.prod s =
      C.combine a * ofInt C.prod (tgt.eval s) + ofInt C.prod e := by
    simp only [FHE.RNS.Basis.combine_toRNS]
    rw [← ofInt_mul, ← ofInt_add, heq, ofInt_add, ofInt_mul, ofInt_centered]
  rw [toB_ext C _ _ h1, toB_ext C _ _ h2, ofRns_toB, ofRns_toB, ofRns_toB, hout]
  exact key

/-- **B's centred algorithm meets A's proved bound** (A-valid keys, odd special primes). -/
theorem bKeySwitch_centred_bound [NeZero N] (Dg : Digits k) (C : FHE.RNS.Basis k)
    (Bp : FHE.RNS.Basis l) (hodd : ∀ j, Bp.q j % 2 = 1) {t Bk Bs : ℕ}
    (ht : ∀ j, Nat.Coprime t (Bp.q j))
    (hcop : ∀ i, Nat.Coprime Bp.prod (C.q i)) (s : IntPoly N) (hs : normInf s ≤ Bs)
    (tgt : KeyTarget) (kb ka : Fin Dg.dnum → Poly (C.prod * Bp.prod) N)
    (hkey : ∀ j, KeyValid .bgv t Bk s (gadgetReq Dg C Bp tgt j) (kb j) (ka j))
    (a : FHE.RNS.RNSPoly C N) :
    ∃ e : IntPoly N,
      ofRns C.q (hybridKeySwitch .centred (some t) C.q Bp.q (digOf Dg) (keyOfA Dg C Bp kb ka)
          (toB C a)).1 +
        ofRns C.q (hybridKeySwitch .centred (some t) C.q Bp.q (digOf Dg) (keyOfA Dg C Bp kb ka)
          (toB C a)).2 * ofInt (Respec.Basis.prod C.q) s =
        ofRns C.q (toB C a) * ofInt (Respec.Basis.prod C.q) (tgt.eval s) +
          ofInt (Respec.Basis.prod C.q) e ∧
      (∀ c, (t : ℤ) ∣ e.coeff c) ∧
      normInf e ≤ ksBound N Bk Bs t (l * Bp.prod) Bp.prod (digitWeight Dg C) := by
  obtain ⟨y0, y1, e, hout, heq, hdvd, hb⟩ :=
    keySwitchBGV_spec Dg C Bp ht hcop s hs tgt kb ka hkey a
  obtain ⟨h1, h2⟩ := keySwitch_centred_eq Dg C Bp hodd t a kb ka
  refine ⟨e, ?_, hdvd, hb⟩
  have key : C.combine (C.toRNS y0) + C.combine (C.toRNS y1) * ofInt C.prod s =
      C.combine a * ofInt C.prod (tgt.eval s) + ofInt C.prod e := by
    simp only [FHE.RNS.Basis.combine_toRNS]
    rw [← ofInt_mul, ← ofInt_add, heq, ofInt_add, ofInt_mul, ofInt_centered]
  rw [toB_ext C _ _ h1, toB_ext C _ _ h2, ofRns_toB, ofRns_toB, ofRns_toB, hout]
  exact key

end Respec.Equiv
