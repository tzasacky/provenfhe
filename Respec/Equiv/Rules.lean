import Respec.Equiv.Encrypt
import Respec.Equiv.Bookkeeping

/-!
# Respec.Equiv.Rules — item 10: B's unproved rules from A's proved theorems

In this module `A` is the specification (`Spec`, `Challenge`) and `B` the independent
re-specification (`Respec`); "A's `x`" and "B's `x`" are the corresponding definitions of each.

B states its worst-case rules as `Prop`s (`Respec.Noise.FreshRule`, `AddRule`, `MulRule`,
`ModSwitchRule`, `KeySwitchRule`) and only exercises them numerically. Here they are derived from
A's theorems through the equivalences of this directory.

| B rule | status | A theorem used |
|---|---|---|
| `FreshRule ml`, either lift (`t ≥ 2`) | PROVED (`freshRule_of_A` in `Encrypt.lean`) | `Validation.FreshNoise.encrypt_encrypts` at the stored polynomial `liftBy ml m` with declared bound `msgBound ml t`, `phase_encrypt`, `freshError_worst` |
| `AddRule` (any lengths) | PROVED (`addRule_of_A`) | `Validation.Scheme.bgvEncrypts_of_phase` (+ `phase_add` here: B's padded `add`) |
| `MulRule`, two 2-component operands | PROVED (`mulRule2_of_A`) | `Validation.Scheme.bgvEncrypts_tensor` |
| `MulRule`, any lengths | PROVED (`mulRule_general` in `MulRule.lean`) | `Validation.Scheme.bgvEncrypts_of_phase`, `abs_coeff_mul_le_N` (+ `phase_mulTensor` there: the Cauchy product for B's `mulTensor`) |
| `ModSwitchRule .centred` | PROVED (`modSwitchRule_centred` in `ModSwitchRule.lean`; any number of components: `modSwitch_centred_parts`) | `ModSwitch.modSwitchElt_eq`, `Validation.Switch.q_mul_sw`, `abs_corr_le`, `Validation.Trace.divq_gen`, `intPhase_switch`, `abs_coeff_intPhase_le` |
| `ModSwitchRule .canonical` | not proved, not stated as a theorem anywhere (A has no budget for the `[0, q)` correction) | — |
| `KeySwitchRule` | PROVED for A's key form (`Bookkeeping.bKeySwitch_*_bound`), constants compared in `KsBound.lean`; B's rule as stated (B's own key generator `hybridKeyGen`, arbitrary `sFrom`, either lift, B's constant) OPEN, not stated as a theorem (for canonical lifts A's bound is weaker than B's constant: `ksBoundAt_canonical_ge`) | `keySwitchBGV_spec`, `keySwitchBGVOpenFHE_spec` |

`FreshRule` at `t = 1` is not covered (A's `encrypt_encrypts` needs `t ≥ 2`; `t = 1` is not a
meaningful plaintext modulus). `FreshRule .centred` (message lifted to `(−t/2, t/2]`, bound
`⌊t/2⌋ + …`) is A's `encrypt_encrypts` for a centred stored plaintext (`Bp = ⌊t/2⌋`,
`Challenge.FreshNoise.centered_stored`); OpenFHE's packed encoding stores the `[0, t)` lift
(`FreshRule .canonical`).
-/

namespace Respec.Equiv

open Spec Spec.NPoly Spec.Scheme Respec Respec.BGV Respec.Noise Validation.Ring Validation.Scheme

variable {N : ℕ}

/-- The phase of B's (zero-padded) componentwise sum. -/
theorem phase_add {Q : ℕ} (x : Poly Q N) : ∀ (c d : List (Poly Q N)),
    Scheme.phase x (BGV.add c d) = Scheme.phase x c + Scheme.phase x d
  | [], d => by
      apply eq_of_neZero; intro; simp only [BGV.add, Scheme.phase]; ring
  | c :: cs, [] => by
      apply eq_of_neZero; intro; simp only [BGV.add, Scheme.phase]; ring
  | c :: cs, d :: ds => by
      simp only [BGV.add, Scheme.phase, padd_eq]
      rw [phase_add x cs ds]
      apply eq_of_neZero; intro; ring

/-- **B's `AddRule`, from A.** -/
theorem addRule_of_A (N t Q : ℕ) : AddRule N t Q := by
  intro s c1 c2 m1 m2 B1 B2 h1 h2 hQ
  rw [← bgvEncrypts_iff] at h1 h2 ⊢
  refine bgvEncrypts_of_phase (centeredPhase s c1 + centeredPhase s c2) ?_ ?_ hQ ?_
  · rw [← phase_eq, phase_eq, phase_add, phase_eq_ofInt_centeredPhase s c1,
      phase_eq_ofInt_centeredPhase s c2, ofInt_add]
  · intro i
    have := (BGVEncrypts.bound h1) i
    have := (BGVEncrypts.bound h2) i
    rw [coeff_add']
    simp only [addBound]; push_cast
    exact (abs_add_le _ _).trans (by linarith)
  · rw [ofInt_add, BGVEncrypts.msg h1, BGVEncrypts.msg h2]

/-- B's tensor of two 2-component ciphertexts is A's. -/
theorem mulTensor_two {Q : ℕ} [NeZero N] (a0 a1 b0 b1 : Poly Q N) :
    mulTensor [a0, a1] [b0, b1] = [a0 * b0, a0 * b1 + a1 * b0, a1 * b1] := by
  simp [mulTensor, psum_eq, List.range_succ]

/-- **B's `MulRule` for two 2-component ciphertexts, from A's `bgvEncrypts_tensor`.** -/
theorem mulRule2_of_A (N t Q : ℕ) :
    ∀ (s : IntPoly N) (a0 a1 b0 b1 : Poly Q N) (m1 m2 : Poly t N) (B1 B2 : ℕ),
      Encrypts t s [a0, a1] m1 B1 → Encrypts t s [b0, b1] m2 B2 → 2 * mulBound N B1 B2 < Q →
      Encrypts t s (mulTensor [a0, a1] [b0, b1]) (m1 * m2) (mulBound N B1 B2) := by
  intro s a0 a1 b0 b1 m1 m2 B1 B2 h1 h2 hQ
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    rw [← bgvEncrypts_iff] at h1 h2 ⊢
    refine ⟨?_, by simp [normInf_unfold]⟩
    exact eq_of_N_zero rfl _ _
  haveI : NeZero N := ⟨hN.ne'⟩
  rw [← bgvEncrypts_iff] at h1 h2 ⊢
  rw [mulTensor_two]
  exact bgvEncrypts_tensor h1 h2 hQ

end Respec.Equiv
