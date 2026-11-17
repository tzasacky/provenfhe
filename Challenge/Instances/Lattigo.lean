import Challenge.Instances.Lattigo.Defs
import Challenge.Profile
import Challenge.BudgetRestrict

/-!
# Challenge.Instances.Lattigo — Lattigo's BGV as an instance of the profile interface   (LOCKED statements; proofs in `Validation/Instances/Lattigo.lean`)

The profile is `Challenge.Instances.Lattigo.profile` (definitions and source citations in
`Challenge.Instances.Lattigo.Defs`).

1. **Coverage at Lattigo's parameters** (`small_instanceOK`, `exampleLogN14_instanceOK`,
   kernel-checked): `instanceOK?` holds at Lattigo's 128-bit example literal at `LogN = 14` and at
   a small set with Lattigo's own primes used for the conformance runs. It is
   `Challenge.Profile.coversBGV?` at `layout P` and `maxParts = 3`, and the size condition under
   which one top-level key set serves every level.
2. **Achievability** (`relin_meets`, `keySwitch_meets`, `modSwitch_meets`): wherever `instanceOK?`
   holds, centred hybrid key switching on Lattigo's digit layout with ONE top-level key set
   (`Challenge.Budget.relin_realizable_top`, `keySwitch_realizable_top`) and the centred
   t-corrected modulus switch of `1, …, 3` components (`Challenge.Budget.modSwitch_realizable_parts`)
   meet the step contracts within `profile P`. These are statements about the proved LSB
   algorithm family. Lattigo's own MSB key switch and rescale are covered by
   `Challenge.Instances.Lattigo.relin_meets_msb`, `keySwitch_meets_msb`, `rescale_meets_msb` and
   their t-readings `*_meets_lsb` (`Challenge.Instances.Lattigo.MSB`, `Challenge.MSB`), as
   transcribed in `Spec.MSB`. What remains executed or argued, not proved: that Lattigo's Go code
   computes that transcription (binary64 `ModUpExact`, the fused `Automorphism`), the
   fresh-encryption error bounds and `BaseTwoDecomposition ≠ 0` (`harness/lattigo-pin`).
3. **Certificates at the profile** (`exampleLogN14_accepts`, `small_accepts`): `certifyProfile?`
   accepts a chain of four multiplicative levels at `exampleLogN14` and rejects five (the worst
   case analysis; the chain has eleven switchable levels), and accepts the full three-level chain
   and the recorded program shape `smallProg` at `small`, so `Challenge.Profile.certifyProfile?_sound`
   applies to them.

**What this does not say.** Nothing here is about the plaintext scale Lattigo tracks per
ciphertext (`MetaData.Scale`) or about decoded slot values: the contracts are about phases. Nor
does it cover `BaseTwoDecomposition ≠ 0`, parameter literals with other error or secret
distributions, or the BFV mode of the same package.
-/

namespace Challenge.Instances.Lattigo
open Spec NPoly Scheme Source Correct Challenge.Profile

/-! ## 1. Coverage at Lattigo's parameters -/

/-- **The small conformance set is an instance**, kernel-checked. -/
theorem small_instanceOK : instanceOK? small = true := sorry

/-- **Lattigo's `LogN = 14` example literal is an instance**, kernel-checked. -/
theorem exampleLogN14_instanceOK : instanceOK? exampleLogN14 = true := sorry

/-! ## 2. Achievability -/

/-- **Hybrid relinearization on Lattigo's digits with one top-level key set meets the `relin`
contract within the Lattigo profile**, at every level, wherever `instanceOK?` holds. -/
theorem relin_meets (P : FullParams) (h : instanceOK? P = true) (ℓ : ℕ) (h1 : 1 ≤ ℓ)
    (hℓ : ℓ ≤ P.src.qs.length) :
    ∃ f : List (IntPoly P.src.N) → List (IntPoly P.src.N × IntPoly P.src.N) →
        List (IntPoly P.src.N),
      ∀ (s : IntPoly P.src.N), SecretOK P.secretBound s →
      ∀ (keys : List (IntPoly P.src.N × IntPoly P.src.N)),
        Budget.GadgetKeysOK P (layout P) P.src.qs.length .square s keys →
      ∀ (ρ ρ' : Env P.src) (σ : Trace.CtEnv P) (d a : Var) (x : Val P.src)
        (ca : List (IntPoly P.src.N)),
        step P.src ρ (.relin d a) = some ρ' → ρ a = some x → σ a = some ca → x.level = ℓ →
        ca.length = x.parts →
        Trace.StepOK P (profile P) s ρ ρ' σ
          (σ.set d (f ca (keys.take ((layout P).sizes ℓ).length))) (.relin d a) := sorry

/-- **Hybrid key switching (after an automorphism) on Lattigo's digits with one top-level key set
meets the `keySwitch` contract within the Lattigo profile**, at every level, wherever
`instanceOK?` holds. -/
theorem keySwitch_meets (P : FullParams) (h : instanceOK? P = true) (ℓ : ℕ) (h1 : 1 ≤ ℓ)
    (hℓ : ℓ ≤ P.src.qs.length) :
    ∃ f : List (IntPoly P.src.N) → List (IntPoly P.src.N × IntPoly P.src.N) →
        List (IntPoly P.src.N),
      ∀ (s : IntPoly P.src.N), SecretOK P.secretBound s →
      ∀ (ρ ρ' : Env P.src) (σ : Trace.CtEnv P) (d a : Var) (x : Val P.src)
        (ca : List (IntPoly P.src.N)),
        step P.src ρ (.keySwitch d a) = some ρ' → ρ a = some x → σ a = some ca → x.level = ℓ →
        ca.length = x.parts →
      ∀ (keys : List (IntPoly P.src.N × IntPoly P.src.N)),
        Budget.GadgetKeysOK P (layout P) P.src.qs.length (.galois x.key) s keys →
        Trace.StepOK P (profile P) s ρ ρ' σ
          (σ.set d (f ca (keys.take ((layout P).sizes ℓ).length))) (.keySwitch d a) := sorry

/-- **The centred t-corrected modulus switch of `k ≤ 3` components meets the `modSwitch`
contract within the Lattigo profile**, at every level, wherever `instanceOK?` holds. -/
theorem modSwitch_meets (P : FullParams) (h : instanceOK? P = true) (ℓ k : ℕ) (hk1 : 1 ≤ k)
    (hk : k ≤ maxParts) :
    ∃ f : List (IntPoly P.src.N) → List (IntPoly P.src.N),
      ∀ (s : IntPoly P.src.N), SecretOK P.secretBound s →
      ∀ (ρ ρ' : Env P.src) (σ : Trace.CtEnv P) (d a : Var) (x : Val P.src)
        (ca : List (IntPoly P.src.N)),
        step P.src ρ (.modSwitch d a) = some ρ' → ρ a = some x → σ a = some ca → x.level = ℓ →
        x.parts = k → ca.length = k →
        Trace.StepOK P (profile P) s ρ ρ' σ (σ.set d (f ca)) (.modSwitch d a) := sorry

/-! ## 3. Certificates at the profile -/

/-- **Four multiplicative levels are certified at Lattigo's `LogN = 14` example under its
profile, five are not** (worst case over every secret and every run within the profile),
kernel-checked. -/
theorem exampleLogN14_accepts :
    (certifyProfile? exampleLogN14 (profile exampleLogN14) (chain 12 4) false).isSome = true ∧
      certifyProfile? exampleLogN14 (profile exampleLogN14) (chain 12 5) false = none := sorry

/-- **At the small conformance set the whole three-level chain and the recorded program shape
are certified under the profile**, kernel-checked. -/
theorem small_accepts :
    (certifyProfile? small (profile small) (chain 4 3) false).isSome = true ∧
      (certifyProfile? small (profile small) smallProg false).isSome = true := sorry

-- The numbers (compiled): the key-switching budget at `small` (`≈ 2^23.4`) and at
-- `exampleLogN14` (`≈ 2^30`, every level), and the input noise: the larger of the secret-key
-- bound `65536 + 65537·19 = 1310739` and the public-key bound, which is `65536 + 65537·8` at
-- `small` and `65536 + 65537·8192 ≈ 2^29` at `exampleLogN14` (there the rounding by `p₀`
-- dominates).
#guard (profile small).keySwitch == 11452593
#guard Nat.log2 (profile exampleLogN14).keySwitch == 30
#guard small.inputNoise == 1310739 && pkFresh 16 65537 [1073741953] == 589832
#guard exampleLogN14.inputNoise == pkFresh 16384 65537 [0x10000140001]
#guard pkErrMSB 16384 [0x10000140001] == 8192

end Challenge.Instances.Lattigo
