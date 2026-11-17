import Challenge.IndCpaD.Defs
import Challenge.BFVEncrypt
import Mathlib.MeasureTheory.Measure.Basic

/-!
# Challenge.IndCpaD — IND-CPA-D reduces to IND-CPA on the certified class   (LOCKED statements; proofs in `Validation/IndCpaD.lean`)

The games, the reduction and the class are in `Spec.IndCpaD` (abstract) and
`Challenge.IndCpaD.Defs` (BFV); their docstrings say what is and is not modelled.

1. **Perfect simulation** (`gameD_eq_gameCPA`): for a scheme that is perfectly correct on its
   declared class (`Spec.IndCpaD.Correct`), on every tape on which the keys and every encryption
   the run performs are good, the IND-CPA-D game and the IND-CPA game played by the reduction
   return the same bit. The reduction (`Spec.IndCpaD.reduce`) takes the public key and the
   adversary, and nothing secret.
2. **Probabilities** (`prob_eq`, `prob_le`): under any measure on the joint randomness (keys,
   encryption randomness, adversary's coins), equal winning probabilities for each bit when the
   keys and all encryptions are good almost surely; for an adversary making at most `q`
   encryption queries, the two winning probabilities differ by at most the probability of the
   explicit bad event "the keys or one of the first `q` encryptions are not good". Each holds for
   each bit, in both directions; the advantage bound
   `Adv^{IND-CPA-D}(A) ≤ Adv^{IND-CPA}(reduction A) + 2·Pr[bad]` follows by the triangle
   inequality and is not stated as a separate theorem.
3. **BFV** (`correct`): `scheme St` (OpenFHE's encryption, the library transcription
   `runLibrary` as evaluator, textbook decryption, the class of circuits `certifyBFVFresh?`
   accepts in the worst-case mode plus the checks `extraOK`) is perfectly correct on its class,
   given that a fresh encryption decrypts in the setting (`freshDecOK`, a closed check) and the
   binary64 arithmetic of the setting conforms to the standard model (`Spec.Float.Conforms`).
   `bfv_prob_eq`, `bfv_prob_le`: the statements of 2 for BFV, every hypothesis visible.
4. **Non-vacuity**: good keys exist for every secret within the bound (`keysOK_exist`); a
   circuit at `tinyBFV` is in the class (`admissible_tiny`, kernel-checked); and a product, a
   relinearization, a rotation and a plaintext addition at `sealBFV` (`N = 2¹³`, four limbs of
   43–44 bits, `t = 65537`, one special prime, HPS multiplication with its binary64 tolerance) is
   in the class (`#guard`, compiled evaluation).

**What is assumed, not proved.** That BFV with the relinearization and rotation keys in the
public key is IND-CPA (a circular-security assumption included); that the keys and the
encryption randomness are within the sampler bounds (a hypothesis or the bad event); that the
platform's binary64 arithmetic conforms (`Spec.Float.Conforms`); that the circuit's declared
drops are those the library would choose; key generation. The decryption oracle returns the
textbook decryption: an application that reveals a library's raw decryption output (which can
depend on the noise) is outside these statements. No statement here is about OpenFHE's security.
-/

namespace Challenge.IndCpaD
open Spec.IndCpaD Spec.IndCpaDBFV MeasureTheory

/-! ## 1–2. The abstract reduction -/

/-- **Perfect simulation.** On every tape on which the keys are good and every encryption the
run of `A` performs is good, the IND-CPA-D game with bit `b` and the IND-CPA game with bit `b`
played by the reduction from `A` return the same bit. -/
theorem gameD_eq_gameCPA (S : HEScheme) [DecidableEq S.M] (hC : Correct S) (b : Bool)
    (pk : S.PK) (sk : S.SK) (tape : ℕ → S.ER) (hk : S.KeysOK pk sk) (A : Adv S Bool)
    (ht : TapeOK pk sk tape A 0) :
    gameD b pk sk tape A 0 [] = gameCPA b pk tape (reduce pk A []) 0 := sorry

/-- **Equal winning probabilities** for each bit (hence equal advantages), under any measure on
the joint randomness for which the keys and every encryption are good almost surely. -/
theorem prob_eq (S : HEScheme) [DecidableEq S.M] (hC : Correct S)
    {Ω Coins : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    (pk : Ω → S.PK) (sk : Ω → S.SK) (tape : Ω → ℕ → S.ER) (coins : Ω → Coins)
    (A : Coins → S.PK → Adv S Bool) (b : Bool)
    (hgood : ∀ᵐ ω ∂μ, S.KeysOK (pk ω) (sk ω) ∧ ∀ i, S.GoodE (pk ω) (sk ω) (tape ω i)) :
    μ {ω | gameD b (pk ω) (sk ω) (tape ω) (A (coins ω) (pk ω)) 0 [] = true} =
      μ {ω | gameCPA b (pk ω) (tape ω) (reduction A (coins ω) (pk ω)) 0 = true} := sorry

/-- **The bad-event version.** For an adversary making at most `q` encryption queries on every
path, under any measure, the two winning probabilities (for each bit) differ by at most the
probability that the keys or one of the first `q` encryptions are not good. -/
theorem prob_le (S : HEScheme) [DecidableEq S.M] (hC : Correct S)
    {Ω Coins : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    (pk : Ω → S.PK) (sk : Ω → S.SK) (tape : Ω → ℕ → S.ER) (coins : Ω → Coins)
    (A : Coins → S.PK → Adv S Bool) (b : Bool) (q : ℕ) (hq : ∀ r p, Bounded (A r p) q) :
    μ {ω | gameD b (pk ω) (sk ω) (tape ω) (A (coins ω) (pk ω)) 0 [] = true} ≤
        μ {ω | gameCPA b (pk ω) (tape ω) (reduction A (coins ω) (pk ω)) 0 = true} +
          μ {ω | ¬ (S.KeysOK (pk ω) (sk ω) ∧ ∀ i < q, S.GoodE (pk ω) (sk ω) (tape ω i))} ∧
      μ {ω | gameCPA b (pk ω) (tape ω) (reduction A (coins ω) (pk ω)) 0 = true} ≤
        μ {ω | gameD b (pk ω) (sk ω) (tape ω) (A (coins ω) (pk ω)) 0 [] = true} +
          μ {ω | ¬ (S.KeysOK (pk ω) (sk ω) ∧ ∀ i < q, S.GoodE (pk ω) (sk ω) (tape ω i))} := sorry

/-! ## 3. BFV -/

open Spec Spec.Scheme Spec.EncryptBFV

/-- **BFV is perfectly correct on the certified class**: for good keys and good encryption
randomness, every fresh encryption decrypts to its message, and the textbook decryptions of the
library transcription's outputs on fresh encryptions of `ms` are what the program computes on
`ms` and the circuit's constants. Hypotheses: a fresh encryption decrypts in the setting
(`freshDecOK`), and the setting's binary64 arithmetic conforms to the standard model. -/
theorem correct (St : Setting) (hSt : freshDecOK St = true) (hA : Spec.Float.Conforms St.A) :
    Correct (scheme St) := sorry

/-- **BFV: equal winning probabilities** for each bit, under any measure on the joint
randomness for which the keys are good (`KeysOK`: the secret within `secretBound`, the public
key's error within `Bk`, the relinearization keys and the rotation keys at `St.rots` valid with
error within `St.base.P.keyNoise`) and
every encryption's randomness is within `Bu`, `B1`, `B2` (`GoodE`), almost surely. -/
theorem bfv_prob_eq (St : Setting) (hSt : freshDecOK St = true) (hA : Spec.Float.Conforms St.A)
    {Ω Coins : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    (pk : Ω → PK (St := St)) (sk : Ω → SK (St := St)) (tape : Ω → ℕ → ER (St := St))
    (coins : Ω → Coins) (A : Coins → PK (St := St) → Adv (scheme St) Bool) (b : Bool)
    (hgood : ∀ᵐ ω ∂μ, KeysOK (pk ω) (sk ω) ∧ ∀ i, GoodE (pk ω) (sk ω) (tape ω i)) :
    μ {ω | gameD (S := scheme St) b (pk ω) (sk ω) (tape ω) (A (coins ω) (pk ω)) 0 [] = true} =
      μ {ω | gameCPA (S := scheme St) b (pk ω) (tape ω)
        (reduction (S := scheme St) A (coins ω) (pk ω)) 0 = true} := sorry

/-- **BFV: the bad-event version**, for an adversary making at most `q` encryption queries. -/
theorem bfv_prob_le (St : Setting) (hSt : freshDecOK St = true) (hA : Spec.Float.Conforms St.A)
    {Ω Coins : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    (pk : Ω → PK (St := St)) (sk : Ω → SK (St := St)) (tape : Ω → ℕ → ER (St := St))
    (coins : Ω → Coins) (A : Coins → PK (St := St) → Adv (scheme St) Bool) (b : Bool) (q : ℕ)
    (hq : ∀ r p, Bounded (A r p) q) :
    μ {ω | gameD (S := scheme St) b (pk ω) (sk ω) (tape ω) (A (coins ω) (pk ω)) 0 [] = true} ≤
        μ {ω | gameCPA (S := scheme St) b (pk ω) (tape ω)
          (reduction (S := scheme St) A (coins ω) (pk ω)) 0 = true} +
          μ {ω | ¬ (KeysOK (pk ω) (sk ω) ∧ ∀ i < q, GoodE (pk ω) (sk ω) (tape ω i))} ∧
      μ {ω | gameCPA (S := scheme St) b (pk ω) (tape ω)
          (reduction (S := scheme St) A (coins ω) (pk ω)) 0 = true} ≤
        μ {ω | gameD (S := scheme St) b (pk ω) (sk ω) (tape ω) (A (coins ω) (pk ω)) 0 [] = true} +
          μ {ω | ¬ (KeysOK (pk ω) (sk ω) ∧ ∀ i < q, GoodE (pk ω) (sk ω) (tape ω i))} := sorry

/-! ## 4. Non-vacuity -/

/-- **Good keys exist** for every secret within the bound (the noiseless ones), when `N` is a
power of two and every index of `St.rots` is odd. -/
theorem keysOK_exist (St : Setting) (hN : ∃ k, St.base.P.src.N = 2 ^ k)
    (hodd : ∀ g ∈ St.rots, g % 2 = 1) (s : IntPoly St.base.P.src.N)
    (hs : SecretOK St.base.P.secretBound s) :
    ∃ (pk : PK (St := St)) (e : IntPoly St.base.P.src.N), KeysOK pk ⟨s, e⟩ := sorry

open Challenge.BFV Challenge.CertifyBFV Challenge.BFVEncrypt

/-- `tinyBFV` (`N = 4`, `t = 17`, two limbs), textbook multiplication, sampler bounds 2, 1, 2,
2, no rotation keys. -/
def tinySetting : Setting := ⟨tinyFresh 0, 2, 1, 2, 2, Spec.Float.exact, []⟩

/-- The product of two fresh inputs, relinearized. -/
def tinyCirc : Circ tinySetting := ⟨mulProg, [], ["a", "b"], fun _ => 0⟩

/-- **The class is not empty**, and a fresh encryption decrypts, at `tinyBFV`. -/
theorem admissible_tiny : freshDecOK tinySetting = true ∧ admissible tinyCirc = true := sorry

/-- `sealBFV` with HYBRID key switching (canonical digits, one limb each), HPS multiplication
with its binary64 tolerance, plaintext addition by `⌈Q·p/t⌉` (`.scaled`, OpenFHE's `TimesQovert`),
every error bound 41 (public-key error, encryption errors, and `keyNoise` for the
relinearization and rotation keys) and 1 (ternary `u`), rotation keys for `g = 5`. -/
def sealSetting : Setting :=
  ⟨⟨{ sealBFV with keyNoise := 41 }, { Budget.uniformLayout 1 with canonical := true },
    Source.Program.mk [] [] [] [],
    some (.hps [1152921504606584833, 1152921504598720513, 1152921504597016577,
      1152921504595968001, 1152921504592822273]), true, some .scaled, true, []⟩,
    41, 1, 41, 41, Spec.Float.exact, [5]⟩

/-- Two fresh inputs and a plaintext constant at the top level; a product, its relinearization,
a rotation by `g = 5` (an automorphism followed by the key switch back to `s`) and a plaintext
addition. -/
def sealCirc : Circ sealSetting :=
  ⟨{ inputs := [⟨"a", 2, 4, 1, 1⟩, ⟨"b", 2, 4, 1, 1⟩, ⟨"p", 1, 4, 1, 1⟩],
     body := [.mul "c" "a" "b", .relin "c" "c", .automorph "r" "c" 5, .keySwitch "k" "r",
       .addPlain "o" "k" "p"],
     outputs := ["o"] }, [], ["a", "b"], fun _ => 0⟩

#guard freshDecOK sealSetting && admissible sealCirc
-- Without the rotation key for 5 in the public key, the same circuit is outside the class.
#guard !admissible (St := { sealSetting with rots := [] }) ⟨sealCirc.prog, [], ["a", "b"], fun _ => 0⟩
-- With the idealised budget (no binary64 tolerance) the certificate records `idealised`.
#guard !admissible (St := { sealSetting with base := { sealSetting.base with floatTol := false } })
  ⟨sealCirc.prog, [], ["a", "b"], fun _ => 0⟩

end Challenge.IndCpaD
