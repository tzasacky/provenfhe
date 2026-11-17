import Spec.Decrypt
import Challenge.Headline.Defs

/-!
# Challenge.Decrypt — decryption with the phase switched to one limb   (LOCKED statements; proofs in `Validation/`)

The noise headline concludes `Encrypts P s B v ct`, which for BGV is exact *textbook* decryption
at the output's level (`Challenge.Trace.encrypts_bgv_decrypts`). OpenFHE's `Decrypt` first
switches the phase down to one limb (`Spec.Decrypt`). These pins say when that changes nothing:

* `decrypt_switched`: if `ct` encrypts `v` with noise at most `B` and `decryptOK?` accepts `B` at
  `v`'s level (the bound `decBound`, about `B / (q₁⋯q_{ℓ-1}) + t/2`, is below `q₀/2`), then the
  switched decryption returns the message times `decScale` (the factor `q_last⁻¹ mod t` of each
  switch, the same factor `Source.step` records for `modSwitch`). Only the final bound matters:
  nothing is assumed about the intermediate levels.
* `outputLevel?_eq`: the level of an output does not depend on the messages, so the tool can
  compute it once.
* `analyze_decrypt_switched`: the two combined with the noise headline for the reference
  analyzer: if `refAnalyze` accepts with `B` and `decryptAllOK?` accepts `B`, every output of
  every run decrypts, *by the switched decryption*, to the scaled message.

The switched phase is one polynomial, so the bound has no secret-dependent term (compare
`Spec.Budget.msBudget`, the budget of switching a two-component ciphertext).
-/

namespace Challenge.Decrypt
open Spec NPoly Scheme Source Correct Spec.Decrypt Challenge.Headline Challenge.Corpus

/-- **Switched decryption is exact under `decryptOK?`.** -/
theorem decrypt_switched (P : FullParams) (hk : P.src.kind = .bgv) (hP : SchemeParamsOK P)
    (s : IntPoly P.src.N) (B : ℕ) (v : Val P.src) (ct : List (IntPoly P.src.N))
    (h : Encrypts P s B v ct) (hok : decryptOK? P.src v.level B = true) :
    ∃ m, v.msg = .exact m ∧
      bgvDecryptSwitched P.src.t (P.src.qs.take v.level) (automorph v.key s)
          (ct.map (ofInt (P.src.qs.take v.level).prod)) =
        decScale P.src v.level • m := sorry

/-- With one limb the switched decryption is the textbook one. -/
theorem bgvDecryptSwitched_one (t q : ℕ) {N : ℕ} (s : IntPoly N) (ct : List (Poly [q].prod N)) :
    bgvDecryptSwitched t [q] s ct = ofInt t (centeredPhase s ct) := sorry

/-- Each round of `decBoundRev` is at most `⌊B/q⌋ + ⌈t/2⌉`: never worse than `refBound`'s rule
for a `modSwitch` of a one-component value at the budget `Spec.Budget.msBudgetOne`. -/
theorem decBoundRev_step_le (t q B : ℕ) (hq : 0 < q) :
    (B + t * (q / 2)) / q ≤ B / q + (t + 1) / 2 := sorry

/-- The level of an output is the same for all messages. -/
theorem outputLevel?_eq (P : Params) (hk : P.kind = .bgv) (prog : Program)
    (msgs : Var → Msg P.t P.N) (ρ : Env P) (h : eval P prog msgs = some ρ) (o : Var) (v : Val P)
    (ho : ρ o = some v) : outputLevel? P prog o = some v.level := sorry

/-- **The noise headline with the library's decryption.** If the reference analysis accepts with
`B` and `decryptAllOK?` accepts `B` (computed checks), then for every secret, all messages and all
input ciphertexts within their bounds, at the end of every run meeting the contracts, each output
decrypts *by the switched decryption* to the message `Source.eval` computes, times `decScale` at
the output's level. -/
theorem analyze_decrypt_switched (P : FullParams) (E : Trace.Budget) (prog : Program) (B : ℕ)
    (hP : SchemeParamsOK P) (hk : P.src.kind = .bgv) (h : refAnalyze P E prog = some B)
    (hd : decryptAllOK? P.src prog B = true)
    (s : IntPoly P.src.N) (msgs : Var → Msg P.src.t P.src.N)
    (cts : Var → List (IntPoly P.src.N)) (hin : InputsOK P s prog msgs cts)
    (hb : Trace.BoundsOK P s prog msgs cts) :
    ∃ ρ, Source.eval P.src prog msgs = some ρ ∧
      ∀ σ, Trace.Run P E s prog.body (initEnv P.src prog msgs) (Trace.initCt P prog cts) σ →
        ∀ o ∈ prog.outputs, ∃ v ct m, ρ o = some v ∧ σ o = some ct ∧ v.msg = .exact m ∧
          bgvDecryptSwitched P.src.t (P.src.qs.take v.level) (automorph v.key s)
              (ct.map (ofInt (P.src.qs.take v.level).prod)) =
            decScale P.src v.level • m := sorry

/-! ## Guards (`tinyBGV`: `N = 4`, `t = 17`, `q₀ = 65537`, `q₁ = 786433`) -/

-- One limb: nothing to switch. Two limbs: `⌊(B + 17·393216) / 786433⌋`.
#guard decBound FullParams.tinyBGV.src 1 1000 == 1000
#guard decBound FullParams.tinyBGV.src 2 1000 == 8
#guard decBound FullParams.tinyBGV.src 2 0 == 8
#guard decBound FullParams.tinyBGV.src 2 (2 ^ 34) == 21853
#guard decryptOK? FullParams.tinyBGV.src 2 (2 ^ 34)
-- A phase bound that fits `Q/2 ≈ 2^34.6` at level 2 but whose switched bound exceeds `q₀/2`.
#guard 2 * 25700000000 < 65537 * 786433
#guard decryptOK? FullParams.tinyBGV.src 2 25700000000
#guard !decryptOK? FullParams.tinyBGV.src 2 25765000000
#guard 2 * 25765000000 < 65537 * 786433
-- The scale at level 2 is `q₁⁻¹ mod 17`; at level 1 it is 1.
#guard (decScale FullParams.tinyBGV.src 1).val == 1
#guard ((decScale FullParams.tinyBGV.src 2).val * 786433) % 17 == 1
-- A concrete switched decryption: the 1-component "ciphertext" `[c]` with `c = m + 17·e`,
-- `m = (3, 0, 16, 5)`, decrypts to `q₁⁻¹ · m`.
#guard (bgvDecryptSwitched 17 [65537, 786433] (0 : IntPoly 4)
    [ofInt _ ⟨![3 + 17 * 1000, 17 * (-70000), 16 + 17 * 5, 5 - 17 * 123456]⟩]).coeff ==
  (((786433 : ZMod 17)⁻¹) • (⟨![3, 0, 16, 5]⟩ : Poly 17 4)).coeff
-- and the textbook decryption of the same value at level 2 gives `m` itself.
#guard (bgvDecrypt 17 (0 : IntPoly 4)
    [(ofInt (65537 * 786433) ⟨![3 + 17 * 1000, 17 * (-70000), 16 + 17 * 5, 5 - 17 * 123456]⟩ :
      Poly (65537 * 786433) 4)]).coeff == (⟨![3, 0, 16, 5]⟩ : Poly 17 4).coeff
#guard outputLevel? FullParams.tinyBGV.src
  { inputs := [⟨"a", 2, 2, 1, 1⟩], body := [.modSwitch "c" "a"], outputs := ["c"] } "c" == some 1
#guard decryptAllOK? FullParams.tinyBGV.src
  { inputs := [⟨"a", 2, 2, 1, 1⟩], body := [.copy "c" "a"], outputs := ["c"] } 64
#guard !decryptAllOK? FullParams.tinyBGV.src
  { inputs := [⟨"a", 2, 2, 1, 1⟩], body := [.copy "c" "a"], outputs := ["nope"] } 64

end Challenge.Decrypt
