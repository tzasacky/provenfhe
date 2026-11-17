import Spec.Scaling
import Challenge.Certify

/-!
# Challenge.Scaling — what the user reads after decoding   (LOCKED; proofs in `Validation/`)

`Challenge.Certify.certify?_sound` is about the message a ciphertext *holds*: the switched
decryption of an output returns `decScale •` the message `Source.eval` computes, and that message
carries a factor `q_last⁻¹` per `modSwitch` and `c` per `mulConst c`. OpenFHE's user reads that
polynomial divided by the factor `Decrypt` hands to `Decode` (`Spec.Scaling`, module docstring,
with the OpenFHE v1.6.1 lines). The statements here connect the two.

* `eval_scaled` (**the algebraic invariant**): if the factors of the program exist
  (`Spec.Scaling.factors?`), then `Source.eval` on the scaled input messages (`scaledMsgs`: the
  user's message of each input times its declared factor) gives every variable the message
  `phi • (plain message)`, at the level the factor computation tracks.
* `certify?_user` (**the user-level headline**): if `certify?` accepts, the library performs the
  switched decryption (`x.switched`), and the scale check `scaleOK?` passes, then for every
  secret, every user message `u` and all inputs as in `certify?_sound` (the stored input messages
  are `factor • u`), every output of every run is decrypted *and decoded* (`userDecrypt`, with the
  decode factor `decodeAt?`) to the plain semantics of the program on `u` (`plainEval`).
  It is derived from `Challenge.Certify.certify?_sound` and `eval_scaled`.
* `certify?_src`: the scheme parameters analysed are the declared ones (`c.params.src =
  x.P.src`), so the scale check can be run at `x.P.src`.

**What remains assumed** (hypotheses of the statements, or the meaning of their data, not
checked by anything here): that OpenFHE's `scalingFactorInt` follows the rules of
`Spec.Scaling.facStep` (so that `decodeAt?` is the factor `Decrypt` hands to `Decode`); that the
marks are exactly OpenFHE's scale adjustments; that the declared input factors are the factors
the encoder applied (`ScaleData.factors`); and everything `certify?_sound` assumes. The frontend
compares the factor it computes with OpenFHE's recorded `scalingFactorInt` per ciphertext
(`harness/frontend/openfhe/extract.py`, `replay`), which is evidence for the first, not proof.

**Discrimination** (`#guard`s and closed pins at `tinyBGV`, `t = 17`, `65537 ≡ 2`,
`786433 ≡ 13 (mod 17)`, `13⁻¹ ≡ 4`):
* the accepted example `adjProg` (a product switched down, plus an adjusted and switched copy of
  an input, added) has output factor 13, not 1: the switched decryption alone returns
  `13 •` the plain result, which differs from it whenever the plain result is not `0`
  (`adjProg_raw_ne_plain`): without the decode factor, "decrypts to the plain result" is false;
* an addition of operands with different true factors is rejected (`addMismatchProg`);
* a plaintext product with a plaintext whose factor differs from the ciphertext's is rejected:
  OpenFHE's tracked factor (`λ²`, `bgvrns-leveledshe.cpp:246`) is then not the true one
  (`mulPlainProg`);
* without tracking (`FIXED*`) a `modSwitch` by a prime `≢ 1 (mod t)` is rejected (`tinyBGV`'s
  primes are not `≡ 1 mod 17`; OpenFHE's `FIXED*` primes are), and accepted with tracking;
* a factor that is not a unit modulo `t` is rejected.
-/

namespace Challenge.Scaling
open Spec NPoly Scheme Source Correct Spec.Scaling Spec.Decrypt Spec.Certify Spec.Budget
open Challenge.Certify

/-! ## The invariant and the headline -/

/-- **The algebraic invariant.** If the factors of the program exist, then on the scaled input
messages every variable `Source.eval` defines holds `phi •` its plain message, at the tracked
level. -/
theorem eval_scaled (P : Params) (prog : Program) (sd : ScaleData) (F : Var → Option (Fac P.t))
    (hF : factors? P prog sd = some F) (u : Var → Poly P.t P.N) (ρ : Env P)
    (hρ : eval P prog (scaledMsgs P sd u) = some ρ) (y : Var) (v : Val P) (hy : ρ y = some v) :
    ∃ x, F y = some x ∧ v.msg = .exact (x.phi • plainEval prog sd.marks u y) ∧
      v.level = x.level := sorry

/-- The scheme parameters analysed are the declared ones (only the input noise may differ). -/
theorem certify?_src (x : Input) (c : Certificate) (h : certify? x = some c) :
    c.params.src = x.P.src := sorry

/-- **The user-level headline.** If `certify?` accepts, the switched decryption is the library's
(`x.switched`), and `scaleOK?` passes for the scaling data `sd`, then for every secret `s`, every
user message `u` of each variable, and all input ciphertexts that hold the scaled messages
`factor • u` as in `certify?_sound` (noise at most the analysed input noise, declared bounds),
every output `o` of every run at the budget `c.budget` is a ciphertext `ct` whose decryption and
decoding by the library (`userDecrypt` with the decode factor and level of `decodeAt?`) is the
plain semantics of the program on `u`. -/
theorem certify?_user (x : Input) (c : Certificate) (h : certify? x = some c)
    (hsw : x.switched = true) (sd : ScaleData) (hsc : scaleOK? c.params.src x.prog sd = true)
    (s : IntPoly c.params.src.N) (u : Var → Poly c.params.src.t c.params.src.N)
    (cts : Var → List (IntPoly c.params.src.N))
    (hin : InputsOK c.params s x.prog (scaledMsgs c.params.src sd u) cts)
    (hb : Trace.BoundsOK c.params s x.prog (scaledMsgs c.params.src sd u) cts) :
    ∀ σ, Trace.Run c.params c.budget s x.prog.body
        (initEnv c.params.src x.prog (scaledMsgs c.params.src sd u))
        (Trace.initCt c.params x.prog cts) σ →
      ∀ o ∈ x.prog.outputs, ∃ ct dF ℓ, σ o = some ct ∧
        decodeAt? c.params.src x.prog sd o = some (dF, ℓ) ∧
        userDecrypt c.params.src dF ℓ s ct = plainEval x.prog sd.marks u o := sorry

/-! ## Examples at `tinyBGV` -/

/-- A product switched down to level 1, plus a copy of `a` adjusted by `13` and switched down
(OpenFHE's `AdjustLevelsAndDepthInPlace` does this to bring `a` to the level and factor of the
product: `13 · 13 · 13⁻¹ = 13 · 13 · 4 ≡ 13`), added. Plain result: `a·b + a`. -/
def adjProg : Program :=
  { inputs := [⟨"a", 2, 2, 1, 1⟩, ⟨"b", 2, 2, 1, 1⟩],
    body := [.mul "c" "a" "b", .modSwitch "c" "c", .mulConst "e" "a" 13, .modSwitch "e" "e",
             .add "o" "c" "e"],
    outputs := ["o"] }

/-- Both inputs with factor `13 ≡ 786433 (mod 17)` (OpenFHE's `FLEXIBLEAUTO` factor at the top
level is the last prime mod `t`); the `mulConst` is an adjustment; factors tracked. -/
def adjSD : ScaleData := ⟨[("a", 13), ("b", 13)], [false, false, true, false, false], true⟩

/-- Adding a product (factor `13² ≡ 16`) to an input (factor 13) without adjusting. -/
def addMismatchProg : Program :=
  { inputs := [⟨"a", 2, 2, 1, 1⟩, ⟨"b", 2, 2, 1, 1⟩],
    body := [.mul "c" "a" "b", .add "o" "c" "a"], outputs := ["o"] }

/-- A ciphertext times a plaintext operand (stored representative in `[0, t)`). -/
def mulPlainProg : Program :=
  { inputs := [⟨"a", 2, 2, 1, 1⟩, ⟨"p", 1, 2, 1, 1⟩],
    body := [.mulPlain "o" "a" "p"], outputs := ["o"], bounds := [("p", 16)] }

/-- One input, copied. -/
def copyProg : Program :=
  { inputs := [⟨"a", 2, 2, 1, 1⟩], body := [.copy "o" "a"], outputs := ["o"] }

/-- The decode factor of an output, as a number. -/
def decodeNat (P : Params) (prog : Program) (sd : ScaleData) (o : Var) : Option (ℕ × ℕ) :=
  (decodeAt? P prog sd o).map fun (d, ℓ) => (d.val, ℓ)

-- ACCEPTED (non-vacuity): certified, and the scale check passes, with output factor 13 at level 1.
#guard (certify? (tinyInput adjProg true .worstCase)).map (·.outputs) == some [("o", 222)]
#guard scaleOK? Spec.FullParams.tinyBGV.src adjProg adjSD
#guard decodeNat Spec.FullParams.tinyBGV.src adjProg adjSD "o" == some (13, 1)
-- The marks matter for the library's factor only: unmarked, the `mulConst` multiplies the plain
-- result instead (`a·b + 13a`), and the true factor is unchanged, so the true factors of the
-- addition differ (`13` vs `13 · 4 ≡ 1`) and the program is rejected.
#guard !scaleOK? Spec.FullParams.tinyBGV.src adjProg { adjSD with marks := [] }
-- REJECTED: operands of an addition with different factors (both certified for noise).
#guard (certify? (tinyInput addMismatchProg true .worstCase)).isSome
#guard !scaleOK? Spec.FullParams.tinyBGV.src addMismatchProg ⟨[("a", 13), ("b", 13)], [], true⟩
-- PLAINTEXT PRODUCT: OpenFHE sets the factor to the square of the ciphertext's. Accepted when
-- the plaintext has the ciphertext's factor (`13 · 13`), rejected when it has another (`13 · 2`
-- is the true factor, `13²` OpenFHE's).
#guard (certify? (tinyInput mulPlainProg true .worstCase)).isSome
#guard scaleOK? Spec.FullParams.tinyBGV.src mulPlainProg ⟨[("a", 13), ("p", 13)], [], true⟩
#guard !scaleOK? Spec.FullParams.tinyBGV.src mulPlainProg ⟨[("a", 13), ("p", 2)], [], true⟩
-- NO TRACKING: a modulus switch by `786433 ≢ 1 (mod 17)` leaves the true factor 4 while the
-- untracked factor stays 1: rejected. With tracking: accepted, factor 4.
#guard (certify? (tinyInput Challenge.Headline.mulSwitchProg true .worstCase)).isSome
#guard !scaleOK? Spec.FullParams.tinyBGV.src Challenge.Headline.mulSwitchProg
  ⟨[("a", 1), ("b", 1)], [], false⟩
#guard decodeNat Spec.FullParams.tinyBGV.src Challenge.Headline.mulSwitchProg
  ⟨[("a", 1), ("b", 1)], [], true⟩ "c" == some (4, 1)
-- NON-UNIT: a factor `≡ 0 (mod 17)` is rejected (the decode factor is not invertible); a
-- missing input factor is rejected.
#guard !scaleOK? Spec.FullParams.tinyBGV.src copyProg ⟨[("a", 17)], [], true⟩
#guard scaleOK? Spec.FullParams.tinyBGV.src copyProg ⟨[("a", 5)], [], true⟩
#guard !scaleOK? Spec.FullParams.tinyBGV.src copyProg ⟨[], [], true⟩

/-! ## Closed pins (kernel evaluation) and the discrimination of the raw decryption -/

/-- `adjProg` is certified, passes the scale check, and its output's decode factor is 13 at
level 1. -/
theorem adjProg_accepted :
    (certify? (tinyInput adjProg true .worstCase)).isSome = true ∧
    scaleOK? Spec.FullParams.tinyBGV.src adjProg adjSD = true ∧
    decodeNat Spec.FullParams.tinyBGV.src adjProg adjSD "o" = some (13, 1) := sorry

/-- Operands with different factors are rejected. -/
theorem addMismatch_rejected :
    scaleOK? Spec.FullParams.tinyBGV.src addMismatchProg ⟨[("a", 13), ("b", 13)], [], true⟩ =
      false := sorry

/-- A plaintext product whose plaintext factor differs from the ciphertext's is rejected (the
library's factor `13²` is not the true `13 · 2`). -/
theorem mulPlain_factor_rejected :
    scaleOK? Spec.FullParams.tinyBGV.src mulPlainProg ⟨[("a", 13), ("p", 2)], [], true⟩ =
      false := sorry

/-- Without tracking, a switch by a prime `≢ 1 (mod t)` is rejected. -/
theorem untracked_switch_rejected :
    scaleOK? Spec.FullParams.tinyBGV.src Challenge.Headline.mulSwitchProg
      ⟨[("a", 1), ("b", 1)], [], false⟩ = false := sorry

/-- A factor that is not a unit modulo `t` is rejected. -/
theorem nonUnit_rejected :
    scaleOK? Spec.FullParams.tinyBGV.src copyProg ⟨[("a", 17)], [], true⟩ = false := sorry

/-- **The factor is not cosmetic.** For `adjProg` at `tinyBGV`, every run from inputs as in
`certify?_user` ends with an output ciphertext whose user-level decryption is the plain result,
while its switched decryption alone (what `certify?_sound` is about, read as the user's value)
differs from the plain result whenever that is not `0`. -/
theorem adjProg_raw_ne_plain (s : IntPoly Spec.FullParams.tinyBGV.src.N)
    (u : Var → Poly Spec.FullParams.tinyBGV.src.t Spec.FullParams.tinyBGV.src.N)
    (cts : Var → List (IntPoly Spec.FullParams.tinyBGV.src.N))
    (hin : InputsOK Spec.FullParams.tinyBGV s adjProg
      (scaledMsgs Spec.FullParams.tinyBGV.src adjSD u) cts)
    (hb : Trace.BoundsOK Spec.FullParams.tinyBGV s adjProg
      (scaledMsgs Spec.FullParams.tinyBGV.src adjSD u) cts)
    (σ : Trace.CtEnv Spec.FullParams.tinyBGV)
    (hσ : Trace.Run Spec.FullParams.tinyBGV
      (certified Spec.FullParams.tinyBGV (uniformLayout 1)) s adjProg.body
      (initEnv Spec.FullParams.tinyBGV.src adjProg (scaledMsgs Spec.FullParams.tinyBGV.src adjSD u))
      (Trace.initCt Spec.FullParams.tinyBGV adjProg cts) σ)
    (hne : plainEval adjProg adjSD.marks u "o" ≠ 0) :
    ∃ ct, σ "o" = some ct ∧
      userDecrypt Spec.FullParams.tinyBGV.src 13 1 s ct = plainEval adjProg adjSD.marks u "o" ∧
      bgvDecryptSwitched Spec.FullParams.tinyBGV.src.t (Spec.FullParams.tinyBGV.src.qs.take 1) s
          (ct.map (ofInt (Spec.FullParams.tinyBGV.src.qs.take 1).prod)) ≠
        plainEval adjProg adjSD.marks u "o" := sorry

end Challenge.Scaling
