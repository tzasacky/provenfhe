import Challenge.Certify.Defs
import Challenge.Budget
import Challenge.BudgetRestrict
import Challenge.Decrypt
import Challenge.FreshNoise
import Challenge.FreshNoiseL2

/-!
# Challenge.Certify — what a certificate of `certify?` means   (LOCKED statements; proofs in `Validation/`)

`Challenge.Certify.certify?` (`Challenge/Certify/Defs.lean`) is the one function that decides whether `fhe_check` prints
"certified". Every statement here has the form `certify? x = some c → …`: the hypotheses of the
underlying pins (`Challenge.Budget`, `Challenge.FreshNoise`, `Challenge.Decrypt`) are discharged
from the computation of `certify?` in the proofs, not by the tool.

* `certify?_spec`, `certify?_worstCase`, `certify?_fresh`: what the fields of the certificate
  are, and that every check was made at `c.params`, the parameters analysed.
* `certify?_paramsOK`, `certify?_keys_restrict`, `certified_run_exists`, `fresh_run_exists`,
  `fresh_l2_run_exists`: the propositions the checks decide hold (`SchemeParamsOK`, BGV,
  `SpecialOK`, the layout usable at every level and restricting from the top level, the key-size
  condition), and so there **is** a run at the certified budget: from every input within the
  analysed noise for a secret within `secretBound` (`certified_run_exists`), and in the fresh
  modes on the event that every fresh error is at most `c.eps` (`fresh_run_exists`,
  `fresh_l2_run_exists`). The "every run" of the statements below is about at least one run in
  those cases (non-vacuity only; see "For which secrets" below for what this does not show).
* `certify?_sound`, `certify?_decrypts`: **the headline statements**, named as BFV's
  `Challenge.CertifyBFV.certifyBFV?_sound` and `certifyBFV?_decrypts`: every output of every run
  decrypts with the secret key (and has noise at most its own bound in the certificate): all
  outputs at once. `certify?_sound` is `certified_sound` under the headline name (the older name
  is kept: earlier documents cite it); `worst_certified` is the same in the worst-case mode,
  written at the declared parameters, and is what `fhe_check` cites for a worst-case verdict
  (with `Challenge.Budget.certified_sound`, the analyzer's bound at the certified budget).
* `fresh_kappa_certified`, `fresh_kappa_decrypts`: the fresh-encryption mode: the probability
  that **some** output of some run, for some messages, fails is at most `2^(−κ)`: one event for
  all outputs, with each output held to its own bound. `fresh_worst_certified`: when `certify?`
  used the worst case of the fresh error, the same with no probability.
* `certify?_freshL2`, `fresh_l2_certified`, `fresh_l2_decrypts`, `fresh_l2_run_exists`: the
  fresh-encryption mode described in `ℓ₂` (`Challenge.FreshNoiseL2`): the same joint statement at
  `2^(−κ)`, with the bounds `E2`, `S2` on the squared `ℓ₂` norms of the public-key error and the
  secret, and the sub-Gaussian proxies `Vu`, `V1`, `V2` of the samplers, as explicit hypotheses.

**Why the per-output accounting costs nothing in probability.** `certify?` analyses each output
as a one-output program, with its own bound (step 6 in `Challenge.Certify.Defs`); an output at a
low level is then not held to the noise of an output at a high level. The pin
`Challenge.FreshNoise.fresh_kappa_decrypts` is about one program and one bound; applied once per
output it would give `(number of outputs) · 2^(−κ)` for all outputs together. Here the statement
is about all outputs with failure probability `2^(−κ)`: every output fails only on the one event
"the error of some fresh encryption exceeds `c.eps`", and runs (`Spec.Trace.Run`) do not depend
on which variables are outputs.

**"Noise" includes the message.** Every bound here is a bound on the centred phase `m + t·e` of
a BGV ciphertext (`Spec.Scheme.BGVEncrypts`), not on the error `e`.

**"Decrypts" means: to the message `Source.eval` computes.** That message is the one the
ciphertext holds: `Source.step` multiplies it by `q_last⁻¹ mod t` at every `modSwitch`, and the
library's switched decryption returns it times `Spec.Decrypt.decScale`. These factors are in the
statements (`OutputsCertified`), not hidden. What a library's user reads after decoding, with the
library's own bookkeeping of the factor, is a separate matter: see `Challenge.Scaling`.

**For which secrets.** `certify?_sound`, `certified_sound` and `worst_certified` hold for
*every* integer polynomial `s`: they take no `SecretOK` hypothesis. This is weaker than it may
sound. The statements are about the runs within the budget `c.budget`, and the budget (the
key-switching and modulus-switching bounds of `Spec.Budget`) is computed from `secretBound`: for
a secret outside it nothing says that any algorithm stays within the budget, and the statements
may be about no run at all. `certified_run_exists` shows only that the set of runs is nonempty: the
contracts of `Spec.Trace.StepOK` constrain only the phase and the length of a result, whose
components are otherwise free, so a run exists at any budget (a key-switching error can be taken
zero; a modulus switch asks only for the correction of one switch), and this is not evidence that
the budget is achievable. That evidence is the realizability statements of `Challenge.Budget`
(`relin_realizable`, `keySwitch_realizable`, `modSwitch_realizable_parts`), where the algorithm is
a function fixed before the secret is chosen and meets the contract for every secret within the
bound. Both are proved for secrets with `SecretOK c.params.secretBound s` only. So: soundness of
the bounds for every secret; non-emptiness of the set of runs, and realizability of the budget,
for secrets within `secretBound`.

**The failure probability `2^(−κ)` is per execution of the program.** In the fresh-encryption
modes `certify?` computes `c.eps` by a union bound over `fresh.length · 2N` terms: the `N`
coefficients, two tails each, of every fresh input of *one* execution
(`Spec.Encrypt.epsFor V (n·2N) κ`). The statements bound the probability that this execution
goes wrong, for one fixed key and one draw of the encryption randomness of its `fresh.length`
inputs. They are not a bound over many executions: for `E` executions (or `E` batches of fresh
encryptions that a party may request and choose among) the union bound gives `E · 2^(−κ)`, so
to keep `2^(−κ₀)` overall `κ` must be raised to `κ₀ + ⌈log₂ E⌉`. Nothing here models an
adversary who adaptively discards or re-requests encryptions; the remark above is the plain
union bound, which the statements leave to the reader (`Challenge.FreshNoise`, module
docstring).

**Assumptions that no check discharges** (they are hypotheses of the statements, visibly):

* *The library's execution is a run.* The statements are about every `Spec.Trace.Run` at the
  budget `c.budget = Spec.Budget.certified c.params x.lay`: every key switch adds at most
  `ksBudget` to the phase, every modulus switch of `k` components at most `msBudgetAt k`. That
  a library's key switching (with the digits and the representatives `x.lay` describes, keys of
  noise at most `keyNoise`) and its modulus switching (the centred t-corrected switch) stay
  within these numbers is proved for the reference algorithms (`Challenge.Budget`:
  `relin_realizable`, `keySwitch_realizable`, `modSwitch_realizable_parts`, and with one
  top-level key set `relin_realizable_top`, `keySwitch_realizable_top`; `Challenge.Trace`:
  the textbook pins of every other instruction), not for any library's code.
* *The inputs.* Worst-case mode: `InputsOK`, `Trace.BoundsOK` (noise at most the declared input
  noise and the declared bounds). Fresh mode: `FreshInputs` (the fresh inputs are
  `Spec.Encrypt.encrypt`, under a public key with error at most `Bk`, of stored plaintext
  polynomials of norm at most the declared `Bp`), and `SamplerOK` (independence, the support
  bounds and the declared mean bound `mn/md`; or, in the worst case, the support bounds alone)
  of the encryption randomness. The secret is within `secretBound`
  where a statement says `SecretOK`. In the `ℓ₂` mode: `normSq e ≤ E2`, `normSq s ≤ S2` of the
  one fixed key, and `SubGaussSamplerOK` with the proxies `Vu`, `V1`, `V2` and the mean bound
  `mn/md` of the randomness (numbers the input supplies; nothing checks them against a key or a
  sampler).
* *The declared conventions.* `x.msMethod = .centred` (checked: `certify?_centred`) and
  `x.lay.canonical` say which modulus switch and which key-switching representatives the
  budget is for; that the library uses them is not checked here (the conformance harness
  compares the reference algorithms with OpenFHE's outputs: `harness/openfhe-pin/`).
* *The keys.* The budget assumes key-switching keys with noise at most `keyNoise`, generated
  once at the top level; `certify?` checks that such keys serve every level
  (`certify?_keys_restrict`).
* *Decryption.* `x.switched` says which decryption is covered; that the library performs it is
  not checked.
-/

namespace Challenge.Certify
open Spec NPoly Scheme Source Correct Spec.Budget Spec.Encrypt Spec.Certify Challenge.Headline
open Challenge.FreshNoise Challenge.FreshNoiseL2 MeasureTheory ProbabilityTheory

/-! ## What the certificate contains -/

/-- **The fields of a certificate, and the checks behind it.** If `certify? x = some c`: the
budget is the certified budget of the analysed parameters and the layout; the parameter checks
and the layout check passed at the analysed parameters; `c.bound` is what the reference analysis
returns on the whole program at that budget; the program has an output, and `c.outputs` lists
the outputs in order; and for each output `o`, its bound `B` in the certificate is what the
reference analysis returns on the program with `o` as its only output, is at most `c.bound`, and
passed `certOK?` (for that one-output program, at `B`). -/
theorem certify?_spec (x : Input) (c : Certificate) (h : certify? x = some c) :
    c.budget = certified c.params x.lay ∧
    schemeParamsOK? c.params = true ∧ specialOK? c.params = true ∧
    layoutOK? c.params x.lay = true ∧
    refAnalyze c.params c.budget x.prog = some c.bound ∧
    x.prog.outputs ≠ [] ∧ c.outputs.map Prod.fst = x.prog.outputs ∧
    ∀ o ∈ x.prog.outputs, ∃ B, c.outputs.lookup o = some B ∧ B ≤ c.bound ∧
      refAnalyze c.params c.budget { x.prog with outputs := [o] } = some B ∧
      certOK? c.params { x.prog with outputs := [o] } B x.switched = true := sorry

/-- In the worst-case mode the analysed parameters are the declared ones. -/
theorem certify?_worstCase (x : Input) (c : Certificate) (h : certify? x = some c)
    (hm : x.mode = .worstCase) : c.params = x.P ∧ c.used = .declared := sorry

/-- **Only the centred modulus switch is certified.** A certificate exists only for an input
that declares the centred t-corrected modulus switch: the budgets `Spec.Budget.msBudgetAt`, and
the switched decryption, are proved for that correction and exceeded by the canonical one
(`Respec.Equiv.twoPart_nonCentred_exceeds`). -/
theorem certify?_centred (x : Input) (c : Certificate) (h : certify? x = some c) :
    x.msMethod = .centred := sorry

/-- **The fresh-encryption mode: which input noise was analysed.** The variance proxy and the
denominator of the declared mean bound are positive; the analysed parameters are the declared
ones with the input noise *replaced* by `freshNoise t Bp c.eps` (the declared input noise is not
used; `Bp` is the declared bound of the stored plaintext polynomials); `freshOK?` passed at
those parameters; and `c.eps` is either `epsFor V (n·2N) κ + c.drift`, with `c.drift` the mean
drift `meanDrift (N·B_k + 1 + N·B_s) mn md`, below the worst case (`c.used = .freshKappa`), or
the worst case `worstError`, not above that sum (`c.used = .freshWorst`, `c.drift = 0`). -/
theorem certify?_fresh (x : Input) (c : Certificate) (h : certify? x = some c)
    (fresh : List Var) (Bp Bk Bu B1 B2 mn md κ : ℕ)
    (hm : x.mode = .fresh fresh Bp Bk Bu B1 B2 mn md κ) :
    0 < varProxy x.P.src.N x.P.secretBound Bk Bu B1 B2 ∧ 0 < md ∧
    c.params = { x.P with inputNoise := freshNoise x.P.src.t Bp c.eps } ∧
    freshOK? c.params x.prog fresh = true ∧
    ((c.used = .freshKappa ∧
        c.drift = meanDrift (x.P.src.N * Bk + 1 + x.P.src.N * x.P.secretBound) mn md ∧
        c.eps = epsFor (varProxy x.P.src.N x.P.secretBound Bk Bu B1 B2)
          (fresh.length * (2 * x.P.src.N)) κ + c.drift ∧
        c.eps < worstError x.P.src.N x.P.secretBound Bk Bu B1 B2) ∨
      (c.used = .freshWorst ∧ c.drift = 0 ∧
        c.eps = worstError x.P.src.N x.P.secretBound Bk Bu B1 B2 ∧
        worstError x.P.src.N x.P.secretBound Bk Bu B1 B2 ≤
          epsFor (varProxy x.P.src.N x.P.secretBound Bk Bu B1 B2)
            (fresh.length * (2 * x.P.src.N)) κ +
          meanDrift (x.P.src.N * Bk + 1 + x.P.src.N * x.P.secretBound) mn md)) := sorry

/-- The certified budget does not depend on the input noise: replacing it (as the fresh mode
does) leaves the budget of the declared parameters. -/
theorem certified_inputNoise (P : FullParams) (lay : KSLayout) (n : ℕ) :
    certified { P with inputNoise := n } lay = certified P lay := sorry

/-! ## Non-vacuity: the side conditions hold, and a run exists -/

/-- **The checks establish the side conditions** of the budget pins: the analysed parameters are
valid at the scheme level, BGV, the special primes are usable (odd, in particular), and the
layout is usable at every level of the chain and restricts to it from the top level. (These are
the hypotheses of `Challenge.Budget.relin_realizable`, `keySwitch_realizable`,
`modSwitch_realizable_parts`, `certified_run_exists`, and, with `certify?_keys_restrict`, of
`relin_realizable_top`, `keySwitch_realizable_top`.) -/
theorem certify?_paramsOK (x : Input) (c : Certificate) (h : certify? x = some c) :
    SchemeParamsOK c.params ∧ c.params.src.kind = .bgv ∧ SpecialOK c.params ∧
      ∀ ℓ, 1 ≤ ℓ → ℓ ≤ c.params.src.qs.length →
        x.lay.okAt ℓ = true ∧ restrictsTo x.lay c.params.src.qs.length ℓ = true := sorry

/-- **A certificate is about one key set, generated at the top level.** If `certify?` accepts,
then at every level `ℓ` of the chain the size condition of `gadgetKeys_restrict` holds, and any
gadget keys valid at the top level `L` (for any secret and any target: `s²` or `σ_g(s)`), cut to
the digits of level `ℓ` and read modulo `Q_ℓ·P`, are valid gadget keys at level `ℓ` with the same
noise bound. So the per-level keys that `Challenge.Budget.relin_realizable` and
`keySwitch_realizable` take as a hypothesis exist as soon as top-level keys do, as libraries
generate them: no certificate rests on keys generated separately for each level. -/
theorem certify?_keys_restrict (x : Input) (c : Certificate) (h : certify? x = some c)
    (ℓ : ℕ) (h1 : 1 ≤ ℓ) (hℓ : ℓ ≤ c.params.src.qs.length) :
    2 * (c.params.keyNoise / c.params.src.t * c.params.src.t) <
        c.params.src.modulus ℓ * specialProd c.params ∧
    ∀ (tgt : KeyTarget) (s : IntPoly c.params.src.N)
      (keys : List (IntPoly c.params.src.N × IntPoly c.params.src.N)),
      GadgetKeysOK c.params x.lay c.params.src.qs.length tgt s keys →
      GadgetKeysOK c.params x.lay ℓ tgt s (keys.take (x.lay.sizes ℓ).length) := sorry

/-- **A certified program has a run at the certified budget** from every valid input: for every
secret within the bound (`SecretOK`: this statement needs it, the soundness statements do not)
and all input ciphertexts within the analysed input noise. The run is
the textbook one of `Challenge.Budget.certified_run_exists`: hybrid key switching on the digits
of `x.lay` (`Challenge.Budget.relin_realizable`, `keySwitch_realizable`), the t-corrected switch
of every component (`modSwitch_realizable_parts`), and the textbook operations of
`Challenge.Trace` (`stepOK_add_textbook`, `stepOK_mul_textbook`, … : the table in its module
docstring). So the statements below, about every run, are about at least this one. -/
theorem certified_run_exists (x : Input) (c : Certificate) (h : certify? x = some c)
    (s : IntPoly c.params.src.N) (hs : SecretOK c.params.secretBound s)
    (msgs : Var → Msg c.params.src.t c.params.src.N)
    (cts : Var → List (IntPoly c.params.src.N)) (hin : InputsOK c.params s x.prog msgs cts) :
    ∃ σ, Trace.Run c.params c.budget s x.prog.body (initEnv c.params.src x.prog msgs)
      (Trace.initCt c.params x.prog cts) σ := sorry

/-- **The same in the fresh-encryption mode.** For every secret within the bound, every public
key for it, all randomness and all messages (and plaintext operands within their declared
bounds): if the inputs are as `FreshInputs` says and the error of every fresh encryption is at
most `c.eps` (this event is contained in the complement of `CertifiedFails`, the event whose
probability `fresh_kappa_certified` bounds; it always holds when `c.used = .freshWorst`, the
public-key error is at most `Bk` and the randomness is within its bounds:
`Challenge.FreshNoise.freshError_worst`), there is a run at the certified budget. So the
statements below are, on that event, about at least one run. (Outside it nothing is claimed
about the outputs.) -/
theorem fresh_run_exists (x : Input) (c : Certificate) (h : certify? x = some c)
    (fresh : List Var) (Bp Bk Bu B1 B2 mn md κ : ℕ)
    (hm : x.mode = .fresh fresh Bp Bk Bu B1 B2 mn md κ)
    (s e b a : IntPoly c.params.src.N) (hs : SecretOK c.params.secretBound s)
    (hpk : PublicKeyOK c.params.src.t (c.params.src.modulus c.params.src.qs.length) s e b a)
    (u e₁ e₂ : Var → IntPoly c.params.src.N)
    (hgood : ∀ y ∈ fresh, normInf (freshError s e (u y) (e₁ y) (e₂ y)) ≤ c.eps)
    (p : Var → IntPoly c.params.src.N)
    (m : Var → Poly c.params.src.t c.params.src.N) (cts : Var → List (IntPoly c.params.src.N))
    (hin : FreshInputs c.params x.prog fresh Bp s b a u e₁ e₂ p m cts) :
    ∃ σ, Trace.Run c.params c.budget s x.prog.body
      (initEnv c.params.src x.prog fun y => .exact (m y)) (Trace.initCt c.params x.prog cts) σ :=
  sorry

/-! ## What "certified" means for the outputs -/

/-- **Every output decrypts, and has noise at most its own bound.** The program is well formed
and, at the end of every run meeting the contracts at the budget `E`, each output `o` is a
ciphertext that encrypts the value `Source.eval` computes with noise at most the bound `bounds`
lists for `o`, is under the secret key `s` itself, decrypts *with `s`* by textbook decryption at
its own level to that value, and, if `switched`, by the library's switched decryption to that
value times `decScale` at the output's level. This is
`Challenge.FreshNoise.OutputsDecrypt` with the per-output noise bounds added
(`outputsCertified_decrypts`). -/
def OutputsCertified (P : FullParams) (E : Trace.Budget) (prog : Program) (switched : Bool)
    (bounds : List (Var × ℕ)) (s : IntPoly P.src.N) (msgs : Var → Msg P.src.t P.src.N)
    (cts : Var → List (IntPoly P.src.N)) : Prop :=
  ∃ ρ, Source.eval P.src prog msgs = some ρ ∧
    ∀ σ, Trace.Run P E s prog.body (initEnv P.src prog msgs) (Trace.initCt P prog cts) σ →
      ∀ o ∈ prog.outputs, ∃ v ct m B, ρ o = some v ∧ σ o = some ct ∧
        bounds.lookup o = some B ∧ Encrypts P s B v ct ∧
        v.msg = .exact m ∧ v.key = 1 ∧
        bgvDecrypt P.src.t s (ct.map (ofInt (P.src.modulus v.level))) = m ∧
        (switched = true →
          Decrypt.bgvDecryptSwitched P.src.t (P.src.qs.take v.level) s
              (ct.map (ofInt (P.src.qs.take v.level).prod)) =
            Decrypt.decScale P.src v.level • m)

/-- `OutputsCertified` is `OutputsDecrypt` and more. -/
theorem outputsCertified_decrypts (P : FullParams) (E : Trace.Budget) (prog : Program)
    (switched : Bool) (bounds : List (Var × ℕ)) (s : IntPoly P.src.N)
    (msgs : Var → Msg P.src.t P.src.N) (cts : Var → List (IntPoly P.src.N))
    (h : OutputsCertified P E prog switched bounds s msgs cts) :
    OutputsDecrypt P E prog switched s msgs cts := sorry

/-- **The certificate, for inputs within the analysed input noise** (any mode). If
`certify? x = some c`, then for every integer polynomial `s` as the secret (no `SecretOK`
hypothesis: module docstring, "For which secrets"), all messages and all input ciphertexts with
noise at most `c.params.inputNoise` (and their declared bounds), every output of every run at
the budget `c.budget` decrypts with `s` and has noise at most its bound in `c.outputs`: all
outputs at once. In the fresh-encryption modes `c.params.inputNoise` is
`freshNoise t Bp c.eps`, `Bp` the declared bound of the stored plaintext polynomials
(`certify?_fresh`, `certify?_freshL2`), and this is the deterministic core of the statements
below. The same statement under the headline name: `certify?_sound`. -/
theorem certified_sound (x : Input) (c : Certificate) (h : certify? x = some c)
    (s : IntPoly c.params.src.N) (msgs : Var → Msg c.params.src.t c.params.src.N)
    (cts : Var → List (IntPoly c.params.src.N)) (hin : InputsOK c.params s x.prog msgs cts)
    (hb : Trace.BoundsOK c.params s x.prog msgs cts) :
    OutputsCertified c.params c.budget x.prog x.switched c.outputs s msgs cts := sorry

/-- **`certify?` is sound: the BGV headline.** If `certify? x = some c`, then for every integer
polynomial `s` as the secret, all messages and all input ciphertexts that encrypt them under `s`
with noise at most the analysed input noise `c.params.inputNoise` (and within their declared
bounds), the program is well formed and at the end of **every** run at the budget `c.budget`
each output is under `s` itself, has noise at most its own bound in `c.outputs`, decrypts with
`s` by textbook decryption at its own level to the message `Source.eval` computes, and, if
`x.switched`, by the switched decryption to that message times `decScale` (`OutputsCertified`).

Read with the module docstring: "noise" includes the message; the message is the one the
ciphertext holds (factor `q_last⁻¹` per `modSwitch`); no `SecretOK` is assumed, and a run is
proved to exist only for secrets within `secretBound` (`certified_run_exists`); "every run"
means every `Spec.Trace.Run`, and that a library's execution is one is an assumption. This is
`certified_sound`, stated again under the name parallel to
`Challenge.CertifyBFV.certifyBFV?_sound`. -/
theorem certify?_sound (x : Input) (c : Certificate) (h : certify? x = some c)
    (s : IntPoly c.params.src.N) (msgs : Var → Msg c.params.src.t c.params.src.N)
    (cts : Var → List (IntPoly c.params.src.N)) (hin : InputsOK c.params s x.prog msgs cts)
    (hb : Trace.BoundsOK c.params s x.prog msgs cts) :
    OutputsCertified c.params c.budget x.prog x.switched c.outputs s msgs cts := sorry

/-- **The same for decryption alone**, as `Challenge.FreshNoise.OutputsDecrypt` (parallel to
`Challenge.CertifyBFV.certifyBFV?_decrypts`): every output of every run is under `s`, decrypts
with `s` at its own level to the message the program computes and, if `x.switched`, by the
switched decryption to that message times `decScale`. -/
theorem certify?_decrypts (x : Input) (c : Certificate) (h : certify? x = some c)
    (s : IntPoly c.params.src.N) (msgs : Var → Msg c.params.src.t c.params.src.N)
    (cts : Var → List (IntPoly c.params.src.N)) (hin : InputsOK c.params s x.prog msgs cts)
    (hb : Trace.BoundsOK c.params s x.prog msgs cts) :
    OutputsDecrypt c.params c.budget x.prog x.switched s msgs cts := sorry

/-- **The worst-case certificate**, at the declared parameters. If `certify?` accepts in the
worst-case mode, then for every integer polynomial `s` as the secret (no `SecretOK` hypothesis:
module docstring, "For which secrets"), all messages and all input ciphertexts with
noise at most `x.P.inputNoise` (and their declared bounds), every output of every run at the
budget `Spec.Budget.certified x.P x.lay` decrypts with `s` and has noise at most its own bound in
`c.outputs`. -/
theorem worst_certified (x : Input) (c : Certificate) (h : certify? x = some c)
    (hm : x.mode = .worstCase)
    (s : IntPoly x.P.src.N) (msgs : Var → Msg x.P.src.t x.P.src.N)
    (cts : Var → List (IntPoly x.P.src.N)) (hin : InputsOK x.P s x.prog msgs cts)
    (hb : Trace.BoundsOK x.P s x.prog msgs cts) :
    OutputsCertified x.P (certified x.P x.lay) x.prog x.switched c.outputs s msgs cts := sorry

/-! ## The fresh-encryption mode -/

/-- **The fresh-encryption certificate when the worst case of the error was used** (no
probability). If `certify?` accepts in the fresh mode with `c.used = .freshWorst`, then for
every secret within the bound, every public key for it with error at most `Bk`, all encryption
randomness within the bounds and all messages (and plaintext operands within their declared
bounds), every output of every run decrypts with `s` and has noise at most its bound in
`c.outputs`. The parameters are the analysed ones, `c.params`: the declared ones with input
noise `freshNoise t Bp (worstError …)` (`certify?_fresh`). Nothing is assumed of the means. -/
theorem fresh_worst_certified (x : Input) (c : Certificate) (h : certify? x = some c)
    (fresh : List Var) (Bp Bk Bu B1 B2 mn md κ : ℕ)
    (hm : x.mode = .fresh fresh Bp Bk Bu B1 B2 mn md κ)
    (hu : c.used = .freshWorst)
    (s e b a : IntPoly c.params.src.N) (hs : SecretOK c.params.secretBound s)
    (he : normInf e ≤ Bk)
    (hpk : PublicKeyOK c.params.src.t (c.params.src.modulus c.params.src.qs.length) s e b a)
    (u e₁ e₂ : Var → IntPoly c.params.src.N)
    (hrand : ∀ y ∈ fresh, normInf (u y) ≤ Bu ∧ normInf (e₁ y) ≤ B1 ∧ normInf (e₂ y) ≤ B2)
    (p : Var → IntPoly c.params.src.N)
    (m : Var → Poly c.params.src.t c.params.src.N) (cts : Var → List (IntPoly c.params.src.N))
    (hin : FreshInputs c.params x.prog fresh Bp s b a u e₁ e₂ p m cts) :
    OutputsCertified c.params c.budget x.prog x.switched c.outputs s (fun y => .exact (m y)) cts :=
  sorry

/-- The failure event of the fresh-encryption certificate: for this draw `ω` of the encryption
randomness there are stored plaintext polynomials within `Bp`, messages (and plaintext operands
within their bounds) for which `OutputsCertified` fails: **some** output of some run is not under `s`, or does not decrypt with
`s` to the value the program computes, or has noise above its own bound. -/
def CertifiedFails (P : FullParams) (E : Trace.Budget) (prog : Program) (switched : Bool)
    (bounds : List (Var × ℕ)) (fresh : List Var) (Bp : ℕ) (s b a : IntPoly P.src.N) {Ω : Type*}
    (u e₁ e₂ : Var → Ω → IntPoly P.src.N) (ω : Ω) : Prop :=
  ∃ (p : Var → IntPoly P.src.N) (m : Var → Poly P.src.t P.src.N)
      (cts : Var → List (IntPoly P.src.N)),
    FreshInputs P prog fresh Bp s b a (fun y => u y ω) (fun y => e₁ y ω) (fun y => e₂ y ω)
        p m cts ∧
      ¬ OutputsCertified P E prog switched bounds s (fun y => .exact (m y)) cts

/-- **The fresh-encryption certificate: failure probability at most `2^(−κ)`, for all outputs
together.** If `certify?` accepts in the fresh mode with exponent `κ` (whichever error bound it
used), then: for every secret within the bound and every public key for it with error at most
`Bk`; on any probability space carrying, for each fresh input, randomness meeting `SamplerOK`
(independent coefficients within the bounds, with means at most `mn/md` in absolute value; the
triples of different inputs need not be independent of each other): the probability that there
exist stored plaintext polynomials within `Bp` and messages for which some output of some run
fails to decrypt with `s`, or exceeds its own noise bound in `c.outputs`, is at most `2^(−κ)`.

The parameters and the budget in the event are the analysed ones: `c.params` is `x.P` with the
input noise replaced by `freshNoise t Bp c.eps` (`certify?_fresh`), `c.budget` its certified budget
(`certify?_spec`). The declared `x.P.inputNoise` does not occur. What the probability is over,
and what is not claimed: the module docstring of `Challenge.FreshNoise`.

(If `c.used = .freshWorst` the event has probability zero under `SamplerOK`;
`fresh_worst_certified` says more: it is empty for randomness within the bounds.) -/
theorem fresh_kappa_certified (x : Input) (c : Certificate) (h : certify? x = some c)
    (fresh : List Var) (Bp Bk Bu B1 B2 mn md κ : ℕ)
    (hm : x.mode = .fresh fresh Bp Bk Bu B1 B2 mn md κ)
    (s e b a : IntPoly c.params.src.N) (hs : SecretOK c.params.secretBound s)
    (he : normInf e ≤ Bk)
    (hpk : PublicKeyOK c.params.src.t (c.params.src.modulus c.params.src.qs.length) s e b a)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (u e₁ e₂ : Var → Ω → IntPoly c.params.src.N)
    (hsamp : ∀ y ∈ fresh, SamplerOK μ Bu B1 B2 mn md (u y) (e₁ y) (e₂ y)) :
    μ.real {ω | CertifiedFails c.params c.budget x.prog x.switched c.outputs fresh Bp s b a
      u e₁ e₂ ω} ≤ (2 : ℝ)⁻¹ ^ κ := sorry

/-- **The same for decryption alone**, with the failure event of `Challenge.FreshNoise`: the
probability that there exist messages for which some output of some run is not under `s` or
does not decrypt with `s` to the value the program computes is at most `2^(−κ)`. -/
theorem fresh_kappa_decrypts (x : Input) (c : Certificate) (h : certify? x = some c)
    (fresh : List Var) (Bp Bk Bu B1 B2 mn md κ : ℕ)
    (hm : x.mode = .fresh fresh Bp Bk Bu B1 B2 mn md κ)
    (s e b a : IntPoly c.params.src.N) (hs : SecretOK c.params.secretBound s)
    (he : normInf e ≤ Bk)
    (hpk : PublicKeyOK c.params.src.t (c.params.src.modulus c.params.src.qs.length) s e b a)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (u e₁ e₂ : Var → Ω → IntPoly c.params.src.N)
    (hsamp : ∀ y ∈ fresh, SamplerOK μ Bu B1 B2 mn md (u y) (e₁ y) (e₂ y)) :
    μ.real {ω | DecryptFails c.params c.budget x.prog x.switched fresh Bp s b a u e₁ e₂ ω} ≤
      (2 : ℝ)⁻¹ ^ κ := sorry

/-! ## The fresh-encryption mode described in `ℓ₂` -/

/-- **The `ℓ₂` fresh-encryption mode: which input noise was analysed.** The variance proxy
`varProxyL2 E2 S2 Vu V1 V2` and the denominator of the declared mean bound are positive; the
analysed parameters are the declared ones with the input noise *replaced* by
`freshNoise t Bp c.eps`; `freshOK?` passed at those parameters; and
`c.eps = epsFor V (n·2N) κ + c.drift` with `c.drift = meanDrift (E2 + 1 + S2) mn md` (there is no
fallback in this mode). -/
theorem certify?_freshL2 (x : Input) (c : Certificate) (h : certify? x = some c)
    (fresh : List Var) (Bp E2 S2 Vu V1 V2 mn md κ : ℕ)
    (hm : x.mode = .freshL2 fresh Bp E2 S2 Vu V1 V2 mn md κ) :
    0 < varProxyL2 E2 S2 Vu V1 V2 ∧ 0 < md ∧
    c.params = { x.P with inputNoise := freshNoise x.P.src.t Bp c.eps } ∧
    freshOK? c.params x.prog fresh = true ∧ c.used = .freshKappaL2 ∧
    c.drift = meanDrift (E2 + 1 + S2) mn md ∧
    c.eps = epsFor (varProxyL2 E2 S2 Vu V1 V2) (fresh.length * (2 * x.P.src.N)) κ + c.drift :=
  sorry

/-- **The `ℓ₂` fresh-encryption certificate: failure probability at most `2^(−κ)`, for all
outputs together.** If `certify?` accepts in the mode `freshL2 fresh Bp E2 S2 Vu V1 V2 mn md κ`,
then: for
every secret `s` and public key `(b, a)` for it with error `e` such that `normSq s ≤ S2` and
`normSq e ≤ E2` (hypotheses on the one fixed key: nothing here says a generated key meets
them); on any probability space carrying, for each fresh input, randomness meeting
`SubGaussSamplerOK` with the proxies `Vu`, `V1`, `V2` and the mean bound `mn/md` (independent
coefficients, sub-Gaussian about their means; the triples of different inputs need not be
independent of each other): the probability that there exist stored plaintext polynomials within
`Bp` and messages for which some output of some run fails to decrypt with `s`, or exceeds
its own noise bound in `c.outputs`, is at most `2^(−κ)`. One event for all outputs and all fresh
inputs. The parameters and the budget in the event are the analysed ones (`certify?_freshL2`,
`certify?_spec`); the declared `x.P.inputNoise` does not occur.

What is assumed and not proved about `E2`, `S2`, `Vu`, `V1`, `V2`: the module docstring of
`Challenge.FreshNoiseL2`. (The secret is not assumed within `secretBound` here; the runs the
statement is about are those within the certified budget, which the reference algorithms meet
for secrets within `secretBound`: `fresh_l2_run_exists`.) -/
theorem fresh_l2_certified (x : Input) (c : Certificate) (h : certify? x = some c)
    (fresh : List Var) (Bp E2 S2 Vu V1 V2 mn md κ : ℕ)
    (hm : x.mode = .freshL2 fresh Bp E2 S2 Vu V1 V2 mn md κ)
    (s e b a : IntPoly c.params.src.N) (hs : normSq s ≤ S2) (he : normSq e ≤ E2)
    (hpk : PublicKeyOK c.params.src.t (c.params.src.modulus c.params.src.qs.length) s e b a)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (u e₁ e₂ : Var → Ω → IntPoly c.params.src.N)
    (hsamp : ∀ y ∈ fresh, SubGaussSamplerOK μ Vu V1 V2 mn md (u y) (e₁ y) (e₂ y)) :
    μ.real {ω | CertifiedFails c.params c.budget x.prog x.switched c.outputs fresh Bp s b a
      u e₁ e₂ ω} ≤ (2 : ℝ)⁻¹ ^ κ := sorry

/-- **The same for decryption alone**, with the failure event of `Challenge.FreshNoise`. -/
theorem fresh_l2_decrypts (x : Input) (c : Certificate) (h : certify? x = some c)
    (fresh : List Var) (Bp E2 S2 Vu V1 V2 mn md κ : ℕ)
    (hm : x.mode = .freshL2 fresh Bp E2 S2 Vu V1 V2 mn md κ)
    (s e b a : IntPoly c.params.src.N) (hs : normSq s ≤ S2) (he : normSq e ≤ E2)
    (hpk : PublicKeyOK c.params.src.t (c.params.src.modulus c.params.src.qs.length) s e b a)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (u e₁ e₂ : Var → Ω → IntPoly c.params.src.N)
    (hsamp : ∀ y ∈ fresh, SubGaussSamplerOK μ Vu V1 V2 mn md (u y) (e₁ y) (e₂ y)) :
    μ.real {ω | DecryptFails c.params c.budget x.prog x.switched fresh Bp s b a u e₁ e₂ ω} ≤
      (2 : ℝ)⁻¹ ^ κ := sorry

/-- **A run exists in the `ℓ₂` mode** on the event that the error of every fresh encryption is
at most `c.eps`, for a secret within `secretBound` (as `fresh_run_exists`). -/
theorem fresh_l2_run_exists (x : Input) (c : Certificate) (h : certify? x = some c)
    (fresh : List Var) (Bp E2 S2 Vu V1 V2 mn md κ : ℕ)
    (hm : x.mode = .freshL2 fresh Bp E2 S2 Vu V1 V2 mn md κ)
    (s e b a : IntPoly c.params.src.N) (hs : SecretOK c.params.secretBound s)
    (hpk : PublicKeyOK c.params.src.t (c.params.src.modulus c.params.src.qs.length) s e b a)
    (u e₁ e₂ : Var → IntPoly c.params.src.N)
    (hgood : ∀ y ∈ fresh, normInf (freshError s e (u y) (e₁ y) (e₂ y)) ≤ c.eps)
    (p : Var → IntPoly c.params.src.N)
    (m : Var → Poly c.params.src.t c.params.src.N) (cts : Var → List (IntPoly c.params.src.N))
    (hin : FreshInputs c.params x.prog fresh Bp s b a u e₁ e₂ p m cts) :
    ∃ σ, Trace.Run c.params c.budget s x.prog.body
      (initEnv c.params.src x.prog fun y => .exact (m y)) (Trace.initCt c.params x.prog cts) σ :=
  sorry

/-! ## Discrimination: what `certify?` accepts and what it rejects

`tinyBGV` (`Spec.FullParams.tinyBGV`): `N = 4`, `t = 17`, `Q = 65537 · 786433`, input noise 64,
secret bound 1, no special prime (`Spec.Budget.SpecialOK` accepts the empty list: key switching
by digit decomposition alone); one limb per digit. The closed pins at the end are the same facts checked by the kernel
(the `#guard`s are compiled evaluation). -/

/-- An input at `tinyBGV` with one limb per digit. -/
def tinyInput (prog : Program) (switched : Bool) (mode : Mode) : Input :=
  ⟨Spec.FullParams.tinyBGV, uniformLayout 1, prog, switched, mode, .centred⟩

/-- What the guards compare: the analysed input noise, the mode used, `ε`, the whole-program
bound and the per-output bounds. (The drift is `0` in every guard that uses `summary`: mean
bound `0/1`.) -/
def summary (o : Option Certificate) : Option (ℕ × NoiseUsed × ℕ × ℕ × List (Var × ℕ)) :=
  o.map fun c => (c.params.inputNoise, c.used, c.eps, c.bound, c.outputs)

/-- Three outputs with different bounds at different levels: a sum at level 2, a relinearized
product at level 2, and its modulus switch at level 1. -/
def threeOutProg : Program :=
  { inputs := [⟨"a", 2, 2, 1, 1⟩, ⟨"b", 2, 2, 1, 1⟩],
    body := [.add "c" "a" "b", .mul "d" "a" "b", .relin "d" "d", .modSwitch "e" "d"],
    outputs := ["c", "d", "e"] }

/-- A layout that is not usable at level 1 (no digit) and is one limb per digit at level 2. -/
def badLayout : KSLayout := ⟨fun ℓ => if ℓ = 1 then [] else List.replicate ℓ 1, false⟩

/-- `tinyBGV` with a special prime equal to the plaintext modulus (not coprime to `t`). -/
def badSpecialParams : FullParams :=
  { Spec.FullParams.tinyBGV with
    store := { Spec.FullParams.tinyBGV.store with special := [⟨17, 0⟩] } }

/-- `tinyBGV` with the special prime 2. -/
def evenSpecialParams : FullParams :=
  { Spec.FullParams.tinyBGV with
    store := { Spec.FullParams.tinyBGV.store with special := [⟨2, 0⟩] } }

/-- One input at level 3 of `Challenge.Budget.restrictBadParams` (`N = 1`), copied. -/
def restrictProg : Program :=
  { inputs := [⟨"a", 2, 3, 1, 1⟩], body := [.copy "o" "a"], outputs := ["o"] }

/-- One input at level 2 of `Challenge.Budget.restrictSizeParams`, copied. -/
def restrictSizeProg : Program :=
  { inputs := [⟨"a", 2, 2, 1, 1⟩], body := [.copy "o" "a"], outputs := ["o"] }

-- ACCEPTED, worst case: tensor product, relinearization, rotation (automorphism and key switch)
-- and modulus switch (`Challenge.Budget.runDemoProg`), with either decryption.
#guard summary (certify? (tinyInput Challenge.Budget.runDemoProg false .worstCase)) ==
  some (64, .declared, 0, 320, [("c", 320)])
#guard summary (certify? (tinyInput Challenge.Budget.runDemoProg true .worstCase)) ==
  some (64, .declared, 0, 320, [("c", 320)])
-- ACCEPTED, fresh encryptions (all bounds 1: `V = 9`, worst case 9). At `κ = 1` the
-- high-probability bound `epsFor 9 16 1 = 8` is below the worst case: input noise
-- `16 + 17·8 = 152`. At `κ = 128` it is not: the worst case 9 is used, input noise 169.
#guard summary (certify? (tinyInput Challenge.Budget.runDemoProg true
  (.fresh ["a", "b"] 16 1 1 1 1 0 1 1))) == some (152, .freshKappa, 8, 320, [("c", 320)])
#guard summary (certify? (tinyInput Challenge.Budget.runDemoProg true
  (.fresh ["a", "b"] 16 1 1 1 1 0 1 128))) == some (169, .freshWorst, 9, 320, [("c", 320)])
#guard epsFor (varProxy 4 1 1 1 1 1) (2 * (2 * 4)) 1 == 8 && worstError 4 1 1 1 1 1 == 9
-- A three-component modulus switch (no relinearization) is certified, at `msBudgetAt P 3`.
#guard summary (certify? (tinyInput Challenge.Headline.mulSwitchProg true .worstCase)) ==
  some (64, .declared, 0, 179, [("c", 179)])
-- THE JOINT-ACCOUNTING CASE: three outputs, each with its own bound, in both modes.
#guard summary (certify? (tinyInput threeOutProg true .worstCase)) ==
  some (64, .declared, 0, 109068544, [("c", 128), ("d", 109068544), ("e", 181)])
#guard summary (certify? (tinyInput threeOutProg true (.fresh ["a", "b"] 16 1 1 1 1 0 1 1))) ==
  some (152, .freshKappa, 8, 109144576, [("c", 304), ("d", 109144576), ("e", 181)])
-- With the one bound of the whole program (the maximum, the bound of `d` at level 2) the
-- switched decryption of `e` at level 1 is not shown exact: `certOK?` on the whole program
-- fails, so `Challenge.FreshNoise.fresh_kappa_decrypts` does not apply to it as one program;
-- with its own bound 181 the output `e` passes.
#guard refAnalyze Spec.FullParams.tinyBGV
  (certified Spec.FullParams.tinyBGV (uniformLayout 1)) threeOutProg == some 109068544
#guard !certOK? Spec.FullParams.tinyBGV threeOutProg 109068544 true
#guard certOK? Spec.FullParams.tinyBGV { threeOutProg with outputs := ["e"] } 181 true
-- At `exampleBGV31` with OpenFHE's sampler bounds, two outputs, `κ = 128`.
#guard summary (certify? ⟨.exampleBGV31, uniformLayout 1,
    { inputs := [⟨"a", 2, 2, 1, 1⟩, ⟨"b", 2, 2, 1, 1⟩],
      body := [.add "c" "a" "b", .automorph "d" "c" 3, .keySwitch "d" "d"],
      outputs := ["c", "d"] }, true, .fresh ["a", "b"] 65536 39 1 39 39 0 1 128, .centred⟩) ==
  some (6537315749, .freshKappa, 99749, 47862607911, [("c", 13074631498), ("d", 47862607911)])

-- THE `ℓ₂` MODE. At `tinyBGV` with `E2 = S2 = 4`, proxies 1: `V = 9`, `ε = epsFor 9 16 1 = 8`,
-- the same figures as the support-bound mode at `κ = 1` above; at `κ = 128` there is no fallback
-- (`ε = epsFor 9 16 128 = 41`). Rejected when the variance proxy is zero.
#guard summary (certify? (tinyInput threeOutProg true (.freshL2 ["a", "b"] 16 4 4 1 1 1 0 1 1))) ==
  some (152, .freshKappaL2, 8, 109144576, [("c", 304), ("d", 109144576), ("e", 181)])
#guard (summary (certify? (tinyInput Challenge.Budget.runDemoProg true
  (.freshL2 ["a", "b"] 16 4 4 1 1 1 0 1 128)))).map (fun r => (r.2.1, r.2.2.1)) ==
  some (.freshKappaL2, epsFor 9 16 128)
#guard (certify? (tinyInput Challenge.Budget.runDemoProg false
  (.freshL2 ["a", "b"] 16 0 0 0 0 0 0 1 128))).isNone
-- At `exampleBGV31`, OpenFHE-like `ℓ₂` figures (`Challenge.FreshNoiseL2`, guards): `ε = 8483`
-- against 99749 in the support-bound mode, and smaller bounds for the same two outputs.
#guard summary (certify? ⟨.exampleBGV31, uniformLayout 1,
    { inputs := [⟨"a", 2, 2, 1, 1⟩, ⟨"b", 2, 2, 1, 1⟩],
      body := [.add "c" "a" "b", .automorph "d" "c" 3, .keySwitch "d" "d"],
      outputs := ["c", "d"] }, true, .freshL2 ["a", "b"] 65536 (11 * 16384) 16384 1 11 11 0 1 128,
      .centred⟩) ==
  some (556015907, .freshKappaL2, 8483, 35900008227, [("c", 1112031814), ("d", 35900008227)])

-- THE STORED-PLAINTEXT BOUND AND THE MEAN BOUND. The same program and randomness bounds with a
-- centred encoding (`Bp = ⌊17/2⌋ = 8`): input noise `8 + 17·8 = 144`; with a stored polynomial of
-- norm up to 40 (a scaled coefficient-packed plaintext): `40 + 17·8 = 176`. A certificate
-- declared at `Bp = 16` is about input noise 152 and says nothing of the latter
-- (`Challenge.FreshNoise.encrypt_stored_exceeds`).
#guard summary (certify? (tinyInput Challenge.Budget.runDemoProg true
  (.fresh ["a", "b"] 8 1 1 1 1 0 1 1))) == some (144, .freshKappa, 8, 320, [("c", 320)])
#guard summary (certify? (tinyInput Challenge.Budget.runDemoProg true
  (.fresh ["a", "b"] 40 1 1 1 1 0 1 1))) == some (176, .freshKappa, 8, 320, [("c", 320)])
-- A mean bound of `1/100` for every coordinate: weight `N·B_k + 1 + N·B_s = 9`, drift
-- `⌈9/100⌉ = 1`, so `ε = 8 + 1 = 9`, which is the worst case: the worst case is used (drift 0).
-- At `exampleBGV31` with a mean bound of `3431/2⁶⁴`: drift 1, `ε = 99750`.
#guard (certify? (tinyInput Challenge.Budget.runDemoProg true
  (.fresh ["a", "b"] 16 1 1 1 1 1 100 1))).map (fun c => (c.used, c.eps, c.drift)) ==
  some (.freshWorst, 9, 0)
#guard (certify? ⟨.exampleBGV31, uniformLayout 1,
    { inputs := [⟨"a", 2, 2, 1, 1⟩, ⟨"b", 2, 2, 1, 1⟩],
      body := [.add "c" "a" "b", .automorph "d" "c" 3, .keySwitch "d" "d"],
      outputs := ["c", "d"] }, true, .fresh ["a", "b"] 65536 39 1 39 39 3431 (2 ^ 64) 128,
      .centred⟩).map (fun c => (c.params.inputNoise, c.used, c.eps, c.drift)) ==
  some (6537315749 + 65537, .freshKappa, 99750, 1)
#guard (certify? (tinyInput threeOutProg true
  (.freshL2 ["a", "b"] 16 4 4 1 1 1 1 100 128))).map (fun c => (c.used, c.eps, c.drift)) ==
  some (.freshKappaL2, epsFor 9 16 128 + 1, 1)
-- REJECTED: a mean bound with denominator zero (it would read as mean zero).
#guard (certify? (tinyInput Challenge.Budget.runDemoProg true
  (.fresh ["a", "b"] 16 1 1 1 1 1 0 1))).isNone
#guard (certify? (tinyInput threeOutProg true
  (.freshL2 ["a", "b"] 16 4 4 1 1 1 1 0 1))).isNone

-- REJECTED: a declared modulus-switching method other than the centred one, whatever the
-- program (also one with no modulus switch: the switched decryption uses the same correction).
#guard (certify? ⟨Spec.FullParams.tinyBGV, uniformLayout 1, Challenge.Budget.runDemoProg, true,
  .worstCase, .canonical⟩).isNone
#guard (certify? ⟨Spec.FullParams.tinyBGV, uniformLayout 1, Challenge.Budget.runDemoProg, true,
  .worstCase, .other⟩).isNone
#guard (certify? ⟨Spec.FullParams.tinyBGV, uniformLayout 1,
  { inputs := [⟨"a", 2, 2, 1, 1⟩], body := [.copy "o" "a"], outputs := ["o"] }, false,
  .worstCase, .canonical⟩).isNone

-- REJECTED: an even special prime (2 is coprime to `t = 17` and to both ciphertext primes, and
-- was accepted before `SpecialOK` required odd special primes).
#guard (certify? ⟨evenSpecialParams, uniformLayout 1, Challenge.Budget.runDemoProg, false,
  .worstCase, .centred⟩).isNone
#guard !specialOK? evenSpecialParams

-- REJECTED: a layout that is usable at every level but does not restrict from the top level
-- (`Challenge.Budget.restrictBadLayout`: digits `[2, 1]` at level 3, one limb per digit below);
-- top-level keys are not keys at level 2 for it
-- (`Challenge.Budget.gadgetKeys_restrict_needs_restrictsTo`). The same input with one limb per
-- digit at every level is accepted.
#guard (certify? ⟨Challenge.Budget.restrictBadParams, Challenge.Budget.restrictBadLayout,
  restrictProg, false, .worstCase, .centred⟩).isNone
#guard [1, 2, 3].all Challenge.Budget.restrictBadLayout.okAt
#guard !layoutOK? Challenge.Budget.restrictBadParams Challenge.Budget.restrictBadLayout
#guard (certify? ⟨Challenge.Budget.restrictBadParams, uniformLayout 1, restrictProg, false,
  .worstCase, .centred⟩).isSome
-- REJECTED: key noise too large for a top-level BGV key to stay a key at level 1
-- (`Challenge.Budget.restrictSizeParams`: `2·4 ≥ q₀ = 5`;
-- `Challenge.Budget.gadgetKeys_restrict_needs_size_bgv`); accepted with key noise 2.
#guard (certify? ⟨Challenge.Budget.restrictSizeParams, uniformLayout 1, restrictSizeProg, false,
  .worstCase, .centred⟩).isNone
#guard !keysRestrict? Challenge.Budget.restrictSizeParams
#guard (certify? ⟨Challenge.Budget.restrictParams [5, 7] [] 2, uniformLayout 1, restrictSizeProg,
  false, .worstCase, .centred⟩).isSome
-- Uniform digits pass the layout check at every chain length and digit size.
#guard (List.range 6).all fun α => layoutOK? .exampleBGV31 (uniformLayout α)
#guard (List.range 6).all fun α =>
  layoutOK? (Challenge.Budget.restrictParams [5, 7, 11, 13, 17] [3, 19] 0) (uniformLayout α)

-- REJECTED: a special prime that is not coprime to `t` (the same input with the special prime
-- 19 is accepted).
#guard (certify? ⟨badSpecialParams, uniformLayout 1, Challenge.Budget.runDemoProg, false,
  .worstCase, .centred⟩).isNone
#guard (certify? ⟨{ Spec.FullParams.tinyBGV with
    store := { Spec.FullParams.tinyBGV.store with special := [⟨19, 0⟩] } },
  uniformLayout 1, Challenge.Budget.runDemoProg, false, .worstCase, .centred⟩).isSome
-- ACCEPTED: a special modulus that is not prime (15) but odd and coprime to `t` and to both
-- ciphertext primes: `SpecialOK` asks for coprimality, not primality (its docstring says why
-- that suffices).
#guard (certify? ⟨{ Spec.FullParams.tinyBGV with
    store := { Spec.FullParams.tinyBGV.store with special := [⟨15, 0⟩] } },
  uniformLayout 1, Challenge.Budget.runDemoProg, false, .worstCase, .centred⟩).isSome
-- REJECTED: a layout not usable at level 1, although the reference analysis accepts the
-- program at its budget (the analysis does not look at the layout's shape).
#guard (certify? ⟨Spec.FullParams.tinyBGV, badLayout, Challenge.Budget.runDemoProg, false,
  .worstCase, .centred⟩).isNone
#guard !layoutOK? Spec.FullParams.tinyBGV badLayout
#guard (refAnalyze Spec.FullParams.tinyBGV
  (certified Spec.FullParams.tinyBGV badLayout) Challenge.Budget.runDemoProg).isSome
-- REJECTED: variance proxy zero (all sampler bounds zero).
#guard (certify? (tinyInput Challenge.Budget.runDemoProg false
  (.fresh ["a", "b"] 16 0 0 0 0 0 1 128))).isNone
-- REJECTED in the fresh mode: an input that is neither fresh nor a bounded plaintext.
#guard (certify? (tinyInput Challenge.Budget.runDemoProg false
  (.fresh ["a"] 16 1 1 1 1 0 1 1))).isNone
-- REJECTED: an output left under a rotated key (accepted once it is key-switched back).
#guard (certify? (tinyInput
  { inputs := [⟨"a", 2, 2, 1, 1⟩], body := [.automorph "o" "a" 5], outputs := ["o"] }
  false .worstCase)).isNone
#guard (certify? (tinyInput
  { inputs := [⟨"a", 2, 2, 1, 1⟩], body := [.automorph "o" "a" 5, .keySwitch "o" "o"],
    outputs := ["o"] } false .worstCase)).isSome
-- REJECTED only with the switched decryption: a bound that fits `Q/2` at the output's level
-- but whose switched phase does not fit `q₀/2` (`Challenge.Decrypt`'s guards).
#guard (certify? ⟨{ Spec.FullParams.tinyBGV with inputNoise := 25765000000 }, uniformLayout 1,
  { inputs := [⟨"a", 2, 2, 1, 1⟩], body := [.copy "o" "a"], outputs := ["o"] }, false,
  .worstCase, .centred⟩).isSome
#guard (certify? ⟨{ Spec.FullParams.tinyBGV with inputNoise := 25765000000 }, uniformLayout 1,
  { inputs := [⟨"a", 2, 2, 1, 1⟩], body := [.copy "o" "a"], outputs := ["o"] }, true,
  .worstCase, .centred⟩).isNone
-- REJECTED: noise overflow (four squarings); a program with no output.
#guard (certify? (tinyInput
  { inputs := [⟨"a", 2, 2, 1, 1⟩],
    body := [.square "c" "a", .square "c" "c", .square "c" "c", .square "c" "c"],
    outputs := ["c"] } false .worstCase)).isNone
#guard (certify? (tinyInput
  { inputs := [⟨"a", 2, 2, 1, 1⟩], body := [.copy "c" "a"], outputs := [] }
  false .worstCase)).isNone
-- REJECTED: one bad output among good ones (`o` is under a rotated key).
#guard (certify? (tinyInput
  { inputs := [⟨"a", 2, 2, 1, 1⟩], body := [.copy "c" "a", .automorph "o" "a" 5],
    outputs := ["c", "o"] } false .worstCase)).isNone

/-- `certify?` accepts `runDemoProg` at `tinyBGV` (worst case, switched decryption): the
statements above are about at least this input. -/
theorem certify?_accepts_runDemo :
    (certify? (tinyInput Challenge.Budget.runDemoProg true .worstCase)).isSome = true := sorry

/-- `certify?` accepts the three-output program in the fresh-encryption mode at `κ = 1`, with
the high-probability bound (`c.used = .freshKappa`) and three different per-output bounds. -/
theorem certify?_accepts_threeOut :
    (certify? (tinyInput threeOutProg true (.fresh ["a", "b"] 16 1 1 1 1 0 1 1))).map
        (fun c => (c.used, c.outputs)) =
      some (.freshKappa, [("c", 304), ("d", 109144576), ("e", 181)]) := sorry

/-- `certify?` accepts the three-output program in the `ℓ₂` fresh-encryption mode. -/
theorem certify?_accepts_threeOut_l2 :
    (certify? (tinyInput threeOutProg true (.freshL2 ["a", "b"] 16 4 4 1 1 1 0 1 1))).map
        (fun c => (c.used, c.outputs)) =
      some (.freshKappaL2, [("c", 304), ("d", 109144576), ("e", 181)]) := sorry

/-- `certify?` rejects a special prime that is not coprime to the plaintext modulus. -/
theorem certify?_rejects_badSpecial :
    (certify? ⟨badSpecialParams, uniformLayout 1, Challenge.Budget.runDemoProg, false,
      .worstCase, .centred⟩).isSome = false := sorry

/-- `certify?` rejects a layout that is not usable at some level. -/
theorem certify?_rejects_badLayout :
    (certify? ⟨Spec.FullParams.tinyBGV, badLayout, Challenge.Budget.runDemoProg, false,
      .worstCase, .centred⟩).isSome = false := sorry

/-- `certify?` rejects the fresh mode when the variance proxy is zero. -/
theorem certify?_rejects_varProxy_zero :
    (certify? (tinyInput Challenge.Budget.runDemoProg false
      (.fresh ["a", "b"] 16 0 0 0 0 0 1 128))).isSome = false := sorry

/-- `certify?` rejects an output left under a rotated key. -/
theorem certify?_rejects_rotatedKey :
    (certify? (tinyInput
      { inputs := [⟨"a", 2, 2, 1, 1⟩], body := [.automorph "o" "a" 5], outputs := ["o"] }
      false .worstCase)).isSome = false := sorry

/-- `certify?` rejects, for the switched decryption, a bound that fits the output's level but
not `q₀/2` after the switch. -/
theorem certify?_rejects_switched :
    (certify? ⟨{ Spec.FullParams.tinyBGV with inputNoise := 25765000000 }, uniformLayout 1,
      { inputs := [⟨"a", 2, 2, 1, 1⟩], body := [.copy "o" "a"], outputs := ["o"] }, true,
      .worstCase, .centred⟩).isSome = false := sorry

/-- `certify?` rejects a declared modulus-switching method that is not the centred one (the same
input is accepted with `.centred`: `certify?_accepts_runDemo`). -/
theorem certify?_rejects_nonCentred :
    (certify? ⟨Spec.FullParams.tinyBGV, uniformLayout 1, Challenge.Budget.runDemoProg, true,
      .worstCase, .canonical⟩).isSome = false ∧
    (certify? ⟨Spec.FullParams.tinyBGV, uniformLayout 1, Challenge.Budget.runDemoProg, true,
      .worstCase, .other⟩).isSome = false := sorry

/-- `certify?` rejects an even special prime. -/
theorem certify?_rejects_evenSpecial :
    (certify? ⟨evenSpecialParams, uniformLayout 1, Challenge.Budget.runDemoProg, false,
      .worstCase, .centred⟩).isSome = false := sorry

/-- `certify?` rejects a layout that is usable at every level but whose lower-level digits are
not the top-level digits cut down, and accepts the same input with uniform digits. -/
theorem certify?_rejects_nonRestricting :
    (certify? ⟨Challenge.Budget.restrictBadParams, Challenge.Budget.restrictBadLayout,
      restrictProg, false, .worstCase, .centred⟩).isSome = false ∧
    (∀ ℓ, 1 ≤ ℓ → ℓ ≤ 3 → Challenge.Budget.restrictBadLayout.okAt ℓ = true) ∧
    (certify? ⟨Challenge.Budget.restrictBadParams, uniformLayout 1, restrictProg, false,
      .worstCase, .centred⟩).isSome = true := sorry

/-- `certify?` rejects a key noise for which a top-level BGV key need not be a key at level 1. -/
theorem certify?_rejects_keySize :
    (certify? ⟨Challenge.Budget.restrictSizeParams, uniformLayout 1, restrictSizeProg, false,
      .worstCase, .centred⟩).isSome = false := sorry

/-- **Uniform digits always pass the layout check**: for every digit size `α` and both kinds of
representatives, `layoutOK?` holds of `uniformLayout α`. (So a layout built with `uniformLayout` is never rejected
by this check.) -/
theorem layoutOK?_uniform (P : FullParams) (α : ℕ) (c : Bool) :
    layoutOK? P (uniformLayout α c) = true := sorry

/-- `certify?` in the `ℓ₂` fresh-encryption mode (`freshL2`) with a nonzero declared mean bound:
the drift is charged. -/
theorem certify?_accepts_drift :
    (certify? (tinyInput threeOutProg true (.freshL2 ["a", "b"] 16 4 4 1 1 1 1 100 128))).map
        (fun c => (c.used, c.eps, c.drift)) =
      some (.freshKappaL2, epsFor 9 16 128 + 1, 1) := sorry

/-- `certify?` rejects a noise overflow (four squarings at `tinyBGV`). -/
theorem certify?_rejects_overflow :
    (certify? (tinyInput
      { inputs := [⟨"a", 2, 2, 1, 1⟩],
        body := [.square "c" "a", .square "c" "c", .square "c" "c", .square "c" "c"],
        outputs := ["c"] } false .worstCase)).isSome = false := sorry

end Challenge.Certify
