# ProvenFHE: the Spec

Scope: BGV and BFV at the RNS level; not CKKS, not bootstrapping. Every one of the 681 locked
statements is proved (the gate's `pin-classes.txt` is the authority; machine-generated status is
written to `build/check-spec/` by `scripts/check-spec.sh`). This file explains the design (§1-§2),
maps what is proved (§3) and how vacuity is excluded (§4).

## 1. Requirements and how the design meets them

Two requirements for the Spec: **(a)** it is formalized so that it does not matter whether its
authors are fallible, and **(b)** it works.

**(a)** A spec cannot be proved correct; it defines what correct means. So the design never trusts
an author's judgment. The trusted definitions imported by `Spec.lean` are pinned mechanically, in
one of three ways, of different strength (§2 says which file has which):

- **a Mathlib pin**: a locked theorem in `Challenge/` saying the definition agrees with Mathlib's
  standard object (negacyclic multiplication is multiplication in `R[X]/(X^N+1)`), proved in
  `Validation/`. Only `Spec/Ring` has this kind.
- **an equality pin**: a proof that the definition equals the corresponding definition of an
  independent re-specification written blind from the literature (`Respec/`, proofs in
  `Respec/Equiv/`; `docs/TRUSTED-DEFINITIONS.md` lists which definitions have one).
- **an execution pin**: the definition (or a proved algorithm meeting it) is executed on recorded
  OpenFHE v1.6.1 runs and compared bit for bit (`harness/openfhe-pin`, `harness/bfv-float`; gate
  steps 6 and 7), with mutation tests showing the comparison catches injected bugs.
- **realizability and self-consistency pins**: locked theorems relating the definition to textbook
  formulas and algorithms written in `Challenge/` (a contract can be met, two definitions agree,
  a hypothesis is satisfiable). `Spec/Scheme`, `Spec/Source` (`Source.step`), `Spec/Trace*`,
  `Spec/Budget*`, `Spec/Encrypt`, `Spec/Decrypt`, `Spec/Layout`, `Spec/Params` and `Spec/Correct`
  have this kind, some of them also one of the two above (§2). In addition the frontend tests run
  an untrusted message-level value cross-check on recorded OpenFHE runs, with a Python mirror of
  `Source.step` (`harness/frontend/tests/run.sh`, run in gate step 6 by
  `harness/frontend/difftest.sh` from committed fixtures); that check is not a pin of the Lean
  definitions.

Every file under `Spec/` is in the import closure of `Spec.lean` (the gate checks it).

In addition, the trusted base is kept small by stating headline theorems at the level of
*decryption*, so that RNS algorithms, NTT networks and intermediate representations are
proof obligations rather than trusted definitions. A wrong intermediate definition makes a proof
fail; it cannot make a false claim go through.

The author of a definition never writes its pin's proof, and pin statements are locked.

What is left for a human to read is listed in §2 (the "root"). The residual risks are an error
shared between a definition and the re-specification or the recorded runs it is compared with, a
behavior no recorded run exercises, and a scheme-level definition that is self-consistent but does
not describe what a library does (`docs/TRUSTED-CORE.md`, section 3, lists where a definition
could be wrong without any proof failing).

**Three words used throughout, with their exact meaning here.**

- *Noise* (BGV): the ∞-norm of the whole centred phase `m + t·e`, **message included**
  (`Spec.Scheme.BGVEncrypts`). It is not the error `e`, and not `t·e`. Every BGV bound in this
  document is of this kind. For BFV the bound is on the error alone.
- *Decrypts*: the phase of the output, reduced modulo `t`, is the message `Spec.Source.eval`
  computes. That message carries a factor `q⁻¹ mod t` for every `modSwitch` (the `q` dropped),
  and the library's switched decryption returns it times `Spec.Decrypt.decScale`; both factors
  are written in the statements. What the library's user reads after decoding is the subject of
  `Spec/Scaling.lean` and `Challenge.Scaling.certify?_user`: under the computed check
  `Spec.Scaling.scaleOK?`, the switched decryption times the inverse of the factor the library
  hands to its decoder is the plain result `Spec.Scaling.plainEval` (ring operations modulo `t`
  on the encoded polynomials). That the library's factor bookkeeping is `Spec.Scaling.facStep`
  is an assumption, validated on recorded runs only.
- *For every secret*: the soundness statements about `certify?`
  (`Challenge.Certify.certify?_sound`, `certified_sound`, `worst_certified`) have no hypothesis
  on the secret. The existence of a run within the budget
  (`Challenge.Certify.certified_run_exists`) and the realizability of the budget
  (`Challenge.Budget.relin_realizable`, `keySwitch_realizable`, `modSwitch_realizable_parts`)
  are proved for secrets within `secretBound` (`SecretOK`). The fresh-encryption statements
  take `SecretOK` (or, in the `ℓ₂` mode, a bound on `‖s‖₂²`) as a hypothesis.
- *Failure probability `2^(−κ)`* (fresh-encryption modes): per execution of the program, a union
  bound over `fresh.length · 2N` tails. For `E` executions or encryption queries raise `κ` by
  `⌈log₂ E⌉`.

**(b)** "Works" is defined by `scripts/check-spec.sh` (release mode: `STRICT=1`; a from-scratch
strict `./verify.sh`, which runs it, took 817 s with a peak single-process memory of 7.2 GB on a
128-core machine that was otherwise idle when the run started). It has eight steps: (1) locked
files match the manifest `trust/LOCK` and the conformance evidence matches `trust/EVIDENCE`;
(2) no banned constructs in `Spec/` and `Challenge/` (`sorry` other than as the body of a locked
theorem, axioms, `native_decide`, `bv_decide`, `implemented_by`, `extern`, `unsafe`, `partial`,
new notation or syntax); (3) a text audit of the definition holes (§4);
(4) a sandboxed, two-phase build of `Spec`/`Challenge` and then `Validation`, every file of the
untrusted `FHE` library and the `Respec` library; (5) every pin, headline and hole is checked
structurally (statement identical to the locked one, only standard axioms) and the dependency
closure of every pin is replayed through the Lean kernel in a fresh environment, so a proof that
skipped the kernel is not accepted; (6) every `harness/*/difftest.sh` passes: the trusted
definitions and proved algorithms agree bit for bit with recorded OpenFHE runs
(`harness/openfhe-pin`), the BFV floating-point steps agree with OpenFHE's (`harness/bfv-float`),
and the `fhe_check` frontend tests pass (`harness/frontend/difftest.sh`: extraction plus a
message-level value cross-check on recorded OpenFHE runs, from committed fixtures), and on one
seed the proved reference implementation decrypts every accepted example circuit to its plaintext
semantics and refuses every rejected one (`harness/ref/difftest.sh`); (7) every
injected mutation is caught (`harness/openfhe-pin/mutants.sh`, `harness/bfv-float/mutants.sh`);
(8) the locked files are re-checked against the manifest. Step 5 also scans every constant of the
untrusted `FHE` library and of `Respec/Equiv` for `sorryAx` and non-standard axioms (and replays
them), checks that every `.lean` file under `Challenge/` and `Spec/` is in the import closure of
`Challenge.lean` / `Spec.lean`, and lists (without counting them as pins) the generated field
projections of `Prop` structures declared in `Challenge/`.

A reviewer's job is reading the root.

## 2. The root: what a human must read

| File | What it defines | Pinned by |
|---|---|---|
| `Spec/Correct.lean` | `Encrypts`, `inputVal`, `InputsOK` (a list of integer polynomials encrypts a `Source` value at a level; used by every noise statement) | the definitions below (`Spec/Scheme.lean`); non-vacuity pins of the statements that assume them |
| `Spec/Scheme.lean` | BGV/BFV decryption, the noise invariants `*Encrypts`, `KeyValid`, `SecretOK` | `Challenge/Scheme.lean`: textbook decryption, add/mul soundness, non-vacuity (self-consistency only). No differential test against OpenFHE |
| `Spec/Source.lean` | source programs and their meaning (`step`, `eval`) at the message level | `Challenge/Source.lean`: realizability pins (a textbook operation maps ciphertexts encrypting `step`'s operands to one encrypting `step`'s result; a plaintext operand is any representative of its message with a declared bound, `encrypts_plain_bgv`, with the conventions `[0, t)` (bound `t − 1`) and centred (bound `⌊t/2⌋`) as instances). Not pinned to OpenFHE: the only check against it is untrusted (extraction plus a message-level value cross-check on recorded OpenFHE runs, with a Python mirror of `Source.step`; `harness/frontend/tests/run.sh`) |
| `Spec/Layout.lean` | the per-limb storage parameters of a parameter set (`LimbParams`, `StoreParams`: moduli, a root of unity per modulus, a word size); the certificates read only the special moduli | `Challenge/Params.lean` (through `ParamsOK`) |
| `Spec/Params.lean` | `SchemeParamsOK` (all the noise statements assume of the parameters), `ParamsOK` (adds storage clauses: 32-bit words, a root of unity per limb; no certificate assumes them), and two example parameter sets: `FullParams.tinyBGV` (`N = 4`, `t = 17`, two primes, no special prime; hand-evaluable) and `FullParams.exampleBGV31` (`N = 2¹⁴`, two 31-bit primes and one 31-bit special prime, each just above `2³⁰`). The noise certificates read `src`, `secretBound`, `inputNoise`, `keyNoise` and the special moduli; they ignore `store.W`, `store.limbs`, every `ψ` and `outputNoise` | `Challenge/Params.lean`, `Challenge/Corpus.lean` (the instances satisfy `ParamsOK`; the compiled checks are sound) |
| `Spec/Ring.lean` | computable `R[X]/(X^N+1)` | `Challenge/Ring.lean`: bijective ring homomorphism to Mathlib's quotient |
| `Spec/Encrypt.lean` | BGV public-key encryption of a stored plaintext polynomial `p` with a declared bound `Bp` on `‖p‖∞` (`freshNoise t Bp ε = Bp + t·ε`; `Bp = t − 1` for a packed encoding), the drift `meanDrift` that a declared bound on the samplers' means adds to ε, the fresh-input check `freshOK?` (a fresh input declares no bound of its own; any other input is a 1-part value with a declared bound), the ε of the `--kappa` mode, and the computed precondition of a decryption certificate `certOK?` (every output under the secret key itself, `outputKey?`; switched decryption exact) (the sampler hypothesis `SamplerOK` is in `Challenge/FreshNoise.lean`; its four generated field projections are listed by the gate and not counted as pins) | `Challenge/FreshNoise.lean` (phase identity, the two standard stored representatives and a stored polynomial that the bound at `t − 1` does not cover, worst case of the fresh error attained, tail bound for samplers with mean at most `mn/md`, `freshOK?_spec`, `outputKey?_eq`, and the three certificate statements `certified_decrypts`, `fresh_worst_decrypts`, `fresh_kappa_decrypts` that `fhe_check` cites, with guards that the vacuous and rotated-key cases are rejected): self-consistency; that OpenFHE encrypts this way is read from its source and executed on recorded OpenFHE encryptions by the conformance harness (`harness/openfhe-pin/`, check `c.encrypt`) |
| `Spec/Scaling.lean` | the library's scaling-factor bookkeeping (OpenFHE v1.6.1, file:line in the docstring): the plain (user-level) semantics `plainEval`, the true and tracked factors (`facStep`, `factors?`), user-level decryption `userDecrypt`, the check `scaleOK?` | `Challenge/Scaling.lean`: the invariant `eval_scaled`, the user-level headline `certify?_user`, discrimination pins (operands with different factors, a plaintext product whose tracked factor is wrong, an untracked switch, a non-unit factor, and `adjProg_raw_ne_plain`: without the factor the raw decryption is not the plain result). That OpenFHE follows `facStep` is not proved; the frontend's replay and the recorded runs check it |
| `Spec/Certify.lean` | the data of the BGV decision `Challenge.Certify.certify?`: its input (`Input`: parameters, key-switching layout, program, decryption, the input-noise `Mode`, the declared modulus-switching method `MSMethod`), its result (`Certificate`, `NoiseUsed`), and the computations that do not involve the analyzer (`freshDrift`, `freshEps`, `layoutOK?`, `keysRestrict?`); no claim | `Challenge/Certify.lean`: `certify?_spec` (what a certificate contains and which checks passed) and the soundness statements of §3; `docs/TRUSTED-DEFINITIONS.md`, rows 99-103 |
| `Spec/CertifyBFV.lean` | the same for BFV and `Challenge.CertifyBFV.certifyBFV?`: `InputBFV` (with the declared multiplication `Technique`, plaintext-addition and modulus-switching methods and internal drops), `CertificateBFV`, and the hypotheses a certificate can record (`AssumptionBFV`) | `Challenge/CertifyBFV.lean`: `certifyBFV?_spec`, `certifyBFV?_assumed` (exactly when each hypothesis is recorded); built from every extracted program of the conformance fixtures as `fhe_check` builds it (`docs/TRUSTED-DEFINITIONS-BFV.md`) |
| `Spec/EncryptBFV.lean` | OpenFHE v1.6.1 BFV public-key encryption, `STANDARD` (`encryptBFV`: `(b·u + e₁ + ⌈Q·p/t⌉, a·u + e₂)`, noise scale 1; `scaleUpCeil` is `TimesQovert`), the deterministic encoding term `encodeDev = ⌈(Q mod t)(t−1)/t⌉`, the computed input noise `freshInputNoise`, the input check `freshOKBFV?`, the modes `FreshModeBFV` (worst / κ / κ-ℓ₂) and the result `FreshCertBFV` of the locked decision `Challenge.BFVEncrypt.certifyBFVFresh?` (which runs `certifyBFV?` with the input noise replaced) | `Challenge/BFVEncrypt.lean` (17 pins: `scaleUpCeil_spec`, `scaleUpCeil_timesQovert` (the per-limb `TimesQovert` arithmetic), `phase_encryptBFV`, `encryptBFV_encrypts`, `encodeDev_needed`, `freshOKBFV?_spec`, the certificate statements `certifyBFVFresh?_worst`, `_kappa`, `_kappaL2` (failure probability `2^(−κ)` per execution, union bound over `n·2N` events), `_spec`, `_*_eps`, `_run_exists`, discrimination): self-consistency; that OpenFHE encrypts this way is read from its source (file:line in the docstring); the conformance harness executes `encryptBFV` on the recorded encryptions (check `c.encryptBFV`: 638 `STANDARD` encryptions equal to OpenFHE's ciphertexts; `docs/TRUSTED-DEFINITIONS-BFV.md`). `EXTENDED` encryption is not modelled (the frontend refuses it) |
| `Spec/DecryptBFV.lean` | OpenFHE v1.6.1 BFV decryption for the HPS family at the full level: `DCRTPolyImpl::ScaleAndRound(t, …)` (`dcrtpoly-impl.h:1220-1490`), all 8 code paths, with its tables built in floating point (`bfvrns-cryptoparameters.cpp:430-481`), `GetMSB`, wrapping 64-bit integer steps and the two truncating casts, over an abstract binary64 arithmetic `ArithD` with the standard-model predicate `ConformsD` (extends `Spec.Float`); `bfvDecryptLib`, the parameter side condition `decParamsOK?`, the proved float error `delta`, and the margin check `decLibOK?` | `Challenge/BFVDecrypt.lean`: exactness with exact arithmetic (`decrypt1_exact`), no wrap and cast ranges, error bounds per path, the main theorem `bfvDecryptLib_correct` (within `decLibOK?` the library's output is the message mod t, and at most t), the certificate corollary `certifyBFV?_decryptsLib` with the locked check `decryptLibOK?` (full level of the HPS family only; the decision `fhe_check` runs for BFV is `decryptLibExtOK?` with `certifyBFV?_decryptsLibExt`, row `Spec/DecryptBFVLib.lean`), and `margin_needed` (a conforming arithmetic decrypts wrongly at a noise `decOK` accepts); executed bit for bit against 36 recorded real `Decrypt` outputs (`FHE/Float/RNE.lean`). BEHZ decryption and the path after `Compress` are in the next three rows |
| `Spec/DecryptBFVLow.lean` | OpenFHE v1.6.1 BFV decryption of a ciphertext with fewer limbs than `Q` (`bfvrns-pke.cpp:254-275`, every technique): the `DropLastElementAndScale` chain with its table row `diffQl + l` (`bfvrns-cryptoparameters.cpp:643-654`), the centred `SwitchModulus` (three branches, Barrett `GeneralShrinkLoop`, the bit-mask lanes of `mubintvecnat.cpp:54-127,190-237`), `MultiplyAndRound(t, q₀)` in binary64 (`ubintnat.h:657-661`, `mubintvecnat.cpp:539-553`; contraction allowed, `double(t)` not assumed exact) and the final `SwitchModulus(t)`; `bfvDecryptLow`, the side condition `decLowParamsOK?`, the proved error `lowErr`, the noise after the drops `lowNoise` (`Spec.Decrypt.decBoundRev`), the margin `decLowOK?`. The drops' NTT-form vector operations are modelled as exact modular arithmetic | `Challenge/BFVDecryptLow.lean`: the switch is the centred reduction (`switchModulus_spec`), the drops are exact (`dropAll_spec`) and their noise (`dropAll_noise`), the rounding step is exact with exact arithmetic (`roundStep_exact`), its binary64 error and cast range (`multiplyAndRound_err`), the main theorem `bfvDecryptLow_correct` (`c ≡ mᵢ`, `c < t`), `decLowOK?_t_lt` (the margin implies `t < 2⁵¹`), `lowMargin_needed`; executed bit for bit against 35 recorded real `Decrypt` outputs (`FHE/Float/RNELow.lean`) |
| `Spec/DecryptBFVBEHZ.lean` | OpenFHE v1.6.1 BFV decryption under `BEHZ` at the full level: the integer `ScaleAndRound(moduliQ, t, tgamma, …)` (`dcrtpoly-impl.h:1651-1696`) with its tables (`bfvrns-cryptoparameters.cpp:844-873`; `tgamma` a wrapping 64-bit product), `PrepModMulConst` and Shoup's `ModMulFastConst` with the signed fix-up transcribed literally (`ubintnat.h:1234-1253`); `bfvDecryptBEHZ`, the side condition `behzParamsOK?` (`t·2²⁶ < 2⁶³`), the margin `decBEHZOK?` | `Challenge/BFVDecryptBEHZ.lean`: `modMulFastConst_spec` (Shoup is `a·b mod m` for `m < 2⁶³`), exactness up to the dropped fraction `L/γ` (`behz1_exact`), the main theorem `bfvDecryptBEHZ_correct` (`c ≡ mᵢ`, `c ≤ t`), `behzParamsOK?_t_lt` (`t < 2³⁷`), `behzMargin_needed`; executed bit for bit against recorded real outputs (`FHE/Float/RNELow.lean`) |
| `Spec/DecryptBFVLib.lean` | the routine `PKEBFVRNS::Decrypt` (`bfvrns-pke.cpp:225-278`) runs, by limb count and technique: `bfvDecryptOpenFHE` | `Challenge/BFVDecryptLib.lean`: the locked check `decryptLibExtOK?` (every output covered by one of the three proved routines at its own level and bound; BEHZ below the top level only with one limb, the drop table being empty under BEHZ) and the corollary `certifyBFV?_decryptsLibExt` (the library decrypts every output of a certified program) |
| `Spec/Float.lean` | the standard model of binary64 arithmetic: an abstract arithmetic `Arith` and the predicate `Conforms` (relative error at most `u = 2⁻⁵³` when the exact result is zero or in `[2⁻¹²⁸, 2¹²⁸]`, contraction to fused multiply-add allowed), the two sums `Sums` of the HPS-family multiplications, and the exact arithmetic `exact`; nothing here is an axiom, and no IEEE 754 encoding is formalised | `Challenge/BFVMul/Float.lean`: `exact_conforms` (the model is satisfiable), the statements of §3 quantify over every conforming arithmetic; an executable correctly rounded binary64 arithmetic reproduces every recorded library multiplication bit for bit, not proved to conform (`docs/TRUSTED-DEFINITIONS-BFV.md`, `Spec/Float.lean`). That a given build conforms is a platform hypothesis (x87 extended precision is not covered) |
| `Spec/Decrypt.lean` | OpenFHE-style decryption that first switches to one prime | `Challenge/Decrypt.lean` (the switched decryption returns the message when `decBound` fits): self-consistency only; that it is OpenFHE's `Decrypt` is read from its source, and its scale factor is compared with recorded OpenFHE runs by the untrusted value cross-check |
| `Spec/IndCpaD.lean` | the IND-CPA-D game (Li–Micciancio, for exact schemes) on a declared circuit class, the multi-query IND-CPA game, the reduction `reduce` (it takes the public key only), `Correct`, `TapeOK`, `Bounded` | `Challenge/IndCpaD.lean`: `gameD_eq_gameCPA`, `prob_eq`, `prob_le`. Self-consistency only, not executed |
| `Spec/IndCpaDBFV.lean` | the BFV instance's data (`Setting`, `Circ`, `PK`, `SK`), `enc` (= `encryptBFV` at the top level), textbook `dec`, `sem` (= `Source.eval`), `KeysOK`, `GoodE`, `ksKeysIn`, `Circ.extraOK`, and a decidable-equality instance on polynomials | `Challenge/IndCpaD.lean`: `correct`, `bfv_prob_eq`, `bfv_prob_le`, `keysOK_exist`, `admissible_tiny`, compiled checks at a realistic parameter set. Self-consistency only, not executed |
| `Spec/IndCpaDProfile.lean` | an abstract RNS BGV/BFV scheme for the IND-CPA-D game with no library in it: abstract encryption, keys and randomness (what is assumed of them is `EncOKBFV` / `EncOKBGV`), an abstract type of circuits with public accessors, textbook decryption at the ciphertext's level | `Challenge/IndCpaD/Profile.lean`, `ProfileBGV.lean`: `correct_bfv`, `correct_bgv`, the probability statements. Self-consistency only; not executed against any library |
| `Spec/IndCpaDLM.lean` | the IND-CPA-D game in which an evaluation query may take any earlier ciphertext, fresh or derived (`gameLM`); the global program of provenance with the declared constant bounds of every inlined query (`Global.bounds`) and its reachable set `Reach`; admissibility on the whole inlined program (`admLM`); the reduction's local step interpreter | `Challenge/IndCpaD/LM.lean`: `gameLM_eq_gameCPA`, `probLM_eq`, `probLM_le`, `advLM_le`; `LMAgree.lean`: on fresh entries the oracle accepts what the fresh-only class accepts. Self-consistency only; not executed against any library |
| `Spec/IndCpaDSanity.lean` | vocabulary for the sanity statements only: `CpaBounded` (an IND-CPA adversary makes at most `q` queries on every path) and the `swap` maps that exchange the two messages of every encryption query or entry; read by no game, reduction or headline statement | `Challenge/IndCpaD/Sanity.lean`: `reduction_cpaBounded`, `gameD_swap`, `sim_iff` and the other sanity statements of §3 |
| `Spec/MSB.lean` | BGV in MSB form (plaintext stored scaled by `t⁻¹ mod Q`, so the phase is `t⁻¹·p + e`): encoding, decryption `msbDecrypt`, the noise predicates, MSB key validity and the map to the LSB form (the t-reading). Source citations are to Lattigo v6.2.0, which is read from its source, not proved or run here | `Challenge/MSB.lean`: decryption and noise statements transfer to the LSB statements the certificates are about |
| `Spec/MSBScale.lean` | the plaintext scale of the MSB form and the decoded-value semantics | `Challenge/MSBScale.lean`: `certifyProfile?_user_msb` |
| `Spec/Budget.lean`, `Spec/BudgetBFV.lean`, `Spec/BudgetBFVRns.lean` (slacks of the RNS multiplications; cross-checked by `#guard` against the exact-rational reference `harness/bfv-rns/bounds.py`) | error budgets computed from the parameters: key switching (both schemes), modulus switching (BGV, BFV), multiplication (BFV) | realizability pins in `Challenge/Budget.lean`, `Challenge/BFV.lean` (this repository's algorithms meet them). For BGV: the modulus-switching budgets are for the centred correction only and `certify?` refuses any other declared method; special primes must be odd; top-level keys serve every level under `restrictsTo` and a size condition, both checked by `certify?` (`Challenge/BudgetRestrict.lean`, `Challenge.Certify.certify?_keys_restrict`). The canonical-representative key switch is proved equal to the independent re-specification's (`Respec/Equiv/`) and compared bit for bit with recorded OpenFHE runs (`harness/openfhe-pin/`). Named-algorithm pins (`Challenge/Realize.lean`): locked transcriptions of OpenFHE v1.6.1's relinearization, key switch and rotation (`Challenge/Realize/OpenFHE.lean`; equal to the `FHE.*` functions the harness runs, kernel-checked in `FHE/Realize/`, not locked) meet the step contracts at `ksBoundAt` and at `c.budget` (`Challenge.Realize.relinOpenFHE_stepOK`, `keySwitchOpenFHE_stepOK`, `rotateOpenFHE161_run`, `certify?_relinOpenFHE`, `certify?_keySwitchOpenFHE`, `certify?_rotateOpenFHE161`, `certify?_modSwitch`) |

Run contracts. The `Spec/Trace*` contracts have realizability pins:

| File | What it defines | Pinned by |
|---|---|---|
| `Spec/Trace.lean` | ciphertext-level run contracts for BGV (each operation meets its phase contract, with key switching and modulus switching inside an error budget); used by the noise headline | `Challenge/Trace.lean`: realizability (the textbook algorithms meet the contracts) and agreement of its phase with `Encrypts`. That a library's operations meet the contracts is an assumption |
| `Spec/TraceBFV.lean` | the same for BFV (scale-invariant multiplication, textbook form) | `Challenge/BFV.lean` (each contract met by the textbook algorithm) |

## 3. What is proved: the statement map

The 681 locked statements are theorems of `Challenge/`, stated with `:= sorry`, hash-locked, and
proved under the same name in `Validation/`; the gate replays every proof through the Lean kernel.
The gate classifies them (`pin-classes.txt`, rule in `scripts/PinStatus.lean`): 300 substantive,
146 realisability, 111 instances of another statement, 56 discrimination, 40 closed computations,
28 true by unfolding. The headline statements, keyed on the paper's theorems and on the groups
H1-H4 whose reading closure `docs/TRUSTED-CORE.md` computes (namespace `Challenge.` omitted, files
under `Challenge/` unless named):

| Paper | H | Statements (file:line) | What they say |
|---|---|---|---|
| Thm `sound` | H1 | `Profile.certifyProfile?_sound` (`Profile.lean:58`), `Profile.certifyBFVProfile?_sound` (`:69`) | accepted at a declared budget ⇒ for every secret, every output of every run within that budget decrypts to the message the program computes, with noise at most its bound |
| default mode (what `fhe_check` prints) | H2 | `Certify.certify?_sound` (`Certify.lean:311`), `certify?_decrypts` (`:321`), `worst_certified` (`:333`); `CertifyBFV.certifyBFV?_sound` (`CertifyBFV.lean:184`), `certifyBFV?_decrypts` (`:190`) | the same at the budget the decision computes from the parameters |
| Thm `cover` | - | `Profile.coversBFV?_mul`, `_square`, `_modSwitch` (`Profile.lean:151,173,226`); `ProfileNamed.coversBFVAt?_relinBFV`, `coversBGV?_relinOpenFHE` (`Profile/Named.lean:124,160`); `Realize.relinOpenFHE_stepOK` (`Realize.lean:56`); `RealizeBFV.relinBFV_stepOK` (`RealizeBFV.lean:69`) | if the coverage check passes, the named RNS algorithms meet their contracts within the budget |
| Thm `mulapprox`, `hpsfloat` | - | `BFVMul.stepOK_mul_approx`, `stepOK_square_approx` (`BFVMul.lean:56,78`); `BFVMul.stepOK_mul_hps_tol`, `stepOK_mul_hps_float` (`BFVMul/Float.lean:371,481`) and the P-over-Q, leveled and squaring forms | approximate and HPS-family products, binary64 sums included, meet the multiplication contract |
| BEHZ; MSB transfer | H4 | `BFVMul.stepOK_mul_behz` (`BFVMul.lean:271`); `MSB.certifyProfile?_sound_msb` (`MSB.lean:257`) | BEHZ multiplication meets the contract; profile soundness for BGV in MSB form |
| Thm `indcpad` | H3 | `IndCpaDProfile.correct_bfv`, `bfv_prob_eq` (`IndCpaD/Profile.lean:93,103`), `correct_bgv`, `bgv_prob_eq` (`IndCpaD/ProfileBGV.lean:90,97`), `bfv_adv_le`, `bgv_adv_le` (`IndCpaD/ProfileAdv.lean:41,63`); `IndCpaDLM.gameLM_eq_gameCPA`, `advLM_le` (`IndCpaD/LM.lean:92,139`); not H3 roots: the compositions `advLM_le_bfv`, `advLM_le_bgv` (`IndCpaD/LMCompose.lean:98,181`) | IND-CPA-D advantage ≤ IND-CPA advantage + 2·Pr[bad] on the certified class; fresh-only game and the game with evaluation on earlier results |
| Thm `librun` | - | `CertifyBFV.certifyBFV?_library_run`, `certifyBFV?_library_decrypts` (`CertifyBFV/Library.lean:230,246`) | the transcribed OpenFHE BFV execution of an accepted program is a run within the certificate's budget |
| reference implementation (not locked) | - | `FHE.Ref.ksEvalA_eq` (`FHE/Ref/BGV.lean:138`), `FHE.Ref.bfvEvalA_eq` (`FHE/Ref/BFV.lean:212`) | `provenfhe_ref` computes the definitions |

The 681 statements by group (files under `Challenge/`):

| Group | Files | Statements |
|---|---|---|
| Trusted-definition pins | `Ring`, `Scheme`, `Params`, `Source`, `Trace`, `Decrypt`, `Corpus` | 73 |
| Budgets and realisability | `Budget*`, `Realize*`, `Word`, `BFV`, `BFV/*`, `BFVMul*` | 125 |
| The library's BFV decryption | `BFVDecrypt*` | 32 |
| Decisions and fast paths | `Certify*`, `CertifyBFV*`, `Scaling`, `FreshNoise*`, `BFVEncrypt`, `Fast*`, `Headline*` | 149 |
| Profiles and other libraries | `Profile*`, `Families/*`, `MSB*`, `Instances/*` | 118 |
| Security | `IndCpaD`, `IndCpaD/*` except `Sanity*` | 124 |
| Sanity and diligence | `Sanity/*`, `IndCpaD/Sanity*` | 60 |

**Namespaces under `Challenge/IndCpaD/`.** The directory holds six namespaces (number of locked statements in
parentheses):

| Namespace | Files | Content |
|---|---|---|
| `Challenge.IndCpaD` | `IndCpaD.lean`, `IndCpaD/Defs`, `Generic`, `Textbook` (18) | the fresh-only reduction for a perfectly correct scheme (`gameD_eq_gameCPA`, `prob_eq`, `prob_le`); the OpenFHE-shaped BFV instance; the library-transcription and textbook-multiplication evaluators |
| `Challenge.IndCpaDProfile` | `Profile`, `ProfileBGV`, `ProfileAdv`, `ProfileInstances`, `ProfileBGVInstances`, `ProfileBGVKS`, `ProfileKernel` (30) | the library-free BFV and BGV scheme over the profile class: correctness, the fresh-only reduction, the advantage bounds, instances and kernel-checked class members |
| `Challenge.IndCpaDLM` | `LM`, `LMBFV`, `LMExact`, `LMCompose`, `LMAgree`, `LMEmbed`, `LMBounds` (53) | the game with evaluation on earlier results (after Li and Micciancio): the reduction for local interpreters, instances, agreement with the fresh-only class, the embedding of regular adversaries |
| `Challenge.IndCpaDBad` | `BadEvent` (13) | the bad event: union bound, advantage bounds with the sum, coefficient tails |
| `Challenge.IndCpaDSanity` | `Sanity`, `SanityInstances` (41) | what the games and reductions do: query counts, tape locality, symmetry, games that can be lost, necessity of correctness, measurability, joint non-vacuity, what the public key contains |
| `Challenge.IndCpaDAttack` | `Attack` (10) | the attack circuits of the IND-CPA-D literature at their parameter sets |

"Profile" means two things: the certificate at a declared budget (`Challenge.Profile`,
`certifyProfile?`) and the security scheme over that class (`Challenge.IndCpaDProfile`). The
parameter sets `sealBFV`, `bgvSeal`, `bgvKSSeal` (and the builders `mkSeal`, `admSeal` at
`bgvKSSeal`) are variants of one parameter set (`N = 2¹³`, `t = 65537`, a 174-bit modulus). The
docstring of `sealBFV` (`Challenge/BFV.lean:91-96`) says that the names `sealBFV`, `sealProg` are
historical and that nothing there is a claim about any library's defaults or samplers.

**Names shared by several theorems.** `certified_sound` is `Challenge.Budget.certified_sound`
(the analyzer `refAnalyze` at the certified budget) and `Challenge.Certify.certified_sound` (the
decision `certify?`, the name `fhe_check` prints); `certified_run_exists` exists in
`Challenge.Budget`, `Challenge.Certify` and `Challenge.BFV`; `fresh_kappa_decrypts` is
`Challenge.FreshNoise.fresh_kappa_decrypts` (one program, one bound) and
`Challenge.Certify.fresh_kappa_decrypts` (`certify?`, all outputs jointly). This file uses full
names where a short one is ambiguous.

The noise theorems (budgets, decryption, fresh noise, the certificates) take only the scheme-level
parameter hypothesis `SchemeParamsOK P` (`Spec/Params.lean`): no bound on the size of the primes
and nothing about storage. Input declarations are matched first-match (`Spec.Correct.InputsOK`),
so duplicate declarations of one input do not make the hypothesis unsatisfiable. The groups in
more detail:

- **The BGV certificate** (`Challenge/Certify.lean`, decision in `Challenge/Certify/Defs.lean`).
  `Challenge.Certify.certify?_sound` and `certify?_decrypts` are the statements `fhe_check`'s BGV
  verdict rests on: if the locked decision function returns `certify? x = some c`, then for every
  secret, all messages and all inputs within the analysed input noise, every output of every run
  within `c.budget` is under the secret key itself, has noise at most its own bound in
  `c.outputs`, and decrypts (textbook decryption at its level; and, if declared, the switched
  decryption up to `decScale`) to the message `Source.eval` computes. `worst_certified`,
  `fresh_worst_certified`, `fresh_kappa_certified`, `fresh_l2_certified` are the per-mode forms.
  The budget is the one `Spec/Budget.lean` computes from key noise, special primes and digit
  layout, with realizability pins showing this repository's algorithms meet it; that a library
  meets it is an assumption.
- **The analyzer behind it** (`Challenge/Headline.lean`, predicates in
  `Challenge/Headline/Defs.lean`). `analyze_sound`, `analyze_tight`, `analyze_accepts_addMul`,
  `analyze_rejects_nonBGV` state the BGV noise analysis against the definition hole
  `FHE.Holes.analyze`; the gate's hole tables check them; the paper does not cite them.
  `NoiseSoundBGV analyze`: if `SchemeParamsOK P`, `P` is BGV and `analyze P E prog = some B`, then
  for every secret, messages and inputs with noise at most `P.inputNoise`, the program is well
  formed, and at the end of every run in the sense of `Spec.Trace` within the budget `E` each
  output encrypts the message `Source.eval` computes with noise at most `B`. `NoiseTightBGV
  analyze`: `analyze` is never worse than the locked reference analyzer `refAnalyze`; this is
  trivially true, since `FHE.Holes.analyze` is defined as `FHE.Noise.analyze`, which is
  `refAnalyze` (`FHE/Noise/Analyze.lean`); it would constrain a faster analyzer.
  `NoiseAcceptsAddMul analyze`: `analyze` accepts `y = (a + b) · c` at `exampleBGV31`.
- **The BFV analysis and certificate** (`Challenge/BFV.lean`, `BFV/Domain.lean`,
  `BFV/PerInstr.lean`, `BFVMul*.lean`, `CertifyBFV.lean`).
  - `Challenge.BFV.refAnalyzeBFV_sound` and, with one budget per instruction,
    `refAnalyzeBFVAt_sound`: the locked reference analyzer is sound for every run meeting the BFV
    contracts; multiplication is the textbook scale-invariant product. The analyzer accepts `mul`,
    `square` and `modSwitch` only on two-component operands (`domainOK`), the domain in which the
    certified budget is proved achievable; every program it accepts at the certified budget has a
    run (`Challenge.BFV.certified_run_exists`). `BFV/PerInstr.lean` (7 statements): the run
    contract and the analysis with one budget per instruction (`Spec.TraceBFV.RunAt`,
    `refAnalyzeBFVAt`; at a constant budget they are `Run` and `refAnalyzeBFV`).
  - `Challenge/BFVMul.lean` (26 statements): every multiplication of representatives of bounded
    size with a bounded rounding slack meets the contract (`stepOK_mul_lifted`,
    `stepOK_square_lifted`, `stepOK_mul_approx`); limb-level HPS, BEHZ, P-over-Q and leveled
    P-over-Q (`Challenge/BFVMul/{HPS,BEHZ,POverQ}.lean`) have the slacks `Spec/BudgetBFVRns.lean`
    computes (HPS family with exact arithmetic in place of the library's binary64 sums; BEHZ with
    integers only).
  - `Challenge/BFVMul/Float.lean` (15 statements; model `Spec/Float.lean`): the HPS family with its
    two binary64 sums transcribed operation by operation from OpenFHE v1.6.1, for every arithmetic
    conforming to `Spec.Float.Conforms` (relative error at most `2⁻⁵³`, contraction to fused
    multiply-add allowed): the sums are within `doubleSw`/`doubleSr` of their exact values
    (`nuSw_tol`, `nuSr_tol`), the casts are in range (`nu_range`, `nuSw_index`), the 128-bit
    accumulations cannot wrap under `floatAuxOK?` (`acc_no_overflow`), and HPS, P-over-Q and
    leveled P-over-Q with such sums meet the `mul` contract at the slacks evaluated at those
    tolerances (`stepOK_*_tol`, `stepOK_*_float`; squaring for HPS only). The floating-point error
    is charged to the budget.
  - `Challenge/BFVMul/BEHZWord.lean` (2 statements): the machine-word side condition
    `behzWordOK?` of OpenFHE's BEHZ code, which `certifyBFV?` checks at every BEHZ `mul`/`square`
    next to `behzAuxOK?` (where it does not hold the tool refuses the multiplication): under both
    conditions the Shenoy–Kumaresan correction the transcription computes is at least `−q` for
    every ciphertext modulus (`behz_sk_alpha_ge`); that the library's word routines then compute
    the transcription's residues is argued, not proved.
  - `Challenge/BFVMul/KSLeveled.lean` (5 statements): OpenFHE's key switch with an internal drop
    under `HPSPOVERQLEVELED` (`RelinearizeCore`, `bfvrns-leveledshe.cpp:856-900`), as
    `Fl.leveledKS`, meets the `relin` and `keySwitch` contracts within
    `Spec.BudgetBFV.ksLeveled` for every conforming arithmetic (`stepOK_relin_leveled_tol`,
    `stepOK_keySwitch_leveled_tol`, `ksCore_realizable`, `run_key_odd`; with no drop the result
    does not depend on the arithmetic, `leveledKS_drop_zero`).
  - `Challenge/CertifyBFV.lean` (35 statements about the locked decision
    `Challenge.CertifyBFV.certifyBFV?`, data types in `Spec/CertifyBFV.lean`; `fhe_check`'s BFV
    verdict is its result). The certificate carries one budget per instruction (`c.budget k`):
    each multiplication is charged the slack of its own level and, under `HPSPOVERQLEVELED`, of the
    internal drop the library makes there; each key switch `ksBoundAt` at its own level, or
    `ksLeveled` for its drop; each plaintext addition the number at its own level. The statements:
    what the certificate contains; soundness within `c.budget` (`certifyBFV?_sound`);
    realizability at every instruction of the multiplication per technique (for the HPS family
    the idealised algorithm when `floatTol` is false, the library's floating-point algorithm for
    every conforming arithmetic otherwise: `certifyBFV?_hps_mul_float`, `_hps_square_float`,
    `_poverq_mul_float`, `_leveled_mul_float`) and of the key switch with its internal drop
    (`certifyBFV?_leveled_relin`, `_leveled_keySwitch`, `_drop0` forms); level coverage
    (`certifyBFV?_mulLevels`); a run within `c.budget` (`certifyBFV?_textbook_run_exists`, the
    all-textbook run: it shows non-vacuity and is no evidence about the declared technique); and
    which hypothesis is recorded (`certifyBFV?_assumed`: `binary64`, the platform conforms;
    `idealised`, the input declares `floatTolerant = false`, so the certificate is about the
    idealised algorithms, not the library's code; `declaredDrops`, the budget rests on the
    internal drops the extractor declared; `binary64Dec`, the library's decryption conforms to
    `Spec.DecryptBFV.ConformsD`). `fhe_check` prints each recorded hypothesis in the verdict line.
    Not discharged by any check: under `HPSPOVERQLEVELED` the declared internal drops are the
    library's (`FindLevelsToDrop` is not modelled; the extractor checks that the drop recorded at
    run time equals its own dumped table and an independent replica; `harness/frontend/levelbfv/`).
    Not proved: that a build conforms to the floating-point model (IEEE binary64, round to nearest,
    no value-changing optimisation; x87 extended precision is not covered), machine-word arithmetic
    and the NTT (audited, with the needed bounds checked), anything else about library code.
  - The certificate is about textbook decryption at the output level. The library's own
    decryption is a separate locked statement (`Challenge.BFVDecryptLib.certifyBFV?_decryptsLibExt`
    under the check `decryptLibExtOK?`; rows `Spec/DecryptBFV*.lean` of §2), and `fhe_check`
    prints CERTIFIED for a BFV program only when that check holds for every output.
  - **Named library algorithms, composed** (`Challenge/Realize/OpenFHEBFV.lean`, definitions;
    `Challenge/RealizeBFV.lean`, 5 statements; `Challenge/CertifyBFV/Library.lean`, 4 statements).
    A locked transcription of OpenFHE v1.6.1's BFV key switching (HYBRID: the BGV transcription at
    plaintext modulus 1; BV with digit size 0) meets the key-switch contract within
    `Spec.BudgetBFV.ksBoundAt` (`relinBFV_stepOK`, `keySwitchBFV_stepOK`, `rotateBFV_run`) under
    `ksDeclOK?` (the declared layout is the library's; checked by `certifyBFV?`). `runLibrary`
    executes the declared technique's algorithms instruction by instruction, and
    `certifyBFV?_library_run` proves it is a `RunAt … c.budget` for every accepted input, every
    arithmetic conforming to `Spec.Float.Conforms` when `binary64 ∈ c.assumed`, top-level
    relinearization and rotation keys, a secret within bound and inputs meeting `InputsOK`, when
    the certificate does not record `idealised`; `certifyBFV?_library_decrypts` is
    `certifyBFV?_sound` applied to it.
- **Fresh encryption** (`Challenge/FreshNoise*.lean`, `Challenge/BFVEncrypt.lean`). In the BGV
  fresh-encryption modes `certify?` computes the input noise of the inputs named as fresh from the
  declared encryption bounds (`fresh_worst_certified`, `fresh_kappa_certified`,
  `fresh_l2_certified`). For BFV, when the extractor emits a `freshEncryption` section (OpenFHE
  `STANDARD` encryption), the verdict is that of the locked `Challenge.BFVEncrypt.certifyBFVFresh?`,
  which computes the input noise and ignores `params.inputNoise`: without `--kappa` the bound is
  the worst case (`certifyBFVFresh?_worst`); with `--kappa K` (and `--l2`) it holds with failure
  probability at most `2^−K` per execution over the encryption randomness
  (`certifyBFVFresh?_kappa`, `_kappaL2`); evaluation stays worst case. Without that section the
  declared `params.inputNoise` is used and `--kappa` is refused.
- **OpenFHE's machine words** (`Challenge/Word.lean`). The statements above model the library's
  integer arithmetic as exact modular arithmetic. `Challenge.Word.ksWordOK?` (every ciphertext and
  special modulus in `[2, 2⁶⁰)`, and the unreduced 128-bit sums of the hybrid key switch's base
  conversions below `2¹²⁸`; `modUp_acc_no_overflow`, `modDown_acc_no_overflow`,
  `acc_wraps_without`) is checked by `fhe_check` for OpenFHE files of both schemes, outside the
  library-neutral `certify?` (`FHE/Check/Report.lean:679-692`); the BFV
  multiplications' word conditions are in `certifyBFV?` (`floatAuxOK?`, `behzWordOK?`). That the
  Barrett, Shoup and NTT routines are exact under these bounds is argued in an audit by reading the
  source, not proved.
- **What `fhe_check` prints** (untrusted report layer, `FHE/Check/Report.lean`,
  `FHE/Check/BFVReport.lean`). The plain headline "every output decrypts correctly" is printed only
  when the proved statements cover what the user reads: for BGV, the user-level decryption
  (`Challenge.Scaling.certify?_user`, under `Spec.Scaling.scaleOK?`) must be covered, and the
  report says so in one line ("user-level decryption covered" or "not covered: <reason>"; JSON
  field `userDecryption`); for BFV, OpenFHE's own decryption of every output must be proved
  (`decryptLibExtOK?`; NOT CERTIFIED or UNSUPPORTED otherwise). For BGV, when user-level decryption
  is not covered, the certificate is withheld for a library-extracted input (NOT CERTIFIED), and an
  input not extracted from a library (hand-written, or HEIR's) is reported as `CERTIFIED AT PHASE
  LEVEL`.
- **The fast path of `fhe_check`** (`Challenge/Fast.lean`, predicates in `Challenge/Fast/Defs.lean`).
  The reference analyzers and decisions keep their environments as functions and are quadratic in
  the program length. The tool runs eight definition holes instead (`FHE.Holes.analyzeFast`,
  `certifyFast`, `analyzeBFVFast`, `certifyBFVFast`, `certifyBFVFreshFast`, `decryptLibFast`,
  `decryptLibExtFast`, `scaleOKFast`), and eight locked statements say they are **equal** to
  `refAnalyze`, `certify?`, `refAnalyzeBFVAt`, `certifyBFV?`, `certifyBFVFresh?`, `decryptLibOK?`,
  `decryptLibExtOK?`, `Spec.Scaling.scaleOK?` on every input. Equality, not one direction: every
  statement about the decisions applies unchanged to the verdict the tool prints. The holes are
  audited like the headline holes (`scripts/PinStatus.lean` tables `headlinesFast`, `holes`;
  `scripts/holes_audit.py`).
- **Profile mode of `fhe_check`** (`Challenge/Fast/Profile.lean`). `fhe_check --profile FILE`
  checks a program at a budget the user declares. Four holes, `FHE.Holes.certifyProfileFast`,
  `certifyBFVProfileFast`, `coversBFVFast`, `coversBFVAtFast`, are equal on every input to
  `Challenge.Profile.certifyProfile?`, `certifyBFVProfile?`, `coversBFV?`, `coversBFVAt?`
  (`certifyProfileFast_eq`, `certifyBFVProfileFast_eq`, `coversBFVFast_eq`, `coversBFVAtFast_eq`).
  CERTIFIED is printed only when the locked profile decision accepts at the declared budget;
  acceptance at a profile the coverage check rejects is conditional on an implementation meeting
  the profile.
- **Profile certificates, coverage and achievability** (`Challenge/Profile.lean`,
  `Profile/Defs.lean`, `Profile/Named.lean`, `Profile/Achieve.lean`, `Profile/Inputs.lean`,
  `Profile/Tool.lean`). Soundness at every budget, input non-vacuity, budget monotonicity; if the
  coverage check accepts a profile, approximate multiplication with declared lift and rounding
  slack, the transcribed hybrid relinearization and key switching and the textbook modulus switch
  meet their contracts within it (`coversBFV?_*`, `coversBFV?_relinBFV`,
  `coversBGV?_relinOpenFHE`, …). `achieve_bgv` and `achieve_bfv`: when the profile certificate
  accepts and the coverage check passes, a named evaluator (`ksRun`, `bfvRun`) produces a run
  within the profile, so its outputs decrypt; the hypotheses the checks do not discharge (canonical
  digits, the key-restriction conditions, the supplied Galois keys, operand shapes) stay explicit.
  The zero profile is accepted but not covered (`tiny_accepts`). The decisions include the
  per-declaration input checks `inputsMsgOK?` (BGV: every input's level has a modulus above `t`,
  every declared input bound is at least `⌊t/2⌋`) and `plainBoundsOK` (BFV: every plaintext input's
  declared bound is at least `⌊t/2⌋`); for every accepted program, every secret and every
  assignment of messages, inputs meeting the input hypotheses exist
  (`certifyProfile?_inputs_exist_all`, `certifyBFVProfile?_inputs_exist_all`,
  `certify?_inputs_exist`, `certifyBFV?_inputs_exist`), and `bgv_low_level_excludes`,
  `Challenge.Params.bgv_small_noise_excludes` show that a program the checks reject has a message
  with no input. `Profile/Tool.lean`: the tool's computed budget is one profile (acceptance by
  `certify?`/`certifyBFV?` implies acceptance by the profile decisions at that budget with
  identical bounds, and the computed budget passes the coverage checks). That a library's own code
  stays within a profile is not a consequence of these statements.
- **Other libraries and families** (`Challenge/Instances/Lattigo*.lean`, `Challenge/Families/*`,
  `Challenge/MSB.lean`, `Challenge/MSBScale.lean`). Lattigo v6.2.0 BGV: its profile as a function of
  its parameters, coverage at its 128-bit LogN 14 example and a small set, acceptance of concrete
  programs; that Lattigo's code stays within the profile is executed evidence on recorded runs at
  small ring dimension (`harness/lattigo-pin`), not a proof. BGV in MSB form: MSB decryption and
  the MSB step contracts map to the LSB ones, so profile soundness applies to MSB runs
  (`certifyProfile?_sound_msb`); MSB key switching and rescaling stay within the existing budgets;
  Lattigo's `relin`, `keySwitch` and `rescale` as transcribed meet the contracts within its profile
  (`*_meets_msb`, `*_meets_lsb`). Families: BEHZ multiplication under a base-size rule, with the
  rule SEAL applies shown to imply it and kernel-checked instances at SEAL's and OpenFHE's
  parameter sets; a round-then-scale multiplication contract and its check at Lattigo's example
  set; coverage checks at SEAL's and Lattigo's key-switching layouts; the HPS family at arbitrary
  summation tolerances. That SEAL's and Lattigo's code computes the stated algorithms is read from
  their source, not proved and not run here (for Lattigo: also its binary64 `ModUpExact`, its
  fused `Automorphism` and `BaseTwoDecomposition ≠ 0`).
- **Security** (`Challenge/IndCpaD*`, data in `Spec/IndCpaD.lean`, `Spec/IndCpaDBFV.lean`,
  `Spec/IndCpaDProfile.lean`, `Spec/IndCpaDLM.lean`; namespaces in the legend above).
  - The fresh-only game: the reduction of IND-CPA-D to IND-CPA for an abstract encryption and any
    public deterministic evaluator that meets the contracts within a profile-certified class, for
    BFV and BGV (`correct_bfv`, `bfv_prob_eq`, `bfv_adv_le` and the BGV twins); the OpenFHE-shaped
    statements are corollaries (`correct_via_profile`, `bfv_prob_*_via_profile`). Evaluators
    meeting hypothesis (ii): the library transcription under the binary64 model (`libEval_meets`),
    a textbook-multiplication evaluator (`textEval_meets`), a BGV evaluator with relinearization,
    key switching and modulus switching and public evaluation keys (`ksEval_meets`; the transcribed
    hybrid key switch, not OpenFHE's fused rotation), and the exact-operation BGV evaluator (no
    `relin`, `keySwitch` or `modSwitch`). Acceptance alone is not achievability; the evaluator
    hypothesis (`EvalMeets`) carries it.
  - The game with evaluation on earlier results: an evaluation query may take any earlier
    ciphertext; admissibility is checked on the whole inlined program over the fresh encryptions,
    with the declared constant bounds of every inlined query (`Global.bounds`), over the reachable
    global programs `Reach`; queries use global names. The reduction holds for every evaluator that
    is a local step interpreter and perfectly correct in the fresh-only game (`gameLM_eq_gameCPA`,
    `advLM_le`), and from the profile hypotheses (`advLM_le_bfv`, `advLM_le_bgv`). Instances at
    `N = 2¹³`: BGV exact operations; BGV with transcribed hybrid key switching and modulus switching
    (top-level keys in the public key); BFV with textbook multiplication, the transcribed key switch
    (one key set per level) and rounding modulus switching. Not covered: OpenFHE's full BFV library
    transcription. On a query over fresh entries alone and a certificate class at a constant budget
    the oracle accepts exactly what the fresh-only class accepts, whatever the history
    (`admLM_fresh_*`, `LMAgree.lean`); regular fresh-only adversaries embed with identical outcomes
    on every tape (`embed_*`, `embedProb_*`, `LMEmbed.lean`); `LMBounds.lean` gives kernel-checked
    examples in which a declared constant bound is carried. Not proved: the translation from
    adversaries with local names, the embedding of irregular adversaries, circuit- or
    instruction-dependent budgets.
  - The bad event (`BadEvent.lean`, `SanityInstances.lean`): the union bound `bad_le_sum`, the
    advantage bounds with the sum (`adv_le_sum`, `advLM_le_sum*`), equality when everything is good
    almost surely (`adv_eq`, `advLM_eq`), the coefficient tails `goodE_bad_le_*`, and a null bad
    event for samples within their bounds almost surely (`bad_null_bgvKSData`,
    `bad_null_bfvKSData`). No tail is evaluated for any distribution and the key term is not
    bounded (`docs/TRUSTED-CORE.md`, F1).
  - With key switching the reduction is to IND-CPA with the evaluation keys in the public key
    (`bgvKSData_pk_has_gadget_keys`), which includes a circular-security assumption that is not
    proved. In the instance `bgvKSSeal` the key noise `21·t` is a parameter choice.
- **Sanity statements** (`Challenge/IndCpaD/Sanity.lean`, `SanityInstances.lean`, vocabulary in
  `Spec/IndCpaDSanity.lean`; `Challenge/Sanity/*`). About the games: the reductions make exactly the
  adversary's encryption queries and at most `q`; the games read only the first `q` entries of the
  tape; they are symmetric in the two messages; they can be lost (an identity scheme is broken by
  an obvious adversary, and the reduction keeps the win); evaluation correctness cannot be dropped
  (a scheme in which `gameD_eq_gameCPA` fails), and correctness at every position is necessary and
  sufficient for the perfect simulation (`sim_iff`); discrete samplers give measurable events
  (`gameD_measurableSet`, `gameCPA_reduction_measurableSet`, `bad_measurableSet`,
  `gameLM_measurableSet`, `gameCPA_reductionLM_measurableSet`); good randomness is
  exactly "every coefficient within its bound"; every hypothesis of the BGV and BFV instances at
  `N = 2¹³` holds at once with non-zero keys and randomness (`bgvKSSeal_jointly`,
  `bfvSeal_jointly`). About the certificates: for every accepted program, every secret within the
  bound and every assignment of messages, inputs and a run within the budget exist jointly
  (`certify?_end_to_end`, `certifyBFV?_end_to_end`, and the profile forms, in which the run is the
  one a named evaluator computes from the public keys alone); the same at Lattigo's parameters;
  the rounding, lift and noise conventions (round half up; BFV decryption does not depend on the
  lift; the centred-message noise is larger by at most `Q mod t`); the exact contracts leave no
  freedom; the conservative BFV coverage check implies the level-exact one. `Sanity/Edges.lean`
  holds compiled `#guard`s and no locked statement: appending dead code can turn acceptance into
  rejection, which is conservative.
- **The attack circuits at their parameter sets** (`Challenge/IndCpaD/Attack.lean`;
  `harness/eval/cks26`). Kernel-checked: at the five parameter sets of the published
  plaintext--ciphertext attack the attack circuit is refused (the failing check is the noise
  bound), and at the same ring dimension and plaintext modulus with one more 60-bit prime the same
  circuit is in the class and the locked reduction applies (`Adv^{IND-CPA-D} ≤ Adv^{IND-CPA} +
  2·Pr[bad]`). The ciphertext--ciphertext (squaring) attack has statements of its own at its
  parameter set (`sqReduces_of`, `cks_ctct_t257`, with relinearization keys assumed within a
  bound). Qualifiers: the circuits are our re-implementation, written from the paper's description
  and a reading of its public code, not the authors' code; the evaluator is our proved evaluator,
  not library code; decryption is textbook decryption; the evaluation keys are in the public key;
  every error coefficient is assumed within its bound; the fifth prime was identified by
  reproducing the recorded input noise of the checker's runs, not read from a recorded run; "one
  more prime" is the countermeasure statement for the plaintext--ciphertext attack only.
- **The reference implementation** (`FHE/Ref/*.lean`, `ProvenfheRef.lean`, executable
  `provenfhe_ref`, `docs/REFERENCE-IMPLEMENTATION.md`, `harness/ref/`). Not locked: it is untrusted
  code. Key generation, encryption, evaluation and decryption of BGV and BFV at `N = 2¹³` are
  computed by functions proved equal to the definitions the theorems are about (the equalities are
  in `FHE/Ref`, kernel-checked, with the standard axioms only, and replayed by the gate). It is
  unoptimised and not constant-time, and it trusts the compiler, the runtime and the big-integer
  library.
- **Executed evidence about the library** (not proved). Whole-program conformance at real sizes
  (`harness/openfhe-pin/realsize`): 82 recorded cases at `N = 8192` to `32768` are checked (80 finished; two
  11-limb cases were terminated after 16,567 and 21,604 s), and the
  locked `runLibrary` is executed on certified programs at those sizes: 33 of the 35 certified
  programs (the same two did not finish), every intermediate and output ciphertext compared, 0
  differing; a committed sample of two cases is checked by the gate. Three third-party OpenFHE BGV
  programs (comparison, sign, integer division; `harness/eval/analyzer-speed/real`) are accepted by
  the full analysis at the parameters of `results.tsv`: a correctness statement only, at a toy ring
  dimension; no secure parameter set exists for them.
- **Related work.** Other Lean 4 projects prove textbook-level or phase-level results about FHE
  (FormalProof4FHE, ckks-noise-lean-model, minidregg); this one is about the RNS algorithms as a
  library executes them. The paper's related-work section compares in full.

## 4. Anti-vacuity

- Every hypothesis of the noise statements is satisfiable (`Challenge.Scheme.keyValid_exists`,
  `bgvEncrypts_exists`, `Challenge.Params.exampleBGV31_ok`, `Challenge.Params.bgv_inputs_exist`),
  and every certificate comes with a run within its budget (`certified_run_exists`,
  `certifyBFV?_textbook_run_exists`).
- Discrimination pins: what a certificate decision must refuse is pinned by statements of the form
  `certify? x = none` / `certifyBFV? x = none` (`Challenge/Certify.lean`, `Challenge/CertifyBFV.lean`,
  `Challenge/BudgetRestrict.lean`, `Challenge/Scaling.lean`, …), and the noise analysis of `Challenge/Headline.lean` must reject
  programs outside its scope (`analyze_rejects_nonBGV`).
- Definition holes are audited by `scripts/check-spec.sh` step 3 (text) and step 5 (structure of the built statements), on every run. The locked statements
  of `Challenge/Headline.lean` mention `FHE.Holes.analyze` (and those of `Challenge/Fast.lean`
  the fast-path holes `analyzeFast`, `certifyFast`, `analyzeBFVFast`, `certifyBFVFast`,
  `certifyBFVFreshFast`, `decryptLibFast`), which live
  in untrusted code, so
  the step takes `FHE/Holes.lean` and everything it imports from the `FHE/` tree and fails if any of
  them:
  - contains `sorry`, `admit`, an `axiom` declaration, `implemented_by`, `@[extern`, `unsafe`,
    `native_decide`, `bv_decide`, `decide +native`, `partial def`, `opaque`, `noncomputable` or
    `set_option debug` (the compiled aliases in `Challenge/Headline.lean` additionally fail the
    build if a hole is not computable);
  - declares a syntax extension or instance (`macro`, `syntax`, `notation`, `elab`, `macro_rules`,
    `elab_rules`, `infix*`, `prefix`, `postfix`, `instance`, `attribute [instance`; leading
    attributes and `local`/`scoped`/`private`/`protected` prefixes are allowed for the match), so
    the hole cannot change how a pin line parses or elaborates;
  - imports anything under `Validation` or `Challenge.Headline` (importing
    `Challenge.Headline.Defs` is expected).
  The text check strips comments and is a cheap filter, not a parser; step 5 is the structural
  defence. The lock manifest (step 1, re-checked in step 8) protects the locked files, and the
  build is sandboxed so untrusted code cannot alter locked build outputs.
- The acceptance pins in §3 keep the holes from being trivial rejecters. The noise checker is
  compared to a reference on all programs (`NoiseTightBGV`; `FHE.Holes.analyze` is that reference, see §3),
  and the fast-path holes are proved equal to the locked decisions.
