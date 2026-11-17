# Trusted definitions and their evidence (BGV and shared layer)

The project's criterion: every trusted definition is proved equal to `Respec` or executed against OpenFHE, and a table says which. This is that table for the BGV and shared layer; the BFV rows are in `docs/TRUSTED-DEFINITIONS-BFV.md`. Line numbers are of this release; row numbers that do not appear belong to definitions outside its scope.
Columns. (1) Lean name and `file:line`. (2) Theorems in `Respec/Equiv/` that relate the definition to an independently written `Respec` definition, and exactly what they say; a theorem that only uses the definition, or relates it to something defined in `Respec/Equiv` from the same formula, is marked as such. (3) Checks of `openfhe_pin` that run the definition on data dumped from OpenFHE (kinds below). (4) Locked statements in `Challenge/` that pin it. (5) Evidence class.
OpenFHE: upstream v1.6.1, commit `b59e1f29` (`harness/openfhe-pin/fixtures/SOURCE.txt`). Counts are from `harness/openfhe-pin/lean/README.md` and `harness/openfhe-pin/algo/README.md`, on the committed fixtures: 263 cases (220 at N = 16, 43 at N = 64), 151 with an extracted program, 112 refused by the extractor (each refusal tested); 93443 check lines, 78409 ok, 0 failing, 15034 `null`; 790 encryptions; `algo.*` 7311 operations, 963104 coefficients, 0 differing; mutants 13 of 13 and 9 of 9 caught. Per-check ok/fail/null counts of one gated run are committed as data in `harness/openfhe-pin/results/difftest-counts.json` (`bgv.perCheck`; written by `harness/openfhe-pin/counts.sh`); most rows below do not quote it, and where a cell says "every recorded …" no count is claimed. Larger suites (`tiny`, `mid`) are not committed.
`Spec/Layout.lean` (the storage parameters `LimbParams`, `StoreParams`) and the storage-level clauses of `ParamsOK` served the kernel-level headline, which is not part of this release; no noise certificate reads them except the special primes' moduli (`Spec/Layout.lean` module docstring, `Spec/Params.lean:6-10`).
Reviews: the BGV definitions were reviewed during development from three angles (cryptography, formal methods, proof checking) with AI assistance (see `README.md`), not by human experts; the review reports are not published, so no column records them.

Kinds of execution in column 3:
- **[D]** the definition itself is executed: literally (applied to wrapped arrays) or in a forced form proved equal to it in `FHE/Pin/Force.lean` (theorem named).
- **[S]** a trusted predicate is decided by a function proved sound in one direction only (`FHE/Pin/Sound.lean`: `stepOKb_sound`, `gadgetKeysCheck_sound`). Completeness is not proved, and the hypotheses `Ph.Good`/`GetOK` on the context are mirrored, not proved.
- **[B]** a bound the definition computes is compared with a norm measured on the data (soundness on recorded runs, not exactness).
- **[I]** computed and printed on an information line (`ok: null`); nothing is asserted.
- **[A]** a proved algorithm (not a `Spec` definition) is compared bit-exactly with OpenFHE's output (`algo.*`); the exceptions `algo.encrypt` and `algo.tensor` run `Spec` definitions and are listed as [D].
- **[P]** only an untrusted Python mirror runs (`harness/frontend/openfhe/value_check.py`, 44 runs at N = 1024 on v1.6.1, `harness/frontend/tests/run.sh` section 6).

Files of the `Respec/Equiv/` theorems cited in column 2 (where a cell names only the theorem):
- `Decrypt.lean`: `phase_eq`, `crit_eq`, `decrypt_eq`, `wrong_ne`, `bgvEncrypts_iff`, `encrypts_imp_ex`, `ex_imp_encrypts`, `ex_not_imp`, `normInf_unfold`.
- `Encrypt.lean`: `liftMsg_eq`, `pkGen_iff`, `pkGenStd_ok`, `encrypt_eq`, `encrypt_eq_liftMsg`, `encrypt_eq_centered`, `freshCrit_eq`, `freshBound_eq`, `freshBound_centred_le`.
- `Gadget.lean`: `gadgetFactor_eq_gadgetOF`, `gadgetFactor_residue`, `isKsk_iff`, `keyValid_imp_ksk`, `ksk_imp_keyValid`, `keyValid_restrict`, `digitModuli_pairwise`, `modulus_dvd`, `gadgetReq_restrict`, `gadgetReq_restrict_of_restrictsTo`, `gadgetReq_restrict_uniform`, `nested_of_restrictsTo`, `uniformLayout_nested`.
- `KsBound.lean`: `digitModuli_eq_B` (and the helper `digitsB`), `specialProd_eq`, `ksBoundAt_centred_eq`, `ksBoundAt_canonical_ge`, `canonical_strict`.
- `KeySwitch.lean`: `specialBasis_odd`, `keySwitch_centred_eq_specialOK`, `centredModDown_differs'`.
- `ModSwitch.lean`: `step_modSwitch_msg`, `state_modSwitch_translate`, `msCharge_vs_B`, `msBudgetAt_vs_B`, `msBudget_vs_B`, `threePart_needs_parts`, `threePart_refAnalyze`, `twoPart_nonCentred_exceeds`.
- `ModSwitchRule.lean`: `modSwitch_centred_parts`.
- `Bookkeeping.lean`: `transl_add`, `transl_mul`, `parts_mul`, `transl_mulConst`, `transl_automorph`, `key_automorph`, `galoisKeyOF_valid`, `switchPhase_eq`, `switchPhase_round`.
- `Respec/Basic.lean` (not an equivalence file): the `rfl`-style bridges `pauto_eq`, `red_eq`, `liftC_eq` that show `Respec` reuses `Spec.Ring`.

Evidence classes: `Mathlib pin` (a locked statement ties the definition to Mathlib's construction), `Respec + executed`, `Respec only`, `executed only`, `pins only` (only self-consistency, realizability or discrimination statements in `Challenge/`), `none`. A qualifier in parentheses says where the class holds only partly. Data types (structures and inductives that carry no computation) are classed `none (data)`: their meaning is in the definitions that use them.

## `Spec/Ring.lean`

`Respec` imports `Spec.Ring` and builds on it (`Respec/Basic.lean`: `padd`, `pmul`, `pauto`, `red`, `liftC`, `cnorm` are defined through `+`, `*`, `automorph`, `ofInt`, `centered`, `normInf`), so no row of this file has an independent `Respec` counterpart.

| # | Definition | Respec | Executed against OpenFHE v1.6.1 | Challenge pins | Class |
|---|---|---|---|---|---|
| 1 | `Spec.NPoly`, `Spec.Poly`, `Spec.IntPoly` (`Spec/Ring.lean:24,28,31`) | shared with Respec | the carrier of every check | `toQuot_bijective` | Mathlib pin |
| 2 | `NPoly` instances `Zero`, `One`, `Add`, `Neg`, `Sub`, `SMul`, `Mul`, `Pow` (`Spec/Ring.lean:40-59`, grouped) | shared with Respec | [D] `*` through `mulF` (`mulF_eq`): `algo.tensor` 845 operations limb-exact against the inverse NTT of OpenFHE's pointwise product; `+`, `*` inside every phase (rows 13-14); mutant `mul-negacyclic` caught | `toQuot_zero`, `toQuot_one`, `toQuot_add`, `toQuot_neg`, `toQuot_sub`, `toQuot_mul`, `toQuot_pow`, `toQuot_smul` (ring homomorphism to `R[X]/(X^N+1)`) | Mathlib pin |
| 3 | `Spec.NPoly.const` (`Spec/Ring.lean:62`) | shared | [D] inside `gadgetReq` factors (`d.key`) | `toQuot_const` | Mathlib pin |
| 4 | `Spec.NPoly.automorph` (`Spec/Ring.lean:67`) | shared (`pauto_eq`) | [D] through `autoF` (`autoF_eq`): rotation keys (`d.key`), automorph steps (`b.msg`), keys of `phaseAt`; [A] inside `rotateOpenFHE161` (`algo.rotate` 720); mutants `automorph-index`, `automorph-shift`, `automorph-sign` caught | `toQuot_automorph` (substitution `X ↦ X^g`) | Mathlib pin |
| 5 | `Spec.NPoly.map` (`Spec/Ring.lean:74`) | shared | no (not read by the BGV/BFV certificates; `ofInt` is not defined through it) | `toPolynomial_map`, `ofInt_eq_map` | Mathlib pin |
| 6 | `Spec.NPoly.Quot`, `toPolynomial`, `toQuot` (`Spec/Ring.lean:82,87,91`, grouped) | n/a | no (noncomputable anchors) | none of their own: the `toQuot_*` pins check rows 2-5 against them | none (the anchor itself: one-line definitions from Mathlib's `Polynomial` and `Ideal.Quotient`, checked by reading) |
| 7 | `Spec.NPoly.ofInt` (`Spec/Ring.lean:97`) | shared (`red_eq`) | [D] literal at every N (README "Two execution modes"), in every reduction mod Q | `ofInt_eq_map` | Mathlib pin |
| 8 | `Spec.NPoly.centered` (`Spec/Ring.lean:100`) | shared (`liftC_eq`); Respec's own `Respec.cmod` is related to `valMinAbs` only in a docstring | [D] literal at every N; inside `a.*`, `b.*`, `e.step`, `f.bound`; mutant `centring` caught | none names it (hypothesis of `bgv_decrypt_honest`) | executed only |
| 9 | `Spec.NPoly.canonical` (`Spec/Ring.lean:103`) | no | no | none | none (no use found in the BGV-layer files of this table) |
| 10 | `Spec.NPoly.normInf` (`Spec/Ring.lean:106`) | shared (`normInf_unfold` is `rfl`) | [D] literal at every N; every [B] check compares a `normInf` | none names it (`normSq_le` relates it to `normSq`) | executed only |
| 11 | `Spec.NPoly.BoundedQ` and its `Decidable` instance (`Spec/Ring.lean:109,111`) | unused by the BGV and BFV certificates (kept as a definition) | no | none | none |

## `Spec/Scheme.lean`

BFV definitions of this file (`roundDiv`, `bfvDecrypt`, `BFVEncrypts`; `Respec/Equiv/BFV.lean` has `bfvDecrypt_eq`, `bfvEncrypts_iff`): see `docs/TRUSTED-DEFINITIONS-BFV.md`.

| # | Definition | Respec | Executed against OpenFHE v1.6.1 | Challenge pins | Class |
|---|---|---|---|---|---|
| 12 | `Spec.Scheme.Kind` (`Spec/Scheme.lean:30`) | n/a | n/a | none | none (data) |
| 13 | `Spec.Scheme.phase` (`:36`) | `Respec/Equiv/Decrypt.lean` `phase_eq`: `BGV.phase s ct = Scheme.phase (ofInt Q s) ct`, equality, every N, Q, ciphertext length | [D] forced `phaseZ` (`phaseZ_spec`, phase modulo any Q), literal for N ≤ 32 (N ≤ 16 for 3 components); used by `a.*`, `b.msg`, `e.step`, `f.bound`; `a.phase.literal-vs-forced` | `phase_two`, `phase_three` | Respec + executed |
| 14 | `Spec.Scheme.centeredPhase` (`:42`) | `crit_eq`: B's `crit s ct = centeredPhase s ct`, equality | [D] `centredPhaseA` (`centredPhaseA_spec`); measured noise of `f.bound`, `a.decbound` | via `bgv_decrypt_honest`, `encrypts_bgv_iff_phase` | Respec + executed |
| 15 | `Spec.Scheme.bgvDecrypt` (`:48`) | `decrypt_eq`: B's `decrypt t s ct = bgvDecrypt t s ct`, equality, every t, Q, s, length; `wrong_ne`: B's canonical-lift decryption differs (kernel witness) | [D] `decryptA` (`decryptA_spec`): `a.textbook` (`decScale · bgvDecrypt` = OpenFHE `Decrypt`, `null` when `decryptOK?` fails for the measured phase), `b.msg` (message of `Source.step` = `bgvDecrypt` of OpenFHE's ciphertext), every recorded ciphertext/decryption | `bgv_decrypt_honest`, `encrypts_bgv_decrypts` | Respec + executed |
| 16 | `Spec.Scheme.BGVEncrypts` (`:54`) | `bgvEncrypts_iff`: iff with B's decidable `Encrypts t s ct m B`, no side condition; `encrypts_imp_ex` (implies B's existential form, either lift); `ex_imp_encrypts` (converse, needs `2B < Q`); `ex_not_imp` (converse false without it) | not as a predicate: its two conjuncts are checked separately per variable, decryption by `b.msg` [D], the norm by `f.bound` [B] | `bgv_add_sound`, `bgv_mul_sound`, `bgvEncrypts_exists` | Respec + executed (conjunct-wise) |
| 17 | `Spec.Scheme.SecretOK` (`:76`) | no (B states `normInf s ≤ Bs` inline) | the same formula with B = 1 on every recorded secret (`c.support`, through the array norm `normA`, a mirror) | hypothesis of `relin_realizable`, `keySwitch_realizable`, `modSwitch_realizable_parts`, `fresh_run_exists`; no dedicated pin | executed only (mirror; one-line definition) |
| 18 | `Spec.Scheme.KeyTarget`, `KeyTarget.eval` (`:79,85`) | used inside `isKsk_iff`, `keyValid_imp_ksk`, `ksk_imp_keyValid` (B's `sFrom` is `tgt.eval s`); `galoisKeyOF_valid` (OpenFHE's Galois key is valid for `.galois g` under `σ_{g⁻¹}(s)`) | [D] `targetZ` (`targetZ_spec`) in `d.key`; `d.key.power`: keys for s³, s⁴ have no trusted target (`ok: null`) | via `relin_realizable`, `keySwitch_realizable` | Respec + executed |
| 19 | `Spec.Scheme.KeyReq` (`:92`) | through rows 20 and 47 | through `d.key` | via `keyValid_exists` | none (data) |
| 20 | `Spec.Scheme.KeyValid` (`:110`) | `Respec/Equiv/Gadget.lean` `keyValid_imp_ksk` / `ksk_imp_keyValid`: for BGV and a constant factor `g`, `KeyValid .bgv t (t·Be) s ⟨M, const g, tgt⟩ b a` iff B's one-digit `KskDigitOK t Be g s tgt b a`, the direction `←` needing `2·(t·Be) < M` (convention `keyNoise = t·Be`); `isKsk_iff`; `keyValid_restrict` is a property (validity survives `M' ∣ M` when `2B < M'`), not an equivalence | [S] `d.key` at every level (`gadgetKeysCheck_sound`); `keyValid_iff` (`FHE/Pin/Force.lean`) ties the forced error to `KeyValid .bgv` for a constant factor; `d.key.literal-vs-forced`; `d.reading` [I]; mutants `gadget-factor`, `gadget-digit`, `key-order` caught | `keyValid_exists` (non-vacuity, degenerate key) | Respec + executed |

## `Spec/Source.lean`

| # | Definition | Respec | Executed against OpenFHE v1.6.1 | Challenge pins | Class |
|---|---|---|---|---|---|
| 21 | `Spec.Source.Var`, `Params` (`Spec/Source.lean:55,60`) | n/a | decoded from each extracted program; `load.params` checks the chain against `pin.json` | none | none (data) |
| 22 | `Spec.Source.Params.modulus` (`:71`) | no (used in `modulus_dvd`, a property) | [D] the modulus of every level in every check | none dedicated | executed only |
| 23 | `Msg`, `Val`, `Instr`, `Decl`, `Program`, `Env` (`:74,78,92,134,156,168`, grouped) | `Respec/Equiv/Bookkeeping.lean`: B's `State` read through `transl st = st.sf • st.msg` (convention, not an equality of types) | decoded from the 151 extracted programs (`b.step`, `b.decls`, `b.outputs`) | `tensorParts_two` | none (data) |
| 24 | `Spec.Source.Decl.ok` (`:146`) | no | [D] inside `Source.eval` (`b.eval`, `b.decls`); well-formedness only, nothing compared with the library | `eval_badDecl`, `refAnalyze_badDecl` | pins only |
| 25 | `Spec.Source.Program.boundOf` (`:164`) | no | [D] read by `c.ptbound` and `f.bound` (declared bounds); a lookup | none | executed only (bookkeeping) |
| 26 | `Env.set`, `Msg.lift₂`, `Msg.lift₁`, `Msg.fits` (`:170,177,181,187`, helpers of `step`) | no | [D] inside `step` (row 27) | through the `step_*` pins | executed only (through `step`) |
| 27 | `Spec.Source.step` (`:202`) | partial: `Respec/Equiv/ModSwitch.lean` `step_modSwitch_msg` (A's `step` on `modSwitch` multiplies the message by `q_last⁻¹`) and `state_modSwitch_translate`; `Bookkeeping.lean` `transl_add`, `transl_mul`, `parts_mul`, `transl_mulConst`, `transl_automorph`, `key_automorph` relate B's `State` updates to the message arithmetic `step` performs, under `msg_A = sf_B • msg_B`; no theorem states `step` equal to a B evaluator | [D] literal at every N and forced `stepA` (`stepA_spec`): `b.shape`, `b.msg` (message = `bgvDecrypt` of OpenFHE's ciphertext), `b.raw` (`decScale` · message = OpenFHE `Decrypt`), `b.step`, `b.negate`, `b.literal-vs-forced`, every traced operation of the 151 programs; mutant `scale-step` caught (needs `q ≢ 1 mod t`); [P] `value_check.py` mirrors it on 44 runs | `step_add_bgv`, `step_mul_bgv`, `step_automorph_bgv`, `step_modSwitch_bgv`, `step_dropLimbs_bgv`, `step_dropLimbs_level`, `step_addPlain_parts`, `step_mulPlain_msg`, `step_modSwitch_level` | Respec (partial) + executed |
| 28 | `Spec.Source.initEnv` (`:272`) | no | [D] `FHE/Pin/ChecksProg.lean:270` (start of the per-step walk) | `eval_input` | executed only |
| 29 | `Spec.Source.eval` (`:278`) | no direct theorem | [D] `b.eval`: the literal `Source.eval` of the whole program (cost-limited), and the fold of `stepA` (`foldlM_stepA`) | `eval_badDecl`, `eval_input`, `eval_rotatedKeySwitch`, `eval_mixedKeys` | executed only |

## `Spec/Layout.lean` (storage parameters)

Nothing in this file is executed against OpenFHE; the dumps hold no evaluation-format vector, so the ψ-ordering of OpenFHE's NTT is not checked (`harness/openfhe-pin/algo/README.md`, "Evaluation vs coefficient format"). No `Respec` counterpart. Rows 30-32 and 34-37 (word and evaluation-form definitions, memory images) were removed with the kernel-level headline.

| # | Definition | Respec | Executed against OpenFHE v1.6.1 | Challenge pins | Class |
|---|---|---|---|---|---|
| 33 | `LimbParams`, `StoreParams`, `StoreParams.units` (`:18,27,36`) | no | no | none | none (data) |

## `Spec/Params.lean`

| # | Definition | Respec | Executed against OpenFHE v1.6.1 | Challenge pins | Class |
|---|---|---|---|---|---|
| 38 | `Spec.FullParams` (`Spec/Params.lean:25`) | n/a | decoded; `load.params` | none | none (data) |
| 39 | `Spec.FullParams.allLimbs` (`:40`, storage level) | no | no | via `paramsOK?_sound` | pins only |
| 40 | `Spec.SchemeParamsOK` (`:49`) | hypothesis of `digitModuli_pairwise`, `gadgetReq_restrict` (not an equivalence) | [I] `schemeParamsOK?` is printed in `load.params` on every case, not asserted | `schemeParamsOK?_sound`, `bgv_inputs_exist`, `bgv_small_noise_excludes`, `exampleBGV31_ok` | pins only |
| 41 | `Spec.ParamsOK` (`:72`, storage level) | no | no | `exampleBGV31_ok`, `paramsOK?_sound`, `paramsOK?_exampleBGV31`, `tinyBGV_ok` (`Challenge/Corpus.lean:29`) | pins only |
| 42 | `Spec.powMod`, `noDivisorFrom`, `twoPart`, `primeOK?` (`:109,118,125,132`, grouped: the primality test) | no | no (run by `fhe_check` on every input) | through `schemeParamsOK?_sound`, `paramsOK?_sound`, `paramsOK?_rejects_composite` | pins only |
| 43 | `Spec.schemeParamsOK?` (`:138`) | no | [I] `load.params` | `schemeParamsOK?_sound`, `schemeParamsOK?_wideBGV` | pins only |
| 44 | `Spec.limbOK?`, `paramsOK?` (`:146,152`, storage level) | no | no | `paramsOK?_sound`, `paramsOK?_exampleBGV31`, `paramsOK?_rejects_composite`, `paramsOK?_rejects_root`, `paramsOK?_rejects_msgRange`, `paramsOK?_tinyBGV` | pins only |

Example parameter sets (not definitions needing evidence): `Spec.FullParams.tinyBGV` (`Spec/Params.lean:167`) and `Spec.FullParams.exampleBGV31` (`:199`). Their own pins: `tinyBGV_ok`, `paramsOK?_tinyBGV`, `exampleBGV31_ok`, `paramsOK?_exampleBGV31`, and the `#guard`s of `Challenge/Budget.lean`.

## `Spec/Correct.lean`

Rows 45-47 and 51-54 (the execution model and `Implements` of the kernel-level headline) were removed with that headline.

| # | Definition | Respec | Executed against OpenFHE v1.6.1 | Challenge pins | Class |
|---|---|---|---|---|---|
| 48 | `Spec.Correct.Encrypts` (`:20`) | no theorem names it; its BGV branch is `BGVEncrypts` (row 16) under `σ_key(s)` modulo the level's modulus, so `bgvEncrypts_iff` applies after unfolding (not stated as a theorem) | not as a predicate; the conjuncts of its BGV branch per variable through `b.msg` [D] and `f.bound` [B] | `encrypts_bgv_iff_phase`, `encrypts_bgv_decrypts`, `encrypts_plain_bgv`, `encrypts_plain_canonical`, `encrypts_plain_centred`, `bgv_inputs_exist` | pins only (BGV branch reduces to row 16) |
| 49 | `Spec.Correct.inputVal` (`:29`) | no | no | via `eval_input` | none (bookkeeping) |
| 50 | `Spec.Correct.InputsOK` (`:36`) | no | its premise is evaluated per input by `f.bound` (a run where it fails is marked `premiseBad`, nothing downstream claimed) | `bgv_inputs_exist` (non-vacuity) | pins only |

## `Spec/Trace.lean`

| # | Definition | Respec | Executed against OpenFHE v1.6.1 | Challenge pins | Class |
|---|---|---|---|---|---|
| 55 | `Spec.Trace.dst` (`Spec/Trace.lean:48`) | no | [D] inside `e.step` | none | executed only (bookkeeping) |
| 56 | `Spec.Trace.Budget` (`:56`) | no | the budget `certified P lay` of `e.step`; [I] `f.budget` | none | none (data) |
| 57 | `Spec.Trace.Budget.modSwitchAt` (`:80`) | no theorem names it (`msBudgetAt_vs_B` is about `msBudgetAt`, row 74) | [B] `e.step`, `e.modswitch-parts` through `Mut.msBudgetM` (`Mut.msBudget_none`: `rfl` to `modSwitchAt`); the 10 three-component switches of the fixtures are within `msBudgetAt P 3`, 6 of them above the two-component budget; mutant `ms-parts` caught by exactly these | `certified_modSwitchAt`; the many-component budget: `Challenge/Budget.lean:233-243` | executed only |
| 58 | `Spec.Trace.CtEnv`, `CtEnv.set` (`:87,90`) | no | inside the conclusion of `stepOKb_sound` | none | none (bookkeeping) |
| 59 | `Spec.Trace.phaseAt` (`:96`) | no direct theorem (row 13 covers `phase`) | [D] `phaseAtZ` (`phaseAtZ_spec`), literal at small N; `e.phase.literal-vs-forced` | `encrypts_bgv_iff_phase` | executed only |
| 60 | `Spec.Trace.initCt` (`:100`) | no | no | via `certified_sound`, `analyze_decrypt_switched` | none (bookkeeping) |
| 61 | `Spec.Trace.BoundsOK` (`:107`) | no | as row 50 (`f.bound`, `premiseBad`); `c.ptbound` checks plaintext operands against their declared bounds | `encrypts_plain_bgv` | pins only |
| 62 | `Spec.Trace.StepOK` (`:116`) | no theorem names it (`modSwitch_centred_parts` reuses A's proof of `stepOK_modSwitch_textbook_parts` for B's switch) | [S] `e.step`: every traced operation of the 151 programs at the budget `certified P lay`, decided by `stepOKb` (`stepOKb_sound`; witnesses `ks_witness`, `ms_witness`); no composite modulus switch occurs on the fixtures; count not in the README; [A] the operations themselves: `algo.relin`, `algo.rotate`, `algo.modReduce`, `algo.tensor`, `algo.add` and the others bit-exact (6200 operations) | `stepOK_add_textbook`, `stepOK_mul_textbook`, `stepOK_modSwitch_textbook`, `stepOK_modSwitch_textbook_parts`, `stepOK_mul_tensor`, `stepOK_automorph_textbook` and the other `stepOK_*` of `Challenge/Trace.lean`; `relin_realizable`, `keySwitch_realizable`, `modSwitch_realizable_parts` | executed only |
| 63 | `Spec.Trace.Run` (`:151`) | no | per step only: `b.step` (`step`) and `e.step` (`StepOK`) along each recorded trace | `certified_run_exists`, `wellFormed_run_exists`, `fresh_run_exists` | executed only (per step) |

## `Spec/Budget.lean`

| # | Definition | Respec | Executed against OpenFHE v1.6.1 | Challenge pins | Class |
|---|---|---|---|---|---|
| 64 | `Spec.Budget.KSLayout`, `KSLayout.okAt` (`Spec/Budget.lean:103,108`) | hypotheses of `gadgetReq_restrict` | the layout of each case (`FHE.Check.layoutOf` of the extracted program, else `uniformLayout` of OpenFHE's towers per digit, `OpenfhePin.lean:120`); `algo.layout`: OpenFHE's digit partition = the layout used, 350 of 350 (cases × levels); `d.layout` | `uniformLayout_ok`, `digitModuli_prod`, `restrictsTo_okAt` | executed only |
| 65 | `Spec.Budget.cutSizes`, `restrictsTo` (`:113,121`) | `nested_of_restrictsTo` (a property: `restrictsTo` gives nested digit moduli), not an equivalence | no (`layoutOK?` is run by `fhe_check`, not by `openfhe_pin`) | `restrictsTo_okAt`, `uniformLayout_restrictsTo`, `gadgetKeys_restrict`, `gadgetKeys_restrict_needs_restrictsTo` | pins only |
| 66 | `Spec.Budget.uniformLayout` (`:125`) | `uniformLayout_nested`, `gadgetReq_restrict_uniform` (properties) | as row 64 (`algo.layout` 350 of 350) | `uniformLayout_ok`, `uniformLayout_restrictsTo`, `layoutOK?_uniform` | executed only |
| 67 | `Spec.Budget.specialProd` (`:130`) | `specialProd_eq` (`rfl` restatement) | [D] in `d.key`, `d.layout`, `e.step` | none dedicated | executed only |
| 68 | `Spec.Budget.digitModulus`, `digitModuli` (`:133,137`) | `digitModuli_eq_B` relates it to `digitsB`, which is defined in `Respec/Equiv/KsBound.lean` from the same formula: a bridge, not independent | [D] `d.layout` (number of digits = OpenFHE's `numPartitions`), `d.key` | `digitModuli_prod` | executed only |
| 69 | `Spec.Budget.gadgetFactor` (`:144`) | `Respec/Equiv/Gadget.lean` `gadgetFactor_eq_gadgetOF`: `(gadgetFactor Pm Qs j : ℤ) = gadgetOF Pm Qs j` (B's OpenFHE gadget), equality for every `Pm`, `Qs`, `j`; `gadgetFactor_residue` (residue form, pairwise coprime moduli) | [D] `d.layout` (residues of `gadgetFactor` against every stored key limb), `d.key` (through `Mut.gadgetFactorM`, equal to it without a mutant); mutants `gadget-factor`, `gadget-digit` caught | `gadgetFactor_reconstruct`, `gadgetFactor_restrict` | Respec + executed |
| 70 | `Spec.Budget.gadgetReq` (`:150`) | by composition: its factor is `const (gadgetFactor …)` (row 69) and `keyValid_imp_ksk`/`ksk_imp_keyValid` cover `KeyValid` at a constant factor; `gadgetReq_restrict`, `gadgetReq_restrict_of_restrictsTo`, `gadgetReq_restrict_uniform` are properties (top-level keys valid at lower levels, with hypotheses) | [S] `d.key` (`keyValid_iff` "for a constant factor (every `gadgetReq`)") | via `relin_realizable`, `keySwitch_realizable`, `gadgetKeys_restrict` | Respec (by composition) + executed |
| 71 | `Spec.Budget.GadgetKeysOK` (`:159`) | no theorem names it; by composition of rows 20 and 70 | [S] `d.key` at every level for the relinearization and rotation keys of every case, decided by `gadgetKeysCheck` (`gadgetKeysCheck_sound`); the restriction ℓ ≤ (chain limbs of the key) that `d.key` adds is mirrored only; count not in the README | `relin_realizable`, `keySwitch_realizable`, `relin_realizable_top`, `keySwitch_realizable_top`, `gadgetKeys_restrict`, `gadgetKeys_restrict_uniform`, `gadgetKeys_restrict_needs_size_bgv` | Respec (by composition) + executed |
| 72 | `Spec.Budget.SpecialOK` (`:196`) | hypothesis of `keySwitch_centred_eq_specialOK`, `specialBasis_odd`; the oddness clause is motivated by `centredModDown_differs'` (P = 2) | [I] `specialOK?` printed in `load.params` | `specialOK?_sound`, `certify?_rejects_badSpecial`, `certify?_rejects_evenSpecial` | pins only |
| 73 | `Spec.Budget.pairwiseCoprime?`, `specialOK?` (`:203,208`) | no | [I] `load.params` | `specialOK?_sound` | pins only |
| 74 | `Spec.Budget.ksBoundAt` (`:215`) | `Respec/Equiv/KsBound.lean` `ksBoundAt_centred_eq`: for `canonical = false`, `keyNoise = t·Be`, `ℓ ≤ L`, `Σ sizes = ℓ`: equal to `⌊ksAddedBound .centred …⌋₊`. `ksBoundAt_canonical_ge`: for `canonical = true` (OpenFHE default build, the case the harness uses) only `⌊B's bound⌋₊ ≤ ksBoundAt`, one direction; strict at `canonical_strict` (60 vs 5191760/86609) | [B] `e.step` on every relinearization and key switch, through `ksBudget` (row 75); `ksBoundAt` of the operand's level is printed in each such line [I]; [A] `algo.relin` (1510 comparisons) and `algo.rotate` (720) are bit-exact for `relinOpenFHE` and `rotateOpenFHE161` (and for the unlocked `keySwitchBGVOpenFHE` forms: 759 and 360 of those comparisons), which `relinOpenFHE_spec` and `rotateOpenFHE161_spec` prove within the bound `ksBoundAt` charges with `canonical = true` (algo README, "What is proved"; not proved as `Spec.Trace` steps there); the 9 algo mutants are caught; the recorded-run `e.step` checks find no key switch above the canonical bound (the budget `ksBoundAt` charges with `canonical = true`) | `relin_realizable`, `keySwitch_realizable` (existential `f`), `ksBoundAt_le_ksBudget`, `ksBoundAt_le_canonical` | Respec + executed (centred: equal up to the floor; canonical: one-sided) |
| 75 | `Spec.Budget.ksBudget` (`:224`) | no | [B] `e.step`: the bound `E.keySwitch` for every relinearization and key switch | `ksBoundAt_le_ksBudget` | executed only |
| 76 | `Spec.Budget.msBudget`, `msBudgetOne` (`:229,234`) | `Respec/Equiv/ModSwitch.lean` `msBudget_vs_B`: `⌊B's bound⌋ ≤ ⌊B/q⌋ + msBudget ≤ ⌊B's bound⌋ + 1` (centred correction, `q > 0`); `msBudgetOne` is the case `D = 0` of `msBudgetAt_vs_B` | [B] `e.step`, `e.modswitch-parts` (through `modSwitchAt`); [A] `algo.modReduce` is bit-exact for the centred switch the budget is for (621 RNS `bgvModSwitchPoly` + 621 integer; mutant `modreduce-canonical` caught; not proved as `Spec.Trace` steps there) | `msBudgetAt_one`, `msBudgetAt_two`, `modSwitch_realizable`, `modSwitch_realizable_one` | Respec + executed |
| 77 | `Spec.Budget.msBudgetAt` (`:240`) | `msBudgetAt_vs_B`: for `D + 1` components `⌊B's bound⌋ ≤ ⌊B/q⌋ + msBudgetAt P (D+1) ≤ ⌊B's bound⌋ + 1` (equal up to rounding); `msCharge_vs_B`; witness `threePart_needs_parts` | [B] `e.step`, `e.modswitch-parts`; on the fixtures 10 three-component switches, all within `msBudgetAt P 3`, 6 above `msBudget`; mutant `ms-parts` caught; [A] `algo.modReduce` as row 76 | `certified_modSwitchAt`, `modSwitch_realizable_parts`, `msBudgetAt_one`, `msBudgetAt_two`; the many-component budget: `Challenge/Budget.lean:233-243` | Respec + executed |
| 78 | `Spec.Budget.certified` (`:247`) | used in the kernel evaluations `threePart_refAnalyze`, `twoPart_nonCentred_exceeds` (witnesses, not equivalences) | [B] the budget of every `e.step` line; [I] `f.budget` | `certified_modSwitchAt`, `certified_sound`, `certified_run_exists` | executed only |

## `Spec/Encrypt.lean`

| # | Definition | Respec | Executed against OpenFHE v1.6.1 | Challenge pins | Class |
|---|---|---|---|---|---|
| 79 | `Spec.Encrypt.liftMsg` (`Spec/Encrypt.lean:75`) | `Respec/Equiv/Encrypt.lean` `liftMsg_eq`: `liftBy .canonical m = liftMsg m`, equality | [D] in `algo.encrypt` (`FHE/Pin/Algo.lean:358`); `c.stored` checks the packed convention (591 of the 790 encryptions in `[0, t)`) | `liftMsg_stored` | Respec + executed |
| 80 | `Spec.Encrypt.PublicKeyOK` (`:79`) | `pkGen_iff`: `PublicKeyOK t Q s e b a ↔ ofInt Q b = (pkGen t s a e).b` (B's OpenFHE key `b = t·e − a·s`), iff, no side condition; `pkGenStd_ok` (B's standard key satisfies it with `−e`) | [D] `c.pubkey` on each case's public key, forced and literal (N ≤ 32), `c.pubkey.literal-vs-forced`; mutant `key-order` caught | hypothesis of `fresh_sound`, `fresh_run_exists` | Respec + executed |
| 81 | `Spec.Encrypt.encrypt` (`:87`) | `encrypt_eq`: for either lift `ml`, `(encrypt t b a (liftBy ml m) u e₁ e₂).map (ofInt Q) = BGV.encrypt ml ⟨ofInt Q b, ofInt Q a⟩ m u e₁ e₂`; `encrypt_eq_liftMsg`, `encrypt_eq_centered`. Not compared for a stored polynomial with `‖p‖∞ > t − 1` | [D] `c.encrypt`: 790 of 790 recorded encryptions equal `encrypt t b a p u e₁ e₂` mod Q (forced `encryptMF .none`, `encryptMF_none`; literal on the 662 at N = 16); `algo.encrypt` 790; `c.stored.exceeds` on the 108 with `‖p‖∞ > t − 1`; mutant `lift` caught | `phase_encrypt`, `encrypt_encrypts`, `encrypt_stored_exceeds` | Respec + executed |
| 82 | `Spec.Encrypt.freshError` (`:91`) | `freshCrit_eq`: B's `freshCrit ml m s e u e₁ e₂ = liftBy ml m + t • freshError s e u e₁ e₂` | [D] `c.phase`: phase = `p + t·freshError` on 790 of 790 (forced `freshErrorF`, `freshErrorF_eq`) | `phase_encrypt`, `freshError_worst`, `freshError_tail` | Respec + executed |
| 83 | `Spec.Encrypt.worstError` (`:96`) | `freshBound_eq` (only at `Bk = B1 = B2 = Be`) | [B] `c.worst`: `‖freshError‖∞ ≤ worstError N 1 39 1 39 39` on 790 of 790 | `freshError_worst`, `freshError_worst_attained` | Respec + executed |
| 84 | `Spec.Encrypt.varProxy` (`:103`) | no | [I] `c.tail` only (790 `null` lines) | `varProxy_ternary`, `freshError_tail` | pins only |
| 85 | `Spec.Encrypt.normSq`, `varProxyL2` (`:106,116`) | no | no | `normSq_le`, `varProxyL2_support`, `freshError_tail_l2` | pins only |
| 86 | `Spec.Encrypt.freshNoise` (`:120`) | `freshBound_eq`: B's `freshBound ml N t Bs Be Bu = freshNoise t (msgBound ml t) (worstError N Bs Be Bu Be Be)`; `freshBound_centred_le` | [B] `c.worst`: noise ≤ `freshNoise t Bp worstError` on 790 of 790 (at the declared `Bp` for 455, at the measured `‖p‖∞` for the 335 without a program) | `encrypt_encrypts`, `fresh_sound` | Respec + executed |
| 87 | `Spec.Encrypt.meanDrift` (`:128`) | no | no (the sampler-mean allowance it pays for, 3431/2⁶⁴, is the tool's declared assumption for OpenFHE's Gaussian sampler) | `meanDrift_spec`, `meanDrift_zero`, `meanDrift_lt` | pins only |
| 88 | `Spec.Encrypt.epsFor` (`:134`) | no | [I] `c.tail` only | `epsFor_spec` | pins only |
| 89 | `Spec.Encrypt.freshOK?` (`:149`) | no | no | `freshOK?_spec` | pins only |
| 90 | `Spec.Encrypt.outputKey?`, `outputsUnderS?` (`:169,175`) | no | no | `outputKey?_eq`, `certify?_rejects_rotatedKey` | pins only |
| 91 | `Spec.Encrypt.certOK?` (`:181`) | no | no | via `certify?_decrypts`, `certify?_rejects_switched` | pins only |

## `Spec/Decrypt.lean`

| # | Definition | Respec | Executed against OpenFHE v1.6.1 | Challenge pins | Class |
|---|---|---|---|---|---|
| 92 | `Spec.Decrypt.switchPhase` (`Spec/Decrypt.lean:29`) | `Respec/Equiv/Bookkeeping.lean` `switchPhase_eq` (`rfl`: it is `Challenge.Source.bgvModSwitchComp`); `switchPhase_round`: one round reduced mod `Q'` = B's `modSwitchElt (.ghs .centred) t q Q'` of the reduction mod `Q'·q`, for `0 < q`, `0 < Q'`, `t` coprime to `q` | [D] inside `a.switched`, `a.switchedQ0`; mutant `switch-centring` caught by `a.switchedQ0`, `a.decbound`, `f.decrypt`; [D] being `rfl` to `Challenge.Source.bgvModSwitchComp`, it is also what `algo.modReduce` runs in integer mode on OpenFHE's `ModReduce` inputs (621 of the 1242, bit-exact) | via `decrypt_switched` | Respec + executed |
| 93 | `Spec.Decrypt.switchDownRev` (`:36`) | per round only (row 92); no theorem for the recursion | [D] literal at every N inside `a.switched` | via `decrypt_switched`, `bgvDecryptSwitched_one` | executed only (Respec per round) |
| 94 | `Spec.Decrypt.bgvDecryptSwitched` (`:44`) | per round only; `Respec/Equiv/Test.lean` section 4 compares it with B's ciphertext-switch decryption on one instance (`#guard`, tested, not proved) | [D] `a.switched`: equals OpenFHE's `Decrypt` (`decrypt.raw`) in all N coefficients on every recorded decryption (forced `decryptSwitchedA`, `decryptSwitchedA_spec`; literal for N ≤ 32; `a.switched.literal-vs-forced`); count not in the README | `decrypt_switched`, `bgvDecryptSwitched_one`, `analyze_decrypt_switched` | executed only (Respec per round) |
| 95 | `Spec.Decrypt.decBoundRev`, `decBound` (`:51,57`) | no | [B] `a.decbound` (switched phase within `decBound` of the measured phase), `f.decrypt` | `decBoundRev_step_le`, `decrypt_switched` | executed only |
| 96 | `Spec.Decrypt.decScale` (`:60`) | no theorem (the `Bookkeeping.lean` docstring identifies it with OpenFHE's `scalingFactorInt` update) | [D] `a.textbook`, `b.raw`, `b.sf` (through `Mut.decScaleM`, `Mut.decScale_none`: `rfl`); mutant `scale-dec` caught (needs `q ≢ 1 mod t`) | `decrypt_switched`, `analyze_decrypt_switched` | executed only |
| 97 | `Spec.Decrypt.decryptOK?` (`:64`) | no | [D] the gate of `a.textbook` (a disagreement while `decryptOK?` holds is a failure); printed by `f.decrypt` | hypothesis of `decrypt_switched` | executed only |
| 98 | `Spec.Decrypt.outputLevel?`, `decryptAllOK?` (`:68,75`) | no | no (run by `fhe_check` through `certOK?`) | `outputLevel?_eq`, `analyze_decrypt_switched` | pins only |

## `Spec/Certify.lean`

| # | Definition | Respec | Executed against OpenFHE v1.6.1 | Challenge pins | Class |
|---|---|---|---|---|---|
| 99 | `Spec.Certify.Mode`, `Input`, `NoiseUsed`, `Certificate` (`Spec/Certify.lean:20,58,75,89`) | no | `Input` is decoded from the extracted programs (151 reproduced) | via the `certify?_*` pins | none (data) |
| 100 | `Spec.Certify.MSMethod` (`:48`) | no | no | `certify?_centred`, `certify?_rejects_nonCentred` | pins only |
| 101 | `Spec.Certify.freshDrift`, `freshEps` (`:110,116`) | no | no | `certify?_fresh`, `certify?_accepts_drift`, `fresh_worst_certified`, `fresh_kappa_certified` | pins only |
| 102 | `Spec.Certify.layoutOK?` (`:126`) | no | no | `layoutOK?_uniform`, `certify?_rejects_badLayout`, `certify?_rejects_nonRestricting`, `certify?_keys_restrict` | pins only |
| 103 | `Spec.Certify.keysRestrict?` (`:132`) | no | no | `certify?_keys_restrict`, `certify?_rejects_keySize` | pins only |

## Locked definitions: `Challenge/Certify/Defs.lean`, `Challenge/Headline/Defs.lean`, `Challenge/FreshNoise.lean`

| # | Definition | Respec | Executed against OpenFHE v1.6.1 | Challenge pins | Class |
|---|---|---|---|---|---|
| 104 | `Challenge.Certify.outputBound?` (`Challenge/Certify/Defs.lean:69`) | no | no | via `certify?_spec`, `certify?_sound`, `certify?_decrypts` | pins only |
| 105 | `Challenge.Certify.checked?` (`:77`) | no | no | via `certify?_paramsOK`, `certify?_spec` | pins only |
| 105a | `Challenge.Certify.inputsMsgOK?` (`Challenge/Certify/Defs.lean:63`) | no | no | `certify?_inputs_exist`, `certifyProfile?_inputs_exist_all`, `certifyProfile?_inputs_checked`, `bgv_low_level_excludes` (`Challenge/Profile/Inputs.lean`), `Challenge.Params.bgv_small_noise_excludes`: acceptance gives the check, and a program it rejects has a message with no input ciphertext; `#guard`s there evaluate the rejections | pins only |
| 106 | `Challenge.Certify.certify?` (`:91`) | no | no `openfhe_pin` check; `fhe_check` runs it, among others on programs extracted from OpenFHE v1.6.1 traces, and `harness/frontend/tests/run.sh` compares the verdicts with `harness/frontend/tests/expected.tsv` (verdict tables, not library behaviour) | `certify?_spec`, `certify?_worstCase`, `certify?_centred`, `certify?_fresh`, `certify?_paramsOK`, `certify?_keys_restrict`, `certify?_sound`, `certify?_decrypts`, `certify?_freshL2`, `certify?_accepts_runDemo`, `certify?_accepts_threeOut`, `certify?_rejects_*` (10 of them) | pins only |
| 107 | `Challenge.Headline.refBound` (`Challenge/Headline/Defs.lean:76`) | no theorem names it; `msBudgetAt_vs_B` compares the arithmetic of its `modSwitch` rule with B's bound | [D]+[B] `f.bound`: `refBound` run per instruction along each of the 151 programs and compared with the measured centred phase (`null` when a wrap is not excluded, when an input exceeds its bound, or for arbitrary inputs) | via `analyze_sound`, `certified_sound` | executed only (bound) |
| 108 | `Challenge.Headline.refRun`, `refAnalyze` (`:101,116`) | only kernel evaluations on witnesses: `threePart_refAnalyze`, `twoPart_nonCentred_exceeds` (not equivalences) | [I] `f.refAnalyze` only | `analyze_sound`, `analyze_tight`, `analyze_accepts_addMul`, `analyze_rejects_nonBGV` (about `FHE.Holes.analyze`, which is `refAnalyze`), `refAnalyze_badDecl`, `certified_sound`, `certified_run_exists`, `analyze_decrypt_switched` | pins only |
| 109 | `Challenge.FreshNoise.coords`, `coordBound`, `SamplerOK` (`Challenge/FreshNoise.lean:154,159,168`) | no | not a check: `c.support` checks each recorded draw's support (`‖u‖∞ ≤ 1`, `‖e₁‖∞`, `‖e₂‖∞ ≤ 39`); the tool's declared assumptions for OpenFHE's samplers: support within the declared bounds and a mean allowance `mn/md = 3431/2⁶⁴` (the `mean` condition fails with `mn = 0` and holds with it); independence is neither tested nor proved | `samplerOK_rademacher` (satisfiable), `subGaussSamplerOK_of_samplerOK`, `freshError_tail` | pins only |
| 110 | `Challenge.FreshNoise.FreshInputs` (`:225`) | no | not as a predicate; its conjuncts on the data: `c.encrypt` (`cts x = encrypt …`, 790 of 790), `c.worst` and `c.ptbound` (`‖p‖∞ ≤ Bp`), `b.msg` (`p mod t` is the message) | used in `fresh_sound`, `fresh_certified`, `fresh_run_exists` | executed only (conjunct-wise) |

## `Spec/Scaling.lean`

| # | Definition | Respec | Executed against OpenFHE v1.6.1 | Challenge pins | Class |
|---|---|---|---|---|---|
| S1 | `Spec.Scaling.upd`, `plainInstr`, `plainRun`, `plainEval` (`Spec/Scaling.lean:108-135`) | no | [D] forced `plainRunA` (`plainRunA_eq`, `plainStepA_eq`, `plainInstrF_eq`, `FHE/Pin/ChecksUser.lean:61,96,110`), literal `plainEval` at small N (`b.user.literal-vs-forced`, `ChecksUser.lean:306-307`): `b.user.decrypt` (`ChecksUser.lean:290`) compares, per output OpenFHE decrypted, `plainEval prog marks u` on the user's messages `u x = sf_x⁻¹ • p_x` with `userDecrypt` of OpenFHE's output ciphertext and with OpenFHE's own reading `decrypt.sf⁻¹ • decrypt.raw`; gated difftest on the committed fixtures: `b.user.decrypt` 390 ok, `b.user.literal-vs-forced` 706 ok (`userDecrypt` and `plainEval` lines together), 0 fail (`harness/openfhe-pin/lean/README.md:52-54`, `difftest-counts.json`); [P] `value_check.py` predicts the stored message, not the plain one | `Challenge.Scaling.eval_scaled`, `certify?_user`, `adjProg_raw_ne_plain` | executed only |
| S2 | `Spec.Scaling.ScaleData`, `inputFactor`, `scaledMsgs` (`:146-158`) | no | `ScaleData` is built as `fhe_check` builds it (`$.scaling` of the committed programs, equal to the extractor's rule on all 151: `fileVsRule`); `inputFactor` literal in `b.user.decrypt` (`ChecksUser.lean:232`); `scaledMsgs`: no | via `eval_scaled`, `certify?_user` | none (data) (`inputFactor`: executed only, as part of S1) |
| S3 | `Spec.Scaling.Fac`, `facInit`, `facStep`, `facRun`, `factors?` (`:163-219`): the library's factor bookkeeping | no | [D] literal: `b.user.factors` (`ChecksUser.lean:205`, `factors?` is `some` on each extracted program: 151 ok); `b.user.decode` (`ChecksUser.lean:265`): the factor and level `decodeAt?` derives through `facStep` = the `scalingFactorInt` OpenFHE's `Decrypt` returned and the ciphertext's towers, 390 ok, 0 fail, all four scaling techniques (`harness/openfhe-pin/lean/README.md:52-56`). That OpenFHE follows `facStep` is not proved (the assumption `Challenge.Scaling` names); these lines are its executed evidence on the fixtures. Also the frontend's untrusted replay (`extract.py` `replay()`) | `eval_scaled`; discrimination `addMismatch_rejected`, `mulPlain_factor_rejected`, `untracked_switch_rejected`, `nonUnit_rejected` | executed only |
| S4 | `Spec.Scaling.decodeFactor`, `decodeAt?`, `userDecrypt` (`:228-239`) | no | [D] `decodeFactor`, `decodeAt?` literal in `b.user.decode` (390, row S3) and printed by `b.user.scaleOK`; `userDecrypt` forced (`userDecryptA_spec`, `ChecksUser.lean:124`) in `b.user.decrypt` (390, row S1); its literal counterpart in `b.user.literal-vs-forced` evaluates the unfolded body (`dF⁻¹ • bgvDecryptSwitched …`, `ChecksUser.lean:304`), not the name; [P] `value_check.py` compares Decrypt's `scalingFactorInt` with its replayed scale | `certify?_user`, `adjProg_raw_ne_plain` | executed only |
| S5 | `Spec.Scaling.scaleOK?` (`:247`) | no | [D] literal: `b.user.scaleOK` (`ChecksUser.lean:211`) asserts `scaleOK? = true` on each of the 151 extracted programs (scaling data from the recorded factors), 151 ok; what it is compared with is the premise checked by `b.user.decode` (row S3). Also run by `fhe_check` on the OpenFHE extractor's `$.scaling` data (one report line); all 37 certified OpenFHE BGV examples covered, 3 negatives in `harness/frontend/tests/negative/scaling_*` | `certify?_user`, `adjProg_accepted` and the rejection pins | executed only |

## Locked word condition: `Challenge/Word.lean`

| # | Definition | Respec | Executed against OpenFHE v1.6.1 | Challenge pins | Class |
|---|---|---|---|---|---|
| 111 | `Challenge.Word.accOK?`, `ksWordOK?` (`Challenge/Word.lean:44,50`): the machine-word side condition of OpenFHE's hybrid key switching (BGV and BFV; every word operation on these paths was audited by reading) | no | no: `openfhe_pin` does not evaluate it; `fhe_check` evaluates it on every OpenFHE file of either scheme and withholds the certificate where it fails (`FHE/Check/Report.lean:679-692`); `certify?` and `certifyBFV?` do not read it | `modUp_acc_no_overflow`, `modDown_acc_no_overflow`, `acc_wraps_without`; `#guard`s at `Challenge/Word.lean:78-83` | pins only |

## `Spec/MSB.lean`, `Spec/MSBScale.lean` (BGV in MSB form)

OpenFHE stores BGV in LSB form, so no row here is executed against it. `harness/lattigo-pin` checks Lattigo's recorded ciphertexts through a t-reading against the LSB contracts of `Spec/Trace.lean` (rows 55-63); it does not run the definitions below.

| # | Definition | Respec | Executed against OpenFHE v1.6.1 | Challenge pins | Class |
|---|---|---|---|---|---|
| M1 | `Spec.MSB.toLSB`, `msbDecrypt`, `MSBEncrypts`, `MSBEncryptsRep` (`Spec/MSB.lean:89,93,99,109`) | no | no | `msbDecrypt_toLSB`, `msbDecrypt_iff`, `msbEncrypts_toLSB`, `toLSB_msbEncrypts`, `toLSB_encrypts_of_rep`, `msbEncryptsRep_toLSB` | pins only |
| M2 | `Spec.MSB.KeyValidMSB`, `divRound`, `rescale`, `mulTensor`, `GadgetKeysOK`, `gadgetProduct`, `keySwitch`, `relin` (`:117,123,127,132,145,154,163,172`) | no | no | `keyValidMSB_iff`, `gadgetKeysOK_iff`, `keyValidMSB_toLSB`, `gadgetKeys_restrict`, `keySwitch_stepOK`, `relin_stepOK`, `rescale_stepOK`, `mulTensor_stepOK`, `keySwitch_toLSB`, `relin_toLSB`, `rescale_toLSB`; Lattigo's transcriptions: `relin_meets_msb`, `keySwitch_meets_msb`, `rescale_meets_msb` (`Challenge/Instances/Lattigo/MSB.lean`) | pins only |
| M3 | `Spec.MSB.toLSBEnv`, `Encrypts`, `InputsOK`, `StepOK`, `Run` (`:180,185,194,201,235`) | no | no | `stepOK_toLSB`, `run_toLSB`, `certifyProfile?_sound_msb` | pins only |
| M4 | `Spec.MSBScale.decodeAt?`, `userDecrypt`, `scaleOK?` (`Spec/MSBScale.lean:48,56,62`) | no | no | `Challenge.MSBScale.certifyProfile?_user_msb` | pins only |

## Definitions with no external evidence

The rows classed `pins only` or `none`: no `Respec` equivalence and no check that compares them with OpenFHE's behaviour. Some are run or printed without an assertion, or have their conjuncts checked separately, as their rows say (`Encrypts`, `InputsOK`, `BoundsOK`, `Decl.ok`, `schemeParamsOK?`, `specialOK?`, `refAnalyze`).
- Storage level (by design not compared with OpenFHE): `Spec/Layout.lean` (row 33); `FullParams.allLimbs`, `ParamsOK`, `limbOK?`, `paramsOK?` (rows 39, 41, 44).
- Certificate layer, pins only: `SchemeParamsOK`, the primality test, `schemeParamsOK?`, `SpecialOK`, `pairwiseCoprime?`, `specialOK?` (only printed, rows 40, 42-43, 72-73); `cutSizes`, `restrictsTo` (row 65); `varProxy`, `normSq`, `varProxyL2`, `meanDrift`, `epsFor`, `freshOK?`, `outputKey?`, `outputsUnderS?`, `certOK?` (rows 84-85, 87-91); `outputLevel?`, `decryptAllOK?` (row 98); `MSMethod`, `freshDrift`, `freshEps`, `layoutOK?`, `keysRestrict?` (rows 100-103); `outputBound?`, `checked?`, `certify?`, `refRun`, `refAnalyze` (rows 104-106, 108); `SamplerOK` (row 109); `Encrypts`, `InputsOK`, `BoundsOK`, `Decl.ok` (rows 48, 50, 61, 24).
- Locked word condition, pins only (evaluated by `fhe_check`, compared with nothing): `accOK?`, `ksWordOK?` (row 111).
- BGV in MSB form: rows M1-M4.
- None at all: the anchors `Quot`, `toPolynomial`, `toQuot` (row 6, by design), `Spec.NPoly.canonical` (row 9), `inputVal`, `initCt`, `CtEnv` (rows 49, 58, 60), and the data types.

## Open items

- `Respec`'s key-switching rule `KeySwitchRule` for its own key generator, an arbitrary `sFrom` and either lift is open and not stated as a theorem (`Respec/Equiv/Rules.lean`, the `KeySwitchRule` row); it is proved for keys valid in the sense of `Spec`. For canonical lifts `Spec`'s `ksBoundAt` is weaker than `Respec`'s constant (`ksBoundAt_canonical_ge`, `canonical_strict`). Key switching is covered by bit-exact execution instead.
- `ModSwitchRule .canonical` is not stated as a theorem anywhere (`Respec/Equiv/Rules.lean`); `FreshRule` is not covered at t = 1; `encrypt` with a stored polynomial of norm above t − 1 is not compared with `Respec` (`Respec/Equiv/Encrypt.lean`).
- `Challenge/Realize.lean` names locked transcriptions of the functions `algo.relin`/`algo.rotate` compare bit-exactly (`Challenge/Realize/OpenFHE.lean`) and proves they meet the step contracts; their equality with `keySwitchBGVOpenFHE`/`rotateOpenFHE161` is kernel-checked in `FHE/Realize/` but not locked. `Challenge.Budget.relin_realizable`/`keySwitch_realizable` remain existential.
- `Spec/Budget.lean:41` comments on the `canonical` flag of `ksBoundAt`. The flag is a declaration by the extractor (`canonical = true` for OpenFHE's default build); `ksBoundAt` is proved equal to the centred bound only for `canonical = false` (row 74). Nothing in the gate depends on the comment's source.
- The gated conformance suite is the committed fixtures, N = 16 and 64.
- EvalSum and EvalInnerProduct outputs are not compared: 16 ciphertexts in 11 cases (`algo.coverage` `null`); the extractor refuses those programs.
- The ψ-ordering of OpenFHE's NTT is not checked (row 32 and the `Spec/Layout.lean` note).
- Per-check line counts of `openfhe_pin` are committed as data (`harness/openfhe-pin/results/difftest-counts.json`, `perCheck`); most rows above do not quote them.
- BFV rows: `docs/TRUSTED-DEFINITIONS-BFV.md`.
