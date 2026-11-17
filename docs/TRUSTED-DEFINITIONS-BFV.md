# Trusted definitions and their evidence: BFV

The BFV rows of the table `docs/TRUSTED-DEFINITIONS.md` describes (the project's criterion:
every trusted definition is proved equal to `Respec` or executed against OpenFHE, and a table says
which). Same columns and kinds of execution as that file ([D] the definition itself executed,
literally or in a forced form proved equal; [S] a trusted predicate decided by a function proved
sound; [B] a computed bound compared with a measured norm; [A] a proved or locked algorithm
compared bit for bit with OpenFHE's output; [I] information only; [P] untrusted Python mirror only),
except that the Respec column is folded into an "Other" column (`Respec/Equiv/BFV.lean` has
`bfvDecrypt_eq`, `bfvEncrypts_iff`) and there is no review column (review reports are not published).

**Data.** Upstream OpenFHE v1.6.1, commit `b59e1f29`, with the observation-only tracer
(`harness/openfhe-pin/fixtures/SOURCE-bfv.txt`; recorded from a single-threaded build, `WITH_OPENMP=OFF`,
`-O3 -DNDEBUG -std=gnu++17`, no `-march`, no fast-math, `FLT_EVAL_METHOD` 0, no FMA instruction in the library). Counts are from
the GATED suite, `harness/openfhe-pin/difftest.sh` on the committed `fixtures-bfv.tar.xz` (BFV part, as recorded in `harness/openfhe-pin/results/difftest-counts.json`: 91243 check lines, 78291 ok, 0 fail, 12952 null; `algo.*` lines 25588 ok, 0 differing): 241 cases
(213 at N = 16, 28 at N = 64 of which 16 are hand-built adversarial inputs), all four multiplication
techniques (HPS, HPSPOVERQ, HPSPOVERQLEVELED including contexts with every technique left at its
default, BEHZ), HYBRID and BV key switching, 30/45/60-bit limbs, t = 65537 / 786433, depth 1–6,
internal drops of HPSPOVERQLEVELED on products, relinearisations and rotation key switches (drops 1–3);
189 programs extracted, 52 refused by the extractor (each refusal tested). Not gated, run on the same
build (`harness/openfhe-pin/fixtures/README-bfv.md`, "Larger suites"): `bfv-mid` (90 cases,
N = 256–2048), `bfv-adv` (320 adversarial cases, N = 16–4096), `bfv-real` (53 cases, N = 4096–32768,
48 checked by the contract checks within a 3-hour box; every key switch with an internal drop
checked bit for bit). Mutation: `harness/openfhe-pin/mutants.sh` (gate step 7).

Line numbers are of this release.

## `Spec/TraceBFV.lean`

| Definition | Executed against OpenFHE v1.6.1 | Other | Class |
|---|---|---|---|
| `Budget` (`:71`), `Bnd` (`:88`) | n/a (data) | | none (data) |
| `PlainOK` (`:98`) | [S] `inputPtOKb` (`inputPtOKb_sound`, `FHE/Pin/BFV/Sound.lean`) on every plaintext input (`c.input`) | | executed (sound decider) |
| `inputBound` (`:105`) | [D] literal: the bound every `c.input` line uses | | executed |
| `InputsOK` (`:113`) | [S] per input: `inputOKb` (`inputOKb_sound`): `c.input` 1249 lines on the 241 fixtures, 0 fail (`harness/openfhe-pin/results/difftest-counts.json`, `bfv.perCheck`); every recorded fresh input is within the declared bound | | executed (sound decider, conjunct per input) |
| `StepOK` (`:123`) | [S] `stepOKb` (`stepOKb_sound`) at the budget `certifyBFV?` charges for that instruction (`budgetBFV x k`, equal to `c.budget k`: `f.budget`): `e.step` on every instruction of every extracted program, all 13 instruction kinds the extractor emits (add, sub, addPlain, subPlain, mulPlain, mul, square, mulConst, relin, keySwitch, automorph, modSwitch, copy), 0 fail; `harness/openfhe-pin/lean/coverage.py`: all 66 instruction shapes (op × operand components × technique × key switching) the extractor can emit are covered by an accepting line. Mutants caught: `delta-ceil`, `mul-no-t`, `mulround-zero`, `mullift-zero`, `ks-zero`, `ms-zero`, `plainadd-zero`, `wrong-technique`, `slack-idealised`, `mulround-textbook`, `automorph-index`, `mul-cyclic`, … (19 of 24) | the extractor refuses programs with one operation pattern whose steps the contract does not cover | executed (sound decider; completeness not proved) |
| `Run` (`:175`), `RunAt` (`:189`) | not as a predicate: every step of a recorded run by `e.step`; `f.certified-consistent`: no CERTIFIED program has a violated step | | executed (step-wise) |

## `Spec/BudgetBFV.lean`, `Spec/BudgetBFVRns.lean`

Every number is executed literally inside `budgetBFV` / `slacksAt` on every fixture (`f.budget`) and
is the bound of the `e.step` lines above. What the recorded executions say about each constant
(the budget held on every recorded step of the fixtures and `bfv-adv`; where a margin is stated it is the smallest over them):

| Definition | Measured against the budget | Mutant | Class |
|---|---|---|---|
| `ksBoundAt`, `ksBudget`, `unitPlain` (`BudgetBFV:39-46`), `ksLeveled` (`BudgetBFVRns:185`) | the budget held on every recorded key switch | `ks-zero` caught; `ks-half` SURVIVES (documented): no recorded key switch comes within a factor two of the budget | executed; loose |
| `msBudget` (`:50`) | Compress: ⌈‖δ‖/q⌉ ≤ 3 against 9 | `ms-zero` caught; `ms-half` survives | executed; loose |
| `mulLift` (`:54`), `mulLiftNormAt` (`BudgetBFVRns:78`) | lift witness ‖k‖ 1.2–4.9 bits below | `mullift-zero` caught; `mullift-half` survives | executed; loose |
| `mulRound` (`:58`), `mulRoundApprox` (`BudgetBFVRns:41`), `hpsSlack`/`poverqSlack`/`leveledSlack`/`behzSlack` (`BudgetBFVRns:130-172`), `doubleSw`/`doubleSr`/`floatDen` (`BudgetBFVRns:105-114`) | rounding ⌈2‖D‖/Q⌉: 3.8–6.4 bits below (BEHZ), 4.3–14.9 (HPS), 6.3–19 (P-over-Q); 0.02 bit on a hand-built bfv-adv product. Measured above the textbook value (HPS −5 bits, P-over-Q −14, leveled with a drop −44 to −136) and above the idealised exact-arithmetic slack: the binary64 tolerance is used | `mulround-zero`, `mulround-textbook`, `slack-idealised`, `wrong-technique` caught; `mulround-half` survives | executed; the float slack is necessary |
| `plainAddRoundedAt`, `plainAddRounded`, `plainAddScaledAt`, `plainAddScaled` (`BudgetBFVRns:44-58`) | the library adds ⌈Q·p/t⌉ (`c.timesQovert`, `algo.addPlain`): deviation reaches `plainAddScaled` to within 0.04 bit. `plainAddRounded` (the maximum over the levels) is not a budget `certifyBFV?` charges: it is only printed (`rounded` on the `e.step` lines of plaintext additions, `FHE/Pin/BFV/ChecksProg.lean:236`) and used by the mutant `plainadd-rounded` | `plainadd-zero` caught; `plainadd-rounded` survives (0.04 bit) | executed; tight |
| `certified`, `budgetOf`, `Slack`, `ceilDiv` | through the above | | executed |
| `mulLiftApprox` (`BudgetBFVRns:37`), `certifiedApprox` (`BudgetBFVRns:64`) | not executed: no caller in `FHE/` or `Challenge/CertifyBFV/` was found (`certifyBFV?` builds its budgets with `budgetOf`); pins `Challenge.BFVMul.stepOK_mul_approx`, `stepOK_square_approx`, `certifiedApprox_sound`, `#guard`s `Challenge/BFVMul.lean:98-102`, `:626-628` | none | pins only |

## `Spec/CertifyBFV.lean`

| Definition | Executed | Class |
|---|---|---|
| `Technique`, `PlainAddMethod`, `InputBFV`, `AssumptionBFV`, `CertificateBFV` (`:19-104`) | data; built from every extracted program exactly as `fhe_check` builds it (`FHE.Check.BFV.inputBFV`); `f.verdict`: 176 CERTIFIED (with and without `binary64`), 13 NOT CERTIFIED, 0 CERTIFIED with a violation | none (data), exercised |
| `AssumptionBFV.binary64Dec` (`Spec/CertifyBFV.lean:100`): the hypothesis that OpenFHE's decryption of the outputs computes its binary64 steps in an arithmetic conforming to `Spec.DecryptBFV.ConformsD` | data; recorded by `certifyBFV?` exactly when the declared technique is one of OpenFHE's four (`Challenge.CertifyBFV.certifyBFV?_assumed`, `Challenge/CertifyBFV.lean:573`, clause `:590`; `#guard`s from `:624`); it is the hypothesis `hA : ConformsD A` of `Challenge.BFVDecryptLib.certifyBFV?_decryptsLibExt` (`Challenge/BFVDecryptLib.lean:73`); printed by `fhe_check` (`FHE/Check/BFVReport.lean:180,194-195`). Recorded on all 176 CERTIFIED fixture programs (`harness/openfhe-pin/results/difftest-counts.json`, `bfv.certifiedByAssumed`). That the executed arithmetic conforms is not proved (row `ArithD`, `ConformsD` below) | none (data) |

## `Spec/Scheme.lean` (BFV part), `Spec/Correct.lean` (`Encrypts`, BFV branch)

| Definition | Executed | Class |
|---|---|---|
| `roundDiv`, `bfvDecrypt` | [D] `decryptBFVA` (`decryptBFVA_spec`): `a.decrypt` on every recorded decryption = OpenFHE's `Decrypt` (exact rounding) except 22 ciphertexts whose noise is outside `decLibOK?` (null, reason given); `b.msg`/`b.raw` | Respec: `bfvDecrypt_eq` | Respec + executed |
| `BFVEncrypts`, `Encrypts` (BFV) | [S] `inputCtOKb` (`inputCtOKb_sound`) and `noiseA` (`noiseA_spec`) | Respec: `bfvEncrypts_iff` | Respec + executed |

## `Spec/EncryptBFV.lean`

| Definition | Executed | Class |
|---|---|---|
| `scaleUpCeil` (`:84`) | [D] `c.timesQovert`: residues = the library's own `TimesQovert`, 640 encryptions, all equal | executed |
| `encryptBFV` (`:91`) | [D] `c.encryptBFV` (forced `encryptBFVF`, `encryptBFVF_eq`; literal at N ≤ 32): 638 STANDARD encryptions = OpenFHE's ciphertext; EXTENDED: null (out of the definition's scope; refused by the extractor). Mutants `delta-round`, `enc-floor` are caught only by the mirrored `c.predict` | executed |
| `encodeDev`, `freshNoiseBFV`, `freshInputNoise`, `freshOKBFV?`, `FreshModeBFV`, `FreshCertBFV` | [B] the declared input noise vs the measured fresh noise (`c.fresh`, `c.input`) | executed (bounds) |
| public key `PublicKeyOK 1 …` | [D] `c.pubkeyBFV` (`pubKeyF_iff`), 241 | executed |

## `Spec/DecryptBFV.lean`

| Definition | Executed | Class |
|---|---|---|
| `tables`, `frac`, `theta`, `invMod`, `Tab` (`:189-212`) | [D] `a.decryptLib.tables` under `FHE.Float.RNE.rneA`: equal, bit pattern for bit pattern, to the library's four tables (190 contexts; BEHZ computes none) | executed |
| `decrypt1`, `bfvDecryptLib`, `words`, `allWords`, `intSum`, `floatSum`, `floatSumInt`, `quot`, `reduced`, `residues`, the word helpers `msb`, `isPow2`, `mulFast`, `addFast`, `subFast`, `lshift`, `rshift`, `modMulConst`, `truncU64` and the path selectors `qMSB`, `sizeQMSB`, `qMSBHf`, `pathSplit`, `pathReduce` (`:129-286`; the word level: see the word audit) | [D] `a.decryptLib` (and `algo.decrypt`; `FHE/Pin/BFV/ChecksEnc.lean:240,253`, `FHE/Pin/BFV/Algo.lean:1245,1253`): OpenFHE's unreduced raw output on every one of 2165 HPS-family decryptions, coefficient by coefficient, including outputs equal to t; split/unsplit × reduced/unreduced paths; the power-of-two-t path is NOT exercised (no fixture has such t) | executed (power-of-two t: none) |
| `decParamsOK?`, `decLibOK?`, `wordCaps`, `caps`, `sumErr`, `intMax`, `floatMax`, `delta`, `overshoot` (`:297-346`) | [B] `a.decryptLib.textbook`: wherever `decLibOK?` holds at the measured noise, the library output equals textbook decryption (2143), elsewhere null (22) | executed (bounds) |
| `ArithD`, `ConformsD`, `exactD` | data / model; the executed arithmetic is `FHE.Float.RNE` (correctly rounded binary64, not proved to conform) | none (model) |

## `Spec/DecryptBFVLow.lean`, `Spec/DecryptBFVBEHZ.lean`, `Spec/DecryptBFVLib.lean`

The library's decryption of a ciphertext below the top level (every technique) and of a BEHZ ciphertext at the top level. What runs where:
- In the gated difftest only the top-level HPS-family routine runs as a trusted definition (`decrypt1`, `bfvDecryptLib`, section above). For the two routines here, the gate's `algo.decrypt` lines with `impl` `mirror-only` (`FHE/Pin/BFV/Algo.lean:1273`) compare OpenFHE's output with untrusted Lean mirrors (`decSmallF`, `decBehzF`, `FHE/Pin/BFV/Routines.lean:119,98`) that are NOT proved equal to these definitions (2923 `mirror-only` comparisons, 0 differing, all three routines together: `difftest-counts.json`, `bfv.algo.byCheck`; no per-routine count is committed).
- The trusted coefficient functions themselves run in 35 `#guard decLow1 …` and 12 `#guard behz1 …` of `FHE/Float/RNELow.lean`, checked when the `FHE` library builds: residue vectors given to OpenFHE v1.6.1's `Decrypt` and the values it returned.
- [P] A literal Python mirror of these functions was compared with the library outside the gate; that harness is not part of this release.

| Definition | Executed | Other | Class |
|---|---|---|---|
| `Spec.DecryptBFVLow.topBitMask`, `modSubLane`, `centeredCorrectionLane`, `multDHi`, `divD`, `generalShrink`, `switchModulus` (`Spec/DecryptBFVLow.lean:78-126`): the vector modulus switch | inside `decLow1` (below); the word level: see the word audit | `Challenge.BFVDecryptLow.switchModulus_spec` | executed (inside the `decLow1` `#guard`s only) |
| `qlInvModq`, `dropLastElementAndScale`, `dropAll` (`:135-151`) | inside `decLow1` | `dropAll_spec`, `dropAll_noise` | executed (inside the `decLow1` `#guard`s only) |
| `multiplyAndRound`, `multiplyAndRoundVec` (`:160-167`) | inside `decLow1` | `multiplyAndRound_err`, `roundStep_exact` | executed (inside the `decLow1` `#guard`s only) |
| `decLow1` (`:174`) | [D] literal (arithmetic `FHE.Float.RNE.rneA`) in 35 `#guard`s on recorded library values; [P] a Python mirror outside the gate (not part of this release); in the gate only the mirror `decSmallF` | `decLow1_correct` | executed (`#guard`s on recorded values; not in `openfhe_pin`) |
| `bfvDecryptLow` (`:182`) | no: not applied to a ciphertext by any check (`decLow1` is its coefficient function) | `bfvDecryptLow_correct` | pins only |
| `decLowParamsOK?`, `lowErr`, `lowNoise`, `decLowOK?` (`:193-213`) | evaluated by `fhe_check` (`FHE/Check/BFVReport.lean:472-475`) and inside `decryptLibExtOK?` (locked checks below); no gated line compares them with a measured noise | `decLowOK?_t_lt`, `lowMargin_needed`, `#guard`s `Challenge/BFVDecryptLow.lean:152-169` | pins only |
| `Spec.DecryptBFVBEHZ.gamma`, `tgamma`, `prepModMulConst`, `modMulFastConst`, `modAddFastEq`, `negInvqModtgamma`, `tgammaQHatInvModq` (`Spec/DecryptBFVBEHZ.lean:46-72`): the constant, the word operations and the tables | inside `behz1` (below); the word level: see the word audit | `Challenge.BFVDecryptBEHZ.modMulFastConst_spec` | executed (inside the `behz1` `#guard`s only) |
| `behz1` (`:78`) | [D] literal in 12 `#guard`s on recorded library values; [P] a Python mirror outside the gate (not part of this release); in the gate only the mirror `decBehzF` | `behz1_exact`, `behz1_correct` | executed (`#guard`s on recorded values; not in `openfhe_pin`) |
| `bfvDecryptBEHZ` (`:90`) | no: not applied to a ciphertext by any check | `bfvDecryptBEHZ_correct` | pins only |
| `behzParamsOK?`, `decBEHZOK?` (`:98,108`) | evaluated by `fhe_check` (`FHE/Check/BFVReport.lean:460-463`) and inside `decryptLibExtOK?`; no comparison with OpenFHE | `behzParamsOK?_t_lt`, `behzMargin_needed`, `#guard`s `Challenge/BFVDecryptBEHZ.lean:87-94` | pins only |
| `Spec.DecryptBFVLib.bfvDecryptOpenFHE` (`Spec/DecryptBFVLib.lean:28`): which routine `PKEBFVRNS::Decrypt` runs | no: the dispatch itself is not executed; its branches are the rows above and `bfvDecryptLib` | `Challenge.BFVDecryptLib.output_decryptLibExt`, `certifyBFV?_decryptsLibExt` | pins only (each branch: its own row) |

## Locked checks (`Challenge/`)

| Definition | Executed | Other | Class |
|---|---|---|---|
| `Challenge.CertifyBFV.plainBoundsOK` (`Challenge/CertifyBFV/Defs.lean:229`): every plaintext input's declared bound is at least `⌊t/2⌋`; item of `checksOK` and of `certifyBFVProfile?` | evaluated by `fhe_check` with the decision; no comparison with OpenFHE | `certifyBFVProfile?_plain_checked`, `certifyBFV?_inputs_exist` (`Challenge/Profile/Inputs.lean`): acceptance gives it, and without it some message has no plaintext within the bound (`bgv_small_noise_excludes`) | pins only |
| `Challenge.BFVDecryptLib.techLib?`, `outputLibOK?`, `decryptLibExtOK?` (`Challenge/BFVDecryptLib.lean:30,38,47`) | `fhe_check` certifies only where `decryptLibExtOK?` holds (`FHE/Check/BFVReport.lean:47-48`; its fast form is related to it by `Challenge.Fast.decryptLibExtFast_eq`); in the gate it is computed only for the information line `f.verdict` (`toolAgrees`, `FHE/Pin/BFV/ChecksProg.lean:726`); no check compares it with OpenFHE | `output_decryptLibExt`, `certifyBFV?_decryptsLibExt`, `decryptLibOK?_ext`, `#guard`s `:94-100` | pins only |
| `Challenge.BFVMul.behzWordOK?`, `BEHZ.skAlpha1` (`Challenge/BFVMul/BEHZWord.lean:78,67`): the machine-word condition of OpenFHE's BEHZ multiplication (see the word audit) | read by `certifyBFV?` for a BEHZ multiplication (`Challenge/CertifyBFV/Defs.lean:281`), so evaluated wherever `certifyBFV?` runs on such a program (in the gate: the information line `f.verdict`); explained by `fhe_check` (`FHE/Check/BFVBudget.lean:259-260`); no check compares it with OpenFHE | `behz_sk_alpha_ge`, `sk1_alpha`, `#guard`s `:117-121` | pins only |

## `Spec/IndCpaD*.lean`: the security games

These files define the security games and schemes of the IND-CPA-D reduction (`Challenge/IndCpaD.lean`, `Challenge/IndCpaD/`). They
are not executed against OpenFHE: the pins are self-consistency theorems about the modelled schemes,
and no recorded run compares with them. Nothing here is a claim about OpenFHE's implementation.

| Definition | Executed | Pinned by | Class |
|---|---|---|---|
| `Spec/IndCpaD.lean`: the IND-CPA-D game (Li–Micciancio, for exact schemes) on a declared circuit class, the multi-query IND-CPA game, the reduction `reduce` (it takes the public key only), `Correct`, `TapeOK`, `Bounded` | no | `Challenge/IndCpaD.lean`: `gameD_eq_gameCPA`, `prob_eq`, `prob_le` | self-consistency only, not executed |
| `Spec/IndCpaDBFV.lean`: the BFV instance's data (`Setting`, `Circ`, `PK`, `SK`), `enc` (= `encryptBFV` at the top level), textbook `dec`, `sem` (= `Source.eval`), `KeysOK`, `GoodE`, `ksKeysIn`, `Circ.extraOK`, and a decidable-equality instance on polynomials | no | `Challenge/IndCpaD.lean`: `correct`, `bfv_prob_eq`, `bfv_prob_le`, `keysOK_exist`, `admissible_tiny`, compiled checks at a realistic parameter set | self-consistency only, not executed |
| `Spec/IndCpaDProfile.lean`: the abstract RNS BGV/BFV scheme `AbsScheme` with no library in it (`Spec/IndCpaDProfile.lean:48`): abstract keys, randomness, encryption and circuits, textbook decryption at the ciphertext's level (`decBFV`, `decBGV`, `:93,97`), `sem` (= `Source.eval`, `:101`), and the encryption hypotheses `EncOKBFV`, `EncOKBGV` (`:115,123`) | no | `Challenge/IndCpaD/Profile.lean`, `ProfileBGV.lean`, `ProfileAdv.lean`: `correct_bfv`, `bfv_prob_eq`, `bfv_adv_le` and the BGV twins; instances in `ProfileInstances.lean`, `ProfileBGVInstances.lean`, `ProfileBGVKS.lean` | self-consistency only, not executed |
| `Spec/IndCpaDLM.lean`: the game with evaluation on earlier results: the global program `Global` (`:68`) with the declared constant bounds of every inlined query, its reachable set `Reach` (`:137`), admissibility on the inlined program `admLM` (`:127`), `evalLM` (`:156`), the game `gameLM` (`:222`), the fresh-only scheme `freshScheme` (`:181`) and the reduction `reductionLM` (`:248`) | no | `Challenge/IndCpaD/LM.lean`: `gameLM_eq_gameCPA`, `probLM_eq`, `probLM_le`, `advLM_le`; `LMCompose.lean`, `LMAgree.lean`, `LMEmbed.lean`, `LMBFV.lean`, `LMExact.lean` | self-consistency only, not executed |
| `Spec/IndCpaDSanity.lean`: `CpaBounded` and the `swap` maps (`:24-57`), read by no game, reduction or headline statement | no | `Challenge/IndCpaD/Sanity.lean`: `reduction_cpaBounded`, `reduceLM_cpaBounded`, `gameD_swap`, `gameCPA_swap`, `gameLM_swap`, `sim_iff` and the rest of that file | vocabulary for the sanity statements |

## `Spec/Float.lean`

| Definition | Executed | Class |
|---|---|---|
| `u`, `InRange`, `Rounds`, `Arith`, `Conforms`, `Sums`, `exact` | the arithmetic `A64` (executable correctly rounded binary64 on ℚ, `FHE/Pin/BFV/Float64.lean`; NOT proved to satisfy `Conforms`) reproduces every library multiplication bit for bit; the exact arithmetic `exact` (= the idealised algorithms) differs from the library on 43 % of coefficients of the fixtures (29438 of 68544 over 413 products; `harness/openfhe-pin/results/difftest-counts.json`, `bfv.idealMul`), 65 % at real sizes (bfv-real; not in a committed output); with every step fused (FMA) on 9.5 % of the fixtures' coefficients, 17 % at real sizes. `harness/bfv-float/difftest.sh`: the library's tables and the outputs of its `SwitchCRTBasis`/`ScaleAndRound` equal the Python transcription, all errors within `doubleSw`/`doubleSr` | executed (model satisfiability not checked against the hardware) |

## Locked algorithm definitions (`Challenge/`) compared bit for bit ([A])

| Definition | Evidence (gated fixtures) |
|---|---|
| `Fl.hpsMul`, `Fl.poverqMul`, `Fl.leveledMul` (`Challenge/BFVMul/Float.lean`) with `Fl.floatSums A64`; `behzMul` | `algo.mul`: 1466 products / 223 k coefficients, 0 differing (literal at N ≤ 16, forced proved equal at N ≤ 256, array mirror at every N); P-over-Q `EvalSquare` = `poverqMul c c`; mutants of every convention (fma, exact sums, ½ offset, floor, digit centring, aux order, operand roles, drop ignored, Montgomery and Shenoy–Kumaresan steps) caught |
| `Fl.leveledKS` with `Fl.scaleDown`/`scaleUp` (`Challenge/BFVMul/KSLeveled.lean`) around `ksBFV` | `algo.relin.leveled` 96, `algo.rotate.leveled` 23 on the fixtures; all 42 drop key switches of bfv-real (N up to 32768, drops 1–3, HYBRID and BV): bit-exact |
| `Challenge.Realize.relinBFV`, `keySwitchBFV`, `rotateBFV`, `ksBFV` (`Challenge/Realize/OpenFHEBFV.lean`) | `algo.relin` 1303, `algo.rotate` 234: bit-exact (HYBRID staged form proved equal through `ksStaged_openfhe` and `FHE.RealizeBFV.ksHybrid_toRNS`); BV with a digit size > 0: no definition (refused by the extractor) |
| `Challenge.CertifyBFV.runLibrary` (`Challenge/CertifyBFV/Library.lean`) | `algo.runLibrary` on every program that passes `certifyBFV?`, at N = 16 and N = 64 in the fixture suite (176 programs: 151 at N = 16, 25 at N = 64; 1472 instructions, 1323 ciphertexts, 159 k coefficients; `harness/openfhe-pin/results/difftest-counts.json`, `bfv.runLibrary`): every intermediate and output equals OpenFHE's, 0 differing (forced form proved equal: `runLibrary_forced`). The real-size suite (`harness/openfhe-pin/realsize/README.md`, `library.md`) also executes it at N = 8192, 16384 and 32768: 33 of the 35 certified programs, every intermediate and output ciphertext equal, 0 differing (two 11-limb cases timed out) |
| `bfvModSwitchComp` | `algo.compress` 102: bit-exact |
| `bfvAddPlain`, `bfvAddPlainRounded`, `scaleUp` (`Challenge/BFVMul.lean`) | variant lines only: the library adds ⌈Q·p/t⌉ (= `Spec.EncryptBFV.scaleUpCeil`), which neither ⌊Q/t⌋·p nor the rounding matches |

## Not covered

- Decryption of BEHZ and of ciphertexts below the top level: trusted definitions exist
  (`Spec/DecryptBFVBEHZ.lean`, `Spec/DecryptBFVLow.lean`), but the gate compares OpenFHE's output only
  with untrusted Lean mirrors and with textbook `bfvDecrypt`; the definitions themselves run only in the
  47 `#guard`s of `FHE/Float/RNELow.lean`, and their Python mirror outside the gate (not part of this release).
- EXTENDED encryption (no trusted definition; refused).
- BV key switching with a digit size > 0 (no definition; refused).
- The power-of-two-t branch of `decrypt1`.
- `Spec.Float.Conforms A64` (the executed binary64 model) is not proved; nor is `Spec.DecryptBFV.ConformsD`
  for the arithmetic `FHE.Float.RNE` that runs the decryption (the hypothesis `binary64Dec` records).
- `ksWordOK?` (the word condition of hybrid key switching, `docs/TRUSTED-DEFINITIONS.md` row 111) is
  evaluated by `fhe_check` only, not compared with OpenFHE.
- Completeness of the sound deciders: a failing `e.step` says only that the witnesses tried fail.
- Five bfv-real cases (N = 16384–32768) not finished by the contract checks in the time box.
