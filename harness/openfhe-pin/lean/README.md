# openfhe_pin: the Lean checker of the OpenFHE differential harness

`openfhe_pin` executes the project's **trusted** BGV definitions (`Spec/`, and the locked
definitions of `Challenge/`) on exact-integer data dumped from real runs of **upstream OpenFHE
v1.6.1** (commit `b59e1f29…`, `../fixtures/README.md`; format `harness/openfhe-pin/FORMAT.md`) and
reports every disagreement, one JSON line per check. The same executable runs the bit-exact
comparisons of the proved reference algorithms (`algo.*`, `../algo/README.md`).

Files:

| file | what |
|---|---|
| `OpenfhePin.lean` | the executable: arguments, scheduling, summary |
| `FHE/Pin/Force.lean` | arrays ↔ `NPoly` (`ofArr`, `toArr`), the *forced* (memoised) forms of the trusted definitions and their kernel-checked equality theorems |
| `FHE/Pin/Kron.lean` | the negacyclic product by Kronecker substitution (one big-integer multiplication of two packed integers) and the automorphism by a linear scatter, each kernel-checked equal to the trusted definition on all inputs (`mulNeg_eq`, `autoL_eq`); what makes the real-size suite (`../realsize/`) feasible |
| `FHE/Pin/Sound.lean` | the two deciding mirrors, `stepOKb` (`e.step`) and `gadgetKeysCheck` (`d.key`), with their soundness theorems |
| `FHE/Pin/Mutants.lean` | deliberately wrong copies of trusted operations (`--mutate`) |
| `FHE/Pin/Load.lean` | `polys.txt` splitter, CRT reconstruction (verified against every limb), `pin.json`, `prog.fhecheck.json` (through `FHE.Check.decode`), `trace.jsonl` |
| `FHE/Pin/Core.lean`, `ChecksA.lean`, `ChecksProg.lean` | the checks |
| `FHE/Pin/ChecksUser.lean` | `b.user.*`: what the user reads after `Decode` (`Spec.Scaling`); forced `plainRunA`, `userDecryptA` with their equality theorems |
| `FHE/Pin/Algo*.lean` | the `algo.*` family (`../algo/README.md`) |
| `harness/openfhe-pin/lean/build_lean.sh` | `lake build openfhe_pin`, prints the executable's path (with `DIR --subst REL FILE`: a scratch Lake project with one repository file replaced, for mutating a trusted definition) |
| `harness/openfhe-pin/lean/verdict.py` | the verdict of a run: expected-fail list, tested refusals, coverage that must not disappear, counts (untrusted) |
| `harness/openfhe-pin/lean/mutation.sh` | mutation table: every mutant must make the suite fail |
| `harness/openfhe-pin/lean/summarize.py` | Markdown statistics from result lines (untrusted) |
| `harness/openfhe-pin/lean/synthetic.py` | a toy BGV case writer (loader test; no OpenFHE needed) |

## Build and run

    harness/openfhe-pin/difftest.sh                        # the gate: committed fixtures, one summary line
    harness/openfhe-pin/run.sh                             # the same, with every table
    lake build openfhe_pin; EXE=.lake/build/bin/openfhe_pin
    $EXE --threads 48 --with-algo --out results.jsonl --list caselist.txt   # one case directory per line
    python3 harness/openfhe-pin/lean/verdict.py results.jsonl harness/openfhe-pin/fixtures/EXPECTED_FAIL.tsv
    harness/openfhe-pin/lean/mutation.sh caselist.txt      # exit 0 iff every mutant is caught

Options: `--threads K` (cases processed in parallel, default 32; each case runs sequentially in
its worker), `--chunks C` (default 0: tasks inside one case; they scale badly because the big
integers of a case are shared and reference-counted atomically), `--literal-max-n M` (default
32), `--literal3-max-n M` (default 16; 3-component values cost N⁴), `--literal-max-cost C`
(budget of the literal `Source.eval` per variable), `--only a,b,…` (check groups `a b c d e f x`;
`x` is the refusal test `x.refusal`; `algo` selects the family `algo.*`), `--with-algo` (adds `algo.*` to the selected groups), `--mutate NAME`, and
the options of the `algo.*` family (`../algo/README.md`). Exit code 1 iff some line has
`"ok": false`; a malformed case gives a `check: "load"` failure line.

The executable is the target `openfhe_pin` of the repository's `lakefile.toml` (`FHE/Pin/*`
belongs to the library `FHE`).

**Result on the committed fixtures** (`../run.sh`, 263 cases): 93443 check lines, 78409 ok,
**0 failing**, 15034 `null` (information lines and not-checkable items: `d.reading*` 11032,
`algo.variant.*` 2021, `c.tail` 790, `info.build` 263, `c.ptbound` 238, …). 151 cases have an extracted program;
112 are refused by the extractor, each with a passing `x.refusal` line. The expected-fail list
is empty. Both mutation tests catch every mutant (13 of 13, 9 of 9). `b.user.*` (151 programs):
`b.user.factors` 151, `b.user.scaleOK` 151, `b.user.decode` 390, `b.user.decrypt` 390,
`b.user.literal-vs-forced` 706, all ok; by technique (factors / decode / decrypt): FIXEDAUTO
40 / 111 / 111, FIXEDMANUAL 37 / 102 / 102, FLEXIBLEAUTO 41 / 106 / 106, FLEXIBLEAUTOEXT 33 / 71 / 71
(159 of the 177 FLEXIBLEAUTO* outputs have a decode factor ≠ 1; 65 programs have adjustments). The
committed `prog.fhecheck.json` files carry the extractor's `$.scaling` section (re-extracted with
the current `extract.py`; `program` unchanged), and `b.user.*` builds `sd` from it as `fhe_check`
does (`sdSource`); the section equals the extractor's rule on all 151. `algo.relin` / `algo.rotate` now also run the
locked `Challenge.Realize` transcriptions (`staged=locked` 405 + 194, `literal` 346 + 166, all
bit-exact; `../algo/README.md`). Wall time of
`../difftest.sh` on 128 cores: 17.5 s at load average 43, 21.2 s at load average 87, 35.6 s at
load average 194.

**Larger suites** of `export/gen_matrix.py`, generated and checked on the same v1.6.1 build (not
committed; `LIVE=1 SUITES=… ../run.sh`): `probe`, 303 cases at N = 16: 252987 lines, 0 failing,
17384 operations / 2011856 coefficients bit-exact; `tiny`, 4044 cases at N = 16, 32, 64
(2174 with a program, 1870 refused, every refusal classified): 2453093 lines, **0 failing**,
12204 encryptions all satisfying the encryption relation (2247 with `‖p‖∞ > t − 1`), 136 modulus
switches of 3-component values within `msBudgetAt P 3` (86 above the 2-component budget),
169683 operations / 31883168 coefficients bit-exact, 0 differing (6 min 22 s on 64 threads).
232 further `tiny` cases cannot be generated: v1.6.1 refuses the parameters of N = 64,
FLEXIBLEAUTOEXT at depth 1 and 2 (`fixtures/README.md`).
`mid` (55 cases at N = 256, 1024, 4096; `--chunks 4 --max-ks 4 --max-tensor 4`): 53 cases finished
within a 40-minute limit (18 at N = 256, 19 at N = 1024, 16 at N = 4096), 12198 lines, 0 failing,
922 operations / 9103616 coefficients bit-exact; the two random programs at N = 4096 that did not
finish were not checked. Runs at OpenFHE's default ring dimension are not part of this release.

## Two execution modes (`"impl"` in every result line)

`Spec.NPoly R N` is a function `Fin N → R`: nothing is memoised, and the literal
`Spec.Scheme.phase` costs N³ ring operations for two components.

* **literal**: the trusted definition applied to wrapped arrays, only the final result forced
  (`bgvDecrypt`, `centeredPhase`, `bgvDecryptSwitched`, `Trace.phaseAt`, `Source.eval` on the
  whole program, `decide (GadgetKeysOK …)`, `decide (PublicKeyOK …)`). Run for N ≤ 32 (N ≤ 16 for
  3 components). Operations whose literal form is linear (`normInf`, `centered`, `ofInt`,
  `switchDownRev`, `refBound`, `decBound`, `ksBoundAt`, `Source.step` itself, …) are always
  executed literally, at every N.
* **forced**: the same trusted primitives composed along the unfolding of the definition, with
  intermediate results stored in arrays. Kernel-checked equalities (`FHE/Pin/Force.lean`, no
  `sorry`, axioms `propext`, `Classical.choice`, `Quot.sound` only):

  | forced | theorem | trusted definition |
  |---|---|---|
  | `toArr` / `ofArr` | `ofArr_toArr`, `toArr_inj` | identity |
  | `mulF`, `autoF` (`Fin.foldl` loops) | `mulF_eq`, `autoF_eq` | `Spec.NPoly`'s `*`, `automorph` |
  | `mulArr`, `mulArrM`, `mulArrQ` (via `FHE/Pin/Kron.lean`'s `mulNeg`), `addArr` | `ofArr_mulArr`, `ofArr_mulArrM_none`, `ofArr_mulArrQ`, `ofArr_addArr` | `Spec.NPoly`'s `*` and `+` on arrays (the Kronecker product replaces the schoolbook sum) |
  | `encryptMF .none`, `freshErrorF` | `encryptMF_none`, `freshErrorF_eq` | `Spec.Encrypt.encrypt` (on the stored plaintext polynomial `p`), `freshError` |
  | `phaseZ` (Horner over ℤ) | `phaseZ_spec` | `Spec.Scheme.phase` modulo any Q |
  | `phaseAtZ` | `phaseAtZ_spec` | `Spec.Trace.phaseAt` |
  | `centredPhaseA`, `centredA ∘ phaseAtZ` | `centredPhaseA_spec`, `centredA_phaseAtZ_spec` | `Spec.Scheme.centeredPhase`, `centered (phaseAt …)` |
  | `decryptA` | `decryptA_spec` | `Spec.Scheme.bgvDecrypt` |
  | `decryptSwitchedA` | `decryptSwitchedA_spec` | `Spec.Decrypt.bgvDecryptSwitched` |
  | `keyErrA`, `keyValidOfErr` | `keyErrA_spec`, `keyValid_iff` | the error `e` of `Spec.Scheme.KeyValid`, and `KeyValid .bgv` itself, for a constant factor (every `gadgetReq`) |
  | `stepA`, fold of `stepA` | `stepA_spec`, `foldlM_stepA` | `Spec.Source.step`, the body of `Spec.Source.eval` |
  | `plainRunA` (`FHE/Pin/ChecksUser.lean`) | `plainRunA_eq` | `Spec.Scaling.plainRun` (the body of `plainEval`) |
  | `userDecryptA` (`FHE/Pin/ChecksUser.lean`) | `userDecryptA_spec` | `Spec.Scaling.userDecrypt` |

  Two checks decide a trusted *predicate* rather than compare computed values; their deciding
  functions are proved **sound** in `FHE/Pin/Sound.lean` (same axioms):

  | decision (the verdict of) | theorem | statement |
  |---|---|---|
  | `stepOKb` (`e.step`) | `stepOKb_sound` | if `stepOKb P E K .none i v.level d get = some true`, where `d` is the forced phase (`Ph.Good`) of the ciphertext `d.comps` with the key, level and number of components that `ρ'` records for the destination, and `get` returns the forced phases of the operands' ciphertexts in `σ` (`GetOK`), then `Spec.Trace.StepOK P E s ρ ρ' σ (σ.set (dst i) d.comps) i`. Every instruction case is covered (`rescale`: the decision is `some false`). The witnesses are `e := centered (φ' − φ_a)` and `δ := q·Φ' − Φ_a` (`ks_witness`, `ms_witness`). |
  | `gadgetKeysCheck` (`d.key`) | `gadgetKeysCheck_sound` | if `gadgetKeysCheck P lay ℓ K .none (keys.map (keyLhsZ …)) (targetZ … tgt) = true`, then `Spec.Budget.GadgetKeysOK P lay ℓ tgt s` holds of the first `(lay.sizes ℓ).length` stored digits. |

  **Not proved, only mirrored** (cross-checked against the literal mode at small N by the
  `*.literal-vs-forced` lines where one exists):

  * that the context builds phases satisfying `Ph.Good` and operand lookups satisfying `GetOK`
    (`Cx.mkPh` calls exactly the functions named in `Ph.Good`, through a per-key cache in `IO`;
    `e.phase.literal-vs-forced` compares the result with the literal `Spec.Trace.phaseAt`);
  * completeness of `stepOKb` (a `false` verdict says only that *its* witnesses fail);
  * the composite modulus switch through intermediates that have no OpenFHE object (`e.step`
    lines with `"composite": true`; none occurs on the committed fixtures) and the level
    restriction `ℓ ≤` (number of chain limbs the key has) that `d.key` adds to `gadgetKeysCheck`;
  * the bookkeeping checks (`b.sf`, `b.shape`, `d.layout`, `d.limbs`, `x.refusal`, `c.stored`),
    which are glue comparisons of dumped metadata, and `f.bound`/`f.decrypt`, which compare a
    measured norm with the number `refBound`/`decBound` return;
  * the loader (JSON, `polys.txt`; the CRT lift is verified against every limb at run time).

## Checks

| check | what is compared |
|---|---|
| `load`, `load.params`, `load.secret`, `load.prog` | well-formed case; CRT verified against every limb; chain of `prog.fhecheck.json` = `pin.json`; the secret's RNS form |
| `a.switched` | `Spec.Decrypt.bgvDecryptSwitched t (qs.take towers) s ct` = OpenFHE's `Decrypt` (`decrypt.raw`), all N coefficients |
| `a.switchedQ0` | the switched phase modulo q₀ = `decrypt.rawQ0` |
| `a.textbook` | `decScale · Spec.Scheme.bgvDecrypt t s ct` = `decrypt.raw`; `null` if `decryptOK?` fails for the measured phase |
| `a.decbound` | ‖switched phase‖∞ ≤ `decBound` of the measured phase norm |
| `b.shape`, `b.msg`, `b.raw`, `b.sf` | level/parts/key of `Source.step`; its message = `bgvDecrypt` of OpenFHE's ciphertext; `decScale ·` message = OpenFHE's `Decrypt`; scaling factors |
| `b.step`, `b.eval`, `b.outputs`, `b.decls` | well-formedness of the extracted program under `Source.step` / `Source.eval` |
| `c.encrypt` | `Spec.Encrypt.encrypt t b a p u e₁ e₂` mod Q = OpenFHE's ciphertext, with `p` the **stored plaintext polynomial** OpenFHE added (the centred lift of the plaintext's limbs), forced and (N ≤ 32) literal |
| `c.stored` | the encoder's convention as `Spec.Encrypt`'s docstring states it: packed ⇒ every coefficient of `p` in `[0, t)`; CoefPacked under FIXEDMANUAL/FIXEDAUTO ⇒ `‖p‖∞ ≤ t/2`; otherwise `null` (no convention claimed) |
| `c.stored.exceeds` | emitted where `‖p‖∞ > t − 1`: the encryption relation holds for that `p` (the generalisation is exercised) |
| `c.pubkey`, `c.pubkey.shape` | `PublicKeyOK t Q s e b a`; centred `(b + a·s)` divisible by t with quotient = `pk.e`, norm ≤ 39 |
| `c.phase` | the centred phase = `p + t·freshError` (when that is below Q/2) |
| `c.worst` | `‖freshError‖∞ ≤ worstError`, `‖p‖∞ ≤ Bp` and noise ≤ `freshNoise t Bp worstError`, with `Bp` the **declared** bound of the stored plaintext (`freshEncryption.plaintextBound` of the extracted program, `t − 1` if it declares none); for a case the extractor refused nothing is declared and `Bp` is the measured `‖p‖∞` (`plaintextBoundDeclared: false`) |
| `c.ptbound` | every plaintext object: centred norm ≤ the bound the program declares for it (else the declared bound of fresh encryptions); `null` when the extractor refused the case |
| `c.support`, `c.tail` | sampler supports; tail statistics |
| `d.limbs`, `d.key`, `d.reading`, `d.layout` | key limbs vs chain; `GadgetKeysOK` at every level, decided by `gadgetKeysCheck` (sound: `gadgetKeysCheck_sound`); which `KeyValid` reading holds; digits and factor residues |
| `e.step` | `Spec.Trace.StepOK` at the budget `Spec.Budget.certified P lay`, decided by `stepOKb` (sound: `stepOKb_sound`); a `modSwitch` is charged `E.modSwitchAt k` for an operand with `k` components |
| `e.modswitch-parts` | every traced `ModReduceInternalInPlace` (on the data alone, also when the extractor refused): `‖δ‖∞ ≤ q·E.modSwitchAt k`, `t ∣ δ` |
| `f.bound`, `f.decrypt`, `f.refAnalyze`, `f.budget` | `refBound` vs the measured centred phase; `decBound`; verdict of `refAnalyze`; the four fields of the budget (`keySwitch`, `modSwitch`, `modSwitchOne`, `modSwitchMany k` for k = 3…6, and `modSwitchAt k` for k = 1…6) |
| `x.refusal` | for a case without a program: `prog.fhecheck.json` is an extractor refusal whose message is one of the expected ones **and** the dumped data shows its reason (`FHE.Pin.refusalClasses`); anything else fails |
| `b.negate` | every traced `EvalNegate`: phase' = (−1)·phase, decrypt' = −decrypt, scaling factors |
| `b.user.factors`, `b.user.scaleOK` | the scaling data `sd` built as `fhe_check` builds it (`$.scaling`; for files without that section, the extractor's formula: inputs' recorded `sf` mod t, `mulConst` indices of the JSON body, technique ∈ FLEXIBLEAUTO*; `sdSource`, and `fileVsRule` when the file has it): `Spec.Scaling.factors?` is `some`; `Spec.Scaling.scaleOK? = true` |
| `b.user.decode` | per decrypted output: the factor and level of `Spec.Scaling.decodeAt?` = the `scalingFactorInt` OpenFHE's `Decrypt` returned (`decrypt.sf`) and the towers. **Not proved**: that OpenFHE follows `facStep` is the assumption `Challenge.Scaling` names; this line is the executed evidence |
| `b.user.decrypt` | with `u x = sf_x⁻¹ • p_x` (`p_x` the stored plaintext polynomial of each input): `Spec.Scaling.userDecrypt` of OpenFHE's output ciphertext (decode factor and level of `decodeAt?`) = `Spec.Scaling.plainEval prog marks u` at the output, and OpenFHE's own reading `decrypt.sf⁻¹ • decrypt.raw` = the same; forced (`userDecryptA_spec`, `plainRunA_eq`), literal at small N (`b.user.literal-vs-forced`); `null` where `b.raw` would be (phase wrap not excluded, premise false, hand-built inputs) |
| `d.key.power` | keys for s³, s⁴ (`evalKeys[].power`): no trusted target exists (`ok: null`); `holds` is the `KeyValid` error formula with target s^k on the data |
| `*.literal-vs-forced` | both modes on the same data |

Verdicts. `ok: false` is a disagreement. `ok: null` means not checkable, with `why`; in
particular `b.msg`, `b.raw`, `f.bound`, `f.decrypt` are `null` when (i) the reference analysis
does not exclude a phase wrap (`tainted`: `2·β ≥ Q` at the variable or an ancestor) and the
message disagrees, (ii) an input the value depends on exceeds its own bound β₀ (`premiseBad`:
the hypothesis `InputsOK`/`BoundsOK` is false for the run; the input's own `f.bound` line
fails), or (iii) `pin.json` says `"inputsArbitrary": true`.

To add a check family: write `runCase : FHE.Pin.Cx → IO Unit` that emits lines with `Cx.emit`
(`Cx.objPh id` gives the forced phase of an object, `Cx.objComps` its CRT-lifted components,
`Cx.c.polys` the raw limbs) and add `guard "name" (runCase x)` next to the others in
`OpenfhePin.lean` (`runCase`).

## Fixed by the generalised definitions

The former expected-fail list (331 `(check, case)` pairs on the v1.3.1 fixtures: `c.encrypt` 94,
`c.phase` 94, `c.ptbound` 48, `f.bound` 33, `c.worst` 24, `e.relin-parts` 23, `e.step` 15) had seven
checks. None is listed any more; `fixtures/EXPECTED_FAIL.tsv` is empty.

1. **`c.encrypt`, `c.phase`: stored plaintexts that are not the lift to `[0, t)`.**
   `Spec.Encrypt.encrypt t b a p u e₁ e₂` now takes the stored polynomial `p`. On the 263
   fixtures the relation `ciphertext = encrypt t b a p u e₁ e₂` holds on **all 790** recorded
   encryptions (and literally on the 662 at N = 16), the phase identity `Φ = p + t·freshError`
   on all 790. Of these, 591 are packed (every coefficient in `[0, t)`: `c.stored` ok), 81 are
   CoefPacked under FIXEDMANUAL/FIXEDAUTO (centred, `‖p‖∞ ≤ t/2`: `c.stored` ok), 108 are
   CoefPacked under FLEXIBLEAUTO/FLEXIBLEAUTOEXT and 10 are string-encoded.
2. **`c.worst`, `c.ptbound`, `f.bound` of a plaintext input: stored norm above `t − 1`.** All
   108 CoefPacked plaintexts under FLEXIBLEAUTO/FLEXIBLEAUTOEXT (35 cases) have
   `‖p‖∞ > t − 1` (largest: 2130870272 ≈ (t/2)(t − 1)); each has a passing `c.stored.exceeds`
   line. The noise statements take a declared bound `Bp` (`freshNoise t Bp ε`), so a
   declaration of `t − 1` simply does not cover these inputs, and the extractor refuses them
   (next section) instead of declaring a false bound. `c.worst` passes on all 790 encryptions:
   at the declared `Bp` where a program exists (455), at the measured `‖p‖∞` otherwise (335).
3. **`e.step`, `f.bound`: modulus switch of a 3-component ciphertext.** `StepOK` and
   `refBound` charge `E.modSwitchAt k` (`Spec.Budget.msBudgetAt P k`). The 10 switches of
   3-component values the extracted programs contain are within `msBudgetAt P 3`; 6 of them
   exceed the 2-component budget `msBudget` (`exceeds2PartBudget`), which is what failed before.
   The mutant `ms-parts` (the old rule) is caught by exactly these lines.

## Refused by the extractor (tested)

A case the extractor refuses is not a checker failure and not an excused one: the refusal itself
is tested (`x.refusal`; `fixtures/EXPECTED_REFUSALS.tsv`; `export/refusals.py` re-runs the
extractor on the recorded trace and requires the recorded message), and every check that does
not need the extracted program still runs (key validity `d.*`, encryption with the stored
plaintext `c.*`, decryption `a.*`, every traced `ModReduce` and `EvalNegate`, and all `algo.*`
comparisons). On the fixtures (112 refused cases):

| class (count) | extractor message (abridged) | what the data must show |
|---|---|---|
| `non-packed-plaintext` (67) | `plaintext pt_k has encoding coefpacked` / `string: only packed plaintexts are mapped …` | a plaintext object whose encoding is not `packed` |
| `evalmult-key-on-3-part-operand` (20) | `EvalMult(Ciphertext,Ciphertext,EvalKey)` / `EvalSquare(Ciphertext,EvalKey) on a 3-part operand …: OpenFHE relinearizes only the third component of the product and drops the rest, so the result is not an encryption of the product` | a ciphertext with ≥ 3 components |
| `fast-rotation-not-mapped` (7) | `EvalFastRotationPrecompute …: EvalFastRotation / EvalFastRotationExt … is not mapped` | the trace calls it |
| `evalsum-not-mapped` (5), `evalinnerproduct-not-mapped` (4) | `EvalSum …: OpenFHE >= 1.6 computes the rotation sum as a fused radix fold …`; `EvalInnerProduct calls EvalSum …` | the trace calls it |
| `compress-not-mapped` (3), `evalmultmutable-not-mapped` (3) | `Compress is not mapped`; `EvalMultMutable … run untraced cores in v1.6.1; not mapped` | the trace calls it |
| `rotation-of-3-part-threw` (3) | `EvalAutomorphism(…) on a 3-part operand: OpenFHE throws "Ciphertext should be relinearized before." (base-leveledshe.cpp:441); the call produced no ciphertext; relinearize the operand first` | a 3-component ciphertext and the exporter's note that OpenFHE's `EvalAutomorphism` threw "Ciphertext should be relinearized before." (the call threw before it registered its key) |

The former classes `e.relin-parts` (the 3-component relinearising `EvalMult`) and the CoefPacked
part of `c.ptbound`/`c.worst`/`f.bound` are the first two rows.

**Extractor aliasing** (the former item 4: a recurring content-hash id resolved to the wrong
operand, `b.step`/`b.eval` failing) does not reproduce on v1.6.1 with the current extractor:
no `b.step` or `b.eval` line fails on the 151 extracted fixture programs, nor on the larger
uncommitted suites of `gen_matrix.py` (`probe`: 303 cases, 0 failing lines). A variable `id#k`
(the extractor's name for a later definition with the same id) is checked against the object
`id`.

Conventions. The message of a plaintext is the textbook decryption of the one-component value
`[p]` (centred representative modulo its own modulus, then mod t). The integer representative of
a key component is its CRT lift over all the key's limbs; `ofInt (Q_ℓ·P)` restricts it to the
limbs `q_0..q_{ℓ-1}, p_0..` (so `GadgetKeysOK` at level ℓ is about exactly those limbs).

## Mutants (`--mutate`)

`centring`, `switch-centring`, `automorph-index` (g ↦ g⁻¹), `automorph-shift` (g ↦ g+2),
`automorph-sign`, `gadget-factor` (no `[Q̂⁻¹]`), `gadget-digit` (next digit), `scale-step` (q
instead of q⁻¹ in `modSwitch`), `scale-dec` (`decScale` without the inverse), `mul-negacyclic`,
`lift` (`encrypt` adds the centred lift of `p mod t` instead of the stored `p`), `key-order` (b
and a swapped), `ms-parts` (the 2-component modulus-switching budget for every operand with more
than one component). With a mutant the literal mode is off, so a failure is a disagreement with
OpenFHE's data, not with the literal definition. Visibility: `scale-step` and `scale-dec` need a
prime `q ≢ 1 (mod t)` (FLEXIBLEAUTO, FLEXIBLEAUTOEXT; invisible under FIXEDMANUAL/FIXEDAUTO,
whose primes are ≡ 1 mod t); `automorph-*` and the rotation-key part of the gadget mutants need
a rotation; `gadget-digit` needs at least two digits; `automorph-index` is invisible for
`g² ≡ 1 (mod 2N)`; `switch-centring` is invisible modulo t (the two representatives differ by a
multiple of t): it is caught by `a.switchedQ0`, `a.decbound` and `f.decrypt`; `lift` needs a
stored plaintext that is not centred modulo t (a packed plaintext with a coefficient above
t/2); `ms-parts` needs a modulus switch of a 3-component value above the 2-component budget.
On `fixtures/mutation.list` (20 cases) all 13 are caught (`../run.sh`).

## BFV (`pin.json: "scheme": "BFV"`)

A case whose `pin.json` has `"scheme": "BFV"` (`../FORMAT.md`, "BFV cases": a run of
`CryptoContextBFVRNS` of the same OpenFHE v1.6.1 build, program extracted by
`harness/frontend/openfhe/extract_bfv.py`) is checked by `FHE.Pin.BFV.runCase` against the
**trusted BFV definitions**: `Spec/TraceBFV.lean` (`StepOK`, `InputsOK`, `PlainOK`, `inputBound`),
`Spec/Scheme.lean` (`bfvDecrypt`, `BFVEncrypts`), `Spec/Budget.lean` (`GadgetKeysOK`), and the
locked `Challenge/CertifyBFV/Defs.lean` (`certifyBFV?`, `budgetBFV`) and `Challenge/BFV/Defs.lean`
(`refAnalyzeBFV`, `refBoundBFV`, `decOK`). Every other case is a BGV case and is checked exactly as
before. Every BFV line carries `"scheme": "BFV"`, `"mult"` (multiplication technique), `"ks"`,
`"enc"`, `"N"`, `"impl"`, and `"measured"`, `"bound"`, `"slackBits"` (= log2(bound / measured))
where a bound is involved.

| file | what |
|---|---|
| `FHE/Pin/BFV/Sound.lean` | `stepOKb` (decides `Spec.TraceBFV.StepOK`; `stepOKb_sound`), `inputOKb` (`Spec.Correct.Encrypts` for BFV / `PlainOK`; `inputOKb_sound`), `noiseA` (`noiseA_spec`), `decryptBFVA` (`decryptBFVA_spec`) |
| `FHE/Pin/BFV/Keys.lean` | `gadgetKeysCheck` (decides `Spec.Budget.GadgetKeysOK` for `kind = .bfv`: the norm of the key error, no divisibility by `t`; `gadgetKeysCheck_sound`) |
| `FHE/Pin/BFV/Mutants.lean` | the mutants (`BMut.all`) |
| `FHE/Pin/BFV/Load.lean`, `Checks.lean`, `ChecksProg.lean`, `Run.lean` | decoding (`FHE.Check.BFV.decode`, `FHE.Check.BFV.inputBFV`: the input of `certifyBFV?` exactly as `fhe_check` builds it), the checks, the dispatch |
| `lean/verdict_bfv.py`, `lean/summarize_bfv.py`, `lean/mutation_bfv.sh` (+ `mutation_bfv.py`) | verdict, tables, mutation test of a BFV run (untrusted) |

    EXE=.lake/build/bin/openfhe_pin
    $EXE --threads 16 --out bfv.jsonl --list bfv-cases.txt            # one BFV case directory per line
    python3 -I harness/openfhe-pin/lean/verdict_bfv.py bfv.jsonl harness/openfhe-pin/fixtures/EXPECTED_FAIL.tsv \
        --gate --refusals harness/openfhe-pin/fixtures/EXPECTED_REFUSALS-bfv.tsv
    python3 -I harness/openfhe-pin/lean/summarize_bfv.py bfv.jsonl    # the tables
    harness/openfhe-pin/lean/mutation_bfv.sh mutation-bfv.txt $EXE    # the mutation table

### BFV checks

Groups (`--only`): `a` decryption, `b` message semantics, `c` fresh encryptions and inputs,
`d` keys, `e` step contracts, `f` bounds and the verdict, `x` refusals.

| check | what is decided | decided by |
|---|---|---|
| `load.params`, `load.prog`, `load.secret`, `load.declared` | well-formed case; chain of the program file = `pin.json`; the program file's technique, auxiliary basis (`auxR` / `behzBsk`, `mSk`, `mTilde`), special primes and key-switching variant against the library's accessors dumped in `pin.json` | glue |
| `a.decrypt` | for every ciphertext object with a recorded `decrypt.raw`: `Spec.Scheme.bfvDecrypt t s ct` at the object's own modulus = OpenFHE's raw `Decrypt` output, all N coefficients. Where they differ: for a program variable under `s`, FAIL if the noise `f.bound` measures (for the message the program computes) satisfies `decOK`, `null` otherwise; for any other object (no intended message: it may be under another key, as the key-switched ciphertext inside `EvalAutomorphism` before the permutation), FAIL if a differing coefficient is more than 1/4 from a rounding boundary (the error OpenFHE's comments allow its floating-point `ScaleAndRound`), `null` otherwise. `tieDistMin`, `tieDistMismatchMax`: distance of `t·Φ/Q` from a rounding boundary | literal `bfvDecrypt` (N ≤ 32) and forced `decryptBFVOfPhaseA` (`decryptBFVOfPhaseA_spec`) |
| `c.fresh` | every recorded encryption satisfies `Spec.Scheme.BFVEncrypts` (the BFV case of `Spec.Correct.Encrypts`) with message = the stored plaintext polynomial mod `t` and bound `Spec.TraceBFV.inputBound P prog d` (the bound the certificate uses); for a case the extractor refused, the bound is the extractor's documented formula (`declared: false`; `FHE.Pin.BFV.extractorInputNoise`) | literal `BFVEncrypts`; forced `inputCtOKb` (`inputCtOKb_sound`) |
| `c.encryptBFV`, `c.pubkeyBFV` | `Spec.EncryptBFV.encryptBFV t Q_k b a p u e₁ e₂` (Q_k the plaintext's own limbs; recorded key, stored plaintext, randomness) mod Q_k = the recorded ciphertext, and every stored coefficient in `[0, t)`; `Spec.Encrypt.PublicKeyOK 1 Q s e b a`. `null` for EXTENDED encryption | forced `encryptBFVF` (`encryptBFVF_eq`), `pubKeyLhsF`/`pubKeyRhsF` (`pubKeyF_iff`); literal at small N |
| `c.timesQovert` | the residues of `Spec.EncryptBFV.scaleUpCeil t Q_k p` = the library's recorded `TimesQovert`, limb by limb | `scaleUpCeil` itself (linear) |
| `a.decryptLib.tables`, `a.decryptLib.phase`, `a.decryptLib`, `a.decryptLib.textbook` | HPS family, all limbs (`decrypt.branch = hps-float`): `Spec.DecryptBFV.tables FHE.Float.RNE.rneA t qs` = `decryptTables` (doubles decoded exactly from their bit patterns); the recorded `decrypt.phase` = the residues of the trusted phase; `Spec.DecryptBFV.decrypt1 FHE.Float.RNE.rneD t qs (tables …)` on those residues = OpenFHE's UNREDUCED raw output, every value ≤ t (`outputEqualsT` counts values equal to t); and its value mod t = `bfvDecrypt` wherever `Spec.DecryptBFV.decLibOK? t qs B` holds at the measured noise B (else `null`) | the trusted transcription on recorded residues; literal `bfvDecryptLib` at small N |
| `c.input`, `c.inputs` | `Spec.TraceBFV.InputsOK`, input by input: `Encrypts` for a ciphertext input, `PlainOK` for a plaintext input, at `inputBound` | literal; forced `inputOKb` (`inputOKb_sound`) |
| `c.predict` | the measured noise polynomial `[phase − ⌊Q/t⌋·m]_Q` equals `e_pk·u + e₁ + e₂·s + (⌈Q·p/t⌉ − ⌊Q/t⌋·p)` computed from the recorded randomness (this pins the Δ-encoding `TimesQovert` as the library does it), with the Gaussian part ≤ 39·(1+2N) and the encoding deviation ≤ ⌈(Q mod t)(t−1)/t⌉; `null` for EXTENDED encryption (no closed relation) | glue (`FHE/Pin/BFV/Checks.lean`); the trusted encryption definition `Spec.EncryptBFV.encryptBFV` is checked separately by `c.encryptBFV` and `c.timesQovert` |
| `c.support`, `c.stored` | sampler outputs within the declared bounds (secret and `u`: 1 for a ternary secret distribution, 39 for GAUSSIAN; `e₁`, `e₂`: 39); packed ⇒ every stored coefficient in `[0, t)` | mirrored |
| `d.key` | `Spec.Budget.GadgetKeysOK P lay ℓ tgt s` at every level ℓ for the relinearisation key (target `s²`) and every rotation key (target `σ_g(s)`; OpenFHE switches with the stored key and then applies `X ↦ X^g`, so the key checked is `σ_g` of the stored one). HYBRID: digits over `Q·P`. BV with digit size 0: `special = []`, one limb per digit: the trusted `KSLayout`/`gadgetFactor` express it (`P = 1`). BV with a digit size `w > 0`: `KSLayout` cannot express base-`2^w` digits, the line is `null` and `holds` evaluates the same error formula with the factor `2^(w·k)·(idempotent of limb i)` on the data (the extractor refuses these cases: `x.refusal`, class `bv-digit-size`). With EXTENDED encryption and BV the library generates the keys over `Q·r` (one more limb, `d.limbs: extraLimbs`); the statement is about the residues modulo `Q_ℓ` | literal `GadgetKeysOK`; forced `BFV.gadgetKeysCheck` (`gadgetKeysCheck_sound`) |
| `d.pubkey`, `d.limbs` | `b + a·s ≡ e (mod Q)`, `‖e‖∞ ≤ keyNoise`, `e` = the exported key error; key limbs = chain ++ special (++ the extended prime) | mirrored |
| `e.step` | every recorded step satisfies `Spec.TraceBFV.StepOK` at the budget of its instruction, `E := Challenge.CertifyBFV.budgetBFV x k` (`k` the instruction's index in the body, `x` the decoded `InputBFV` with its declared internal drops `x.drops`; `f.budget`: this is `c.budget k` whenever `certifyBFV?` returns a certificate). Fields: `mul`/`square`: `liftA`, `liftB` (‖k_a‖, ‖k_b‖) against `liftBound` (= `E.mulLift`), `liftTextbook`; `roundMeasured` (= ⌈2‖D‖/Q⌉) against `roundBound` (= `E.mulRound`), `roundTextbook` (`Spec.BudgetBFV.mulRound`), `roundIdealised` (`floatTol := false`), with the three `roundSlackBits*`; `relin`/`keySwitch`: ‖e‖ against `E.keySwitch` and against `ksBoundAt` at the operand's level; `addPlain`/`subPlain`: ‖δ‖ against `E.plainAdd`; `modSwitch`: ⌈‖δ‖/q⌉ against `E.modSwitch`; `levelsDropped`: the traced internal drop of HPSPOVERQLEVELED (`provenance[].internalDrop`) | forced `stepOKb` (`stepOKb_sound`; for `mul`/`square` through `stepOKb_mul`, `stepOKb_square`: the rounding witness is computed once) |
| `b.msg`, `b.raw`, `b.output` | the message `Source.step` computes = `bfvDecrypt` of the recorded object = OpenFHE's `Decrypt`; outputs: OpenFHE's `Decrypt` = `Source.eval` on the recorded input messages | forced `stepA` (`stepA_spec`); `b.eval`, `b.literal-vs-forced`: literal `Source.eval` |
| `f.bound`, `f.decok` | measured noise `‖[phase − ⌊Q/t⌋·m]_Q‖∞` (`m` the message `Source.eval` computes) ≤ the bound of the variable, replayed with `Challenge.BFV.refBoundBFV`/`domainOK`/`bndOK` as `refRunBFVAt` does at the per-instruction budget; the measured noise satisfies `decOK` | forced `noiseA` (`noiseA_spec`) against the literal `refBoundBFV` |
| `f.refAnalyze` | the replay's result = `Challenge.BFV.refAnalyzeBFVAt P (budgetBFV x) prog` | literal |
| `f.budget` | `budgetBFV x k` for every instruction `k` (`perInstruction`; the top-level numbers are the maxima), the textbook budget, the declared drops; `ok`: equal to the certificate's `c.budget k` at every `k` | literal |
| `f.verdict` | information: `certifyBFV? x` (CERTIFIED / NOT CERTIFIED), `assumed` (`c.assumed`), bound and margin bits per output, the failing conjunct of `checksOK` or the first instruction `refRunBFV` rejects, and the verdict of `fhe_check`'s own pipeline (`FHE.Check.BFV.runCheck`: `tool`, `toolAgrees`) | literal |
| `f.certified-consistent` | for a CERTIFIED program: no `e.step`, `f.bound` or `c.input` line of the case fails | glue |
| `x.refusal` | a case whose `prog.fhecheck.json` is an extractor refusal: the message is an expected one **and** the data shows its reason (`FHE.Pin.BFV.refusalClasses`); the checks that need no program (`a`, `c.fresh`, `c.predict`, `d`) still run | glue |

**Object-less variables.** `id#k` is checked against the object `id`. The intermediate
`a@g~k` of a rotation has no object (OpenFHE key-switches first and permutes after): the trusted
automorphism is applied to the operand's components (`"synthetic": true`), and both `automorph`
and the following `keySwitch` are decided by `stepOKb` on that ciphertext. The intermediates
`a~k` of a `Compress` by several limbs have no object: the chain is checked as one composite
modulus switch against `Σ_j (q_1⋯q_j)·E.modSwitch` (`"composite": true, "mirroredOnly": true`).

**Witnesses of the product contract.** `StepOK` for `mul` is existential:
`Q·X = t·(Φ_a + Q·k_a)(Φ_b + Q·k_b) + D`. The checker supplies `k := (Ψ − Φ)/Q`, `Ψ` the integer
phase of the centred components (the lift of an exact, centred base extension); `stepOKb` computes
`X` (the representative of the result's phase nearest to `t·A·B/Q`) and `D`. A FAIL says that these
witnesses fail (soundness only). BEHZ lifts by a Montgomery-corrected fast base conversion, which
differs from the centred lift by `±Q` near `±Q/2` (one coefficient of 2·2048 on
`bfv_n2048_behz_bv_d3_chain_q30_small`, where the centred witness gives ⌈2‖D‖/Q⌉ ≈ 2⁸⁶): under BEHZ,
when the centred witness fails, the witness of the untrusted model `FHE.Pin.BFV.behzLift`
(`v = Σ [cᵢ·m̃·q̂ᵢ⁻¹]_{qᵢ}·q̂ᵢ`, `r = [−v·Q⁻¹]_{m̃}` centred, lift `(v + Q·r)/m̃`) is tried; the line
says which witness decided (`witness`) and keeps the centred one's number
(`centredWitnessRoundMeasured`). Either way the verdict is `stepOKb`'s, sound for every witness.

**Verdicts.** `ok: false` is a disagreement. `ok: null`: not checkable, with `why`. `b.msg`,
`b.raw`, `f.bound`, `f.decok` are `null` (never `false`) when (i) `refRunBFV` rejects the program
at the variable or an ancestor (`tainted`: the bound is not a claim), (ii) an input the value
depends on fails `c.input` (`premiseBad`), (iii) the step that produced the value or an ancestor
fails `e.step` (`stepBad`: the failing line is the `e.step` line; `b.output` still fails, it is
what the user sees), or (iv) `pin.json` says `inputsArbitrary`.

**Results** (2026-11-14; suites of `export/gen_matrix_bfv.py`, OpenFHE v1.6.1). On the committed
`fixtures-bfv.tar.xz` (`../difftest.sh`, 241 cases: 189 programs, 52 tested refusals): 91149 check
lines, 78158 ok, **0 failing**, 12991 `null`, with the `algo.*` family (25469 ok, 0 differing);
176 programs CERTIFIED, 13 NOT CERTIFIED, and no CERTIFIED program has a violated step, a noise above
its bound or an input outside its bound; `coverage.py`: 66 of 66 emittable instruction shapes
covered.

*Counts, machine-readable* (`../counts.sh` writes `../results/difftest-counts.json` from one
`difftest.sh` run; `lean/counts.py` documents every field). "CERTIFIED" in the gate's summary line
and here is the verdict of `certifyBFV?` (the noise certificate, `f.verdict`), not `fhe_check`'s
printed verdict, which also requires the library-decryption check. The 176 programs are 151 at
N = 16 and 25 at N = 64; none records `idealised`. `algo.runLibrary` executes the locked
`Challenge.CertifyBFV.runLibrary` on **every one of the 176** (1472 instructions, 1323 ciphertexts
compared, 0 differing): before 2026-11-14 it ran at N <= 16 only (`--algo-literal-max-n`), 141
programs at the time it was first counted and 151 after the fixtures were re-extracted, and the 25
programs at N = 64 were skipped; its own limit `--library-max-n` (default 64) now covers every
fixture, at a cost of about 15 s of the run. Since 2026-11-15 it runs `runLibL`
(`FHE/Pin/BFV/AlgoLibrary.lean`, proved equal to the locked `runLibrary`: `runLibrary_list`),
whose key switches, plaintext products and automorphisms are forced Kronecker products and
linear-time scatters (`ksBFVF_eq`, `libStepF_eq`), so the limit is the larger of
`--library-max-n` and the forced cap of the multiplications (`--forced-max-n`): at real sizes
see `../realsize/README.md`. The committed fixtures give the same counts with it. The 65 BFV cases it does not run are the 52 refused
extractions and the 13 programs `certifyBFV?` does not certify. The JSON also gives per-check
ok/fail/null counts (e.g. `a.switched`, `d.key`, `e.step`), and for the `algo.*` comparisons both
the number of comparisons (the gate line's "operations": one per recorded operation and execution
mode) and the number of distinct recorded operations. bfv-adv (320 hand-built or scripted inputs at the declared bound): no failing line. On the committed
suites no check fails, and every `d.key` check passes against the declared `keyNoise`.

### BFV mutants (`--mutate NAME` on BFV cases; `lean/mutation_bfv.sh`)

Each perturbs ONE trusted definition or ONE number of the budget (`FHE/Pin/BFV/Mutants.lean`);
with a mutant the literal mode is off. `delta-round`, `delta-ceil` (Δ = ⌊Q/t⌉, ⌈Q/t⌉ in the noise
definition and in `addPlain`/`subPlain`), `enc-floor` (the predicted encoding is ⌊Q·p/t⌋),
`mul-no-t`, `mulround-half`, `mulround-textbook` (ρ := 1), `mulround-zero`, `mullift-zero`,
`mullift-half`, `ks-half`, `ks-zero`, `ks-noleveled` (`ksBudget` where `ksLeveled` applies),
`ms-half`, `ms-zero`, `plainadd-zero`, `plainadd-rounded`, `wrong-technique` (the slacks of
another technique), `slack-idealised` (`floatTol := false`), `fresh-half`, `decrypt-floor`,
`automorph-index`, `mul-cyclic`, `bound-no-carry` (`refBoundBFV` without the `Q mod t` terms),
`bound-mul-k0` (`mulBound` with `E.mulLift := 0`). A surviving BUDGET mutant is a result: the
recorded executions stay below the perturbed number; `mutation_bfv.sh` prints the headroom and
compares the survivors with `fixtures/MUTANTS_SURVIVING-bfv.tsv`. On `fixtures/mutation-bfv.list`
(61 cases of bfv-fixtures, 16 of them hand-built at N = 64): 19 of 24 caught (76 s); the five
survivors (`mulround-half`, `mullift-half`, `ks-half`, `ms-half`, `plainadd-rounded`) are listed
there with their headroom.
`delta-round` and `enc-floor` are caught only by `c.predict`, which is glue: no check against a
trusted definition distinguishes ⌊Q/t⌋ from ⌊Q/t⌉ on these data.
