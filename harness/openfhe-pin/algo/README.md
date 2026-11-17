# openfhe-pin / algo — the proved reference algorithms against OpenFHE, limb by limb

`FHE/Pin/Algo.lean` feeds the exact inputs of every operation of a dumped OpenFHE BGV run
(`../FORMAT.md`) to the corresponding Lean function and compares the result with OpenFHE's output
ciphertext, RNS limb by RNS limb, coefficient by coefficient (check names `algo.*`). The recorded
runs are of **upstream OpenFHE v1.6.1** (commit `b59e1f291965f14fbee5172cd83a20f5b856204f`,
`../fixtures/README.md`).

| file | content |
|---|---|
| `FHE/Pin/AlgoStage.lean` | `forceFam`/`ofFam`, `Stages`, `ksPipe`, `ksStaged`; theorems `ksStaged_openfhe` (= `keySwitchBGVOpenFHE`), `ksStaged_centred` (= `keySwitchBGV`), `ksStaged_addDown` |
| `FHE/Pin/AlgoOpenFHE.lean` | `relinOpenFHE`, `rotateOpenFHE161` (v1.6.1), `rotateOpenFHE` (v1.3.1 order), in RNS form; `addKS_openfhe`, `rotStaged161_openfhe`, `rotStaged_openfhe` (staged = definition); `relinOpenFHE_spec`, `rotateOpenFHE161_spec`, `rotateOpenFHE_spec` |
| `FHE/Pin/AlgoLocked.lean` | `addKS_locked`, `rotStaged161_locked`: the staged executions, on the bases built from the scheme parameters, are limb for limb the RNS form of the LOCKED `Challenge.Realize.relinOpenFHE` / `rotateOpenFHE161` |
| `FHE/Pin/AlgoMutants.lean` | one representative convention perturbed per mutant |
| `FHE/Pin/Algo.lean` | trace walker, comparisons, entry point `FHE.Pin.Algo.runCase (c : Case) (o : Opts) : IO (Array Json)` |
| `build_algo.sh` | builds `openfhe_pin` (the comparisons are part of that executable; there is no separate `algo_pin` any more) |
| `summarize.py` | per check: cases, operations, limbs, coefficients, exact / differing |
| `mutation.sh CASELIST [EXE]` | every mutant must make a comparison fail |

    lake build openfhe_pin; B=.lake/build/bin/openfhe_pin
    $B --threads 48 --only algo --out out.jsonl --list cases.list     # the algo.* family alone
    $B --threads 48 --with-algo --out out.jsonl --list cases.list     # with the checks a-f (../run.sh)
    $B --chunks 96 --threads 1 --only algo --max-ks 1 --max-tensor 1 --out out.jsonl CASE   # N = 16384
    harness/openfhe-pin/algo/summarize.py out.jsonl
    harness/openfhe-pin/algo/mutation.sh cases.list

Options of the family: `--algo-mutate NAME`, `--algo-only encrypt,lin,tensor,ks,modreduce`,
`--algo-literal-max-n M` (default 16), `--variants-max-n M` (default 64), `--max-ks n`,
`--max-tensor n`, `--forced-max-n M` (default 0: the forced, proved array forms of the BFV
multiplication pipelines also run at `N ≤ max(16 · litMaxN, M)`; the real-size suite
`../realsize/run.sh` passes 32768).

## Result on the committed fixtures (263 cases, `../run.sh`)

**7311 operations, 45389 limbs, 963104 coefficients compared; 0 differ.** Per check (operations
with `impl` limb/staged + crt/literal): `algo.encrypt` 790; `algo.add` 566, `algo.sub` 250,
`algo.addPlain` 230, `algo.subPlain` 135, `algo.negate` 72, `algo.mulConst` 428, `algo.mulPlain`
200; `algo.tensor` 845, `algo.tensorN` 45; `algo.relin` 1510 (409 staged + 350 literal + 405 staged=locked + 346 literal locked),
`algo.rotate` 720 (194 staged + 166 literal + 194 staged=locked + 166 literal locked); `algo.modReduce` 1242 (621 RNS + 621 integer);
`algo.levelReduce` 128, `algo.morph` 98, `algo.copy` 52. `algo.layout`: OpenFHE's digit
partition = the layout used, 350 of 350 (cases × levels). Coverage: 3671 of the 3687 ciphertexts
the traces produce are outputs of a compared operation; the other 16 (11 cases) are produced
inside `EvalSum` / `EvalInnerProduct`, whose fused rotation sum (v1.6.1) is not compared
(`algo.coverage` is `null` there, with the ids).

## Which Lean function is which OpenFHE operation

Source references are to OpenFHE **v1.6.1** (`src/pke/lib/…`, `src/core/include/…` at commit
b59e1f29), re-read for this table.

| check | OpenFHE v1.6.1 | Lean |
|---|---|---|
| `algo.encrypt` | `PKERNS::Encrypt(DCRTPoly, PublicKey)` (`schemerns/rns-pke.cpp:61-75`: `(*ba)[0] += plaintext`), `EncryptZeroCore` (`:152-200`: `c0 = p0·v + ns·e0`, `c1 = p1·v + ns·e1`) | `Spec.Encrypt.encrypt t b a p u e₁ e₂` with `p` the stored plaintext polynomial (centred lift of the plaintext's limbs), limb by limb |
| `algo.add`, `algo.sub`, `algo.addPlain`, `algo.subPlain` | `LeveledSHEBase::EvalAddCoreInPlace`, `EvalSubCoreInPlace` (`schemebase/base-leveledshe.cpp:632`, `:662`; element versions `:786`, `:800`) | `Challenge.Source.padZip (· + ·)`, `(· - ·)` |
| `algo.negate`, `algo.mulConst`, `algo.mulPlain` | `EvalNegateInPlace` (`base-leveledshe.cpp:63`), `LeveledSHEBGVRNS::EvalMultCoreInPlace(ct, NativeInteger)` (`scheme/bgvrns/bgvrns-leveledshe.cpp:254`), `EvalMultCoreInPlace(ct, pt)` (`base-leveledshe.cpp:814`) | `-·`, `c • ·`, `c * ·` |
| `algo.tensor` | `EvalMultCore`, `EvalSquareCore` (`base-leveledshe.cpp:684`, `:728`; 2 × 2 parts) | `Challenge.Source.tensor` |
| `algo.tensorN` | the same with other numbers of parts | `FHE.Pin.Algo.tensorGen` (convolution; not a project definition) |
| `algo.relin` | `RelinearizeInPlace` (`base-leveledshe.cpp:362-380`: `KeySwitchCore(cv[j], key[j−2])` for every `j ≥ 2`); `EvalMult(ct, ct, key)` (`:232-247`) and `EvalSquare(ct, key)` (`:282`), which key-switch `cv[2]` **only** and `resize(2)`, dropping parts ≥ 3 | `relinOpenFHE` = `c + keySwitchBGVOpenFHE`; on a 3-component operand also the LOCKED `Challenge.Realize.relinOpenFHE` (core `Challenge.Realize.ksOpenFHE`, which is also the core of the locked `keySwitchOpenFHE`): `impl = "staged=locked:…"` (the left-hand side of `addKS_locked`, every `N`) and `"literal:Challenge.Realize.relinOpenFHE"` (the locked definition run as written, `N ≤ 16`) |
| `algo.rotate` | `EvalAutomorphism` (`base-leveledshe.cpp:433-452`) → `EvalAutomorphismCore` (`:455-506`, HYBRID branch) with `EvalFastKeySwitchCoreExt` (`keyswitch/keyswitch-hybrid.cpp:389-421`): inner products of the ModUp digits of `c₁` with the key over `Q_ℓ·P`, `+ P·c₀`, **automorphism over `Q_ℓ·P`, then `ApproxModDown`** | `rotateOpenFHE161` (canonical ModUp, inner products, `P·c₀` added, `σ_g`, then `bgvModDownPoly`); also the LOCKED `Challenge.Realize.rotateOpenFHE161`: `impl = "staged=locked:…"` (left-hand side of `rotStaged161_locked`) and `"literal:Challenge.Realize.rotateOpenFHE161"` (`N ≤ 16`) |
| `algo.modReduce` | `LeveledSHEBGVRNS::ModReduceInternalInPlace` (`bgvrns-leveledshe.cpp:49-70`) → `DCRTPoly::ModReduce` (`lattice/hal/default/dcrtpoly-impl.h:786-805`; `SwitchModulus` lifts `δ` centred, `:733`) | `Basis.bgvModSwitchPoly` (RNS, centred δ) and `Challenge.Source.bgvModSwitchComp` (integers) |
| `algo.levelReduce`, `algo.morph`, `algo.copy` | `LevelReduceInternalInPlace` (`bgvrns-leveledshe.cpp:87`), `MorphPlaintext` (`base-leveledshe.cpp:579`), metadata-only changes | limbs dropped / copied |
| `algo.variant.*` (never a failure) | | the other proved variants, for the record: `keySwitchBGV` (centred), `keySwitchBGVAddDown`, `bgvModSwitchCanon`, and the v1.3.1 rotation order `rotateOpenFHE` |
| `algo.coverage` | | every ciphertext id produced in the trace is the output of a compared operation |

Decryption is compared by the checker's `a.switched` / `a.switchedQ0` (`FHE/Pin/ChecksA.lean`;
`PKEBGVRNS::Decrypt`, `scheme/bgvrns/bgvrns-pke.cpp:48`).

**The rotation changed between v1.3.1 and v1.6.1.** v1.3.1 key-switched `c₁`, added `c₀` and
applied `σ_g` last (`rotateOpenFHE`). v1.6.1 applies `σ_g` over `Q_ℓ·P` *before* ModDown, in
`EvalAutomorphism`, `EvalAtIndex`/`EvalRotate` and `EvalFastRotation` alike. With canonical
representatives ModDown does not commute with `σ_g` (a coefficient `x` becomes `−x`, whose
representative in `[0, p)` is `p − x`), so the two results differ by multiples of `t` modulo each
prime: on the
fixtures `rotateOpenFHE` reproduces 1 of the 194 recorded rotations and `rotateOpenFHE161` all
194 (both as recorded variants / checks; the mutant `automorph-last` is the old order). Proved
for `rotateOpenFHE161`: the staged execution equals the definition (`rotStaged161_openfhe`), and
its correctness and worst-case noise, `rotateOpenFHE161_spec`: for odd `g`, `N` a power of two and
valid BGV keys, the output is the RNS form of `(σ_g(c₀) + y₀, y₁)` with
`y₀ + y₁·σ_g(s) ≡ σ_g(c₁)·σ_g(tgt(s)) + e (mod Q)`, `t ∣ e`, and `‖e‖∞` within the same bound as
`keySwitchBGVOpenFHE_spec` (the bound `Spec.Budget.ksBoundAt` with `canonical = true` charges).
With OpenFHE's stored rotation key (valid for the secret `σ_{g⁻¹}(s₀)` and the target
`galois g`) this is the rotated phase `σ_g(c₀ + c₁·s₀) + e` under the user's secret `s₀`.
`rotateOpenFHE_spec` is the corresponding statement for the v1.3.1 order.

**The locked transcriptions.** `Challenge.Realize.relinOpenFHE` and `rotateOpenFHE161` (locked
definitions, integer representatives; `Challenge.Realize` states that they meet the `Spec.Trace`
contracts) are **proved equal** to what the harness runs: `FHE.Pin.Algo.addKS_locked` and
`rotStaged161_locked` (`FHE/Pin/AlgoLocked.lean`; kernel-checked, axioms `propext`,
`Classical.choice`, `Quot.sound`) say that `addKS` / `rotStaged161` with OpenFHE's stages, on the
bases `Basis.take P.src.qs ℓ`, `Basis.ofList (special primes)`, `digitsOfSizes (lay.sizes ℓ)` and
on the RNS forms of integer operands, return the RNS form of the locked functions on those
operands, under `SchemeParamsOK P`, `SpecialOK P`, `lay.okAt ℓ` (composition of `addKS_openfhe` /
`rotStaged161_openfhe` with `FHE.Realize.relinOpenFHE_toRNS` / `rotateOpenFHE161_toRNS`). The
`staged=locked` lines evaluate exactly that left-hand side (operands: CRT lifts of OpenFHE's limbs;
keys: CRT lifts over `Q_ℓ·P` read through `keys.getD j (0, 0)`; `P` the case's parameters with
`inputNoise` raised to `t/2`, which the functions do not read), decide the three hypotheses
(`theoremHypotheses`, `theoremApplies`), say whether the extracted program declares the same
layout (`declaredLayoutAgrees`), and compare with OpenFHE bit for bit. At `N ≤ 16` the locked
definitions are also run literally. No new convention appears, so no new mutant.

## Evaluation vs coefficient format

OpenFHE computes in evaluation (NTT) format. The exporter converted every polynomial with
OpenFHE's own inverse NTT (`SetFormat(COEFFICIENT)`), so every comparison here is in the coefficient
domain and relies on OpenFHE's NTT being the ring isomorphism
`Z_q[X]/(X^N+1) → Z_q^N`. That is pinned by `algo.tensor`: the trusted negacyclic `*` of two dumped
polynomials equals, limb for limb, the inverse NTT of OpenFHE's pointwise product. (The dumps hold
no evaluation-format vector, so the ψ-ordering of OpenFHE's NTT itself is not checked.)

## What is proved and what is executed

Proved (kernel-checked, axioms `propext`, `Classical.choice`, `Quot.sound` only): the staged
executions are the definitions — `ksStaged_openfhe`, `addKS_openfhe`, `rotStaged161_openfhe`,
`rotStaged_openfhe` — and `relinOpenFHE_spec`, `rotateOpenFHE161_spec`, `rotateOpenFHE_spec`
(correctness and the worst-case noise bound of `keySwitchBGVOpenFHE_spec`, for the
relinearisation, the v1.6.1 rotation and the v1.3.1 rotation). Not proved here: these operations
as `Spec.Trace` steps (for the centred variant that is `FHE/KeySwitch/Order.lean` + `Step.lean`).
Executed only: that compiled Lean code of these functions returns OpenFHE's residues on the dumps;
at `N ≤ 16` (`--algo-literal-max-n`) the unstaged definitions (`relinOpenFHE`, `rotateOpenFHE161`)
are run as well (`impl = "literal:…"`), and the limbwise ring operations are also run on the
CRT-lifted integers (`impl = "crt"`).

## Mutants (`mutation.sh`)

`modup-centred`, `moddown-centred`, `moddown-add`, `moddown-no-t`, `ks-all-centred`,
`digit-boundary`, `automorph-first` (σ_g before the key switch), `automorph-last` (the v1.3.1
order), `modreduce-canonical`. On `../fixtures/mutation.list` (20 cases; in the unmutated run 42 staged relinearisations and rotations, 16 of them rotations,
and 33 modulus switches, all exact) all 9 are killed.

## BFV cases (`FHE/Pin/BFV/*.lean`, `"scheme": "BFV"`)

`openfhe_pin --only algo` sends a case whose `pin.json` has `"scheme": "BFV"` to
`FHE.Pin.BFV.Algo.runCase`; every line carries `"scheme": "BFV"`, `mult`, `ks`, `enc`, `N`, `impl`.

| check | OpenFHE | Lean (`impl`) |
|---|---|---|
| `algo.mul` | nested `LeveledSHEBFVRNS::EvalMult(ct,ct)` / `EvalSquare(ct)` (3 components) | `Challenge.BFVMul.Fl.hpsMul` / `Fl.poverqMul` (HPSPOVERQ; HPSPOVERQLEVELED below the top or with `levelsDropped = 0`; `EvalSquare` as `poverqMul c c`) / `Fl.leveledMul` (top level, `levelsDropped > 0`), sums `Fl.floatSums A64` (`A64fma` if `build.float.fmaContraction`); `behzMul`. `literal` at N ≤ 16 (4 per case), `forced` (proved equal: `hpsForced_eq`, `poverqForced_eq`, `leveledForced_eq`, `behzForced_eq`, `FHE/Pin/BFV/Stage.lean`) at N ≤ 256, `staged` array mirror at every N (`FHE/Pin/BFV/Fast.lean`), cross-checked by `algo.mul.literal-vs-staged`, `forced-vs-staged` and `spot` (mirror vs the locked scalar functions on sampled coefficients) |
| `algo.relin` | `RelinearizeCore`, `LeveledSHEBase::RelinearizeInPlace` | HYBRID: `keySwitchBGVOpenFHE` at plaintext modulus 1 (`relinOpenFHE … 1`), `staged` (proved, `addKS_openfhe`) and `literal`; BV, and the HPSPOVERQLEVELED top-level drop (`ScaleAndRound` to `Q_l`, key switch, `ExpandCRTBasisQlHat`): `mirror-only` |
| `algo.automorph`, `algo.rotate` | `LeveledSHEBFVRNS::EvalAutomorphism`: `RelinearizeCore` with the key for `g`, then `σ_g` | `σ_g` of the traced inner output; the whole rotation as `rotateOpenFHE` (v1.3.1 order) at t = 1 |
| `algo.add/sub/negate/mulConst/mulPlain/tensor` | ring operations | trusted `Spec.NPoly` per limb (`limb`) and on CRT lifts (`crt`); mixed representations: `mirror-only` |
| `algo.addPlain/subPlain` | `c₀ ± TimesQovert(p)`, `TimesQovert(p) = ⌈Q·p/t⌉` | `mirror-only` (`bfvAddPlainRounded` rounds to nearest: `algo.variant.addPlain`) |
| `algo.encrypt` | `PKEBFVRNS::Encrypt`, STANDARD and EXTENDED (`ScaleAndRoundPOverQ`) | `mirror-only` (there is no trusted BFV encrypt) |
| `algo.compress` | `Compress`: `DropLastElementAndScale` per dropped limb | `staged` mirror and `Challenge.BFV.bfvModSwitchComp` on the CRT lift |
| `algo.decrypt` | `PKEBFVRNS::Decrypt` raw output | the library's procedure, `mirror-only` (`FHE/Pin/BFV/Routines.lean`) |
| `algo.decrypt.exact` | same | `Spec.Scheme.bfvDecrypt` (exact rounding); `null` (reported, not failed) when the ciphertext is not an encryption under `s` |
| `algo.observe.relin` | — | OpenFHE's own decryptions before / after its relinearisation (nothing recomputed) |

Arithmetic: `FHE/Pin/BFV/Float64.lean` (`A64`, `A64fma`: binary64 round-to-nearest-even on ℚ;
dyadic form `D` for the mirrors). `Spec.Float.Conforms A64` is NOT proved. Summaries:
`summarize_bfv.py`. Mutants: `mutation_bfv.sh` (kill detection relative to the unmutated run).
