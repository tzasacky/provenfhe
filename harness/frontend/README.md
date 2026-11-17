# fhe_check: will this BGV program always decrypt correctly?

`fhe_check` reads a BGV program and its parameters, as produced by Google HEIR or OpenFHE, and
answers **CERTIFIED**, **NOT CERTIFIED** or **UNSUPPORTED**. A CERTIFIED answer comes with a
machine-checked Lean theorem: under the assumptions the report lists, every output decrypts
exactly, for every key, every input and every run. By default it is a worst-case answer. With
`--kappa K` the noise of the *fresh encryptions* is instead bounded with probability at least
1 − 2^-K over the encryption randomness (everything after encryption stays worst case); the
certificate then says exactly that. NOT CERTIFIED means the analysis could not show the program
safe; it does not mean the program fails in practice.

Everything in this directory (extractors, schema, preview, tests) is **untrusted** glue. The
verdict is computed by the executable `fhe_check` (`FheCheck.lean`, `FHE/Check/`), which runs
verified Lean definitions compiled by the Lean compiler.

## Quickstart

Prerequisites: [elan](https://github.com/leanprover/elan) (it installs the Lean toolchain named in
`lean-toolchain`, Lean 4.35.0), git, python3 (stdlib only). Build the checker once:

```
lake exe cache get              # optional: downloads Mathlib's prebuilt .olean files
lake build fhe_check            # writes .lake/build/bin/fhe_check
```

Without `lake exe cache get` the first `lake build fhe_check` compiles Mathlib from source (269 s on
128 cores in a fresh-clone test; much longer on a laptop).
With it (tested 2026-11-13 in a fresh clone with empty caches: Mathlib's cache for this
revision, `v4.35.0`, exists): 9031 files downloaded in 3 min here, then `lake build fhe_check`
compiles only the project and the C code of the Mathlib modules the executable links (160 s on
128 cores; no Mathlib `.lean` file is elaborated).

**I have a HEIR program (`prog.mlir`).** Get `heir-opt` from HEIR's dated nightly release
`nightly-2026.11.11` (HEIR commit 86d9fc0acd760bee21003830a6cfba54d6182bec), the version the
examples were made with:

```
curl -LO https://github.com/google/heir/releases/download/nightly-2026.11.11/heir-opt-manylinux_2_28_x86_64
echo "ff9a597eb115dcf6ad29d21ee599b25a6b9d278d70dec6abdb0a9b93bc5f078b  heir-opt-manylinux_2_28_x86_64" | sha256sum -c
chmod +x heir-opt-manylinux_2_28_x86_64 && mv heir-opt-manylinux_2_28_x86_64 heir-opt
```

Then compile the program for BGV on the Lattigo backend, extract, check (`annotate-noise-bound=true`
makes HEIR's own bound appear in the extracted file, as `heirNoiseBoundLog2`):

```
./heir-opt --annotate-module="backend=lattigo scheme=bgv" \
  --mlir-to-bgv="noise-model=bgv-noise-by-bound-coeff-worst-case annotate-noise-bound=true" prog.mlir > prog.bgv.mlir
python3 -I harness/frontend/heir/extract_bgv.py prog.bgv.mlir > prog.fhecheck.json
.lake/build/bin/fhe_check prog.fhecheck.json
```

To reproduce the `mult_dep_8` example, `prog.mlir` is
https://github.com/google/heir/blob/86d9fc0acd760bee21003830a6cfba54d6182bec/tests/Examples/common/mult_dep_8.mlir
(raw: `https://raw.githubusercontent.com/google/heir/86d9fc0acd760bee21003830a6cfba54d6182bec/tests/Examples/common/mult_dep_8.mlir`).
Programs with loops (`simple_sum`, `box_blur_16x16`, `roberts_cross_16x16`) need
`unroll-fhe-kernel-loops=true` in `--mlir-to-bgv`, as HEIR's own tests pass it.

The extractor needs HEIR's Lattigo path, because only that path carries the actual primes. The
`noise-model` option only changes which parameters HEIR picks. HEIR has four BGV noise models
(`heir-opt --help`; `lib/Transforms/GenerateParam/GenerateParam.td:11-15` at 86d9fc0a):
`bgv-noise-by-bound-coeff-worst-case` (coefficient bounds with expansion factor N, error bound
6σ = 19.2); the DEFAULT `bgv-noise-kpz21` = `bgv-noise-by-bound-coeff-average-case` (the same
formulas with the heuristic expansion factors 2√N for products and 4√N for modulus switching,
`lib/Analysis/NoiseAnalysis/BGV/NoiseByBoundCoeffModel.cpp:48-74`: "average-case" is HEIR's own
name for this heuristic high-probability bound, not an average); `bgv-noise-by-variance-coeff`
(`mp24`, a variance model whose documentation says it "may give underestimates",
`GenerateParam.td:27-30`); and `bgv-noise-mono` (a canonical-embedding model, MMLGA22). Only the
worst-case model's parameters are designed to meet a worst-case analysis; with the others HEIR's
parameters are usually NOT CERTIFIED (a coverage study run once, not part of this release: 0 of 12 programs under the
default and mp24 models, 2 of 11 under mono, 11 of 11 under worst-case).

**I have an OpenFHE program.** The supported library is upstream **OpenFHE v1.6.1**
(openfheorg/openfhe-development, tag `v1.6.1`, commit b59e1f291965f14fbee5172cd83a20f5b856204f)
with this directory's tracer: `openfhe/openfhe-v1.6.1-tracer.patch` (observation hooks only; see
"Tracer patch") and `openfhe/fhecheck-tracer.h`. Build it (no sudo; needs git, a C++17 compiler
(gcc 13.3 used; the script configures the library with `WITH_OPENMP=OFF`), cmake ≥ 3.22 and < 4 and ninja on PATH, e.g.
`uv venv harness/.venv-cpp && uv pip install -p harness/.venv-cpp "cmake<4" ninja`; a from-scratch
build of the library and the examples took 1 min 30 s on 128 cores shared with other jobs):

```
harness/frontend/openfhe/build_openfhe.sh   # clone v1.6.1, apply the patch, build, install, build bgv_demo
                                            # and bfv_demo into harness/build/frontend-openfhe/
```

`build_openfhe.sh` builds the library single-threaded (`WITH_OPENMP=OFF`): the committed
recordings reproduce byte for byte only from the build configuration they were recorded with
(single-threaded).

Compile your program like `openfhe/build.sh` compiles `bgv_demo.cpp` (`-std=gnu++17`, the
include directories under `harness/build/frontend-openfhe/install/include/openfhe`,
`-lOPENFHEpke -lOPENFHEcore` with an rpath). Run it UNMODIFIED with tracing switched on by the
environment, single-threaded:

```
FHECHECK_TRACE_DIR=out OMP_NUM_THREADS=1 ./prog      # every BGV or BFV context writes out/p<pid>.ctx<k>.{trace.jsonl,params.json}
python3 -I harness/frontend/openfhe/extract.py --params out/p*.ctx1.params.json --trace out/p*.ctx1.trace.jsonl \
  --outputs-from-decrypt > prog.fhecheck.json
.lake/build/bin/fhe_check prog.fhecheck.json
```

(a BFV context: `openfhe/extract_bfv.py` with the same `--params`/`--trace`, see "BFV extraction")
(or set the tracer yourself as `bgv_demo.cpp` does: `cc->setTracer(std::make_shared<fhecheck::JsonTracer>(...))`
**before** `KeyGen`). The trace must contain the key generation and the encryptions: the extractor
takes ciphertext inputs only from traced `Encrypt` calls, so that no untraced change to a
ciphertext can pass as a fresh encryption, and it checks where every key comes from ("Key
provenance"). `OMP_NUM_THREADS=1` matters: the tracer is not designed for concurrent calls; a
traced call from another thread or from inside an OpenMP parallel region makes it write an error
record and the extractor refuses the trace (calls are serialised by a mutex, so nothing crashes).

All four BGV scaling techniques are supported, including OpenFHE's default FLEXIBLEAUTOEXT (see
"OpenFHE scaling techniques" below). Extractor options:
- outputs: every ciphertext the program passes to a traced `Decrypt` must be a value of the
  extracted program (otherwise the extraction FAILS: the program changed it outside the traced
  calls), and is an output. Default: the values no later instruction consumes PLUS every decrypted
  one; `--outputs-from-decrypt`: exactly the decrypted ones; `--outputs a,b` names them and must
  include every decrypted one. A trace without `Decrypt` (the demo drivers decrypt with the tracer
  off) certifies the never-consumed values; `crossCheck.outputs` says which rule applied
  (same options for `extract_bfv.py`);
- `--no-decrypt-switch`: declare textbook decryption at the output's level instead of OpenFHE's
  `Decrypt` (see "Decryption");
- `--assume-fresh-inputs`: for a trace that starts after encryption, every 2-part ciphertext no
  traced operation produced is ASSUMED to be a fresh public-key encryption (the input's `origin`
  says so). It applies to INPUTS only and is refused otherwise: the ciphertext must be used before
  the first traced operation produces a ciphertext, the trace must contain no traced `Encrypt` (a
  traced `KeyGen` is allowed: keys generated under the trace, inputs built or deserialized outside
  it), and for BFV its noiseScaleDeg must be 1. (A ciphertext changed by an untraced call
  in the middle of the program has a content id no traced operation produced; without these
  conditions it would pass as a fresh encryption.) Consequence: every input must be used by the
  first traced operation(s); a program whose inputs enter later must be traced from before
  encryption;
- `--assume-single-party-keys`: for a trace without the key generation (keys deserialized from
  another process), ASSUME that every key is a single-party key of one secret instead of checking it
  (the file's `noiseDerivation.keyProvenance` says so);
- `--compact` (no indentation) and `--cse` (merge exact duplicate instructions) for large
  programs (see "Large programs").

`bgv_demo run DIR [--scal FIXEDMANUAL|FIXEDAUTO|FLEXIBLEAUTO|FLEXIBLEAUTOEXT|default] [--depth D]
[--qbits B] [--firstbits B] [--evaladd A] [--kscount K] [--n N] [--ringdim N] [--time R] [--prog P]` writes `params.json`,
`trace.jsonl` and `values.json` for a built-in program `P`: `chain` ((a·b)^(2^(D−1))), `dot`
(a·b + rot(a·b, 1) + c), `rot`, `plain` ((a·b)·p₁ + p₂ − p₃ with `MakePackedPlaintext(v)`
plaintexts), `plainlvl` (the same with plaintexts made at the ciphertext's level and depth),
`lr` (`ModReduce(a·b) + LevelReduce(c, 1)`), `rotsum` (`EvalAtIndex`/`EvalRotate` by 1, 2, −1),
`negate` (−(a·b) + c, `EvalNegate`), `subpt` (p₁ − a·b, `EvalSub(plaintext, ciphertext)`), `symenc`
(a·b + c with c encrypted under the PRIVATE key), `nocheck` (`Relinearize(EvalMultNoRelinNoCheck(a, b))`);
and, refused by the extractor and kept for the refusal fixtures, `innerprod` (`EvalInnerProduct`,
i.e. `EvalMult` + `EvalSum`), `coefpk` (CoefPacked plaintexts) and `threepart` (`EvalMult` with a
key on a 3-part operand). `--ringdim N`
sets the ring dimension and keeps the security level (OpenFHE checks it; `--n` sets HEStd_NotSet);
`--time R` times R untraced re-runs of the evaluation into `timing.json`. `bgv_demo dump cc.json`
prints `params.json` for a serialized context. `openfhe/make_examples.sh` regenerates every OpenFHE
example and fixture.

Options: `--kappa K` selects the probabilistic fresh-noise mode (see "Probabilistic fresh
noise"); `--json` prints a machine-readable report; `--steps` prints the bound after every
instruction; `--dump-program` prints the decoded `Source.Program` that the certificate is about;
`--no-suggest` skips the "smallest fix" search on NOT CERTIFIED; `--max-instructions N` sets the
program-size limit below (0 = none); `--time` prints the time of each phase. `fhe_check recommend FILE`
finds parameters that ARE certified (see "Getting parameters that are certified").
Exit codes: 0 CERTIFIED, 1 NOT CERTIFIED, 2 UNSUPPORTED, 3 INVALID INPUT, 4 usage error.

Limits on `--kappa K`: K = 0 is a usage error (a failure probability of at most 2^-0 = 1 says
nothing), and so is K > 10^6. For K < 40 the report carries a `WARNING` line directly under the
verdict: 2^-K is then not negligible, and the verdict should not be read as "decrypts correctly".
The floor 40 is a convention of this tool (one in 2^40 per set of encryptions), not a theorem.

Limits on the input (all answered INVALID INPUT, before or during decoding, so that no input can
hang or crash the tool): the file is at most 1 GB (checked on its size before it is read); arrays and objects nest at most 64 deep; a
number token is at most 400 characters and has no positive exponent (a negative one, in a
printed-only float, has at most 3 digits); every integer field must be a plain integer or a
decimal string of at most 400 digits; an input name
declared twice, an output listed twice, and a `freshEncryption.inputs` entry that is repeated or
is not a declared input are errors. (`Source` reads the first declaration of a name only, so a
second declaration with another shape or bound would silently not be the program certified.)

Program size (answered UNSUPPORTED, exit 2, after decoding and before any analysis, for BGV
and BFV alike): a program of more than 2,000,000 instructions is refused with its instruction
count, the limit and an estimate of time and memory; `--max-instructions N` changes the limit
(0 = no limit), also for `fhe_check recommend`. The limit is a resource guard. The check is
near-linear in the program length: the verdict is computed by `FHE.Holes.certifyFast`
(`certifyBFVFast`), which keeps the environments of the analysis in search trees and runs the
body once, and which the locked statements `Challenge.Fast.certifyFast_eq`
(`certifyBFVFast_eq`) prove equal to `Challenge.Certify.certify?` (`certifyBFV?`) on every input.
(The reference analyzers keep their environments as chains of closures and are quadratic: 100,000
instructions took 15 to 19 minutes, the old default limit.) Measured
(`harness/eval/analyzer-speed/RESULTS.md`; one core of a 128-core machine under load): about 15
to 25 microseconds per instruction for BGV and 25 to 80 for BFV, and 0.7 to 1.8 kB of peak memory
per instruction; 1,000,000 instructions in 13 to 24 s (BGV) and 24 to 77 s (BFV) with 0.9 to
1.7 GB. The 2^18-term sum with 44 squarings of ePrint 2026/2546 (524,375 instructions): 17 s
(BGV), 24 s (BFV). JSON reading and decoding are linear and about a fifth of the BGV total.

## What the report says

- **What the plain CERTIFIED headline means (policy, both schemes).** "CERTIFIED: every output
  decrypts correctly" is printed only when the certified statement covers what the user READS.
  BGV: user-level decryption is covered (the input carries the library's scaling data, declares
  the switched decryption, and `Spec.Scaling.scaleOK?` accepts, so `Challenge.Scaling.certify?_user`
  applies; the report line `user-level decryption covered`). When it is not covered: an input
  extracted from a library (`source.tool = "openfhe"`) is NOT CERTIFIED, with the reason (the
  phase-level certificate is withheld: e.g. a FIXED* context whose primes are not
  1 mod t, which the extractor refuses); any other input (hand-written,
  HEIR without scaling data) is printed `CERTIFIED AT PHASE LEVEL: the raw (phase-level)
  decryption of every output is correct ...; user-level decryption depends on the backend and is
  NOT covered` (exit 0; JSON: `verdict` CERTIFIED, `verdictLabel` CERTIFIED AT PHASE LEVEL). BFV:
  the library decryption side is in "BFV". Every ciphertext the traced program decrypts is an
  output ("What the frontend assumes", 3), so no decrypted value is outside the certificate.
- **Verdict.** CERTIFIED is issued only where the locked function `Challenge.Certify.certify?`
  (`Challenge/Certify/Defs.lean`) returns a certificate for the decoded data (parameters,
  key-switching layout, program, decryption, mode). `certify?` makes every check itself
  (`schemeParamsOK?`, `specialOK?` (special primes odd, pairwise coprime, coprime to the chain
  and to t), the declared modulus-switching method (`t-corrected-centred` or no certificate,
  whether or not the program switches: `certify?_centred`), the layout at every level and that
  it restricts from the top level (`Spec.Certify.layoutOK?`), the key noise against
  `Spec.Certify.keysRestrict?` (2·⌊keyNoise/t⌋·t < q₀·P), `refAnalyze` on the program and on
  each output alone, `certOK?` per output, and in the fresh modes `freshOK?` and the replaced
  input noise); the rest of the tool decodes, prints, words these refusals, and can only refuse
  further (a disagreement with the frontend's `expect` annotations, or a printed figure that is
  not the certificate's). On CERTIFIED, a line says that what is certified is correctness (exact
  decryption), not security.
- **Security note** (never part of the verdict): log₂(Q·P) of the file (every ciphertext limb,
  including FLEXIBLEAUTOEXT's extra one, and every special prime) and the caps at the file's N
  for 128-, 192- and 256-bit classical security with a ternary secret, from the
  HomomorphicEncryption.org standard's table (an INPUT ASSUMPTION; the table and its citation are
  under "Security limit" below; the rows 2^16 and 2^17 are labelled as OpenFHE's extension). An N
  with no row (below 1024, above 2^17, not a power of two) is said so: below 1024 is "not secure
  per the standard". `--json`: the `security` object (`partOfVerdict: false`) and, on CERTIFIED,
  `certifiedProperty`.
- **Parameters**, with the verified parameter checks `Spec.schemeParamsOK?` and
  `Spec.Budget.specialOK?`. On a failure the report names the first failing clause, for example
  that a modulus is not prime.
- **Budgets**, computed by the tool from the parameters, never read from the input:
  - key switching: `Spec.Budget.ksBudget`, the worst-case error of one hybrid key switch,
    maximised over the levels;
  - modulus switching: `Spec.Budget.msBudget` = ⌈t(1+N·B_s)/2⌉ for a 2-part ciphertext,
    `Spec.Budget.msBudgetOne` = ⌈t/2⌉ for a 1-part value (a plaintext operand), and
    `Spec.Budget.msBudgetAt P k` = ⌈t·Σ_{i<k}(N·B_s)ⁱ/2⌉ for a k-part value (a product not yet
    relinearized; `Challenge.Budget.modSwitch_realizable_parts`; JSON `budget.modSwitchMany`).
- **Warnings**, directly under the verdict: K below 40; a `--kappa` run that fell back to the
  worst case of a fresh encryption; a frontend `inputNoise` below the worst case of a fresh
  encryption with the sampler bounds the same file declares (in worst-case mode the certificate
  then rests on an assumption the file's own sampler description does not support); a
  `SECURITY` warning when log₂(Q·P) exceeds the 128-bit cap at N, or N is below 1024.
- **Mode**: worst case, or `--kappa K` (with `--l2`: the ℓ₂ description) with the computed error
  bound ε and input noise.
- **Per output**: the proved noise bound and the margin, in bits, below Q/2 at the output's
  level; and, when the file declares OpenFHE's decryption, the bound on the phase switched to one
  limb (`Spec.Decrypt.decBound`) and its margin below q₀/2. An output left under a rotated key
  (after `automorph` without `keySwitch`, or an input declared under a Galois element other than
  1) is flagged and the verdict is NOT CERTIFIED: the noise theorems speak of decryption under
  σ_g(s), and a library decrypts with s (`Spec.Encrypt.certOK?`).
- **Which analyzer ran**: `Challenge.Headline.refAnalyze`, the reference analyzer, which is the
  function every cited theorem is about. (The hole `FHE.Holes.analyze` of the headline theorem
  is defined as the same function today.) A CERTIFIED verdict instantiates exactly one locked
  statement of the form `certify? x = some c → …`, named in the report and in the
  `certificateTheorem` field of `--json`: `Challenge.Certify.worst_certified` (worst case),
  `fresh_kappa_certified` (`--kappa`), `fresh_worst_certified` (`--kappa` falling back to the
  worst case of a fresh encryption) or `fresh_l2_certified` (`--kappa --l2`). Each is about all
  outputs jointly (one failure event), each output with its own bound. Also cited:
  `certify?_spec`, `certify?_paramsOK`, `certified_run_exists` (a certified program has runs), and
  the one-program pins of `Challenge.FreshNoise` the proofs use.
- **Suggestions** on NOT CERTIFIED (a search, not a theorem): the largest K for which `--kappa K`
  certifies, and the smallest uniform growth of the moduli that certifies (see "Smallest fix").
- **On failure**: the first failing instruction and the bound that overflowed, with the number
  of bits by which it overflowed. The location is confirmed by the verified analyzer on the
  program prefixes.
- **What the certificate means.** A fixed statement that names the Lean theorems and lists, as
  ASSUMPTIONS, everything that is an input rather than a theorem:
  - the fresh-input, key and secret noise bounds the frontend supplied;
  - that the library's operations meet the per-operation contracts (proved for this repository's
    reference algorithms, **not** for OpenFHE's C++ or Lattigo's Go);
  - that the analysis is worst case (or, with `--kappa`, which sampler description is assumed;
    with `--l2`, the ℓ₂ bounds on the key and the sub-Gaussian proxies, and which of them the
    input supplied);
  - which decryption is covered;
  - BGV only, and no security claim;
  - that the Lean compiler is trusted.

  Neither OpenFHE, HEIR nor Lattigo is verified by this tool.

## Real examples (`examples/`)

| Input | Verdict | Exact figures |
|---|---|---|
| OpenFHE at depth 2 with the non-default scaling technique FIXEDMANUAL, otherwise default parameters (N = 2^14, three 45-bit primes, t = 65537, HYBRID), program `(a*b)^2` | NOT CERTIFIED | overflow at `body[3]` (`square`, level 2): bound 2^97.15 against Q/2 = 2^89.00, **8.15 bits** over |
| OpenFHE, depth 8, 55-bit scaling moduli (N = 2^15, nine 55-bit primes, three special primes, dnum 3), same chain to depth 8 | CERTIFIED | output at level 1: bound 1074841706 = 2^30.00, Q/2 = 2^54.00, **margin 24.00 bits** |
| HEIR `mult_dep_8`, worst-case noise model (N = 2^14, Q = 32+3×45 bits, P = 2×45 bits) | CERTIFIED | output bound **796529503 = 2^29.57**, the same as HEIR's own annotation (`noise.bound = "29.57"`); Q/2 = q₀/2 = 2^31.00, **margin 1.43 bits** |
| HEIR `mult_dep_8`, HEIR's default model `bgv-noise-kpz21` (HEIR's "average-case" label for a heuristic bound; N = 2^13, Q = 27+3×34 bits) | NOT CERTIFIED | overflow at `body[6]` (the third `mul`, level 2): bound 2^111.05 against Q/2 = 2^60.00, **51.05 bits** over |

Further examples:
- `openfhe_rot_depth2`, `openfhe_dot_depth2`: real OpenFHE traces with rotations
  (`automorph` + `keySwitch`). Both are CERTIFIED for OpenFHE's decryption (phase switched to one
  limb, see "Decryption"): switched-phase bound 2^15.00 against q₀/2 = 2^44.00, a margin of 29.00
  bits; at the output level the margins are 96.69 and 46.41 bits.
- `openfhe_<technique>_<program>` for every scaling technique, with OpenFHE's default
  parameters at depth 2. The programs are `chain`, `plain`, `plainlvl`, `lr`, `rotsum`, `negate`
  (`EvalNegate`), `subpt` (`EvalSub(plaintext, ciphertext)`), `symenc` (one input encrypted with the private key), `nocheck`
  (`EvalMultNoRelinNoCheck` + `Relinearize`), plus `dot`/`rot` under FLEXIBLEAUTOEXT;
  `openfhe_default_chain_depth1` leaves the technique unset.
  - CERTIFIED (worst case): every `lr`, `rotsum`, `negate`, `subpt`, `symenc`, `nocheck`, `dot`, `rot`, and
    every `plain`/`plainlvl` (the automatic modes' 1-part modulus switch has a proved budget).
    Decryption margins at q₀ for `lr`/`rotsum`/`negate`/`subpt`/`symenc`/`nocheck`: 29.00 bits for
    FIXEDMANUAL, 17.81 for FIXEDAUTO, 17.00 for FLEXIBLEAUTO and 15.00 for FLEXIBLEAUTOEXT (they
    were 15.00, 3.81, 3.00 and 1.00 when decryption was modelled by 2-part switches).
    `plain`/`plainlvl`: 14.75 (FIXEDMANUAL), 3.25 (FIXEDAUTO), 2.43 (FLEXIBLEAUTO), 2.98
    (FLEXIBLEAUTOEXT).
  - `symenc` with `--kappa 128`: UNSUPPORTED, by design (its private-key input is not a fresh
    public-key encryption; see "Key provenance").
  - NOT CERTIFIED (worst case): every `chain`. With `--kappa 128` the FIXEDMANUAL chain
    (`openfhe_depth2_fixedmanual`) is CERTIFIED with 6.47 bits; the automatic-mode chains are not.
  - `tests/expected.tsv` has each figure.
- Refused (`tests/refused/`, 12 fixtures at N = 1024, each with the message): `innerprod`
  (`EvalInnerProduct` = `EvalMult` + `EvalSum`, whose `EvalSum` OpenFHE v1.6 computes as a fused
  rotation sum, see "Unsupported"), `coefpk` (CoefPacked plaintexts) and `threepart` (`EvalMult`
  with a key on a 3-part operand), under each scaling technique.
- `heir_dot_product_8.worstcase`: HEIR output with `mul_plain` and three `rotate_cols`. CERTIFIED,
  bound 2^28.34 against HEIR's own annotation of 2^28.18, margin 2.66 bits. Every `expect`
  (HEIR's own level and number of parts) matches `Source.step`.
- `exampleBGV31_one_limb_digits` / `exampleBGV31_two_limb_digit`: the sample parameters with one
  limb per digit (CERTIFIED, ksBudget 2^35.02) and with a single two-limb digit (ksBudget 2^65.00,
  NOT CERTIFIED by 6.00 bits).
- `heir_cmux.worstcase`: HEIR's `cmux` (it contains `bgv.sub_plain %pt, %ct`, plaintext minus
  ciphertext, mapped to `negate` then `addPlain` as HEIR's `--scheme-to-lattigo` lowers it:
  `lattigo.rlwe.negate_new` then `lattigo.bgv.add`). CERTIFIED, bound 2^27.32 against HEIR's own
  annotation of 2^27.17, margin 2.68 bits.
- HEIR's loop programs `simple_sum`, `box_blur_16x16` and `roberts_cross_16x16` are accepted by
  `heir-opt` on the Lattigo path only with `unroll-fhe-kernel-loops=true` (HEIR's own test
  setting); without it they fail inside `heir-opt` ("tensor.extract with dynamic cleartext indices
  not supported yet", "value has invalid level"). All three extract and are CERTIFIED under HEIR's
  worst-case model (the same coverage study).

**What the agreement with HEIR's annotations does and does not show** (HEIR @ 86d9fc0a, Lattigo v6.1.0, HEIR's worst-case model; the step-by-step comparison was run once and is not part of this release):
- On `mult_dep_8` (and `mult_dep_16`, `mult_indep_*`, `binops`) the tool's bound equals HEIR's
  annotation to two decimals at every step (at full precision within 0.0002 bit). That is two
  implementations of the same dominant textbook terms (product N·B₁·B₂, modulus switch
  B/q + t(1+N)/2, both from the KPZ21 / DPSZ12 worst-case formulas); the terms that differ are below
  2^-12 relative. It is NOT independent validation.
- The informative cases are where the rules differ:
  - (a) `mul_plain`. HEIR's worst-case rule bounds a plaintext's coefficients by t/2, i.e. it
    assumes a centred lift (`lib/Analysis/NoiseAnalysis/BGV/NoiseByBoundCoeffModel.cpp:151-168`,
    comment at `:158-163`), while Lattigo multiplies by the [0, t) lift (`schemes/bgv/encoder.go`
    `RingT2Q`, `:350-378`; `evaluator.go:736-749`). The tool uses t − 1. On `dot_product_8` the
    tool's output bound is 2^28.34 against HEIR's 2^28.18, and replacing t/2 by t − 1 in HEIR's
    rule reproduces the tool's figure to 0.0004 bit. Lattigo v6.1.0's own `Mul(ct, pt)` and
    `Rescale` were executed on a crafted input ciphertext whose noise is within HEIR's own bound
    for that step, with a plaintext whose every coefficient is t − 1: (1) with a Lattigo-generated
    key, the `mul_plain` result exceeds HEIR's bound for that step by 0.999 bit; (2) with the
    all-±1 ternary key and the rescale rounding aligned, the output after `Rescale` exceeds HEIR's
    output bound by 0.16 bit. Both stay within the tool's bound (tight to 0.0002 bit in (2)). This
    confirms the per-operation rule difference on Lattigo's code. It is a contract-level witness
    (crafted input noise; in (2) a chosen key), not an honest end-to-end run from fresh
    encryptions, and there is no decryption failure (2^28.34 < q₀/2 = 2^31).
  - (b) Rotations. HEIR's key-switching term treats every digit as the size of P
    (`NoiseByBoundCoeffModel.cpp:198-241`, "we use log(pi...) as an approximation", `:221-223`);
    the tool uses the actual digit moduli. On `simple_sum` (P = 82 bits, digits 63 and 41 bits)
    HEIR's term is 3.58 bits above the tool's at every `rotate_cols`: HEIR is conservative there.
    With a single digit as large as P (`box_blur`) the two differ by 0.02 bit.

Budgets for the first four inputs:

| Input | E.keySwitch | E.modSwitch |
|---|---|---|
| OpenFHE depth 2 | 2^31.00 | 2^29.00 |
| OpenFHE depth 8 | 2^32.59 | 2^30.00 |
| HEIR worst-case | 2^35.32 | 2^29.00 |
| HEIR default | 2^34.33 | 2^28.00 |

Corrections to the earlier research predictions:
- **OpenFHE depth 8, 55 bits:** ~23 bits was predicted; the margin is **24.00 bits**.
- **HEIR `mult_dep_8`, worst case:** confirmed. It flips to CERTIFIED with the tightened
  modulus-switching budget, with the exact bound above.
- **HEIR `mult_dep_8`, default model:** ~59 bits was predicted. The first overflow is **51.05
  bits**, at the third multiplication; the analysis stops there.

Provenance of the inputs:
- **HEIR:** the `.mlir` files are verbatim `heir-opt` output on HEIR's
  `tests/Examples/common/{mult_dep_8,dot_product_8,cmux}.mlir` at commit
  86d9fc0acd760bee21003830a6cfba54d6182bec
  (https://github.com/google/heir/blob/86d9fc0acd760bee21003830a6cfba54d6182bec/tests/Examples/common/mult_dep_8.mlir),
  run with `annotate-noise-bound=true`, plus `noise-model=bgv-noise-by-bound-coeff-worst-case` for
  the worst-case files (`dot_product_8` also with `min-slot-count=2048`, HEIR's own test option).
- **HEIR binary:** the HEIR nightly release tagged `nightly-2026.11.11` (commit
  86d9fc0acd760bee21003830a6cfba54d6182bec; source asset `heir-v2026.11.11.tar.gz`; published
  2026-11-11T02:08Z from `main`), asset `heir-opt-manylinux_2_28_x86_64`, sha256
  `ff9a597eb115dcf6ad29d21ee599b25a6b9d278d70dec6abdb0a9b93bc5f078b`. That digest matches
  GitHub's. The binary is kept in `harness/build/heir-nightly/`, which is gitignored. (The tag
  `nightly` moves; `heir-v2026.11.11` is not a tag.)
- **OpenFHE:** `bgv_demo run` output on upstream OpenFHE v1.6.1 with the tracer
  (`openfhe/build_openfhe.sh`), `OMP_NUM_THREADS=1`.
  - `openfhe_depth2_fixedmanual.*` uses `--depth 2`.
  - `openfhe_depth8_q55_fixedmanual.*` uses `--depth 8 --qbits 55 --firstbits 55`.
  - `openfhe/make_examples.sh` regenerates all of them (byte-identical `.fhecheck.json` files on
    re-runs). Each trace starts before key generation and was cross-checked on levels, scales and
    plaintext values.
  - OpenFHE chose the primes, the ring dimension and the special primes in all cases.
- **Speed:** each example takes 1 to 25 ms of checking (about 0.05 s with process start). For
  large programs see "Large programs" and the measurements under "Limits on the input".

## Large programs

Real programs reach sizes far above the examples: FHERMA's max-element circuit (N = 2^16, depth
22) runs 1 h 57 min single-threaded under the tracer and writes a 1.95 GB trace; bgv-extend's
integer division writes 2 GB. What the frontend does about it (all UNVERIFIED glue):
- `extract.py` reads the trace as a stream (each top-level call is translated when it ends, then
  dropped): the 1.95 GB FHERMA trace extracts in 27 s with 83 MB peak RSS, the 2 GB bgv-int-division
  trace in 9 min 43 s with 3.4 GB (the program itself is 2,183,901 instructions).
- `--compact` and `--no-provenance` shrink the file (bgv-int-division: 203 MB of program, 239 MB of
  provenance); `fhe_check` reads files up to 1 GB.
- `--cse` merges exact duplicates: an instruction with the same op, the same (already merged)
  operands, the same constants and the same `expect` as an earlier one. Why this cannot turn NOT
  CERTIFIED into CERTIFIED (or change any bound): the verified analyzer's bound for an instruction
  and `Source.step`'s result are functions of the op, its constants and its operands only, so the
  duplicate gets exactly the original's bound, level and parts, every check made on it was
  already made on the original, and every later instruction sees the same operand bounds; the
  outputs are computed after the merge. Dead-code elimination is NOT done: the analyzer also
  checks values no output depends on, and removing one could hide an overflow. Effect:
  bgv-int-division 2,183,901 → 1,580,806 instructions; FHERMA max-element 35,196 → 31,023; on
  max-element the verdict and the overflow (25.66 bits at the same `mul`) are unchanged.
  Regression: `tests/keyprov/check.py` (a duplicated `EvalMult`).
- `--allow-truncated` extracts the completed calls of a killed run (a prefix, stated in the file).

What `fhe_check` can then check: the check is near-linear (the fast path proved equal to the
locked decision, "Limits on the input"). FHERMA max-element, 35,196 instructions, NOT CERTIFIED at
`body[410]` in 0.33 s; bgv-int-division (1.58 million instructions after `--cse`)
is within the default limit of 2,000,000 (not re-run here; by the measured rate about a minute).

## Constants the frontends supply, with sources

These values are **assumptions** of the certificate. They are printed in every report under
"noise derivation".

**OpenFHE.** Source: upstream OpenFHE v1.6.1 (openfheorg/openfhe-development, commit
b59e1f291965f14fbee5172cd83a20f5b856204f), built with `WITH_REDUCED_NOISE=OFF`. File:line
references are to that commit.
- **Error bound.** σ = 3.19f
  (`src/pke/include/scheme/gen-cryptocontext-params-defaults.h:132`). The Peikert sampler builds
  a table of `ceil(σ·12.00610553538285)` = **39** entries and throws when a sample falls outside
  it (`src/core/include/math/discretegaussiangenerator-impl.h:81-82,94-99`). So |e| ≤ 39 is a
  hard bound, and it is the bound the extractor declares. The extractor also declares a bound on
  the generator's mean, 3431/2^64, as `freshEncryption.mean` (see "Probabilistic fresh noise"). Ternary secret (`defaults.h:133`, `base-pke.cpp:66-67`); `SPARSE_TERNARY` (192 nonzero
  coefficients in {−1, 1}, `base-pke.cpp:69-73`, `ternaryuniformgenerator-impl.h:76-107`) is also
  accepted, since |s| ≤ 1 still holds and the encryption ephemeral is uniform ternary for every
  non-Gaussian secret (`rns-pke.cpp:168-169`); a Gaussian secret is refused.
- **Plaintexts: packed only.** A CoefPacked plaintext is stored centred and, under FLEXIBLEAUTO /
  FLEXIBLEAUTOEXT, multiplied by the scaling factor modulo each q without reduction modulo t
  (`src/pke/lib/encoding/coefpackedencoding.cpp:42-83`), so its norm reaches about (t/2)(t−1),
  far above t − 1; the tracer records each plaintext's encoding and the extractor refuses any
  non-packed plaintext operand or encryption (found by the conformance harness
  `harness/openfhe-pin/`).
- **Build.** `params.json` records `WITH_REDUCED_NOISE`, `NATIVEINT` and `HAVE_INT128`. A build
  `WITH_REDUCED_NOISE` (centred base conversion in hybrid key switching,
  `dcrtpoly-impl.h:943-946`, and halved estimates) , without HAVE_INT128, or with NATIVEINT ≠ 64 is refused: the
  declarations below describe the default build.
- **Plaintext lift: NOT centred.** Packed values are mapped to [0, t)
  (`src/pke/lib/encoding/packedencoding.cpp:79-85`), and the other towers get the same values
  (`:119`, `:128-129`; `mubintvecnat.h:285-290`: the values are below t ≪ q₀/2, so the copy keeps them). The message term is therefore **t − 1**, not t/2.
  - Fresh public-key phase: `inputNoise = (t−1) + t·39·(1+2N)`, with v ternary and e0, e1
    Gaussian (`src/pke/lib/schemerns/rns-pke.cpp:168-173,184-185,190-191`).
  - A plaintext operand is declared with bound t − 1, its true centred norm. ⌊t/2⌋ would be
    wrong, because the lift is not centred. A declared bound restricts the theorem to inputs
    that meet it, and the report says so.
- **Key noise** = t·39: `b = −a·s' + t·e` (`src/pke/lib/keyswitch/keyswitch-hybrid.cpp:104-128`).
- **Modulus switch: centred** t-corrected. δ = [−c·t⁻¹]_q is switched to its centred
  representative before being multiplied by t (`src/core/include/lattice/hal/default/dcrtpoly-impl.h:786-805`).
- **Key switching: canonical** representatives. ModUp sums canonical terms with no correction
  (`dcrtpoly-impl.h:946-967`). ModDown is `(x − t·Conv([t⁻¹x]_P))/P` with a one-sided rounding
  (`:1020-1055`). This is the variant of `FHE.KeySwitch.keySwitchBGVOpenFHE_spec`, so
  `canonical = true`.
- **Digits:** α = ⌈L/dnum⌉ consecutive towers (`rns-cryptoparameters.cpp:89-103`;
  `keyswitch-hybrid.cpp:312-316`).
- **Scaling techniques.** The formulas above hold for all four BGV techniques: the scaling
  factor is applied to the slot values mod t before the inverse NTT and the lift to [0, t)
  (`packedencoding.cpp:66-69,87-90`), so the message term stays t − 1 (see the next section
  for FLEXIBLEAUTOEXT's extra limb).

**HEIR and Lattigo.** Lattigo v6.1.0 is the version HEIR's `go.mod` pins. Source zip from
proxy.golang.org, sha256 `d944f522f3ae6c296d92562418ab354b065d195596a22cf4df2f0f18ae4d6e8e`.
- **Error bound.**
  - `DefaultXe` = discrete Gaussian with σ = 3.2 and Bound = 19.2
    (`core/rlwe/security.go:10-17`).
  - The sampler rejects any v > 19.2 and then rounds, so **|e| ≤ 19 is a hard bound**
    (`ring/sampler_gaussian.go:160-166`).
  - HEIR emits no Xe or Xs, so these defaults apply (`lib/Target/Lattigo/LattigoEmitter.cpp:1992-2010`).
  - Ternary secret of density 2/3 (`security.go:19`).
- **MSB form.** Lattigo keeps `phase = m·t⁻¹ + e` (`schemes/bgv/encoder.go:376-377`). Every
  bound here is for the equivalent LSB view `Φ = t·phase = m + t·e`.
- **Encryption.** Whenever special primes exist, Lattigo encrypts modulo Q·p₀ and divides by p₀,
  whatever HEIR's `encryptionTechnique` says (`core/rlwe/encryptor.go:172-175,205-260`). The
  plaintext lift is [0, t) (`encoder.go:218-222,361`). So:
  `inputNoise = (t−1) + t·⌊(2·19·(2N+1) + (N+1)(p₀−1)) / (2p₀)⌋`.
- **Keys** carry plain e in MSB form (`keygenerator.go:296-310`), which is **keyNoise = 19t** in
  the LSB view.
- **Rescale: centred** (`schemes/bgv/evaluator.go:1436-1443`, `ring/scaling.go:99-107`).
- **Key switching.**
  - Digits are |P| consecutive primes (`core/rlwe/params.go:541-548`).
  - ModUp is exact and centred (`ring/basis_extension.go:401-435,498-525`), and ModDown is an
    exact centred rounding (`:222-256`).
  - Declared `canonical`, the project's conservative default. Lattigo's LSB-view error,
    `t·(N·19·Σ_j Q_j/2 + P(1+N)/2)/P`, is at most the centred bound, which is at most the
    canonical one (`Challenge.Budget.ksBoundAt_le_canonical`). That Lattigo meets the bound is
    argued from the source, not proved: Lattigo's algorithm is not literally the repository's
    reference algorithm.
- **HEIR's own model** uses B_e = 19.2 (`lib/Analysis/NoiseAnalysis/BGV/NoiseByBoundCoeffModel.cpp:84-91`).
  It divides the extended encryption by q_L, not p₀.

## OpenFHE scaling techniques

File:line references are to upstream OpenFHE v1.6.1 (b59e1f29). BGVRNS
defaults to **FLEXIBLEAUTOEXT** and HYBRID key switching
(`src/pke/include/scheme/gen-cryptocontext-params-defaults.h:135-136`). Below,
`bgvrns-leveledshe.cpp` and `rns-leveledshe.cpp` are in `src/pke/lib/scheme/bgvrns/` and
`src/pke/lib/schemerns/`.

**What each technique does to ciphertexts.**

| | FIXEDMANUAL | FIXEDAUTO | FLEXIBLEAUTO | FLEXIBLEAUTOEXT |
|---|---|---|---|---|
| primes | ≡ 1 mod 2N and ≡ 1 mod t (`bgvrns-parametergeneration.cpp:514-542`) | ≡ 1 mod lcm(2N, t) (`:146-170`) | ≡ 1 mod 2N | ≡ 1 mod 2N, plus an extra prime at the top of the chain (`:181,203-220`; per-level noise estimate `:134-140`; 17-20 bits in the runs here: the first prime ≡ 1 mod 2N above a small bound, see "What a default OpenFHE user sees") |
| user `ModReduce`/`LevelReduce` | act | no-ops (`rns-leveledshe.cpp:352-356,371-378`) | no-ops | no-ops |
| before `+`/`−` (`AdjustForAddOrSubInPlace`, `:437-514`) | drop limbs of the higher operand (`:428-435`) | `AdjustLevelsAndDepthInPlace` (`bgvrns-leveledshe.cpp:85-215`) | same | same |
| before `×` (`AdjustForMultInPlace`, `:516-522`) | drop limbs | `AdjustLevelsAndDepthToOneInPlace` (`bgvrns-leveledshe.cpp:217-225`): align, then ModReduce both if degree 2 | same | same |
| `EvalSquare` | square | ModReduce first if degree 2 (`rns-leveledshe.cpp:231-241`) | same | same |
| message scale `scalingFactorInt` | 1 | 1 (`m_fixedSF = 1`, `rns-cryptoparameters.h:1176-1207,1769`) | tracked: ×q⁻¹ per ModReduce (`bgvrns-leveledshe.cpp:70-76`), ×c per constant (`:236-238`) | same |
| fresh encryption | at L limbs, degree 1, scale 1 | same | at L limbs, scale `sf[0]` = q_{L−1} mod t | at **L+1** limbs, degree 2, scale q_ext·q_{L−1} mod t (`cryptocontext.h:185-212`; `bgvrns-cryptoparameters.cpp:105-139`) |

`AdjustLevelsAndDepthInPlace` brings the two operands to the same level and noise-scale degree
with three primitives: `EvalMultCoreInPlace(ct, c)` (multiply every component by an integer
c ∈ [0, t), chosen so that the message scales agree after the next switch: `sf₂·sf₁⁻¹·q mod t`),
`ModReduceInternalInPlace` (t-corrected switch, `:47-77`) and `LevelReduceInternalInPlace` (drop
limbs, `:79-83`). FIXEDAUTO runs the same code with every factor equal to 1.

**How it maps.** Every primitive that changes a ciphertext's polynomials is traced (see "Tracer
patch"), and the extractor translates it wherever it occurs:

| OpenFHE v1.6.1 | Source |
|---|---|
| `LeveledSHEBase::EvalAdd/SubCoreInPlace`, `EvalMultCore` | `add`, `sub`, `mul` |
| `CryptoContext::EvalMultNoRelinNoCheck` (inline in `cryptocontext.h`; the same tensor product, no alignment) | `mul` |
| `LeveledSHERNS::EvalSquare` (untraced core) | `square` of the operand after its sub-calls |
| `LeveledSHEBGVRNS::EvalMultCoreInPlace(ct, NativeInteger c)` | `mulConst c` |
| `LeveledSHEBase::EvalNegate(InPlace)` | `negate` (the message is negated; `scalingFactorInt` is kept) |
| `ModReduceInternalInPlace(ct, k)` | k × `modSwitch` |
| `LevelReduceInternalInPlace(ct, k)` | `dropLimbs k` |
| `EvalAutomorphism(ct, g)` (`EvalRotate`, `EvalAtIndex`) | `automorph g; keySwitch` |
| `EvalMult/EvalSquare` with a relinearization key; `Relinearize` of 3 parts | the product, then `relin` |
| `LeveledSHERNS::Eval{Add,Sub,Mult}InPlace(ct, pt)` | `addPlain`/`subPlain`/`mulPlain` (below) |
| `LeveledSHEBGVRNS::EvalMultInPlace(ct, pt)` | `copy` (it only rewrites `scalingFactorInt`, `:241-249`) |
| `CryptoContext::Encrypt` with a public key | a declared fresh input (2 parts, at its number of towers) |
| `CryptoContext::Encrypt` with a private key | a declared input with its own bound (t−1) + t·39 (see "Key provenance") |

A plaintext operation either uses the plaintext element directly, when the alignment would be a
no-op (v1.6 fast path, `rns-leveledshe.cpp:47-71`: same level, noise-scale degree and tower count,
plaintext in EVALUATION form; for a product also FIXEDMANUAL or both of degree 1;
`Eval{Add,Sub}InPlace(ct, pt)` `:118-127,184-193`, `EvalMultInPlace(ct, pt)` `:263-279`), or
morphs the plaintext into a 1-part ciphertext (`MorphPlaintext`,
`src/pke/lib/schemebase/base-leveledshe.cpp:522-535`, untraced) and passes it through
`AdjustFor*InPlace`, which may multiply it by a constant, drop its limbs or **modulus-switch it**,
before the untraced element-level core. The extractor binds the plaintext (direct) or the 1-part
value (morphed) to a declared plaintext input (1 part, at the plaintext's towers, bound t − 1,
checked to have the plaintext's towers, degree and scale), translates the adjustment ops on it,
and emits the plaintext op on the adjusted operands. All levels, parts and scales are checked
against the trace. (v1.6 also skips the second ModReduce of `EvalMult(x, x)` when both operands
are the same object, `bgvrns-leveledshe.cpp:221-222`; the extractor follows whatever is traced.)
Trace ids are content hashes, so an id can recur (FIXEDAUTO multiplies operands by the constant 1;
a value can be recomputed): every traced output gets a fresh name in the extracted program and a
use refers to the latest value with that content (equal content is the same polynomial, so its
bound applies). Before this, a recurring morphed-plaintext id made the extractor bind the next
plaintext operation to the wrong value (regression
`tests/keyprov/pin/n16_fa_d2_randomcore_max_07`). `EvalMult`/`EvalSquare` with a key on an operand
of more than 2 parts is refused, as is any traced call that recorded no output (it threw).

**A modulus switch of a 1-part value** (certified since `Challenge.Budget.modSwitch_realizable_one`).
In FIXEDAUTO, FLEXIBLEAUTO and FLEXIBLEAUTOEXT, `AdjustLevelsAndDepthToOneInPlace` ModReduces the
morphed plaintext whenever its degree is 2 (`bgvrns-leveledshe.cpp:220-223`): for every
`EvalMult(ct, pt)` on a ciphertext of degree 2, and for every plaintext made at level 0 under
FLEXIBLEAUTOEXT. A 1-part value `[p]` has phase `p`, so its switch `(p + δ)/q`,
δ = t·[−p·t⁻¹]_q centred, adds at most t·⌊q/2⌋/q ≤ ⌈t/2⌉ with no secret-dependent term. The
contract (`Spec.Trace.StepOK`) and the analyzer (`refBound`) charge `E.modSwitchOne` =
`Spec.Budget.msBudgetOne` = ⌈t/2⌉ for it (2^15 at t = 65537) instead of msBudget (2^29).

**Unsupported (reported, not approximated).**
- Refused by the extractor, each with a specific message: BV key switching, a non-ternary secret,
  σ ≥ 300, EXTENDED encryption (BFV only), COMPOSITESCALING*, a noise scale other than t;
  multiparty / threshold calls (`CryptoContext::Multi*`), proxy re-encryption (`ReKeyGen`,
  `ReEncrypt`), key switching between keys (`KeySwitchGen`, `KeySwitch*`), sparse keys, and any key
  whose single-party origin the trace does not show (see "Key provenance");
  `EvalSum`/`EvalSumRows`/`EvalSumCols`/`EvalInnerProduct`/`EvalMerge` (v1.6 computes the rotation sum
  as a fused radix fold, `base-advancedshe.cpp:514-637`: per radix level one digit decomposition,
  up to three rotations key-switched in the extended basis Q·P, accumulated, and ONE ModDown, with
  `PARTIAL_SUM_RADIX = 4`, `CMakeLists.txt:112-113`; it calls no traced primitive, and its
  intermediate values are not ciphertexts of the operations `fhe_check` certifies, so it is not
  translated; write the sum with `EvalRotate`/`EvalAtIndex` and `EvalAdd`); `EvalFastRotation`
  (hoisted rotation); the `EvalMultMutable`/`EvalSquareMutable` ciphertext products (untraced
  cores in v1.6.1); `Compress`; a trace in which a traced call ran on another thread or inside an
  OpenMP parallel region; and any traced function that outputs a ciphertext without a recognised
  primitive.
- A ciphertext that appears as an operand without a traced origin (third-party code multiplying
  ciphertext components directly, deserialization, an untraced core) is an extraction error
  ("is used but no traced operation produced it"; tested by removing operations from real traces).
- Exercised by real traces (42 examples plus 44 fixtures, all value-checked):
  - `add`, `sub`, `mul` (also from `EvalMultNoRelinNoCheck`), `square`, `relin` (also from
    `Relinearize`), `negate`;
  - `mulConst` on 2-part ciphertexts and on morphed plaintexts;
  - 2-part `modSwitch`, and 1-part `modSwitch` (auto modes);
  - `dropLimbs` on 2-part ciphertexts (FIXEDMANUAL `LevelReduce`) and on plaintexts;
  - `addPlain`, `subPlain`, `mulPlain` (morphed and direct), `copy`;
  - `automorph`/`keySwitch` from `EvalRotate` and `EvalAtIndex` (±);
  - private-key `Encrypt`.
- Not exercised: `dropLimbs` of a 2-part ciphertext under an automatic mode (that needs two
  ciphertexts at different levels and depths); `EvalMultKeysGen` keys for s³ and above.

**Fresh-encryption noise per technique.** All four use `PKERNS::Encrypt` with a public key
(`rns-pke.cpp:61-75,152-199`), so `inputNoise = (t−1) + t·39·(1+2N)` for each. Packed values are
scaled mod t and lifted to [0, t) (`packedencoding.cpp:66-69,79-90,119`). For FLEXIBLEAUTOEXT the
input is declared at all L+1 towers. The reduction that drops the extra prime is the first
`ModReduceInternalInPlace` OpenFHE applies, inside the first multiplication's
`AdjustLevelsAndDepthToOneInPlace` or the first `AdjustLevelsAndDepthInPlace` that needs it. The
extractor emits it as a `modSwitch`, and the verified analyzer bounds the result as
⌊inputNoise/q_ext⌋ + msBudget. No post-reduction bound is computed by hand. The extra prime is
small: 17-30 bits by default, so this step is dominated by msBudget = 2^29.

## Tracer patch (`openfhe/openfhe-v1.6.1-tracer.patch`, `openfhe/fhecheck-tracer.h`)

Upstream OpenFHE has no tracer. Public-API tracing is not enough: under the automatic scaling
techniques OpenFHE multiplies operands by constants c ∈ [0, t) and ModReduces/LevelReduces them
inside `EvalAdd`/`EvalMult`/`EvalSquare` and the plaintext operations, and only the resulting
metadata is visible from outside. So the patch adds observation hooks inside the library. It is a
port of the hooks of the tracing fork
AlexanderViand/openfhe-development 7e2eafc to v1.6.1, plus this directory's additions. Applies
cleanly to b59e1f29; 20 files, +2556/−177 lines, including `src/pke/include/utils/fhecheck-tracer.h`
as a new file whose content is exactly `openfhe/fhecheck-tracer.h` (the editable copy; after
editing it, regenerate the patch with `git diff` in the patched checkout, new files added with
`git add -N`). `build_openfhe.sh` applies the patch and refuses a tree whose header differs from
`openfhe/fhecheck-tracer.h` (`tests/run.sh` section 9 checks that the patch carries it).
Provenance: upstream tag v1.6.1, commit b59e1f291965f14fbee5172cd83a20f5b856204f (released
2026-10-09); `git apply --check` passes on a pristine checkout. sha256 of the patch:
a1792781bd823a7a57eaaae2b924343b4808b9121140db211ab9d5d5aa79a461 (also recorded in
`harness/openfhe-pin/fixtures/SOURCE.txt`). Its deletions are `return x;`
lines rewritten as `return REGISTER_IF_TRACE(x);`, two constructor signatures that gain an
`IF_TRACE(...)` tracer parameter, and whitespace. The hooks of the fork were merged with a 3-way
cherry-pick; the conflicting hunks (upstream reformatted, renamed `params` to `m_params`, took
arguments by reference and added fast paths) were resolved by keeping upstream's code and
re-inserting the fork's statements. Every traced function name of the fork exists in the port and
registers its outputs, except 7 key-generation wrappers whose signatures changed upstream; none of
those produces or changes a ciphertext. With `ENABLE_TRACER=OFF` the patched tree builds and adds
no code path except the `CoefPackedEncoding` default constructor and plaintext save/load templates,
which are unused unless plaintexts are serialized.

Tracer version. Every `params.json` the tracer writes (`paramsJson`, both schemes) records
`"tracer": FHECHECK_TRACER_VERSION`, the SHA-256 of `fhecheck-tracer.h` with that value zeroed
(`openfhe/tracer_version.py`; after editing the header run `tracer_version.py --update-header`, then
regenerate the patch). `extract.py` and `extract_bfv.py` refuse, before anything else, a trace whose
recorded version is not the one of the header next to them ("trace written by a different fhecheck
tracer ...: rebuild OpenFHE with harness/frontend/openfhe/build_openfhe.sh"): a stale install. A
`params.json` without the field (every trace committed before it existed) is accepted only if the
SHA-256 pair of its `params.json` and trace is listed in `openfhe/legacy-traces.tsv`
(`tracer_version.py --allowlist`, from the committed traces and fixture archives; `tests/run.sh`
section 6d checks it and the refusals). Tests that mutate a committed trace stamp its `params.json`
with the current version (`extract.stamp_tracer`, `tracer_version.py --stamp`). `build.sh`,
`build_bfv.sh` and the other scripts that compile against the install run `openfhe/check_install.sh`,
which stops with the same instruction when the installed header is not this one.

What it changes, exactly (`openfhe/patch_residue.py b59e1f29 HEAD` in the patched checkout prints
every difference that remains after deleting the hook macros, comments and whitespace):
- `IF_TRACE(...)` statements and `REGISTER_IF_TRACE(x)` wrappers (863 lines mention them): a
  `FunctionTracer` per traced call that records its inputs and outputs. With `ENABLE_TRACER=OFF`
  they expand to nothing / to `x`. A hook only reads its arguments; the tracer's `registerOutput`
  returns its argument unchanged. `cryptocontext.cpp`, `base-leveledshe.cpp`, `rns-leveledshe.cpp`,
  `ckksrns-leveledshe.cpp` are IDENTICAL to v1.6.1 once the macros are removed.
- The `ENABLE_TRACER` CMake option (`CMakeLists.txt`, `configure/config_core.in`,
  `OpenFHEConfig.cmake.in`), the fork's `utils/tracing.h` and `utils/simpletracer.h` (new files),
  and `#include`s of them.
- Plaintext serialization (cereal `save`/`load` in `plaintext.h` and the encodings, new
  `plaintext-ser.h`) and default constructors of `CoefPackedEncoding` and `StringEncoding` (cereal
  registration needs them); unused unless plaintexts are serialized.
- `CryptoContextFactory::AddContext` calls `fhecheck::MaybeAutoTrace` (inside `IF_TRACE`): with
  `FHECHECK_TRACE_DIR` set, every BGVRNS and every BFVRNS context gets a tracer (for unmodified
  programs), and its `params.json` (`fhecheck::paramsJson`: `bgv_demo dump` resp. `bfv_demo dump`;
  for BFV it includes the auxiliary bases of the multiplication and the library's own
  `FindLevelsToDrop` evaluated on the context, see "BFV extraction").
- Three rewrites with identical behaviour: `if (levels > 0) f();` → `if (levels == 0) return; f();`
  in `CryptoContext::LevelReduceInPlace`, and `return f();` → `auto result = f(); return result;`
  in `EvalAddManyInPlace` and the BFV `EvalKeySwitchPrecomputeCore` (so the result can be
  registered).

**Automated observation-only check** (`openfhe/check_patch_observation.sh`, a few minutes on 128
cores with JOBS=32; result committed as `openfhe/patch-observation.json`). Two parts, both must pass:
- Static (`check_patch_observation.py`): every one of the patch's 270 hunks is classified on a
  pristine b59e1f29 checkout and the patched copy. A hunk of a modified source file is a hook if its
  two sides are equal once the hook macros are deleted as ENABLE_TRACER=OFF expands them (and
  comments, whitespace, tracer `#include`s); every other hunk must be listed, with the reason it
  changes no computed value, in `openfhe/patch-residue-allowlist.json` (keyed by the SHA-256 of its
  two sides: the 11 hunks of the list above). Every `IF_TRACE` statement must be a tracer variable
  (`StartFunctionTrace`), a single `registerInput`/`registerOutput` call on it, or a loop of such
  calls, else be allowlisted (the tracer member of `CryptoContextImpl`, `MaybeAutoTrace`); every
  `registerOutput` definition in the three tracer headers returns its parameter unchanged, its only
  return. Result: 270 hunks = 249 hook + 2 tracer include + 11 allowlisted residue + 4 new-file + 4
  build-configuration hunks, 0 unexplained; 39 `registerOutput` definitions, 0 violations.
- Behavioural (`patch_obs_driver.cpp`): pristine v1.6.1 and the patched tree with ENABLE_TRACER=ON
  are built with the same flags, and one deterministic program (OpenFHE's external-PRNG hook with
  `harness/openfhe-pin/cpp/pin_prng.cpp`, fixed seeds, one thread) runs against each: 20 contexts
  (BGV with the four scaling techniques and BFV with the four multiplication techniques, each with
  BV and HYBRID at N = 4096; BGV FLEXIBLEAUTOEXT and BFV HPSPOVERQLEVELED at OpenFHE's own ring
  dimension; CKKS FIXEDMANUAL and FLEXIBLEAUTO), key generation, both encryptions, the traced
  evaluation calls (add/sub with ciphertexts and plaintexts, negate, mult, mult without relin then
  relinearize, square, rotate, EvalAtIndex, EvalSum, inner product, add/mult many, in-place add,
  BGV ModReduce/LevelReduce, Compress, key switch, CKKS constants/rescale) and decryption. The
  digests of 470 ciphertexts (every coefficient of every tower, format, level, noiseScaleDeg), 430
  decryptions, 4 library exceptions and the PRNG draw count after every step are identical, line
  for line, on pristine, patched without a tracer, patched with every context traced (the fhecheck
  JsonTracer for BGV/BFV, OpenFHE's SimpleTracer for CKKS), and the frontend's own install
  (`harness/build/frontend-openfhe/install`) traced.
What this does not establish: values on programs or parameters not run (the static part covers
every hunk only under ENABLE_TRACER=OFF semantics plus the syntactic `registerOutput` property; that
a tracer's reading of its arguments changes nothing when ON rests on the behavioural runs).

Added here on top of the evaluation's port:
- **Content identity** (the extractor's dataflow rests on it). An id (`ct_7`, `pt_2`, `ek_3`, ...)
  names the k-th distinct SHA-256 digest (FIPS 180-4; a self-contained implementation in the
  header) of the object's content: every coefficient of every tower and the metadata the library
  computes with (ciphertext: format, moduli, level, noiseScaleDeg, scalingFactorInt, slots,
  encoding type, key tag; plaintext: its DCRTPoly element, level, noiseScaleDeg, scalingFactorInt,
  encoding type and plaintext modulus; keys: their elements and key tag). It is RECOMPUTED at every
  traced use, for every kind of object (evaluation keys included: there is no per-object cache), so
  a change made through the public API outside the traced calls (`GetElements()`/`SetElements()`,
  `SetLevel`, `SetNoiseScaleDeg`, `EvalAddInPlaceNoCheck`, `EvalMultNoCheck`, a plaintext's
  `GetElement<DCRTPoly>()`, a key's `SetAVector`/`SetBVector`, ... and any mutator not listed here)
  gives the object an id no traced operation produced, at its next traced use, including
  `Decrypt`; the extractor refuses it. The digest never appears in the trace (only the counter
  id), so the trace format does not depend on the hash: re-recording the examples with this tracer
  reproduces the committed traces byte for byte up to OpenFHE's random key tags and the plaintext
  field `t` below.
- **Plaintext modulus**: every plaintext record carries `"t"` (its encoding parameters' plaintext
  modulus); the extractors require it to be the context's (traces recorded before have no `t`;
  the plaintext must then still be an output of a traced `Make*Plaintext` of the same trace, i.e.
  of the same context).
- **Parameter watch**: a tracer set by `MaybeAutoTrace` (or `JsonTracer::watch(cc)`, as the demo
  drivers do) records the context's parameters (`paramsJson` without the `FindLevelsToDrop` tables)
  and compares them at the start of every top-level traced call; a parameter setter called on the
  context after `params.json` was written (e.g. `GetEncodingParams()->SetPlaintextModulus`,
  `CryptoParametersBase::SetPlaintextModulus`) writes an `{"ev":"error"}` record and the extraction
  is refused.
- **`Decrypt`** is traced (`CryptoContext::Decrypt`, both argument orders): the ciphertext's id at
  decryption time and the private key. The extractors use it: see the options above and "What the
  frontend assumes".
- **Key records** (for "Key provenance"): the tracer records public, secret and evaluation keys
  (id = content hash, OpenFHE's keyTag, and for rotation keys the automorphism index). `KeyGen`
  records its key pair; `EvalMultKeyGen`/`EvalMultKeysGen` record only a key they generate (not one
  already in OpenFHE's static map); `EvalAtIndexKeyGen`, `EvalAutomorphismKeyGen`, `EvalSumKeyGen`,
  `EvalSumRowsKeyGen`, `EvalSumColsKeyGen` record the secret key and the keys they generate (not the
  returned map, which can hold older keys); `LeveledSHEBase::EvalMult/EvalSquare(…, EvalKey)`,
  `Relinearize(InPlace)` and `EvalAutomorphism` record the key they actually use. This re-creates
  the 7 key-generation hooks the evaluation's port had left out (their v1.6.1 signatures changed),
  because key provenance needs them.
- **`EvalMultNoRelinNoCheck`** (new in v1.6, inline in `cryptocontext.h`): hooked; mapped to `mul`
  for BGV, refused for BFV (it is the componentwise product, without the BFV scaling by t/Q).
- **BFV internal drops**: `LeveledSHEBFVRNS::EvalMult`, `EvalSquare` (HPSPOVERQLEVELED branch) and
  `RelinearizeCore` record, as the int input `levelsDropped`, the number of limbs
  `FindLevelsToDrop` told them to drop (three `IF_TRACE` lines; the value is read after the library
  computed it). `extract_bfv.py` requires it to equal the dumped table.
- **Threads.** The tracer records the thread that created it. A traced call from another thread
  or from an active OpenMP parallel region is not traced; an `{"ev":"error"}` record is written
  and the extractor refuses the trace. All writes take a mutex, so concurrent calls cannot
  corrupt the file or crash (the evaluation saw a SIGSEGV with 8 threads in FHERMA max-element).
  Drivers here run with `OMP_NUM_THREADS=1`; OpenFHE's internal parallel loops (over towers, over
  key-generation indices) call no traced function.
- Fail-safe: an operation whose hook is missing or which the extractor does not understand makes
  its traced wrapper output an unknown ciphertext, and the extraction fails ("outputs … via an
  operation the extractor does not understand"); deleting all events of any one hooked primitive
  from a real trace makes the extractor refuse it .
  The net is the traced wrappers: an untraced computation whose result never passes through a
  traced call and is never used again is not seen (nor is it part of the program certified).

## What the frontend assumes

A CERTIFIED verdict on an OpenFHE program is a theorem about the program `fhe_check` read, under
the declared assumptions it prints. Between the user's program and that file sit the tracer patch
and the extractors, which are not proved. What they rely on, beyond what the report prints:

1. **The program uses OpenFHE through its API, without memory corruption or undefined
   behaviour.** The tracer observes calls; a program that writes into OpenFHE's objects through
   dangling pointers, races or out-of-bounds writes, or calls the library from another thread
   while a traced call runs, can change values between observations in ways no hook sees (calls
   from other threads and OpenMP regions are detected and refused, see "Threads").
2. **Every value change between two traced uses is visible as a content change.** Ciphertexts,
   plaintexts and keys are identified by the SHA-256 of their content, recomputed at every traced
   use (Tracer patch, "Content identity"); the extractors refuse a value whose identity no traced
   operation produced, at every use including `Decrypt`. What is assumed is that SHA-256 has no
   collision the program could hit (by accident or design) and that the hashed fields are all that
   the library's arithmetic reads (ciphertext: elements, moduli, format, level, noiseScaleDeg,
   scalingFactorInt, slots, encoding type, key tag). Metadata outside that list (the CKKS metadata
   map, the PRE hop level) is not hashed; BGV/BFV evaluation does not read it.
3. **What is certified is what the program decrypts, if it decrypts under the trace.** Every
   ciphertext passed to a traced `Decrypt` is an output and must be a value of the extracted
   program. If the trace contains no `Decrypt` (the demo drivers switch the tracer off before
   decrypting; a program that decrypts in another process or after replacing the tracer), the
   outputs are the never-consumed values, and nothing ties them to what is decrypted later:
   `crossCheck.outputs` says so.
4. **One trace is one context.** The extractors read one trace (one `CryptoContext`). Plaintexts
   must be made by a traced `Make*Plaintext` of that trace (so of that context; their `t` must be the
   context's). A program with several contexts is certified per context; ciphertexts moved between
   contexts (serialization) arrive as values no traced operation produced and are refused.
5. **The parameters are the dumped ones.** `params.json` is written when the context is
   registered; later setter calls are detected at the next top-level traced call (Tracer patch,
   "Parameter watch") and refused. A change made and undone between two traced calls is not seen,
   and neither is one that only affects calls that are not traced.
6. **The internal limb drops of HPSPOVERQLEVELED are the library's.** The three observations the
   BFV extractor compares (the library's `FindLevelsToDrop` evaluated on the context by the tracer,
   the Python replica written from the same source, and the value the hooked call recorded at run
   time) are observations of ONE implementation, not independent evidence; `fhe_check` cannot
   detect an understated drop from the file (`FHE/Check/BFVDecode.lean`). The drops are an input
   assumption, as the parameters are.
7. **The noise constants are OpenFHE v1.6.1's.** The sampler bounds (σ = 3.19 only, both schemes:
   the declared sampler mean is for 3.19f), the key and encryption formulas, the build
   flags in `params.json` (`build`) and the mapping of each traced function to an operation are
   read from the v1.6.1 source (file:line in the extractors); the cross-checks (levels, parts,
   scale factors; `value_check*.py` against the library's own decryption on recorded runs) test
   the mapping, they do not prove it.
8. **Assumptions the user adds** are written into the file: `--assume-fresh-inputs` (inputs only,
   see the option), `--assume-single-party-keys`, `--assume-default-build`, `--outputs`, and
   `--idealised` (BFV: the verdict is labelled IDEALISED, it is not the library's algorithm).

Negative tests for 2-5: `tests/tamper/` (real OpenFHE runs of `openfhe/tamper_demo.cpp` that change
a ciphertext, plaintext, key or parameter through the public API outside the traced calls; every
one must be refused) and the trace mutations of `tests/run.sh` section 6c.

## Key provenance

The noise constants the OpenFHE extractor declares (`secretBound = 1`, `keyNoise = t·39`) are
those of a SINGLE-PARTY key. They are wrong for a threshold/multiparty key (the joint secret is
the sum of the parties' ternary secrets, so it is bounded by the number of parties, and the joint
key error is the sum of their errors), for proxy re-encryption and for key switching to another
key. The evaluation found that the extractor did not check this: OpenFHE's
`openfhe-network-examples` 3-party threshold program, traced and cut before its first multiparty
decryption, was extracted under single-party assumptions and CERTIFIED. Now the extractor requires,
from the trace:
- every `Encrypt` uses a public key that a traced single-party `CryptoContext::KeyGen()` output
  (or a private key it output);
- every relinearization key used was output by a traced `EvalMultKeyGen`/`EvalMultKeysGen` of that
  KeyGen's secret key (for the power of s it is used for), and every rotation key used by
  `EvalAutomorphism` for index g was generated for g from that secret;
- the program uses one secret key;
- no multiparty, proxy re-encryption, key-switching or sparse-key call occurs anywhere in the trace.
Otherwise it refuses, naming the call or the key. `--assume-single-party-keys` (for traces
without the key generation, e.g. keys deserialized in another process) replaces the check by an
assumption written into the file. Regression tests: `tests/keyprov/` (the threshold witness,
traced on v1.6.1 from openfhe-network-examples @1cee5bfe built unmodified, both as cut by the
evaluation and with its multiparty calls hidden; and mutations of a real trace: no KeyGen, no
EvalMultKeyGen, a rotation key used for another index, a second secret, a tracer error event, an
operand with no traced origin).

**Private-key (symmetric) encryption.** `CryptoContext::Encrypt(pt, privateKey)`
(`cryptocontext.h:1419-1436`) computes `c = (a·s + t·e + m, −a)` (`rns-pke.cpp:45-59,115-150`;
the noise scale is t, `gen-cryptocontext-bgvrns-internal.h:97`), whose phase is m + t·e with
|e| ≤ 39 and m in [0, t). It is not a public-key encryption, so it is not declared fresh: the
extractor declares it as a 2-part input WITH its own bound (t−1) + t·39 (an assumption derived from
that source, printed in the file), the worst-case analysis starts it there, and `--kappa` answers
UNSUPPORTED for such a program (the probabilistic theorem covers fresh public-key encryptions
only; `Spec.Encrypt.freshOK?`). Example: `openfhe_<technique>_symenc`.

## Decryption

`PKEBGVRNS::Decrypt` (`src/pke/lib/scheme/bgvrns/bgvrns-pke.cpp:48-102`) does not decrypt at the
ciphertext's level.
- **EVALUATION form** (what `Encrypt` and every homomorphic operation produce): it computes the
  phase b = c₀ + c₁s (+ c₂s²) modulo Q_ℓ, then ModReduces that one polynomial down to **one
  tower** (`:56-75`; `DCRTPoly::ModReduce`, `dcrtpoly-impl.h:786-805`: δ = [−b·t⁻¹]_q switched to
  its centred representative, then (b + t·δ)/q), then reads b mod q₀, centred, mod t
  (`DecryptionCRTInterpolate` → `NativeVector::Mod`, `mubintvecnat.cpp:260-288`).
- **COEFFICIENT form**: it ModReduces each ciphertext component instead (`:75-96`). Not covered.

`Spec/Decrypt.lean` defines exactly the first procedure (`bgvDecryptSwitched`), and
`Challenge.Decrypt.decrypt_switched` (proved; used by the one-program statements
`Challenge.FreshNoise.certified_decrypts` / `Challenge.FreshNoise.fresh_kappa_decrypts` /
`Challenge.FreshNoise.fresh_worst_decrypts`, which add that the output is under s itself, and
through them by the certificate statements about `Challenge.Certify.certify?`) says: if an output's
phase is at most B at its level ℓ and `decBound` — B mapped through ⌊(B + t·⌊q/2⌋)/q⌋ for each
dropped limb, about B/(q₁⋯q_{ℓ−1}) + t/2 — is below q₀/2, then the switched decryption returns
the message times (q₁⋯q_{ℓ−1})⁻¹ mod t (the factor OpenFHE keeps in `scalingFactorInt`). Only
the final bound matters; the intermediate levels may wrap. There is no secret-dependent term.

The extractor no longer appends `modSwitch` operations. It writes
`"decryption": {"method": "switch-to-one-limb"}` (or `at-output-level` with
`--no-decrypt-switch`), and `fhe_check` evaluates `Spec.Encrypt.certOK?` (the output is under
the secret key itself, and `Spec.Decrypt.decryptAllOK?`) on each output with its proved bound. The certificate text states which decryption is covered. A 3-part output
(no relinearization) is supported: the phase is one polynomial whatever the number of parts.

## Cross-checks against OpenFHE

1. **Levels and scales** (`extract.py`, all techniques): replaying the extracted program must
   reproduce OpenFHE's tower count and `scalingFactorInt` for every traced ciphertext, and give
   equal scales on both sides of every addition. For FIXED* that means every scale stays 1, which
   catches a prime ≢ 1 mod t. Any mismatch is an extraction error. The `expect` fields carry the
   levels and parts to `fhe_check`, which compares them with `Source.step`.
2. **Plaintext values** (`openfhe/value_check.py`, **untrusted**): an independent message-level
   evaluator mirroring `Source.step` over Z_t[X]/(X^N+1). Negacyclic products are exact by
   Kronecker substitution; automorph is X ↦ X^g; modSwitch multiplies by q_last⁻¹ mod t. It runs
   the extracted program on the encoded plaintexts OpenFHE actually encrypted (from `values.json`).
   It requires the prediction for each output, after the decryption switch, to equal OpenFHE's
   raw decryption (`PKEBGVRNS::Decrypt` before `Decode`) in **all N coefficients**. It also
   requires the replayed scale to equal Decrypt's `scalingFactorInt`. A mutated constant,
   rotation index, operation or missing modSwitch is caught: the tests mutate one program four
   ways. With `switch-to-one-limb` the prediction is multiplied by `decScale` = (q₁⋯q_{ℓ−1})⁻¹,
   so this also checks `Spec.Decrypt`'s factor against OpenFHE's `Decrypt` on every run.

Results (OpenFHE v1.6.1 with the tracer):
- 0 mismatches on the 42 OpenFHE examples (default ring dimensions) and on the 44 committed
  N = 1024 fixtures (`tests/values/`: 11 programs × 4 techniques, including `negate`, `subpt`,
  `symenc`, `nocheck`); the 32 runs of the default-user table were value-checked too.
- The scale replay found a frontend bug on upstream programs: `EvalNegate` was
  replayed as a multiplication of `scalingFactorInt` by −1, which OpenFHE does not do (it negates
  the message and keeps the factor), so every program using `EvalNegate` failed the cross-check.
  Fixed: `EvalNegate` maps to `negate`, whose replay keeps the factor; `openfhe_*_negate` and
  `tests/values/n1024_*_negate` exercise it.

## Probabilistic fresh noise (`--kappa K`)

Only the fresh-error component of the worst case is proved attained: the worst-case fresh error
39·(1 + 2N) is reached inside the sampler supports (`Challenge.FreshNoise.freshError_worst_attained`).
That the composed bound of a whole program is attained is not proved in Lean, and nothing here claims it.
What is improbable is that a *fresh encryption* comes out that bad. `--kappa K` bounds only that.

- `Spec/Encrypt.lean` (trusted, computable): public key (b, a) with b + a·s = t·e_pk; encryption
  (b·u + t·e₁ + p, a·u + t·e₂), p the STORED plaintext polynomial, ‖p‖∞ ≤ B_p declared
  (`freshEncryption.plaintextBound`; a packed encoding stores a representative in [0, t), so
  B_p = t − 1). Its phase is p + t·(e_pk·u + e₁ + e₂·s) (`phase_encrypt`), and
  `Spec.Encrypt.freshNoise t B_p ε` = B_p + t·ε.
- `Challenge.FreshNoise.freshError_tail` (proved, Hoeffding): for a fixed key, if the 3N
  coefficients of (u, e₁, e₂) are independent, within their bounds, and each of mean at most
  mn/md in absolute value (`SamplerOK`, on any probability space), then
  P[‖e_pk·u + e₁ + e₂·s‖∞ ≥ ε] ≤ 2N·exp(−(ε−d)²/(2V)) for ε ≥ d, with
  V = N(B_k·B_u)² + B₁² + N(B₂·B_s)² (OpenFHE: 39²·(2N+1)) and the drift
  d = `Spec.Encrypt.meanDrift` of the mean bound and N·B_k + 1 + N·B_s (0 for mean zero).
- `Spec.Encrypt.epsFor V (n·2N) K` (computed; `epsFor_spec` proved): an ε₀ with
  n·2N·exp(−ε₀²/(2V)) ≤ 2^-K, namely ⌊√(2V·(K + ⌈log₂(n·2N)⌉)·0.6931471808)⌋ + 1. The tool
  uses ε = ε₀ + d.
- `fresh_certified_kappa` (proved): with that ε, the probability that there *exist* messages for
  which some output of some run is wrong is at most 2^-K, whenever `refAnalyze` accepts at input
  noise B_p + t·ε and `Spec.Encrypt.freshOK?` holds: there is at least one fresh input; every
  fresh input is a declared 2-part ciphertext under s that declares **no bound of its own**; every
  other input is a 1-part plaintext operand with a declared bound. (A fresh input with a declared
  bound used to pass: the analysis then started it at that bound, the theorem assumed the
  encryption met it, and the certificate was vacuous. `freshOK?_spec` and guards in
  `Challenge/FreshNoise.lean` pin the rejection.)
- `fresh_kappa_decrypts` (proved): the same with decryption in the statement, as ONE theorem: the
  probability that there exist messages for which some output of some run is not under s, or
  does not decrypt with s (textbook, and by the switched decryption when the file declares it),
  is at most 2^-K, given also `Spec.Encrypt.certOK?`. This is the statement the tool cites; it
  does not compose theorems itself.
- `fresh_worst_decrypts` (proved): the same conclusion with no probability, at
  ε = `worstError`, for all randomness within the bounds.

`fhe_check --kappa K` computes ε, runs the reference analyzer at the reduced input noise and
prints the certificate "CERTIFIED (fresh-noise failure probability at most 2^-K; evaluation
worst-case) …". The frontend supplies `freshEncryption`: which inputs are fresh encryptions; the
bounds (OpenFHE: 39 for e_pk, e₁, e₂ and 1 for u); and two optional declarations, both
ASSUMPTIONS that the report prints with their origin:
- `plaintextBound` = B_p. Absent: the tool takes t − 1 and prints "ASSUMED, not declared by the
  input". The OpenFHE extractor declares t − 1 (it maps packed plaintexts only).
- `mean` = `{"num": mn, "den": md}`, a bound on the absolute mean of every coefficient of
  (u, e₁, e₂); `den` = 0 is INVALID INPUT. Absent: mean zero is taken and printed as ASSUMED.
  The OpenFHE extractor declares 3431/2^64 for the discrete Gaussian generator at σ = 3.19f (and
  mean 0 for the ternary generator). This is the tool's declared assumption: `fhe_check` does not
  examine any sampler. For any other σ the extractor
  refuses ("the declared sampler mean applies to sigma = 3.19 only"). With this bound the drift is
  d = 1 on every committed OpenFHE example, so ε is one larger and the input noise t
  larger than under a mean-zero assumption.

No sampler was examined by `fhe_check`.
HEIR/Lattigo files have no such section (Lattigo encrypts modulo Q·p₀ and divides), so `--kappa`
answers UNSUPPORTED on them, as it does when `freshEncryption.inputs` is empty. If the requested
K is so large that ε is not below the worst case of the fresh error (`Spec.Encrypt.worstError`,
computed by the tool from the sampler bounds), the tool uses that worst case, cites
`fresh_worst_decrypts` and a warning says so. In `--kappa` mode the frontend's `inputNoise` is
never used. In worst-case mode it is the stated assumption; if it is below
B_p + t·`worstError` for the sampler bounds the file itself declares, the report says so in a
`WARNING` under the verdict.

At OpenFHE's depth-2 defaults (N = 2^14, three fresh inputs): ε = 100095 = 2^16.61 at K = 128
(`epsFor` 100094 plus the drift 1) against the worst case 1277991 = 2^20.29; input noise
65536 + 65537·100095 = 6559991551 = 2^32.61 instead of the frontend's 2^36.29.

The pins above are about one program and one bound; the tool cites the `Challenge.Certify`
statements built on them (`fresh_kappa_certified`, `fresh_worst_certified`), whose hypothesis is
only that the locked `certify?` returned a certificate.

**The ℓ₂ description (`--kappa K --l2`, `Challenge.FreshNoiseL2`, `Challenge.Certify.fresh_l2_certified`).**
The support model charges every term of the fresh error at its support bound (39² per term for
OpenFHE). With `--l2` the key enters through ‖e_pk‖₂² ≤ E2 and ‖s‖₂² ≤ S2, and the samplers
through sub-Gaussian variance proxies Vu, V1, V2; V = Vu·E2 + V1 + V2·S2
(`Spec.Encrypt.varProxyL2`), ε = `epsFor V (n·2N) K` + `meanDrift` (of the mean bound and
E2 + 1 + S2), no fallback to the worst case. The five
numbers are read from `freshEncryption.l2` = `{keyErrorSq, secretSq, uProxy, e1Proxy, e2Proxy,
source}`; every field given there is an ASSUMPTION, printed as such in the certificate. A missing
field is computed by the tool from the support bounds, which needs no assumption:
E2 = N·Bk², S2 = N·Bs² (`normSq_le`; for a ternary secret ‖s‖₂² ≤ N always), proxies Bu², B1², B2²
(Hoeffding's lemma, `subGaussSamplerOK_of_samplerOK`); with nothing supplied the result is the
support model's ε (`varProxyL2_support`). Not proved here, and assumed by a file that supplies a
proxy below the squared support bound: that the truncated discrete Gaussian of σ has proxy σ²
(σ = 3.19: σ² ≈ 10.18, use 11), and ternary 2/3 (use 1). A supplied E2 is a statement about
the one key (computed from it, or a high-probability bound whose failure probability is not
included). A malformed field is INVALID INPUT; `--l2` without `--kappa` is a usage error.

## What a default OpenFHE user sees

The program is `chain`: `EvalMult(a, b)` then `EvalSquare` up to the multiplicative depth D.
Parameters are OpenFHE's own (`GenCryptoContext`), with t = 65537, HYBRID key switching, and
only the scaling technique and D set. OpenFHE's `Decrypt` is covered (`switch-to-one-limb`).
"✓ m" is CERTIFIED with the smallest margin m in bits (level or decryption); "over x" is the
overflow in bits at the first failing instruction. Regenerate with `openfhe/default_table.sh`.
The κ rows are with the extractor's declared sampler mean (drift 1); against a mean-zero
assumption that moved nine of the 96 κ figures by +0.01 and no verdict.

| D | mode | FIXEDMANUAL | FIXEDAUTO | FLEXIBLEAUTO | FLEXIBLEAUTOEXT (default) |
|---|---|---|---|---|---|
| 1 | worst case | **✓ 5.43** (N=2^13, 2×45) | over 8.76 (34+42) | over 9.57 | over 4.00 (30+36+ext 17) |
|   | κ = 128 / 64 / 40 | ✓ 11.71 / 12.50 / 12.96 | over 2.40 / 1.55 / 1.04 | over 3.21 / 2.36 / 1.85 | over 4.00 (all) |
| 2 | worst case | over 8.15 (N=2^14, 3×45) | over 25.32 | over 26.14 | over 17.05 |
|   | κ = 128 / 64 / 40 | **✓ 6.47 / 8.08 / 9.03** | over 10.64 / 8.97 / 7.97 | over 11.46 / 9.80 / 8.80 | over 17.04 (all) |
| 3 | worst case | over 29.30 | over 54.41 | over 55.28 | over 41.10 |
|   | κ = 128 / 64 / 40 | over 0.07 / **✓ 3.16 / ✓ 5.05** | over 25.05 / 21.72 / 19.73 | over 25.93 / 22.60 / 20.60 | over 41.09 (all) |
| 4 | worst case | over 71.62 | over 11.34 | over 12.28 | over 4.10 |
|   | κ = 128 / 64 / 40 | over 13.15 / 6.69 / 2.91 | over 53.79 / 47.13 / 43.13 | over 54.85 / 48.20 / 44.20 | over 4.09 (all) |
| 5 | worst case | over 26.64 | over 69.39 | over 70.57 | over 52.20 |
|   | κ = 128 / 64 / 40 | over 39.33 / 26.43 / 18.85 | over 10.67 / 4.02 / 0.02 | over 11.85 / 5.20 / 1.20 | over 52.18 (all) |
| 6 | worst case | over 12.73 (N=2^15) | over 37.67 | over 40.57 | over 15.20 |
|   | κ = 128 / 64 / 40 | over 41.33 / 28.25 / 20.48 | over 80.61 / 67.41 / 59.54 | over 83.86 / 70.67 / 62.79 | over 15.18 (all) |
| 7 | worst case | over 129.64 | over 169.69 | over 173.13 | over 111.40 |
|   | κ = 128 / 64 / 40 | over 142.02 / 115.86 / 100.32 | over 36.43 / 23.23 / 15.36 | over 39.86 / 26.67 / 18.79 | over 111.36 (all) |
| 8 | worst case | over 84.77 | over 125.48 | over 129.13 | over 103.19 |
|   | κ = 128 / 64 / 40 | over 97.28 / 71.12 / 55.58 | over 166.99 / 140.60 / 124.84 | over 171.73 / 145.34 / 129.58 | over 103.18 (all) |

Reading it:
- The worst-case column is unchanged by the 1-part budget and the exact decryption model: every
  failure is at a `mul`/`square` in mid-chain.
- An "over" figure is the overflow at the *first* failing instruction. With `--kappa` the first
  failure often moves to a later, larger product, so the figure can be larger than in the
  worst-case row; it is not a distance to certification (the "smallest fix" below is).
- **The feasibility study's prediction is confirmed**: depth-2 FIXEDMANUAL defaults are CERTIFIED
  at κ = 128 with **6.47 bits** (predicted ≈ 6.5). Depth 3 certifies at κ = 64 and 40 and misses
  κ = 128 by 0.07 bits (largest certifying K: 126).
- The automatic modes are **not** rescued by probabilistic fresh noise. Their failures are
  dominated by the worst-case evaluation terms (msBudget = 2^29 after every ModReduce against
  37-44-bit primes; under FLEXIBLEAUTOEXT the fresh noise is switched away by the first
  reduction, so κ changes nothing). At OpenFHE's default parameters they are not certified in
  either mode; raising `SetEvalAddCount` (which makes OpenFHE choose larger primes) certifies them
  in the worst case at every depth 1-8 (see "Getting parameters that are certified").

**With the ℓ2 fresh-noise mode (`--kappa K --l2`).** With every ℓ2 value computed by the tool from
the support bounds the table is unchanged (it reproduces the support model's ε exactly). With
SUPPLIED values (ASSUMPTIONS the certificate prints, not proved here, and not emitted by the
extractor): E2 = ‖e_pk‖₂² ≤ 11·N, sub-Gaussian proxies 11 for the Gaussian errors (σ² ≈ 10.18) and 1
for the ternary ephemeral, the κ = 128 row would read: FIXEDMANUAL certified at D = 1-5 (15.82,
14.51, 14.42, 14.36, 14.31 bits), FIXEDAUTO / FLEXIBLEAUTO at D = 1-2 (4.71 / 3.90; 1.70 / 0.89),
FLEXIBLEAUTOEXT unchanged (its fresh noise is switched away by the first reduction); D ≥ 6 stays
NOT CERTIFIED in every technique.

**Why (worst case): what OpenFHE's parameter generation enforces.** (
file:line in OpenFHE v1.6.1, `src/pke/lib/scheme/bgvrns/bgvrns-parametergeneration.cpp` unless
noted.)
- **FIXEDMANUAL uses no noise model.** The prime size is a fixed rule, `dcrtBits = min(60, 28 +
  GetMSB64(t))` (`:382-385`), 45 bits for t = 65537, and `firstModSize = dcrtBits` (`:387-388`),
  whatever the depth, N, the number of additions or key switches.
- **The automatic modes** (FIXEDAUTO, FLEXIBLEAUTO, FLEXIBLEAUTOEXT) size the primes with a
  heuristic high-probability estimate (`computeNoiseEstimates`, `:86-143`, in the style of
  Kim-Polyakov-Zucca, eprint 2021/204, cited in the file's header): each Gaussian coefficient is
  taken to be at most Berr = σ·√α = 6σ = 19.14 (`:95`; α = 36, `assuranceMeasure`,
  `include/scheme/bgvrns/gen-cryptocontext-bgvrns-internal.h:67`; per coefficient a continuous
  Gaussian exceeds 6σ with probability about 2·10⁻⁹, so this is not a bound with a stated failure
  probability); a product of polynomials grows by the expansion factor 2√N instead of the
  worst-case N (`:104-105`), and the rounding term of a modulus switch by 4√N (`:106-107`). Fresh
  noise V_fresh = Berr·(1 + 2·2√N·Bkey) (`:109`), with Bkey = 1 for a ternary single-party key
  (`:102-103`). The primes are then chosen so that a per-level STEADY-STATE estimate is restored
  after each ModReduce: V_c = (A+1)·V_fresh + (K+1)·V_ks (`:138`; FLEXIBLEAUTOEXT: V_c =
  1 + 4√N·Bkey, `:136`), with A = `EvalAddCount` = 5 and K = `KeySwitchCount` = 3 by default
  (`include/scheme/gen-cryptocontext-params-defaults.h:144-145`); q₀ from 2·t·V − t (`:191-196`);
  every other prime from the bound at `:224-238`. The multiplicative depth only sets the number of
  primes. (HEIR's default BGV model `bgv-noise-kpz21` is the same kind of estimate; HEIR labels it
  "average-case".)

Term by term against `fhe_check`'s worst-case rules (phase units, t = 65537; log₂; "OpenFHE" =
its estimate times t):

| operation | `fhe_check` (worst case) | OpenFHE's estimate | gap at N = 2^13 / 2^14 / 2^15 |
|---|---|---|---|
| fresh encryption | (t−1) + 39t(1+2N): 35.29 / 36.29 / 37.29 | t·V_fresh: 28.76 / 29.26 / 29.76 | 6.5 / 7.0 / 7.5 bits (1.03 from 39 vs 6σ = 19.14, the rest from N vs 2√N) |
| modulus switch | ⌈t(1+N)/2⌉: 28.00 / 29.00 / 30.00 | t·V_ms: 23.50 / 24.00 / 24.50 | 4.5 / 5.0 / 5.5 bits |
| product | N·B₁·B₂ | about 2√N·B₁·B₂ (+ lower terms) | 5.5 / 6.0 / 6.5 bits per product, on top of the operands' gaps |
| addition | B₁ + B₂ | OpenFHE pre-pays (A+1) = 6 products and (K+1) = 4 key switches per level | ~2.6 bits of slack on OpenFHE's side for the `chain` program |

So the gap is not a constant factor: per operation it is 5-7.5 bits, but because OpenFHE sets the
primes right at its own steady state, `fhe_check`'s worst-case excess compounds. With the
worst-case rules a squaring chain has a bounded fixed point only if q ≥ about 4·N·msBudget ≈
2·t·N² (2^43 / 2^45 / 2^47 at N = 2^13 / 2^14 / 2^15); below that the excess exponent doubles at
every square. OpenFHE's chosen scaling primes are 42-44 bits in FIXEDAUTO/FLEXIBLEAUTO and 37-38
in FLEXIBLEAUTOEXT (1-3 and 7-9 bits below that threshold), and FIXEDMANUAL's 45-bit primes clear
it only at N = 2^13 (D = 1, certified with 5.43 bits). This is why the overflow figures grow to
100-1900 bits while the smallest fix is only +3 to +9 bits per prime (next section), and why
`SetEvalAddCount` (which enlarges every prime) certifies the automatic modes (see "Getting
parameters that are certified").

### Smallest fix (the tool's suggestions)

On NOT CERTIFIED `fhe_check` prints, marked as a search and not a theorem:
- the largest K (bisection, 1..512) for which `--kappa K` certifies the same file;
- the smallest k (bisection, 1..64) such that the verified analyzer accepts the same program on
  the hypothetical chain with every ciphertext and special modulus multiplied by 2^k. Sizes only:
  the real primes are chosen by the library, so the suggestion must be re-checked on the
  regenerated parameters. The suggestion states log₂(Q·P) after the fix against the 128-bit cap
  at N. If it exceeds the cap, it says so ("exceeds the 128-bit cap at this N (log2 QP after the
  fix = X > cap C)"), and a second suggestion gives the smallest k at 2N: the same program with
  its rotations moved (±5^e, as `recommend` does), the input noise recomputed at 2N from the
  file's `freshEncryption` bounds (`Spec.Encrypt.freshNoise`/`worstError`; with `--kappa`, ε at
  2N), and whether that is under the cap at 2N. A file without `freshEncryption` (HEIR, neutral)
  gets "cannot be computed by this tool" and a pointer to `fhe_check recommend`, which also
  searches other chains at the same N. Examples (`tests/expected.tsv`): HEIR `mult_dep_8` default
  +7 → 239.00 > 218; OpenFHE default FLEXIBLEAUTOEXT D = 6 +7 → 460.32 > 438, at 2^15 +9 → 480.32
  ≤ 881.

For the table above, in worst-case mode:

| D | FIXEDMANUAL | FIXEDAUTO | FLEXIBLEAUTO | FLEXIBLEAUTOEXT |
|---|---|---|---|---|
| 1 | certified | +5 bits (or K ≤ 11) | +5 | +3 |
| 2 | +3 bits (or any K ≤ 512) | +7 | +7 | +5 |
| 3 | +4 (or K ≤ 126) | +7 | +7 | +6 |
| 4 | +5 (or K ≤ 26) | +8 | +8 | +7 |
| 5 | +5 (or K ≤ 4) | +8 | +8 | +7 |
| 6 | +8 | +9 | +9 | +7 |
| 7 | +8 | +9 | +9 | +8 |
| 8 | +8 | +9 | +9 | +9 |

The FIXEDMANUAL column agrees with real regenerated parameters: `SetScalingModSize` 48, 49, 50,
50, 53, 53, 53 bits certified D = 2..8 in the earlier sweep (45 + 3, 4, 5, 5, 8, 8, 8). For the
automatic modes `SetScalingModSize`/`SetFirstModSize` are rejected
(`gen-cryptocontext-params-validation.cpp:150-159`); the knob that enlarges their primes is
`SetEvalAddCount`. Re-run on 2026-11-13 with the current decryption model
(`recommend/roundtrip.sh --auto`): 100-200 for FIXEDAUTO/FLEXIBLEAUTO, 200-5000 for FLEXIBLEAUTOEXT
(table in "Getting parameters that are certified"). `fhe_check recommend` now gives certified
FIXEDMANUAL settings with OpenFHE's exact primes.

## Getting parameters that are certified (`fhe_check recommend`)

`fhe_check FILE` says whether a program is safe at the parameters in FILE. When the answer is
NOT CERTIFIED, `fhe_check recommend FILE` gives parameters for which it is CERTIFIED, in the
library's own configuration terms, with the exact primes the library will generate:

```
.lake/build/bin/fhe_check recommend prog.fhecheck.json                 # search, print settings
.lake/build/bin/fhe_check recommend --emit rec.fhecheck.json prog.fhecheck.json
.lake/build/bin/fhe_check rec.fhecheck.json                            # the full certificate
                                                    # (with --kappa K: fhe_check --kappa K rec.fhecheck.json)
```

**What it does, in plain terms.** It keeps your program exactly as extracted (operations,
rotations, plaintext operations, and the number of ciphertext primes, which the program's levels
fix) and changes only the parameters: the size of each prime, the number of key-switching digits
and, if needed, the ring dimension N. For every candidate it generates the actual primes the
way the library would and runs the same verified check as a plain `fhe_check` run. Among the
candidates that pass and respect a security limit on the total modulus size, it returns the one
with the least predicted evaluation time (the default objective, below), or with the smallest
log₂(Q·P) it found (the `size` objective). The parameters it returns are then written as a normal
input file (`--emit`), read back, and checked again by the plain pipeline; the verdict it prints
is that check's. So the recommendation is a CERTIFIED result with the usual certificate theorem
(`Challenge.Certify.worst_certified`, or `Challenge.Certify.fresh_kappa_certified` with `--kappa`). It is
**not** claimed to be the smallest possible: the search covers a family of chains (sizes
`[f, s, …, s]` for OpenFHE; for HEIR, each prime size and the special-prime size lowered in turn)
by bisection.

**The search is only a search; soundness never depends on it.** Whatever the search, the cost
model or the batching rule below decide, they only choose WHICH parameters are checked: the
verdict printed is the locked decision (`certify?`, through the same path as a plain check) on
the emitted file. A wrong cost model can make a recommendation slower than necessary, never
uncertified.

**Objective: least predicted time (default) or least log₂(Q·P).** For each ring dimension and
each digit count the search finds the least log₂(Q·P) of its family; among those it takes the
least time proxy `T ≈ N·log₂N·(a·A + b·B)` (`FHE.Check.Rec.costProxy`, a MODEL): `A` sums the
number of limbs ℓ at every multiplication, rotation and modulus switch of the program, `B` sums
`⌈ℓ/α⌉·(ℓ + K)` at every key switch (digits of α limbs, K special primes). `a` and `b` were fitted
on 28 measured OpenFHE v1.6.1 FIXEDMANUAL contexts (pristine build, one thread; chain and
inner-product+polynomial programs, depth 2-12, N = 2^13..2^15, every digit count from 1 to L): the
largest relative error is 7.6% (`harness/eval/frontier/RESULTS.md`, data in
`harness/eval/frontier/data/timing_fit.json`). The file's own digit count is kept unless another
is predicted faster by more than that error (8%), and with `--digits any` the next larger ring
dimension is also compared. Why: minimising log₂(Q·P) alone picked one limb per digit (dnum = L),
which made a depth-10 chain 1.55× SLOWER at the same N (measured); the proxy keeps dnum = 3 there
and still moves depth 6 to N = 2^14 (dnum = 7; measured 0.62× the default's time). The previous
objective is `--objective size` (exactly the earlier output; the option needs the CLI patch noted
in `harness/eval/frontier/README.md` until it is merged). The report states the objective and the
MODELLED time ratio; `harness/eval/frontier/` has the MEASURED ratios.

**Packed encoding limits N (OpenFHE target).** The OpenFHE BGV extractor accepts only packed
plaintexts, and packed encoding needs t ≡ 1 mod 2N (OpenFHE v1.6.1 throws in `RootOfUnity` at
`MakePackedPlaintext` otherwise). So for t = 65537 no ring dimension above 2^15 is proposed; when
none at or below it certifies, the answer is "no certified parameters within N ≤ 32768 for this
plaintext modulus", and `--ring-dim 65536` is refused. (Before this rule, a depth-12 chain with
`--digits keep`, and the `--security 192` case of the depth-8 example, were given N = 2^16, which
OpenFHE rejects.) The rule is applied when the file's own N satisfies it; HEIR/neutral targets are
not restricted.

**BFV and the OpenFHE automatic BGV modes: library-in-the-loop search.** `fhe_check recommend`
answers UNSUPPORTED for them (the BFV context, its auxiliary bases and the internal drops of the
default HPSPOVERQLEVELED, and the programs of the automatic modes, depend on library internals
fhe_check does not model). `harness/eval/frontier/frontier.py` searches the settings OpenFHE's
public API offers for them by running the library itself: for BFV `SetMultiplicativeDepth`
(from 1), `SetScalingModSize` (14-60: every limb of Q has that size; the number of limbs is
⌈estimated log Q / size⌉, `bfvrns-parametergeneration.cpp:292,320`), `SetNumLargeDigits` (HYBRID),
the multiplication and key-switching techniques; for FLEXIBLEAUTOEXT/FIXEDAUTO/FLEXIBLEAUTO
`SetEvalAddCount`, `SetKeySwitchCount` and `SetMultiplicativeDepth` at or above the program's depth
(`SetScalingModSize`/`SetFirstModSize` are refused outside FIXEDMANUAL,
`gen-cryptocontext-params-validation.cpp:150-158`). Each candidate context is generated by OpenFHE,
the program is run traced and extracted, and the verdict is a plain `fhe_check` of that file; the
cheapest certified context by the same kind of time model is reported, with its measured time.

**Options.** `--target openfhe|heir|neutral` (default: the tool that produced FILE);
`--ring-dim N` (fixed N; default: the smallest N meeting the security level); `--security 128|192|256`
(default 128); `--digits keep|any|D` (key-switching digits: keep the file's, search, or a count;
OpenFHE: `SetNumLargeDigits`; HEIR: the number of special primes); `--kappa K`; `--margin BITS`
(require that many bits of margin; default 0, since CERTIFIED is already exact); `--sizes F,S`
(no search: show the primes the library would generate for these sizes, and the verdict);
`--objective time|size` (default time; see below); `--emit OUT`; `--json`. Exit codes: 0 parameters found, 1 none found, 2 unsupported, 3 invalid
input, 4 usage error.

**Primes, and which library rules are honoured** (file:line in upstream OpenFHE v1.6.1, b59e1f29,
and the HEIR source checkout at 26306bb):
- OpenFHE FIXEDMANUAL: every prime is ≡ 1 mod M, M = max(2N, power of 2 in t) × (odd part of t),
  i.e. NTT-friendly and ≡ 1 mod t, which keeps every message scale at 1
  (`bgvrns-parametergeneration.cpp:514-545`; `bgvrns-cryptoparameters.cpp:148-165` for P).
  q₀ = `LastPrime(f, M)`, q₁ = `PreviousPrime(LastPrime(s, M))` (or of q₀ if f = s), then
  `PreviousPrime` down (`nbtheory-impl.h:336-354,357-380,393-402`). Special primes: k =
  ⌈largest digit bit length / 60⌉, plus one more when 60·k − (that length) < 4 (a 4-bit margin new
  in v1.6.0), from `FirstPrime(60, M)` downward, skipping primes of the chain
  (`rns-cryptoparameters.cpp:135-190`, `auxBits = 60`). dnum digits must satisfy
  L > ⌈L/dnum⌉·(dnum−1) (`rns-cryptoparameters.cpp:89-96`). Sizes are at most 60 bits
  (`MAX_MODULUS_SIZE`). OpenFHE's own estimate of log₂(Q·P) (`bgvrns-parametergeneration.cpp:439-472`,
  `EstimateLogP` `rns-cryptoparameters.cpp:433-504`, with no extra bit for FIXEDMANUAL in v1.6.1)
  must also fit the security table, or `SetRingDim(N)` throws (`bgvrns-parametergeneration.cpp:52-80`).
- HEIR (Lattigo backend): `findPrime` = the smallest prime ≡ 1 mod 2N above 2^b, skipping t and
  primes already chosen (`lib/Parameters/RLWEParams.cpp:57-83,115-133`). HEIR skips its own
  parameter generation when the module already carries `bgv.schemeParam`
  (`lib/Transforms/GenerateParam/GenerateParamBGV.cpp:146-149`), and Lattigo uses those primes
  (`lib/Dialect/Lattigo/Transforms/ConfigureCryptoContext.cpp:136-142`,
  `lib/Target/Lattigo/LattigoEmitter.cpp:1992-2005`).
- neutral: the largest primes ≡ 1 mod 2N below 2^b, skipping primes that divide t.
- The test suite checks this mirror against the libraries: with the sizes of each of the 12
  committed OpenFHE FIXEDMANUAL and HEIR examples, `--sizes` predicts exactly the primes the library
  chose. Primality is re-checked by the verified `Spec.primeOK?` inside `schemeParamsOK?`.

**Security limit (an INPUT ASSUMPTION, not proved here).** log₂(Q·P) must stay below the
HomomorphicEncryption.org Security Standard table (Albrecht et al., November 2018) for ternary
secrets, classical security: 27, 54, 109, 218, 438, 881 bits at N = 2^10 … 2^15 for 128 bits
(192: 19 … 611; 256: 14 … 476), as transcribed in OpenFHE `src/core/lib/lattice/stdlatticeparms.cpp:169-186`.
The rows N = 2^16 and 2^17 (1747 and 3523 bits at 128) are OpenFHE's extension, not the 2018
standard, and are labelled so in the output. HEIR's own 128-bit table (ia.cr/2024/463; 214 and 430
bits at 2^13 and 2^14, `RLWESecurityParams.cpp:11-14`) is stricter; the report says whether a
HEIR recommendation meets it (HEIR does not check a user-supplied `schemeParam`).

**What a user gets** (the report also shows margins per output, sizes versus the file's own
parameters, and the fresh-ciphertext size in memory):
- OpenFHE: `CCParams<CryptoContextBGVRNS>` lines (`SetMultiplicativeDepth`, `SetScalingTechnique(FIXEDMANUAL)`,
  `SetFirstModSize`, `SetScalingModSize`, `SetNumLargeDigits`, `SetRingDim`, `SetSecurityLevel`).
  OpenFHE picks its OWN primes of those sizes; the recommendation names the primes its generator
  produces as read from its source, and the round trip below confirms it on the library.
- HEIR: the `module attributes {bgv.schemeParam = #bgv.scheme_param<logN = …, Q = […], P = […], …>}`
  wrapper for the input module, and the equivalent Lattigo `bgv.ParametersLiteral{LogN, Q, P, PlaintextModulus}`.

### Closing the loop: re-generated by the library and re-certified

`recommend/roundtrip.sh OUTDIR [--openfhe] [--heir] [--auto]` takes each recommendation, configures
the real library with it, re-runs the program, re-extracts, and re-checks with a plain `fhe_check`
run. Results of 2026-11-13 on this machine with OpenFHE v1.6.1 and the tracer
(128 cores, shared with other jobs, load average 16-35;
timings with `OMP_NUM_THREADS=1`/`GOMAXPROCS=1`, minimum over 75 OpenFHE evaluations or 15 Lattigo
evaluations per configuration, run interleaved; they are measurements, not claims).

**OpenFHE FIXEDMANUAL, the default-user `chain` program** ((a·b)^(2^(D−1)), t = 65537, HYBRID,
dnum kept at OpenFHE's default). "Re-check" is the plain check of the file re-extracted from
OpenFHE's run at the recommended settings (value-checked against OpenFHE's decryption):

| D | OpenFHE default (FIXEDMANUAL) | verdict | recommended | OpenFHE's primes = predicted | re-check on OpenFHE's primes | log2(Q*P) | ciphertext | evaluation (min of runs) |
|---|---|---|---|---|---|---|---|---|
| 1 | N=2^13, 45+45, dnum 2 | certified (5.43) | N=2^13, f=36, s=49, dnum 2 | yes | certified (0.06) | 150.0 -> 144.6 | 256 -> 256 KiB | 4.2 -> 4.2 ms (x1.00) |
| 2 | N=2^14, 45+45+45, dnum 2 | not certified (over 8.15) | N=2^14, f=36, s=51, dnum 2 | yes | certified (0.43) | 255.0 -> 257.6 | 768 -> 768 KiB | 21.9 -> 21.8 ms (x1.00) |
| 3 | N=2^14, 45+45+45+45, dnum 2 | not certified (over 29.30) | N=2^14, f=34, s=51, dnum 2 | yes | certified (1.14) | 300.0 -> 306.8 | 1024 -> 1024 KiB | 32.8 -> 33.2 ms (x1.01) |
| 4 | N=2^14, 45+45+45+45+45, dnum 3 | not certified (over 71.62) | N=2^14, f=34, s=51, dnum 3 | yes | certified (3.60) | 345.0 -> 357.8 | 1280 -> 1280 KiB | 65.6 -> 63.9 ms (x0.97) |
| 5 | N=2^14, 45+45+45+45+45+45, dnum 3 | not certified (over 26.64) | N=2^14, f=34, s=51, dnum 3 | yes | certified (3.80) | 390.0 -> 408.8 | 1536 -> 1536 KiB | 95.3 -> 96.7 ms (x1.01) |
| 6 | N=2^15, 45+45+45+45+45+45+45, dnum 3 | not certified (over 12.73) | N=2^15, f=37, s=53, dnum 3 | yes | certified (5.52) | 494.9 -> 534.5 | 3584 -> 3584 KiB | 303.7 -> 284.0 ms (x0.93) |
| 7 | N=2^15, 45+45+45+45+45+45+45+45, dnum 3 | not certified (over 129.64) | N=2^15, f=37, s=53, dnum 3 | yes | certified (5.52) | 539.9 -> 587.5 | 4096 -> 4096 KiB | 366.5 -> 349.1 ms (x0.95) |
| 8 | N=2^15, 45+45+45+45+45+45+45+45+45, dnum 3 | not certified (over 84.77) | N=2^15, f=37, s=53, dnum 3 | yes | certified (5.52) | 584.9 -> 640.5 | 4608 -> 4608 KiB | 464.3 -> 452.2 ms (x0.97) |

- **Recommended settings were regenerated by OpenFHE and re-certified on OpenFHE's own primes**
  at every depth 1-8: OpenFHE's primes are exactly the predicted ones, the extracted program is the
  same, and the plain check is CERTIFIED.
- The cost is nil at these depths: the recommendation keeps N and the number of primes (in memory
  every prime is a 64-bit word whatever its size), so the ciphertext is the same size and the
  measured evaluation time is within 3% (within the run-to-run noise). The scaling primes grow
  from 45 to 49-53 bits and the first prime shrinks to 34-37 bits.
- Margins are thin (0.06-5.52 bits) because the search minimises size, even when the input is
  already certified: at D = 1 OpenFHE's default is certified with 5.43 bits, and the
  recommendation is 5 bits smaller with 0.06 bits of margin. Both are certificates; `--margin BITS`
  keeps headroom.

**HEIR (Lattigo backend)**: HEIR's default-model (`bgv-noise-kpz21`) parameters, HEIR's worst-case noise
model, and the recommendation (from the default file), re-compiled by `heir-opt` with the
recommended `bgv.schemeParam`, re-extracted and re-checked; then each version is translated to Go
by HEIR (`--scheme-to-lattigo`, `heir-translate --emit-lattigo`), run on Lattigo v6.1.0 and timed;
every run decrypted the right result:

| program | HEIR default model (kpz21) | HEIR worst-case model | recommended | HEIR's primes = predicted | re-check | log2(Q*P) default / worst / rec | Lattigo evaluation, min (default / worst / rec) |
|---|---|---|---|---|---|---|---|
| mult_dep_8 | N=2^13, 28+35+35+35 / P 35+35: not certified (over 51.05) | N=2^14, 33+46+46+46 / P 46+46: certified (1.43) | N=2^13, 40+41+41+41 / P 26+26 | yes | certified (0.29) | 197.0 / 257.0 / 209.0 | 11.4 / 24.9 / 11.8 ms |
| dot_product_8 | N=2^13, 28+32+38 / P 38+38: not certified (over 7.01) | N=2^13, 33+32+49 / P 49+49: certified (2.66) | N=2^13, 34+36+36 / P 21+21 | yes | certified (0.81) | 169.0 / 207.0 / 143.2 | 15.0 / 15.4 / 14.9 ms |

- HEIR's primes after re-compilation are the predicted ones, and the re-extracted program is the same.
- `mult_dep_8`: certified at N = 2^13 (209 bits, within HEIR's own 214-bit table), where HEIR's
  worst-case model needs N = 2^14; Lattigo evaluation as fast as HEIR's uncertified default and
  about half the time of HEIR's worst-case choice. `dot_product_8`: certified with a smaller
  log₂(Q·P) than HEIR's own default.
- The special primes come out small (21-26 bits): the proved key-switching budget allows it here
  because the product noise dominates. Lattigo accepts such P and decrypted correctly; the
  certificate is about the noise bound, as always.
- `heir-translate` was fetched on 2026-11-13 from the HEIR `nightly` release
  (`heir-translate-manylinux_2_28_x86_64`, sha256 `596620538688d24fa75b3d06f63c0df46d8d2279f25e15a0e357dbad5a1fb5a5`;
  a later nightly than the `heir-opt` above, used only to turn the lattigo dialect into Go), into
  the gitignored `harness/build/heir-nightly/`. Lattigo v6.1.0 and its Go dependencies come from
  proxy.golang.org.

**OpenFHE's automatic scaling modes (FIXEDAUTO, FLEXIBLEAUTO, FLEXIBLEAUTOEXT, the default)**:
`fhe_check recommend` answers UNSUPPORTED for them, by design. There the extracted program itself
depends on the primes (OpenFHE inserts its own modulus switches and multiplies by constants
c = sf₂·sf₁⁻¹·q mod t chosen from the primes, `bgvrns-leveledshe.cpp:85-225`; FLEXIBLEAUTOEXT adds a
limb), so certifying the same program on other primes would certify something OpenFHE does not
run; and OpenFHE refuses `SetScalingModSize`/`SetFirstModSize` outside FIXEDMANUAL
(`gen-cryptocontext-params-validation.cpp:150-159`). What a user CAN do:
1. switch to FIXEDMANUAL (with `ModReduce` after each multiplication) and use `recommend` as
   above; or
2. raise `SetEvalAddCount`, one of the inputs OpenFHE's own noise estimate uses to size its
   primes (`bgvrns-parametergeneration.cpp:86-143` estimate, `:171-278` prime sizes), and re-check the result.
   `roundtrip.sh --auto` measures what that achieves on the `chain` program (values tried: 5
   (the default), 10, 20, 50, …, 100000; the first one that certifies):

| technique | D | OpenFHE default (SetEvalAddCount 5): N, limb bits, verdict | smallest SetEvalAddCount tried that certifies | N, limb bits there | margin | ciphertext | evaluation (median) |
|---|---|---|---|---|---|---|---|
| FIXEDAUTO | 1 | 2^13, 34+43: not certified (over 8.76) | 100 | 2^13, 38+51 | 2.74 | 256 -> 256 KiB | 10.3 -> 4.2 ms |
| FIXEDAUTO | 2 | 2^14, 34+44+44: not certified (over 25.32) | 100 | 2^14, 38+52+52 | 2.67 | 768 -> 768 KiB | 22.3 -> 54.0 ms |
| FIXEDAUTO | 3 | 2^14, 34+44+44+44: not certified (over 54.41) | 100 | 2^14, 38+52+52+52 | 5.42 | 1024 -> 1024 KiB | 91.8 -> 83.6 ms |
| FIXEDAUTO | 4 | 2^14, 34+44+44+44+44: not certified (over 11.34) | 100 | 2^14, 38+52+52+52+52 | 10.51 | 1280 -> 1280 KiB | 65.5 -> 89.6 ms |
| FIXEDAUTO | 5 | 2^14, 34+44+44+44+44+44: not certified (over 69.39) | 100 | 2^14, 38+52+52+52+52+52 | 15.41 | 1536 -> 1536 KiB | 105.2 -> 279.9 ms |
| FIXEDAUTO | 6 | 2^15, 37+45+45+45+45+45+45: not certified (over 37.67) | 200 | 2^15, 40+55+55+55+55+55+55 | 17.08 | 3584 -> 3584 KiB | 286.2 -> 332.3 ms |
| FIXEDAUTO | 7 | 2^15, 37+45+45+45+45+45+45+45: not certified (over 169.69) | 200 | 2^15, 40+55+55+55+55+55+55+55 | 17.08 | 4096 -> 4096 KiB | 658.0 -> 360.5 ms |
| FIXEDAUTO | 8 | 2^15, 37+45+45+45+45+45+45+45+45: not certified (over 125.48) | 200 | 2^15, 40+55+55+55+55+55+55+55+55 | 17.08 | 4608 -> 4608 KiB | 1113.1 -> 945.0 ms |
| FLEXIBLEAUTO | 1 | 2^13, 34+43: not certified (over 9.57) | 100 | 2^13, 38+51 | 2.43 | 256 -> 256 KiB | 13.1 -> 10.7 ms |
| FLEXIBLEAUTO | 2 | 2^14, 34+44+44: not certified (over 26.14) | 100 | 2^14, 38+52+52 | 1.83 | 768 -> 768 KiB | 74.5 -> 57.1 ms |
| FLEXIBLEAUTO | 3 | 2^14, 34+44+44+44: not certified (over 55.28) | 100 | 2^14, 38+52+52+52 | 4.58 | 1024 -> 1024 KiB | 46.6 -> 44.9 ms |
| FLEXIBLEAUTO | 4 | 2^14, 34+44+44+44+44: not certified (over 12.28) | 100 | 2^14, 38+52+52+52+52 | 9.66 | 1280 -> 1280 KiB | 76.2 -> 64.9 ms |
| FLEXIBLEAUTO | 5 | 2^14, 34+44+44+44+44+44: not certified (over 70.57) | 100 | 2^14, 38+52+52+52+52+52 | 14.56 | 1536 -> 1536 KiB | 104.1 -> 99.7 ms |
| FLEXIBLEAUTO | 6 | 2^15, 35+45+45+45+45+45+45: not certified (over 40.57) | 200 | 2^15, 40+55+55+55+55+55+55 | 16.97 | 3584 -> 3584 KiB | 400.3 -> 343.3 ms |
| FLEXIBLEAUTO | 7 | 2^15, 35+45+45+45+45+45+45+45: not certified (over 173.13) | 200 | 2^15, 40+55+55+55+55+55+55+55 | 16.97 | 4096 -> 4096 KiB | 430.1 -> 498.5 ms |
| FLEXIBLEAUTO | 8 | 2^15, 35+45+45+45+45+45+45+45+45: not certified (over 129.13) | 200 | 2^15, 40+55+55+55+55+55+55+55+55 | 16.97 | 4608 -> 4608 KiB | 633.8 -> 364.6 ms |
| FLEXIBLEAUTOEXT | 1 | 2^13, 31+37+17: not certified (over 4.00) | 200 | 2^13, 31+42+17 | 1.00 | 384 -> 384 KiB | 4.5 -> 4.5 ms |
| FLEXIBLEAUTOEXT | 2 | 2^14, 32+38+38+18: not certified (over 17.05) | 1000 | 2^14, 32+45+45+18 | 0.83 | 1024 -> 1024 KiB | 22.8 -> 22.6 ms |
| FLEXIBLEAUTOEXT | 3 | 2^14, 32+38+38+38+18: not certified (over 41.10) | 2000 | 2^14, 32+46+46+46+18 | 2.05 | 1280 -> 1280 KiB | 35.5 -> 40.2 ms |
| FLEXIBLEAUTOEXT | 4 | 2^14, 32+38+38+38+38+18: not certified (over 4.10) | 2000 | 2^14, 32+46+46+46+46+18 | 1.86 | 1536 -> 1536 KiB | 60.3 -> 60.6 ms |
| FLEXIBLEAUTOEXT | 5 | 2^14, 32+38+38+38+38+38+18: not certified (over 52.20) | 5000 | 2^15, 32+49+49+49+49+49+20 | 2.55 | 1792 -> 3584 KiB | 75.3 -> 173.3 ms |
| FLEXIBLEAUTOEXT | 6 | 2^14, 32+38+38+38+38+38+38+18: not certified (over 15.20) | 5000 | 2^15, 32+49+49+49+49+49+49+20 | 2.54 | 2048 -> 4096 KiB | 103.9 -> 233.9 ms |
| FLEXIBLEAUTOEXT | 7 | 2^14, 32+38+38+38+38+38+38+38+18: not certified (over 111.40) | 5000 | 2^15, 32+49+49+49+49+49+49+49+20 | 2.54 | 2304 -> 4608 KiB | 134.3 -> 505.5 ms |
| FLEXIBLEAUTOEXT | 8 | 2^15, 32+39+39+39+39+39+39+39+39+20: not certified (over 103.19) | 5000 | 2^15, 32+49+49+49+49+49+49+49+49+20 | 2.54 | 5120 -> 5120 KiB | 728.3 -> 3140.8 ms (SetEvalAddCount 500: see below) |

- Every automatic mode certifies, in the worst case, at every depth 1-8 once `SetEvalAddCount` is
  large enough: 100 (D ≤ 5) or 200 (D = 6-8) for FIXEDAUTO and FLEXIBLEAUTO, without changing N
  (the cost is larger primes only: 38-40-bit first prime, 51-55-bit others); 200-5000 for the
  default FLEXIBLEAUTOEXT, whose first prime stays 31-32 bits so the decryption margin stays thin
  (0.83-2.55 bits). At D = 5-7 FLEXIBLEAUTOEXT then moves to N = 2^15, which doubles the
  ciphertext.
- Values tried: 5, 10, 20, 50, 100, 200, 500, 1000, 2000, 5000, ...; the first certifying one is
  shown, so the true threshold lies between it and the previous value. This is a measurement of
  OpenFHE v1.6.1 on the `chain` program, not a rule: re-check your own program. At FLEXIBLEAUTOEXT
  D = 8, `SetEvalAddCount(500)` made the traced v1.6.1 build throw (`PrecomputeCRTTables(): EstimateLogP()
  failure: expected sizeP [3], but got sizeP [4]`, `rns-cryptoparameters.cpp:161`); not investigated
  further and not re-checked on an untraced build, so not claimed as an OpenFHE issue.
- The evaluation times in this table are medians of 3 runs, not interleaved, on a loaded machine:
  differences under about 1.5x are noise. Where N is unchanged the cost is expected to be nil (the
  FIXEDMANUAL table above, measured carefully, shows 1-3%).
- Why `recommend` does not do this itself: the program extracted from an automatic mode depends on
  the primes (and the inputs to OpenFHE's noise estimate are not parameters `fhe_check` models), so
  the only sound procedure is the one above: change the setting, re-run, re-extract, re-check.

**Scope.** BGV only. Worst-case evaluation (with `--kappa`, fresh-encryption noise is probabilistic,
as in a plain check). The number of ciphertext primes is the program's. Assumed about the library,
as for any certificate: that its operations meet the per-operation contracts (not verified for
OpenFHE's C++ or Lattigo's Go), the noise constants the extractor supplies, and, for the
recommendation specifically, that the library generates the primes it is predicted to; the round
trip checks that last one instead of assuming it. Unverified glue that can affect a verdict is
printed in the report: the input noise when N or the special primes change (OpenFHE: recomputed
with the verified `Spec.Encrypt.freshNoise`/`worstError` from the file's `freshEncryption` bounds;
HEIR: the Lattigo formula of `heir/extract_bgv.py` at the new N and p₀), and the Galois elements of
rotations when N changes (±5^e mod 2N ↦ ±5^e mod 2N'). Files without a `freshEncryption` section
(neutral, hand-written) are recommended at their own N only.

## Declare your own profile (`--profile FILE`, `--emit-profile`)

The default mode computes the budget every operation is charged from OpenFHE's own algorithms (the
key-switching layout, the BFV technique table). The **profile mode** takes the budget from you
instead, so it works for any implementation, with no library table involved:

    fhe_check --emit-profile PROGRAM.fhecheck.json > my.profile.json   # start from the table mode's budget
    fhe_check --profile my.profile.json [--json] PROGRAM.fhecheck.json

**What it decides.** CERTIFIED only when the locked `Challenge.Profile.certifyProfile? P E prog sw`
(BGV) or `Challenge.Profile.certifyBFVProfile? P E prog` (BFV) accepts at the declared budget `E`, and
whenever it does, except that a frontend `expect` that disagrees with `Source.step` withholds the
certificate (as in the default mode; a malformed profile is INVALID INPUT and a program above
`--max-instructions` UNSUPPORTED before any decision). The decision is
computed by `FHE.Holes.certifyProfileFast` / `certifyBFVProfileFast`, which are proved equal to them
on every input and at every budget (`Challenge.Fast.certifyProfileFast_eq`,
`certifyBFVProfileFast_eq`; proofs `Validation/FastProfile.lean`). It then instantiates
`Challenge.Profile.certifyProfile?_sound` (`certifyBFVProfile?_sound`): **every run in which each
instruction meets its contract within the declared budget** ends in outputs that decrypt (textbook
decryption at the output's level, or after the switch to one limb for BGV) to what the program
computes, with noise at most the printed bound. The report then says whether the **coverage
check** passes: BGV `Challenge.Profile.coversBGV?` (hybrid key switching on the layout, the centred
t-corrected modulus switch of 1..K components, K at least the largest number of components the
program switches), BFV the level-exact `Challenge.Profile.coversBFVAt?` (by
`FHE.Holes.coversBFVAtFast`, proved equal; the multiplication family `(U, r)`: lifts within `U`,
rounding within `r/2`, default `U = 0`, `r = 1`, the textbook multiplication) and, as a further line,
the conservative `coversBFV?` (key switching charged at every level). When it passes, the proved
algorithm families meet every instruction's contract within the profile (`coversBGV?_relin`, ...,
`coversBFVAt?_mul`, ...; secret within `secretBound`, keys meeting `Spec.Budget.GadgetKeysOK`).
When it does not, **the verdict is a conditional statement** about implementations that meet the
profile, not a claim that one exists; the report says so in the verdict line. (The zero profile is
accepted for many programs: it is sound, and says nothing about any implementation.) The per-class
lines under COVERAGE (which class fails, at which instruction, needed vs declared) are untrusted
diagnostics; the covered/not covered claim is the Bool of the locked check.

**What it does not read**: the technique table and internal drops (`bfv`), `freshEncryption`
(`--kappa` is a usage error with `--profile`), `modSwitch.method`, `scaling`. `params.inputNoise` is
the ASSUMPTION on every input ciphertext. Not covered: the library's own decryption routine and
user-level decoding. Exit codes as in the default mode (0 CERTIFIED, whether covered or not: read
`coverage.covered` in `--json`).

**The file** (`fhe-check-profile/v1`, strict schema; numbers as decimal strings or JSON integers;
`source` is printed only):

    { "format": "fhe-check-profile/v1", "scheme": "BGV",
      "budget": { "keySwitch": n, "modSwitch": n, "modSwitchOne": n,
                  "modSwitchMany": { "default": n, "at": [ { "parts": 3, "bound": n } ] } },
      "coverage": { "keySwitching": { as in the program file }, "modSwitchParts": K } }

    { "format": "fhe-check-profile/v1", "scheme": "BFV",
      "uniform": { "keySwitch": n, "modSwitch": n, "mulLift": n, "mulRound": n, "plainAdd": n },
      -- or, instead of uniform:
      "perInstruction": { "budgets": [ {the five numbers}, ... ], "at": [ i_0, ..., i_{n-1} ] },
      "coverage": { "keySwitching": { ... }, "mulFamily": { "U": n, "r": n } } }

BGV: the fields of `Spec.Trace.Budget`; `modSwitchMany k` (a value with `k ≥ 3` components) is the
listed bound, else `default` (required: no silent zero). BFV: `Spec.TraceBFV.Budget`, either one for
every instruction, or instruction `k` gets `budgets[at[k]]` with one `at` entry per instruction; the
budget is then `Challenge.CertifyBFV.budgetFn` of that array, which is how the table mode stores
its own, so the BFV profile `--emit-profile` writes is exactly the table mode's budget `c.budget`
(tested against `--json budget.perInstruction`). The BGV emitted profile is not literally
`Spec.Budget.certified P lay`: `modSwitchMany` agrees with it at the listed numbers of components
only, which are all the analysis of that program reads, so the BGV JSON round trip is a test, not
a theorem. The round-trip theorems below are about `c.budget` and the table mode's own parameters;
a BFV file with `freshEncryption` is certified by the table mode at the computed fresh input
noise, while the profile mode reads `params.inputNoise` (the committed OpenFHE files carry the
same number in both places, which is why their round trip agrees). The coverage layout defaults to the program file's.
`--emit-profile` writes the table mode's budget: BGV `Spec.Budget.certified P lay` (with
`modSwitchMany` listed at the numbers of components the program switches), BFV
`Challenge.CertifyBFV.budgetsBFV`. Table-mode acceptance implies profile acceptance at it with the
same bounds (`Challenge.Profile.certify?_profile`, `certifyBFV?_profile`; for the fast functions
`Validation.FastProfile.certifyFast_profileFast`, `certifyBFVFast_profileFast`); the converse fails,
since the table mode refuses more (special primes, layout restriction, key restriction, the
technique's side conditions, the library's decryption).

**Worked example** (`examples/profile/`): Lattigo v6.2.0's BGV at its small literal parameters
(`Challenge.Instances.Lattigo.small`) and the program shape recorded in `harness/lattigo-pin`
(`smallProg`), with Lattigo's profile `Challenge.Instances.Lattigo.profile small`:

    $ fhe_check --profile examples/profile/lattigo_small.profile.json examples/profile/lattigo_small.fhecheck.json
    VERDICT: CERTIFIED for every implementation within the declared profile (Challenge.Profile.certifyProfile? accepts at the declared budget); the profile IS covered by the proved algorithm families (COVERAGE below)
    ...
      z: noise <= 1385235815 (2^30.37), level 2, Q/2 = 2^54.00, margin 23.63 bits

Lower `keySwitch` to `1` and the verdict stays CERTIFIED but reads "the profile is NOT covered by
the proved algorithm families, so this is a conditional statement ..."; raise it to `2^60` and it
is NOT CERTIFIED at `body[6]`.

**Speed** (quiet 128-core machine, 2026-11-15, load average 1.2 to 2.7; median of
three runs, wall clock of the whole process including reading the file; synthetic `mixed` programs of
`harness/eval/analyzer-speed/gen.py`; the profile files are the one `--emit-profile` writes for the
base example (BGV, BFV) and a hand-written uniform BFV budget):
10^4 / 10^5 / 10^6 instructions: BGV 0.14 / 1.39 / 15.3 s;
BFV uniform profile 0.15 / 1.37 / 14.7 s; BFV per-instruction profile (the emitted one; 6 MB at
10^6) 0.17 / 1.82 / 19.0 s. The table mode on the same files (default flags, suggestions on): BGV
0.16 / 1.61 / 17.6 s, BFV 0.29 / 2.57 / 28.7 s. Writing the BFV per-instruction profile
(`--emit-profile`): 0.09 / 0.61 / 6.8 s. Spread of the three runs at 10^6: at most 7 %, except the BFV per-instruction
profile (18.9 to 20.0 s). Tests: `tests/profile/check_profile.py` (run.sh section 11) and run.sh
section 10 (linear growth at 15k/30k/60k).

## Lean side

1. **Modulus switch of a 1-part value.** `Spec.Trace.Budget.modSwitchOne`; the `modSwitch`
   clause of `StepOK` and `refBound` use it when the operand has one part;
   `Spec.Budget.msBudgetOne` = ⌈t/2⌉; pin `Challenge.Budget.modSwitch_realizable_one`.
2. **Decryption as OpenFHE does it.** `Spec/Decrypt.lean`, `Challenge/Decrypt.lean`
   (`decrypt_switched`, `outputLevel?_eq`, `analyze_decrypt_switched`).
3. **Probabilistic fresh noise.** `Spec/Encrypt.lean`, `Challenge/FreshNoise.lean`.
4. **The certificates as single statements, with the output key.** `Spec.Encrypt.outputKey?`,
   `outputsUnderS?`, `certOK?`; `Challenge.FreshNoise.OutputsDecrypt`, `certified_decrypts`,
   `fresh_worst_decrypts`, `fresh_kappa_decrypts`, `outputKey?_eq`, `freshOK?_spec`.

## Format (`fhe-check-v1.schema.json`)

- Big integers are decimal strings. Every bound, root of unity, budget and `expect` value in the
  file is re-derived or re-checked; only the fields marked ASSUMPTION are taken as given.
- `expect` (the library's own level and number of parts after an instruction) is compared with
  `Source.step`. A disagreement withholds the certificate.
- `fhe-check/v0` files are rejected; regenerate them with the extractors.

Operations:
- **Certified:** `add sub mul square mulConst negate copy toEval toCoeff relin keySwitch
  automorph modSwitch addPlain subPlain mulPlain dropLimbs`.
  A `modSwitch` of a value with k ≥ 3 parts is certified at `msBudgetAt P k`.
- **Answered UNSUPPORTED, with the operation named:** `rescale` (CKKS), unknown operations,
  and decryption methods other than `at-output-level` / `switch-to-one-limb`.
- **Answered UNSUPPORTED whatever the program:** a `modSwitch.method` other than
  `t-corrected-centred` (also for a program without any modulus switch), and an explicit
  per-level digit table (`keySwitching.digits.perLevel`) that does not restrict from the top
  level: the digits at each level must be the top-level digits cut down to that level's limbs
  (a `consecutive` layout always is).
- **Answered NOT CERTIFIED on the parameters:** an even special modulus (`specialOK?`), and a
  key noise with 2·⌊keyNoise/t⌋·t ≥ q₀·P (`keysRestrict?`).
- **Strict schema:** an object the decoder reads values from may contain only the fields of the
  format (`FHE.Check.onlyKeys`): a misspelt or unknown field (top level, `params`, `keySwitching`,
  `program`, an input declaration, an instruction, `freshEncryption`, `scaling`, `bfv`, ...) is
  INVALID INPUT, so an optional field is never silently replaced by its default. The printed-only
  objects (`source`, `noiseDerivation`, `crossCheck`, `provenance`, an input's `origin`,
  `bfv.encryption`) are free.
- **Optional sections:** `decryption` (which decryption the library performs; absent:
  at the output's level) and `freshEncryption` (needed by `--kappa`), with its optional
  `plaintextBound` and `mean` (absent: t − 1 and mean zero, printed as ASSUMED) and its optional
  `l2` object (`--kappa --l2`; see "Probabilistic fresh noise").

<!-- BEGIN BFV -->
## BFV (`params.scheme: "BFV"`)

A file with `params.scheme: "BFV"` is checked by the BFV pipeline (`FHE/Check/BFV*.lean`). The
verdict is CERTIFIED only if the locked `Challenge.CertifyBFV.certifyBFV?` returns a certificate
`c` on the decoded data AND the locked `Challenge.BFVDecryptLib.decryptLibExtOK?` holds of it (OpenFHE's
own decryption of every output is proved: "The library's own decryption decides too" below); it then instantiates `Challenge.CertifyBFV.certifyBFV?_sound`: every
output of every run in which instruction `k` meets its contract within `c.budget k` decrypts with
`s`, exactly (textbook decryption, `Spec.Scheme.bfvDecrypt`), at its own level, with noise at most
its own bound (worst case). **Fresh encryptions** (`freshEncryption`, written by the OpenFHE BFV
frontend for `ENCRYPTION_TECHNIQUE = STANDARD`; same fields as for BGV, `plaintextBound` unused):
the verdict is that of the locked `Challenge.BFVEncrypt.certifyBFVFresh?`, which computes the input
noise from the key and sampler bounds (`Spec.EncryptBFV.freshInputNoise = ε + max encodeDev`, the
error bound of `Spec.EncryptBFV.encryptBFV` plus the deterministic encoding term
`⌈(Q mod t)(t−1)/t⌉`), ignores `params.inputNoise`, and runs `certifyBFV?` at it:
`certifyBFVFresh?_worst` without `--kappa`; with `--kappa K` (and `--l2`) `certifyBFVFresh?_kappa`
(`_kappaL2`): failure probability at most `2^−K` per execution over the fresh-encryption
randomness (a union bound over `n·2N` events), evaluation worst case. Without `freshEncryption`
the declared `params.inputNoise` is used and `--kappa` is refused. **One budget per instruction**:
`c.budget k = Challenge.CertifyBFV.budgetBFV x k`, `Spec.BudgetBFV.budgetOf ks ms lift round pa`
for `body[k]`, analysed by the locked `Challenge.BFV.refAnalyzeBFVAt` (`Spec.TraceBFV.RunAt`).
When `c.assumed` is not empty (it can only be `[binary64]`) the verdict is printed "CERTIFIED
(binary64 steps of OpenFHE's … under the standard model Spec.Float.Conforms; see platform
conditions)": the library's floating-point multiplication (HPS family, `floatTolerant: true`) and
the floating-point scaling inside a key switch of `HPSPOVERQLEVELED` that drops limbs are proved to meet their
contracts for every arithmetic conforming to the standard model (`Challenge/BFVMul/Float.lean`,
`Challenge/BFVMul/KSLeveled.lean`, `Spec/Float.lean`), and that the platform conforms is the
hypothesis. Further locked statements: `certifyBFV?_mulLevels` (every `mul`/`square` is at a level
of the chain), `certifyBFV?_textbook_run_exists` (a run within `c.budget` exists: non-vacuity
only), and the realizability pins, each about ONE instruction (`Challenge.CertifyBFV.AtInstr`) and
its own budget. The program, parameters, `keySwitching`, `expect` and `provenance` are as for
BGV. Differences:

- `params.inputNoise`: ASSUMPTION (only without `freshEncryption`), every input ciphertext's BFV noise `e = [phase − ⌊Q/t⌋·m]_Q`
  has `‖e‖∞ ≤ inputNoise` (no lower bound). `params.keyNoise`: bound on the key-switching key
  errors (no divisibility by `t`). `params.special` may be empty (with one limb per digit that is
  RNS-digit, "BV", key switching).
- `program.inputs[].bound`: for a ciphertext its noise bound, for a plaintext (parts = 1)
  `‖p‖∞` (default `t − 1`). Unlike BGV, a declared bound **replaces** the default whether smaller
  or larger (`Spec.TraceBFV.inputBound`); the report carries a NOTE when it is larger.
- `modSwitch.method` must be `"round"` if the program modulus-switches
  (`Spec.BudgetBFV.msBudget`); `decryption.method`, if present, must be `"at-output-level"`.
- `bfv.multiplication` (needed iff the program has `mul`/`square`): `technique` is one of
  `textbook`, `HPS`, `HPSPOVERQ`, `HPSPOVERQLEVELED`, `BEHZ`; `auxBasis` (HPS: the auxiliary
  primes; P-over-Q: `P_l`; BEHZ: the base `B`), `mSk`, `mTilde` (BEHZ), `internalDrops`
  (`HPSPOVERQLEVELED`, ASSUMPTION, below), `floatTolerant` (default `true`: the budget includes
  the binary64 tolerances `doubleSw`/`doubleSr`, i.e. the floating-point error of the library's
  two sums is charged to the budget, and the bases must pass `Challenge.BFVMul.floatAuxOK?`: at
  most 128 moduli, each below 2^60; `false`: the idealised exact algorithm, which the library does
  not compute), `source`.
- `bfv.multiplication.internalDrops` (`HPSPOVERQLEVELED`): one natural number per instruction of
  `program.body`, the number of limbs OpenFHE drops internally at it (`FindLevelsToDrop` inside
  `EvalMult`, `EvalSquare`, `RelinearizeCore`; 0 elsewhere). REQUIRED when the program has a
  `mul`, `square`, `relin` or `keySwitch` (INVALID INPUT if missing, of the wrong length, or not
  below the number of limbs, and if nonzero anywhere but at a `mul`/`square`/`relin`/`keySwitch` of a
  TOP-LEVEL operand: the locked `Challenge.CertifyBFV.stepChecks` rejects such a drop, and the
  extractor never emits one); a program with none of them may omit
  it. Under any other technique it must be absent or all zero. `maxInternalDrop` /
  `maxInternalDropKS` (what older files carried instead) are still accepted as a CROSS-CHECK only:
  if present they must be at least every entry at a `mul`/`square`/`relin`, resp. `keySwitch`
  (INVALID INPUT otherwise); they do not enter the budget. **The checker cannot detect an
  understated drop** (0 where the library dropped 1: a smaller budget) from the file: the drops are
  an input assumption, which the OpenFHE extractor establishes by a three-way check (the drop
  OpenFHE recorded at run time, its dumped `FindLevelsToDrop` table, a Python replica; a tampered
  trace or table is refused, `tests/run.sh` 9g). `tests/negative-bfv/bfv_leveled_understated_drop.json`
  shows what such a file gets.
- **What each instruction is charged** (`Challenge.CertifyBFV.stepBudget`, `ℓ` the level of its
  first operand, `dr` its declared drop):
  - `mul`/`square`: the ONE slack of the technique at `(ℓ, dr)` (`Challenge.CertifyBFV.slackAt`:
    `textbook` ↦ (0, 1); `HPS` ↦ `hpsSlack` (exact: `Challenge.BFVMul.hpsAuxOK?`, slack (0, 1));
    `HPSPOVERQ` ↦ `poverqSlack` at `ℓ`; `HPSPOVERQLEVELED` ↦ `poverqSlack` below the top level or
    with `dr = 0`, `leveledSlack` for the drop `dr` at the top level; `BEHZ` ↦ `behzSlack`), then
    `mulLift = max(mulLift, mulLiftNormAt P ℓ e)`, `mulRound = mulRoundApprox P (max 1 ρ)`
    (`Challenge.BFVMul.stepOK_mul_lifted`); every other instruction gets the textbook numbers.
  - `relin`/`keySwitch`: `Spec.BudgetBFV.ksBoundAt` at the operand's own level; under
    `HPSPOVERQLEVELED` at the top level with `dr ≥ 1`, the larger of that and
    `Spec.BudgetBFV.ksLeveled N (Q_L/Q_{L−dr}) (ksBoundAt at L−dr) btgt r1` (`btgt = N·B_s²` for
    `relin`, `B_s` for `keySwitch`; `r1` the binary64 tolerance of the scaling, charged whatever
    `floatTolerant` says). PROVED: `Challenge.BFVMul.stepOK_relin_leveled_tol`,
    `stepOK_keySwitch_leveled_tol`, `ksCore_realizable` (certificate pins
    `Challenge.CertifyBFV.certifyBFV?_leveled_relin`, `_leveled_keySwitch`), for every arithmetic
    conforming to `Spec.Float.Conforms`. Under `HPSPOVERQLEVELED` a top-level key switch also needs
    the ciphertext moduli to pass `floatAuxOK?` (the library scales with a binary64 sum there even
    when it drops nothing). The certificate records `binary64` (with `floatTolerant: true`) only
    if the library drops limbs inside some key switch (`Challenge.CertifyBFV.ksDropped`): a key switch
    with drop 0 scales over no limb and is proved for every arithmetic
    (`Challenge.BFVMul.leveledKS_drop_zero`; pins `certifyBFV?_leveled_relin_drop0`,
    `_leveled_keySwitch_drop0`).
  - `addPlain`/`subPlain`: `0` (`delta`), `plainAddRoundedAt P ℓ b` (`rounded`) or
    `plainAddScaledAt P ℓ b` (`ceil`/`floor`/`scaled`) at the operand's own level, `b` the largest
    plaintext bound of the program.
  - `modSwitch`: `msBudget`.

  Which slacks are PROVED (report: "slacks PROVED", `budget.slacksProved`, `budget.mulPins`), always
  for a limb-level algorithm of `Challenge/BFVMul/*.lean` under its locked side condition, never
  for a library's machine code: `textbook`; `BEHZ` (integers only: `stepOK_mul_behz`,
  `stepOK_square_behz`); with `floatTolerant: false`, the idealised `HPS` (`stepOK_mul_hps`),
  `HPSPOVERQ` (`stepOK_mul_poverq`) and `HPSPOVERQLEVELED` (`stepOK_mul_leveled`); with
  `floatTolerant: true` (what OpenFHE's HPS family runs) the same three with the two binary64 sums
  as OpenFHE v1.6.1 computes them (`stepOK_mul_hps_float`, `stepOK_square_hps_float`,
  `stepOK_mul_poverq_float`, `stepOK_mul_leveled_float`, with `nuSw_tol`, `nuSr_tol`; measured
  against the real library functions in `harness/bfv-float/`). A false side condition, HPS or BEHZ
  below the top level, and a `square` under the P-over-Q variants (write `mul a a`) are answered
  UNSUPPORTED.
- The report prints the largest value of each number over the instructions that use it, the slack
  of each `(level, drop)` with the instructions charged it, and a per-instruction table (`mul`,
  `square`, `relin`, `keySwitch`, `addPlain`, `subPlain`); `--json` has every instruction in
  `budget.perInstruction` (`index`, `op`, `level`, `drop`, the five numbers with `log2`), and keeps
  the old top-level keys (`budget.keySwitch`, `mulLift`, `mulRound`, `plainAdd` are now these
  maxima; `budget.slacksProved`, `mulPins`, `slacks[]` with `drop` and `instructions`).
- `bfv.plainAdd.method` (needed iff the program has `addPlain`/`subPlain`): `delta` (the library
  adds `⌊Q/t⌋·p`), `rounded` (it adds `⌊Q·p/t⌉`), or `ceil` / `floor` / `scaled` (it adds a
  polynomial within one unit of `Q·p/t`, as OpenFHE's `TimesQovert` does by rounding up).
- `bfv.encryption`: printed only.
- Answered UNSUPPORTED: `dropLimbs` and `rescale` (not BFV operations), a `mul`/`square`/
  `modSwitch` of anything but a two-part ciphertext, `--kappa`. `negate` is `mulConst −1`.
- `fhe_check recommend` has no BFV mode (UNSUPPORTED, with the reason): a parameter search would
  have to model OpenFHE's BFV parameter generation and, for the default `HPSPOVERQLEVELED`, the
  internal drops of the hypothetical context, which `fhe_check` does not model (`FindLevelsToDrop`;
  the drops are an input assumption read from a run). The honest search is to re-generate the
  context, re-run, re-extract and re-check: `harness/eval/frontier/frontier.py bfv` does that over
  the multiplicative depth, the scaling-mod (limb) size, the digits and the techniques
  (library in the loop; every reported setting is a plain `fhe_check` verdict on the library's own
  run), and `levelbfv/depth_table.py` over the depth alone for the `chain` program.
- **The library's own decryption decides too.** `fhe_check` prints CERTIFIED for a BFV file only
  if the locked `Challenge.BFVDecryptLib.decryptLibExtOK?` holds
  (`Challenge.BFVDecryptLib.certifyBFV?_decryptsLibExt`: OpenFHE's decryption,
  `PKEBFVRNS::Decrypt` transcribed as `Spec.DecryptBFVLib.bfvDecryptOpenFHE`, returns, coefficient
  by coefficient, a representative in `[0, t]` of each output's message modulo `t`, for every
  arithmetic conforming to `Spec.DecryptBFV.ConformsD`). Each output, at its own level `ℓ` and with
  its own bound, must pass the routine the library runs on it:
  - `ℓ = L`, HPS family: the binary64 `DCRTPolyImpl::ScaleAndRound(t)` (`Spec/DecryptBFV.lean`),
    side condition `decParamsOK?` (`t < 2^50`, at most 128 odd pairwise coprime moduli below
    `2^60`) and margin `decLibOK?`;
  - `ℓ = L`, BEHZ: the integer `ScaleAndRound(…, tgamma, …)` (`Spec/DecryptBFVBEHZ.lean`), side
    condition `behzParamsOK?` (`t < 2^37`) and margin `decBEHZOK?`;
  - `ℓ < L` (after `Compress`), every technique: `DropLastElementAndScale` and the binary64
    `NativeIntegerT::MultiplyAndRound` (`bfvrns-pke.cpp:254-275`; `Spec/DecryptBFVLow.lean`), side
    condition `decLowParamsOK?` (`2t < q₀`) and margin `decLowOK?` (implies `t < 2^51`); under BEHZ
    only at `ℓ = 1`.

  Otherwise the certificate is withheld:
  - NOT CERTIFIED when an output's routine applies but its side condition or margin fails. The
    margins are needed: the locked statements `margin_needed` and `behzMargin_needed` exhibit, for a
    conforming arithmetic, phases inside the textbook threshold that the transcribed routines do not
    decrypt correctly, so the tool certifies the library's decryption only inside the margin.
  - UNSUPPORTED when no proved routine applies: a BEHZ output with `1 < ℓ < L` limbs (the library
    reads an empty table there), and a file that declares no library technique.
  An earlier untrusted guard (`FHE.Check.BFV.libDecryptBound`, the `2^53` magnitude of the
  full-limb routine's sum) still runs before it and prints a NOTE with less
  than one bit to spare. Tests: `tests/negative-bfv/bfv_libdecrypt_*.json`,
  `bfv_hps_libdecrypt_margin_*.json`, `bfv_f1_compress_t2pow54.json`, `bfv_behz_modswitch_level2.json` (UNSUPPORTED), `bfv_ok_behz_modswitch_level1.json` (CERTIFIED).
- **The verdict line names what the frontend declared** that changes the budget: the technique,
  `floatTolerant` and the internal drops. With `floatTolerant: false` (extractor `--idealised`) the
  certificate records `idealised` and the verdict reads "NOT CERTIFIED FOR THE LIBRARY (idealised
  algorithm certified)", with the reason that the budget is that of the idealised exact algorithm,
  not of the library's binary64 code.

Hand-written examples: `examples/bfv_tiny_*.fhecheck.json` mirror `tinyBFV` (their bounds equal
the locked `#guard` values of `Challenge/BFV.lean`). Every other BFV example is a real OpenFHE
v1.6.1 run ("BFV extraction"); SEAL is out of scope and has no examples.
<!-- END BFV -->

<!-- BEGIN BFV EXTRACTION -->
## BFV extraction (OpenFHE v1.6.1)

Usage only; what the checker does with the file is the section above. Everything here is
UNTRUSTED. The library is the same traced upstream OpenFHE v1.6.1 as for BGV ("I have an OpenFHE
program", "Tracer patch"); file:line references are to pristine v1.6.1 (b59e1f29).

```
openfhe/build_openfhe.sh [WORKDIR]       # also builds WORKDIR/bfv_demo (default WORKDIR harness/build/frontend-openfhe)
B=../build/frontend-openfhe/bfv_demo
OMP_NUM_THREADS=1 $B run DIR [--mult HPS|HPSPOVERQ|HPSPOVERQLEVELED|BEHZ|default] [--ks HYBRID|BV|default]
           [--enc STANDARD|EXTENDED|default] [--depth D] [--progdepth K] [--t T] [--n N] [--qbits B]
           [--dnum K] [--digitsize W] [--prog chain|dot|rot|plain|rotsum|norelin|neg|compress|coefpk]
        # writes DIR/params.json, trace.jsonl, values.json, cc.json, check.txt
$B dump cc.json > params.json            # the same params.json for a context you serialized yourself
python3 -I openfhe/extract_bfv.py --params DIR/params.json --trace DIR/trace.jsonl > prog.fhecheck.json
python3 -I openfhe/value_check_bfv.py prog.fhecheck.json DIR/values.json
fhe_check prog.fhecheck.json
```

For your own program: run it unmodified with `FHECHECK_TRACE_DIR=out OMP_NUM_THREADS=1` (every
BFVRNS context writes `out/p<pid>.ctx<k>.{trace.jsonl,params.json}`), or install a
`fhecheck::JsonTracer` with `setTracer` before `KeyGen` as `bfv_demo.cpp` does. `default` means the
setter is never called: OpenFHE v1.6.1's BFVRNS defaults are HPSPOVERQLEVELED
(`gen-cryptocontext-params-defaults.h:111`), BV key switching (`:99`) with digit size 0 (`:95`),
STANDARD encryption (`:110`) and 60-bit primes (`:105`).

`extract_bfv.py` shares with `extract.py` (imports it): the trace reader (tracer error events and
truncated traces refused), key provenance ("Key provenance": one single-party `KeyGen` secret;
every relinearization key from `EvalMultKeyGen` and every rotation key generated for the index it
is used for; multiparty / PRE / key-switching / sparse-key calls refused; `--assume-single-party-keys`),
the build-flag refusals (`WITH_REDUCED_NOISE`, `NATIVEINT` ≠ 64, no `HAVE_INT128`; a `params.json`
without the `build` section is refused unless `--assume-default-build`), and the refusal by name of
`EvalSum`/`EvalInnerProduct` (fused radix fold in v1.6), `EvalFastRotation` and the `*Mutable`
products. BFV-specific refusals: `Encrypt` with the private key, plaintexts that are neither packed
nor CoefPacked with `scalingFactorInt` = 1 (see "CoefPacked plaintexts" below),
a plaintext with fewer limbs than the ciphertext, `EvalMultNoRelinNoCheck` (the componentwise
product, without BFV's scaling by t/Q), a relinearization of more than 3 parts (OpenFHE
key-switches only `cv[2]` and drops the rest), a GAUSSIAN secret (SPARSE_TERNARY is accepted with
|s| ≤ 1, as for BGV), `noiseScale` ≠ 1, threshold contexts, σ ≥ 300, BV with a digit size, and a
`FindLevelsToDrop` table that disagrees with the replica or with the drop the library recorded.
**Unrelinearised products.** The output of a BFV product without a key (`EvalMultNoRelin`, or the
`EvalMult`/`EvalSquare` call inside a relinearizing one) may only be added to or subtracted from
another such value, negated, or relinearized; any other use (combining it with an ordinary
ciphertext or a plaintext, multiplying, rotating or compressing it) is refused (the
`PRODUCT_RULE` comment in `extract_bfv.py`; `tests/refused-bfv/mixadd_*`). The rule admits only
combinations that were run on OpenFHE v1.6.1 and passed the trusted step contracts in
`harness/openfhe-pin/`.
Regression tests: `tests/keyprov/expected-bfv.tsv`, `tests/refused-bfv/`, run.sh 9g, 9g2.

**CoefPacked plaintexts** (`MakeCoefPackedPlaintext`) are accepted for BFV, as encrypted
plaintexts and as operands of `EvalMult`/`EvalAdd`/`EvalSub`, with the same declarations as packed
ones (`bound: t − 1`, encoding deviation `⌈(Q mod t)·m/t⌉`). Reason: for BFVRNS, OpenFHE v1.6.1
stores a value `v ∈ (−t/2, t/2]` as `v` if `v ≥ 0` and as `t − |v|` if `v < 0`
(`pke/lib/encoding/coefpackedencoding.cpp:46-70`, the `isBFVRNS` branch `:58-61`; other values
throw, `:53-55`), the same integer in `[0, t)` in every limb, then multiplies by
`scalingFactorInt` (`:77-90`), which no BFV code sets; the extractor requires the trace to record
`sf = 1` for the plaintext and refuses otherwise. The trusted contract needs no more than this:
a plaintext operand is any polynomial congruent to the message mod `t` within its declared bound
(`Spec.TraceBFV.PlainOK`), and an encryption is charged the deviation of `TimesQovert` on the
stored polynomial. The extracted file names the CoefPacked plaintexts in
`noiseDerivation.coefPackedPlaintexts` (files of packed-only programs are unchanged). This is the
BFV branch only: under BGV a negative value is stored as `q − |v|` and FLEXIBLEAUTO(EXT) scales
without reduction mod `t`, so `extract.py` still refuses CoefPacked (`tests/refused/coefpk_*`).
Tests: `bfv_demo --prog coefpk` (negative coefficients and the extremes `±t/2`: stored values
`≥ t/2`), value-checked against OpenFHE's decryption in `tests/values-bfv/*coefpk*` (five runs:
every technique, BV) and `examples/openfhe_bfv_*coefpk*`; run.sh 9g2
(stored coefficients in `[0, t)`, observed fresh noise within `inputNoise`, the same program as
the trace relabelled packed, refusals for `sf ≠ 1`, an unrecorded `sf`, another or an unrecorded
encoding). Found by the evaluation `harness/eval/cks26` (the attack code of Choe-Kang-Stehlé uses
CoefPacked throughout).

What `extract_bfv.py` declares, each with file:line citations in the emitted `source` strings:

| field | OpenFHE v1.6.1 | value |
|---|---|---|
| `params.limbs`, `special` | `GetElementParams`, `GetParamsP` | the primes of `Q`; `P` for HYBRID, `[]` for BV |
| `params.inputNoise` | `PKEBFVRNS::Encrypt` with a public key (`bfvrns-pke.cpp:167-223`) | STANDARD: `Be·(1 + 2N) + ⌈(Q mod t)(t−1)/t⌉`, `Be = 39` (DGG cut at `⌈3.19·12.006⌉`), printed only: fhe_check recomputes it from `freshEncryption` in Lean (`Spec.EncryptBFV.freshInputNoise`). The second term is the encoding: `TimesQovert` (`dcrtpoly-impl.h:918-935`) computes **`⌈Q·m/t⌉`** for the stored `m ∈ [0, t)`, not `⌊Q/t⌋·m`. EXTENDED: refused (the trusted model `Spec.EncryptBFV` is STANDARD only) |
| `freshEncryption` | the traced public-key encryptions | `inputs` = every two-component input; `keyError = e1 = e2 = Be`, `u = 1`; `mean` = `3431/2^64` for `σ = 3.19f` (as for BGV) |
| `params.keyNoise` | key-switching keys, noise scale 1 | `Be` |
| plaintext inputs | packed encoding, or CoefPacked with `scalingFactorInt` = 1: stored in `[0, t)` | `parts: 1`, `bound: t − 1` |
| `keySwitching` | HYBRID | as for BGV (`variant: "openfhe"`, consecutive digits); ModDown without the `t`-correction |
| | BV, digit size 0 | modelled as hybrid with `special: []`, one limb per digit, `variant: "centred"` (the digit of limb `i` is the centred `[c]_{q_i}`); any other digit size is an extraction error |
| `bfv.multiplication` | `GetParamsRl`, `GetModuliBsk` | `auxBasis` = all primes of `R` in the library's order (HPS: `L+1`; P-over-Q: `L`, a product on `k` limbs uses the first `k`); BEHZ: `B`, `mSk`, `mTilde = 2^16`; `floatTolerant: true` for the HPS family |
| `internalDrops` (and the cross-check maxima `maxInternalDrop`, `maxInternalDropKS`) | `FindLevelsToDrop` (HPSPOVERQLEVELED, `bfvrns-leveledshe.cpp:98-198`) | one entry per instruction of `program.body` (0 where the library drops nothing; equal to `provenance[].internalDrop`); the maxima over the traced products/relinearizations, resp. rotation key switches. The values are the library's own function called on the context (`params.json: levelsToDrop`); they must agree with a Python replica AND with the drop each `EvalMult`/`EvalSquare`/`RelinearizeCore` recorded at run time (`levelsDropped` hook), or the extraction fails |
| `bfv.plainAdd` | `EvalAdd/EvalSub(ct, pt)` use `TimesQovert` (`bfvrns-leveledshe.cpp:56-96`) | `method: "ceil"` (`⌈Q·p/t⌉`: not `"rounded"`, whose budget is one unit too small whenever frac(`(Q mod t)·p/t`) < 1/2), emitted only if the program adds or subtracts a plaintext; always described in `noiseDerivation.plainAdd` |
| `modSwitch` | `Compress` (`bfvrns-leveledshe.cpp:902-932`) | `round`, one `modSwitch` per dropped limb |
| `decryption` | `PKEBFVRNS::Decrypt` (`bfvrns-pke.cpp:225-278`) | `at-output-level`; the `source` string says how the library's RNS/float decryption and its handling of compressed ciphertexts differ from exact rounding |

Instruction mapping: `EvalMult`/`EvalMultNoRelin` → `mul`; `EvalSquare` → `square` under HPS and
BEHZ, **`mul a a` under the P-over-Q techniques** (the library lifts the operand in two different
ways there, `bfvrns-leveledshe.cpp:459-524,626-636`); the relinearization inside
`EvalMult`/`EvalSquare` and `Relinearize` → `relin`; `EvalRotate`/`EvalAtIndex`/`EvalAutomorphism`
→ `automorph; keySwitch`; `EvalNegate` → `mulConst −1`; `EvalAdd/Sub` → `add`/`sub` or
`addPlain`/`subPlain`; `EvalMult(ct, pt)` → `mulPlain`; `Compress` → `modSwitch`. Anything else
that changes a ciphertext makes the extraction fail with an error document.

`extract_bfv.py --idealised` emits the same file with `floatTolerant: false` for the HPS family:
the idealised exact algorithm. It is **not** a description of the library (whose binary64 sums
differ from exact arithmetic) and exists to show the two budgets side by side. The file says
`source.idealised: true`, and `fhe_check` never prints the plain headline for it: the verdict
reads `NOT CERTIFIED FOR THE LIBRARY (idealised algorithm certified)` followed by the reason
(the file declares the exact algorithm, not the library's binary64 one).

Scripts: `openfhe/make_examples_bfv.sh` regenerates `examples/openfhe_bfv_*` (every technique ×
{HYBRID, BV} at depth 1 and 2, programs with rotations, plaintext operations, `Compress`, and two runs at ring dimension 1024, see below), the `N = 16` value fixtures
`tests/values-bfv/` and the refusal fixtures `tests/refused-bfv/` (among them three EXTENDED-encryption runs: refused, the trusted model `Spec.EncryptBFV` is STANDARD only). `value_check_bfv.py` evaluates
the extracted program on the recorded plaintexts (BFV message semantics: a modulus switch keeps
the message) and compares with the library's raw decryption; it also checks that every observed
fresh noise is within `inputNoise` and reports a mismatch with the library's decryption as such (exit 3).

### What a default OpenFHE BFV user sees

`openfhe/default_table_bfv.sh [OUTDIR]` (several minutes): the chain program of depth D (one
product, D−1 squarings, each relinearized) on `CCParams<CryptoContextBFVRNS>` with only
`t = 65537` and the multiplicative depth D set (so HPSPOVERQLEVELED, 60-bit primes,
HEStd_128_classic; BV unless HYBRID is asked for), and the same with `--mult BEHZ`. Worst-case
verdicts of `fhe_check`; "margin" for a NOT CERTIFIED row is the overflow at the first failing
instruction; "observed" is the output noise of that one run and "limit" the largest noise that
decrypts (bits). In every row the library's own decryption was correct. The last column is the
first of a fixed list of real variants (HYBRID instead of BV, parameters generated for depth
D+1, BEHZ, HPS, …; the script lists them) that is CERTIFIED. OpenFHE v1.6.1.

Default technique (HPSPOVERQLEVELED), regenerated 2026-11-14 with the per-instruction certificate
(`default_table_bfv.sh`, `bfv_demo` of OpenFHE v1.6.1). Every slack is PROVED (the rows are what the
library runs, `floatTolerant: true`, under the standard model of binary64); the key switch after an
internal drop is proved too:

| D | key switching | N | log2 Q | verdict | bound | margin | `--idealised` (not the library) | observed / limit | smallest certified variant |
|---|---|---|---|---|---|---|---|---|---|
| 1 | BV | 8192 | 120 | CERTIFIED | 78.29 | 24.71 | CERTIFIED, margin 24.71 | 67.3 / 103 |  |
| 1 | HYBRID | 16384 | 120 | CERTIFIED | 64.44 | 38.56 | CERTIFIED, margin 38.56 | 39.6 / 103 |  |
| 2 | BV | 8192 | 180 | CERTIFIED | 138.29 | 24.71 | CERTIFIED, margin 24.71 | 127.3 / 163 |  |
| 2 | HYBRID | 16384 | 120 | NOT CERTIFIED | 108.44 at body[2] | −5.44 | NOT CERTIFIED, −5.44 | 69.3 / 103 | one more limb: N = 16384, 3 limbs, margin 54.55 |
| 3 | BV | 8192 | 180 | NOT CERTIFIED | 180.29 at body[4] | −17.29 | NOT CERTIFIED, −17.29 | 155.3 / 163 | HYBRID instead of BV: N = 16384, 3 limbs, margin 10.55 |
| 3 | HYBRID | 16384 | 180 | CERTIFIED | 152.45 | 10.55 | CERTIFIED, margin 10.55 | 99.2 / 163 |  |
| 4 | BV | 16384 | 240 | NOT CERTIFIED | 227.87 at body[6] | −4.87 | NOT CERTIFIED, −4.87 | 187.7 / 223 | BEHZ: N = 16384, 4 limbs, margin 10.71 |
| 4 | HYBRID | 16384 | 180 | NOT CERTIFIED | 196.45 at body[6] | −33.45 | NOT CERTIFIED, −33.45 | 128.8 / 163 | one more limb: N = 16384, 4 limbs, margin 26.64 |
| 5 | BV | 16384 | 240 | NOT CERTIFIED | 227.87 at body[6] | −4.87 | NOT CERTIFIED, −4.87 | 217.0 / 223 | one more limb: N = 16384, 5 limbs, margin 10.71 |
| 5 | HYBRID | 16384 | 240 | NOT CERTIFIED | 240.36 at body[8] | −17.36 | NOT CERTIFIED, −17.36 | 159.0 / 223 | BEHZ + 2 more limb(s): N = 32768, 5 limbs, margin 31.67 |
| 6 | BV | 16384 | 300 | NOT CERTIFIED | 316.29 at body[10] | −33.29 | NOT CERTIFIED, −33.29 | 247.9 / 283 | BEHZ + 2 more limb(s): N = 16384, 6 limbs, margin 42.13 |
| 6 | HYBRID | 16384 | 240 | NOT CERTIFIED | 240.36 at body[8] | −17.36 | NOT CERTIFIED, −17.36 | 190.3 / 223 | BEHZ + 2 more limb(s): N = 32768, 6 limbs, margin 45.68 |

Each failure is at a product (`body[2k]`), after a relinearization at which the library dropped a
limb internally: that relinearization is charged `ksLeveled` (about `Q_L/Q_(L−1)` times a fresh
key-switching error) and the next product multiplies it by about 2^42..2^46 (`N·(t·(K+1)+t−1)`,
see `levelbfv/depth_table.md`). The multiplications themselves are charged only their own slack:
a product at which the library drops nothing no longer pays for a drop elsewhere. NOT CERTIFIED is not a statement that decryption fails.

The same program with `--mult BEHZ` (integer-only; slacks PROVED in every row):

| D | key switching | N | log2 Q | verdict | bound | margin | observed / limit | smallest certified variant |
|---|---|---|---|---|---|---|---|---|
| 1 | BV | 8192 | 120 | CERTIFIED | 78.29 | 24.71 | 67.2 / 103 |  |
| 1 | HYBRID | 16384 | 120 | CERTIFIED | 64.41 | 38.59 | 39.5 / 103 |  |
| 2 | BV | 8192 | 180 | CERTIFIED | 120.87 | 42.13 | 95.4 / 163 |  |
| 2 | HYBRID | 16384 | 120 | NOT CERTIFIED | 108.41 at body[2] | −5.41 | 69.2 / 103 | one more limb: N = 16384, 3 limbs, margin 54.60 |
| 3 | BV | 8192 | 180 | CERTIFIED | 162.87 | 0.13 | 123.8 / 163 |  |
| 3 | HYBRID | 16384 | 180 | CERTIFIED | 152.40 | 10.60 | 99.1 / 163 |  |
| 4 | BV | 16384 | 240 | CERTIFIED | 212.29 | 10.71 | 156.1 / 223 |  |
| 4 | HYBRID | 16384 | 180 | NOT CERTIFIED | 196.40 at body[6] | −33.40 | 128.6 / 163 | one more limb: N = 16384, 4 limbs, margin 26.71 |
| 5 | BV | 16384 | 240 | NOT CERTIFIED | 256.29 at body[8] | −33.29 | 186.0 / 223 | one more limb: N = 16384, 5 limbs, margin 26.39 |
| 5 | HYBRID | 16384 | 240 | NOT CERTIFIED | 240.29 at body[8] | −17.29 | 158.8 / 223 | BEHZ + 2 more limb(s): N = 32768, 5 limbs, margin 31.67 |
| 6 | BV | 16384 | 300 | NOT CERTIFIED | 300.61 at body[10] | −17.61 | 216.0 / 283 | BEHZ + 2 more limb(s): N = 16384, 6 limbs, margin 42.13 |
| 6 | HYBRID | 16384 | 240 | NOT CERTIFIED | 240.29 at body[8] | −17.29 | 189.3 / 223 | BEHZ + 2 more limb(s): N = 32768, 6 limbs, margin 45.68 |

The release bar tested in `tests/run.sh` (section 9h): for BEHZ, on real OpenFHE runs with HYBRID
and with BV, the extracted program is CERTIFIED with the library's BEHZ decryption proved
("Library decryption: PROVED", `Spec/DecryptBFVBEHZ.lean`), the report names `stepOK_mul_behz` with
`budget.slacksProved = true`, and the value cross-check against OpenFHE's own decryption passes
on the same run.

**At insecure parameters.** With the ring dimension forced to 1024
(`SetRingDim(1024)`, `HEStd_NotSet`: not a secure parameter set), depth 2, and OpenFHE's default
technique with BV key switching, the extracted file
`examples/openfhe_bfv_n1024_default_chain_d2` is NOT CERTIFIED (overflow 8.29 bits at the second
product), and a test requires that it never be CERTIFIED. The same parameters with
HYBRID are CERTIFIED (`openfhe_bfv_n1024_hybrid_chain_d2`, margin 13.82).
<!-- END BFV EXTRACTION -->

## Tests (`tests/`)

```
harness/frontend/tests/run.sh    # uses .lake/build/bin/fhe_check; FHE_CHECK=PATH overrides (relative paths work)
                                 # --update rewrites goldens; --live also re-runs OpenFHE (needs build_openfhe.sh)
harness/frontend/difftest.sh     # the same, as gate step 6
```

`scripts/check-spec.sh` runs these tests in step 6 through `difftest.sh`, from the committed
fixtures (no OpenFHE or HEIR installation). They test the registered `fhe_check` executable, the
extractors, and (item 6) an untrusted Python mirror of `Source.step` against recorded OpenFHE
runs. They are not a pin of the Lean definitions in `Spec/`.

1. The extractors reproduce the committed `.fhecheck.json` files byte for byte from the
   committed traces and MLIR.
2. `expected.tsv` fixes the verdict, exit code and a key figure for every example and for 43
   negative or edge cases; `expected-kappa.tsv` does the same for `--kappa` runs (certified at
   128/64/40, not certified, fallback to worst case for an absurd K, no `freshEncryption`
   section, an input that is not fresh, the declared and the assumed plaintext bound and sampler
   mean), plus monotonicity in K on every OpenFHE example, K = 0
   and absurd K as usage errors, and the warning below K = 40. `expected-redteam.tsv` holds the
   witnesses of the adversarial review (`tests/redteam/`), each run under a
   timeout: an output under a rotated key, a fresh input with a declared bound, a non-fresh
   2-part input, an empty fresh list, a frontend `inputNoise` below the verified worst case,
   duplicate names, and inputs that hung or would crash the parser (`1e400000`, deep nesting, a
   5000-digit number). Every example, negative and witness must also finish within 60 s in both
   modes. `make_negatives.py` generates the cases:
   - composite modulus, duplicate prime, t not coprime, N not a power of two, inputNoise < t/2;
   - special prime not coprime;
   - input above the chain, undefined operand or output, relin of 2 parts;
   - a noise overflow;
   - the frontend's `expect` disagreeing with the verified semantics;
   - a 3-part modSwitch (CERTIFIED at `msBudgetAt P 3` = 2^43.00; it was UNSUPPORTED before
     `Challenge.Budget.modSwitch_realizable_parts`), rescale, an unknown op, CKKS, unknown
     key-switch variant, modulus-switch method or decryption method;
   - the ℓ₂ mode (`l2_supplied`, `l2_malformed`; run.sh section 2e): values computed from the
     support bounds give the support model's ε; supplied values give a smaller ε and are named
     as assumptions; NOT CERTIFIED on an automatic-mode chain; a malformed field, no
     `freshEncryption`, and `--l2` without `--kappa` are refused;
   - a 1-part modSwitch (certified, charged ⌈t/2⌉); an output that fits Q/2 at its level but
     whose switched phase does not fit q₀/2 (NOT CERTIFIED), and the same file with textbook
     decryption declared (CERTIFIED);
   - a non-partitioning digit layout; an explicit digit table that restricts from the top level
     (same answer as the consecutive layout it equals) and one that does not (UNSUPPORTED);
   - a non-centred modulus-switching method on a program without any modulus switch
     (UNSUPPORTED); an even special modulus on a program without key switching (NOT CERTIFIED);
     the smallest key noise that fails `keysRestrict?` (NOT CERTIFIED) and that value minus one
     (CERTIFIED);
   - `freshEncryption.plaintextBound` = 2^33 and 2^34 on the depth-2 example (with `--kappa 128`:
     CERTIFIED with 1.70 bits instead of 6.47, and NOT CERTIFIED, over by 0.88 bits);
     `freshEncryption.mean` with denominator 0 (INVALID INPUT);
   - malformed JSON, a malformed big integer, a missing field, a v0 file, an extraction error;
   - plaintext ops (certified), a 2-part "plaintext", dropping every limb;
   - the sample parameters `exampleBGV31`, which show the budget's dependence on the digit layout:
     - with one limb per digit, ksBudget = 34787976413 (2^35.02) and `mul; relin` is CERTIFIED
       with 3.00 bits of margin;
     - with a single two-limb digit, ksBudget = 2^65.00, above Q, so the same program is NOT
       CERTIFIED. The special modulus must be about as large as the largest digit.
3. Golden human and `--json` outputs for all of them (`golden/`), and for every OpenFHE example
   with `--kappa 128` (`golden/*.kappa128.*`).
4. Agreement with `preview_check.py`, the independent Python mirror. Every verdict difference is
   listed with its reason in `compare_preview.py`. All of them are cases the preview does not
   check (parameter clauses, `SpecialOK`, input declarations, format, method fields) or crashes
   on. The preview also has the plaintext operations, declared bounds, the 1-part budget and the
   switched-decryption bound (worst-case mode only). On
   every other real example the two agree, including every bound and budget to two decimals.
5. The certificate text names the theorems, says which decryption is covered and keeps the "not
   verified" disclaimers; the `--kappa` certificate contains the fixed wording verbatim; a
   worst-case report makes no probabilistic claim; suggestions are marked as non-theorems.
6. OpenFHE value cross-check. `tests/values/` holds 44 small-ring runs on OpenFHE v1.6.1 (N = 1024,
   HEStd_NotSet, not secure): 11 programs × 4 scaling techniques, with `params.json`, `trace.jsonl` and
   `values.json`. For each run:
   - the extraction must succeed with no scale or level mismatch;
   - `openfhe/value_check.py` must reproduce OpenFHE's raw decryption in every coefficient.
   The step also tests the checks themselves:
   - four mutants of one program (constant, rotation index, a dropped modSwitch, sub→add) must
     all be caught;
   - a trace with its `Encrypt` calls removed must be an extraction error, and
     `--assume-fresh-inputs` must not apply to its input first used after the first operation.
   6b. Key provenance and refusals (`tests/keyprov/check.py`): the threshold witness and the
   mutated traces of "Key provenance" must be refused with the expected message, as must a
   `params.json` with σ other than 3.19 (the declared sampler mean is for 3.19 only) (and extracted
   with `--assume-single-party-keys` where the key generation is missing); `tests/refused/*` must
   be refused with the recorded message; and `run.sh` must resolve a relative `FHE_CHECK`.
   6c. What is certified is what is decrypted (`tests/tamper/check.py`, "What the frontend
   assumes"): the real runs of `tests/tamper/` (`openfhe/tamper_demo.cpp`, recorded by
   `openfhe/make_tamper.sh`: `EvalMultNoCheck`, `EvalAddInPlaceNoCheck`, `GetElements()`, `SetLevel`
   before `Decrypt`; an intermediate changed in place; a plaintext element changed after encoding;
   a plaintext of another context; a relinearization key changed with `SetBVector`; a parameter
   setter after registration) must be refused, both schemes, and the honest run extracted with its
   decrypted ciphertext as an output; trace mutations of the examples (a `Decrypt` of an unknown
   ciphertext, `--outputs` omitting a decrypted one, `--assume-fresh-inputs` mid-program or with
   a traced `Encrypt` in the trace and its positive case, a plaintext with no traced `Make*` or another `t`)
   likewise; `fhe_check` answers INVALID INPUT on unknown fields and labels an `--idealised` file
   IDEALISED; `extract_bfv.py` refuses σ ≠ 3.19; `extract.py` refuses a FIXEDMANUAL/FIXEDAUTO context whose
   primes are not 1 mod t (the extractor refuses such a context); `tests/tamper/sha256_test.py` checks the tracer's SHA-256 against hashlib.
7. `fhe_check recommend` (`tests/recommend/`): golden human and `--json` outputs for every
   example; when a recommendation is found, the emitted file is CERTIFIED by a plain `fhe_check`
   run and carries exactly the reported primes (when none is found, nothing is emitted); the prime
   mirror (`--sizes`) reproduces the primes of all 12 committed OpenFHE FIXEDMANUAL and HEIR
   examples; `expected.tsv` holds the negative and option cases (no parameters at a fixed N within
   the cap and the smallest feasible N, automatic-mode files, N fixed by a file without
   `freshEncryption`, bad options, a t the OpenFHE rule cannot serve, a t that is itself a
   candidate prime, `--kappa`, `--security`, `--digits any`, `--margin`, rotations moved to another N).
8. `--live` (needs `bgv_demo` from `openfhe/build_openfhe.sh`): re-runs OpenFHE v1.6.1 through `openfhe/make_examples.sh`, value-checks
   every run, and requires the re-extracted examples to equal the committed ones byte for byte.
9. BFV (section 9; files with `params.scheme = "BFV"`, skipped by the BGV-only steps): the tracer
   patch carries the current `fhecheck-tracer.h`;
   `extract_bfv.py` reproduces every `examples/openfhe_bfv_*` file from its committed trace; every
   extracted file has the neutral BFV shape; OpenFHE's own `FindLevelsToDrop` table agrees with the
   two Python replicas; `expected-bfv.tsv` fixes the verdict, exit code and key figure of every BFV
   example and of the negatives `tests/negative-bfv/` (`make_negatives_bfv.py`, mutations of the
   v1.6.1 examples; among them the textbook technique on a squaring chain, certified, and the
   same with two more squarings, `bfv_textbook_squarings_overflow`, NOT CERTIFIED), with goldens; the value cross-check passes on the 49 `N = 16` runs of
   `tests/values-bfv/` and catches mutants; the extractor refuses mutated inputs (unknown
   operations, a missing or different recorded internal drop, a replica mismatch, tracer errors,
   truncation, ...); the BEHZ release bar (9h); `--idealised` changes only `floatTolerant`. Key
   provenance, build flags, parameter mutations and the refusal fixtures `tests/refused-bfv/`
   (EvalInnerProduct, private-key Encrypt, a 3-part relinearization,
   EvalMultNoRelinNoCheck) are checked in 6b (`tests/keyprov/expected-bfv.tsv`); CoefPacked
   plaintexts under BFV (accepted; refusals for a scaling factor other than 1 or another
   encoding) in 9g2.

## Files

- `openfhe/`:
  - `openfhe-v1.6.1-tracer.patch`, `fhecheck-tracer.h`, `build_openfhe.sh`: the traced OpenFHE
    v1.6.1 (see "Tracer patch"); `patch_residue.py` shows what the patch changes besides hooks;
  - `bgv_demo.cpp` with `build.sh`: demo programs under every scaling technique, and `dump`;
  - `extract.py`: trace → v1, with key provenance, the scale/level cross-check, the decryption
    declaration and the fresh-encryption model;
  - `default_table.sh`: regenerates the "default user" table;
  - `value_check.py`: the untrusted message-level evaluator for the value cross-check;
  - `make_examples.sh`: regenerates the OpenFHE examples, `tests/values/` and `tests/refused/`;
  - BFV: `bfv_demo.cpp` with `build_bfv.sh`; `extract_bfv.py` (shares the trace reader, key
    provenance, build-flag and encoding checks of `extract.py`); `value_check_bfv.py`;
    `make_examples_bfv.sh` (examples, `tests/values-bfv/`, `tests/refused-bfv/`);
    `default_table_bfv.sh` (the BFV "default user" table).
- `heir/extract_bgv.py`: bgv-dialect MLIR (Lattigo path) → v1.
- `recommend/roundtrip.sh` (`roundtrip.py`): the round trip of `fhe_check recommend` through
  OpenFHE and HEIR/Lattigo, with timings; `--table roundtrip.json` prints the README tables.
- `preview_check.py`: the untrusted mirror, used only by the tests.
- `tests/keyprov/`: key-provenance red-team traces (`mutate.py`, `check.py`, `expected.tsv`);
  `tests/refused/`: traces the extractor must refuse, with the message.
- `lean/Timing.lean`: an early timing probe, superseded by `fhe_check --time`.
