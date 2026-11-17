# Quickstart: `fhe_check` on your own program

`fhe_check` answers, for a BGV or BFV program and its parameters, whether every output is
guaranteed to decrypt correctly in the worst case. A CERTIFIED verdict instantiates a
machine-checked Lean theorem; NOT CERTIFIED and UNSUPPORTED come with the reason and, where one
exists, a suggested fix. The check is a static analysis of the noise bounds: it runs no
encryption, and its running time does not depend on the ring dimension (a program at N = 2^16 is
checked as fast as the same program at N = 2^10).

There are three ways in. Each was tested from a clean environment (section "How these paths were
tested"). Section 4 checks a program against a budget you declare for your own implementation
(tested in the repository's suite, not from a clean environment).

| path | you need | time to the first verdict |
|---|---|---|
| 1. no library | Linux or macOS, git, elan (the pinned Lean toolchain) | build from source: 2 min 23 s for the build itself, measured on a quiet 128-core server (see below). Optional: a prebuilt Linux x86-64 executable attached to releases, under 2 minutes (download, unpack, run) |
| 2. your OpenFHE program | the repository, git, a C++17 compiler, python3 | 6 min 23 s from nothing on a loaded 128-core server (most of it building OpenFHE once, on all cores); 25 to 28 s per program afterwards; not measured on a laptop, where building OpenFHE takes much longer |
| 3. a HEIR program | the repository, python3, curl | under 10 s from nothing (3 to 4 s of it downloading HEIR's `heir-opt`) |

## 1. No library: build from source (or the optional prebuilt executable)

**Build it from source (the way to run it).** Install [elan](https://github.com/leanprover/elan),
clone the repository, and in it run `lake exe cache get && lake build fhe_check` (the toolchain and
Mathlib are pinned by `lean-toolchain` and `lake-manifest.json`; `lake exe cache get` downloads
Mathlib's prebuilt modules). The executable is `.lake/build/bin/fhe_check`; the examples in
`harness/frontend/examples/` run with it directly (`harness/quickstart/run-examples.sh` shows the
three used below). Measured: `lake build fhe_check` took 2 min 23 s (6,638 build jobs) from a clean clone on a 128-core server at a load of about 2 (otherwise idle), with Mathlib's prebuilt modules already in `.lake/packages` (copied from another checkout; `lake exe cache get` then found nothing to download and took 10 s); the one-time download of that cache and of the toolchain is not included, and no laptop was measured.

**The prebuilt executable (an optional convenience, never committed to the repository).** A
Linux x86-64 executable is attached to each release. Release executables are built by CI from the
tagged commit (`.github/workflows/release.yml`), with a build provenance attestation and SHA-256
checksums; check the checksum, and the attestation with `gh attestation verify`, before running it.

Download `fhe_check-linux-x86_64.tar.gz` (34 MB; `.tar.xz`, 20 MB, if your system has `xz`) and its
`.sha256` file from the release (tag `v0.1.0` on this repository's Releases page), verify
the checksum, then:

```
tar xzf fhe_check-linux-x86_64.tar.gz
cd fhe_check-linux-x86_64
./run-examples.sh
```

`run-examples.sh` checks the three shipped examples, OpenFHE programs extracted by the frontend:
a BGV program that is certified, a BFV program that is certified, and a BGV program (OpenFHE's
FIXEDMANUAL parameters at depth 2) that is refused, with the smallest change that would certify it
and the parameters `fhe_check recommend` finds for it, re-checked:

```
$ ./run-examples.sh
bgv_certified (exit 0): VERDICT: CERTIFIED: every output decrypts correctly, in the worst case, under the assumptions below
bfv_certified (exit 0): VERDICT: CERTIFIED (binary64 steps of OpenFHE's HPSPOVERQLEVELED under the standard model [...]
bgv_refused (exit 1): VERDICT: NOT CERTIFIED: the worst-case noise bound overflows at body[3]

bgv_refused: the smallest change, and parameters that certify (fhe_check recommend):
SUGGESTIONS (smallest change that would certify, found by running the verified analyzer on
hypothetical inputs; NOT a theorem, not proved minimal; re-check on the real regenerated input):
  - probabilistic fresh noise: `fhe_check --kappa K` certifies this same program and parameters for K = 512 [...]
  - larger moduli: with every ciphertext and special modulus 3 bit(s) larger [...]

RECOMMENDATION: CERTIFIED: parameters found that fhe_check certifies (minimum margin 0.43 bits)
  CCParams<CryptoContextBGVRNS> parameters;
  parameters.SetPlaintextModulus(65537);
  parameters.SetMultiplicativeDepth(2);   // a chain of 3 primes (gen-cryptocontext-bgvrns-internal.h:102)
  parameters.SetScalingTechnique(FIXEDMANUAL);
  parameters.SetFirstModSize(36);
  parameters.SetScalingModSize(51);
  parameters.SetNumLargeDigits(2);
  parameters.SetKeySwitchTechnique(HYBRID);
  parameters.SetSecurityLevel(HEStd_128_classic);   // OpenFHE re-checks N against its own table
  parameters.SetRingDim(16384);
  CryptoContext<DCRTPoly> cc = GenCryptoContext(parameters);

re-check of the recommended parameters (examples/bgv_fixed.fhecheck.json):
VERDICT: CERTIFIED: every output decrypts correctly, in the worst case, under the assumptions below
```

Each example by hand, and the options you will use most:

```
./fhe_check examples/bgv_refused.fhecheck.json           # the full report: bounds, the failing step, suggestions
./fhe_check --kappa 128 examples/bgv_refused.fhecheck.json   # fresh-encryption noise with failure probability <= 2^-128
./fhe_check --json examples/bgv_certified.fhecheck.json      # machine-readable
./fhe_check recommend --emit fixed.json examples/bgv_refused.fhecheck.json   # certified parameters (BGV)
```

Exit codes: 0 CERTIFIED, 1 NOT CERTIFIED, 2 UNSUPPORTED, 3 INVALID INPUT, 4 usage error.

**What the executable needs.** Linux on x86-64 with glibc 2.17 or later (the C library of every
mainstream distribution since 2014). It is dynamically linked against the C library only (`libc`,
`libm`, `libpthread`, `libdl`, `librt`) and reads no file besides its input. Tested on Ubuntu
14.04 (glibc 2.19) and Ubuntu 24.04 (glibc 2.39). Unpacked: 87 MB (the executable is 91 MB stripped; the archive 34 MB as `.tar.gz`, 20 MB as `.tar.xz`).

**Building the archive yourself**: `harness/quickstart/make_dist.sh` builds `fhe_check` as above
and packs the same archive (see `harness/frontend/README.md`, "Quickstart").

**Writing the input by hand.** The input is the neutral JSON format
`harness/frontend/fhe-check-v1.schema.json` (parameters, the program as a list of instructions,
the outputs); `harness/generic-demo/` has hand-written examples, and
`harness/frontend/README.md` documents every field.

## 2. Your own OpenFHE program

From a clone of this repository, with the `fhe_check` of path 1 (built from source or downloaded) on your `PATH`:

```
export PATH=/path/to/fhe_check-linux-x86_64:$PATH
harness/quickstart/check_openfhe.sh my_program.cpp
```

The script builds the supported OpenFHE (upstream v1.6.1 with an observation-only tracer patch;
once, into `./provenfhe-work/openfhe`), compiles your program against it, runs it with tracing
switched on by an environment variable, extracts every BGV and BFV `CryptoContext` it created, and
prints `fhe_check`'s verdict for each. Arguments after `--` are passed to your program. For
OpenFHE's own `simple-integers-bgvrns.cpp` and `simple-integers.cpp`, unmodified:

```
$ harness/quickstart/check_openfhe.sh simple-integers-bgvrns.cpp
[check_openfhe 0s] cmake >= 3.22 and < 4 with ninja not found: installing them into <home>/provenfhe-work/venv (pip)
[check_openfhe 15s] building the traced OpenFHE v1.6.1 into <home>/provenfhe-work/openfhe (once; log: [...]/build.log)
[check_openfhe 356s] built
[check_openfhe 356s] compiling <home>/simple-integers-bgvrns.cpp
[check_openfhe 380s] running simple-integers-bgvrns  (traced; output in [...]/program.out)
[check_openfhe 382s] p1322.ctx1 (BGV, 20 instructions): VERDICT: NOT CERTIFIED: the worst-case noise bound overflows at body[10]
    full report: <home>/provenfhe-work/runs/simple-integers-bgvrns/p1322.ctx1.report.txt
[check_openfhe 383s] done
$ harness/quickstart/check_openfhe.sh simple-integers.cpp
[check_openfhe 0s] traced OpenFHE v1.6.1: reusing <home>/provenfhe-work/openfhe/install
[check_openfhe 0s] compiling <home>/simple-integers.cpp
[check_openfhe 23s] running simple-integers  (traced; output in [...]/program.out)
[check_openfhe 25s] p1364.ctx1 (BFV, 14 instructions): VERDICT: CERTIFIED (binary64 steps of OpenFHE's HPSPOVERQLEVELED [...]): every output decrypts correctly, by OpenFHE's own decryption and by textbook decryption, in the worst case, with the input noise computed from the key and sampler bounds, under the assumptions below
    full report: <home>/provenfhe-work/runs/simple-integers/p1364.ctx1.report.txt
[check_openfhe 25s] done
```

**What you must change in your program: nothing**, as long as

- the program generates its keys and encrypts its inputs in the same run (the frontend takes
  ciphertext inputs only from traced encryptions, and checks where every key comes from; for keys
  or ciphertexts loaded from files see `--assume-fresh-inputs` and
  `--assume-single-party-keys` in `harness/frontend/openfhe/extract.py`);
- it decrypts the ciphertexts whose correctness you care about (they become the outputs; a
  program that decrypts nothing is checked on the values no later operation consumes);
- it uses BGV or BFV (CKKS and the threshold and proxy re-encryption modes are not checked: the
  script says so).

The script runs your program single-threaded (`OMP_NUM_THREADS=1`). Its prerequisites: git, a C++17
compiler (tested with gcc 13.3), python3, and cmake (at least 3.22, below 4) with ninja; if cmake
or ninja is missing the script installs both into `./provenfhe-work/venv` with pip. `KAPPA=128`
also prints the `--kappa 128` verdict. The report of each context is in
`./provenfhe-work/runs/<program>/`.

## 3. A compiler's output: HEIR

```
harness/quickstart/check_heir.sh prog.mlir
```

`prog.mlir` is either a HEIR input program (it is compiled for BGV on HEIR's Lattigo backend with
HEIR's pinned nightly `heir-opt`, downloaded once and checked against its sha256, with the
worst-case noise model `bgv-noise-by-bound-coeff-worst-case`; give another model as the second
argument) or HEIR's output on that path (as in `harness/frontend/examples/heir_*.lattigo.*.mlir`),
which is used as it is. Then `harness/frontend/heir/extract_bgv.py` and `fhe_check`. For three of
HEIR's examples and one committed HEIR output:

```
$ harness/quickstart/check_heir.sh mult_dep_8.mlir
[check_heir 0s] downloading heir-opt nightly-2026.11.11 (once)
[check_heir 4s] compiling mult_dep_8 with heir-opt (BGV, Lattigo backend, noise model bgv-noise-by-bound-coeff-worst-case)
[check_heir 4s] mult_dep_8 (9 instructions): VERDICT: CERTIFIED AT PHASE LEVEL: the raw (phase-level) decryption of every output is correct, in the worst case, under the assumptions below; user-level decryption depends on the backend and is NOT covered
$ harness/quickstart/check_heir.sh dot_product_8.mlir      # dot_product_8 (14 instructions): CERTIFIED AT PHASE LEVEL, 1 s
$ harness/quickstart/check_heir.sh simple_sum.mlir         # a loop, unrolled: 21 instructions, CERTIFIED AT PHASE LEVEL, 1 s
$ harness/quickstart/check_heir.sh mult_dep_8.mlir bgv-noise-kpz21
[check_heir 1s] mult_dep_8 (9 instructions): VERDICT: NOT CERTIFIED: the worst-case noise bound overflows at body[6]
    parameters that certify: fhe_check recommend [...]/prog.fhecheck.json
$ harness/quickstart/check_heir.sh harness/frontend/examples/heir_cmux.lattigo.worstcase.mlir
[check_heir 0s] heir_cmux.lattigo.worstcase: already HEIR output (bgv dialect, Lattigo backend)
[check_heir 0s] heir_cmux.lattigo.worstcase (6 instructions): VERDICT: CERTIFIED AT PHASE LEVEL: [...]
```

HEIR programs are certified "AT PHASE LEVEL": the raw decryption is proved correct; how the
backend decodes it is not modelled. HEIR's default noise model gives parameters that are usually
NOT CERTIFIED in the worst case (`harness/frontend/README.md`, "Quickstart").

## 4. Declare your own profile (any implementation)

The paths above charge every operation what OpenFHE's own algorithms need. For another library, or
your own implementation, declare the budget each operation meets instead (an *implementation
profile*) and check against it, with no library table involved:

```
fhe_check --emit-profile PROGRAM.fhecheck.json > my.profile.json   # the table mode's budget, to edit
fhe_check --profile my.profile.json PROGRAM.fhecheck.json
```

A worked example, Lattigo's BGV profile on a small program:

```
$ fhe_check --profile harness/frontend/examples/profile/lattigo_small.profile.json \
            harness/frontend/examples/profile/lattigo_small.fhecheck.json
VERDICT: CERTIFIED for every implementation within the declared profile (Challenge.Profile.certifyProfile? accepts at the declared budget); the profile IS covered by the proved algorithm families (COVERAGE below)
```

CERTIFIED means that the locked `Challenge.Profile.certifyProfile?` (BGV) or
`certifyBFVProfile?` (BFV) accepts at your budget: every run in which each operation stays within it
decrypts correctly. Whether any implementation does stay within it is a separate question, which
the report answers for the proved algorithm families (hybrid key switching on a digit layout, the
textbook or approximate multiplication, the rounding/centred modulus switch). A profile they do
not cover is still certified, and the verdict line then says the certificate is conditional.
Format and details: `harness/frontend/README.md`, "Declare your own profile".

## Speed

`fhe_check`'s time grows almost linearly with the program length (local exponent 1.0 to 1.1, measured from 10^4 to 10^7
instructions; `harness/eval/analyzer-speed/RESULTS.md`) and does not depend on the ring dimension.
Wall time on a quiet 128-core server (AMD EPYC 7742, load average below 3; the check itself uses a
few cores at most), median of three runs for 10^4 to 10^6 and one run at 10^7, including reading the
file, on synthetic programs (`harness/eval/analyzer-speed/`): 10^4 instructions in
0.16 to 0.33 s, 10^5 in 1.5 to 3.4 s, 10^6 in 18 to 39 s (1.5 to 2.5 GB of memory); 10^7 in 3.3 to
6.6 minutes (14 to 19 GB). The largest real extracted program (2.18 million instructions, refused
about 1 % in) takes 26 s and 4.6 GB.
Files above 2,000,000 instructions need `--max-instructions 0` (a resource guard, not a
time-out). No laptop was measured.

## How these paths were tested

On 2026-11-14, on a shared 128-core Linux server (load average 35 to 135 during the runs), each
path in a sandbox (bubblewrap) holding only a fresh home directory and a release-shaped copy of
this repository, with the environment cleared; no container runtime was available.

- Path 1: unpacked and run in an Ubuntu 14.04 root file system (glibc 2.19), an Ubuntu 24.04 one
  (glibc 2.39), and the host's own `/usr` (Pop!_OS 24.04): the same output in each, 4.4 to 4.7 s
  for unpacking and `run-examples.sh` together.
- Path 2: the host's `/usr` read-only (gcc 13.3, python3 3.12, git; no cmake): the script installed
  cmake and ninja (15 s), cloned and built OpenFHE (341 s), compiled and ran the program and checked
  it (27 s): first verdict after 6 min 23 s. Each further program: 25 to 28 s, almost all of it
  compiling the program against OpenFHE's headers.
- Path 3: heir-opt downloaded (3 to 4 s); each program then checked in under 1 s.

## Where to read more

- `harness/frontend/README.md`: the manual (every option, the report, the input format, the
  OpenFHE and HEIR frontends, what each verdict assumes).
- `README.md`: what is proved, and how to re-check the proofs (`./verify.sh`).
