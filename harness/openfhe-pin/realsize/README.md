# openfhe-pin at real sizes (the full suite is not gated; the committed sample is)

The gated fixtures (`../difftest.sh`) are recorded at N = 16 and 64. This directory is the same
checker (`openfhe_pin`, every check family `a`-`f` plus `algo.*`) on executions of **upstream
OpenFHE v1.6.1** in the contexts the library builds **itself at 128-bit security**
(`HEStd_128_classic`: no ring dimension is set; only the depth, the plaintext modulus and the
technique), N = 8192, 16384 and 32768, 60-bit limbs for BFV, up to 13 limbs.

The recordings come from the build configuration of the committed fixtures: unmodified v1.6.1 plus
the observation-only tracer patch, built single-threaded by `harness/frontend/openfhe/build_openfhe.sh`
(`WITH_OPENMP=OFF`; `../export/build_cpp.sh` refuses any other build).

| file | what |
|---|---|
| `suite.py` | the case list (`--list`, also in `CASES.tsv`) and the recorder (`--out DIR`): one `../export/export_case.sh` / `export_case_bfv.sh` per case, seeds from the case names |
| `run.sh` | regenerates the recordings from a traced single-threaded build, verifies them against `MANIFEST.sha256.tsv`, checks every case (one `openfhe_pin --threads 1 --with-algo --forced-max-n 32768` per case, at most `CASE_TIMEOUT` seconds, default 21,600), summarizes, compares with `summary.json`; `SAMPLE=1 run.sh`: the committed sample only |
| `summarize.py` | per case and in total: check lines ok / fail / null, bit-exact operations / coefficients / differing, wall time, peak memory (`summary.json`, `table.md`) |
| `MANIFEST.sha256.tsv` | sha256 of the five files of every case (`../export/sha_manifest.py`); a second, independent recording of all 82 cases was byte-identical |
| `summary.json`, `table.md` | the result of the run reported below |
| `sample/*.tar.xz`, `sample/summary.json` | two recorded cases at N = 8192 (one BGV, one BFV; about 9 MB each compressed) and their expected counts |
| `library.json`, `library.md` | `algo.runLibrary` alone (`--only algo --algo-only library`) on every BFV case, per case (section below) |

## The suite (82 cases)

BGV: every scaling technique (FIXEDMANUAL, FIXEDAUTO, FLEXIBLEAUTO, FLEXIBLEAUTOEXT) at depths 1,
3, 6 and 10 with the program `ops` (every operation once: encryption, add/sub, plaintext operands,
products with relinearisation, rotations, modulus switching, decryption), a product chain down the
whole modulus chain per technique, `rotsum`, and `Compress`. v1.6.1 refuses its own default
parameters for FIXEDAUTO and FLEXIBLEAUTO at depths 9, 10 and 11 (`rns-cryptoparameters.cpp:161`,
`EstimateLogP() failure: expected sizeP [3], but got sizeP [4]`); those two use depth 12.

BFV: every multiplication technique (HPS, HPSPOVERQ, HPSPOVERQLEVELED, BEHZ) x key switching
(HYBRID, BV) at depths 1, 3, 6 and 10 with a seeded random program of mapped operations (where the
extractor refuses the random program, `rotsum` as well), `ops` at depth 3, a product chain at depth
10 per technique; 9 and 11 limbs of 60 bits at N = 32768 (HPS at depths 14 and 16, HPSPOVERQ at
16: the 128-bit accumulator branch of the HPS scaling); `Compress`; HPSPOVERQLEVELED level drops
(`levels`); EXTENDED encryption; and the library defect reported upstream (defaults, t = 786433,
depth 6, an `EvalMult` chain).

## What makes it feasible

The trusted negacyclic product (`Spec.NPoly`'s `*`, a schoolbook sum) and `automorph`, evaluated
literally, cost N^2 big-integer operations per product, so a case costs 16-25 times more for 4
times N (a depth-2 product chain: 59 s at N = 1024 and 977 s at N = 4096 for BGV, 177 s and 4417 s
for BFV; hours per case at N = 16384). The checker therefore evaluates forms proved equal to them:

* `FHE/Pin/Kron.lean` (kernel-checked; axioms `propext`, `Classical.choice`, `Quot.sound`):
  `mulNeg_eq`, the negacyclic product by Kronecker substitution (one GMP multiplication of two
  packed integers, slot width computed from the data) **is** the trusted `*` on all inputs;
  `autoL_eq`, a linear-time scatter **is** `automorph`.
* Every forced path uses them: phases, encryption, keys, `Source.step` messages
  (`fastMsg_spec`), the staged key switches (`ofFam_innerZ`, `ofFam_autoFam`), the tensor, the BFV
  forced multiplication pipelines; each forced form has its equality theorem (`phaseZ_spec`,
  `keyErrA_spec`, `stepA_spec`, `ksStaged_openfhe`, `addKS_locked`, `rotStaged161_locked`,
  `hpsForced_eq` ...).
* The products are computed as arrays: `Spec.NPoly` is a structure with one function field, and
  compiled code re-evaluates an `NPoly`-valued intermediate for every coefficient where it is used
  inside another coefficient function (`FHE/Pin/Force.lean`, before `mulArr`). The untrusted glue
  avoids two such re-evaluations: the CRT lift of the key switch inside the BFV
  `algo.relin.leveled` comparison is computed once, and the never-forced closure of `plainInstrF`
  (`b.user.*`) does not evaluate an automorphism eagerly.
* The BFV multiplication is compared as the LOCKED definitions with forced intermediates
  (`algo.mul`, `impl = forced`, proved equal) at every N up to `--forced-max-n` (32768 here).
* The composed BFV library run `Challenge.CertifyBFV.runLibrary` (`algo.runLibrary`) is executed
  at real N: `runLibL` (`FHE/Pin/BFV/AlgoLibrary.lean`) is the locked execution with the
  multiplications as the forced pipelines above, the key switches as `ksBFVF` (every ModUp or CRT
  digit forced once, every inner product a Kronecker product: `ksBFVF_eq` against the locked
  `Challenge.RealizeBFV.ksBFV`), the plaintext products as Kronecker products, the automorphisms
  as the linear-time scatter, and the ciphertext environment kept as a list; `runLibrary_list`
  proves it equal to `runLibrary` (axioms `propext`, `Classical.choice`, `Quot.sound`). Its cap is
  that of the forced multiplications (`--forced-max-n`).

On the committed gated fixtures this checker gives exactly the recorded counts (`../run.sh`: BGV
93443 lines, 78409 ok / 0 fail / 15034 null; BFV 91243, 78291 / 0 / 12952; every mutant caught;
the library run on 176 programs, 1323 ciphertexts, 0 differing).

Still bounded by size (`null` with the reason, at real N): the literal evaluation of the unstaged
definitions (`*.literal-vs-forced`, N <= 32) and the other key-switching variants
(`algo.variant.*`, N <= 64).

## The composed library run at real sizes (`library.json`, `library.md`)

`algo.runLibrary` alone (`openfhe_pin --threads 1 --only algo --algo-only library --forced-max-n
32768`, one process per case) on the 60 recorded BFV cases (recordings byte-identical to
`MANIFEST.sha256.tsv`), checker built from this tree, 2026-11-15, up to 32 processes at a time on
the 128-core machine (shared; 1-minute load 6 to 33), per-case timeout 2,700 s, then 5,100 s
(N = 16384) or 6,600 s (N = 32768) for the cases that had not finished:

* **33 of the 35 CERTIFIED programs executed** at N = 8192 (7), 16384 (21) and 32768 (5), 2-9
  limbs of 60 bits, every technique (HPS, HPSPOVERQ, HPSPOVERQLEVELED, BEHZ) with both key
  switchings (HYBRID, BV): 531 instructions, **455 intermediate and output ciphertexts compared
  limb for limb with OpenFHE's, 90,923,008 coefficients, 0 differing** (488 lines ok, 0 fail).
  Wall time 12 s (N = 8192, 2 limbs) to 6,156 s (N = 32768, 7 limbs); peak memory 0.2-2.8 GB.
* 2 not finished within 6,600 s: `rs_bfv_hps_bv_d16_random` and `rs_bfv_poq_def_d16_chain`
  (N = 32768, 11 limbs).
* 25 not applicable (`null` with the reason): 17 the extractor does not map, 8 NOT CERTIFIED
  (`runLibrary` is stated for certified programs).

The time is the forced multiplications (the same pipelines as `algo.mul`'s forced tier: the locked
per-coefficient scalar functions recompute their tables at every coefficient); a key switch is
seconds (on `rs_bfv_hps_bv_d10_random`, N = 16384, 7 limbs: a rotation's key switch 3.4 s, one
forced squaring more than 150 s). Per case: `library.md` / `library.json`.

The full run below (with `algo.runLibrary` at real N) executed the composed library run on the same
33 programs with the same counts (531 instructions, 455 ciphertexts, 90,923,008 coefficients, 0
differing); the two 11-limb programs did not finish there either (see below).

## Result

Checker: `openfhe_pin` built from the Lean sources of this tree (binary sha256 `2bcf344a…`),
one process per case, 32 at a time, on a 128-core x86-64 machine (shared at the start with one strict
gate run), 2026-11-15/16; recordings regenerated by `run.sh` and byte-identical to
`MANIFEST.sha256.tsv`. Timeout policy of this run: none in `run.sh` (it had none then; the default is
now `CASE_TIMEOUT=21600`); the two cases still running were terminated by hand:
`rs_bfv_hps_bv_d16_random` at 16,567 s and `rs_bfv_poq_def_d16_chain` at 21,604 s (both N = 32768,
11 limbs; both also did not finish in the library-only run above). **80 of the 82 cases finished**
(BGV 22: N = 8192-32768, 2-13 limbs; BFV 58: N = 8192-32768, 2-9 limbs of 60 bits): **35,242 check
lines: 29,275 ok, 0 fail, 5,967 null; 7,547 bit-exact operations over 878,149,632 coefficients (every
coefficient of every limb, no sampling), 0 differing**, `algo.runLibrary` executed on 33 programs and
not applicable on 25. Of the BFV programs the finished cases map, 33 are CERTIFIED and 8 NOT
CERTIFIED (no claim is made for these); 226 BFV products were compared both as the proved-equal
forced locked definition and as the staged mirror, all bit-exact. Per case: `table.md`. Wall time
29 s to 13,242 s (`rs_bfv_hps_def_d14_chain`, N = 32768, 9 limbs) for the finished cases; peak memory
0.2-4.3 GB (6.6 GB for the terminated HPS case); 52.1 CPU-hours in all (terminated cases included),
6 h 02 min elapsed with 32 processes.

The library defect reported in a public issue (issue 1 on the author's fork of OpenFHE, "BFV with default settings: EvalMult silently decrypts wrong in every slot for some t and depths"; `rs_bfv_def_def_d6_t786433_chain`): the last `EvalMult`
(level 5, 3 levels dropped) decrypts wrong in 7,497 of 16,384 coefficients. The checker does not
report conformance there: `certifyBFV?` is NOT CERTIFIED, the reference run rejects the program at
that product (2β ≥ Q), so `b.msg`, `b.raw` and `f.decok` are `null` at it and after it; the step
contract itself (`e.step`) holds at the measured noise.

    harness/openfhe-pin/realsize/run.sh                 # hours on 128 cores; WORK=..., JOBS=..., CASE_TIMEOUT=...
    SAMPLE=1 harness/openfhe-pin/realsize/run.sh        # the committed sample, a few minutes
