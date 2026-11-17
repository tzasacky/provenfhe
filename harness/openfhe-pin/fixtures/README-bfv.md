# Committed openfhe-pin BFV fixtures

**Where they come from.** Every case of `fixtures-bfv.tar.xz` is a BFV `openfhe-pin/v1` dump
(`../FORMAT.md`, section "BFV cases" and "BFV format changes") of a real `CryptoContextBFVRNS` run of
**upstream OpenFHE v1.6.1**, commit `b59e1f291965f14fbee5172cd83a20f5b856204f`, built by
`harness/frontend/openfhe/build_openfhe.sh` (single-threaded, `WITH_OPENMP=OFF`) with the frontend's
observation-only tracer, exported by `../cpp/pin_export_bfv.cpp` (+ `pin_dump_bfv.h`, `pin_adv_bfv.h`, the shared `pin_dump.h`,
`pin_prng.cpp`) under the deterministic `pin_prng` engine, and extracted by the unmodified
`harness/frontend/openfhe/extract_bfv.py`. `SOURCE-bfv.txt` records the commit, the hashes of the
patch, the tracer and the extractor, the compiler, the exact compile flags of the library and its
floating-point facts (`../export/float_facts.sh`: `FLT_EVAL_METHOD = 0`, no fast-math, no FMA
instruction in `libOPENFHEcore.so` / `libOPENFHEpke.so`, target `x86-64` without `-march`/`-mfma`;
9 x87 instructions in `libOPENFHEcore.so`).

**Recorded hashes and the tracer version.** The archive was recorded with the current tracer: every
`params.json` carries its version stamp (`FHECHECK_TRACER_VERSION`,
`harness/frontend/openfhe/fhecheck-tracer.h`), so no case needs an entry in
`harness/frontend/openfhe/legacy-traces.tsv`, and the hashes in `SOURCE-bfv.txt` are those of the
committed patch, tracer header and extractor. `export/make_fixtures_bfv.sh` reproduces the archive
byte for byte from that build (same compiler, tar and xz).

**What is in it.** Every case of `../export/gen_matrix_bfv.py --suite bfv-fixtures` (241 cases:
213 at N = 16, 28 at N = 64, of which 16 hand-built adversarial inputs, `inputsArbitrary`; about 5 MB with `xz -9e`; `export.log`, `selftest.json`,
`extract.err` are dropped). HPS 57, HPSPOVERQ 55, HPSPOVERQLEVELED 78 (incl. contexts where no
technique setter was called), BEHZ 51; HYBRID 120, BV 121 (6 with a digit size); EXTENDED 10 (refused by the extractor since STANDARD-only encryption);
30/45/60-bit primes; t = 65537 and t = 786433 = 3*2^18 + 1; depth 1-4 (6 for `levels`); every
program of `pin_export_bfv` (chain, square, dot, rot, rotsum, plain, addsub, norelin, norelin2, compress (also to the same number of limbs),
levels, ops, random core/all, coefpacked, mixadd, and the refusal programs innerprod, symenc,
threepart, nocheck, coefpk); messages random / max / small / zero. 24 cases have a traced internal
drop of HPSPOVERQLEVELED (9 of them on a rotation key switch). 189 cases have an extracted
program; **52 are refused** by the extractor: `EXPECTED_REFUSALS-bfv.tsv` (with the Lean
checker's `x.refusal` class of each).

Every case passed `../export/selftest_bfv.py` (independent Python: CRT shapes, secret, `pk.b = e -
a*s`, the STANDARD and EXTENDED encryption relations incl. `extendedPre`, every key digit,
`decrypt.phase`, every `timesQovert` = `ceil(Q'*p/t)`, `decryptTables` recomputed from `qs` and `t`
with Python binary64, and the library's raw decryption against exact rounding of the phase).
`decrypt.raw` is the library's value unreduced (`rawReduced: false`; BEHZ can return `t`).

**Cases whose recorded values are not expected to decrypt or to be checkable as program steps**:

* Programs that combine an unrelinearised product with an ordinary ciphertext or a plaintext
  (`mixadd`, every `ops` at depth 3, and some `random` programs) are refused by `extract_bfv.py`
  (refusal class in `EXPECTED_REFUSALS-bfv.tsv`); the checks that need no program still run on them.
* The rotation intermediate (output of the inner `RelinearizeCore` of `EvalAutomorphism`) is under
  the permuted secret: its `decrypt.raw` is not a decryption of anything.
* `threepart`, `nocheck`: refused by the extractor; their outputs do not decrypt.
* HPSPOVERQLEVELED at a forced small N with OpenFHE's 60-bit default chain (e.g.
  `bfv_n16_def_def_d2_chain_random`): the output does not decrypt; `fhe_check` answers NOT CERTIFIED
  (consistent).

Regenerate (needs the OpenFHE build above; about 2 minutes, most of it `xz -9e`):

    harness/frontend/openfhe/build_openfhe.sh WORKDIR
    OPENFHE_INSTALL=WORKDIR/install harness/openfhe-pin/export/make_fixtures_bfv.sh [RESULTS.jsonl]

The archive is deterministic for a given OpenFHE build and extractor (seeds derived from the case
names; sorted names, fixed mtime and owner); two independent generations of the suite gave
byte-identical case files. No archived file contains an absolute local path (checked by the script).
