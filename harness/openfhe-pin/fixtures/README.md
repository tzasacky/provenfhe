# Committed openfhe-pin fixtures

**Where they come from.** Every case of `fixtures.tar.xz` is an `openfhe-pin/v1` dump
(`../FORMAT.md`) of a real run of **upstream OpenFHE v1.6.1**, commit
`b59e1f291965f14fbee5172cd83a20f5b856204f` (openfheorg/openfhe-development), built by
`harness/frontend/openfhe/build_openfhe.sh` with the frontend's observation-only tracer
(`openfhe-v1.6.1-tracer.patch` + `fhecheck-tracer.h`; Release, single-threaded `WITH_OPENMP=OFF`,
`WITH_REDUCED_NOISE=OFF`, 64-bit native integers, gcc 13.3.0), exported by `../cpp/pin_export.cpp` and extracted by the unmodified
`harness/frontend/openfhe/extract.py`. `SOURCE.txt` records the commit, the hashes of the patch,
the tracer and the extractor, and the compiler. Nothing in the archive comes from the v1.3.1
tracing fork the harness used before.

**Recorded hashes and the tracer version.** The archive was recorded with the current tracer: every
`params.json` carries its version stamp (`FHECHECK_TRACER_VERSION`,
`harness/frontend/openfhe/fhecheck-tracer.h`), so no case needs an entry in
`harness/frontend/openfhe/legacy-traces.tsv`, and the hashes in `SOURCE.txt` are those of the
committed patch, tracer header and extractor. `export/make_fixtures.sh` reproduces the archive byte
for byte from that build (same compiler, tar and xz).

**What is in it.** 263 cases, 5615408 bytes: every case with N = 16 (220) or N = 64 (43) of the
`fixtures` suite of `../export/gen_matrix.py` (269 cases; the 4 at N = 256 and the 2 at N = 1024
are left out to keep the archive small; `export.log`, `selftest.json`, `extract.err` are dropped).

* scaling techniques: FIXEDMANUAL 62, FIXEDAUTO 67, FLEXIBLEAUTO 67, FLEXIBLEAUTOEXT 67;
  depth 1 to 4;
* programs (cases): `chain` 14, `dot` 6, `rot` 6, `plain` 6, `plainlvl` 6, `lr` 6, `rotsum` 6,
  `innerprod` 6, `ops` 6, `opsnn` 6, `mixed-a…d` 16, random programs 64 (`randomcore` 52,
  `randomall` 12), `paths-*` 68 (`fastrot multmany compress relinearize mutable negate coefpacked
  string evalsum ptfirst multrelin automorphism scalar`), `threepart-*` 47 (`modreduce mul3x2
  mul3x3 square add3x2 rot mulplain autoreduce`, incl. keys for s³, s⁴);
* messages: packed (`random`, `max`, `small`) and, in a quarter of the rotation, CoefPacked
  (`alt`, `witness`); `paths-coefpacked` (5) and `paths-string` (5) are non-packed by construction;
* 151 cases have an extracted program (checks a–f and `algo.*`); **112 are refused by the
  extractor** (checks a, c, d and `algo.*` still run on them): see `EXPECTED_REFUSALS.tsv`.

N = 64 under FLEXIBLEAUTOEXT is generated at depth 3: OpenFHE v1.6.1 refuses to generate
parameters for that ring dimension at depth 1 or 2 (`rns-cryptoparameters.cpp:161`,
"EstimateLogP() failure: expected sizeP [1], but got sizeP [2]").

| file | |
|---|---|
| `fixtures.tar.xz` | the cases (`params.json`, `trace.jsonl`, `prog.fhecheck.json`, `pin.json`, `polys.txt` each) |
| `SOURCE.txt` | provenance of the archive (written by `make_fixtures.sh`) |
| `EXPECTED_FAIL.tsv` | `check<TAB>case` pairs known to fail: **empty**. `../difftest.sh` fails if it has an entry; `../run.sh` fails on any failing check not listed, and on a listed one that passes |
| `EXPECTED_REFUSALS.tsv` | `case<TAB>class<TAB>message` of the 112 refused cases. The checker's `x.refusal` line must pass with exactly this class for exactly these cases, and `../export/refusals.py` re-runs the extractor on each recorded trace and requires the recorded message |
| `mutation.list` | the 20 cases the two mutation tests run on (per technique: `chain` depth 3, `rotsum`, `rot`, `plainlvl`, and a 3-component modulus switch) |

Refusal classes (count): `non-packed-plaintext` 67, `evalmult-key-on-3-part-operand` 20,
`fast-rotation-not-mapped` 7, `evalsum-not-mapped` 5, `evalinnerproduct-not-mapped` 4,
`compress-not-mapped` 3, `evalmultmutable-not-mapped` 3, `rotation-of-3-part-threw` 3.

Regenerate (needs the OpenFHE build above; about 70 s, most of it `xz -9e`):

    harness/frontend/openfhe/build_openfhe.sh WORKDIR
    OPENFHE_INSTALL=WORKDIR/install harness/openfhe-pin/export/make_fixtures.sh

The archive is deterministic for a given OpenFHE build and extractor (seeds are derived from the
case names; sorted names, fixed mtime and owner). `mutation.list` and `EXPECTED_FAIL.tsv` are
maintained by hand.
