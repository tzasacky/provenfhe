#!/usr/bin/env bash
# The gate entry of the OpenFHE conformance harness. From the COMMITTED fixtures only (no OpenFHE):
#
#   harness/openfhe-pin/difftest.sh                    # builds with `lake build openfhe_pin`
#   OPENFHE_PIN=<exe> harness/openfhe-pin/difftest.sh  # uses an already built checker
#
# Runs, on every case of fixtures/fixtures.tar.xz (recorded from upstream OpenFHE v1.6.1, commit
# b59e1f291965f14fbee5172cd83a20f5b856204f): the checks a-f of the trusted definitions, the
# bit-exact algorithm comparisons `algo.*`, the extractor's refusals and extractions on the
# recorded traces, and the same for the BFV fixtures (fixtures/fixtures-bfv.tar.xz) with the
# coverage cross-check (run.sh with GATE=1 MUTANTS=0; see its header). The mutation tests are the
# gate's step 7: harness/openfhe-pin/mutants.sh. Then the real-size sample (realsize/run.sh with
# SAMPLE=1) prints one more line, `realsize sample: PASS ...`; its failure fails this suite too.
# Prints ONE summary line:
#   openfhe-pin: PASS: <cases> cases, <lines> check lines (<ok> ok / <fail> fail / <null> null),
#     expected-fail list 0, <n> extractor refusals tested (...), <e>/<e> encryptions = encrypt ...,
#     algo: <ops> operations / <coefficients> coefficients bit-exact (0 differing),
#     mutants caught: <c>/<c> checks + <a>/<a> algo; <seconds> s, load <load average>
# preceded, on failure only, by the output of the failing step. Exit 0 iff everything passes AND
# fixtures/EXPECTED_FAIL.tsv has no entry.
# Environment: THREADS (default: the number of cores, at most 48), KEEP=1.
set -uo pipefail
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
GATE=1 LIVE=0 MUTANTS=0 "$HERE/run.sh"; rc=$?
# The committed real-size sample (realsize/sample: two recorded cases at N = 8192, no OpenFHE needed):
# the checker on it must reproduce the committed counts (realsize/sample/summary.json). About a minute.
SAMPLE=1 OPENFHE_PIN="${OPENFHE_PIN:-}" "$HERE/realsize/run.sh" || rc=1
exit $rc
