#!/usr/bin/env bash
# Closes the loop for `fhe_check recommend` (UNTRUSTED driver, see roundtrip.py):
# recommended settings -> the real library (OpenFHE re-run / HEIR re-compile) -> re-extract ->
# plain fhe_check, plus primes-as-predicted, margins, sizes and measured evaluation time.
#   roundtrip.sh OUTDIR [--openfhe] [--auto] [--heir] [--depths 1,2,...] [--reps R]
# Needs bgv_demo (harness/frontend/openfhe/build.sh), the HEIR binary in harness/build/heir-nightly,
# and fhe_check (lake build fhe_check). Timings use OMP_NUM_THREADS=1 and are measurements on the
# machine that runs this, not claims.
set -euo pipefail
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
exec python3 -I "$HERE/roundtrip.py" "$@"
