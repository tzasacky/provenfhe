#!/usr/bin/env bash
# Gate entry (scripts/check-spec.sh step 6 runs every harness/*/difftest.sh): the fhe_check and
# frontend tests of tests/run.sh, from committed fixtures only (no OpenFHE or HEIR installation).
# What this is: verdict/exit-code/golden regressions of the registered fhe_check executable
# (including the red-team witnesses), extractor reproducibility, and, on recorded OpenFHE runs,
# extraction plus a message-level value cross-check by an UNTRUSTED Python mirror of Source.step
# (openfhe/value_check.py). What it is not: a pin of the Lean definitions in Spec/.
#   FHE_CHECK=/path/to/exe harness/frontend/difftest.sh    test another build
set -euo pipefail
cd "$(dirname "$0")/../.."
export PATH="$HOME/.elan/bin:$PATH"
if [ -z "${FHE_CHECK:-}" ]; then
  lake build fhe_check >/dev/null 2>&1 || { echo "lake build fhe_check failed"; lake build fhe_check 2>&1 | tail -20; exit 1; }
fi
exec harness/frontend/tests/run.sh "$@"
