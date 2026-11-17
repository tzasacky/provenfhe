#!/usr/bin/env bash
# Regenerates the CKS26 evaluation (harness/eval/cks26): fhe_check on the evaluation circuits of
# attacks 2 and 3 of Choe, Kang, Stehle, "New IND-CPA-D Attacks on BFV and BGV" (CCS 2026).
#
#   run.sh                 everything: needs the traced OpenFHE v1.6.1
#                          (harness/frontend/openfhe/build_openfhe.sh) and .lake/build/bin/fhe_check
#                          (lake build fhe_check). Removes out/ and cases/ first. About 1.5 h on 12
#                          cores (the N = 2^17 runs dominate); JOBS=n changes the parallelism.
#   run.sh --keep          the same, but cases with a summary in out/ are not re-run
#   run.sh --committed     no OpenFHE: re-runs fhe_check on the committed cases/*.fhecheck.json.gz,
#                          compares verdict line, exit code and bounds with out/*.summary.json,
#                          (the checker's verdict, exit code and bounds)
#
# Outputs: out/NAME.summary.json (one per run), cases/NAME.fhecheck.json.gz (the files checked, for
# the headline cases).
# Verdicts, bounds and K' are deterministic (they depend on the parameters and the program only);
# measured noises and times depend on the run's randomness and on the machine.
set -euo pipefail
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(cd "$HERE/../../.." && pwd)"
FHE="${FHE_CHECK:-$ROOT/.lake/build/bin/fhe_check}"
[ -x "$FHE" ] || { echo "no fhe_check at $FHE: run 'lake build fhe_check' (or set FHE_CHECK)" >&2; exit 1; }
mode="${1:-}"
if [ "$mode" = "--committed" ]; then
  python3 -I "$HERE/recheck.py"
else
  "$HERE/build.sh" > /dev/null
  if [ "$mode" != "--keep" ]; then rm -rf "$HERE/out" "$HERE/cases"; fi
  python3 -I "$HERE/run.py" --jobs "${JOBS:-12}"
fi
if grep -n "$ROOT" "$HERE"/out/*.json > /dev/null; then
  echo "absolute paths in the results" >&2; exit 1
fi
echo "done: $HERE/out"
