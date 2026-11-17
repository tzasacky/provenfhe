#!/usr/bin/env bash
# Build and run the proved reference implementation (`provenfhe_ref`, docs/REFERENCE-IMPLEMENTATION.md).
#
#   harness/ref/run.sh [SEEDS] [LOGN]      default: 2 seeds, N = 2^13
#
# For each seed and scheme (BGV at `bgvKSSeal`, BFV at `sealBFV`): keys, encryption, the accepted
# example circuits evaluated, decrypted and compared with `sem`; the rejected ones refused. Exit
# code non-zero on any mismatch or unexpected class verdict. Log under $OUT (default build/ref-impl/logs,
# relative to the repository root). LAKE: the lake executable (default: lake on the PATH).
set -euo pipefail
cd "$(dirname "$0")/../.."
SEEDS="${1:-2}"
LOGN="${2:-13}"
OUT="${OUT:-build/ref-impl/logs}"
mkdir -p "$OUT"
LAKE="${LAKE:-lake}"
"$LAKE" build provenfhe_ref >/dev/null
LOG="$OUT/run-$(date +%Y%m%d-%H%M%S)-n$LOGN.log"
status=0
if command -v /usr/bin/time >/dev/null; then
  /usr/bin/time -v .lake/build/bin/provenfhe_ref all "$SEEDS" 1 "$LOGN" >"$LOG" 2>"$LOG.time" || status=$?
  grep -E "Maximum resident|Elapsed" "$LOG.time" || true
else
  .lake/build/bin/provenfhe_ref all "$SEEDS" 1 "$LOGN" >"$LOG" || status=$?
fi
echo "PASS lines: $(grep -cE " PASS$" "$LOG" || true)"
grep -E "FAIL" "$LOG" || true
tail -n 1 "$LOG"
echo "log: $LOG"
exit "$status"
