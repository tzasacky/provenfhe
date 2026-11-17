#!/usr/bin/env bash
# Regenerates the certified-frontier tables (README.md says what is measured and how).
#   run.sh OUT [TRACED_INSTALL] [PRISTINE_INSTALL]
# TRACED_INSTALL   OpenFHE v1.6.1 with the fhe_check tracer, single-threaded build
#                  (default harness/build/frontend-openfhe-noomp/install)
# PRISTINE_INSTALL unmodified OpenFHE v1.6.1 (default harness/build/reports-openfhe/install)
# Environment: FHE_CHECK (default .lake/build/bin/fhe_check), WORKERS (default 32), SKIP_FIT=1 to
# keep the fitted cost model, SKIP_TIMING=1 to skip the measured ratios.
# Time: about 2-3 hours of searches on a 128-core machine, then about 1 hour of timing (single
# runs at a time per worker; run it on a quiet machine: rows timed above load 20 are flagged).
set -euo pipefail
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(cd "$HERE/../../.." && pwd)"
OUT="$(mkdir -p "${1:?usage: run.sh OUT [TRACED_INSTALL] [PRISTINE_INSTALL]}" && cd "$1" && pwd)"
export FHE_CHECK="${FHE_CHECK:-$ROOT/.lake/build/bin/fhe_check}"
export FRONTIER_BIN="$OUT/bin"
W="${WORKERS:-32}"
"$HERE/build.sh" "$FRONTIER_BIN" "${2:-$ROOT/harness/build/frontend-openfhe-noomp/install}" \
  "${3:-$ROOT/harness/build/reports-openfhe/install}"
[ "${SKIP_FIT:-0}" = 1 ] || python3 "$HERE/timing_fit.py" "$OUT" --rounds 2 --reps 3
python3 "$HERE/frontier.py" "$OUT" bgvfm --workers "$W"
python3 "$HERE/frontier.py" "$OUT" bgvauto --workers "$W"
python3 "$HERE/frontier.py" "$OUT" bfv --workers "$W"
[ "${SKIP_TIMING:-0}" = 1 ] || python3 "$HERE/timing.py" "$OUT" --workers 4
python3 "$HERE/tables.py" "$OUT"
echo "tables: $OUT/tables.md, $OUT/frontier.tsv; raw rows: $OUT/results/"
