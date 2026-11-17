#!/bin/bash
# Phase-contract check of recorded Lattigo BGV runs. usage: harness/lattigo-pin/run.sh [CASE_DIR] [OUT.jsonl]
# Default: the committed fixtures. Exit 1 iff some phase check is not ok (expected for the defect suites).
set -euo pipefail
cd "$(dirname "$0")/../.."
DIR=${1:-harness/lattigo-pin/fixtures}
OUT=${2:-$(mktemp)}
LAKE=${LAKE:-$HOME/.elan/bin/lake}
"$LAKE" build FHE.Pin.Sound Challenge.Instances.Lattigo.Defs >/dev/null
rc=0
"$LAKE" env lean --run harness/lattigo-pin/lean/LattigoPin.lean "$OUT" "$DIR"/*.json || rc=$?
python3 -I harness/lattigo-pin/lean/summarize.py "$OUT"
exit $rc
