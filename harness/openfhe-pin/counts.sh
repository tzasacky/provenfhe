#!/usr/bin/env bash
# Regenerates results/difftest-counts.json (lean/counts.py over one difftest.sh run: per-check
# ok/fail/null counts, comparisons vs distinct recorded operations of algo.*, programs passing
# certifyBFV? by ring dimension and recorded assumption, the programs executed through
# runLibrary and why the others were not, the idealised-multiplication difference). From the
# committed fixtures only; same environment as difftest.sh (OPENFHE_PIN, THREADS).
#   harness/openfhe-pin/counts.sh
set -euo pipefail
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
mkdir -p "$HERE/results"
COUNTS_JSON="$HERE/results/difftest-counts.json" "$HERE/difftest.sh"
python3 -I -c 'import json,sys; json.load(open(sys.argv[1]))' "$HERE/results/difftest-counts.json"
echo "wrote harness/openfhe-pin/results/difftest-counts.json"
