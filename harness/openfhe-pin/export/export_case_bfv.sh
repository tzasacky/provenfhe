#!/usr/bin/env bash
# export_case_bfv.sh <outdir> <pin_export_bfv args...>
# Runs pin_export_bfv (upstream OpenFHE v1.6.1 + the frontend's tracer, export/build_cpp_bfv.sh), then
# the UNMODIFIED extractor harness/frontend/openfhe/extract_bfv.py exactly as the frontend's tests call
# it (harness/frontend/tests/run.sh 9a/9f: `python3 -I extract_bfv.py --params P --trace T --artifact NAME`;
# the outputs are the extractor's default: every ciphertext the program never consumes).
#   EXTRACT_FLAGS   extra extractor options (the adversarial hand-built inputs use --assume-fresh-inputs)
# If extraction fails, prog.fhecheck.json keeps the extractor's {"format":..., "error":...} object and
# a line "EXTRACT-FAIL <case> <msg>" is printed. Exit status: pin_export_bfv's (0 = the case was dumped).
set -uo pipefail
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(cd "$HERE/../../.." && pwd)"
BIN="${OPENFHE_PIN_BUILD:-$ROOT/harness/build/openfhe-pin}/bin/pin_export_bfv"
OUT="$1"; shift
mkdir -p "$OUT"
export OMP_NUM_THREADS=1
OUT="$(cd "$OUT" && pwd)"
"$BIN" "$OUT" "$@" > "$OUT/export.log" 2>&1
rc=$?
if [ $rc -ne 0 ]; then
  echo "EXPORT-FAIL $(basename "$OUT") rc=$rc $(tail -n 1 "$OUT/export.log")"
  exit $rc
fi
# shellcheck disable=SC2086
python3 -I "$ROOT/harness/frontend/openfhe/extract_bfv.py" --params "$OUT/params.json" --trace "$OUT/trace.jsonl" \
     --artifact "$(basename "$OUT")" ${EXTRACT_FLAGS:-} \
     > "$OUT/prog.fhecheck.json" 2> "$OUT/extract.err"
xrc=$?
if [ $xrc -ne 0 ]; then
  msg="$(python3 -I - "$OUT/prog.fhecheck.json" "$OUT/extract.err" <<'PY'
import json, sys
try:
    print(json.load(open(sys.argv[1]))["error"])
except Exception:
    err = open(sys.argv[2]).read().strip().splitlines()
    m = "extract_bfv.py crashed: " + (err[-1] if err else "no output")
    json.dump({"format": "fhe-check/v1", "error": m}, open(sys.argv[1], "w"), indent=2)
    print(m)
PY
)"
  echo "EXTRACT-FAIL $(basename "$OUT") $msg"
fi
[ -s "$OUT/extract.err" ] || rm -f "$OUT/extract.err"
exit 0
