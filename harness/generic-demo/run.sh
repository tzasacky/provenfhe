#!/usr/bin/env bash
# Generic demo: the trusted core and the checker need no OpenFHE.
#
#   harness/generic-demo/run.sh            # from the repository root; needs .lake/build/bin/fhe_check
#   UPDATE=1 harness/generic-demo/run.sh   # rewrite expected/ from this run
#
# Steps: (0) fhe_check links no FHE library; (1) the hand-written inputs regenerate byte for byte
# from make_inputs.py; (2) the HEIR input re-extracts byte for byte from the committed HEIR/Lattigo
# MLIR (no heir-opt, no OpenFHE); (3) fhe_check on every input; the exit code, the VERDICT line and
# the per-output bound lines are compared with expected/*.summary (the full reports are kept in
# expected/*.txt for reading, not compared: they cite file paths and the tool's wording).
set -euo pipefail
cd "$(git rev-parse --show-toplevel)"
D=harness/generic-demo
BIN=.lake/build/bin/fhe_check
[ -x "$BIN" ] || { echo "missing $BIN: run 'lake build fhe_check'"; exit 2; }
TMP=$(mktemp -d)
trap 'rm -rf "$TMP"' EXIT
fail=0

echo "== 0. shared libraries of fhe_check (no OpenFHE, SEAL, Lattigo, HEIR)"
if ldd "$BIN" | grep -iE 'openfhe|seal|lattigo|heir'; then echo "FAIL: links an FHE library"; fail=1
else echo "ok: $(ldd "$BIN" | awk '{print $1}' | tr '\n' ' ')"; fi

echo "== 1. hand-written inputs regenerate"
python3 -I "$D/make_inputs.py" "$TMP/gen" >/dev/null
for f in "$TMP"/gen/*.json; do
  if cmp -s "$f" "$D/inputs/$(basename "$f")"; then echo "ok: $(basename "$f")"
  else echo "FAIL: $(basename "$f") differs from make_inputs.py"; fail=1; fi
done

echo "== 2. HEIR input re-extracted from the committed MLIR (HEIR nightly-2026.11.11, Lattigo backend)"
python3 -I harness/frontend/heir/extract_bgv.py \
  harness/frontend/examples/heir_dot_product_8.lattigo.worstcase.mlir > "$TMP/heir.json"
if cmp -s "$TMP/heir.json" "$D/inputs/heir_dot_product_8.worstcase.fhecheck.json"; then
  echo "ok: heir_dot_product_8.worstcase.fhecheck.json"
else echo "FAIL: HEIR extraction differs"; fail=1; fi

echo "== 3. fhe_check"
for f in "$D"/inputs/*.json; do
  n=$(basename "$f" .fhecheck.json)
  set +e; "$BIN" --no-suggest "$f" > "$TMP/$n.txt"; code=$?; set -e
  { echo "exit $code"; grep -E '^VERDICT|noise <=|overflow:' "$TMP/$n.txt"; } > "$TMP/$n.summary"
  if [ "${UPDATE:-0}" = 1 ]; then
    cp "$TMP/$n.txt" "$D/expected/$n.txt"; cp "$TMP/$n.summary" "$D/expected/$n.summary"
  fi
  if diff -u "$D/expected/$n.summary" "$TMP/$n.summary"; then
    echo "ok: $n: $(sed -n 2p "$TMP/$n.summary" | cut -c1-60) (exit $code)"
  else echo "FAIL: $n"; fail=1; fi
done

[ $fail = 0 ] && echo "ALL OK" || { echo "SOME CHECKS FAILED"; exit 1; }
