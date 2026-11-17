#!/usr/bin/env bash
# Regenerates the OpenFHE examples (harness/frontend/examples/openfhe_*), the small-ring
# value-check fixtures (harness/frontend/tests/values/*) and the refusal fixtures
# (harness/frontend/tests/refused/*: programs the extractor must refuse, e.g. EvalInnerProduct)
# with bgv_demo on traced upstream OpenFHE v1.6.1 (build it with build_openfhe.sh).
# Runs single-threaded (OMP_NUM_THREADS=1): the tracer refuses calls from parallel regions.
#   make_examples.sh [OUTROOT]   default: write into the repository
# Every run is followed by the scale/level cross-check (extract.py) and the plaintext-value
# cross-check (value_check.py); any mismatch stops the script.
set -euo pipefail
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
FRONT="$(cd "$HERE/.." && pwd)"
ROOT="$(cd "$FRONT/../.." && pwd)"
B="$ROOT/harness/build/frontend-openfhe/bgv_demo"
B="${BGV_DEMO:-$B}"
EX="${1:-$FRONT}/examples"
VA="${1:-$FRONT}/tests/values"
RF="${1:-$FRONT}/tests/refused"
export OMP_NUM_THREADS=1
TMP="$(mktemp -d)"
trap 'rm -rf "$TMP"' EXIT
mkdir -p "$EX" "$VA" "$RF"

# name | bgv_demo arguments
EXAMPLES=(
  "openfhe_depth2_fixedmanual|--scal FIXEDMANUAL --prog chain --depth 2"
  "openfhe_depth8_q55_fixedmanual|--scal FIXEDMANUAL --prog chain --depth 8 --qbits 55 --firstbits 55"
  "openfhe_rot_depth2|--scal FIXEDMANUAL --prog rot --depth 2"
  "openfhe_dot_depth2|--scal FIXEDMANUAL --prog dot --depth 2"
)
for s in FLEXIBLEAUTOEXT FLEXIBLEAUTO FIXEDAUTO FIXEDMANUAL; do
  l=$(echo $s | tr A-Z a-z)
  for p in chain plain plainlvl lr rotsum negate subpt symenc nocheck; do
    [ $s = FIXEDMANUAL ] && [ $p = chain ] && continue  # = openfhe_depth2_fixedmanual
    EXAMPLES+=("openfhe_${l}_${p}|--scal $s --prog $p --depth 2")
  done
done
EXAMPLES+=("openfhe_flexibleautoext_dot|--scal FLEXIBLEAUTOEXT --prog dot --depth 2"
           "openfhe_flexibleautoext_rot|--scal FLEXIBLEAUTOEXT --prog rot --depth 2"
           "openfhe_default_chain_depth1|--scal default --prog chain --depth 1")

run_one() {  # name args outdir mode (0: example, 1: value fixture, 2: refusal fixture)
  local name=$1 args=$2 out=$3 keep=$4 d="$TMP/$1"
  mkdir -p "$d"
  # shellcheck disable=SC2086
  "$B" run "$d" $args > /dev/null
  if [ "$keep" = 2 ]; then
    if python3 -I "$HERE/extract.py" --params "$d/params.json" --trace "$d/trace.jsonl" > "$d/prog.json"; then
      echo "expected a refusal: $name"; exit 1; fi
    mkdir -p "$out/$name"
    cp "$d/params.json" "$d/trace.jsonl" "$out/$name/"
    python3 -I -c "import json,sys; print(json.load(open(sys.argv[1]))['error'])" "$d/prog.json" > "$out/$name/refusal.txt"
    echo "$name: refused: $(cat "$out/$name/refusal.txt")"
    return
  fi
  python3 -I "$HERE/extract.py" --params "$d/params.json" --trace "$d/trace.jsonl" --artifact "$name" > "$d/prog.json"
  python3 -I "$HERE/value_check.py" "$d/prog.json" "$d/values.json" > "$d/value_check.txt" || {
    cat "$d/value_check.txt"; echo "value check failed: $name"; exit 1; }
  if [ "$keep" = 1 ]; then
    mkdir -p "$out/$name"
    cp "$d/params.json" "$d/trace.jsonl" "$d/values.json" "$out/$name/"
  else
    cp "$d/params.json" "$out/$name.params.json"
    cp "$d/trace.jsonl" "$out/$name.trace.jsonl"
    cp "$d/prog.json" "$out/$name.fhecheck.json"
  fi
  echo "$name: $(cat "$d/value_check.txt" | tail -1)"
}

for e in "${EXAMPLES[@]}"; do run_one "${e%%|*}" "${e#*|}" "$EX" 0; done
# Small ring (N = 1024, HEStd_NotSet: NOT secure; only the value cross-check uses them), so that
# the raw decryptions can be committed: every program under every technique.
for s in FLEXIBLEAUTOEXT FLEXIBLEAUTO FIXEDAUTO FIXEDMANUAL; do
  l=$(echo $s | tr A-Z a-z)
  for p in chain dot rot plain plainlvl lr rotsum negate subpt symenc nocheck; do
    run_one "n1024_${l}_${p}" "--scal $s --prog $p --depth 2 --n 1024" "$VA" 1
  done
  # EvalInnerProduct = EvalMult + EvalSum: refused on OpenFHE >= 1.6 (fused rotation sum)
  run_one "innerprod_${l}" "--scal $s --prog innerprod --depth 2 --n 1024" "$RF" 2
  # a CoefPacked plaintext, and EvalMult with a key on a 3-part operand: refused
  run_one "coefpk_${l}" "--scal $s --prog coefpk --depth 2 --n 1024" "$RF" 2
  run_one "threepart_${l}" "--scal $s --prog threepart --depth 3 --n 1024" "$RF" 2
done
