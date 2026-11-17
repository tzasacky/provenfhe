#!/usr/bin/env bash
# "What a default OpenFHE user sees" (README table) on upstream v1.6.1: copy of
# harness/frontend/openfhe/default_table.sh with CSV output. Since the 2026-11-14 re-run the
# defaults are the repository's own: bgv_demo of harness/build/frontend-openfhe (traced v1.6.1,
# harness/frontend/openfhe/build_openfhe.sh + build.sh), the current extractor
# harness/frontend/openfhe/extract.py (records $.scaling, so fhe_check can decide the user-level
# verdict), its value_check.py, and the repository's fhe_check (.lake/build/bin). The earlier
# defaults (the upstream build of this directory, the patched extractor copy extract.py here and
# a pinned checker) can still be selected with BGV_DEMO / EXTRACT / VALUE_CHECK / FHE_CHECK.
# Extra column `scaling`: whether the extracted file carries $.scaling.
#   default_table.sh [OUTDIR] > default_table_upstream.csv
set -uo pipefail
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(cd "$HERE/../../.." && pwd)"
B="${BGV_DEMO:-$ROOT/harness/build/frontend-openfhe/bgv_demo}"
FC="${FHE_CHECK:-$ROOT/.lake/build/bin/fhe_check}"
EXTRACT="${EXTRACT:-$ROOT/harness/frontend/openfhe/extract.py}"
VALUE_CHECK="${VALUE_CHECK:-$ROOT/harness/frontend/openfhe/value_check.py}"
export OMP_NUM_THREADS=1
OUT="${1:-$HERE/out/default_table}"
RUNS="$ROOT/harness/build/eval/upstream/runs/$(basename "$OUT")"
mkdir -p "$OUT" "$RUNS"
cell() {
  python3 -I - "$FC" "$@" <<'PY'
import json, subprocess, sys
r = json.loads(subprocess.run([sys.argv[1], "--json", "--no-suggest"] + sys.argv[2:], capture_output=True, text=True).stdout)
v = r["verdict"]
if v == "CERTIFIED":
    ms = [o.get("decMarginBits", o["marginBits"]) for o in r["outputs"]] + [o["marginBits"] for o in r["outputs"]]
    # the printed verdict: "CERTIFIED" only if user-level decryption is covered ($.scaling);
    # otherwise e.g. "CERTIFIED AT PHASE LEVEL", written as such
    print(f"{r.get('verdictLabel', v)} {min(ms):.2f}")
elif v == "NOT CERTIFIED":
    f = (r.get("failure") or {}).get("firstFailing")
    print(f"over {f['overflowBits']:.2f}" if f and f.get("overflowBits") is not None else "NOT CERTIFIED (decryption)")
else:
    print(v)
PY
}
echo "D,technique,logN,limb_bits,special_bits,worst,kappa128,kappa64,kappa40,value_check,scaling"
for d in 1 2 3 4 5 6 7 8; do
  for s in FIXEDMANUAL FIXEDAUTO FLEXIBLEAUTO FLEXIBLEAUTOEXT; do
    w="$RUNS/run_${s}_$d"; mkdir -p "$w"
    "$B" run "$w" --scal $s --prog chain --depth $d > "$w/run.log" 2>&1
    f="$OUT/$(echo $s | tr A-Z a-z)_d$d.fhecheck.json"
    python3 -I "$EXTRACT" --params "$w/params.json" --trace "$w/trace.jsonl" --artifact "default_${s}_d$d" > "$f"
    vc=$(python3 -I "$VALUE_CHECK" "$f" "$w/values.json" 2>&1 | grep -q "value_check: OK" && echo OK || echo FAIL)
    meta=$(python3 -I -c "
import json,sys,math
p=json.load(open(sys.argv[1]))
print(str(int(math.log2(p['N'])))+','+'+'.join(str(round(math.log2(q['q']),2)) for q in p['qs'])+','+'+'.join(str(round(math.log2(q['q']),2)) for q in p['special']))" "$w/params.json")
    sc=$(python3 -I -c "import json,sys; print('yes' if 'scaling' in json.load(open(sys.argv[1])) else 'no')" "$f")
    echo "$d,$s,$meta,$(cell "$f"),$(cell "$f" --kappa 128),$(cell "$f" --kappa 64),$(cell "$f" --kappa 40),$vc,$sc"
  done
done
