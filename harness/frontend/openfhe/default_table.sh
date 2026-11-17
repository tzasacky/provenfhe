#!/usr/bin/env bash
# "What a default OpenFHE user sees": the `chain` program at OpenFHE's own parameters
# (GenCryptoContext; t = 65537, HYBRID), 4 scaling techniques x depth 1..8, checked by fhe_check in
# worst-case mode and with --kappa 128, 64, 40. Needs bgv_demo (build_openfhe.sh) and fhe_check.
# Runs OpenFHE single-threaded (OMP_NUM_THREADS=1; the tracer refuses calls from parallel regions).
#   default_table.sh [OUTDIR]     writes OUTDIR/<technique>_d<D>.fhecheck.json and prints a TSV
set -euo pipefail
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(cd "$HERE/../../.." && pwd)"
B="${BGV_DEMO:-$ROOT/harness/build/frontend-openfhe/bgv_demo}"
export OMP_NUM_THREADS=1
FHE_CHECK="${FHE_CHECK:-$ROOT/.lake/build/bin/fhe_check}"
OUT="${1:-$(mktemp -d)}"
mkdir -p "$OUT"
cell() {  # file, extra args -> "CERTIFIED m" (smallest margin shown) or "over x" or the verdict
  python3 -I - "$FHE_CHECK" "$@" <<'PY'
import json, subprocess, sys
r = json.loads(subprocess.run([sys.argv[1], "--json", "--no-suggest"] + sys.argv[2:], capture_output=True, text=True).stdout)
v = r["verdict"]
if v == "CERTIFIED":
    ms = [o.get("decMarginBits", o["marginBits"]) for o in r["outputs"]] + [o["marginBits"] for o in r["outputs"]]
    print(f"CERTIFIED {min(ms):.2f}")
elif v == "NOT CERTIFIED":
    f = (r.get("failure") or {}).get("firstFailing")
    print(f"over {f['overflowBits']:.2f}" if f and f.get("overflowBits") is not None else "NOT CERTIFIED (decryption)")
else:
    print(v)
PY
}
printf 'D\ttechnique\tN\tlimb bits\tworst case\tkappa 128\tkappa 64\tkappa 40\n'
for d in 1 2 3 4 5 6 7 8; do
  for s in FIXEDMANUAL FIXEDAUTO FLEXIBLEAUTO FLEXIBLEAUTOEXT; do
    w="$OUT/run_${s}_$d"; mkdir -p "$w"
    "$B" run "$w" --scal $s --prog chain --depth $d > /dev/null
    f="$OUT/$(echo $s | tr A-Z a-z)_d$d.fhecheck.json"
    python3 -I "$HERE/extract.py" --params "$w/params.json" --trace "$w/trace.jsonl" --artifact "default_${s}_d$d" > "$f"
    python3 -I "$HERE/value_check.py" "$f" "$w/values.json" | grep -q "value_check: OK" || { echo "value check failed: $s $d" >&2; exit 1; }
    meta=$(python3 -I -c "
import json,sys,math
p=json.load(open(sys.argv[1]))['params']
print(str(int(math.log2(p['N'])))+'\t'+'+'.join(str(round(math.log2(int(l['q'])))) for l in p['limbs']))" "$f")
    printf '%s\t%s\t2^%s\t%s\t%s\t%s\t%s\n' "$d" "$s" "$meta" "$(cell "$f")" "$(cell "$f" --kappa 128)" "$(cell "$f" --kappa 64)" "$(cell "$f" --kappa 40)"
    rm -rf "$w"
  done
done
