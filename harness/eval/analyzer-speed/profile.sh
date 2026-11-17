#!/usr/bin/env bash
# Time split and peak memory of fhe_check by program size, for BGV and BFV and both verdict paths.
# Run from the repository root:
#
#   harness/eval/analyzer-speed/profile.sh [--sizes "10000 100000 1000000 10000000"]
#
# Programs (gen.py): "certified" = `mixed` (every instruction kind in turn; one output);
# "refused" = `sumsq` (a sum of M = n/2 fresh ciphertexts, then 44 squarings: the noise overflows
# at the first squaring, so the whole sum is analysed before the refusal). Parameters: BGV = the
# OpenFHE depth-8 FIXEDMANUAL example (N = 2^15, nine 55-bit primes; its scaling data rewritten for
# the generated inputs, so the user-level decryption check runs); BFV = the OpenFHE
# HPSPOVERQLEVELED chain example for `mixed`, the BEHZ chain example for `sumsq` (HPSPOVERQLEVELED
# refuses squaring before any analysis).
#
# Two runs per program: `fhe_check --no-suggest --max-instructions 0 FILE` for the wall time and
# peak resident memory (GNU time), and the same with `--time` for the split (read, lex, JSON parse,
# decode, check, render; for BFV the parts of the check are timed one by one and the check is then
# run whole, so the --time run takes longer than the first). Prints a Markdown table and the raw
# --time lines.
#
# Environment: FHE_CHECK (default .lake/build/bin/fhe_check); OUT (default a fresh temporary
# directory; the programs are deleted after use); TIMEOUT per run in seconds (default 3600).
set -uo pipefail
cd "$(dirname "$0")/../../.."
FHE_CHECK="${FHE_CHECK:-.lake/build/bin/fhe_check}"
TIMEOUT="${TIMEOUT:-3600}"
SIZES="10000 100000 1000000 10000000"
while [ $# -gt 0 ]; do
  case "$1" in
    --sizes) SIZES="$2"; shift 2;;
    *) echo "unknown argument $1"; exit 2;;
  esac
done
OUT="${OUT:-$(mktemp -d)}"; mkdir -p "$OUT"
HERE=harness/eval/analyzer-speed
EX=harness/frontend/examples
BGV=$EX/openfhe_depth8_q55_fixedmanual.fhecheck.json
BFV=$EX/openfhe_bfv_default_chain_d3.fhecheck.json
BFVB=$EX/openfhe_bfv_behz_hybrid_chain_d2.fhecheck.json
echo "commit: $(git rev-parse --short HEAD)$(git diff --quiet HEAD -- FHE FheCheck.lean || echo ' (modified tree)')"
echo "machine: $(nproc) cores, $(sed -n 's/^model name[^:]*: //p' /proc/cpuinfo | head -1), $(awk '/MemTotal/ {printf "%d GB RAM", $2/1048576}' /proc/meminfo); load average at start $(cut -d' ' -f1-3 /proc/loadavg)"
echo
echo "| scheme | path | instructions | MB file | verdict | wall s | peak MB | read+lex | parse | decode | check | render |"
echo "|---|---|---|---|---|---|---|---|---|---|---|---|"
RAW="$OUT/raw.txt"; : >"$RAW"
for n in $SIZES; do
  for spec in "BGV:certified:$BGV:mixed:$n" "BGV:refused:$BGV:sumsq:$((n / 2))" \
              "BFV:certified:$BFV:mixed:$n" "BFV:refused:$BFVB:sumsq:$((n / 2))"; do
    IFS=: read -r sch path base kind m <<<"$spec"
    f="$OUT/${sch}_${kind}_$n.json"
    python3 -I "$HERE/gen.py" "$base" "$kind" "$m" "$f" || continue
    cnt="$(python3 -I -c 'import json,sys; print(len(json.load(open(sys.argv[1]))["program"]["body"]))' "$f")"
    mb="$(( $(stat -c %s "$f") / 1048576 ))"
    /usr/bin/time -f "%e %M" -o "$OUT/t" timeout "$TIMEOUT" "$FHE_CHECK" --no-suggest --max-instructions 0 "$f" >"$OUT/o" 2>/dev/null
    read -r s kb < <(tail -1 "$OUT/t")
    v="$(sed -n 's/^VERDICT: \([^:]*\):.*/\1/p' "$OUT/o" | head -1)"
    case "$v" in *" ("*) v="${v%% (*} (qualified)";; esac
    timeout "$TIMEOUT" "$FHE_CHECK" --no-suggest --max-instructions 0 --time "$f" 2>"$OUT/e" >/dev/null
    { echo "## $sch $path $cnt"; cat "$OUT/e"; } >>"$RAW"
    # the split: ms values from the --time lines
    get() { grep -o "$1 [0-9]* ms" "$OUT/e" | head -1 | grep -o '[0-9]*' | head -1; }
    rd=$(( $(get read) + $(get lex) )); ps=$(get "JSON parse"); dc=$(get decode)
    if [ "$sch" = BFV ]; then ck=$(get "report data)"); else ck=$(get check); fi
    rn=$(get render)
    echo "| $sch | $path | $cnt | $mb | ${v:-?} | $s | $((kb / 1024)) | $rd | $ps | $dc | $ck | $rn |"
    rm -f "$f"
  done
done
echo
echo "Split columns in ms, from the --time run. BFV 'check': the whole check run after the parts were timed"
echo "(decode included). Raw --time output:"
echo
sed 's/^/    /' "$RAW"
