#!/usr/bin/env bash
# Wall time and peak memory of fhe_check on synthetic programs of 10^3..10^6 instructions, and on
# real programs. Run from the repository root:
#
#   harness/eval/analyzer-speed/bench.sh [--sizes "1000 10000 100000 1000000"] [FILE...]
#
# Environment:
#   FHE_CHECK   the executable (default .lake/build/bin/fhe_check)
#   BEFORE      an executable built from the commit before the fast analyzer (optional): the same
#               runs, each under BEFORE_TIMEOUT seconds (default 1200), are added to the table
#   BEFORE_MAX  largest size given to BEFORE (default 100000; the quadratic analyzer needs hours
#               to days above that)
#   KINDS       program families of gen.py (default "add rot mulrelin modswitch lincomb mixed")
#   OUT         directory for the generated programs (default a fresh temporary directory)
#   BGV_BASE, BFV_BASE  the examples that supply the parameters (default: OpenFHE depth-8
#               FIXEDMANUAL BGV; OpenFHE BFV HPSPOVERQLEVELED chain, which refuses squaring)
#
# FILE...: further fhe-check/v1 inputs (real programs), run as they are.
# Prints a Markdown table. Every run is `fhe_check --no-suggest --max-instructions 0 FILE`; the
# time is wall time of the whole process (reading, parsing, checking, printing), the memory its
# peak resident set (GNU time).
set -uo pipefail
cd "$(dirname "$0")/../../.."
FHE_CHECK="${FHE_CHECK:-.lake/build/bin/fhe_check}"
BEFORE="${BEFORE:-}"
BEFORE_TIMEOUT="${BEFORE_TIMEOUT:-1200}"
BEFORE_MAX="${BEFORE_MAX:-100000}"
KINDS="${KINDS:-add rot mulrelin modswitch lincomb mixed}"
SIZES="1000 10000 100000 1000000"
FILES=()
while [ $# -gt 0 ]; do
  case "$1" in
    --sizes) SIZES="$2"; shift 2;;
    *) FILES+=("$1"); shift;;
  esac
done
OUT="${OUT:-$(mktemp -d)}"
mkdir -p "$OUT"
HERE=harness/eval/analyzer-speed
BGV="${BGV_BASE:-harness/frontend/examples/openfhe_depth8_q55_fixedmanual.fhecheck.json}"
BFV="${BFV_BASE:-harness/frontend/examples/openfhe_bfv_default_chain_d3.fhecheck.json}"

# one run: prints "verdict | seconds | MB" (or "timeout")
run1() { # BIN TIMEOUT FILE
  local t="$OUT/time.txt" o="$OUT/out.txt"
  /usr/bin/time -f "%e %M" -o "$t" timeout "$2" "$1" --no-suggest --max-instructions 0 "$3" >"$o" 2>/dev/null
  local rc=$?
  if [ $rc = 124 ]; then echo "timeout|>$2|-"; return; fi
  local v; v="$(sed -n 's/^VERDICT: \([^:]*\):.*/\1/p' "$o" | head -1)"
  local at; at="$(grep -o 'at body\[[0-9]*\]' "$o" | head -1)"
  # GNU time prepends "Command exited with non-zero status N" for a nonzero exit (NOT CERTIFIED)
  read -r s kb < <(tail -1 "$t")
  echo "${v:-exit $rc}${at:+ $at}|$s|$((kb / 1024))"
}

echo "commit: $(git rev-parse --short HEAD)$(git diff --quiet HEAD -- . ':!harness/eval/analyzer-speed' || echo ' (modified tree)')"
echo "machine: $(nproc) cores, $(sed -n 's/^model name[^:]*: //p' /proc/cpuinfo | head -1), $(awk '/MemTotal/ {printf "%d GB RAM", $2/1048576}' /proc/meminfo); load average at start $(cut -d' ' -f1-3 /proc/loadavg)"
echo "date: $(date -u +%Y-%m-%d)"
echo
if [ -n "$BEFORE" ]; then
  echo "| scheme | program | instructions | verdict | before: s | before: MB | after: s | after: MB |"
  echo "|---|---|---|---|---|---|---|---|"
else
  echo "| scheme | program | instructions | verdict | s | MB |"
  echo "|---|---|---|---|---|---|"
fi
row() { # SCHEME NAME N FILE
  local a b=""
  a="$(run1 "$FHE_CHECK" 7200 "$4")"
  IFS='|' read -r v s m <<<"$a"
  if [ -n "$BEFORE" ]; then
    if [ "$3" -le "$BEFORE_MAX" ]; then
      b="$(run1 "$BEFORE" "$BEFORE_TIMEOUT" "$4")"
      IFS='|' read -r bv bs bm <<<"$b"
      [ "$bv" = "$v" ] || [ "$bv" = timeout ] || v="$v (BEFORE: $bv)"
    else bs="not run"; bm="-"; fi
    echo "| $1 | $2 | $3 | $v | $bs | $bm | $s | $m |"
  else
    echo "| $1 | $2 | $3 | $v | $s | $m |"
  fi
}
for n in $SIZES; do
  for base in "BGV:$BGV" "BFV:$BFV"; do
    sch="${base%%:*}"; bf="${base#*:}"
    for kind in $KINDS; do
      f="$OUT/${sch}_${kind}_$n.json"
      python3 -I "$HERE/gen.py" "$bf" "$kind" "$n" "$f" || continue
      cnt="$(python3 -I -c 'import json,sys; print(len(json.load(open(sys.argv[1]))["program"]["body"]))' "$f")"
      row "$sch" "$kind" "$cnt" "$f"
      rm -f "$f"
    done
  done
done
for f in ${FILES[@]+"${FILES[@]}"}; do
  info="$(python3 -I -c 'import json,sys; d=json.load(open(sys.argv[1])); print(d["params"]["scheme"], len(d["program"]["body"]))' "$f")"
  row "${info%% *}" "$(basename "$f")" "${info##* }" "$f"
done
