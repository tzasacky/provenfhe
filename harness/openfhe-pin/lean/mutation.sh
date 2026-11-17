#!/usr/bin/env bash
# Mutation test of the openfhe_pin harness: the unmutated executable must pass on the given cases,
# and with every `--mutate NAME` (a deliberately wrong copy of one trusted operation swapped into
# the forced path, FHE/Pin/Mutants.lean) the suite must FAIL.
#   harness/openfhe-pin/lean/mutation.sh CASELIST [EXE]      # CASELIST: one case directory per line
# Prints a table mutant -> number of failing checks, first failing check, checks that fail; the
# last line is `lean mutants: C caught of M`. Exit 0 iff the baseline passes and every mutant is
# caught. Environment: MUTATION_OUT (output directory), THREADS (per run, default 8; the runs go
# in parallel).
set -uo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../../.." && pwd)"
LIST="${1:?usage: mutation.sh CASELIST [EXE]}"
EXE="${2:-$ROOT/.lake/build/bin/openfhe_pin}"
OUT="${MUTATION_OUT:-${OPENFHE_PIN_BUILD:-$ROOT/harness/build/openfhe-pin}/mutation}"
THREADS="${THREADS:-8}"
MUTANTS="centring switch-centring automorph-index automorph-shift automorph-sign gadget-factor gadget-digit scale-step scale-dec mul-negacyclic lift key-order ms-parts"
mkdir -p "$OUT"
rc=0
( "$EXE" --threads "$THREADS" --out "$OUT/none.jsonl" --list "$LIST" > "$OUT/none.log" 2>&1; echo $? > "$OUT/none.rc" ) &
for m in $MUTANTS; do
  ( "$EXE" --threads "$THREADS" --mutate "$m" --out "$OUT/$m.jsonl" --list "$LIST" > "$OUT/$m.log" 2>&1; echo $? > "$OUT/$m.rc" ) &
done
wait
if [ "$(cat "$OUT/none.rc")" != 0 ]; then
  echo "BASELINE FAILS (see $OUT/none.log):"; grep '^FAIL' "$OUT/none.log" | head; rc=1
else
  echo "baseline: $(tail -1 "$OUT/none.log")"
fi
printf '%-18s %-8s %-8s %-28s %s\n' mutant verdict fails "first failing check" "failing checks (count)"
caught=0; total=0
for m in $MUTANTS; do
  code="$(cat "$OUT/$m.rc")"
  summary="$(python3 -I - "$OUT/$m.jsonl" <<'PY'
import json, sys, collections
c = collections.Counter(); first = None
for l in open(sys.argv[1]):
    d = json.loads(l)
    if d.get("ok") is False:
        c[d["check"]] += 1
        if first is None: first = d["check"] + ":" + d["id"]
print(sum(c.values()), first or "-", " ".join(f"{k}({v})" for k, v in sorted(c.items())))
PY
)"
  n="${summary%% *}"; rest="${summary#* }"; first="${rest%% *}"; checks="${rest#* }"
  total=$((total + 1))
  if [ "$code" -eq 1 ] && [ "$n" -gt 0 ]; then v=CAUGHT; caught=$((caught + 1)); else v=MISSED; rc=1; fi
  printf '%-18s %-8s %-8s %-28s %s\n' "$m" "$v" "$n" "$first" "$checks"
done
echo "lean mutants: $caught caught of $total"
exit $rc
