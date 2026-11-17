#!/usr/bin/env bash
# Mutation check of the algorithm-level comparison (FHE/Pin/Algo.lean).
#   harness/openfhe-pin/algo/mutation.sh CASELIST [EXE] [-- extra openfhe_pin options]
# CASELIST: a file with one case directory per line. For the unmutated run and for every mutant of
# FHE/Pin/AlgoMutants.lean (one representative convention perturbed each), runs the key-switching
# and ModReduce comparisons (`openfhe_pin --only algo --algo-only ks,modreduce --algo-mutate M`)
# and prints a table: mutant -> comparisons run / failed, first differing operation, limb and
# coefficient; the last line is `algo mutants: C killed of M`. Exit 0 iff the unmutated run
# compares something without a failure and every mutant is killed (at least one comparison fails).
# Environment: MUTATION_OUT (output directory), THREADS (per run, default 8; the runs go in
# parallel).
set -uo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../../.." && pwd)"
LIST="${1:?usage: mutation.sh CASELIST [EXE] [-- openfhe_pin options]}"; shift
EXE="$ROOT/.lake/build/bin/openfhe_pin"
if [ $# -gt 0 ] && [ "$1" != "--" ]; then EXE="$1"; shift; fi
[ "${1:-}" = "--" ] && shift
OUT="${MUTATION_OUT:-${OPENFHE_PIN_BUILD:-$ROOT/harness/build/openfhe-pin}/algo-mutation}"
mkdir -p "$OUT"
MUTANTS="none modup-centred moddown-centred moddown-add moddown-no-t ks-all-centred digit-boundary automorph-first automorph-last modreduce-canonical"
for m in $MUTANTS; do
  "$EXE" --only algo --algo-mutate "$m" --algo-only ks,modreduce --variants-max-n 0 --algo-literal-max-n 0 \
     --threads "${THREADS:-8}" --out "$OUT/$m.jsonl" --list "$LIST" "$@" >"$OUT/$m.log" 2>&1 &
done
wait
python3 -I - "$OUT" $MUTANTS <<'PY'
import json, sys
out, muts = sys.argv[1], sys.argv[2:]
relevant = {'automorph-first': ('algo.rotate',), 'automorph-last': ('algo.rotate',), 'modreduce-canonical': ('algo.modReduce',)}
ok = True; killed = 0
print(f"{'mutant':22} {'comparisons':>11} {'exact':>7} {'DIFF':>6} {'n/a':>5}  first difference")
for m in muts:
    rel = relevant.get(m, ('algo.relin', 'algo.rotate', 'algo.modReduce') if m == 'none' else ('algo.relin', 'algo.rotate'))
    n = good = bad = na = 0; first = None
    for l in open(f"{out}/{m}.jsonl"):
        j = json.loads(l)
        if j['check'] not in rel: continue
        n += 1
        if j['ok'] is True: good += 1
        elif j['ok'] is False:
            bad += 1
            if first is None: first = j
        else: na += 1
    if first is not None and 'first' in first:
        f = first['first']
        d = f"{first['case']} {first['check']} {first['id']} ({first.get('via', first['op'])}): part {f['part']} limb {f['limb']} coeff {f['coeff']}: OpenFHE {f['openfhe']} vs {f['lean']}" \
            + (" [all differences multiples of t]" if first.get('allDiffsMultipleOfT') else "")
    elif first is not None: d = f"{first['case']} {first['check']} {first['id']}: {first.get('why')}"
    else: d = "-"
    if m == 'none':
        verdict = "UNEXPECTED DIFFERENCE" if bad else "PASS (no difference)" if n else "NOTHING COMPARED"
        if bad or n == 0: ok = False
    else:
        verdict = "killed" if bad else "SURVIVED"
        if bad: killed += 1
        else: ok = False
    print(f"{m:22} {n:11} {good:7} {bad:6} {na:5}  {verdict}: {d}")
print(f"algo mutants: {killed} killed of {len(muts) - 1}")
sys.exit(0 if ok else 1)
PY
