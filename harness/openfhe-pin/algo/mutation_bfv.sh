#!/usr/bin/env bash
# Mutation check of the BFV algorithm-level comparison (FHE/Pin/BFV/Algo.lean).
#   harness/openfhe-pin/algo/mutation_bfv.sh CASELIST [EXE] [SURVIVORS.tsv] [-- extra openfhe_pin options]
# SURVIVORS.tsv (default fixtures/MUTANTS_SURVIVING-bfv-algo.tsv if it exists): `mutant<TAB>reason`,
# mutants known to survive on the data (invisible there); they are reported, not failures.
# CASELIST: a file with one BFV case directory per line. For the unmutated run and for every
# mutant of FHE/Pin/BFV/Mutants.lean plus the HYBRID key-switching mutants shared with BGV
# (FHE/Pin/AlgoMutants.lean), each of which perturbs ONE convention, runs
# `openfhe_pin --only algo --algo-mutate M` and prints a table: mutant -> comparisons run / exact /
# differing, the first differing operation, limb and coefficient, and how many coefficients were
# compared. The last lines are `bfv algo mutants: C killed of M` and the survivors.
# `moddown-no-t` is a CONTROL: at plaintext modulus 1 (BFV's ModDown has no t-correction) it is
# the library's convention itself and must NOT produce a difference.
# Kill detection is relative to the unmutated run: its failing comparisons are standing differences
# (e.g. additions that mix coefficient and evaluation representations) and a mutant is killed by
# a failing comparison that is not one of them. Exit 0 iff the unmutated run compares something,
# the control passes and every mutant is killed. `algo.decrypt.exact` (the trusted exact decryption against
# the recorded decryption: not a comparison of a mirror) is
# reported separately and never counts.
# Environment: MUTATION_OUT (output directory), THREADS (per run, default 4), JOBS (runs in
# parallel, default 4).
set -uo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../../.." && pwd)"
LIST="${1:?usage: mutation_bfv.sh CASELIST [EXE] [-- openfhe_pin options]}"; shift
EXE="$ROOT/.lake/build/bin/openfhe_pin"
if [ $# -gt 0 ] && [ "$1" != "--" ]; then EXE="$1"; shift; fi
SURV="$ROOT/harness/openfhe-pin/fixtures/MUTANTS_SURVIVING-bfv-algo.tsv"
if [ $# -gt 0 ] && [ "$1" != "--" ]; then SURV="$1"; shift; fi
[ "${1:-}" = "--" ] && shift
OUT="${MUTATION_OUT:-${OPENFHE_PIN_BUILD:-$ROOT/harness/build/openfhe-pin}/algo-mutation-bfv}"
mkdir -p "$OUT"
MUTANTS="none moddown-no-t float-fma-flipped sw-exact sr-exact sw-no-half sr-floor poverq-centred-digits \
behz-no-montgomery behz-no-sk behz-sk-canonical aux-order poverq-roles leveled-mul-drop-ignored \
leveled-ks-drop-ignored ks-moddown-t automorph-before-moddown bv-digits-canonical bv-digits-unbalanced \
timesqovert-round timesqovert-floor timesqovert-delta compress-floor decrypt-small-exact-scale \
modup-centred moddown-centred moddown-add ks-all-centred digit-boundary automorph-first"
JOBS="${JOBS:-4}"
n=0
for m in $MUTANTS; do
  "$EXE" --only algo --algo-mutate "$m" --variants-max-n 0 --algo-literal-max-n 0 \
     --threads "${THREADS:-4}" --out "$OUT/$m.jsonl" --list "$LIST" "$@" >"$OUT/$m.log" 2>&1 &
  n=$((n + 1))
  if [ $((n % JOBS)) -eq 0 ]; then wait; fi
done
wait
python3 -I - "$OUT" "$SURV" $MUTANTS <<'PY'
import json, sys, os
out, surv, muts = sys.argv[1], sys.argv[2], sys.argv[3:]
known = {}
if os.path.isfile(surv):
    for l in open(surv):
        if l.strip() and not l.startswith('#'):
            k, _, why = l.rstrip('\n').partition('\t'); known[k] = why
skip = ('algo.decrypt.exact', 'algo.coverage', 'algo.info', 'algo.copy')
def load(m):
    rows = []
    for l in open(f"{out}/{m}.jsonl"):
        j = json.loads(l)
        c = j['check']
        if j.get('scheme') != 'BFV' or not c.startswith('algo.'): continue
        if c in skip or c.startswith('algo.variant') or c.startswith('algo.observe'): continue
        rows.append(j)
    return rows
key = lambda j: (j['case'], j['check'], j['id'], j['impl'])
base = load('none')
# standing differences of the unmutated run (e.g. additions of operands held in different representations, which the trusted
# ring operation does not reproduce): a mutant is killed by a failing comparison NOT among them
standing = {key(j) for j in base if j['ok'] is False}
ok = True; killed = 0; total = 0; survivors = []
print(f"standing failures of the unmutated run (excluded from kill detection): {len(standing)}")
print(f"{'mutant':26} {'comparisons':>11} {'coeffs':>10} {'exact':>7} {'DIFF':>6} {'new':>5} {'n/a':>5}  first new difference")
for m in muts:
    rows = base if m == 'none' else load(m)
    n = len(rows); coeffs = sum(j.get('coeffs', 0) for j in rows)
    good = sum(1 for j in rows if j['ok'] is True); bad = sum(1 for j in rows if j['ok'] is False)
    na = n - good - bad
    new = [j for j in rows if j['ok'] is False and key(j) not in standing]
    first = new[0] if new else None
    if first is not None and 'first' in first:
        f = first['first']
        where = (f"part {f['part']} limb {f['limb']} " if 'part' in f else "") + f"coeff {f['coeff']}"
        d = f"{first['case']} {first['check']} {first['id']} [{first['impl']}] ({first.get('via', first['op'])}): {where}: OpenFHE {f['openfhe']} vs {f['lean']}; {first.get('mismatches')} of {first.get('coeffs')} coefficients differ"
    elif first is not None: d = f"{first['case']} {first['check']} {first['id']}: {first.get('why', first.get('mismatches'))}"
    else: d = "-"
    if m == 'none':
        verdict = "NOTHING COMPARED" if n == 0 else f"baseline ({bad} standing differences)"
        if n == 0: ok = False
    elif m == 'moddown-no-t':
        verdict = "CONTROL FAILED" if new else "control passes (equivalent to the library's convention)"
        if new: ok = False
    else:
        total += 1
        verdict = "killed" if new else ("survives (listed)" if m in known else "SURVIVED")
        if new: killed += 1
        else:
            if m not in known: ok = False
            survivors.append((m, n, coeffs))
    print(f"{m:26} {n:11} {coeffs:10} {good:7} {bad:6} {len(new):5} {na:5}  {verdict}: {d}")
print(f"bfv algo mutants: {killed} killed of {total}")
for m, n, c in survivors:
    print(f"SURVIVOR {m}: no new difference in {n} comparisons, {c} coefficients" + (f" (listed: {known[m]})" if m in known else " (NOT listed)"))
sys.exit(0 if ok else 1)
PY
