#!/usr/bin/env python3
"""Summarise the `algo.*` lines of openfhe_pin result files (`--with-algo` / `--only algo`).
   summarize.py results.jsonl [more.jsonl ...] [--fails K]
Prints, per (check, impl): cases, comparisons, limbs and coefficients compared, and how many were
exact / differed / were not run; then the first K failing lines per check; then the coverage."""
import json, sys, collections
files = [a for a in sys.argv[1:] if not a.startswith('--')]
K = int(sys.argv[sys.argv.index('--fails') + 1]) if '--fails' in sys.argv else 3
if '--fails' in sys.argv: files.remove(sys.argv[sys.argv.index('--fails') + 1])
rows = collections.OrderedDict()
fails = collections.defaultdict(list)
unexpl = collections.Counter(); cov = [0, 0]
variants = collections.defaultdict(lambda: [0, 0, 0, 0])
cases = set()
byN = collections.defaultdict(set)
for f in files:
    for l in open(f):
        l = l.strip()
        if not l: continue
        j = json.loads(l)
        c = j['check']
        if not c.startswith('algo.'): continue
        cases.add(j.get('case')); byN[j.get('N')].add(j.get('case'))
        if c.startswith('algo.variant'):
            v = variants[(c, j['impl'])]
            v[0] += 1; v[1] += 1 if j.get('matches') else 0
            v[2] += 1 if j.get('matches') is False and j.get('allDiffsMultipleOfT') else 0
            v[3] += 1 if 'matches' not in j else 0
            continue
        if c == 'algo.coverage':
            cov[0] += j.get('produced', 0); cov[1] += j.get('explained', 0)
            continue
        k = (c, j['impl'].split(':')[0] if c in ('algo.relin', 'algo.rotate') and False else j['impl'])
        r = rows.setdefault(k, dict(cases=set(), n=0, limbs=0, coeffs=0, ok=0, bad=0, null=0, ms=0))
        r['cases'].add(j['case']); r['n'] += 1
        r['limbs'] += j.get('limbs', 0); r['coeffs'] += j.get('coeffs', 0); r['ms'] += j.get('ms', 0)
        if j['ok'] is True: r['ok'] += 1
        elif j['ok'] is False:
            r['bad'] += 1; fails[k].append(j)
        else: r['null'] += 1
print(f"{len(cases)} cases; by N: " + ", ".join(f"N={n}: {len(s)}" for n, s in sorted(byN.items(), key=lambda x: (x[0] is None, x[0]))))
print(f"{'check':28} {'impl':34} {'cases':>6} {'ops':>7} {'limbs':>8} {'coeffs':>11} {'exact':>7} {'DIFF':>6} {'n/a':>5} {'ms':>9}")
for (c, i), r in sorted(rows.items()):
    print(f"{c:28} {i:34} {len(r['cases']):6} {r['n']:7} {r['limbs']:8} {r['coeffs']:11} {r['ok']:7} {r['bad']:6} {r['null']:5} {r['ms']:9}")
if variants:
    print("\nother variants (for the record; not checks):")
    print(f"{'check':28} {'impl':34} {'ops':>7} {'match':>7} {'differ by multiples of t':>26} {'n/a':>5}")
    for (c, i), v in sorted(variants.items()):
        print(f"{c:28} {i:34} {v[0]:7} {v[1]:7} {v[2]:26} {v[3]:5}")
print(f"\ncoverage: {cov[1]} of {cov[0]} ciphertexts produced by the traces are outputs of a compared operation")
for k, js in sorted(fails.items()):
    print(f"\n--- {k[0]} [{k[1]}]: {len(js)} failing; first {min(K, len(js))}:")
    for j in js[:K]:
        print("   ", json.dumps({x: j[x] for x in j if x not in ('suite', 'scaling', 'impl', 'check', 'ok')})[:700])
