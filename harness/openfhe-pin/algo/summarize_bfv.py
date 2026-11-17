#!/usr/bin/env python3
"""Summarise the BFV `algo.*` lines (`"scheme": "BFV"`) of openfhe_pin result files.
   summarize_bfv.py results.jsonl [more.jsonl ...] [--fails K]
Prints
  1. per (check, impl, multiplication technique [, key switching]): cases, operations, limbs and
     coefficients compared, operations exact / differing / not run, coefficients differing;
  2. the variants (never failures): per (check, variant, technique) the operations that reproduce
     OpenFHE and the number of coefficients on which the variant differs from OpenFHE
     (for `algo.variant.mul`: the float model against the exact sums and the other contraction);
  3. exact decryption and observations: `algo.decrypt.exact` (the trusted exact decryption against the library's own),
     `algo.observe.relin` (OpenFHE's decryptions before and after its own relinearisation);
  4. coverage, and the first K failing lines per check."""
import json, sys, collections
files = [a for a in sys.argv[1:] if not a.startswith('--')]
K = int(sys.argv[sys.argv.index('--fails') + 1]) if '--fails' in sys.argv else 3
if '--fails' in sys.argv: files.remove(sys.argv[sys.argv.index('--fails') + 1])
rows = collections.OrderedDict()
fails = collections.defaultdict(list)
cov = [0, 0]; unexpl = []
variants = collections.defaultdict(lambda: [0, 0, 0, 0])
cases = set(); byN = collections.defaultdict(set); byTech = collections.defaultdict(set)
dec = collections.defaultdict(lambda: [0, 0, 0, 0, 0, 0])   # (validity) -> cts, coeffs, cts differing, coeffs differing
obs = []; nobs = 0
KS_CHECKS = ('algo.relin', 'algo.rotate')
for f in files:
    for l in open(f):
        l = l.strip()
        if not l: continue
        j = json.loads(l)
        c = j['check']
        if j.get('scheme') != 'BFV' or not c.startswith('algo.'): continue
        cases.add(j['case']); byN[j.get('N')].add(j['case']); byTech[(j.get('mult'), j.get('ks'), j.get('enc'))].add(j['case'])
        if c.startswith('algo.variant'):
            v = variants[(c, j.get('variant', j['impl']), j.get('mult') if 'relin' not in c and 'rotate' not in c else j.get('mult', '') + '/' + j.get('ks', ''))]
            v[0] += 1; v[1] += 1 if j.get('matches') else 0
            v[2] += j.get('coeffs', 0); v[3] += j.get('mismatches', 0)
            continue
        if c == 'algo.coverage':
            cov[0] += j.get('produced', 0); cov[1] += j.get('explained', 0)
            if j.get('unexplained'): unexpl.append((j['case'], j['unexplained']))
            continue
        if c == 'algo.observe.relin':
            nobs += 1
            if j.get('plaintextCoeffsChanged', 0): obs.append(j)
            continue
        if c == 'algo.info': continue
        if c == 'algo.decrypt.exact':
            d = dec[('not under s' if 'notAnEncryptionUnderS' in j else 'valid', j.get('mult'), j['procedure'].split(':')[0])]
            d[0] += 1; d[1] += j.get('coeffs', 0)
            d[2] += 1 if j.get('mismatches', 0) else 0; d[3] += j.get('mismatches', 0)
        tech = j.get('mult', '?') + ('/' + j.get('ks', '?') if c in KS_CHECKS else '')
        k = (c, j['impl'], tech)
        r = rows.setdefault(k, dict(cases=set(), n=0, limbs=0, coeffs=0, ok=0, bad=0, null=0, mism=0, ms=0))
        r['cases'].add(j['case']); r['n'] += 1
        r['limbs'] += j.get('limbs', 0); r['coeffs'] += j.get('coeffs', 0); r['ms'] += j.get('ms', 0)
        r['mism'] += j.get('mismatches', 0)
        if j['ok'] is True: r['ok'] += 1
        elif j['ok'] is False:
            r['bad'] += 1; fails[k].append(j)
        else: r['null'] += 1
print(f"{len(cases)} BFV cases; by N: " + ", ".join(f"N={n}: {len(s)}" for n, s in sorted(byN.items(), key=lambda x: (x[0] is None, x[0]))))
print("by technique: " + ", ".join(f"{m}/{k}/{e}: {len(s)}" for (m, k, e), s in sorted(byTech.items(), key=str)))
print(f"\n{'check':28} {'impl':22} {'technique':24} {'cases':>5} {'ops':>6} {'limbs':>8} {'coeffs':>12} {'exact':>6} {'DIFF':>5} {'n/a':>5} {'coeffs differing':>16} {'ms':>9}")
for (c, i, t), r in sorted(rows.items()):
    print(f"{c:28} {i:22} {t:24} {len(r['cases']):5} {r['n']:6} {r['limbs']:8} {r['coeffs']:12} {r['ok']:6} {r['bad']:5} {r['null']:5} {r['mism']:16} {r['ms']:9}")
tot = collections.defaultdict(lambda: [0, 0, 0, 0, 0, 0])
for (c, i, t), r in rows.items():
    x = tot[c]; x[0] += r['n']; x[1] += r['limbs']; x[2] += r['coeffs']; x[3] += r['ok']; x[4] += r['bad']; x[5] += r['null']
print(f"\n{'check (all impl, all techniques)':40} {'ops':>7} {'limbs':>9} {'coeffs':>13} {'exact':>7} {'DIFF':>6} {'n/a':>6}")
for c, x in sorted(tot.items()):
    print(f"{c:40} {x[0]:7} {x[1]:9} {x[2]:13} {x[3]:7} {x[4]:6} {x[5]:6}")
if variants:
    print("\nvariants (for the record; not checks): operations reproducing OpenFHE, coefficients differing from OpenFHE")
    print(f"{'check':24} {'technique':22} {'variant':72} {'ops':>6} {'match':>6} {'coeffs':>12} {'differing':>11}")
    for (c, i, t), v in sorted(variants.items(), key=str):
        print(f"{c:24} {str(t):22} {i[:72]:72} {v[0]:6} {v[1]:6} {v[2]:12} {v[3]:11}")
print("\nEXACT DECRYPTION AND OBSERVATIONS")
print("  algo.decrypt.exact: Spec.Scheme.bfvDecrypt (exact rounding) against OpenFHE's recorded decryption")
for (val, m, proc), d in sorted(dec.items(), key=str):
    print(f"    {val:12} {str(m):18} {proc:44}: {d[0]:6} ciphertexts, {d[1]:10} coefficients; differing: {d[2]} ciphertexts, {d[3]} coefficients")
print(f"  algo.observe.relin: OpenFHE's own decryption before / after its relinearisation: {nobs} relinearisations observed, {len(obs)} changed the plaintext")
for j in obs[:max(K, 12)]:
    print(f"    {j['case']} {j['operands'][0]} -> {j['id']}: {j['plaintextCoeffsChanged']} of {j['coeffs']} coefficients changed (mult {j.get('mult')}, ks {j.get('ks')}, towers {j.get('towers')}, levelsDropped {j.get('levelsDropped')}, N {j.get('N')})")
print(f"\ncoverage: {cov[1]} of {cov[0]} ciphertexts produced by the traces are outputs of a compared operation")
for c, u in unexpl[:10]: print(f"   not covered: {c}: {u}")
for k, js in sorted(fails.items()):
    print(f"\n--- {k[0]} [{k[1]}] {k[2]}: {len(js)} failing; first {min(K, len(js))}:")
    for j in js[:K]:
        print("   ", json.dumps({x: j[x] for x in j if x not in ('suite', 'scaling', 'impl', 'check', 'ok')})[:900])
