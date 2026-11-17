#!/usr/bin/env python3
"""Aggregate openfhe_pin result lines into Markdown tables.   (UNTRUSTED statistics)

    summarize.py results.jsonl [more.jsonl ...] > summary.md

Exact integers in (decimal strings in the result lines), log2 floats out. Nothing here decides a
verdict: every `ok` was computed by the Lean checker from the trusted definitions. Every line
with "ok": false is printed in full at the end.
"""
import collections, json, math, re, statistics, sys


def log2(n):
    n = int(n)
    return math.log2(n) if n > 0 else float("-inf")


def slack(bound, measured):
    """log2(bound / measured); +inf when measured = 0."""
    b, m = int(bound), int(measured)
    if m == 0:
        return float("inf")
    if b == 0:
        return float("-inf")
    return math.log2(b) - math.log2(m)


def fmt(x):
    if x is None:
        return "-"
    if isinstance(x, float):
        if math.isinf(x):
            return "inf" if x > 0 else "-inf"
        return f"{x:.2f}"
    return str(x)


def mmm(xs):
    xs = [x for x in xs]
    if not xs:
        return ("-", "-", "-")
    fin = sorted(xs)
    return (fmt(fin[0]), fmt(statistics.median(fin)), fmt(fin[-1]))


def table(header, rows):
    out = ["| " + " | ".join(header) + " |", "|" + "|".join("---" for _ in header) + "|"]
    for r in rows:
        out.append("| " + " | ".join(fmt(c) for c in r) + " |")
    return "\n".join(out) + "\n"


def prog_of(suite):
    m = re.search(r"--prog\s+(\S+)", suite or "")
    return m.group(1) if m else "?"


def main(paths):
    lines = []
    for p in paths:
        with open(p) as f:
            for l in f:
                l = l.strip()
                if l:
                    lines.append(json.loads(l))
    out = []
    cases = {d["case"] for d in lines}
    out.append(f"# openfhe_pin summary\n\n{len(lines)} result lines, {len(cases)} cases, "
               f"{sum(1 for d in lines if d['ok'] is False)} FAIL.\n")
    by_scal = collections.Counter()
    seen = set()
    for d in lines:
        if d["case"] not in seen and "scaling" in d:
            seen.add(d["case"]); by_scal[(d.get("N"), d["scaling"])] += 1
    out.append("## Cases\n\n" + table(["N", "scaling", "cases"], [[n, s, c] for (n, s), c in sorted(by_scal.items(), key=str)]))

    # ---- per check
    agg = collections.defaultdict(lambda: [set(), 0, 0, 0, collections.Counter()])
    for d in lines:
        a = agg[d["check"]]
        a[0].add(d["case"])
        a[1 if d["ok"] is True else 2 if d["ok"] is False else 3] += 1
        a[4][d.get("impl", "?")] += 1
    out.append("## Per check\n\n" + table(
        ["check", "cases", "data points", "pass", "FAIL", "unchecked", "impl"],
        [[k, len(a[0]), a[1] + a[2] + a[3], a[1], a[2], a[3], ", ".join(f"{i}:{n}" for i, n in sorted(a[4].items()))]
         for k, a in sorted(agg.items())]))

    # ---- f
    fb = [d for d in lines if d["check"] == "f.bound" and d["ok"] is not None and "measured" in d]
    def ftab(keyname, keyf):
        g = collections.defaultdict(list)
        for d in fb:
            g[keyf(d)].append(slack(d["bound"], d["measured"]))
        return table([keyname, "points", "min slack (bits)", "median", "max"],
                     [[k, len(v), *mmm(v)] for k, v in sorted(g.items(), key=lambda kv: str(kv[0]))])
    out.append("## f. Analyzer bound vs measured centred phase (slack = log2(bound/measured))\n")
    out.append(f"{len(fb)} checked points; {sum(1 for d in fb if d['ok'] is False)} with measured > bound "
               f"(CRITICAL if any); {sum(1 for d in lines if d['check']=='f.bound' and d.get('wrapped'))} wrapped; "
               f"{sum(1 for d in lines if d['check']=='f.bound' and d['ok'] is None)} unchecked.\n")
    out.append("By operation:\n\n" + ftab("op", lambda d: d["op"]))
    out.append("By multiplicative depth:\n\n" + ftab("depth", lambda d: d.get("depth")))
    out.append("By scaling technique:\n\n" + ftab("scaling", lambda d: d.get("scaling")))
    out.append("By ring dimension:\n\n" + ftab("N", lambda d: d.get("N")))
    fd = [d for d in lines if d["check"] == "f.decrypt" and d["ok"] is not None]
    out.append("Switched phase at decryption vs `decBound`:\n\n" + table(
        ["points", "FAIL", "min slack", "median", "max"],
        [[len(fd), sum(1 for d in fd if d["ok"] is False), *mmm([slack(d["bound"], d["measured"]) for d in fd])]]))

    # ---- e
    out.append("## e. Phase contracts\n")
    es = [d for d in lines if d["check"] == "e.step"]
    g = collections.defaultdict(lambda: [0, 0, 0])
    for d in es:
        g[d["op"]][0 if d["ok"] is True else 1 if d["ok"] is False else 2] += 1
    out.append(table(["op", "pass", "FAIL", "unchecked"], [[k, *v] for k, v in sorted(g.items())]))
    ks = [d for d in es if d["op"] in ("relin", "keySwitch") and "measured" in d]
    rows = []
    for label, sel in (("honest", lambda d: not d.get("arbitrary")), ("adversarial (inputsArbitrary)", lambda d: d.get("arbitrary"))):
        for op in ("relin", "keySwitch"):
            v = [d for d in ks if sel(d) and d["op"] == op]
            if v:
                rows.append([label, op, len(v), sum(1 for d in v if d["ok"] is False),
                             *mmm([log2(d["measured"]) for d in v]),
                             *mmm([slack(d["bound"], d["measured"]) for d in v]),
                             *mmm([slack(d["ksBoundAt"], d["measured"]) for d in v if "ksBoundAt" in d]),
                             *mmm([slack(d["ksBoundAtCentred"], d["measured"]) for d in v if "ksBoundAtCentred" in d])])
    out.append("Key switching: measured ‖e‖∞ against `ksBudget` (the contract), `ksBoundAt` at the operand's level "
               "(canonical layout) and the centred-variant value (negative slack = the centred formula would be violated):\n\n" +
               table(["inputs", "op", "points", "FAIL", "min log2 ‖e‖", "median", "max",
                      "min slack vs ksBudget", "median", "max", "min slack vs ksBoundAt", "median", "max",
                      "min slack vs centred", "median", "max"], rows))
    ms = [d for d in es if d["op"] == "modSwitch" and "measured" in d]
    rows = []
    for parts in sorted({d.get("operandParts") for d in ms}, key=str):
        for comp in (False, True):
            v = [d for d in ms if d.get("operandParts") == parts and bool(d.get("composite")) == comp]
            if v:
                rows.append([parts, comp, len(v), sum(1 for d in v if d["ok"] is False),
                             *mmm([slack(d["bound"], d["measured"]) for d in v])])
    out.append("Modulus switching (`StepOK`): ‖δ‖∞ against q·budget:\n\n" +
               table(["operand parts", "composite", "points", "FAIL", "min slack (bits)", "median", "max"], rows))
    mp = [d for d in lines if d["check"] == "e.modswitch-parts" and "measured" in d]
    rows = []
    for parts in sorted({d.get("parts") for d in mp}, key=str):
        v = [d for d in mp if d.get("parts") == parts]
        rows.append([parts, len(v), sum(1 for d in v if d["ok"] is False), sum(1 for d in v if d["ok"] is None),
                     sum(1 for d in v if d.get("exceeds2part")), sum(1 for d in v if d.get("exceeds1part")),
                     *mmm([log2(d["measuredOverQ"]) for d in v]),
                     fmt(log2(v[0]["msBudgetOne"])), fmt(log2(v[0]["msBudget"])), fmt(log2(v[0]["msBudget3"]))])
    out.append("Every traced `ModReduceInternalInPlace`, by number of components of the operand "
               "(reference values in bits are those of the first case; they depend on N):\n\n" +
               table(["parts", "points", "FAIL", "unchecked", "exceeds 2-part budget", "exceeds 1-part budget",
                      "min log2(‖δ‖/q)", "median", "max", "msBudgetOne", "msBudget", "3-part value"], rows))

    # ---- d
    out.append("## d. Keys\n")
    dk = [d for d in lines if d["check"] == "d.key" and d.get("impl") == "forced"]
    g = collections.defaultdict(lambda: [0, 0, 0])
    for d in dk:
        a = g[(d["scaling"], d["op"])]
        a[0 if d["ok"] else 1] += 1
        if d["ok"]:
            a[2] = max(a[2], int(d["measured"]))
    out.append("`GadgetKeysOK` at every level (primary reading), max ‖e‖∞/t:\n\n" +
               table(["scaling", "key", "levels×keys pass", "FAIL", "max ‖e‖∞/t (bound 39)"],
                     [[s, k, *v] for (s, k), v in sorted(g.items())]))
    rs = [d for d in lines if d["check"] == "d.reading.summary"]
    g = collections.defaultdict(lambda: [0, 0])
    for d in rs:
        g[d["reading"]][0 if d["holdsAtEveryLevel"] else 1] += 1
    out.append("Readings of the stored keys (which `KeyValid` statement holds at every level):\n\n" +
               table(["reading", "keys: holds", "does not hold"], [[k, *v] for k, v in sorted(g.items())]))
    dl = [d for d in lines if d["check"] == "d.layout"]
    g = collections.defaultdict(lambda: [0, 0, set()])
    for d in dl:
        a = g[(d["scaling"], d.get("level"))]
        a[0 if d["ok"] else 1] += 1
        a[2].add(f"lean {d.get('leanDigits')} / openfhe {d.get('openfheDigits')}")
    out.append("Layout (digits per level; factor residue by residue):\n\n" +
               table(["scaling", "level", "pass", "FAIL", "digits"],
                     [[s, l, v[0], v[1], "; ".join(sorted(v[2]))] for (s, l), v in sorted(g.items(), key=str)]))
    pats = collections.Counter((d["scaling"], d.get("pattern")) for d in dl)
    out.append("Factor patterns of the stored keys (P = P mod q_i, 0 = zero; `|` before the special primes):\n\n" +
               table(["scaling", "pattern", "lines"], [[s, f"`{p}`", n] for (s, p), n in pats.most_common(12)]))
    lim = [d for d in lines if d["check"] == "d.limbs"]
    g = collections.Counter((d["scaling"], d["ok"], d.get("keyLimbs"), d.get("chainLimbs")) for d in lim)
    out.append(table(["scaling", "key limbs = chain ++ special", "key limbs", "chain limbs", "keys"],
                     [[s, ok, kl, cl, n] for (s, ok, kl, cl), n in sorted(g.items(), key=str)]))

    # ---- c
    out.append("## c. Fresh encryption\n")
    tl = [d for d in lines if d["check"] == "c.tail"]
    if tl:
        out.append(table(["encryptions", "max |u|", "max |e1|", "max |e2|", "max |e_pk|", "max ‖freshError‖∞"],
                         [[len(tl)] + [max(int(d[k]) for d in tl) for k in ("maxU", "maxE1", "maxE2", "maxEpk", "freshError")]]))
        for n in sorted({d["N"] for d in tl}):
            v = [d for d in tl if d["N"] == n]
            V = int(v[0]["varProxy"]); worst = int(v[0]["worstError"])
            fe = sorted(int(d["freshError"]) for d in v)
            out.append(f"N = {n}: {len(v)} encryptions; ‖freshError‖∞ min/median/max = {fe[0]}/{fe[len(fe)//2]}/{fe[-1]}; "
                       f"worstError = {worst}; √V = {math.sqrt(V):.1f}.\n")
            rows = []
            for i, k in enumerate(v[0]["kappa"]):
                eps = int(v[0]["eps"][i])
                ex = sum(1 for d in v if d["exceeds"][i])
                rows.append([k, eps, f"{eps / math.sqrt(V):.2f}", ex, f"{ex / len(v):.3g}", f"{2.0 ** -k:.3g}",
                             "yes" if ex / len(v) <= 2.0 ** -k else "NO (see note)"])
            out.append(table(["κ", "epsFor(V, 2N, κ)", "ε/√V", "encryptions with ‖freshError‖∞ ≥ ε",
                              "empirical fraction", "proved bound 2^-κ", "bound dominates"], rows))
            hist = collections.Counter(min(int(int(d["freshError"]) / math.sqrt(V) * 4), 39) for d in v)
            out.append("Histogram of ‖freshError‖∞/√V (bin width 0.25):\n\n" +
                       table(["bin", "count"], [[f"[{b/4:.2f}, {(b+1)/4:.2f})", hist[b]] for b in sorted(hist)]))
        out.append("Note: an empirical fraction above 2^-κ on a finite sample would refute the proved tail "
                   "bound only beyond sampling error; with n encryptions the resolution is 1/n.\n")
    ce = [d for d in lines if d["check"] == "c.encrypt" and d["ok"] is not None and d.get("impl") == "forced"]
    g = collections.defaultdict(lambda: [0, 0, 0, 0, float("-inf")])
    for d in ce:
        a = g[(d.get("ptEncoding"), d["scaling"])]
        a[0 if d["ok"] else 1] += 1
        a[2] += 1 if d.get("storedInZeroT") else 0
        a[3] += 1 if d.get("storedExceedsTMinus1") else 0
        a[4] = max(a[4], log2(d.get("storedNorm", "0")))
    out.append("`Spec.Encrypt.encrypt t b a p u e₁ e₂` (p = the stored plaintext polynomial) = OpenFHE's "
               "ciphertext, by plaintext encoding:\n\n" +
               table(["encoding", "scaling", "relation holds", "FAIL", "p in [0, t)", "‖p‖∞ > t − 1", "max log2 ‖p‖∞"],
                     [[e, sc, *v] for (e, sc), v in sorted(g.items(), key=str)]))
    pb = [d for d in lines if d["check"] == "c.ptbound"]
    g = collections.defaultdict(lambda: [0, 0, 0, 0, float("-inf")])
    for d in pb:
        a = g[(d["op"], d["scaling"])]
        a[0 if d["ok"] is True else 1 if d["ok"] is False else 2] += 1
        a[3] += 1 if d.get("exceedsTMinus1") else 0
        a[4] = max(a[4], log2(d["measured"]))
    out.append("Stored plaintext polynomial vs the DECLARED bound (null: the extractor refused the case, "
               "nothing is declared):\n\n" +
               table(["encoding", "scaling", "centred norm ≤ declared bound", "FAIL", "no declaration (null)",
                      "norm > t − 1", "max log2 centred norm"],
                     [[e, s, *v] for (e, s), v in sorted(g.items())]))

    # ---- paths
    out.append("## Extraction coverage (by exporter program)\n")
    cs = collections.defaultdict(lambda: {"prog": "?", "refused": False, "mismatch": False, "step": False, "why": ""})
    for d in lines:
        c = cs[d["case"]]
        c["prog"] = prog_of(d.get("suite"))
        if d["check"] == "load.prog" and d["ok"] is None:
            c["refused"] = True; c["why"] = d.get("why", "")[:160]
        if d["check"].startswith(("b.", "e.")) and d["ok"] is False:
            c["mismatch"] = True
        if d["check"] == "b.step":
            c["step"] = True
    g = collections.defaultdict(lambda: [0, 0, 0, 0, ""])
    for c in cs.values():
        a = g[c["prog"]]
        a[0] += 1
        if c["refused"]:
            a[1] += 1; a[4] = a[4] or c["why"]
        elif c["mismatch"] or c["step"]:
            a[3] += 1
        else:
            a[2] += 1
    out.append(table(["program", "cases", "refused by extract.py", "extracted + verified (b, e)", "extracted + MISMATCH", "example refusal"],
                     [[k, *v] for k, v in sorted(g.items())]))

    # ---- failures
    fails = [d for d in lines if d["ok"] is False]
    out.append(f"## Every FAIL line ({len(fails)})\n")
    if len(fails) > 400:
        g = collections.Counter((d["check"], d.get("op"), d.get("scaling"), (d.get("why") or "")[:100]) for d in fails)
        out.append(table(["check", "op", "scaling", "why", "lines"], [[*k, n] for k, n in g.most_common()]))
        out.append("(more than 400 FAIL lines: first 400 follow)\n")
    out.append("```")
    for d in fails[:400]:
        out.append(json.dumps(d, sort_keys=True))
    out.append("```")
    print("\n".join(out))


if __name__ == "__main__":
    if len(sys.argv) < 2:
        print(__doc__); sys.exit(2)
    main(sys.argv[1:])
