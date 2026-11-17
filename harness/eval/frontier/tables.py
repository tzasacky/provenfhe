#!/usr/bin/env python3
"""Tables of the certified frontier from OUT/results/*.jsonl (frontier.py, timing.py).

  tables.py OUT [--md OUT/tables.md] [--tsv OUT/frontier.tsv]

Every number is copied from the result files: verdicts and margins are plain fhe_check results on
the library's own runs; "ratio" is MEASURED (timing.py: pristine library, single thread, minimum of
the runs); "pred" is the time proxy (MODELLED). A row whose timing ran above the load limit is
marked "*".
"""
import argparse, json, math, os


def rowkey(r):
    return "|".join(str(r.get(k)) for k in ("family", "prog", "t", "d"))


def load(out, name):
    p = os.path.join(out, "results", f"{name}.jsonl")
    rows = {}
    if os.path.exists(p):
        for l in open(p):
            r = json.loads(l)
            rows[rowkey(r) if "family" in r else r["row"]] = r
    return rows


def pN(N):
    return f"2^{int(math.log2(N))}" if N else "-"


def verdict(c):
    if not c:
        return "-"
    v = c.get("verdict") or "?"
    if v.startswith("CERTIFIED"):
        return f"CERT {c.get('margin', 0):.1f}"
    if c.get("over") is not None:
        return f"over {c['over']:.1f}"
    return v[:12]


def shape_txt(p):
    if not p or "N" not in p:
        return "-"
    lb = p.get("limbBits") or []
    if lb and all(abs(b - lb[0]) < 0.5 for b in lb):
        q = f"{len(lb)}x{round(lb[0])}"
    elif lb:
        q = f"{round(lb[0])}+{len(lb) - 1}x{round(lb[1])}" if all(abs(b - lb[1]) < 0.5 for b in lb[1:-1] or lb[1:]) else "+".join(str(round(b)) for b in lb)
    else:
        q = "?"
    sp = f", P {p['special']}x60" if p.get("special") else ""
    return f"N={pN(p['N'])}, {q}{sp}"


def ratio_txt(tm, name):
    if not tm:
        return "n/m"
    if tm.get("identical"):
        return "1 (same)"
    r = (tm.get("ratio") or {}).get(name)
    if r is None:
        return "n/m"
    return f"{r:.2f}{'*' if tm.get('highLoad') else ''}"


def params_from_check(c):
    if not c:
        return None
    return {"N": c.get("N"), "limbBits": c.get("limbBits"), "special": len(c.get("specialBits") or []),
            "log2Q": c.get("log2Q")}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("out")
    ap.add_argument("--md")
    ap.add_argument("--tsv")
    a = ap.parse_args()
    md_path = a.md or os.path.join(a.out, "tables.md")
    tsv_path = a.tsv or os.path.join(a.out, "frontier.tsv")
    timing = load(a.out, "timing")
    md = []
    tsv = [["family", "prog", "t", "d", "default_N", "default_limbs", "default_special", "default_log2Q", "default_worst",
            "default_k128", "cert_N", "cert_limbs", "cert_special", "cert_log2Q", "cert_setting", "cert_margin",
            "dlog2Q", "dlimbs", "N_doubles", "ratio_measured", "least_log2Q_in_class", "k128_N", "k128_limbs", "k128_log2Q",
            "k128_ratio_measured", "e2e_validated", "timing_high_load"]]

    def tsvrow(r, dp, dw, dk, cp, cset, cm, lq, kp, rw, rk, e2e, hl):
        def g(p, k):
            return (p or {}).get(k, "")
        dl = len(g(dp, "limbBits") or []) if dp else ""
        cl = len(g(cp, "limbBits") or []) if cp else ""
        tsv.append([r["family"], r["prog"], r["t"], r["d"], g(dp, "N"), dl, g(dp, "special"), g(dp, "log2Q"), dw, dk,
                    g(cp, "N"), cl, g(cp, "special"), g(cp, "log2Q"), cset, cm,
                    (round(g(cp, "log2Q") - g(dp, "log2Q"), 2) if cp and dp and g(dp, "log2Q") != "" else ""),
                    (cl - dl if cp and dp else ""), (g(cp, "N") > g(dp, "N") if cp and dp else ""), rw, lq,
                    g(kp, "N"), len(g(kp, "limbBits") or []) if kp else "", g(kp, "log2Q"), rk, e2e, hl])

    # ---------------- BGV FIXEDMANUAL
    fm = load(a.out, "bgvfm")
    for prog in ("chain", "poly"):
        for t in (65537, 786433):
            rs = sorted([r for r in fm.values() if r["prog"] == prog and r["t"] == t], key=lambda r: r["d"])
            if not rs:
                continue
            md += [f"\n### BGV FIXEDMANUAL, {prog}, t = {t}\n",
                   "| d | OpenFHE default | default: worst / k128 | certified, digits kept (e2e) | dbits | ratio | certified, least predicted time (e2e) | ratio | certified k128 (e2e) | ratio |",
                   "|---|---|---|---|---|---|---|---|---|---|"]
            for r in rs:
                tm = timing.get(rowkey(r))
                dflt = r["default"]
                dp = dflt.get("params")
                cells = []
                for tag in ("rec_keep", "rec_any", "rec_any_k128"):
                    e = r.get(tag) or {}
                    rec = e.get("rec") or {}
                    ee = e.get("e2e") or {}
                    ch = ee.get("check") or {}
                    if rec.get("verdict") != "CERTIFIED":
                        cells.append(("none" if "plaintext modulus" in (rec.get("summary") or "") or rec.get("verdict") == "NOT CERTIFIED" else rec.get("verdict", "-"), None, ch, ee))
                        continue
                    ok = (ch.get("verdict") or "").startswith("CERTIFIED") and ee.get("valueCheck") and ee.get("cleartextCheck") and ee.get("primesEqual") and ee.get("specialEqual")
                    txt = f"N={pN(rec['N'])}, {rec['firstModSize']}+{len(rec['limbs']) - 1}x{rec['scalingModSize']}, dnum {rec['digits']}, P {len(rec['special'])}x60{'' if ok else ' (E2E FAILED)'}"
                    cells.append((txt, rec, ch, ee))
                keep, anyc, k128 = cells
                db = round(keep[1]["log2Q"] - dp["log2Q"]) if keep[1] and dp else "-"
                md.append(f"| {r['d']} | {shape_txt(dp)} | {verdict(dflt.get('worst'))} / {verdict(dflt.get('k128'))} | {keep[0]} | {db:+} | {ratio_txt(tm, 'certKeepDigits')} | {anyc[0]} | {ratio_txt(tm, 'certWorst')} | {k128[0]} | {ratio_txt(tm, 'certK128')} |"
                          if isinstance(db, int) else
                          f"| {r['d']} | {shape_txt(dp)} | {verdict(dflt.get('worst'))} / {verdict(dflt.get('k128'))} | {keep[0]} | - | {ratio_txt(tm, 'certKeepDigits')} | {anyc[0]} | {ratio_txt(tm, 'certWorst')} | {k128[0]} | {ratio_txt(tm, 'certK128')} |")
                cp = params_from_check(anyc[2]) if anyc[1] else None
                kp = params_from_check(k128[2]) if k128[1] else None
                if cp and anyc[1]:
                    cp["special"] = len(anyc[1]["special"])
                tsvrow(r, dp, verdict(dflt.get("worst")), verdict(dflt.get("k128")), cp,
                       (f"firstbits {anyc[1]['firstModSize']} qbits {anyc[1]['scalingModSize']} dnum {anyc[1]['digits']} ringdim {anyc[1]['N']}" if anyc[1] else "none"),
                       (anyc[2] or {}).get("margin", ""), "", kp, ratio_txt(tm, "certWorst"), ratio_txt(tm, "certK128"),
                       all((c[2] or {}).get("verdict", "").startswith("CERTIFIED") for c in cells if c[1]), bool(tm and tm.get("highLoad")))

    # ---------------- library-in-the-loop families
    for section, title in (("bgvauto", "BGV {scal}"), ("bfv", "BFV {mult} / {ks}")):
        rows = load(a.out, section)
        fams = sorted({r["family"] for r in rows.values()})
        for fam in fams:
            for prog in ("chain", "poly"):
                for t in (65537, 786433):
                    rs = sorted([r for r in rows.values() if r["family"] == fam and r["prog"] == prog and r["t"] == t], key=lambda r: r["d"])
                    if not rs:
                        continue
                    md += [f"\n### {fam}, {prog}, t = {t}\n",
                           "| d | OpenFHE default | default: worst / k128 | cheapest certified (worst) | setting | margin | dbits | dlimbs | ratio | least log Q in that class | cheapest certified k128 | ratio |",
                           "|---|---|---|---|---|---|---|---|---|---|---|---|"]
                    for r in rs:
                        tm = timing.get(rowkey(r))
                        dflt = r.get("default") or {}
                        dp = dflt.get("params")
                        s = r.get("search") or {}
                        b = s.get("best") or {}
                        w, k = b.get("worst"), b.get("k128")
                        lq = s.get("leastQ")
                        if section == "bfv":
                            cset = (lambda c: f"depth {c['depth']}, qbits {c['qbits']}" + (f", dnum {c['dnum']}" if c.get('dnum') else ""))
                        else:
                            cset = (lambda c: f"depth {c['depth']}" + (f", EvalAddCount {c['evaladd']}" if c.get('evaladd') else "") + (f", KeySwitchCount {c['kscount']}" if c.get('kscount') else ""))
                        if w:
                            wp = w["params"]
                            db = round(wp["log2Q"] - dp["log2Q"]) if dp and "log2Q" in dp else None
                            dl = wp["limbs"] - dp["limbs"] if dp and "limbs" in dp else None
                            wc = shape_txt(wp)
                            lqt = f"{lq['log2Q']:.0f} ({cset(lq['cfg'])})" if lq else "-"
                            setting = cset(w["cfg"])
                            mg = (w.get("worst") or {}).get("margin")
                        else:
                            db = dl = None
                            wc, setting, mg, lqt = "none found", "-", None, "-"
                        md.append(f"| {r['d']} | {shape_txt(dp)} | {verdict(dflt.get('worst'))} / {verdict(dflt.get('k128'))} | {wc} | {setting} | {'' if mg is None else f'{mg:.1f}'} | {'' if db is None else f'{db:+}'} | {'' if dl is None else f'{dl:+}'} | {ratio_txt(tm, 'certWorst') if w else '-'} | {lqt} | {shape_txt(k['params']) if k else 'none found'} | {ratio_txt(tm, 'certK128') if k else '-'} |")
                        tsvrow(r, dp, verdict(dflt.get("worst")), verdict(dflt.get("k128")), w["params"] if w else None,
                               cset(w["cfg"]) if w else "none", mg if mg is not None else "", lq["log2Q"] if lq else "",
                               k["params"] if k else None, ratio_txt(tm, "certWorst") if w else "", ratio_txt(tm, "certK128") if k else "",
                               bool(w and w.get("valueCheck") and w.get("cleartextCheck")), bool(tm and tm.get("highLoad")))
    open(md_path, "w").write("\n".join(md) + "\n")
    with open(tsv_path, "w") as f:
        for row in tsv:
            f.write("\t".join(str(x) for x in row) + "\n")
    print("wrote", md_path, tsv_path, len(tsv) - 1, "rows")


if __name__ == "__main__":
    main()
