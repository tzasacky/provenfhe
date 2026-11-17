#!/usr/bin/env python3
"""UNTRUSTED. Generates suites of openfhe-pin cases in parallel (deterministic: every case's seed
is derived from its name) by running export_case.sh, and writes <out>/MANIFEST.tsv.

  gen_matrix.py --suite smoke|fixtures|tiny|mid|default|probe --out DIR [--jobs J] [--list]
                [--only SUBSTR] [--selftest]

MANIFEST.tsv columns: case, args, exit (pin_export's status), extract (ok | FAIL: <message>),
exceptions (number of OpenFHE exceptions caught inside the program, see pin.json notes),
bytes (whole case directory), polys_bytes, selftest (with --selftest: ok | FAIL | skipped).
"""
import argparse
import json
import os
import subprocess
import sys
import zlib
from concurrent.futures import ThreadPoolExecutor

HERE = os.path.dirname(os.path.abspath(__file__))
TECHS = ["FIXEDMANUAL", "FIXEDAUTO", "FLEXIBLEAUTO", "FLEXIBLEAUTOEXT"]
AUTO = TECHS[1:]
MSGS = ["random", "max", "alt", "witness", "small"]
# The committed fixtures: "alt" and "witness" are CoefPacked plaintexts, which the extractor
# refuses (only packed plaintexts are mapped); a quarter of the rotation, so that most cases
# keep their extracted program (checks b, e, f) and the refusal stays covered.
FMSGS = ["random", "max", "small", "alt", "random", "small", "max", "witness"]
BASIC = ["chain", "dot", "rot", "plain", "plainlvl", "lr", "rotsum", "innerprod"]
THREE = ["threepart:" + v for v in ("modreduce", "mul3x2", "mul3x3", "square", "add3x2", "rot", "mulplain",
                                    "autoreduce")]
PATHS = ["paths:" + v for v in ("fastrot", "multmany", "compress", "relinearize", "mutable", "negate", "coefpacked",
                                "string", "evalsum", "ptfirst", "multrelin", "automorphism", "scalar")]
MIXED = ["mixed:" + v for v in ("a", "b", "c", "d")]


def seed_of(name):
    return zlib.crc32(name.encode()) + 1


def case(name, **kw):
    args = ["--seed", str(seed_of(name))]
    if kw.get("prog") == "paths:string":
        kw["t"] = 256  # StringEncoding requires t = 256 (v1.6.1 stringencoding.cpp:51)
    for k, v in kw.items():
        if v is not None:
            args += ["--" + k, str(v)]
    return name, args


def short(t):
    return {"FIXEDMANUAL": "fm", "FIXEDAUTO": "fa", "FLEXIBLEAUTO": "xa", "FLEXIBLEAUTOEXT": "xe"}[t]


def pname(p):
    return p.replace(":", "-")


def suite_smoke():
    # threepart:modreduce: a modulus switch of a 3-component value (the mutant `ms-parts`)
    return [case(f"n16_{short(t)}_d2_{pname(p)}", n=16, scal=t, depth=2, prog=p, msg="random")
            for t in TECHS for p in ("chain", "ops", "rotsum", "threepart:modreduce")]


def suite_probe():
    out = []
    for t in TECHS:
        for p in BASIC + ["ops", "opsnn", "random"] + THREE + PATHS + MIXED:
            out.append(case(f"n16_{short(t)}_d3_{pname(p)}", n=16, scal=t, depth=3, prog=p, msg="random", len=20))
        for k in range(40):
            out.append(case(f"n16_{short(t)}_d3_randomcore_{k:02d}", n=16, scal=t, depth=3, prog="random",
                            msg="random", len=30, menu="core"))
    return out


def fix_depth(n, t, d):
    """OpenFHE v1.6.1 refuses to generate parameters for N = 64, FLEXIBLEAUTOEXT, depth 1 or 2
    (rns-cryptoparameters.cpp:161, "EstimateLogP() failure: expected sizeP [1], but got sizeP [2]");
    those cases are generated at depth 3."""
    return 3 if (n == 64 and t == "FLEXIBLEAUTOEXT" and d < 3) else d


def suite_fixtures():
    out = []
    i = 0
    for n in (16, 64):
        for ti, t in enumerate(TECHS):
            for pi, p in enumerate(BASIC + ["ops", "opsnn"]):
                if n == 64 and (pi + ti) % 2:
                    continue  # N = 64: each program under two of the four techniques (archive size)
                m = FMSGS[i % len(FMSGS)]
                i += 1
                if p == "innerprod" and m in ("max", "random"):
                    m = "small"  # innerprod sets batch size 8; N-slot vectors do not fit
                d = fix_depth(n, t, 2)
                out.append(case(f"n{n}_{short(t)}_d{d}_{pname(p)}_{m}", n=n, scal=t, depth=d, prog=p, msg=m))
    for t in TECHS:
        for d in (1, 3):
            out.append(case(f"n16_{short(t)}_d{d}_chain_random", n=16, scal=t, depth=d, prog="chain", msg="random"))
    # referee additions: 3-part behaviour, uncovered API paths, mixed levels.
    # N = 16: every program under every technique; N = 64: every program once, techniques rotating
    # (keeps the committed archive small).
    for n in (16, 64):
        for ti, t in enumerate(TECHS):
            for pi, p in enumerate(THREE + PATHS):
                if n == 64 and (pi % 4 != ti or p in ("paths:scalar", "threepart:rot")):
                    continue
                m = "small" if p in ("paths:evalsum",) else FMSGS[i % len(FMSGS)]
                i += 1
                d = fix_depth(n, t, 2)
                out.append(case(f"n{n}_{short(t)}_d{d}_{pname(p)}_{m}", n=n, scal=t, depth=d, prog=p, msg=m))
        for ti, t in enumerate(AUTO):
            for pi, p in enumerate(MIXED):
                if n == 64 and pi % 3 != ti:
                    continue
                d = 4 if p in ("mixed:c", "mixed:d") else 3
                m = FMSGS[i % len(FMSGS)]
                i += 1
                out.append(case(f"n{n}_{short(t)}_d{d}_{pname(p)}_{m}", n=n, scal=t, depth=d, prog=p, msg=m))
    # longer ciphertexts with relinearization keys for s^3, s^4 (SetMaxRelinSkDeg)
    for t in TECHS:
        for p, k in (("threepart:mul3x2", 3), ("threepart:mul3x3", 4), ("paths:multmany", 3)):
            out.append(case(f"n16_{short(t)}_d3_{pname(p)}_relindeg{k}_small", n=16, scal=t, depth=3, prog=p,
                            msg="small", relindeg=k))
    for k in range(64):
        t = TECHS[k % 4]
        d = 1 + (k // 4) % 3
        m = FMSGS[(k // 12 + k) % len(FMSGS)]
        menu = "all" if k % 5 == 4 else "core"
        out.append(case(f"n16_{short(t)}_d{d}_random{menu}_{m}_{k:03d}", n=16, scal=t, depth=d, prog="random", msg=m,
                        len=8 + 2 * (k % 7), menu=menu))
    big = [(256, "FIXEDMANUAL", "chain", 2), (256, "FLEXIBLEAUTOEXT", "opsnn", 1), (256, "FIXEDAUTO", "rotsum", 1),
           (256, "FLEXIBLEAUTO", "random", 2), (1024, "FIXEDMANUAL", "chain", 1), (1024, "FLEXIBLEAUTOEXT", "chain", 1)]
    for n, t, p, d in big:
        out.append(case(f"n{n}_{short(t)}_d{d}_{pname(p)}_random", n=n, scal=t, depth=d, prog=p, msg="random", len=6, menu="core"))
    return out


def suite_tiny():
    out = []
    for n in (16, 32, 64):
        for t in TECHS:
            for d in (1, 2, 3):
                for m in MSGS:
                    for k in range(23):
                        menu = "all" if k >= 17 else "core"  # 17 core + 6 all per combination
                        out.append(case(f"n{n}_{short(t)}_d{d}_random{menu}_{m}_{k:02d}", n=n, scal=t, depth=d,
                                        prog="random", msg=m, len=8 + 4 * (k % 9), menu=menu))
    # the fixed programs (referee additions included) at N = 32 as well
    for t in TECHS:
        for p in BASIC + ["ops", "opsnn"] + THREE + PATHS + (MIXED if t != "FIXEDMANUAL" else []):
            d = 4 if p in ("mixed:c", "mixed:d") else 3
            m = "small" if p in ("innerprod", "paths:evalsum") else "random"
            out.append(case(f"n32_{short(t)}_d{d}_{pname(p)}_{m}", n=32, scal=t, depth=d, prog=p, msg=m))
    return out


def suite_mid():
    out = []
    progs = BASIC + ["ops", "opsnn", "random"] + THREE + PATHS + MIXED
    ns = (256, 1024, 4096)
    for i, p in enumerate(progs):
        t = TECHS[i % 4]
        if p.startswith("mixed:") and t == "FIXEDMANUAL":
            t = "FLEXIBLEAUTOEXT"
        n = ns[i % 3]
        d = 4 if p in ("mixed:c", "mixed:d") else 3 if p.startswith("mixed:") else 2
        m = "small" if p in ("innerprod", "paths:evalsum") else MSGS[i % 5]
        out.append(case(f"n{n}_{short(t)}_d{d}_{pname(p)}_{m}", n=n, scal=t, depth=d, prog=p, msg=m, len=16,
                        menu="core" if p == "random" else None))
    for j, t in enumerate(TECHS):  # random programs: one per technique with each menu
        for menu in ("core", "all"):
            n = ns[(j + (menu == "all")) % 3]
            out.append(case(f"n{n}_{short(t)}_d3_random{menu}_random", n=n, scal=t, depth=3, prog="random",
                            msg="random", len=24, menu=menu))
    # every technique at every size once more, with chain
    for n in ns:
        for t in TECHS:
            name = f"n{n}_{short(t)}_d2_chain_random"
            if all(c[0] != name for c in out):
                out.append(case(name, n=n, scal=t, depth=2, prog="chain", msg="random"))
    return out


def suite_default():
    out = []
    for t in TECHS:
        for d in (1, 2, 3):
            out.append(case(f"def_{short(t)}_d{d}_chain", scal=t, depth=d, prog="chain", msg="random"))
        out.append(case(f"def_{short(t)}_d2_ops", scal=t, depth=2, prog="ops", msg="random"))
        out.append(case(f"def_{short(t)}_d2_rotsum", scal=t, depth=2, prog="rotsum", msg="random"))
        out.append(case(f"def_{short(t)}_d2_plain", scal=t, depth=2, prog="plain", msg="random"))
        out.append(case(f"def_{short(t)}_d3_plain", scal=t, depth=3, prog="plain", msg="max"))
    out.append(case("def_xe_d2_opsnn", scal="FLEXIBLEAUTOEXT", depth=2, prog="opsnn", msg="random"))
    out.append(case("def_xe_d2_threepart-add3x2", scal="FLEXIBLEAUTOEXT", depth=2, prog="threepart:add3x2", msg="random"))
    out.append(case("def_xe_d2_paths-ptfirst", scal="FLEXIBLEAUTOEXT", depth=2, prog="paths:ptfirst", msg="random"))
    out.append(case("def_xe_d3_mixed-a", scal="FLEXIBLEAUTOEXT", depth=3, prog="mixed:a", msg="random"))
    out.append(case("def_default_d2_chain", scal="default", depth=2, prog="chain", msg="random"))
    return out


SUITES = {"smoke": suite_smoke, "fixtures": suite_fixtures, "tiny": suite_tiny, "mid": suite_mid,
          "default": suite_default, "probe": suite_probe}


def dir_size(d):
    return sum(os.path.getsize(os.path.join(d, f)) for f in os.listdir(d))


def run(out, name, args, selftest):
    d = os.path.join(out, name)
    env = dict(os.environ, OMP_NUM_THREADS="1")
    r = subprocess.run([os.path.join(HERE, "export_case.sh"), d] + args, capture_output=True, text=True, env=env)
    extract = "ok"
    for line in r.stdout.splitlines():
        if line.startswith("EXTRACT-FAIL "):
            extract = "FAIL: " + line.split(" ", 2)[2]
        elif line.startswith("EXPORT-FAIL "):
            extract = "not run (" + line.split(" ", 2)[2] + ")"
    exc, polys, st = "", 0, "skipped"
    if r.returncode == 0:
        try:
            pin = json.load(open(os.path.join(d, "pin.json")))
            exc = str(sum(1 for n in pin["notes"] if n.startswith("EXC ")))
        except Exception as e:  # an unreadable pin.json is an exporter bug
            exc = "pin.json unreadable: " + str(e)
        polys = os.path.getsize(os.path.join(d, "polys.txt"))
        if selftest:
            s = subprocess.run([sys.executable, "-I", os.path.join(HERE, "selftest.py"), d, "--json"],
                               capture_output=True, text=True)
            open(os.path.join(d, "selftest.json"), "w").write(s.stdout)
            st = "ok" if s.returncode == 0 else "FAIL"
    size = dir_size(d) if os.path.isdir(d) else 0
    return [name, " ".join(args), str(r.returncode), extract.replace("\t", " "), exc, str(size), str(polys), st]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--suite", required=True, choices=sorted(SUITES))
    ap.add_argument("--out", required=True)
    ap.add_argument("--jobs", type=int, default=16)
    ap.add_argument("--list", action="store_true")
    ap.add_argument("--only")
    ap.add_argument("--selftest", action="store_true")
    a = ap.parse_args()
    cases = SUITES[a.suite]()
    if a.only:
        cases = [c for c in cases if a.only in c[0]]
    assert len({c[0] for c in cases}) == len(cases), "duplicate case names"
    if a.list:
        for n, args in cases:
            print(n, " ".join(args))
        return
    jobs = max(1, min(a.jobs, 32))
    os.makedirs(a.out, exist_ok=True)
    with ThreadPoolExecutor(jobs) as ex:
        rows = list(ex.map(lambda c: run(a.out, c[0], c[1], a.selftest), cases))
    with open(os.path.join(a.out, "MANIFEST.tsv"), "w") as f:
        f.write("case\targs\texit\textract\texceptions\tbytes\tpolys_bytes\tselftest\n")
        for r in rows:
            f.write("\t".join(r) + "\n")
    nfail = sum(1 for r in rows if r[2] != "0")
    nx = sum(1 for r in rows if r[3].startswith("FAIL"))
    nst = sum(1 for r in rows if r[7] == "FAIL")
    print(f"{a.suite}: {len(rows)} cases, {nfail} export failures, {nx} extraction failures, "
          f"{nst} selftest failures, {sum(int(r[5]) for r in rows)} bytes -> {a.out}/MANIFEST.tsv")


if __name__ == "__main__":
    main()
