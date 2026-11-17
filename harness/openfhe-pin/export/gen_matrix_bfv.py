#!/usr/bin/env python3
"""UNTRUSTED. Generates suites of BFV openfhe-pin cases in parallel (deterministic: every case's
seed is derived from its name) by running export_case_bfv.sh, and writes <out>/MANIFEST.tsv.

  gen_matrix_bfv.py --suite sample|bfv-fixtures|bfv-mid|bfv-real|bfv-adv --out DIR [--jobs J]
                    [--list] [--only SUBSTR] [--selftest]

MANIFEST.tsv columns: case, args, exit (pin_export_bfv's status), extract (ok | FAIL: <message>),
exceptions (number of OpenFHE exceptions caught inside the program, see pin.json notes),
bytes (whole case directory), polys_bytes, selftest (with --selftest: ok | FAIL | skipped),
N, L (limbs of Q), mult, ks, enc, drops (traced levelsDropped: products+relinearizations/key
switches with a positive drop, from the extracted program's provenance), seconds (wall time of
export + extraction), decmismatch (with --selftest: coefficients where the library's Decrypt
differs from exact rounding of the phase / their largest distance from a rounding boundary),
finalmargin (with --selftest: over the final ciphertexts, the smallest distance of t*phase/Q_l from
a rounding boundary; 0.5 = no noise, below 0.25 = the output is not reliably decryptable).
"""
import argparse
import json
import os
import subprocess
import sys
import time
import zlib
from concurrent.futures import ThreadPoolExecutor

HERE = os.path.dirname(os.path.abspath(__file__))
MULTS = ["HPS", "HPSPOVERQ", "HPSPOVERQLEVELED", "BEHZ"]
KSS = ["HYBRID", "BV"]
SHORT = {"HPS": "hps", "HPSPOVERQ": "poq", "HPSPOVERQLEVELED": "lev", "BEHZ": "behz", "default": "def",
         "HYBRID": "hy", "BV": "bv"}
T_SMALL = 65537
# primes t = 1 mod 2N near 2^20 (packed encoding needs t = 1 mod 2N)
T_BIG = 1032193      # 63 * 2^14 + 1: 1 mod 2N for N <= 8192
T_BIG17 = 786433     # 3 * 2^18 + 1: 1 mod 2N for N <= 131072
T_17 = 1179649       # 9 * 2^17 + 1: a prime of the form k*2^17 + 1, 1 mod 2N for N <= 65536


def seed_of(name):
    return zlib.crc32(name.encode()) + 1


def case(name, env=None, **kw):
    args = ["--seed", str(seed_of(name))]
    for k, v in kw.items():
        if v is not None:
            args += ["--" + k, str(v)]
    return name, args, env or {}


def nm(n, mult, ks, d, prog, *extra):
    return "_".join([f"bfv_n{n}", SHORT[mult], SHORT[ks], f"d{d}", prog.replace(":", "-")] + [str(x) for x in extra])


def suite_sample():
    out = []
    for m in MULTS:
        for k in KSS:
            # every technique x key switching: chain (depth 2), dot, plain, compress
            out.append(case(nm(16, m, k, 2, "chain"), n=16, mult=m, ks=k, depth=2, prog="chain", msg="random"))
            out.append(case(nm(16, m, k, 2, "dot"), n=16, mult=m, ks=k, depth=2, prog="dot", msg="random"))
            out.append(case(nm(16, m, k, 2, "plain"), n=16, mult=m, ks=k, depth=2, prog="plain", msg="small"))
            if m in ("HPSPOVERQ", "HPSPOVERQLEVELED"):
                out.append(case(nm(16, m, k, 2, "compress"), n=16, mult=m, ks=k, depth=2, prog="compress",
                                msg="random"))
    # a real internal drop on products, relinearizations and rotation key switches
    out.append(case("bfv_n16_lev_bv_d4_levels_q30", n=16, mult="HPSPOVERQLEVELED", ks="BV", depth=4, qbits=30,
                    prog="levels", msg="small"))
    out.append(case("bfv_n16_lev_hy_d4_levels_q30", n=16, mult="HPSPOVERQLEVELED", ks="HYBRID", depth=4, qbits=30,
                    prog="levels", msg="small"))
    out.append(case("bfv_n16_def_def_d2_chain_default", n=16, depth=2, prog="chain", msg="random"))
    out.append(case("bfv_n16_poq_bv_d2_chain_extended", n=16, mult="HPSPOVERQ", ks="BV", enc="EXTENDED", depth=2,
                    prog="chain", msg="random"))
    out.append(case("bfv_n16_hps_hy_d2_dot_extended", n=16, mult="HPS", ks="HYBRID", enc="EXTENDED", depth=2,
                    prog="dot", msg="random"))
    out.append(case("bfv_n16_behz_hy_d2_plain_max", n=16, mult="BEHZ", ks="HYBRID", depth=2, prog="plain", msg="max"))
    out.append(case("bfv_n16_hps_bv_d2_norelin", n=16, mult="HPS", ks="BV", depth=2, prog="norelin", msg="random"))
    out.append(case("bfv_n16_poq_hy_d2_addsub", n=16, mult="HPSPOVERQ", ks="HYBRID", depth=2, prog="addsub",
                    msg="random"))
    # refused by the extractor
    out.append(case("bfv_n16_hps_bv_d2_coefpk", n=16, mult="HPS", ks="BV", depth=2, prog="coefpk", msg="random"))
    out.append(case("bfv_n16_lev_bv_d2_threepart", n=16, mult="HPSPOVERQLEVELED", ks="BV", depth=2, prog="threepart",
                    msg="random"))
    out.append(case("bfv_n16_behz_bv_d2_compress", n=16, mult="BEHZ", ks="BV", depth=2, prog="compress",
                    msg="random"))  # Compress throws under BEHZ
    return out


def _add(out, n, m, k, d, prog, *tag, **kw):
    """One case; m / k = "default": the setter is never called; n = None: OpenFHE picks the ring dimension."""
    if prog == "ops" and "progdepth" not in kw:
        # the `ops` program has two products in sequence after a sum of rotations: parameters one level deeper
        kw["progdepth"] = d
        d += 1
    name = "_".join(["bfv_" + (f"n{n}" if n else "nsec"), SHORT[m], SHORT[k], f"d{d}", prog.replace(":", "-")]
                    + [str(x) for x in tag])
    env = kw.pop("env", None)
    out.append(case(name, env, n=n, mult=None if m == "default" else m, ks=None if k == "default" else k, depth=d,
                    prog=prog, **kw))


QB = [60, 30, 45]
MS = ["random", "max", "small"]
POQ = ("HPSPOVERQ", "HPSPOVERQLEVELED")
# (qbits, ks, depth, progdepth) on which HPSPOVERQLEVELED drops limbs in products, relinearizations and
# rotation key switches (checked from the trace: MANIFEST column "drops")
LEVELS = [(30, "BV", 4, 4), (30, "HYBRID", 4, 4), (45, "BV", 6, 5), (45, "HYBRID", 4, 4), (60, "BV", 6, 5),
          (60, "HYBRID", 6, 5)]


def suite_fixtures():
    """The committed BFV fixtures (fixtures/fixtures-bfv.tar.xz): N = 16 mostly, some N = 64."""
    out = []
    i = 0
    core = [("chain", 1), ("chain", 2), ("chain", 3), ("square", 2), ("dot", 2), ("rot", 1), ("rotsum", 2),
            ("plain", 2), ("addsub", 1), ("norelin", 2), ("ops", 2), ("random", 2), ("random", 3), ("coefpacked", 2)]
    for m in MULTS:
        for k in KSS:
            progs = core + ([("compress", 2), ("compress", 3)] if m in POQ else [])
            for p, d in progs:
                qb, msg = QB[i % 3], MS[(i // 3 + i) % 3]
                i += 1
                _add(out, 16, m, k, d, p, f"q{qb}", msg, qbits=qb, msg=msg, len=14 if p == "random" else None)
    # every operation on unrelinearised products the extractor maps (coverage.py), per technique; and
    # Compress to the same number of limbs (a `copy`) where Compress is supported
    for m in MULTS:
        for k in KSS:
            _add(out, 16, m, k, 2, "norelin2", "random", msg="random")
    for m in POQ:
        _add(out, 16, m, "HYBRID", 2, "compress", "same", "random", msg="random", towers=2)
    # adversarial inputs at N = 64 (hand-built ciphertexts at the input bound; inputsArbitrary): the
    # sharpest recorded cases for the multiplication rule of the reference analyzer (mutants.sh)
    for m in MULTS:
        for v in ("handbuilt", "handbuiltkey", "handbuiltsq"):
            _add(out, 64, m, "HYBRID", 2, "advmul:" + v, msg="max", env={"EXTRACT_FLAGS": "--assume-fresh-inputs"})
        _add(out, 64, m, "HYBRID", 2, "advplain:handmax", msg="max", env={"EXTRACT_FLAGS": "--assume-fresh-inputs"})
    # library defaults (no technique setter called): HPSPOVERQLEVELED, BV, STANDARD, 60-bit primes
    for p, d in [("chain", 1), ("chain", 2), ("chain", 3), ("chain", 4), ("dot", 2), ("plain", 2), ("compress", 3),
                 ("ops", 2), ("random", 3), ("rotsum", 2)]:
        _add(out, 16, "default", "default", d, p, "random", msg="random", len=14 if p == "random" else None)
    # depth 4
    for j, m in enumerate(MULTS):
        for k in KSS:
            _add(out, 16, m, k, 4, "chain", f"q{QB[j % 3]}", "random", qbits=QB[j % 3], msg="random")
    # internal drops of HPSPOVERQLEVELED
    for qb, k, d, pd in LEVELS:
        _add(out, 16, "HPSPOVERQLEVELED", k, d, "levels", f"q{qb}", "small", qbits=qb, progdepth=pd, msg="small")
    _add(out, 16, "default", "default", 6, "levels", "q30", "random", qbits=30, progdepth=5, msg="random")
    # BV with a digit size (base-2^w digits; the extractor refuses it, the keys are still checked)
    for m, w, p in [("HPS", 20, "chain"), ("HPSPOVERQLEVELED", 30, "dot"), ("BEHZ", 10, "chain"),
                    ("HPSPOVERQ", 16, "rot"), ("HPS", 30, "dot"), ("BEHZ", 20, "plain")]:
        _add(out, 16, m, "BV", 2, p, f"w{w}", "random", digitsize=w, msg="random")
    # EXTENDED encryption
    for j, m in enumerate(MULTS):
        _add(out, 16, m, KSS[j % 2], 2, "chain", "ext", "random", enc="EXTENDED", msg="random")
        _add(out, 16, m, KSS[(j + 1) % 2], 2, ["dot", "plain", "rotsum", "addsub"][j], "ext", MS[j % 3], enc="EXTENDED",
             msg=MS[j % 3])
    # a larger plaintext modulus (t = 786433 = 3*2^18 + 1)
    for j, m in enumerate(MULTS):
        _add(out, 16, m, KSS[j % 2], 2, "chain", "t786433", "random", t=T_BIG17, msg="random")
        _add(out, 16, m, KSS[(j + 1) % 2], 2, ["plain", "dot", "ops", "plain"][j], "t786433", MS[(j + 1) % 3], t=T_BIG17,
             msg=MS[(j + 1) % 3])
    # programs the extractor refuses, and what OpenFHE throws
    for m, k in [("HPS", "BV"), ("HPSPOVERQLEVELED", "HYBRID")]:
        for p in ("innerprod", "symenc", "threepart", "nocheck", "coefpk"):
            _add(out, 16, m, k, 2, p, "random", msg="random")
    _add(out, 16, "HPS", "BV", 2, "chain", "gaussian", skdist="GAUSSIAN", msg="random")
    _add(out, 16, "HPS", "BV", 2, "compress", "random", msg="random")
    _add(out, 16, "BEHZ", "HYBRID", 2, "compress", "random", msg="random")
    _add(out, 16, "HPSPOVERQ", "BV", 2, "compress", "ext", "random", enc="EXTENDED", msg="random")
    # random programs over the whole menu
    for j, m in enumerate(MULTS):
        for r in range(2):
            _add(out, 16, m, KSS[(j + r) % 2], 3, "random", f"all{r}", MS[r], menu="all", len=16, msg=MS[r])
            _add(out, 16, m, KSS[(j + r + 1) % 2], 2, "random", f"core{r}", MS[r + 1], menu="core", len=16, msg=MS[r + 1],
                 qbits=QB[(j + r) % 3])
    # a 3-part product plus / minus a 2-part ciphertext (mixed formats in the library)
    for j, m in enumerate(MULTS):
        _add(out, 16, m, KSS[j % 2], 2, "mixadd", "random", msg="random")
    # zero messages
    _add(out, 16, "HPS", "BV", 2, "chain", "zero", msg="zero")
    _add(out, 16, "HPSPOVERQLEVELED", "HYBRID", 2, "dot", "zero", msg="zero")
    # N = 64
    for j, m in enumerate(MULTS):
        _add(out, 64, m, KSS[j % 2], 2, "chain", "random", msg="random")
    _add(out, 64, "HPS", "HYBRID", 2, "dot", "random", msg="random")
    _add(out, 64, "BEHZ", "BV", 2, "plain", "max", msg="max")
    _add(out, 64, "HPSPOVERQ", "HYBRID", 3, "compress", "q30", "random", qbits=30, msg="random")
    _add(out, 64, "HPSPOVERQLEVELED", "BV", 4, "levels", "q30", "small", qbits=30, msg="small")
    _add(out, 64, "HPSPOVERQLEVELED", "HYBRID", 4, "levels", "q30", "small", qbits=30, msg="small")
    _add(out, 64, "default", "default", 2, "rotsum", "random", msg="random")
    _add(out, 64, "BEHZ", "HYBRID", 2, "ops", "t786433", "random", t=T_BIG17, msg="random")
    _add(out, 64, "HPSPOVERQ", "BV", 2, "chain", "ext", "random", enc="EXTENDED", msg="random")
    return out


def suite_mid():
    """N = 256, 1024, 2048 (not committed)."""
    out = []
    progs = [("chain", 2), ("dot", 2), ("plain", 2), ("rotsum", 2), ("ops", 2), ("random", 3), ("chain", 3),
             ("square", 2), ("addsub", 1), ("norelin", 2)]
    i = 0
    for n in (256, 1024, 2048):
        for m in MULTS:
            for k in KSS:
                for _ in range(2):
                    p, d = progs[i % len(progs)]
                    qb, msg = QB[i % 3], MS[(i // 2) % 3]
                    i += 1
                    _add(out, n, m, k, d, p, f"q{qb}", msg, qbits=qb, msg=msg, len=14 if p == "random" else None)
                if m in POQ:
                    _add(out, n, m, k, 3, "compress", "random", msg="random")
        _add(out, n, "HPSPOVERQLEVELED", "BV", 4, "levels", "q30", "small", qbits=30, msg="small")
        _add(out, n, "HPSPOVERQLEVELED", "HYBRID", 4, "levels", "q30", "small", qbits=30, msg="small")
        _add(out, n, "HPSPOVERQLEVELED", "BV", 6, "levels", "q60", "small", qbits=60, progdepth=5, msg="small")
        _add(out, n, "default", "default", 2, "chain", "random", msg="random")
        _add(out, n, "default", "default", 3, "dot", "max", msg="max")
        _add(out, n, "HPS", "HYBRID", 2, "dot", "ext", "random", enc="EXTENDED", msg="random")
        _add(out, n, "BEHZ", "BV", 2, "plain", f"t{T_BIG17}", "max", t=T_BIG17, msg="max")
        _add(out, n, "HPSPOVERQ", "HYBRID", 3, "chain", f"t{T_BIG17}", "random", t=T_BIG17, msg="random")
        _add(out, n, "HPS", "BV", 2, "coefpk", "random", msg="random")
        _add(out, n, "HPSPOVERQLEVELED", "HYBRID", 2, "mixadd", "random", msg="random")
    return out


def suite_real():
    """Real sizes (not committed): fully default contexts (CCParams<CryptoContextBFVRNS> with only the
    depth and t set: OpenFHE picks N for HEStd_128_classic) and N = 4096, 8192, 16384 with 30/45/60-bit
    primes, t = 65537 and t = 1179649 = 9*2^17 + 1."""
    out = []
    D = "default"
    # --- contexts created with defaults (no --n, no --qbits)
    for d in (1, 2, 3, 4):
        _add(out, None, D, D, d, "chain", "random", msg="random")
    _add(out, None, D, D, 2, "dot", "random", msg="random")
    _add(out, None, D, D, 3, "plain", "max", msg="max")
    _add(out, None, D, D, 3, "compress", "random", msg="random")
    _add(out, None, D, D, 4, "levels", "small", msg="small")
    _add(out, None, D, D, 6, "chain", f"t{T_17}", "random", t=T_17, progdepth=4, msg="random")
    _add(out, None, D, "HYBRID", 2, "chain", "random", msg="random")
    _add(out, None, D, "HYBRID", 4, "chain", "random", msg="random")
    _add(out, None, D, "HYBRID", 3, "dot", "random", msg="random")
    _add(out, None, D, "HYBRID", 4, "levels", "small", msg="small")
    _add(out, None, D, "HYBRID", 6, "chain", f"t{T_17}", "random", t=T_17, progdepth=4, msg="random")  # N = 32768
    _add(out, None, D, "HYBRID", 6, "plain", f"t{T_17}", "max", t=T_17, msg="max")                      # N = 32768
    _add(out, None, "BEHZ", D, 2, "chain", "random", msg="random")
    _add(out, None, "BEHZ", D, 3, "dot", "random", msg="random")
    _add(out, None, "BEHZ", "HYBRID", 2, "plain", "random", msg="random")
    _add(out, None, "HPS", D, 2, "chain", "random", msg="random")
    _add(out, None, "HPS", "HYBRID", 3, "dot", "random", msg="random")
    _add(out, None, "HPSPOVERQ", D, 3, "chain", "random", msg="random")
    _add(out, None, "HPSPOVERQ", D, 2, "compress", "random", msg="random")
    _add(out, None, D, D, 2, "chain", "ext", "random", enc="EXTENDED", msg="random")
    _add(out, None, D, D, 2, "mixadd", "random", msg="random")
    # --- explicit ring dimension (HEStd_NotSet)
    combos = [(30, T_SMALL, 2, "chain"), (45, T_17, 3, "dot"), (60, T_SMALL, 4, "chain"), (45, T_SMALL, 2, "plain"),
              (60, T_17, 1, "chain"), (30, T_SMALL, 3, "dot"), (60, T_SMALL, 2, "plain"), (30, T_17, 4, "chain"),
              (45, T_SMALL, 1, "chain"), (60, T_17, 3, "plain"), (45, T_SMALL, 4, "chain")]
    i = 0
    for n in (4096, 8192, 16384):
        for m in MULTS:
            for k in KSS:
                qb, t, d, p = combos[i % len(combos)]
                msg = "max" if p == "plain" else "random"
                i += 1
                _add(out, n, m, k, d, p, f"q{qb}", f"t{t}", msg, qbits=qb, t=t, msg=msg)
    _add(out, 4096, "HPSPOVERQ", "BV", 3, "compress", "q30", "random", qbits=30, msg="random")
    _add(out, 8192, "HPSPOVERQLEVELED", "HYBRID", 3, "compress", "q45", "random", qbits=45, msg="random")
    _add(out, 4096, "HPSPOVERQLEVELED", "BV", 4, "levels", "q30", "small", qbits=30, msg="small")
    _add(out, 8192, "HPSPOVERQLEVELED", "HYBRID", 4, "levels", "q45", "small", qbits=45, msg="small")
    _add(out, 16384, "HPSPOVERQLEVELED", "BV", 4, "levels", "q60", "small", qbits=60, msg="small")
    return out


ADV_N = (16, 64, 1024, 4096)


def suite_adv():
    """Adversarial inputs (hand-built corner cases of the BFV parameters and ciphertexts)."""
    out = []
    for n in ADV_N:
        for m in MULTS:
            for v in ("allmax", "signpos1", "signneg1", "signpos2", "signposh", "keyaware"):
                _add(out, n, m, "HYBRID", 2, "advplain:" + v, msg="max")
            _add(out, n, m, "BV", 2, "advplain:keyaware", msg="max")
            _add(out, n, m, "HYBRID", 2, "advmul:scripted", msg="max")
            _add(out, n, m, "BV", 2, "advmul:scripted", msg="max")
            _add(out, n, m, "HYBRID", 2, "advmul:scriptedsq", msg="max")
            _add(out, n, m, "HYBRID", 2, "advmul:scriptedkey", msg="max")
            _add(out, n, m, "BV", 2, "advmul:scriptedkey", msg="max")
            _add(out, n, m, "HYBRID", 2, "advmul:scriptedkeysq", msg="max")
            for v in ("handbuilt", "handbuiltsq", "handbuiltneg"):
                _add(out, n, m, "HYBRID", 2, "advmul:" + v, msg="max", env={"EXTRACT_FLAGS": "--assume-fresh-inputs"})
            _add(out, n, m, "BV", 2, "advmul:handbuilt", msg="max", env={"EXTRACT_FLAGS": "--assume-fresh-inputs"})
            _add(out, n, m, "HYBRID", 2, "advmul:handbuiltkey", msg="max", env={"EXTRACT_FLAGS": "--assume-fresh-inputs"})
            _add(out, n, m, "HYBRID", 2, "advplain:handmax", msg="max", env={"EXTRACT_FLAGS": "--assume-fresh-inputs"})
            _add(out, n, m, "BV", 2, "advplain:handmax", msg="max", env={"EXTRACT_FLAGS": "--assume-fresh-inputs"})
    return out


SUITES = {"sample": suite_sample, "bfv-fixtures": suite_fixtures, "bfv-mid": suite_mid, "bfv-real": suite_real,
          "bfv-adv": suite_adv}


def dir_size(d):
    return sum(os.path.getsize(os.path.join(d, f)) for f in os.listdir(d))


def run(out, name, args, cenv, selftest):
    d = os.path.join(out, name)
    env = dict(os.environ, OMP_NUM_THREADS="1", **cenv)
    t0 = time.time()
    r = subprocess.run([os.path.join(HERE, "export_case_bfv.sh"), d] + args, capture_output=True, text=True, env=env)
    secs = time.time() - t0
    extract = "ok"
    for line in r.stdout.splitlines():
        if line.startswith("EXTRACT-FAIL "):
            extract = "FAIL: " + line.split(" ", 2)[2]
        elif line.startswith("EXPORT-FAIL "):
            extract = "not run (" + line.split(" ", 2)[2] + ")"
    exc, polys, st = "", 0, "skipped"
    info = ["", "", "", "", "", ""]
    if r.returncode == 0:
        try:
            pin = json.load(open(os.path.join(d, "pin.json")))
            exc = str(sum(1 for n in pin["notes"] if n.startswith("EXC ")))
            b = pin["bfv"]
            dm = dk = 0
            if extract == "ok":
                prog = json.load(open(os.path.join(d, "prog.fhecheck.json")))
                for p in prog.get("provenance", []):
                    if p.get("internalDrop"):
                        if (p.get("findLevelsToDrop") or {}).get("keySwitch"):
                            dk += 1
                        else:
                            dm += 1
            info = [str(pin["N"]), str(len(pin["qs"])), b["mult"], b["ks"] + (f"/w{b['digitSizeBV']}" if b["digitSizeBV"] else ""),
                    b["enc"], f"{dm}/{dk}"]
        except Exception as e:  # an unreadable pin.json is an exporter bug
            exc = "pin.json unreadable: " + str(e)
        polys = os.path.getsize(os.path.join(d, "polys.txt"))
        if selftest:
            s = subprocess.run([sys.executable, "-I", os.path.join(HERE, "selftest_bfv.py"), d, "--json"],
                               capture_output=True, text=True)
            open(os.path.join(d, "selftest.json"), "w").write(s.stdout if s.stdout else json.dumps({"crash": s.stderr[-2000:]}))
            st = "ok" if s.returncode == 0 else "FAIL"
            try:
                sj = json.loads(s.stdout)
                mm = sj.get("decryptMismatch", [])
                info.append(f"{sum(m['coefficients'] for m in mm)}/{max([m['maxBoundaryDistance'] for m in mm], default=0):.3g}")
                fm = sj.get("finalBoundaryDistance", {})
                info.append(f"{min(fm.values()):.3g}" if fm else "")
            except Exception:
                info += ["?", "?"]
    if len(info) == 6:
        info += ["", ""]
    size = dir_size(d) if os.path.isdir(d) else 0
    return [name, " ".join(args) + ("".join(f" [{k}={v}]" for k, v in cenv.items())), str(r.returncode),
            extract.replace("\t", " "), exc, str(size), str(polys), st] + info + [f"{secs:.1f}"]


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
        for n, args, env in cases:
            print(n, " ".join(args), env or "")
        return
    jobs = max(1, min(a.jobs, 20))
    os.makedirs(a.out, exist_ok=True)
    with ThreadPoolExecutor(jobs) as ex:
        rows = list(ex.map(lambda c: run(a.out, c[0], c[1], c[2], a.selftest), cases))
    with open(os.path.join(a.out, "MANIFEST.tsv"), "w") as f:
        f.write("case\targs\texit\textract\texceptions\tbytes\tpolys_bytes\tselftest\tN\tL\tmult\tks\tenc\tdrops\tdecmismatch\tfinalmargin\tseconds\n")
        for r in rows:
            f.write("\t".join(r) + "\n")
    nfail = sum(1 for r in rows if r[2] != "0")
    nx = sum(1 for r in rows if r[3].startswith("FAIL"))
    nst = sum(1 for r in rows if r[7] == "FAIL")
    print(f"{a.suite}: {len(rows)} cases, {nfail} export failures, {nx} extraction failures, "
          f"{nst} selftest failures, {sum(int(r[5]) for r in rows)} bytes -> {a.out}/MANIFEST.tsv")


if __name__ == "__main__":
    main()
