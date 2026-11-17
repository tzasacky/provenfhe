#!/usr/bin/env python3
"""UNTRUSTED. The real-size conformance suite of openfhe-pin: case list and recorder.

  suite.py --list                          # print: case, scheme, exporter arguments
  suite.py --out DIR [--jobs J] [--only S] # record every case (export_case.sh / export_case_bfv.sh)

Every case is a CryptoContext that OpenFHE v1.6.1 builds itself at 128-bit security
(HEStd_128_classic: no --n, the library chooses the ring dimension and the moduli; only the
depth, the plaintext modulus and the technique are set). Seeds are derived from the case names
(crc32 + 1), so a re-recording is byte-identical on the same build. The recorder must be the
exporter built against the single-threaded traced library (build_openfhe.sh, WITH_OPENMP=OFF);
export/build_cpp.sh refuses any other.

Writes DIR/<case>/{params.json,trace.jsonl,pin.json,polys.txt,prog.fhecheck.json} and
DIR/MANIFEST.tsv (case, scheme, args, exit, extract, seconds, bytes).
"""
import argparse
import os
import subprocess
import sys
import time
import zlib
from concurrent.futures import ThreadPoolExecutor

HERE = os.path.dirname(os.path.abspath(__file__))
EXPORT = os.path.join(HERE, "..", "export")
SHORT = {"FIXEDMANUAL": "fm", "FIXEDAUTO": "fa", "FLEXIBLEAUTO": "xa", "FLEXIBLEAUTOEXT": "xe",
         "HPS": "hps", "HPSPOVERQ": "poq", "HPSPOVERQLEVELED": "lev", "BEHZ": "behz",
         "HYBRID": "hy", "BV": "bv", "default": "def"}
TECHS = ["FIXEDMANUAL", "FIXEDAUTO", "FLEXIBLEAUTO", "FLEXIBLEAUTOEXT"]
MULTS = ["HPS", "HPSPOVERQ", "HPSPOVERQLEVELED", "BEHZ"]
KSS = ["HYBRID", "BV"]
DEPTHS = [1, 3, 6, 10]
# the configurations whose seeded random program (the name fixes the seed) the extractor refuses
# (an unrelinearised product combined with another ciphertext), measured on the recording
RANDOM_REFUSED = {("hps", "hy", 3), ("hps", "bv", 3), ("hps", "bv", 6), ("poq", "bv", 6), ("lev", "hy", 3),
                  ("behz", "bv", 1), ("behz", "bv", 3), ("behz", "bv", 10)}


def seed_of(name):
    return zlib.crc32(name.encode()) + 1


def case(scheme, name, **kw):
    args = ["--seed", str(seed_of(name))]
    for k, v in kw.items():
        if v is not None:
            args += ["--" + k, str(v)]
    return name, scheme, args


def cases():
    out = []
    # BGV: every scaling technique at depths 1, 3, 6, 10 (HYBRID key switching, the library's
    # default and the only one its BGV supports), t = 65537; the program `ops` runs every
    # operation once (encryption, add/sub, products with relinearisation, plaintext operands,
    # rotations, modulus switching, decryption); `chain` multiplies down the whole chain.
    for t in TECHS:
        for d in DEPTHS:
            # v1.6.1 refuses its own default parameters for FIXEDAUTO and FLEXIBLEAUTO at depths
            # 9, 10 and 11 (rns-cryptoparameters.cpp:161, "EstimateLogP() failure: expected sizeP
            # [3], but got sizeP [4]"); depth 12 is used there instead
            d = 12 if (d == 10 and t in ("FIXEDAUTO", "FLEXIBLEAUTO")) else d
            out.append(case("BGV", f"rs_bgv_{SHORT[t]}_d{d}_ops", scal=t, depth=d, prog="ops", msg="random"))
        dc = 12 if t in ("FIXEDAUTO", "FLEXIBLEAUTO") else 10
        out.append(case("BGV", f"rs_bgv_{SHORT[t]}_d{dc}_chain", scal=t, depth=dc, prog="chain", msg="random"))
    out.append(case("BGV", "rs_bgv_fa_d6_compress", scal="FIXEDAUTO", depth=6, prog="paths:compress", msg="random"))
    out.append(case("BGV", "rs_bgv_xa_d3_rotsum", scal="FLEXIBLEAUTO", depth=3, prog="rotsum", msg="random"))
    # BFV: every multiplication technique x key switching method at depths 1, 3, 6, 10 (t = 65537),
    # each with a seeded random program of operations the extractor maps (`--menu core`: the whole
    # program is extracted, so the contract and certificate checks run on it); `ops` (every
    # operation once, including combinations the extractor refuses) at depth 3.
    for m in MULTS:
        for k in KSS:
            for d in DEPTHS:
                out.append(case("BFV", f"rs_bfv_{SHORT[m]}_{SHORT[k]}_d{d}_random", mult=m, ks=k, depth=d,
                                prog="random", menu="core", len=16, msg="random"))
            out.append(case("BFV", f"rs_bfv_{SHORT[m]}_{SHORT[k]}_d3_ops", mult=m, ks=k, depth=3, prog="ops",
                            msg="random"))
            # where a random program combines an unrelinearised product (the extractor refuses it),
            # the configuration's whole program is `rotsum` (product, rotations, add, sub)
            for d in DEPTHS:
                if (SHORT[m], SHORT[k], d) in RANDOM_REFUSED:
                    out.append(case("BFV", f"rs_bfv_{SHORT[m]}_{SHORT[k]}_d{d}_rotsum", mult=m, ks=k, depth=d,
                                    prog="rotsum", msg="random"))
        out.append(case("BFV", f"rs_bfv_{SHORT[m]}_def_d10_chain", mult=m, depth=10, prog="chain", msg="random"))
    # nine or more 60-bit limbs (the 128-bit accumulator branch of the HPS scaling): depth 14 gives
    # 9 limbs, depth 16 gives 11 (N = 32768)
    out.append(case("BFV", "rs_bfv_hps_def_d14_chain", mult="HPS", depth=14, prog="chain", progdepth=4, msg="random"))
    out.append(case("BFV", "rs_bfv_hps_bv_d16_random", mult="HPS", ks="BV", depth=16, prog="random", menu="core",
                    len=16, msg="random"))
    out.append(case("BFV", "rs_bfv_poq_def_d16_chain", mult="HPSPOVERQ", depth=16, prog="chain", progdepth=4,
                    msg="random"))
    # Compress, HPSPOVERQLEVELED level drops, EXTENDED encryption, the library default context
    out.append(case("BFV", "rs_bfv_poq_def_d6_compress", mult="HPSPOVERQ", depth=6, prog="compress", msg="random"))
    out.append(case("BFV", "rs_bfv_lev_def_d10_levels", mult="HPSPOVERQLEVELED", depth=10, prog="levels",
                    msg="small"))
    out.append(case("BFV", "rs_bfv_def_def_d3_ext_chain", depth=3, enc="EXTENDED", prog="chain", msg="random"))
    out.append(case("BFV", "rs_bfv_def_def_d6_chain", depth=6, prog="chain", msg="random"))
    # the library defect reported upstream: BFV defaults, t = 786433, depth 6, EvalMult chain
    out.append(case("BFV", "rs_bfv_def_def_d6_t786433_chain", depth=6, t=786433, prog="chain", msg="random"))
    return out


def run(out, name, scheme, args):
    d = os.path.join(out, name)
    script = os.path.join(EXPORT, "export_case.sh" if scheme == "BGV" else "export_case_bfv.sh")
    env = dict(os.environ, OMP_NUM_THREADS="1")
    t0 = time.time()
    r = subprocess.run([script, d] + args, capture_output=True, text=True, env=env)
    secs = time.time() - t0
    extract = "ok"
    for line in r.stdout.splitlines():
        if line.startswith("EXTRACT-FAIL "):
            extract = "FAIL: " + line.split(" ", 2)[2]
        elif line.startswith("EXPORT-FAIL "):
            extract = "not run (" + line.split(" ", 2)[2] + ")"
    size = sum(os.path.getsize(os.path.join(d, f)) for f in os.listdir(d)) if os.path.isdir(d) else 0
    return [name, scheme, " ".join(args), str(r.returncode), extract.replace("\t", " "), f"{secs:.1f}", str(size)]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--out")
    ap.add_argument("--jobs", type=int, default=8)
    ap.add_argument("--list", action="store_true")
    ap.add_argument("--only")
    a = ap.parse_args()
    cs = cases()
    assert len({c[0] for c in cs}) == len(cs), "duplicate case names"
    if a.only:
        cs = [c for c in cs if a.only in c[0]]
    if a.list:
        for n, s, args in cs:
            print(n, s, " ".join(args), sep="\t")
        return
    if not a.out:
        sys.exit("--out DIR is required")
    os.makedirs(a.out, exist_ok=True)
    with ThreadPoolExecutor(max(1, a.jobs)) as ex:
        rows = list(ex.map(lambda c: run(a.out, *c), cs))
    with open(os.path.join(a.out, "MANIFEST.tsv"), "w") as f:
        f.write("case\tscheme\targs\texit\textract\tseconds\tbytes\n")
        for r in rows:
            f.write("\t".join(r) + "\n")
    bad = [r[0] for r in rows if r[3] != "0"]
    print(f"{len(rows)} cases, {len(bad)} export failures {bad}, "
          f"{sum(int(r[6]) for r in rows)} bytes -> {a.out}/MANIFEST.tsv")


if __name__ == "__main__":
    main()
