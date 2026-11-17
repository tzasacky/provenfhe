#!/usr/bin/env bash
# "What a default OpenFHE BFV user sees": the `chain` program (depth D: one product and D-1
# squarings, each relinearized) at OpenFHE's own parameters -- CCParams<CryptoContextBFVRNS> with
# only the plaintext modulus (65537) and the multiplicative depth D set (the defaults are then
# HPSPOVERQLEVELED multiplication, BV key switching, STANDARD encryption, 60-bit primes,
# HEStd_128_classic), and the same with key switching HYBRID -- for D = 1..6, extracted and checked
# by fhe_check (worst case). Needs bfv_demo on traced OpenFHE v1.6.1 (build_openfhe.sh; BFV_DEMO
# overrides its path) and fhe_check. Runs single-threaded (OMP_NUM_THREADS=1, as the tracer needs).
#   default_table_bfv.sh [OUTDIR]   writes OUTDIR/<technique>_<ks>_d<D>[.<fix>].fhecheck.json and prints a TSV
#   DEPTHS="1 2 3" default_table_bfv.sh       restricts the depths
#   TECHS="default BEHZ" default_table_bfv.sh  the base techniques (default: both; BEHZ is the
#                                              integer-only technique whose slacks fhe_check has proved)
# Columns: D, N, log2 Q, limbs, technique, key switching; then for the file AS EXTRACTED (what the
# library runs: floatTolerant = true for the HPS family): verdict, proved bound (bits), margin
# (bits) [for NOT CERTIFIED: the bound and the overflow at the first failing instruction], and
# whether the multiplication slacks are PROVED (for the idealised limb-level algorithm in
# Challenge/BFVMul) or ASSUMED (report field budget.slacksProved); then, for the HPS family, the
# same run extracted with --idealised (floatTolerant = false: the exact algorithm, NOT what the
# library runs); the noise OBSERVED in this one run and the largest noise decryption tolerates
# (bits); whether the library's decryption was correct on this run; and -- when the file as
# extracted is not CERTIFIED -- the first variant in this list that is CERTIFIED:
#   default technique: HYBRID instead of BV | one more limb (parameters generated for depth D+1,
#     same program) | BEHZ | HPS | BEHZ + HYBRID | HPS + HYBRID | then BEHZ / HPS (+ HYBRID) with
#     one, two, three more limbs
#   BEHZ: HYBRID instead of BV | one, two, three more limbs (each also with HYBRID)
# (OpenFHE's default scalingModSize is already the largest it accepts, 60, so "larger primes" is not
# a variant.) The variants are real OpenFHE runs with their own extraction, not hypothetical inputs.
set -euo pipefail
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(cd "$HERE/../../.." && pwd)"
export BFV_DEMO="${BFV_DEMO:-$ROOT/harness/build/frontend-openfhe/bfv_demo}"
export OMP_NUM_THREADS=1
export FHE_CHECK="${FHE_CHECK:-$ROOT/.lake/build/bin/fhe_check}"
export OUT="${1:-$(mktemp -d)}"
export HERE DEPTHS="${DEPTHS:-1 2 3 4 5 6}" TECHS="${TECHS:-default BEHZ}"
mkdir -p "$OUT"
exec python3 -I - <<'PY'
import json, math, os, subprocess, sys

HERE, OUT, B, CHECK = (os.environ[k] for k in ("HERE", "OUT", "BFV_DEMO", "FHE_CHECK"))


def check(f):
    """fhe_check on one file -> (verdict, bound, margin, slacks)."""
    rep = json.loads(subprocess.run([CHECK, "--json", "--no-suggest", f], capture_output=True, text=True).stdout)
    v, bound, margin = rep["verdict"], "", ""
    sp = (rep.get("budget") or {}).get("slacksProved")
    slacks = {True: "PROVED", False: "ASSUMED"}.get(sp, "")
    if v == "CERTIFIED":
        bound = f"{max(o['boundLog2'] for o in rep['outputs']):.2f}"
        margin = f"{min(o['marginBits'] for o in rep['outputs']):.2f}"
    elif v == "NOT CERTIFIED":
        ff = (rep.get("failure") or {}).get("firstFailing") or {}
        if ff.get("overflowBits") is not None:
            bound = f"{ff['boundLog2']:.2f} at body[{ff['index']}]"
            margin = f"-{ff['overflowBits']:.2f}"
        else:
            v += ": " + (rep.get("summary") or "")[:60]
    else:
        v += ": " + (rep.get("summary") or "")[:95]
    return v, bound, margin, slacks


def run(tag, d, ks, mult=None, extra_depth=0):
    """One OpenFHE run + extraction (as the library runs, and --idealised) + value check + fhe_check."""
    w = os.path.join(OUT, "run_" + tag)
    os.makedirs(w, exist_ok=True)
    args = ["--t", "65537", "--prog", "chain", "--depth", str(d + extra_depth), "--progdepth", str(d)]
    if ks != "default":
        args += ["--ks", ks]
    if mult and mult != "default":
        args += ["--mult", mult]
    r = subprocess.run([B, "run", w] + args, capture_output=True, text=True)
    if r.returncode not in (0, 3):
        return {"verdict": f"bfv_demo failed ({r.returncode})"}
    f = os.path.join(OUT, tag + ".fhecheck.json")
    ex = [sys.executable, "-I", os.path.join(HERE, "extract_bfv.py"), "--params", w + "/params.json",
          "--trace", w + "/trace.jsonl", "--artifact", "default_table_" + tag]
    e = subprocess.run(ex, capture_output=True, text=True)
    open(f, "w").write(e.stdout)
    if e.returncode != 0:
        return {"verdict": "EXTRACTION ERROR: " + json.loads(e.stdout).get("error", "?")}
    v = subprocess.run([sys.executable, "-I", os.path.join(HERE, "value_check_bfv.py"), f, w + "/values.json"],
                       capture_output=True, text=True)
    lib = {0: "yes", 3: "NO (differs from the prediction)"}.get(v.returncode, "value check FAILED")
    p = json.load(open(w + "/params.json"))
    vals = json.load(open(w + "/values.json"))
    Q = math.prod(int(x["q"]) for x in p["qs"])
    obs = max(int(o["noise"]) for o in vals["outputs"].values())
    verdict, bound, margin, slacks = check(f)
    row = {"N": p["N"], "log2Q": math.log2(Q), "limbs": len(p["qs"]), "technique": p["multiplicationTechnique"],
           "ks": p["keySwitch"] + (f" (dnum {p['dnum']}, {len(p['special'])} special)" if p["keySwitch"] == "HYBRID" else ""),
           "verdict": verdict, "bound": bound, "margin": margin, "slacks": slacks, "lib": lib, "ideal": "",
           "observed": f"{math.log2(max(obs, 1)):.1f}", "limit": f"{math.log2(Q / (2 * p['t'])):.1f}"}
    if p["multiplicationTechnique"] != "BEHZ":
        fi = os.path.join(OUT, tag + ".idealised.fhecheck.json")
        open(fi, "w").write(subprocess.run(ex + ["--idealised"], capture_output=True, text=True).stdout)
        iv, ib, im, isl = check(fi)
        row["ideal"] = f"{iv}" + (f", bound {ib}, margin {im}" if ib else "") + (f", slacks {isl}" if isl else "")
    for x in ("cc.json", "trace.jsonl", "values.json", "check.txt", "params.json"):
        try:
            os.remove(os.path.join(w, x))
        except OSError:
            pass
    os.rmdir(w)
    return row


def fixes(tech, ks):
    hyb = ks == "HYBRID"
    out = [] if hyb else [("HYBRID instead of BV", dict(ks="HYBRID", mult=tech))]
    out.append(("one more limb (parameters for depth D+1)", dict(ks=ks, mult=tech, extra_depth=1)))
    others = ["BEHZ", "HPS"] if tech == "default" else [tech]
    if tech == "default":
        out += [(m, dict(ks=ks, mult=m)) for m in others]
        if not hyb:
            out += [(f"{m} + HYBRID", dict(ks="HYBRID", mult=m)) for m in others]
    for k in (1, 2, 3):
        for m in others:
            if not (tech != "default" and k == 1):
                out.append((f"{m} + {k} more limb(s)", dict(ks=ks, mult=m, extra_depth=k)))
            if not hyb:
                out.append((f"{m} + HYBRID + {k} more limb(s)", dict(ks="HYBRID", mult=m, extra_depth=k)))
    return out


cols = ["D", "N", "log2 Q", "limbs", "technique", "key switching", "verdict", "proved bound (bits)", "margin (bits)",
        "multiplication slacks", "idealised exact algorithm (--idealised; not the library)", "observed noise (bits)",
        "decryption limit (bits)", "library decryption correct", "smallest certified variant"]
print("\t".join(cols), flush=True)
for tech in os.environ["TECHS"].split():
    for d in map(int, os.environ["DEPTHS"].split()):
        for ks in ("default", "HYBRID"):
            base = f"{tech.lower()}_{ks.lower()}_d{d}"
            r = run(base, d, ks, tech)
            fix = ""
            if r["verdict"] != "CERTIFIED":
                fix = "none of the variants tried"
                for i, (name, kw) in enumerate(fixes(tech, ks)):
                    kw = dict(kw)
                    k2 = kw.pop("ks")
                    rr = run(f"{base}.fix{i}", d, k2, **kw)
                    if rr.get("verdict") == "CERTIFIED":
                        fix = (f"{name}: N = {rr['N']}, {rr['limbs']} limbs, bound {rr['bound']}, margin {rr['margin']} bits, "
                               f"slacks {rr['slacks']}, library decryption correct: {rr['lib']}")
                        break
            if "N" not in r:
                print(f"{d}\t\t\t\t{tech}\t{ks}\t{r['verdict']}", flush=True)
                continue
            print("\t".join(str(x) for x in (d, r["N"], f"{r['log2Q']:.1f}", r["limbs"], r["technique"], r["ks"], r["verdict"],
                                             r["bound"], r["margin"], r["slacks"], r["ideal"], r["observed"], r["limit"],
                                             r["lib"], fix)), flush=True)
PY
