#!/usr/bin/env python3
"""UNTRUSTED driver: close the loop between `fhe_check recommend` and the real libraries.

For each program it
  1. runs the library at its own (default) parameters, extracts, and checks (fhe_check);
  2. asks `fhe_check recommend` for parameters, which predicts the exact primes the library will
     generate and certifies the program on them;
  3. configures the REAL library with the recommendation (OpenFHE: SetFirstModSize,
     SetScalingModSize, SetNumLargeDigits, SetRingDim; HEIR: a bgv.schemeParam module attribute),
     re-runs (OpenFHE: the program itself, traced and value-checked; HEIR: heir-opt), re-extracts,
     and re-checks the re-extracted file with a PLAIN `fhe_check` run;
  4. reports whether the library's own primes equal the predicted ones, the margins, the
     ciphertext size and (OpenFHE) the measured evaluation time at both parameter sets.

Sections: --openfhe (FIXEDMANUAL, `chain` at depth 1..8), --auto (OpenFHE's automatic scaling
modes: what SetEvalAddCount achieves), --heir (mult_dep_8 and dot_product_8 on the Lattigo path).
Nothing here is trusted: the verdicts are fhe_check's; this script only runs tools and tabulates.
"""
import argparse
import json
import math
import os
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
FRONT = os.path.dirname(HERE)
ROOT = os.path.dirname(os.path.dirname(FRONT))
BGV = os.path.join(ROOT, "harness/build/frontend-openfhe/bgv_demo")
HEIR = os.path.join(ROOT, "harness/build/heir-nightly/heir-opt")
HEIR_SRC = os.environ.get("HEIR_EXAMPLES", "")  # directory of the HEIR example .mlir files (--heir mode only)
# heir-translate (only used to turn HEIR's lattigo dialect into Go, to RUN the program on Lattigo
# v6.1.0 and time it); see README "Getting parameters that are certified" for its provenance.
HEIR_TRANSLATE = os.path.join(ROOT, "harness/build/heir-nightly/heir-translate")
LATTIGO = "github.com/tuneinsight/lattigo/v6 v6.1.0"

# A main() per HEIR example: encrypt fixed inputs, run HEIR's generated evaluation function once,
# decrypt and compare with the cleartext result, then time `reps` evaluations (encryption outside
# the timed region). Prints one JSON line.
GO_MAIN = {
    "mult_dep_8": """
	evaluator, param, encoder, encryptor, decryptor := Mult_dep__configure()
	x := int16(3)
	enc := func() []*rlwe.Ciphertext { return Mult_dep__encrypt__arg0(evaluator, param, encoder, encryptor, x) }
	run := func(c []*rlwe.Ciphertext) []*rlwe.Ciphertext { return Mult_dep(evaluator, param, encoder, c) }
	got := Mult_dep__decrypt__result0(evaluator, param, encoder, decryptor, run(enc()))
	want := int16(1)
	for i := 0; i < 8; i++ { want *= x }
""",
    "dot_product_8": """
	evaluator, param, encoder, encryptor, decryptor := Dot_product__configure()
	a := []int16{1, 2, 3, 4, 5, 6, 7, 8}
	b := []int16{2, 3, 4, 5, 6, 7, 8, 9}
	type pair struct{ x, y []*rlwe.Ciphertext }
	enc := func() pair {
		return pair{Dot_product__encrypt__arg0(evaluator, param, encoder, encryptor, a), Dot_product__encrypt__arg1(evaluator, param, encoder, encryptor, b)}
	}
	run := func(c pair) []*rlwe.Ciphertext { return Dot_product(evaluator, param, encoder, c.x, c.y) }
	got := Dot_product__decrypt__result0(evaluator, param, encoder, decryptor, run(enc()))
	want := int16(0)
	for i := range a { want += a[i] * b[i] }
""",
}
GO_TAIL = """
	ms := []float64{}
	for r := 0; r < reps; r++ {
		c := enc()
		t0 := time.Now()
		run(c)
		ms = append(ms, float64(time.Since(t0).Microseconds())/1000)
	}
	s := append([]float64{}, ms...)
	sort.Float64s(s)
	out, _ := json.Marshal(map[string]any{"got": got, "want": want, "ok": got == want, "ms": ms, "minMs": s[0], "medianMs": s[len(s)/2], "logN": param.LogN()})
	fmt.Println(string(out))
}
"""
GO_HEAD = """package main

import (
	"encoding/json"
	"fmt"
	"os"
	"sort"
	"strconv"
	"time"

	"github.com/tuneinsight/lattigo/v6/core/rlwe"
)

func main() {
	reps, _ := strconv.Atoi(os.Args[1])
"""


def lattigo_build(d, bgv_mlir, name):
    """HEIR's own Lattigo backend: heir-opt --scheme-to-lattigo, heir-translate --emit-lattigo,
    go build against Lattigo v6.1.0. Returns the binary or an error string."""
    os.makedirs(d, exist_ok=True)
    lat = sh([HEIR, "--scheme-to-lattigo", bgv_mlir])
    if lat.returncode != 0:
        return None, "heir-opt --scheme-to-lattigo failed: " + lat.stderr[-300:]
    go = sh([HEIR_TRANSLATE, "--emit-lattigo", "--package-name=main"], input=lat.stdout)
    if go.returncode != 0:
        return None, "heir-translate failed: " + go.stderr[-300:]
    open(os.path.join(d, "prog.go"), "w").write(go.stdout)
    open(os.path.join(d, "main.go"), "w").write(GO_HEAD + GO_MAIN[name] + GO_TAIL)
    open(os.path.join(d, "go.mod"), "w").write(f"module lrun\n\ngo 1.22\n\nrequire {LATTIGO}\n")
    env = {**os.environ, "GOFLAGS": "-mod=mod"}
    for cmd in (["go", "mod", "tidy"], ["go", "build", "-o", "prog", "."]):
        r = sh(cmd, cwd=d, env=env)
        if r.returncode != 0:
            return None, f"{' '.join(cmd)} failed: " + r.stderr[-300:]
    return os.path.join(d, "prog"), None


def lattigo_time_pair(bins, rounds, reps):
    """Interleaved timing of HEIR-generated Lattigo binaries (GOMAXPROCS=1)."""
    res = {k: {"ms": [], "ok": True} for k in bins}
    loads = []
    for _ in range(rounds):
        loads.append(load1())
        for k, b in bins.items():
            r = sh([b, str(reps)], env={**os.environ, "GOMAXPROCS": "1"})
            if r.returncode != 0:
                res[k]["ok"] = False; res[k]["error"] = r.stderr[-300:]; continue
            j = json.loads(r.stdout)
            res[k]["ms"] += j["ms"]
            res[k]["ok"] = res[k]["ok"] and j["ok"]
            res[k]["decrypted"] = j["got"]; res[k]["expected"] = j["want"]
    for k in res:
        xs = sorted(res[k].pop("ms"))
        if xs:
            res[k].update({"medianMs": xs[len(xs) // 2], "minMs": xs[0], "runs": len(xs)})
    res["loads"] = loads
    res["loadMedian"] = sorted(loads)[len(loads) // 2]
    return res
FHE_CHECK = os.environ.get("FHE_CHECK", os.path.join(ROOT, ".lake/build/bin/fhe_check"))
ROUNDS = 7  # interleaved timing rounds (each `reps` evaluations per configuration)


def sh(args, **kw):
    r = subprocess.run(args, capture_output=True, text=True, **kw)
    return r


def check(path, *extra):
    r = sh([FHE_CHECK, "--json", "--no-suggest", *extra, path])
    return json.loads(r.stdout)


def recommend(path, emit, *extra):
    r = sh([FHE_CHECK, "recommend", "--json", "--emit", emit, *extra, path])
    return r.returncode, json.loads(r.stdout)


def min_margin(rep):
    """Smallest margin (bits) over the outputs, level and decryption; or 'over x'."""
    if rep["verdict"] == "CERTIFIED":
        ms = [o["marginBits"] for o in rep["outputs"]] + [o["decMarginBits"] for o in rep["outputs"] if "decMarginBits" in o]
        return f"{min(ms):.2f}"
    f = (rep.get("failure") or {}).get("firstFailing")
    if f and f.get("overflowBits") is not None:
        return f"over {f['overflowBits']:.2f}"
    return rep["verdict"]


def qp_bits(params):
    q = [int(l["q"] if isinstance(l, dict) else l) for l in params["limbs"]]
    p = [int(l["q"] if isinstance(l, dict) else l) for l in params["special"]]
    return math.log2(math.prod(q) * math.prod(p)), q, p


def ct_kib(N, L):
    return 2 * N * L * 8 // 1024


def openfhe_run(d, args, reps):
    os.makedirs(d, exist_ok=True)
    r = sh([BGV, "run", d, *args, "--time", str(reps)], env={**os.environ, "OMP_NUM_THREADS": "1"})
    if r.returncode != 0:
        return None, f"bgv_demo failed: {r.stdout.strip()} {r.stderr.strip()[-300:]}"
    prog = os.path.join(d, "prog.fhecheck.json")
    x = sh([sys.executable, "-I", os.path.join(FRONT, "openfhe/extract.py"), "--params", os.path.join(d, "params.json"),
            "--trace", os.path.join(d, "trace.jsonl"), "--artifact", os.path.basename(d)])
    if x.returncode != 0:
        return None, "extraction failed: " + x.stdout[-300:]
    open(prog, "w").write(x.stdout)
    v = sh([sys.executable, "-I", os.path.join(FRONT, "openfhe/value_check.py"), prog, os.path.join(d, "values.json")])
    if "value_check: OK" not in v.stdout:
        return None, "value check failed: " + v.stdout[-300:]
    timing = json.load(open(os.path.join(d, "timing.json")))
    return {"prog": prog, "timing": timing, "params": json.load(open(prog))["params"]}, None


def time_pair(d, args_a, args_b, rounds, reps):
    """Interleaved timing: `rounds` x (A, B), each a bgv_demo run timing `reps` untraced
    evaluations. Returns per-config {median, min} over all runs (milliseconds). Other processes on
    the machine disturb single runs; the minimum is the least disturbed figure."""
    out = {"a": [], "b": []}
    loads = []
    for _ in range(rounds):
        loads.append(load1())
        for key, args in (("a", args_a), ("b", args_b)):
            t = os.path.join(d, f"timing_{key}")
            os.makedirs(t, exist_ok=True)
            r = sh([BGV, "run", t, *args, "--time", str(reps)], env={**os.environ, "OMP_NUM_THREADS": "1"})
            if r.returncode != 0:
                return None
            out[key] += json.load(open(os.path.join(t, "timing.json")))["ms"]
    def summ(xs):
        xs = sorted(xs)
        return {"medianMs": xs[len(xs) // 2], "minMs": xs[0], "runs": len(xs)}
    try:
        load = open("/proc/loadavg").read().split()[0]
    except OSError:
        load = "?"
    return {"default": summ(out["a"]), "recommended": summ(out["b"]), "loadavg": load,
            "loads": loads, "loadMedian": sorted(loads)[len(loads) // 2], "rounds": rounds}


def load1():
    try:
        return float(open("/proc/loadavg").read().split()[0])
    except OSError:
        return float("nan")


def keep_old_timing(rows, old_rows, max_load):
    """If the 1-minute load was not below max_load (median over every timing round of the
    section; one decision for the whole section, so the ratios stay comparable), the new timings
    are not kept: the timings of the earlier run (old_rows, same D) are carried over with
    `remeasure: true`. Rows without an earlier timing keep the new one, marked the same way."""
    old = {r["D"]: r.get("timing") for r in old_rows or []}
    loads = sorted(x for row in rows for x in (row.get("timing") or {}).get("loads", []))
    if not loads or loads[len(loads) // 2] < max_load:
        return
    for row in rows:
        t = row.get("timing")
        if not t:
            continue
        o = old.get(row["D"])
        if o:
            o = dict(o)
            o["remeasure"] = True
            o["discardedLoadMedian"] = t["loadMedian"]
            row["timing"] = o
        else:
            t["remeasure"] = True


def body_ops(path):
    b = json.load(open(path))["program"]["body"]
    return [{k: v for k, v in i.items() if k != "expect"} for i in b]


def section_openfhe(out, depths, reps, extra):
    rows = []
    for D in depths:
        d = os.path.join(out, f"openfhe_fixedmanual_d{D}")
        base_args = ["--scal", "FIXEDMANUAL", "--prog", "chain", "--depth", str(D)]
        base, err = openfhe_run(os.path.join(d, "default"), base_args, 1)
        if err:
            rows.append({"D": D, "error": "default: " + err}); continue
        brep = check(base["prog"])
        rc, rec = recommend(base["prog"], os.path.join(d, "rec.fhecheck.json"), *extra)
        row = {"D": D, "default": {"N": base["params"]["N"], "limbBits": [int(l["q"]).bit_length() for l in base["params"]["limbs"]],
                                   "specialBits": [int(l["q"]).bit_length() for l in base["params"]["special"]],
                                   "verdict": brep["verdict"], "verdictLabel": brep.get("verdictLabel", brep["verdict"]),
                                   "margin": min_margin(brep),
                                   "log2QP": qp_bits(base["params"])[0],
                                   "dnum": json.load(open(base["prog"]))["keySwitching"]["digits"].get("dnum")}}
        row["recommend"] = {"verdict": rec["verdict"], "summary": rec["summary"]}
        if rc != 0:
            rows.append(row); continue
        row["recommend"].update({k: rec[k] for k in ("N", "firstModSize", "scalingModSize", "digits", "limbBits", "specialBits", "log2QP", "minMarginBits")})
        regen_args = ["--scal", "FIXEDMANUAL", "--prog", "chain", "--depth", str(D),
                      "--firstbits", str(rec["firstModSize"]), "--qbits", str(rec["scalingModSize"]),
                      "--dnum", str(rec["digits"]), "--ringdim", str(rec["N"])]
        regen, err = openfhe_run(os.path.join(d, "regenerated"), regen_args, 1)
        if err:
            row["regenerated"] = {"error": err}; rows.append(row); continue
        rrep = check(regen["prog"])
        _, rq, rp = qp_bits(regen["params"])
        row["regenerated"] = {
            "N": regen["params"]["N"], "verdict": rrep["verdict"],
            "verdictLabel": rrep.get("verdictLabel", rrep["verdict"]), "margin": min_margin(rrep),
            "primesAsPredicted": [str(x) for x in rq] == rec["limbs"] and [str(x) for x in rp] == rec["special"],
            "sameProgram": body_ops(regen["prog"]) == body_ops(base["prog"]),
            "log2QP": qp_bits(regen["params"])[0]}
        row["timing"] = time_pair(d, base_args, regen_args, ROUNDS, reps)
        L = len(base["params"]["limbs"])
        row["ctKiB"] = [ct_kib(base["params"]["N"], L), ct_kib(regen["params"]["N"], L)]
        rows.append(row)
        print(f"[openfhe] D={D}: default {row['default']['verdict']} ({row['default']['margin']}); "
              f"recommended f={rec['firstModSize']} s={rec['scalingModSize']} dnum={rec['digits']} N={rec['N']}; "
              f"OpenFHE regenerated -> {rrep['verdict']} ({row['regenerated']['margin']}), primes as predicted: "
              f"{row['regenerated']['primesAsPredicted']}, timing {row['timing']}",
              file=sys.stderr)
    return rows


AUTO_EVALADD = [5, 10, 20, 50, 100, 200, 500, 1000, 2000, 5000, 10000, 20000, 50000, 100000]


def section_auto(out, depths, reps, modes=("FIXEDAUTO", "FLEXIBLEAUTO", "FLEXIBLEAUTOEXT")):
    rows = []
    for mode in modes:
        for D in depths:
            d = os.path.join(out, f"auto_{mode.lower()}_d{D}")
            base, err = openfhe_run(os.path.join(d, "ea5"), ["--scal", mode, "--prog", "chain", "--depth", str(D)], reps)
            if err:
                rows.append({"mode": mode, "D": D, "error": err}); continue
            brep = check(base["prog"])
            rc, rec = recommend(base["prog"], os.path.join(d, "rec.json"))
            row = {"mode": mode, "D": D, "default": {"N": base["params"]["N"], "limbBits": [int(l["q"]).bit_length() for l in base["params"]["limbs"]],
                                                     "verdict": brep["verdict"], "margin": min_margin(brep), "evalMs": base["timing"]["medianMs"]},
                   "recommend": {"exit": rc, "verdict": rec["verdict"]}, "tried": []}
            found = None
            if brep["verdict"] == "CERTIFIED":
                found = {"evalAdd": 5, "N": base["params"]["N"], "margin": min_margin(brep), "evalMs": base["timing"]["medianMs"],
                         "limbBits": row["default"]["limbBits"]}
            for ea in AUTO_EVALADD[1:]:
                if found:
                    break
                run, err = openfhe_run(os.path.join(d, f"ea{ea}"), ["--scal", mode, "--prog", "chain", "--depth", str(D), "--evaladd", str(ea)], reps)
                if err:   # OpenFHE refused this value; record it and try the next one
                    row["tried"].append({"evalAdd": ea, "error": err[:300]}); continue
                rep = check(run["prog"])
                row["tried"].append({"evalAdd": ea, "N": run["params"]["N"], "verdict": rep["verdict"], "margin": min_margin(rep)})
                if rep["verdict"] == "CERTIFIED":
                    found = {"evalAdd": ea, "N": run["params"]["N"], "margin": min_margin(rep), "evalMs": run["timing"]["medianMs"],
                             "limbBits": [int(l["q"]).bit_length() for l in run["params"]["limbs"]]}
            row["found"] = found
            rows.append(row)
            print(f"[auto] {mode} D={D}: default {row['default']['verdict']} ({row['default']['margin']}); "
                  f"certified with SetEvalAddCount: {found['evalAdd'] if found else 'none tried'}", file=sys.stderr)
    return rows


def heir_compile(src_text, path_in, path_out, model):
    open(path_in, "w").write(src_text)
    opt = "annotate-noise-bound=true" + (f" noise-model={model}" if model else "")
    r = sh([HEIR, '--annotate-module=backend=lattigo scheme=bgv', f"--mlir-to-bgv={opt}", path_in])
    if r.returncode != 0:
        return f"heir-opt failed: {r.stderr[-300:]}"
    open(path_out, "w").write(r.stdout)
    return None


def heir_extract(mlir, out):
    x = sh([sys.executable, "-I", os.path.join(FRONT, "heir/extract_bgv.py"), mlir])
    if x.returncode != 0:
        return "extraction failed: " + (x.stdout + x.stderr)[-300:]
    open(out, "w").write(x.stdout)
    return None


def section_heir(out, progs, reps):
    rows = []
    for name in progs:
        d = os.path.join(out, f"heir_{name}")
        os.makedirs(d, exist_ok=True)
        if not HEIR_SRC:
            sys.exit("roundtrip.py --heir: set HEIR_EXAMPLES to the directory of the HEIR example .mlir files")
        src = open(os.path.join(HEIR_SRC, f"{name}.mlir")).read()
        row = {"program": name}
        for model, tag in ((None, "default"), ("bgv-noise-by-bound-coeff-worst-case", "worstcase")):
            mlir, js = os.path.join(d, f"{tag}.bgv.mlir"), os.path.join(d, f"{tag}.fhecheck.json")
            err = heir_compile(src, os.path.join(d, "in.mlir"), mlir, model) or heir_extract(mlir, js)
            if err:
                row[tag] = {"error": err}; continue
            rep = check(js)
            params = json.load(open(js))["params"]
            row[tag] = {"N": params["N"], "limbBits": [int(l["q"] if isinstance(l, dict) else l).bit_length() for l in params["limbs"]],
                        "specialBits": [int(l["q"] if isinstance(l, dict) else l).bit_length() for l in params["special"]],
                        "verdict": rep["verdict"], "verdictLabel": rep.get("verdictLabel", rep["verdict"]),
                        "margin": min_margin(rep), "log2QP": qp_bits(params)[0]}
        base = os.path.join(d, "default.fhecheck.json")
        if not os.path.exists(base):
            rows.append(row); continue
        rc, rec = recommend(base, os.path.join(d, "rec.fhecheck.json"))
        row["recommend"] = {"verdict": rec["verdict"], "summary": rec["summary"]}
        if rc == 0:
            row["recommend"].update({k: rec[k] for k in ("N", "limbBits", "specialBits", "log2QP", "minMarginBits", "sizes", "specialSize")})
            enc = json.load(open(base))["source"].get("encryptionTechnique", "extended")
            attr = (f"module attributes {{bgv.schemeParam = #bgv.scheme_param<logN = {int(math.log2(rec['N']))}, "
                    f"Q = [{', '.join(rec['limbs'])}], P = [{', '.join(rec['special'])}], plaintextModulus = {rec['t']}, "
                    f"encryptionTechnique = {enc}>}} {{\n{src}\n}}\n")
            mlir, js = os.path.join(d, "regenerated.bgv.mlir"), os.path.join(d, "regenerated.fhecheck.json")
            err = heir_compile(attr, os.path.join(d, "in.schemeparam.mlir"), mlir, "bgv-noise-by-bound-coeff-worst-case") or heir_extract(mlir, js)
            if err:
                row["regenerated"] = {"error": err}
            else:
                rep = check(js)
                params = json.load(open(js))["params"]
                _, rq, rp = qp_bits(params)
                row["regenerated"] = {"N": params["N"], "verdict": rep["verdict"],
                                      "verdictLabel": rep.get("verdictLabel", rep["verdict"]), "margin": min_margin(rep),
                                      "primesAsPredicted": [str(x) for x in rq] == rec["limbs"] and [str(x) for x in rp] == rec["special"],
                                      "sameProgram": body_ops(js) == body_ops(base), "log2QP": qp_bits(params)[0]}
        # run the programs on Lattigo (HEIR's own code generation) at HEIR's parameters and ours
        bins = {}
        for tag in ("default", "worstcase", "regenerated"):
            m = os.path.join(d, f"{tag}.bgv.mlir")
            if os.path.exists(m) and os.path.exists(HEIR_TRANSLATE):
                b, err = lattigo_build(os.path.join(d, f"go_{tag}"), m, name)
                if err:
                    row.setdefault("lattigoErrors", {})[tag] = err
                else:
                    bins[tag] = b
        if bins:
            row["lattigo"] = lattigo_time_pair(bins, ROUNDS, max(3, reps // 3))
        rows.append(row)
        print(f"[heir] {name}: {json.dumps(row)[:600]}", file=sys.stderr)
    return rows


def tables(res):
    """Markdown tables of a roundtrip.json (for the README)."""
    L = []
    if res.get("openfhe"):
        L += ["| D | OpenFHE default (FIXEDMANUAL) | verdict | recommended | OpenFHE's primes = predicted | re-check on OpenFHE's primes | log2(Q*P) | ciphertext | evaluation (min of runs) |",
              "|---|---|---|---|---|---|---|---|---|"]
        for r in res["openfhe"]:
            if "error" in r or "regenerated" not in r or "error" in r.get("regenerated", {}):
                L.append(f"| {r['D']} | {r.get('error') or r.get('regenerated', {}).get('error') or r['recommend']['summary']} |"); continue
            b, c, g, t = r["default"], r["recommend"], r["regenerated"], r["timing"]
            bv = "certified" if b["verdict"] == "CERTIFIED" else "not certified"
            L.append(f"| {r['D']} | N=2^{int(math.log2(b['N']))}, {'+'.join(map(str, b['limbBits']))}, dnum {b['dnum']} | {bv} ({b['margin']}) "
                     f"| N=2^{int(math.log2(c['N']))}, f={c['firstModSize']}, s={c['scalingModSize']}, dnum {c['digits']} "
                     f"| {'yes' if g['primesAsPredicted'] else 'NO'} | {g['verdict'].lower()} ({g['margin']}) "
                     f"| {b['log2QP']:.1f} -> {g['log2QP']:.1f} | {r['ctKiB'][0]} -> {r['ctKiB'][1]} KiB "
                     f"| {t['default']['minMs']:.1f} -> {t['recommended']['minMs']:.1f} ms (x{t['recommended']['minMs'] / t['default']['minMs']:.2f}) |")
    if res.get("heir"):
        L += ["", "| program | HEIR default (average-case) | HEIR worst-case model | recommended | HEIR's primes = predicted | re-check | log2(Q*P) default / worst / rec | Lattigo evaluation, min (default / worst / rec) |",
              "|---|---|---|---|---|---|---|---|"]
        for r in res["heir"]:
            d, w, c, g = r.get("default", {}), r.get("worstcase", {}), r.get("recommend", {}), r.get("regenerated", {})
            lt = r.get("lattigo", {})
            f = lambda x: f"N=2^{int(math.log2(x['N']))}, {'+'.join(map(str, x['limbBits']))} / P {'+'.join(map(str, x['specialBits']))}"
            tm = " / ".join(f"{lt[k]['minMs']:.1f}{'' if lt[k].get('ok') else ' WRONG'}" for k in ("default", "worstcase", "regenerated") if k in lt)
            L.append(f"| {r['program']} | {f(d)}: {d['verdict'].lower()} ({d['margin']}) | {f(w)}: {w['verdict'].lower()} ({w['margin']}) "
                     f"| {f(c)} | {'yes' if g.get('primesAsPredicted') else 'NO'} | {g.get('verdict', '?').lower()} ({g.get('margin')}) "
                     f"| {d['log2QP']:.1f} / {w['log2QP']:.1f} / {g.get('log2QP', 0):.1f} | {tm} ms |")
    if res.get("auto"):
        L += ["", "| technique | D | OpenFHE default (SetEvalAddCount 5): N, limb bits, verdict | smallest SetEvalAddCount tried that certifies | N, limb bits there | margin | ciphertext | evaluation (median) |",
              "|---|---|---|---|---|---|---|---|"]
        for r in res["auto"]:
            if "error" in r:
                L.append(f"| {r['mode']} | {r['D']} | {r['error'][:80]} |"); continue
            fd = r.get("found")
            last = r["tried"][-1] if r["tried"] else {}
            refused = [t["evalAdd"] for t in r["tried"] if "error" in t]
            b = r["default"]
            bd = f"2^{int(math.log2(b['N']))}, {'+'.join(map(str, b['limbBits']))}: {b['verdict'].lower()} ({b['margin']})"
            if fd:
                L.append(f"| {r['mode']} | {r['D']} | {bd} | {fd['evalAdd']} | 2^{int(math.log2(fd['N']))}, {'+'.join(map(str, fd['limbBits']))} "
                         f"| {fd['margin']} | {ct_kib(b['N'], len(b['limbBits']))} -> {ct_kib(fd['N'], len(fd['limbBits']))} KiB "
                         f"| {b['evalMs']:.1f} -> {fd['evalMs']:.1f} ms"
                         + (f" (OpenFHE threw for SetEvalAddCount {', '.join(map(str, refused))})" if refused else "") + " |")
            else:
                L.append(f"| {r['mode']} | {r['D']} | {bd} | none up to {last.get('evalAdd')} | {last.get('margin', '')} | | | "
                         + (f"(OpenFHE threw for SetEvalAddCount {', '.join(map(str, refused))})" if refused else "") + " |")
    return "\n".join(L)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("outdir", nargs="?", default="")
    ap.add_argument("--openfhe", action="store_true")
    ap.add_argument("--auto", action="store_true")
    ap.add_argument("--heir", action="store_true")
    ap.add_argument("--depths", default="1,2,3,4,5,6,7,8")
    ap.add_argument("--reps", type=int, default=15)
    ap.add_argument("--modes", default="FIXEDAUTO,FLEXIBLEAUTO,FLEXIBLEAUTOEXT", help="--auto: scaling techniques")
    ap.add_argument("--table", metavar="ROUNDTRIP_JSON", help="only print the markdown tables of a previous run")
    ap.add_argument("--recommend-args", default="", help="extra arguments for fhe_check recommend (OpenFHE section)")
    ap.add_argument("--rounds", type=int, default=7, help="interleaved timing rounds (OpenFHE section)")
    ap.add_argument("--max-load", type=float, default=20.0,
                    help="timings are kept only if the median 1-minute load over the rounds is below this")
    ap.add_argument("--keep-time", metavar="OLD_ROUNDTRIP_JSON",
                    help="carry the timings of this earlier run over (remeasure: true) where the load was too high")
    a = ap.parse_args()
    global ROUNDS
    ROUNDS = a.rounds
    if a.table:
        print(tables(json.load(open(a.table))))
        return
    if not (a.openfhe or a.auto or a.heir):
        a.openfhe = a.auto = a.heir = True
    depths = [int(x) for x in a.depths.split(",")]
    os.makedirs(a.outdir, exist_ok=True)
    res = {"fheCheck": os.path.relpath(FHE_CHECK, ROOT), "reps": a.reps, "ompThreads": 1, "rounds": a.rounds,
           "maxLoad": a.max_load, "threads": os.cpu_count()}
    if a.openfhe:
        res["openfhe"] = section_openfhe(a.outdir, depths, a.reps, a.recommend_args.split())
        old = json.load(open(a.keep_time)).get("openfhe") if a.keep_time else None
        keep_old_timing(res["openfhe"], old, a.max_load)
    if a.heir:
        res["heir"] = section_heir(a.outdir, ["mult_dep_8", "dot_product_8"], a.reps)
        old = {h["program"]: h for h in json.load(open(a.keep_time)).get("heir", [])} if a.keep_time else {}
        for h in res["heir"]:  # same rule as keep_old_timing, for the Lattigo timings
            lt = h.get("lattigo")
            if lt and lt.get("loadMedian", 0) >= a.max_load:
                o = (old.get(h["program"]) or {}).get("lattigo")
                if o:
                    o = dict(o)
                    o["remeasure"] = True
                    o["discardedLoadMedian"] = lt["loadMedian"]
                    for k in ("default", "worstcase", "regenerated"):  # correctness of the new run
                        if k in lt and k in o:
                            o[k] = dict(o[k], okRerun=lt[k].get("ok"))
                    h["lattigo"] = o
                else:
                    lt["remeasure"] = True
    if a.auto:
        res["auto"] = section_auto(a.outdir, depths, max(3, a.reps // 3), a.modes.split(","))
    json.dump(res, open(os.path.join(a.outdir, "roundtrip.json"), "w"), indent=1)
    print(tables(res))


if __name__ == "__main__":
    main()
