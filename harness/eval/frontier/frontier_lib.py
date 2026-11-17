"""Shared glue for harness/eval/frontier (UNTRUSTED: nothing here decides a verdict).

Every verdict comes from a plain `fhe_check` run (`check`) on a file extracted from a traced
OpenFHE run (`traced_run`): the search code only chooses WHICH library settings to run.

Paths: the repository root is found from this file; the drivers (build.sh) and fhe_check are taken
from $FRONTIER_BIN (default: <out>/bin) and $FHE_CHECK (default: <repo>/.lake/build/bin/fhe_check).
"""
import hashlib, json, math, os, shutil, subprocess, sys, threading

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "..", "..", ".."))
OPENFHE_FRONT = os.path.join(ROOT, "harness", "frontend", "openfhe")


class Env:
    def __init__(self, out):
        self.out = os.path.abspath(out)
        self.bin = os.path.abspath(os.environ.get("FRONTIER_BIN", os.path.join(self.out, "bin")))
        self.fc = os.path.abspath(os.environ.get("FHE_CHECK", os.path.join(ROOT, ".lake", "build", "bin", "fhe_check")))
        self.runs = os.path.join(self.out, "runs")
        os.makedirs(self.runs, exist_ok=True)


def sh(cmd, timeout=3600):
    e = dict(os.environ, OMP_NUM_THREADS="1")
    try:
        p = subprocess.run(cmd, capture_output=True, text=True, timeout=timeout, env=e)
    except subprocess.TimeoutExpired:
        return 124, "", "timeout"
    return p.returncode, p.stdout, p.stderr


def lg2(n):
    n = int(n)
    return math.log2(n) if n > 0 else 0.0


def key(args):
    return hashlib.sha1(" ".join(args).encode()).hexdigest()[:16]


def lib_args(scheme, cfg):
    """Driver arguments for a configuration dict (only the public CCParams setters)."""
    a = []
    order = ["scal", "mult", "ks", "depth", "progdepth", "prog", "t", "qbits", "firstbits", "dnum",
             "ringdim", "evaladd", "kscount"]
    for k in order:
        v = cfg.get(k)
        if v is None or v == "" or v == 0 and k not in ("depth",):
            continue
        a += [f"--{k}", str(v)]
    return a


def params_only(env, scheme, cfg):
    """The context OpenFHE generates for cfg (params.json), or {'error': ...}. Cached."""
    args = lib_args(scheme, {k: v for k, v in cfg.items() if k not in ("prog", "progdepth")})
    d = os.path.join(env.runs, "params", scheme, key(args))
    pj = os.path.join(d, "params.json")
    if os.path.exists(pj):
        return json.load(open(pj))
    if os.path.exists(d + "/error"):
        return {"error": open(d + "/error").read()}
    # generated in a private directory and renamed into place: concurrent callers never read a
    # partly written file
    tmp = f"{d}.tmp{os.getpid()}.{threading.get_ident()}"
    os.makedirs(tmp, exist_ok=True)
    os.makedirs(d, exist_ok=True)
    rc, o, e = sh([os.path.join(env.bin, f"frontier_{scheme}"), "params", tmp] + args, timeout=600)
    if rc != 0 or not os.path.exists(tmp + "/params.json"):
        msg = f"rc={rc}: {(o + e).strip()[-300:]}"
        open(tmp + "/error", "w").write(msg)
        os.replace(tmp + "/error", d + "/error")
        shutil.rmtree(tmp, ignore_errors=True)
        return {"error": msg}
    os.replace(tmp + "/params.json", pj)
    shutil.rmtree(tmp, ignore_errors=True)
    return json.load(open(pj))


def shape(p):
    """(N, limb bits, special bits) of a params.json."""
    if "error" in p:
        return None
    N = int(p["N"])
    q = [int(x if not isinstance(x, dict) else x["q"]) for x in p.get("qs", p.get("limbs", []))]
    s = [int(x if not isinstance(x, dict) else x["q"]) for x in p.get("special", p.get("ps", []))]
    return N, q, s


def traced_run(env, scheme, cfg):
    """Run the program traced (single-threaded build), extract, value-check.
    Returns (x.json path or None, info dict)."""
    args = lib_args(scheme, cfg)
    d = os.path.join(env.runs, scheme, key(args))
    x = d + "/x.json"
    if os.path.exists(x) and os.path.exists(d + "/ok"):
        return x, json.load(open(d + "/ok"))
    if os.path.exists(d + "/fail"):
        return None, json.load(open(d + "/fail"))
    shutil.rmtree(d, ignore_errors=True)
    os.makedirs(d)
    json.dump({"scheme": scheme, "cfg": cfg, "args": args}, open(d + "/cfg.json", "w"))
    rc, o, e = sh([os.path.join(env.bin, f"frontier_{scheme}"), "run", d] + args)
    if rc != 0:
        info = {"error": f"driver rc={rc}: {(o + e).strip()[-400:]}"}
        json.dump(info, open(d + "/fail", "w"))
        return None, info
    ex = "extract.py" if scheme == "bgv" else "extract_bfv.py"
    rc, o, e = sh([sys.executable, "-I", os.path.join(OPENFHE_FRONT, ex), "--params", d + "/params.json",
                   "--trace", d + "/trace.jsonl"])
    if rc != 0:
        info = {"error": f"extract rc={rc}: {e.strip()[-400:]}"}
        json.dump(info, open(d + "/fail", "w"))
        return None, info
    open(x, "w").write(o)
    vc = "value_check.py" if scheme == "bgv" else "value_check_bfv.py"
    rc, o, e = sh([sys.executable, "-I", os.path.join(OPENFHE_FRONT, vc), x, d + "/values.json"])
    chk = open(d + "/check.txt").read() if os.path.exists(d + "/check.txt") else ""
    info = {"valueCheck": rc == 0 and "OK" in o, "valueMsg": (o + e).strip()[-300:],
            "cleartextCheck": "cleartext check: OK" in chk, "dir": d}
    try:
        os.remove(d + "/trace.jsonl")  # large; the extracted file keeps what the check needs
    except OSError:
        pass
    json.dump(info, open(d + "/ok", "w"))
    return x, info


def check(env, x, kappa=None):
    """Plain fhe_check of an extracted file: the verdict and the numbers the tables need."""
    cmd = [env.fc, "--json", "--no-suggest"] + (["--kappa", str(kappa)] if kappa else []) + [x]
    rc, o, e = sh(cmd)
    try:
        j = json.loads(o)
    except Exception:
        return {"verdict": "ERROR", "err": (o + e)[-300:]}
    p = j.get("params", {})
    r = {"verdict": j.get("verdictLabel") or j.get("verdict"), "N": int(p.get("N", 0)),
         "limbBits": [round(lg2(q), 2) for q in p.get("limbs", [])],
         "specialBits": [round(lg2(q), 2) for q in p.get("special", [])], "log2Q": p.get("log2Q")}
    r["log2QP"] = round((r["log2Q"] or 0) + sum(r["specialBits"]), 2)
    outs = j.get("outputs") or []
    if outs:
        r["margin"] = min(min(o_.get("marginBits", 1e9), o_.get("decMarginBits", 1e9)) for o_ in outs)
    f = j.get("failure") or {}
    ff = f.get("firstFailing") or {}
    if ff:
        r["over"] = ff.get("overflowBits")
        r["failAt"] = ff.get("index")
        r["failOp"] = ff.get("op")
    if f.get("reason") and not ff:
        r["reason"] = f.get("reason")
    if r["verdict"] not in ("CERTIFIED", "NOT CERTIFIED"):
        r["summary"] = (j.get("summary") or "")[:300]
    return r


def certified(c):
    return (c.get("verdict") or "").startswith("CERTIFIED")
