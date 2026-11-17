#!/usr/bin/env python3
"""Tests of fhe_check's profile mode (--profile FILE, --emit-profile); run.sh section 11.

Usage: check_profile.py FHE_CHECK   (from harness/frontend)

Prints one line per check, "ok ..." or "FAIL ...", and nothing else. run.sh counts them.

1. Round trip: for every committed example and negative, the profile --emit-profile writes is
   accepted by --profile whenever the table mode certifies the file, with the same whole-program
   and per-output bounds (the executable side of Challenge.Profile.certify?_profile,
   certifyBFV?_profile and Validation.FastProfile.certifyFast_profileFast). For a BFV file the
   emitted per-instruction table is exactly the table mode's budget (--json budget.perInstruction).
2. A larger budget flips CERTIFIED to NOT CERTIFIED at the expected instruction (BGV and BFV).
3. A key-switching budget below what the proved family needs: still CERTIFIED (the decision is
   sound at every budget), reported as NOT covered, with the conditional wording.
4. A Lattigo-shaped profile (Challenge.Instances.Lattigo.profile small) certifies the recorded
   program shape smallProg, covered, at the bound the locked definitions give (1385235815).
5. Malformed profiles: INVALID INPUT (exit 3); usage errors (exit 4).
"""
import glob
import json
import os
import subprocess
import sys
import tempfile

F = sys.argv[1]
TMP = tempfile.mkdtemp()


def run(*args):
    return subprocess.run([F, *args], capture_output=True, text=True, timeout=120)


def ok(cond, what):
    print(("ok " if cond else "FAIL ") + what)


def write(name, obj):
    p = os.path.join(TMP, name)
    with open(p, "w") as f:
        f.write(obj if isinstance(obj, str) else json.dumps(obj))
    return p


INTERNAL = []


def profile_json(prog, prof, *extra):
    r = run("--json", *extra, "--profile", prof, prog)
    if "INTERNAL" in r.stdout:
        INTERNAL.append(prog)
    try:
        return r.returncode, json.loads(r.stdout)
    except json.JSONDecodeError:
        return r.returncode, None


# ---------------------------------------------------------------- 1. round trip
files = sorted(glob.glob("examples/*.fhecheck.json") + glob.glob("tests/negative/*.json")
               + glob.glob("tests/negative-bfv/*.json"))
n_cert = 0
for f in files:
    t = run("--json", "--no-suggest", f)
    if t.returncode != 0:
        continue
    n_cert += 1
    e = run("--emit-profile", f)
    if e.returncode != 0:
        ok(False, f"round trip {f}: --emit-profile failed: {e.stderr.strip()[:200]}")
        continue
    prof = write("rt.profile.json", e.stdout)
    code, pj = profile_json(f, prof)
    tj = json.loads(t.stdout)
    same = (code == 0 and pj is not None and pj["bound"] == tj["bound"]
            and [(o["name"], o["bound"]) for o in pj["outputs"]]
            == [(o["name"], o["bound"]) for o in tj["outputs"]])
    ok(same, f"round trip {f}: table CERTIFIED -> profile CERTIFIED at the emitted profile, same bounds")
    # Challenge.Profile.certify?_covers (BGV), certifyBFV?_coversAt (BFV, U = 0, r = 1): the table
    # mode's budget passes the coverage check on the file's layout
    ok(pj is not None and pj["coverage"].get("covered") is True,
       f"round trip {f}: the emitted profile is covered (certify?_covers / certifyBFV?_coversAt)")
    ej = json.loads(e.stdout)
    if ej["scheme"] == "BFV":
        pi = ej["perInstruction"]
        mine = [pi["budgets"][i] for i in pi["at"]]
        keys = ["keySwitch", "modSwitch", "mulLift", "mulRound", "plainAdd"]
        theirs = [{k: r[k] for k in keys} for r in tj["budget"]["perInstruction"]]
        ok(mine == theirs, f"round trip {f}: the emitted per-instruction budget is the table mode's")
ok(n_cert >= 80, f"round trip covered {n_cert} table-certified files (at least 80)")

# ---------------------------------------------------------------- 4. Lattigo-shaped profile
LP = "examples/profile/lattigo_small.fhecheck.json"
LF = "examples/profile/lattigo_small.profile.json"
code, pj = profile_json(LP, LF)
ok(code == 0 and pj["verdict"] == "CERTIFIED" and pj["bound"] == "1385235815"
   and pj["coverage"]["covered"] is True,
   "Lattigo profile: CERTIFIED, covered (coversBGV? at K = 3), bound 1385235815 as the locked #eval")
human = run("--profile", LF, LP).stdout
ok("VERDICT: CERTIFIED for every implementation within the declared profile" in human
   and "IS covered by the proved algorithm families" in human, "Lattigo profile: verdict wording")
ok("openfhe" not in json.load(open(LP))["source"]["tool"].lower() and "bfv" not in json.load(open(LP)),
   "Lattigo profile: the program file is not an OpenFHE extraction and declares no technique table")

# ---------------------------------------------------------------- 2. a larger budget flips the verdict
base = json.load(open(LF))
big = json.loads(json.dumps(base))
big["budget"]["keySwitch"] = str(2 ** 60)
code, pj = profile_json(LP, write("big.json", big))
ok(code == 1 and pj["verdict"] == "NOT CERTIFIED" and pj["failedAt"] == 6,
   "BGV: keySwitch 2^60 flips CERTIFIED to NOT CERTIFIED at body[6] (the square after the key switches: 2B >= Q there)")

BF = "examples/openfhe_bfv_hps_hybrid_chain_d1.fhecheck.json"
e = run("--emit-profile", BF)
ej = json.loads(e.stdout)
code, pj = profile_json(BF, write("bfv.json", ej))
ok(code == 0, "BFV: the emitted profile of openfhe_bfv_hps_hybrid_chain_d1 is CERTIFIED")
body = json.load(open(BF))["program"]["body"]
k = next(i for i, ins in enumerate(body) if ins["op"] in ("relin", "keySwitch"))
pi = ej["perInstruction"]
nb = dict(pi["budgets"][pi["at"][k]])
nb["keySwitch"] = str(2 ** 110)
pi["budgets"].append(nb)
pi["at"][k] = len(pi["budgets"]) - 1
code, pj = profile_json(BF, write("bfvbig.json", ej))
ok(code == 1 and pj["failedAt"] == k,
   f"BFV: keySwitch 2^110 at body[{k}] only flips CERTIFIED to NOT CERTIFIED at body[{k}]")

# ---------------------------------------------------------------- 3. certified but not covered
small = json.loads(json.dumps(base))
small["budget"]["keySwitch"] = "1"
code, pj = profile_json(LP, write("small.json", small))
ok(code == 0 and pj["verdict"] == "CERTIFIED" and pj["coverage"]["covered"] is False,
   "BGV: keySwitch 1 is CERTIFIED and NOT covered (exit 0, coverage.covered = false)")
human = run("--profile", write("small.json", small), LP).stdout
ok("is NOT covered by the proved algorithm families, so this is a conditional statement" in human
   and "key switching (NOT covered)" in human, "BGV: certified-but-uncovered wording")
ej = json.loads(e.stdout)
pi = ej["perInstruction"]
pi["budgets"] = [dict(b, keySwitch="0") for b in pi["budgets"]]
code, pj = profile_json(BF, write("bfvsmall.json", ej))
ok(code == 0 and pj["coverage"]["covered"] is False and pj["coverage"]["classes"]["keySwitch"] is False
   and pj["coverage"]["classes"]["mul"] is True,
   "BFV: keySwitch 0 everywhere is CERTIFIED, NOT covered (key switching only)")
uni = {"format": "fhe-check-profile/v1", "scheme": "BFV",
       "uniform": {"keySwitch": "0", "modSwitch": "0", "mulLift": "0", "mulRound": "0", "plainAdd": "0"}}
code, pj = profile_json(BF, write("zero.json", uni))
ok(code == 0 and pj["coverage"]["covered"] is False,
   "BFV: the zero profile is CERTIFIED (sound at every budget) and NOT covered")

# ---------------------------------------------------------------- 5. malformed profiles, usage errors
def mutate(f):
    p = json.loads(json.dumps(base))
    f(p)
    return p


bad = {
    "format": mutate(lambda p: p.update(format="fhe-check-profile/v0")),
    "unknown top-level field": mutate(lambda p: p.update(budgets={})),
    "unknown budget field": mutate(lambda p: p["budget"].update(keyswitch="1")),
    "missing modSwitchMany default": mutate(lambda p: p["budget"]["modSwitchMany"].pop("default")),
    "modSwitchMany at parts 2": mutate(lambda p: p["budget"]["modSwitchMany"]["at"].append({"parts": 2, "bound": "1"})),
    "negative number": mutate(lambda p: p["budget"].update(keySwitch=-1)),
    "scheme BFV for a BGV program": mutate(lambda p: p.update(scheme="BFV")),
    "unknown scheme": mutate(lambda p: p.update(scheme="CKKS")),
    "coverage.mulFamily on BGV": mutate(lambda p: p["coverage"].update(mulFamily={"U": 0, "r": 1})),
}
for what, p in bad.items():
    r = run("--profile", write("bad.json", p), LP)
    ok(r.returncode == 3 and "INVALID INPUT" in r.stdout, f"malformed profile ({what}): INVALID INPUT, exit 3")
r = run("--profile", write("bad.txt", "{ not json"), LP)
ok(r.returncode == 3, "malformed profile (not JSON): exit 3")
ej = json.loads(e.stdout)
both = dict(ej, uniform=uni["uniform"])
short = json.loads(e.stdout); short["perInstruction"]["at"] = short["perInstruction"]["at"][:-1]
oob = json.loads(e.stdout); oob["perInstruction"]["at"][0] = 99
for what, p in {"uniform and perInstruction": both, "perInstruction.at shorter than the body": short,
                "perInstruction.at index out of range": oob,
                "BGV profile for a BFV program": base}.items():
    r = run("--profile", write("bad.json", p), BF)
    ok(r.returncode == 3 and "INVALID INPUT" in r.stdout, f"malformed profile ({what}): INVALID INPUT, exit 3")
r = run("--json", "--profile", write("bad.json", bad["format"]), LP)
ok(r.returncode == 3 and json.loads(r.stdout)["verdict"] == "INVALID INPUT", "malformed profile: --json verdict INVALID INPUT")
ok(run("--kappa", "128", "--profile", LF, LP).returncode == 4, "--profile with --kappa: usage error (exit 4)")
ok(run("--emit-profile", "--profile", LF, LP).returncode == 4, "--profile with --emit-profile: usage error (exit 4)")
ok(run("--profile").returncode == 4, "--profile without a file: usage error (exit 4)")
ok(not INTERNAL, f"no profile-mode report disagrees between the per-class coverage diagnostic and the locked check ({sorted(set(INTERNAL))[:3]})")
