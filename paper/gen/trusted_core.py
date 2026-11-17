#!/usr/bin/env python3
"""UNTRUSTED: the reading closure of the headline statements (docs/TRUSTED-CORE.md), by script.

    python3 -I paper/gen/trusted_core.py [--tsv FILE] [--out FILE] [--table GROUP]

Runs `lake env lean --run paper/gen/trusted_core.lean` (needs a built tree; about 15 s) on the
headline groups of HEADLINES and writes docs/trusted-core.json (default --out): for each group and
for the unions in UNIONS, every declaration of `Spec/**` and `Challenge/**` that a reader must read
to know what the group's statements claim (the statements' types; the definitions, inductive types
and structures they mention, unfolded transitively; not proofs, and not the statements of lemmas
used inside proof terms), with file, line range (from Lean's declaration ranges, docstring
included), line count and depth (0 = a headline; 1 = mentioned by a headline; ...).

Counting rules, so the numbers can be checked by hand:
* an auxiliary constant without a declaration range (`f.match_1`, `f._f`, `T.ctorIdx`, ...) is
  counted as its nearest enclosing declaration that has one (found by the Lean helper);
* a reached declaration whose range lies inside another reached declaration's range (a
  constructor, a structure field) is counted as part of the enclosing one, not separately;
* `lines` of a set = the number of distinct source lines covered by its declarations' ranges
  (docstrings included; blank lines between declarations not included); `codeLines` the same from
  the line of the declaration's name (docstring excluded).
* the headline theorems themselves are counted (they are part of what is read).
--tsv reads a saved output of the Lean helper instead of running it. --table GROUP prints the
reading-order table (Markdown) of a group or union.
"""
import argparse
import json
import os
import re
import subprocess
import sys

ROOT = os.path.abspath(os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", ".."))
OUT = "docs/trusted-core.json"

HEADLINES = {
    "H1": ("profile certificate soundness, BGV and BFV",
           ["Challenge.Profile.certifyProfile?_sound", "Challenge.Profile.certifyBFVProfile?_sound"]),
    "H2": ("default-mode decision soundness, BGV and BFV (soundness at the certificate's budget, "
           "decryption of every output, and the worst-case certificate)",
           ["Challenge.Certify.certify?_sound", "Challenge.Certify.certify?_decrypts",
            "Challenge.Certify.worst_certified", "Challenge.CertifyBFV.certifyBFV?_sound",
            "Challenge.CertifyBFV.certifyBFV?_decrypts"]),
    "H3": ("security: fresh-only game (BFV, BGV) and the game with evaluation on earlier results",
           ["Challenge.IndCpaDProfile.correct_bfv", "Challenge.IndCpaDProfile.bfv_prob_eq",
            "Challenge.IndCpaDProfile.bfv_adv_le", "Challenge.IndCpaDProfile.correct_bgv",
            "Challenge.IndCpaDProfile.bgv_prob_eq", "Challenge.IndCpaDProfile.bgv_adv_le",
            "Challenge.IndCpaDLM.gameLM_eq_gameCPA", "Challenge.IndCpaDLM.advLM_le"]),
    "H4": ("algorithm level: BEHZ multiplication meets its contract; MSB transfer",
           ["Challenge.BFVMul.stepOK_mul_behz", "Challenge.MSB.certifyProfile?_sound_msb"]),
}
# Not a theorem: the decision functions themselves (what the tool runs, through equal fast
# functions) and everything they call; the paper's "locked decision functions and their analyses".
DECISIONS = ("the four locked decision functions and everything they call",
             ["Challenge.Certify.certify?", "Challenge.CertifyBFV.certifyBFV?",
              "Challenge.Profile.certifyProfile?", "Challenge.Profile.certifyBFVProfile?"])
# The two default-mode decision functions alone (the paper's introduction: "the locked reference
# functions certify? and certifyBFV? with the analyses they call").
DECISIONS_DEFAULT = ("the default-mode decision functions certify? and certifyBFV? and everything they call",
                     ["Challenge.Certify.certify?", "Challenge.CertifyBFV.certifyBFV?"])
# "What is claimed" reading of H1 and H3: as H1+H3, but the bodies of the decision functions are not
# unfolded (a soundness statement is true of whatever the decision accepts; its body says how much
# it accepts, not what acceptance means). Computed by the Lean helper, not as a union.
STOP_DECISIONS = ["Challenge.Profile.certifyProfile?", "Challenge.Profile.certifyBFVProfile?"]
UNIONS = {"H1+H2": ["H1", "H2"], "H1+H3": ["H1", "H3"], "ALL": ["H1", "H2", "H3", "H4"]}

# Layers of docs/TRUSTED-CORE.md "Reading order", by file: regular expressions matched at the start
# of the repository-relative path (first match wins).
LAYERS = [
    ("ring", "Ring and parameters", ["Spec/Ring.lean", "Spec/Params.lean", "Spec/Layout.lean",
                                     "Challenge/Ring.lean", "Challenge/Params.lean"]),
    ("encrypts", "Ciphertexts and the Encrypts relations", ["Spec/Scheme.lean", "Spec/Correct.lean",
                                                           "Spec/MSB.lean", "Spec/MSBScale.lean"]),
    ("decrypt", "Decryption", ["Spec/Decrypt.lean", "Spec/DecryptBFV.*", "Challenge/Decrypt.lean",
                               "Challenge/BFVDecrypt.*"]),
    ("source", "Source language and its semantics", ["Spec/Source.lean", "Challenge/Source.lean"]),
    ("runs", "Per-operation contracts (StepOK) and runs", ["Spec/Trace.lean", "Spec/TraceBFV.lean",
                                                          "Challenge/Trace.lean", "Challenge/BFV/PerInstr.lean",
                                                          "Challenge/BFVMul.*"]),
    ("budget", "Budgets and profiles", ["Spec/Budget.*", "Challenge/Budget.*", "Spec/Scaling.lean",
                                        "Challenge/Scaling.lean", "Spec/Float.lean"]),
    ("encrypt", "Encryption helpers", ["Spec/Encrypt.lean", "Spec/EncryptBFV.lean", "Challenge/BFVEncrypt.*",
                                     "Challenge/FreshNoise.*"]),
    ("certify", "Certificate functions", ["Spec/Certify.*", "Challenge/Certify.*", "Challenge/Headline.*",
                                          "Challenge/BFV/.*", "Challenge/BFV.lean", "Challenge/Profile.*",
                                          "Challenge/MSB.*", "Challenge/Realize.*"]),
    ("games", "Security games", ["Spec/IndCpaD.*", "Challenge/IndCpaD.*"]),
]


# Declarations whose layer is not their file's.
NAME_LAYER = {"Spec.Trace.Budget": "budget", "Spec.Trace.Budget.modSwitchAt": "budget",
              "Spec.TraceBFV.Budget": "budget", "Spec.TraceBFV.Bnd": "budget"}


def layer_of(f, name=None):
    if name in NAME_LAYER:
        return NAME_LAYER[name]
    for key, _, pats in LAYERS:
        if any(re.match(p, f) for p in pats):
            return key
    return "other"


def run_lean():
    roots = [(g, r) for g, (_, r) in HEADLINES.items()] + [("DEC", DECISIONS[1]), ("DEC2", DECISIONS_DEFAULT[1])]
    args = [f"{g}={','.join(r)}" for g, r in roots]
    args.append(f"H1+H3-S={','.join(HEADLINES['H1'][1] + HEADLINES['H3'][1])}/{','.join(STOP_DECISIONS)}")
    env = dict(os.environ)
    env["PATH"] = os.path.expanduser("~/.elan/bin") + os.pathsep + env.get("PATH", "")
    r = subprocess.run(["lake", "env", "lean", "--run", "paper/gen/trusted_core.lean", *args], cwd=ROOT,
                       capture_output=True, text=True, env=env)
    if r.returncode != 0:
        raise SystemExit("trusted_core: trusted_core.lean failed:\n" + (r.stderr + r.stdout)[-3000:])
    return r.stdout


def parse(text):
    decl = {}  # group -> name -> row
    ext = {}  # group -> name -> (module, referrers)
    for line in text.splitlines():
        p = line.split("\t")
        if p[0] == "D":
            _, g, n, kind, mod, d, l0, ls, l1, owner = p
            if int(l0) == 0:
                raise SystemExit(f"trusted_core: no declaration range for {n} or an enclosing declaration")
            rows = decl.setdefault(g, {})
            r = rows.get(owner)
            if r is None:
                r = rows[owner] = {"name": owner, "kind": kind, "module": mod, "depth": int(d),
                                   "first": int(l0), "sel": int(ls), "last": int(l1), "aux": []}
            r["depth"] = min(r["depth"], int(d))
            if owner != n:
                r["aux"].append(n)
        elif p[0] == "X":
            _, g, n, mod, k = p
            ext.setdefault(g, {})[n] = (mod, int(k))
    return decl, ext


def merge(groups):
    out = {}
    for g in groups:
        for n, r in g.items():
            if n not in out or r["depth"] < out[n]["depth"]:
                out[n] = dict(r)
    return out


def resolve(rows):
    """Drop ranges nested in another reached range (constructors, structure fields)."""
    ranged = rows
    # nested ranges (constructors, structure fields) belong to the enclosing declaration
    byfile = {}
    for n, r in ranged.items():
        r["file"] = r["module"].replace(".", "/") + ".lean"
        byfile.setdefault(r["file"], []).append(r)
    top = []
    for f, rs in byfile.items():
        rs.sort(key=lambda r: (r["first"], -r["last"]))
        cur = None
        for r in rs:
            if cur is not None and r["first"] >= cur["first"] and r["last"] <= cur["last"]:
                cur.setdefault("members", []).append(r["name"])
                cur["depth"] = min(cur["depth"], r["depth"])
                continue
            cur = r
            top.append(r)
    for r in top:
        r["lines"] = r["last"] - r["first"] + 1
        r["codeLines"] = r["last"] - r["sel"] + 1
        r["layer"] = layer_of(r["file"], r["name"])
    top.sort(key=lambda r: (r["depth"], r["file"], r["first"]))
    return top


def check_ranges(top):
    """The line of each declaration's name must contain the name's last component: catches ranges
    read from an .olean built from an older source."""
    cache = {}
    for r in top:
        if r["file"] not in cache:
            with open(os.path.join(ROOT, r["file"]), encoding="utf-8") as h:
                cache[r["file"]] = h.read().split("\n")
        last = r["name"].split(".")[-1]
        line = cache[r["file"]][r["sel"] - 1] if 0 < r["sel"] <= len(cache[r["file"]]) else ""
        if last not in line and not last.startswith("inst"):
            raise SystemExit(f"trusted_core: {r['name']}: {r['file']}:{r['sel']} does not name it "
                             f"(stale build? run `lake build Challenge`): {line!r}")


def line_union(top, key="first"):
    s = set()
    for r in top:
        s |= {(r["file"], i) for i in range(r[key], r["last"] + 1)}
    return len(s)


def summary(top):
    out = {"decls": len(top), "lines": line_union(top), "codeLines": line_union(top, "sel"),
           "files": len({r["file"] for r in top}), "maxDepth": max(r["depth"] for r in top),
           "spec": {"decls": sum(r["file"].startswith("Spec/") for r in top),
                    "lines": line_union([r for r in top if r["file"].startswith("Spec/")])},
           "challenge": {"decls": sum(r["file"].startswith("Challenge/") for r in top),
                         "lines": line_union([r for r in top if r["file"].startswith("Challenge/")])},
           "byLayer": {}}
    for key, title, _ in LAYERS + [("other", "Other", [])]:
        sel = [r for r in top if r["layer"] == key]
        if sel:
            out["byLayer"][key] = {"title": title, "decls": len(sel), "lines": line_union(sel)}
    return out


def mathlib_top(ext_groups, top_names):
    agg = {}
    for g in ext_groups:
        for n, (mod, k) in g.items():
            a = agg.setdefault(n, [mod, 0])
            a[1] += k
    ml = {n: v for n, v in agg.items() if v[0].startswith("Mathlib")}
    return [{"name": n, "module": v[0], "referrers": v[1]}
            for n, v in sorted(ml.items(), key=lambda kv: (-kv[1][1], kv[0]))]


def notions(ms):
    """Mathlib constants read directly by a reached declaration, without instance plumbing
    (`Foo.toBar` projections, `inst*` instances): the library notions the statements rely on."""
    def plumbing(n):
        last = n.split(".")[-1]
        ns = n.rsplit(".", 1)[0] if "." in n else ""
        return (last.startswith("to") and last[2:3].isupper() and ns not in ("ENNReal", "Real", "Int", "Nat", "ZMod")) or last.startswith("inst") or n.startswith("inst") \
            or n.split(".")[0].startswith("inst")
    return [m for m in ms if not plumbing(m["name"])]


def table(top):
    print("| depth | declaration | file:lines | lines | layer |")
    print("|---|---|---|---|---|")
    for r in sorted(top, key=lambda r: ([k for k, _, _ in LAYERS + [("other", "", [])]].index(r["layer"]),
                                        r["file"], r["first"])):
        print(f"| {r['depth']} | `{r['name']}` | {r['file']}:{r['first']}-{r['last']} | {r['lines']} | {r['layer']} |")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--tsv")
    ap.add_argument("--out", default=OUT)
    ap.add_argument("--table")
    a = ap.parse_args()
    text = open(a.tsv).read() if a.tsv else run_lean()
    decl, ext = parse(text)
    missing = [g for g in HEADLINES if g not in decl]
    if missing:
        raise SystemExit(f"trusted_core: no output for {missing}")
    sets = {g: decl[g] for g in list(HEADLINES) + ["DEC", "DEC2", "H1+H3-S"]}
    exts = {g: ext.get(g, {}) for g in sets}
    for u, gs in UNIONS.items():
        sets[u] = merge([decl[g] for g in gs])
        exts[u] = {}
        for g in gs:
            for n, v in exts[g].items():
                exts[u].setdefault(n, v)
    doc = {"generator": "paper/gen/trusted_core.py", "helper": "paper/gen/trusted_core.lean",
           "rules": "statement closure: types, and definition bodies of declarations in Spec/ and Challenge/; "
                    "theorems other than the headlines not followed; auxiliary constants counted as their "
                    "owner; nested ranges (constructors, fields) counted in the enclosing declaration; lines "
                    "= distinct source lines of the declaration ranges, docstrings included",
           "headlines": {g: {"what": w, "roots": r} for g, (w, r) in HEADLINES.items()},
           "decisions": {"DEC": {"what": DECISIONS[0], "roots": DECISIONS[1]},
                         "DEC2": {"what": DECISIONS_DEFAULT[0], "roots": DECISIONS_DEFAULT[1]}},
           "statementOnly": {"H1+H3-S": {"what": "H1 and H3 without the bodies of the profile decision functions",
                                         "stops": STOP_DECISIONS}},
           "unions": UNIONS, "groups": {}}
    for g, rows in sets.items():
        top = resolve({n: dict(r) for n, r in rows.items()})
        check_ranges(top)
        doc["groups"][g] = {"summary": summary(top),
                            "mathlib": notions(mathlib_top([exts[g]], None)),
                            "decls": [{k: r[k] for k in ("name", "kind", "file", "first", "sel", "last", "lines",
                                                         "codeLines", "depth", "layer")}
                                      | ({"members": r["members"]} if r.get("members") else {})
                                      for r in top]}
        if a.table == g:
            table(top)
    with open(os.path.join(ROOT, a.out), "w") as h:
        json.dump(doc, h, indent=1, ensure_ascii=False)
        h.write("\n")
    for g in doc["groups"]:
        s = doc["groups"][g]["summary"]
        print(f"{g}: {s['decls']} declarations, {s['lines']} lines ({s['codeLines']} without docstrings), "
              f"{s['files']} files, depth <= {s['maxDepth']}", file=sys.stderr)


if __name__ == "__main__":
    main()
