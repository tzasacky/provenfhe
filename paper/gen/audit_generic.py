#!/usr/bin/env python3
"""UNTRUSTED: the generic-vs-library line classification of the trusted text, by script.

    python3 -I paper/gen/audit_generic.py [--lean] [--rev REV] [--out FILE]

The classification: a file is G (generic: no library policy), L (specific to one library) or M
(mixed). It was made by hand in a working audit of the trusted text (not part of the public
release) and is kept here as data (CLASSES, LIB_SPANS), so the counts can be recomputed.

Writes docs/audit-generic.json (default --out): for every .lean file under Spec/ and Challenge/
that git tracks at REV (default: the working tree), its line count (newline count, as `wc -l`),
its class (CLASSES), and its library-specific lines:

* L file: every line;
* M file under Spec/: the union of the spans listed in LIB_SPANS (a declaration with the
  docstring above it, or a docstring section between two anchors), located by name in the
  current text, so the count follows edits;
* M file under Challenge/: not split; reported as M;
* G file: none.

The totals the paper quotes: `spec.lines` (all Spec/ lines), `spec.libLines` (library-specific
Spec/ lines), `spec.libPercent`, and `spec.libAddedSinceAudit` (library-specific lines of the Spec/
files the audit did not list (AUDIT_SPEC_FILES)). A file not in CLASSES is an error: a new trusted file
must be classified here before the numbers can be regenerated.

With --lean it also runs `lake env lean --run paper/gen/audit_closure.lean` (needs a built tree;
about 15 s) and records which Spec/ declarations the two main soundness statements reach
(`closure`): in mode `statement` (unfolding definitions but stopping at the decision functions
certify?/certifyBFV?) and `full` (unfolding those too), with every reached declaration that lies in
a library-specific span. Without --lean the `closure` section of the existing output is kept
(it is stamped with the tree it was computed on).
"""
import argparse
import hashlib
import json
import os
import re
import subprocess
import sys

ROOT = os.path.abspath(os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", ".."))
OUT = "docs/audit-generic.json"
# The audit's first measured tree (before out-of-scope components were removed from the trusted
# text) is recorded here as data, so the script needs no commit id: the same rules applied to it gave
# AUDIT_TREE, and these are the Spec/ files it had that are still in the tree. Spec/Layout.lean was
# out of its scope then (134 lines, then with storage definitions outside this release's scope); it
# now holds only the storage parameters the noise core reads.
AUDIT_TREE = {
    "rev": "pre-split audit tree",
    "spec": {"files": 18, "lines": 3189, "G": 2144, "M": 695, "L": 350, "libLines": 568, "genericLines": 2621,
             "libPercent": 17.8},
    "challenge": {"files": 32, "lines": 9124, "G": 4582, "M": 3141, "L": 1401},
    "note": "the same rules on the tree the audit was first measured on (its prose estimate: "
            "about 610 of 3,189 Spec/ lines library-specific); Spec/Layout.lean was out of its scope then",
    "outOfScopeThen": ["Spec/Layout.lean"],
}
AUDIT_SPEC_FILES = {"Spec/" + n + ".lean" for n in (
    "Budget BudgetBFV BudgetBFVRns Certify CertifyBFV Correct Decrypt DecryptBFV Encrypt EncryptBFV "
    "Float Params Ring Scaling Scheme Source Trace TraceBFV").split()}

# Per-file classes (from the audit; the files added since are marked "added").
CLASSES = {
    # Spec/
    "Spec/Ring.lean": "G", "Spec/Scheme.lean": "G", "Spec/Source.lean": "G", "Spec/Params.lean": "G",
    "Spec/Correct.lean": "G", "Spec/Trace.lean": "G", "Spec/TraceBFV.lean": "G", "Spec/Budget.lean": "G",
    "Spec/BudgetBFV.lean": "G", "Spec/BudgetBFVRns.lean": "M", "Spec/Float.lean": "G",
    "Spec/Encrypt.lean": "G", "Spec/Decrypt.lean": "G", "Spec/EncryptBFV.lean": "M",
    "Spec/DecryptBFV.lean": "L", "Spec/Certify.lean": "G", "Spec/CertifyBFV.lean": "M",
    "Spec/Scaling.lean": "M",
    "Spec/Layout.lean": "G",  # added: storage parameters split out of Correct/Params
    "Spec/DecryptBFVBEHZ.lean": "L",  # added: OpenFHE's BEHZ ScaleAndRound(moduliQ, t, ...)
    "Spec/DecryptBFVLow.lean": "L",  # added: OpenFHE's fewer-limb decryption
    "Spec/DecryptBFVLib.lean": "L",  # added: PKEBFVRNS::Decrypt's dispatch
    "Spec/IndCpaD.lean": "G",  # added: the IND-CPA-D game and its reduction, abstract over the scheme
    "Spec/IndCpaDBFV.lean": "L",  # added: the BFV instance's data (OpenFHE's encryption at the top level)
    # Challenge/
    "Challenge/Ring.lean": "G", "Challenge/Scheme.lean": "G", "Challenge/Source.lean": "G",
    "Challenge/Trace.lean": "G", "Challenge/Params.lean": "G", "Challenge/Budget.lean": "G",
    "Challenge/BudgetRestrict.lean": "G", "Challenge/Decrypt.lean": "G", "Challenge/FreshNoise.lean": "G",
    "Challenge/FreshNoiseL2.lean": "G", "Challenge/Headline/Defs.lean": "G", "Challenge/Headline.lean": "G",
    "Challenge/Certify/Defs.lean": "G", "Challenge/Certify.lean": "G", "Challenge/BFV/Defs.lean": "G",
    "Challenge/BFV.lean": "G", "Challenge/BFV/Domain.lean": "G", "Challenge/BFV/PerInstr.lean": "G",
    "Challenge/BFVMul.lean": "M", "Challenge/BFVMul/HPS.lean": "M", "Challenge/BFVMul/BEHZ.lean": "M",
    "Challenge/BFVMul/POverQ.lean": "M", "Challenge/BFVMul/Float.lean": "L",
    "Challenge/BFVMul/KSLeveled.lean": "L", "Challenge/CertifyBFV/Defs.lean": "M",
    "Challenge/CertifyBFV.lean": "M", "Challenge/BFVEncrypt/Defs.lean": "M",
    "Challenge/BFVEncrypt.lean": "M", "Challenge/BFVDecrypt.lean": "L", "Challenge/Scaling.lean": "M",
    "Challenge/Realize.lean": "L", "Challenge/Realize/OpenFHE.lean": "L",
    "Challenge/Corpus.lean": "G",  # added: shared test articles at tinyBGV
    "Challenge/Fast/Defs.lean": "G", "Challenge/Fast.lean": "G",  # added: fast path = locked decision
    "Challenge/BFVDecryptBEHZ.lean": "L", "Challenge/BFVDecryptLow.lean": "L",
    "Challenge/BFVDecryptLib.lean": "L",  # added: statements about OpenFHE's decryption routines
    "Challenge/BFVMul/BEHZWord.lean": "L",  # added: machine-word precondition of OpenFHE's BEHZ
    "Challenge/Word.lean": "L",  # added: machine-word precondition of OpenFHE's key switching
    "Challenge/CertifyBFV/Library.lean": "L",  # added: runLibrary, OpenFHE's algorithms composed
    "Challenge/IndCpaD.lean": "M", "Challenge/IndCpaD/Defs.lean": "L",  # added: IND-CPA-D statements; the BFV instance
    "Challenge/RealizeBFV.lean": "L", "Challenge/Realize/OpenFHEBFV.lean": "L",  # added: BFV key switching
    "Challenge/Profile/Defs.lean": "G", "Challenge/Profile.lean": "G",  # added: certificates at a user-supplied budget
    "Challenge/IndCpaD/Generic.lean": "M",  # added: reduction for every evaluator meeting the contracts; libEval as one instance
    "Challenge/Profile/Tool.lean": "G",  # added: the tool's decisions are profile certificates at the computed budget
    "Challenge/Instances/Lattigo/Defs.lean": "L", "Challenge/Instances/Lattigo.lean": "L",  # added: second library instance (Lattigo)
    "Spec/IndCpaDProfile.lean": "G",  # added: library-free IND-CPA-D data (abstract encryption, evaluator class)
    "Spec/MSB.lean": "G", "Spec/MSBScale.lean": "G",  # added: BGV in the other (MSB) form; the contracts transfer
    "Challenge/IndCpaD/Profile.lean": "G", "Challenge/IndCpaD/ProfileBGV.lean": "G",  # added: reduction on profile-certified classes
    "Challenge/IndCpaD/ProfileInstances.lean": "L",  # added: the OpenFHE-shaped and textbook evaluators as instances
    "Challenge/IndCpaD/ProfileBGVInstances.lean": "G",  # added: exact evaluator for circuits without key switching
    "Challenge/MSB.lean": "G", "Challenge/MSBScale.lean": "G",  # added: MSB contracts, transfer, profile soundness
    "Challenge/Instances/Lattigo/MSB.lean": "L",  # added: Lattigo key switch and rescale within the profile
    "Challenge/Families/BEHZ.lean": "M", "Challenge/Families/Quantize.lean": "M",  # added: generic family statements, closed instances at SEAL / OpenFHE / Lattigo parameters
    "Challenge/Families/BEHZCover.lean": "M",  # added: BEHZ in the coverage check; the SEAL instance (not split)
    "Challenge/Families/FloatTol.lean": "M",  # added: HPS-family multiplication at any summation tolerance (generic) with the OpenFHE tolerances as instances (not split)
    "Challenge/Families/Coverage.lean": "M",  # added: coverage checks at SEAL's and Lattigo's layouts (two libraries; not split)
    "Spec/IndCpaDLM.lean": "G",  # added: the game with evaluation on earlier results
    "Challenge/IndCpaD/LM.lean": "M",  # added: the reduction for it (generic) and the BGV key-switching instance (OpenFHE-shaped)
    "Challenge/IndCpaD/LMBFV.lean": "L",  # added: BFV instance with the OpenFHE key-switch transcription
    "Challenge/IndCpaD/LMExact.lean": "G",  # added: the exact BGV evaluator instance
    "Challenge/IndCpaD/ProfileAdv.lean": "G",  # added: any-entry reduction; advantage bound
    "Challenge/IndCpaD/ProfileKernel.lean": "L",  # added: kernel-checked class members at OpenFHE-shaped settings
    "Challenge/IndCpaD/ProfileBGVKS.lean": "L",  # added: BGV evaluator with OpenFHE's key-switching transcription
    "Challenge/Fast/ProfileDefs.lean": "G", "Challenge/Fast/Profile.lean": "G",  # added: profile-mode equality statements
    "Challenge/Profile/Named.lean": "M",  # added: coverage implies the named OpenFHE transcriptions meet the contracts (generic coverage, named algorithms; not split)
    "Challenge/Profile/Achieve.lean": "M",  # added: accepted and covered: a named evaluator's run exists (generic statement, OpenFHE-transcribed evaluators; not split)
    "Challenge/Profile/Inputs.lean": "G",  # added: every accepted program has inputs for every message
    "Challenge/IndCpaD/BadEvent.lean": "M",  # added: advantage bound over the bad event (generic) and its instances (not split)
    "Challenge/IndCpaD/LMCompose.lean": "G",  # added: the reduction for the profile classes
    "Challenge/IndCpaD/LMAgree.lean": "M",  # added: agreement of the game's oracle with the fresh-only class (generic) and the seal instances (not split)
    "Challenge/IndCpaD/LMBounds.lean": "L",  # added: kernel-checked examples at the OpenFHE-shaped seal settings
    "Spec/IndCpaDSanity.lean": "G",  # added: vocabulary for the sanity statements about the games
    "Challenge/IndCpaD/Sanity.lean": "G",  # added: what the games and reductions do (generic)
    "Challenge/IndCpaD/SanityInstances.lean": "M",  # added: good randomness; the hypotheses of the seal instances hold jointly
    "Challenge/IndCpaD/Attack.lean": "L",  # added: parameter sets generated by one library at the published attack parameters
    "Challenge/Sanity/EndToEnd.lean": "G", "Challenge/Sanity/Conventions.lean": "G",  # added: certificate sanity statements
    "Challenge/Sanity/Contracts.lean": "G", "Challenge/Sanity/Coverage.lean": "G", "Challenge/Sanity/Edges.lean": "G",
    "Challenge/Sanity/Lattigo.lean": "L",  # added: every hypothesis at once at Lattigo's parameters
    "Challenge/IndCpaD/LMEmbed.lean": "M",  # added: the fresh-only game embeds in the game with evaluation on earlier results (generic) and the seal instances (not split)
    "Challenge/IndCpaD/Textbook.lean": "M",  # added: textbook-multiplication evaluator; seal/tiny instances
}

# Which library an L file (or the library-specific part of an M file) is specific to. Every file not
# listed here is specific to OpenFHE v1.6.1, the library the audit was made for; the second library
# instance (Lattigo) is listed, so that the report says which library each L line belongs to.
LIBRARY_OF = {
    "Challenge/Instances/Lattigo/Defs.lean": "Lattigo v6.2.0",
    "Challenge/Instances/Lattigo.lean": "Lattigo v6.2.0",
    "Challenge/Instances/Lattigo/MSB.lean": "Lattigo v6.2.0",
    "Challenge/Sanity/Lattigo.lean": "Lattigo v6.2.0",
}
DEFAULT_LIBRARY = "OpenFHE v1.6.1"

# Library-specific parts of the Spec/ M files (from the audit).
# ("decl", name): the declaration (or constructor / structure field) whose line starts with
# `def name`, `structure name`, `inductive name`, `| name` or `name :`, with the docstring above it;
# ("section", start, end): from the first line matching `start` to the line before the first later
# line matching `end`.
LIB_SPANS = {
    "Spec/Scaling.lean": [
        ("section", r"^## The library's factor-tracking policy", r"^-/"),
        ("decl", "facStep"), ("decl", "facRun"), ("decl", "factors?"), ("decl", "decodeFactor"),
        ("decl", "tracks"),
    ],
    "Spec/EncryptBFV.lean": [
        ("section", r"^\*\*What OpenFHE v1\.6\.1 computes\*\*", r"^\*\*The BFV noise of a fresh encryption\.\*\*"),
        ("decl", "scaleUpCeil"), ("decl", "encryptBFV"), ("decl", "encodeDev"),
    ],
    "Spec/BudgetBFVRns.lean": [
        ("decl", "doubleSw"), ("decl", "doubleSr"), ("decl", "leveledSlack"), ("decl", "ksLeveled"),
    ],
    "Spec/CertifyBFV.lean": [
        ("decl", "leveled"), ("decl", "drops"), ("decl", "AssumptionBFV"),
    ],
}

DECL_KW = r"(?:noncomputable\s+|private\s+|protected\s+)*(?:def|abbrev|structure|inductive|theorem|lemma|instance|class)\s+"


def git(*args):
    return subprocess.run(["git", "-C", ROOT, *args], capture_output=True, check=True).stdout


def files_at(rev):
    if rev:
        names = git("ls-tree", "-r", "--name-only", rev, "--", "Spec", "Challenge").decode().split("\n")
    else:
        names = git("ls-files", "--", "Spec", "Challenge").decode().split("\n")
    return sorted(n for n in names if n.endswith(".lean"))


def read_at(rev, f):
    if rev:
        return git("show", f"{rev}:{f}").decode()
    with open(os.path.join(ROOT, f), encoding="utf-8") as h:
        return h.read()


def indent(s):
    return len(s) - len(s.lstrip(" "))


def decl_span(lines, name):
    """[start, end) of the declaration `name` (0-based), with the docstring directly above it."""
    pat = re.compile(r"^\s*(?:" + DECL_KW + r"|\|\s*)" + re.escape(name) + r"(?=[\s:(]|$)|^\s+" + re.escape(name) + r"\s*:")
    hits = [i for i, l in enumerate(lines) if pat.search(l)]
    if len(hits) != 1:
        raise SystemExit(f"audit_generic: declaration {name!r}: {len(hits)} matches (need exactly 1)")
    i = hits[0]
    ind = indent(lines[i])
    start = i
    if i > 0 and lines[i - 1].rstrip().endswith("-/"):
        j = i - 1
        while j >= 0 and not lines[j].lstrip().startswith("/--"):
            j -= 1
        if j < 0:
            raise SystemExit(f"audit_generic: unterminated docstring above {name!r}")
        start = j
    end = i + 1
    while end < len(lines) and lines[end].strip() and indent(lines[end]) > ind:
        end += 1
    return start, end


def section_span(lines, start_re, end_re):
    s = [i for i, l in enumerate(lines) if re.search(start_re, l)]
    if len(s) != 1:
        raise SystemExit(f"audit_generic: section anchor {start_re!r}: {len(s)} matches (need exactly 1)")
    e = next((i for i in range(s[0] + 1, len(lines)) if re.search(end_re, lines[i])), None)
    if e is None:
        raise SystemExit(f"audit_generic: no end {end_re!r} after {start_re!r}")
    return s[0], e


def classify(rev):
    rows = []
    unclassified = []
    lib_lines_of = {}
    for f in files_at(rev):
        text = read_at(rev, f)
        n = text.count("\n")
        lines = text.split("\n")
        c = CLASSES.get(f)
        if c is None:
            unclassified.append(f)
            continue
        lib = set()
        if c == "L":
            lib = set(range(n))
        elif c == "M" and f in LIB_SPANS:
            for sp in LIB_SPANS[f]:
                a, b = decl_span(lines, sp[1]) if sp[0] == "decl" else section_span(lines, sp[1], sp[2])
                lib |= set(range(a, b))
        lib_lines_of[f] = lib
        row = {"file": f, "lines": n, "class": c,
               "libLines": len(lib) if (c != "M" or f in LIB_SPANS) else None}
        if c == "L":
            row["library"] = LIBRARY_OF.get(f, DEFAULT_LIBRARY)
        rows.append(row)
    return rows, unclassified, lib_lines_of


def totals(rows, d):
    sel = [r for r in rows if r["file"].startswith(d + "/")]
    by = {k: sum(r["lines"] for r in sel if r["class"] == k) for k in "GML"}
    out = {"files": len(sel), "lines": sum(r["lines"] for r in sel), "G": by["G"], "M": by["M"], "L": by["L"]}
    if d == "Spec":
        lib = sum(r["libLines"] for r in sel)
        out["libLines"] = lib
        out["genericLines"] = out["lines"] - lib
        out["libPercent"] = round(100.0 * lib / out["lines"], 1)
    out["L_by_library"] = {}
    for r_ in sel:
        if r_["class"] == "L":
            out["L_by_library"][r_["library"]] = out["L_by_library"].get(r_["library"], 0) + r_["lines"]
    return out


def run_closure(lib_lines_of):
    r = subprocess.run(["lake", "env", "lean", "--run", "paper/gen/audit_closure.lean"], cwd=ROOT,
                       capture_output=True, text=True)
    if r.returncode != 0:
        raise SystemExit("audit_generic: audit_closure.lean failed:\n" + r.stderr[-3000:])
    res = {}
    for line in r.stdout.splitlines():
        root, mode, mod, name, l0, l1 = line.split("\t")
        f = mod.replace(".", "/") + ".lean"
        l0 = int(l0)
        e = res.setdefault(root, {}).setdefault(mode, {"specDecls": 0, "libSpecific": []})
        e["specDecls"] += 1
        lib = lib_lines_of.get(f, set())
        if l0 > 0 and (l0 - 1) in lib:
            e["libSpecific"].append({"name": name, "file": f, "line": l0})
    for root in res.values():
        for e in root.values():
            e["libSpecific"].sort(key=lambda x: (x["file"], x["line"], x["name"]))
    return res


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--rev", default=None, help="classify the tree of this commit instead of the working tree")
    ap.add_argument("--lean", action="store_true", help="also recompute the closure (needs a built tree)")
    ap.add_argument("--out", default=OUT)
    a = ap.parse_args()
    rows, unclassified, lib_lines_of = classify(a.rev)
    if unclassified:
        raise SystemExit("audit_generic: not classified (add to CLASSES): " + " ".join(unclassified))
    old_files = AUDIT_SPEC_FILES
    spec = totals(rows, "Spec")
    spec["libAddedSinceAudit"] = sum(r["libLines"] for r in rows if r["file"].startswith("Spec/") and r["file"] not in old_files)
    spec["filesAddedSinceAudit"] = sorted(r["file"] for r in rows if r["file"].startswith("Spec/") and r["file"] not in old_files)
    out_path = os.path.join(ROOT, a.out)
    prev = {}
    if os.path.exists(out_path):
        with open(out_path) as h:
            prev = json.load(h)
    doc = {
        "generator": "paper/gen/audit_generic.py",
        "tree": "release tree",
        "spec": spec,
        "challenge": totals(rows, "Challenge"),
        "auditTree": AUDIT_TREE,
        "files": rows,
        "libSpans": {f: [list(s) for s in v] for f, v in LIB_SPANS.items()},
    }
    if a.lean:
        doc["closure"] = {"tree": doc["tree"], "by": "paper/gen/audit_closure.lean",
                          "roots": {"bgv": "Challenge.Certify.certify?_sound", "bfv": "Challenge.CertifyBFV.certifyBFV?_sound"},
                          "result": run_closure(lib_lines_of)}
    elif "closure" in prev:
        doc["closure"] = prev["closure"]
    with open(out_path, "w") as h:
        json.dump(doc, h, indent=1, ensure_ascii=False)
        h.write("\n")
    print(f"Spec/: {spec['libLines']} of {spec['lines']} lines library-specific ({spec['libPercent']}%), "
          f"{spec['libAddedSinceAudit']} in files added since the audit; wrote {a.out}")


if __name__ == "__main__":
    main()
