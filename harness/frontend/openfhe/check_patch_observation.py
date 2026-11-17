#!/usr/bin/env python3
"""UNTRUSTED: the checks of check_patch_observation.sh (read its header first).

  check_patch_observation.py --pristine DIR --patched DIR --patch PATCH --allowlist JSON --out STATIC.json
      part A: classify every hunk of PATCH; check the residue against the allowlist and the
      `registerOutput` definitions; write STATIC.json; exit 1 on any unexplained difference
  check_patch_observation.py --combine STATIC.json [--digests D0 D1 D2 [D3]] [--traces DIR] --out OUT.json
      part B: compare the digest lists (pristine first) line for line; write the combined result

Part A, per hunk. For both versions of the file a mask marks what the hook macros expand to nothing
with ENABLE_TRACER=OFF (utils/tracing.h): `IF_TRACE(...)` (and a `;` right after it),
`IF_TRACE_(...)`, and of `REGISTER_IF_TRACE([t,] x)` everything but `x`; plus comments, and
`#include` lines of the tracer headers (kind "tracer include"). A hunk is OBSERVATION-ONLY ("hook")
if its old side and its new side are equal once masked text and whitespace are removed; otherwise
its two masked sides are RESIDUE and must be listed in the allowlist (file, sha256 of the two
sides) with a reason. Hunks of new files and of the build configuration are counted by kind.

Hook contents. Every `IF_TRACE(...)` statement is matched against the shapes a tracer call has
(a tracer variable from StartFunctionTrace; registerInput/registerOutput calls on it, alone or in a
for loop over a container; the tracer member and its setter in CryptoContextImpl). Others are
listed as "hook statements outside the known shapes" with the allowlist's reason, or fail.

registerOutput. Every definition in tracing.h, simpletracer.h and fhecheck-tracer.h must end with
`return <its first parameter>;` and not assign that parameter: with ENABLE_TRACER=ON,
`REGISTER_IF_TRACE([t,] x)` is `t->registerOutput(x)`, so it returns x.
"""
import argparse
import hashlib
import json
import os
import re
import sys

TRACER_HEADERS = ("src/core/include/utils/tracing.h", "src/core/include/utils/simpletracer.h",
                  "src/pke/include/utils/fhecheck-tracer.h")
BUILD_FILES = ("CMakeLists.txt", "OpenFHEConfig.cmake.in", "configure/config_core.in")
INCLUDE_RE = re.compile(r'^\s*#\s*include\s+"(utils/)?(tracing|simpletracer|fhecheck-tracer)\.h"\s*$')


def parse_patch(text):
    """[(path, is_new, [(header, [(tag, line)])])] with tag in ' ', '+', '-'."""
    files, cur, hunk = [], None, None
    for ln in text.split("\n"):
        if ln.startswith("diff --git "):
            cur = [ln.split(" b/", 1)[1], False, []]
            files.append(cur)
            hunk = None
        elif cur is None:
            continue
        elif ln.startswith("new file mode"):
            cur[1] = True
        elif ln.startswith("@@"):
            hunk = (ln, [])
            cur[2].append(hunk)
        elif hunk is not None and ln[:1] in (" ", "+", "-") and not ln.startswith(("+++", "---")):
            hunk[1].append((ln[0], ln[1:]))
        elif hunk is not None and ln.startswith("\\"):
            pass
    return files


def match_paren(s, i):
    """index just after the ')' matching the '(' at s[i-1] (strings and chars skipped)."""
    d, j = 1, i
    while d:
        c = s[j]
        if c in "\"'":
            q = c
            j += 1
            while s[j] != q:
                j += 2 if s[j] == "\\" else 1
        elif c == "(":
            d += 1
        elif c == ")":
            d -= 1
        j += 1
    return j


def mask_of(s):
    """per-character mask: True where the text is a comment, a hook macro's vanishing part, or a
    tracer #include line; and the list of IF_TRACE statement contents."""
    n = len(s)
    m = [False] * n
    code = [True] * n  # outside comments and string/char literals
    i = 0
    while i < n:
        c = s[i]
        if s.startswith("//", i):
            j = s.find("\n", i)
            j = n if j < 0 else j
            for k in range(i, j):
                m[k] = True
                code[k] = False
            i = j
        elif s.startswith("/*", i):
            j = s.find("*/", i + 2) + 2
            for k in range(i, j):
                m[k] = True
                code[k] = False
            i = j
        elif c in "\"'" and not (c == "'" and i > 0 and s[i - 1].isalnum()):
            j = i + 1
            while j < n and s[j] != c:
                j += 2 if s[j] == "\\" else 1
            for k in range(i, min(j + 1, n)):
                code[k] = False
            i = j + 1
        else:
            i += 1
    stmts = []
    for mo in re.finditer(r"\b(REGISTER_IF_TRACE|IF_TRACE_|IF_TRACE)\(", s):
        a = mo.start()
        if not code[a]:
            continue
        line_start = s.rfind("\n", 0, a) + 1
        if s[line_start:a].lstrip().startswith("#"):  # the macro definitions themselves
            continue
        j = match_paren(s, mo.end())
        name = mo.group(1)
        if name == "REGISTER_IF_TRACE":
            inner = s[mo.end():j - 1]
            d, cut = 0, 0
            for k, ch in enumerate(inner):
                if ch in "([{":
                    d += 1
                elif ch in ")]}":
                    d -= 1
                elif ch == "," and d == 0:
                    cut = k + 1
            for k in range(a, mo.end() + cut):
                m[k] = True
            m[j - 1] = True
        else:
            for k in range(a, j):
                m[k] = True
            if name == "IF_TRACE":
                stmts.append(s[mo.end():j - 1])
                k = j
                while k < n and s[k] in " \t":
                    k += 1
                if k < n and s[k] == ";":
                    m[k] = True
    pos = 0
    for ln in s.split("\n"):
        if INCLUDE_RE.match(ln):
            for k in range(pos, pos + len(ln)):
                m[k] = True
        pos += len(ln) + 1
    return m, stmts


def kept(s, m, lo, hi):
    """the unmasked text of lines [lo, hi) (1-based line numbers), whitespace removed."""
    starts = [0] + [k + 1 for k, c in enumerate(s) if c == "\n"]
    a = starts[lo - 1] if lo - 1 < len(starts) else len(s)
    b = starts[hi - 1] if hi - 1 < len(starts) else len(s)
    return re.sub(r"\s+", "", "".join(c for k, c in enumerate(s[a:b], a) if not m[k]))


def _one_call(st, name_rx):
    """st is exactly one call `<prefix><name>(args)` (balanced), optionally followed by `;`, and the
    prefix matches name_rx; returns True/False."""
    mo = re.match(name_rx, st, re.S)
    if not mo:
        return False
    try:
        j = match_paren(st, mo.end())
    except IndexError:
        return False
    return re.fullmatch(r"\s*;?\s*", st[j:]) is not None


def _register_call(st):
    return _one_call(st, r"\s*\w+->register(Input|Output)\(")


def _register_loop(st):
    mo = re.match(r"\s*for\s*\(", st)
    if not mo:
        return False
    j = match_paren(st, mo.end())
    body = st[j:].strip()
    if body.startswith("{") and body.endswith("}"):
        body = body[1:-1].strip()
    return _register_call(body) or _register_loop(body)


def hook_shape(st):
    """the shape of an IF_TRACE statement: a tracer variable (`auto t = ...StartFunctionTrace(...)`,
    one call, the receiver a member/accessor chain), one register call on a tracer, or a for loop
    whose body is one register call (or such a loop); None otherwise."""
    if _one_call(st, r"\s*auto\s+\w+\s*=\s*[\w\.]+(?:->\w+\(\)|\.\w+|->\w+)*->StartFunctionTrace\("):
        return "tracer variable"
    if _register_call(st):
        return "register call"
    if _register_loop(st):
        return "register loop"
    return None


def check_register_output(root):
    """every registerOutput definition (one with a body) returns its first parameter, as its only
    return statement and its last one, and does not assign it or call a setter on it."""
    out, bad = 0, []
    for f in TRACER_HEADERS:
        s = open(os.path.join(root, f)).read()
        s = re.sub(r"//[^\n]*", "", s)
        for mo in re.finditer(r"\bregisterOutput\(", s):
            j = match_paren(s, mo.end())
            k = j
            while k < len(s) and (s[k].isspace() or s.startswith("const", k) or s.startswith("override", k)):
                k += 5 if s.startswith("const", k) else 8 if s.startswith("override", k) else 1
            if k >= len(s) or s[k] != "{":
                continue  # a call, a declaration or a pure virtual
            params, d, cur = [], 0, ""
            for ch in s[mo.end():j - 1]:
                if ch in "<([":
                    d += 1
                elif ch in ">)]":
                    d -= 1
                if ch == "," and d == 0:
                    params.append(cur)
                    cur = ""
                else:
                    cur += ch
            params.append(cur)
            par = re.findall(r"\w+", params[0].split("=")[0])[-1]
            e = k + 1
            dd = 1
            while dd:
                dd += {"{": 1, "}": -1}.get(s[e], 0)
                e += 1
            body = s[k + 1:e - 1]
            out += 1
            rets = re.findall(r"\breturn\b([^;]*);", body)
            ok = rets == [" " + par] and re.search(r"return\s+" + re.escape(par) + r"\s*;\s*$", body) is not None \
                and re.search(r"\b" + re.escape(par) + r"\s*(=[^=]|\+\+|--|\.\s*Set|->\s*Set)", body) is None
            if not ok:
                bad.append(f"{f}: registerOutput({par}) does not return its parameter unchanged")
    return out, bad


def static(a):
    patch = open(a.patch).read()
    allow = json.load(open(a.allowlist))
    al = {(e["file"], e["sha256"]): e for e in allow["residue"]}
    al_stmt = {e["statement"]: e for e in allow.get("hookStatements", [])}
    kinds = {"hook": 0, "tracer include": 0, "residue (allowlisted)": 0, "new file": 0, "build configuration": 0,
             "UNEXPLAINED": 0}
    files, residue, unexplained, stmts_other = [], [], [], []
    used = set()
    shapes = {}
    for path, is_new, hunks in parse_patch(patch):
        rec = {"file": path, "hunks": len(hunks), "added": sum(1 for _, h in hunks for t, _ in h if t == "+"),
               "removed": sum(1 for _, h in hunks for t, _ in h if t == "-")}
        if is_new:
            rec["kind"] = "new file"
            kinds["new file"] += len(hunks)
            files.append(rec)
            continue
        if path in BUILD_FILES:
            rec["kind"] = "build configuration"
            kinds["build configuration"] += len(hunks)
            files.append(rec)
            continue
        s0 = open(os.path.join(a.pristine, path)).read()
        s1 = open(os.path.join(a.patched, path)).read()
        m0, _ = mask_of(s0)
        m1, st1 = mask_of(s1)
        for st in st1:
            shapes[hook_shape(st) or "other (allowlist)"] = shapes.get(hook_shape(st) or "other (allowlist)", 0) + 1
            if hook_shape(st) is None:
                key = re.sub(r"\s+", " ", st).strip()
                e = al_stmt.get(key)
                stmts_other.append({"file": path, "statement": key, "reason": e["reason"] if e else None})
                if e is None:
                    unexplained.append(f"{path}: IF_TRACE statement outside the known shapes: {key}")
        kh = {"hook": 0, "tracer include": 0, "residue": 0}
        for hdr, lines in hunks:
            mo = re.match(r"@@ -(\d+)(?:,(\d+))? \+(\d+)(?:,(\d+))? @@", hdr)
            o0, oc, n0, nc = int(mo.group(1)), int(mo.group(2) or 1), int(mo.group(3)), int(mo.group(4) or 1)
            old, new = kept(s0, m0, o0, o0 + oc), kept(s1, m1, n0, n0 + nc)
            if old == new:
                inc = all(INCLUDE_RE.match(l) or not l.strip() for t, l in lines if t == "+")
                k = "tracer include" if inc and any(t == "+" for t, _ in lines) else "hook"
                kinds[k] += 1
                kh[k] += 1
                continue
            h = hashlib.sha256((old + "\n=>\n" + new).encode()).hexdigest()
            e = al.get((path, h))
            kh["residue"] += 1
            r = {"file": path, "hunk": hdr.split("@@")[1].strip(), "sha256": h, "old": old[:600], "new": new[:600],
                 "reason": e["reason"] if e else None}
            residue.append(r)
            if e:
                used.add((path, h))
                kinds["residue (allowlisted)"] += 1
            else:
                kinds["UNEXPLAINED"] += 1
                unexplained.append(f"{path} {r['hunk']}: residue not in the allowlist (sha256 {h})")
        rec["kind"] = "modified source"
        rec["hunkKinds"] = kh
        files.append(rec)
    stale = [f"allowlist entry not used: {k[0]} {k[1]}" for k in al if k not in used]
    seen = {x["statement"] for x in stmts_other}
    stale += [f"allowlist hook statement not used: {k}" for k in al_stmt if k not in seen]
    nreg, badreg = check_register_output(a.patched)
    res = {
        "patch": os.path.basename(a.patch),
        "patchSha256": hashlib.sha256(patch.encode()).hexdigest(),
        "files": len(files), "hunks": sum(f["hunks"] for f in files),
        "linesAdded": sum(f["added"] for f in files), "linesRemoved": sum(f["removed"] for f in files),
        "modifiedSourceFiles": sum(1 for f in files if f["kind"] == "modified source"),
        "newFiles": sum(1 for f in files if f["kind"] == "new file"),
        "hunkKinds": kinds,
        "ifTraceStatements": shapes,
        "ifTraceOutsideKnownShapes": stmts_other,
        "registerOutputDefinitions": nreg, "registerOutputViolations": badreg,
        "residue": residue,
        "perFile": files,
        "problems": unexplained + badreg + stale,
    }
    res["pass"] = not res["problems"]
    json.dump(res, open(a.out, "w"), indent=1)
    print(f"static: {res['files']} files, {res['hunks']} hunks: {kinds}; registerOutput {nreg} definitions, "
          f"{len(badreg)} violations; {'PASS' if res['pass'] else 'FAIL'}")
    for p in res["problems"]:
        print("  " + p)
    return 0 if res["pass"] else 1


def combine(a):
    st = json.load(open(a.combine))
    out = {"what": "harness/frontend/openfhe/check_patch_observation.sh: is the tracer patch observation-only? "
                   "A: static hunk classification (ENABLE_TRACER=OFF semantics + registerOutput returns its argument); "
                   "B: the same deterministic programs on pristine v1.6.1 and on the patched build (ENABLE_TRACER=ON), "
                   "no tracer and with the fhecheck JsonTracer / SimpleTracer recording, digests compared bit for bit",
           "static": st}
    ok = st.get("pass", False)
    if a.digests:
        runs = [open(f).read().splitlines() for f in a.digests]
        names = ["pristine", "patched, no tracer", "patched, tracing every context", "patched, frontend install"][:len(runs)]
        base = runs[0]
        res = {"runs": names, "lines": len(base),
               "contexts": sum(1 for l in base if re.match(r"^ctx\d+ (BGV|BFV|CKKS) ", l)),
               "ciphertextDigests": sum(1 for l in base if re.match(r"^ctx\d+ (?!dec |keygen|context)[^:]+: [0-9a-f]{16} level", l)),
               "decryptions": sum(1 for l in base if re.match(r"^ctx\d+ dec ", l) and " EXC " not in l),
               "exceptions": sum(1 for l in base if ": EXC " in l),
               "differingLines": {}}
        for nm, r in zip(names[1:], runs[1:]):
            d = sum(1 for x, y in zip(base, r) if x != y) + abs(len(base) - len(r))
            res["differingLines"][nm] = d
        if a.traces:
            fs = sorted(os.listdir(a.traces))
            res["tracedContexts"] = len(fs)
            res["traceLines"] = sum(sum(1 for _ in open(os.path.join(a.traces, f))) for f in fs)
        res["identical"] = all(v == 0 for v in res["differingLines"].values()) and len(runs) >= 3
        out["behavioural"] = res
        ok = ok and res["identical"]
    else:
        out["behavioural"] = None
        ok = False
    out["pass"] = ok
    json.dump(out, open(a.out, "w"), indent=1)
    open(a.out, "a").write("\n")
    b = out["behavioural"]
    print(f"patch observation check: {'PASS' if ok else 'FAIL'}"
          + (f"; behavioural: {b['contexts']} contexts, {b['ciphertextDigests']} ciphertexts, {b['decryptions']} decryptions, "
             f"differing lines {b['differingLines']}" if b else "; behavioural part not run"))
    return 0 if ok else 1


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--pristine")
    ap.add_argument("--patched")
    ap.add_argument("--patch")
    ap.add_argument("--allowlist")
    ap.add_argument("--combine")
    ap.add_argument("--digests", nargs="+")
    ap.add_argument("--traces")
    ap.add_argument("--out", required=True)
    a = ap.parse_args()
    sys.exit(combine(a) if a.combine else static(a))


if __name__ == "__main__":
    main()
