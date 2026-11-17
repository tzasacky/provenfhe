#!/usr/bin/env python3
"""Textual audit of the definition holes (scripts/check-spec.sh, step 3).   TRUSTED; see trust/LOCK.

Usage: holes_audit.py ROOT_FILE OUT_DIR

Starts at ROOT_FILE (FHE/Holes.lean), follows its imports inside the FHE tree, and reports:

  banned:          a banned construct anywhere in the raw text (comments are NOT exempt);
  syntax/instance: a syntax extension, instance, or compile-time command, in code (comments and
                   string literals removed first, so a docstring or `open ... in` in front of the
                   keyword does not hide it);
  import:          an import of anything other than Lean/Mathlib, locked `Spec`/`Challenge` modules
                   (not the root `Challenge` or a headline statements module, HEADLINE_MODULES), or the FHE tree.

Imports are parsed from code with comments removed, with any `public`/`private`/`meta` prefix,
`import all`, and `«guillemet»` name components. Writes OUT_DIR/holes-files.txt (files audited) and
OUT_DIR/holes-modules-text.txt (their module names), which check-spec.sh compares with the import
closure read from the .olean headers by PinStatus: a module this parser misses fails the gate.

This is defence in depth. The structural guarantees (headline statements are literally
`<locked predicate> <hole>`; holes are computable, safe, kernel-checked definitions) are in
scripts/PinStatus.lean.
"""
import os
import re
import sys

TRUSTED_ROOTS = {"Init", "Std", "Lean", "Lake", "Mathlib", "Batteries", "Aesop", "Qq",
                 "Plausible", "ProofWidgets", "ImportGraph", "LeanSearchClient"}

# Challenge modules that import the holes (the root, and the statements modules of
# scripts/PinStatus.lean `headlineGroups`): the holes must not import them.
HEADLINE_MODULES = ("Challenge", "Challenge.Headline", "Challenge.Fast", "Challenge.Fast.Profile")

BANNED = re.compile(
    r"\bsorry\b|\badmit\b|\baxiom\b|implemented_by|@\[\s*extern|\bextern\b|\bunsafe\b|"
    r"native_decide|bv_decide|decide\s*\+\s*native|\bpartial\b|\bopaque\b|\bnoncomputable\b|"
    r"set_option\s+debug|\bdebug\.|skipKernelTC|addDecl|\brun_cmd\b|\brun_elab\b|\brun_meta\b|"
    r"#eval|\binitialize\b|\bbuiltin_initialize\b|\bLean\.Elab\b|\bLean\.Meta\b")

# commands that extend syntax, add instances, or run code at compile time
KW = (r"(?:macro|syntax|notation|elab|macro_rules|elab_rules|infix|infixl|infixr|prefix|postfix|"
      r"instance|binder_predicate|declare_syntax_cat|unif_hint|initialize|builtin_initialize|"
      r"run_cmd|run_elab|run_meta|attribute|declare_simp_like_tactic|register_option|"
      r"register_simp_attr|add_decl_doc|deriving\s+instance)")
MODS = r"(?:(?:@\[[^\]]*\]|local|scoped|private|protected|public|noncomputable|partial|unsafe|nonrec|meta)\s+)*"
SYNTAX_AT_START = re.compile(r"(?m)^[ \t]*" + MODS + KW + r"\b")
SYNTAX_AFTER_IN = re.compile(r"\bin\s+" + MODS + KW + r"\b")
BAD_ATTR = re.compile(
    r"@\[[^\]]*\b(instance|default_instance|macro|command_elab|term_elab|tactic|delab|"
    r"app_unexpander|builtin_\w+|env_linter|coe|init|implemented_by|extern|csimp)\b[^\]]*\]")
IMPORT = re.compile(r"\b((?:(?:public|private|meta)\s+)*)import\s+(all\s+)?([^\s]+)")


def strip(src: str) -> str:
    """Replace comments, string and char literals by spaces (newlines kept)."""
    out = []
    i, n = 0, len(src)

    def blank(s):
        return "".join("\n" if c == "\n" else " " for c in s)

    while i < n:
        c = src[i]
        if src.startswith("--", i):
            j = src.find("\n", i)
            j = n if j < 0 else j
            out.append(blank(src[i:j])); i = j
        elif src.startswith("/-", i):
            depth, j = 1, i + 2
            while j < n and depth:
                if src.startswith("/-", j): depth += 1; j += 2
                elif src.startswith("-/", j): depth -= 1; j += 2
                else: j += 1
            out.append(blank(src[i:j])); i = j
        elif c == '"' or (c == "r" and re.match(r'r#*"', src[i:]) and (i == 0 or not (src[i-1].isalnum() or src[i-1] in "_.'!?"))):
            if c == "r":
                m = re.match(r'r(#*)"', src[i:])
                close = '"' + m.group(1)
                j = src.find(close, i + len(m.group(0)))
                j = n if j < 0 else j + len(close)
            else:
                j = i + 1
                while j < n and src[j] != '"':
                    j += 2 if src[j] == "\\" else 1
                j = min(n, j + 1)
            out.append(blank(src[i:j])); i = j
        elif c == "'" and (i == 0 or not (src[i-1].isalnum() or src[i-1] in "_'.!?")) and \
                re.match(r"'(\\.[^']*|[^\\'])'", src[i:]):
            m = re.match(r"'(\\.[^']*|[^\\'])'", src[i:])
            out.append(blank(m.group(0))); i += len(m.group(0))
        else:
            out.append(c); i += 1
    return "".join(out)


def module_name(raw: str) -> str:
    return ".".join(p.strip("«»") for p in raw.split("."))


def main():
    root, out_dir = sys.argv[1], sys.argv[2]
    findings, files, mods = [], [], []
    queue, seen = [root], set()
    while queue:
        f = queue.pop(0)
        if f in seen:
            continue
        seen.add(f)
        files.append(f)
        mods.append(f[:-5].replace("/", ".") if f.endswith(".lean") else f)
        if not os.path.isfile(f):
            findings.append(f"missing: {f}")
            continue
        raw = open(f, encoding="utf-8").read()
        code = strip(raw)
        for ln, line in enumerate(raw.splitlines(), 1):
            if BANNED.search(line):
                findings.append(f"banned: {f}:{ln}:{line.strip()}")
        for rx in (SYNTAX_AT_START, SYNTAX_AFTER_IN, BAD_ATTR):
            for m in rx.finditer(code):
                ln = code.count("\n", 0, m.start()) + 1
                findings.append(f"syntax/instance: {f}:{ln}:{raw.splitlines()[ln-1].strip()}")
        for m in IMPORT.finditer(code):
            prefix, allkw, name = m.group(1).split(), m.group(2), module_name(m.group(3))
            ln = code.count("\n", 0, m.start()) + 1
            where = f"{f}:{ln}:{raw.splitlines()[ln-1].strip()}"
            top = name.split(".")[0]
            if "meta" in prefix:
                findings.append(f"import (meta: compile-time code): {where}")
            if top == "FHE":
                queue.append(name.replace(".", "/") + ".lean")
            elif top in TRUSTED_ROOTS or top == "Spec":
                pass
            elif top == "Challenge" and name not in HEADLINE_MODULES:
                pass
            else:
                findings.append(f"forbidden import: {where}")
    with open(os.path.join(out_dir, "holes-files.txt"), "w") as h:
        h.write("".join(x + "\n" for x in files))
    with open(os.path.join(out_dir, "holes-modules-text.txt"), "w") as h:
        h.write("".join(x + "\n" for x in sorted(set(mods))))
    with open(os.path.join(out_dir, "holes.txt"), "w") as h:
        h.write("".join(x + "\n" for x in dict.fromkeys(findings)))
    if findings:
        print("FAILED:")
        for x in dict.fromkeys(findings):
            print(x)
        return 1
    print(f"ok ({len(files)} file(s): {' '.join(files)})")
    return 0


if __name__ == "__main__":
    sys.exit(main())
