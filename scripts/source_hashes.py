#!/usr/bin/env python3
"""Compare the SHA-256 values that the fixtures' SOURCE*.txt record with the files in the tree.

Usage: source_hashes.py [--strict] [--rebase]      (run from the repository root, by the gate, step 1)

harness/*/fixtures/SOURCE*.txt say which tracer patch, tracer header, extractor and dumper
produced the recorded fixtures, with `<path> (sha256 <hex>)`. A recorded hash that no longer
matches the file in the tree means the evidence was recorded with other code than the one the
suites now ship. That can be legitimate (the tracer gained a version marker after the recording;
the fixtures were re-extracted, or are accepted as legacy), so a difference does not pass silently
either: it must be listed, with the recorded and the current hash, in trust/SOURCE-DRIFT.tsv
(columns: path, recorded sha256, current sha256, status, note). Status `unreviewed` is a
WARNING here and a failure under --strict (the STRICT=1 gate); `reviewed` means a maintainer
decided that the difference does not affect the fixtures. An entry whose hashes no longer match
what is in the tree is stale and fails. trust/SOURCE-DRIFT.tsv is itself in trust/EVIDENCE.
--rebase rewrites trust/SOURCE-DRIFT.tsv for the differences found now, keeping the status and
note of entries for the same path and recorded hash (new entries are `unreviewed`); maintainer only.
Exit 0: every recorded hash matches or is listed (and, with --strict, reviewed); 1 otherwise.
"""
import glob
import hashlib
import os
import re
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
DRIFT = "trust/SOURCE-DRIFT.tsv"
REC = re.compile(r"(\S+)\s+\(sha256 ([0-9a-f]{64})\)")


def sha(path):
    h = hashlib.sha256()
    with open(os.path.join(ROOT, path), "rb") as f:
        for chunk in iter(lambda: f.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def recorded():
    """[(source file, path, recorded sha)] from every harness/*/fixtures/SOURCE*.txt."""
    out = []
    for src in sorted(glob.glob(os.path.join(ROOT, "harness/*/fixtures/SOURCE*.txt"))):
        rel = os.path.relpath(src, ROOT)
        for line in open(src, encoding="utf-8"):
            last_dir = None
            for m in REC.finditer(line):
                p = m.group(1).strip(",;:")
                if "/" in p:
                    last_dir = os.path.dirname(p)
                elif last_dir:      # `which imports extract.py (sha256 ...)`: next to the previous path
                    p = os.path.join(last_dir, p)
                out.append((rel, p, m.group(2)))
    return out


def read_drift():
    entries = {}
    p = os.path.join(ROOT, DRIFT)
    if os.path.isfile(p):
        for line in open(p, encoding="utf-8"):
            if line.strip() and not line.startswith("#"):
                f = line.rstrip("\n").split("\t")
                if len(f) >= 4:
                    entries[(f[0], f[1])] = (f[2], f[3], f[4] if len(f) > 4 else "")
    return entries


def main(argv):
    strict = "--strict" in argv
    rebase = "--rebase" in argv
    recs = recorded()
    if not recs:
        print("FAILED: no `(sha256 ...)` record found in harness/*/fixtures/SOURCE*.txt")
        return 1
    drift = read_drift()
    seen, bad, unrev, diffs, nmatch = set(), [], [], [], 0
    for src, path, want in recs:
        if (path, want) in seen:
            continue
        seen.add((path, want))
        if not os.path.isfile(os.path.join(ROOT, path)):
            bad.append(f"{path}: recorded in {src} but not in the tree")
            continue
        have = sha(path)
        if have == want:
            nmatch += 1
            continue
        diffs.append((path, want, have, src))
        ack = drift.get((path, want))
        if ack is None or ack[0] != have:
            bad.append(f"{path}: {src} records {want[:12]}..., the tree has {have[:12]}..., and trust/SOURCE-DRIFT.tsv does not list this difference")
        elif ack[1] != "reviewed":
            unrev.append(f"{path} (recorded {want[:12]}..., tree {have[:12]}...): {ack[2]}")
    if rebase:
        lines = ["# SOURCE*.txt hashes that differ from the files in the tree: path<TAB>recorded sha256<TAB>current sha256<TAB>status<TAB>note",
                 "# status: unreviewed (warning; failure under STRICT=1) | reviewed. Maintained with scripts/source_hashes.py --rebase."]
        for path, want, have, src in sorted(diffs):
            old = drift.get((path, want))
            # a review applies to the content it saw: keep it only if the current hash is the one listed
            status, note = (old[1], old[2]) if old and old[0] == have else ("unreviewed", old[2] if old else f"recorded in {src}")
            lines.append("\t".join([path, want, have, status, note]))
        with open(os.path.join(ROOT, DRIFT), "w", encoding="utf-8") as h:
            h.write("\n".join(lines) + "\n")
        print(f"wrote {DRIFT} ({len(diffs)} entries)")
        return 0
    current = {(p, w) for p, w, _, _ in diffs}
    for (path, want), (have, status, note) in sorted(drift.items()):
        if (path, want) not in current:
            bad.append(f"{DRIFT}: stale entry for {path} (recorded {want[:12]}...): the recorded hash now matches or is no longer recorded")
    if bad:
        print("FAILED: SOURCE*.txt hashes against the tree:")
        for b in bad:
            print("  " + b)
    if unrev:
        print(f"{'FAILED (STRICT)' if strict else 'WARNING'}: {len(unrev)} recorded hash(es) differ from the tree and the difference is listed but UNREVIEWED in {DRIFT}:")
        for u in unrev:
            print("  " + u)
    if not bad and not unrev:
        print(f"ok ({nmatch} recorded hashes match the tree" + (f"; {len(diffs)} listed and reviewed differences" if diffs else "") + ")")
    elif not bad:
        print(f"({nmatch} recorded hashes match the tree)")
    return 1 if bad or (strict and unrev) else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
