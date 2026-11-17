#!/usr/bin/env python3
"""UNTRUSTED. sha256 manifest of a suite of openfhe-pin cases (the raw cases of the real-size
suites stay out of the repository; this manifest identifies them).

  sha_manifest.py SUITE_DIR > MANIFEST.sha256.tsv

One line per case, sorted by name: case, N, bytes (the five files), wall seconds of the export
(from MANIFEST.tsv, if it has that column), then the sha256 of params.json, trace.jsonl,
prog.fhecheck.json, pin.json, polys.txt.
"""
import hashlib
import json
import os
import sys

FILES = ["params.json", "trace.jsonl", "prog.fhecheck.json", "pin.json", "polys.txt"]


def sha(path):
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for blk in iter(lambda: f.read(1 << 22), b""):
            h.update(blk)
    return h.hexdigest()


def main():
    d = sys.argv[1]
    secs = {}
    mf = os.path.join(d, "MANIFEST.tsv")
    if os.path.exists(mf):
        rows = [l.rstrip("\n").split("\t") for l in open(mf)]
        if "seconds" in rows[0]:
            k = rows[0].index("seconds")
            secs = {r[0]: r[k] for r in rows[1:] if len(r) > k}
    print("# case\tN\tbytes\tseconds\t" + "\t".join("sha256(" + f + ")" for f in FILES))
    for c in sorted(os.listdir(d)):
        p = os.path.join(d, c)
        if not all(os.path.isfile(os.path.join(p, f)) for f in FILES):
            continue
        n = json.load(open(os.path.join(p, "pin.json")))["N"]
        size = sum(os.path.getsize(os.path.join(p, f)) for f in FILES)
        print("\t".join([c, str(n), str(size), secs.get(c, "")] + [sha(os.path.join(p, f)) for f in FILES]))


if __name__ == "__main__":
    main()
