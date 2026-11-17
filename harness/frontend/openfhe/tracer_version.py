#!/usr/bin/env python3
"""UNTRUSTED helper: the fhecheck tracer version (fhecheck-tracer.h, "Tracer version").

  tracer_version.py                  print the version; exit 1 if the header's declared
                                     FHECHECK_TRACER_VERSION is not the SHA-256 of its content
  tracer_version.py --update-header  write the right value into fhecheck-tracer.h (after editing
                                     the header; then regenerate openfhe-v1.6.1-tracer.patch and
                                     rebuild with build_openfhe.sh)
  tracer_version.py --allowlist      regenerate legacy-traces.tsv: the SHA-256 pair (params.json,
                                     trace) of every COMMITTED trace whose params.json records no
                                     tracer version (git ls-files: <stem>.params.json +
                                     <stem>.trace.jsonl, <dir>/params.json + <dir>/trace.jsonl, and
                                     the same pairs inside committed *.tar.xz), which the
                                     extractors accept without a version
  tracer_version.py --allowlist --check
                                     exit 1 if legacy-traces.tsv differs from the regenerated list
  tracer_version.py --stamp PARAMS   print PARAMS (a params.json) with "tracer" set to the current
                                     version (tests that derive a trace from a committed one)
"""
import hashlib
import io
import json
import os
import subprocess
import sys
import tarfile

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
sys.dont_write_bytecode = True
from extract import LEGACY_TRACES, TRACER_HEADER, TRACER_VERSION_RE, stamp_tracer, tracer_header_version  # noqa: E402

ROOT = os.path.abspath(os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..", ".."))


def pair_of(name):
    """The trace member that goes with a params member, or None."""
    if name.endswith(".params.json"):
        return name[: -len(".params.json")] + ".trace.jsonl"
    if os.path.basename(name) == "params.json":
        return os.path.join(os.path.dirname(name), "trace.jsonl")
    return None


def entry(label, pbytes, tbytes):
    try:
        p = json.loads(pbytes)
    except ValueError:
        return None
    if isinstance(p, dict) and "tracer" in p:
        return None  # versioned: checked by version, not listed
    return (hashlib.sha256(pbytes).hexdigest(), hashlib.sha256(tbytes).hexdigest(), label)


def committed_pairs():
    files = subprocess.run(["git", "ls-files", "-z"], cwd=ROOT, capture_output=True, check=True).stdout.decode().split("\0")
    tracked = set(files)
    out = []
    for f in sorted(tracked):
        t = pair_of(f)
        if t and t in tracked:
            e = entry(f[: -len("params.json")], open(os.path.join(ROOT, f), "rb").read(),
                      open(os.path.join(ROOT, t), "rb").read())
            if e:
                out.append(e)
        if f.endswith(".tar.xz"):
            with tarfile.open(os.path.join(ROOT, f)) as tf:
                mem = {m.name: m for m in tf.getmembers() if m.isfile()}
                for n in sorted(mem):
                    t = pair_of(n)
                    if t and t in mem:
                        e = entry(f"{f}:{n[: -len('params.json')]}", tf.extractfile(mem[n]).read(),
                                  tf.extractfile(mem[t]).read())
                        if e:
                            out.append(e)
    return out


def allowlist_text():
    rows = sorted(set(committed_pairs()))
    buf = io.StringIO()
    buf.write("# sha256(params.json)\tsha256(trace.jsonl)\twhere : committed traces whose params.json records no\n"
              "# tracer version, accepted by extract.py / extract_bfv.py without one (tracer_version.py --allowlist)\n")
    for ps, ts, label in rows:
        buf.write(f"{ps}\t{ts}\t{label}\n")
    return buf.getvalue()


def main():
    args = sys.argv[1:]
    declared, computed = tracer_header_version()
    if args == ["--update-header"]:
        data = open(TRACER_HEADER, "rb").read()
        data = TRACER_VERSION_RE.sub(b'#define FHECHECK_TRACER_VERSION "' + computed.encode() + b'"', data)
        open(TRACER_HEADER, "wb").write(data)
        print(computed)
        return 0
    if args in (["--allowlist"], ["--allowlist", "--check"]):
        text = allowlist_text()
        if "--check" in args:
            same = os.path.exists(LEGACY_TRACES) and open(LEGACY_TRACES).read() == text
            print("legacy-traces.tsv " + ("is current" if same else "differs from the committed traces: run "
                                          "tracer_version.py --allowlist"))
            return 0 if same else 1
        open(LEGACY_TRACES, "w").write(text)
        print(f"{LEGACY_TRACES}: {text.count(chr(10)) - 2} pairs")
        return 0
    if len(args) == 2 and args[0] == "--stamp":
        print(json.dumps(stamp_tracer(json.load(open(args[1]))), indent=1))
        return 0
    if args:
        print(__doc__, file=sys.stderr)
        return 2
    print(computed)
    if declared != computed:
        print(f"fhecheck-tracer.h declares FHECHECK_TRACER_VERSION {declared}, its content gives {computed}: "
              "run tracer_version.py --update-header", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
