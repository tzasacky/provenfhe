#!/usr/bin/env python3
"""UNTRUSTED test helper: print TRACE without its traced Encrypt calls (and, with --keys, without the
key generation too: KeyGen, EvalMultKeyGen, rotation-key generation), as a trace that starts after
encryption looks.   strip.py [--keys] TRACE"""
import json
import sys

keys = "--keys" in sys.argv
path = [a for a in sys.argv[1:] if a != "--keys"][0]
skip = None
for line in open(path):
    o = json.loads(line)
    if skip is None and o["ev"] == "begin" and o["d"] == 0 and (
            o["fn"].startswith("CryptoContext::Encrypt") or (keys and "KeyGen" in o["fn"].split("(")[0])):
        skip = o["d"]
        continue
    if skip is not None:
        if o["ev"] == "end" and o["d"] == skip:
            skip = None
        continue
    sys.stdout.write(line)
