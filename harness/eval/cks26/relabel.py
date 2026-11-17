#!/usr/bin/env python3
"""UNTRUSTED glue of the CKS26 evaluation (harness/eval/cks26): a CROSS-CHECK only. It relabels the
CoefPacked plaintexts of a BFV trace as packed.

    relabel.py IN.trace.jsonl OUT.trace.jsonl      prints the number of records changed

History. When this evaluation started, harness/frontend/openfhe/extract_bfv.py refused every
plaintext that was not packed, and the attack code of Choe-Kang-Stehle uses
MakeCoefPackedPlaintext throughout (for most of its plaintext moduli no packed plaintext exists),
so the first verdicts were obtained on relabelled traces, under the assumption that a BFV
CoefPacked plaintext is stored with every coefficient in [0, t). The extractor now accepts such
plaintexts itself (Extractor.check_packed: BFVRNS, scalingFactorInt = 1;
coefpackedencoding.cpp:46-70), and every verdict is on the trace as traced.

What it is used for now: run.py extracts every CoefPacked run a second time from the relabelled
trace and records whether the two extractions have identical parameters and program
(summary field relabelCrossCheck.identical); the native one carries one more derivation note
(noiseDerivation.coefPackedPlaintexts). Nothing is certified from a relabelled trace.

Only the value of the "enc" field of records of kind "pt" is touched.
"""
import json
import sys


def main():
    src, dst = sys.argv[1], sys.argv[2]
    n = 0
    with open(src) as f, open(dst, "w") as g:
        for line in f:
            if '"enc":"coefpacked"' in line:
                rec = json.loads(line)
                if rec.get("kind") != "pt" or rec.get("enc") != "coefpacked":
                    raise SystemExit(f"unexpected record with a coefpacked encoding: {line[:120]}")
                line = line.replace('"enc":"coefpacked"', '"enc":"packed"')
                n += 1
            g.write(line)
    print(n)


if __name__ == "__main__":
    main()
