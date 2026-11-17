#!/usr/bin/env python3
"""UNTRUSTED test: OpenFHE's own FindLevelsToDrop (bfvrns-leveledshe.cpp:102-202), as bfv_demo
recorded it in every params.json (`levelsToDrop`: the exported library function called on the
context for levels 0..63, with and without the keySwitch flag), against the two Python replicas:
openfhe/extract_bfv.py find_levels_to_drop and harness/bfv-rns/find_levels_to_drop.py.

    check_find_levels_to_drop.py PARAMS.json...      exit 0 iff every entry of every table agrees
"""
import json
import os
import struct
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.dont_write_bytecode = True
sys.path.insert(0, os.path.join(HERE, "..", "openfhe"))
sys.path.insert(0, os.path.join(HERE, "..", "..", "bfv-rns"))
import extract_bfv  # noqa: E402

try:
    import find_levels_to_drop as analysis  # noqa: E402
except ImportError:
    analysis = None


def main():
    bad = n = 0
    for path in sys.argv[1:]:
        p = json.load(open(path))
        if p.get("scheme") != "BFV":
            continue
        tab = p["levelsToDrop"]
        for ks in (False, True):
            lib = tab["keySwitch" if ks else "mul"]
            for d, want in enumerate(lib):
                got = [extract_bfv.find_levels_to_drop(p, d, tab["dcrtBits"], ks)]
                if analysis is not None:
                    got.append(analysis.find_levels_to_drop(
                        d, ring_dim=p["N"], plaintext_modulus=p["t"], dcrt_bits=tab["dcrtBits"], size_q=len(p["qs"]),
                        key_switch=ks, digit_size=p["digitSizeBV"], ks_technique=p["keySwitch"],
                        encryption_technique=p["encryptionTechnique"], secret_key_dist=p["secretKeyDist"],
                        sigma=struct.unpack("f", struct.pack("f", float(p["sigma"])))[0], assurance=float(p["assuranceMeasure"]),
                        threshold_parties=p["thresholdParties"], num_per_part_q=p["towersPerDigit"], num_part_q=p["dnum"]))
                n += 1
                if any(g != want for g in got):
                    bad += 1
                    if bad <= 5:
                        print(f"{path}: levels {d}, keySwitch {ks}: library {want}, replicas {got}")
    print(f"find_levels_to_drop: {n} table entries, {bad} disagreement(s); "
          f"replicas: extract_bfv.py{' and harness/bfv-rns/find_levels_to_drop.py' if analysis else ''}")
    return 1 if bad or not n else 0


if __name__ == "__main__":
    sys.exit(main())
