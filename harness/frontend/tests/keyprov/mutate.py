#!/usr/bin/env python3
"""UNTRUSTED test helper: derive key-provenance red-team traces from real OpenFHE v1.6.1 traces.

  mutate.py KIND TRACE > OUT

Each KIND turns an honest trace into what the trace of a program the single-party noise model
does NOT cover would look like, or into a trace a correct extractor must refuse:
  cut_before_decrypt   keep every top-level call before the first MultipartyDecryptLead (the
                       trace of the evaluating party of a threshold program)
  cut_hide_multiparty  the same, and also delete the MultipartyKeyGen calls (as if the joint key
                       had been made by untraced code or another process): only key provenance
                       can tell that the encryption key is not a single-party KeyGen key
  drop_keygen          delete CryptoContext::KeyGen() (keys made before the trace started)
  drop_multkeygen      delete EvalMultKeyGen (relinearization key deserialized or inserted)
  swap_rotation_index  exchange the indices of the first two generated rotation keys (a key for
                       one automorphism used for another)
  second_secret        a second KeyGen whose secret key generates the relinearization key
  thread_error         the event the tracer writes when a traced call runs on another thread
  drop_eval            delete the first top-level CryptoContext::EvalMult (its output becomes a
                       ciphertext with no traced origin)
  dup_eval             repeat the first top-level CryptoContext::EvalMult right after itself (an
                       exact recomputation, for the --cse test)
"""
import json
import sys


def calls(lines):
    """Split the trace into top-level calls: list of (fn, [lines])."""
    out, cur, fn = [], None, None
    for ln in lines:
        o = json.loads(ln)
        if cur is None:
            cur, fn = [], o.get("fn")
        cur.append(ln)
        if o["ev"] == "end" and o["d"] == 0:
            out.append((fn, cur))
            cur = None
    return out


def main():
    kind, path = sys.argv[1], sys.argv[2]
    lines = [ln for ln in open(path) if ln.strip()]
    cs = calls(lines)
    if kind in ("cut_before_decrypt", "cut_hide_multiparty"):
        k = next(i for i, (fn, _) in enumerate(cs) if fn.startswith("CryptoContext::MultipartyDecryptLead"))
        cs = cs[:k]
        if kind == "cut_hide_multiparty":
            cs = [c for c in cs if not c[0].startswith("CryptoContext::MultipartyKeyGen")]
    elif kind == "drop_keygen":
        cs = [c for c in cs if not c[0].startswith("CryptoContext::KeyGen")]
    elif kind == "drop_multkeygen":
        cs = [c for c in cs if not c[0].startswith("CryptoContext::EvalMultKeyGen")]
    elif kind == "drop_eval":
        k = next(i for i, (fn, _) in enumerate(cs) if fn.startswith("CryptoContext::EvalMult("))
        cs = cs[:k] + cs[k + 1:]
    elif kind == "dup_eval":
        k = next(i for i, (fn, _) in enumerate(cs) if fn.startswith("CryptoContext::EvalMult("))
        cs = cs[:k + 1] + [cs[k]] + cs[k + 1:]
    elif kind == "swap_rotation_index":
        done = False
        for i, (fn, ls) in enumerate(cs):
            if "KeyGen" in fn and not done:
                recs = [json.loads(x) for x in ls]
                idx = [j for j, o in enumerate(recs) if o.get("kind") == "ek" and o["ev"] == "out" and "index" in o]
                if len(idx) >= 2:
                    a, b = idx[0], idx[1]
                    recs[a]["index"], recs[b]["index"] = recs[b]["index"], recs[a]["index"]
                    cs[i] = (fn, [json.dumps(o, separators=(",", ":")) + "\n" for o in recs])
                    done = True
        assert done
    elif kind == "second_secret":
        out = []
        for fn, ls in cs:
            if fn.startswith("CryptoContext::KeyGen"):
                out.append((fn, ls))
                extra = [x.replace('"pk_1"', '"pk_99"').replace('"sk_1"', '"sk_99"') for x in ls]
                out.append((fn, extra))
            elif fn.startswith("CryptoContext::EvalMultKeyGen"):
                out.append((fn, [x.replace('"sk_1"', '"sk_99"') for x in ls]))
            else:
                out.append((fn, ls))
        cs = out
    elif kind == "thread_error":
        err = json.dumps({"ev": "error", "what": "a traced OpenFHE call ran on another thread or inside an OpenMP "
                          "parallel region; the call tree is not reliable (run with OMP_NUM_THREADS=1)"}) + "\n"
        cs = cs[:1] + [("error", [err])] + cs[1:]
    else:
        sys.exit(f"unknown kind {kind}")
    for _, ls in cs:
        sys.stdout.writelines(ls)


if __name__ == "__main__":
    main()
