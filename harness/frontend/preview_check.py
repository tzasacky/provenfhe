#!/usr/bin/env python3
"""UNTRUSTED preview of fhe_check on a neutral fhe-check/v1 JSON file (kept as an independent
Python cross-check of the Lean tool; the verdict that counts is `fhe_check`'s).

This mirrors, in Python, what the Lean `fhe_check` executable will do:
  1. the `ParamsOK` clauses of Spec/Params.lean (primality, oddness, 32-bit fit, 2N-th roots,
     distinctness, t coprime to every modulus) -- each reported separately, because the 32-bit
     `fits` clause is a storage condition of a 32-bit accelerator, not a noise condition;
  2. the budget: E.keySwitch = max over the levels where relin/keySwitch occurs of
     ksBound N Bk Bs t (k*P) P M   (FHE/KeySwitch/Core.lean, Step.lean), M_j = l_j * Q_j;
     E.modSwitch = t * (1 + N * Bs)  (Challenge/Trace.lean stepOK_modSwitch_textbook);
  3. refAnalyze (Challenge/Headline/Defs.lean, refBound/refRun): textbook worst-case bounds,
     each intermediate must satisfy 2B < Q at its level.
It is a preview for design work; the verdict that counts is the Lean one.

Plaintext operations and `dropLimbs` follow refBound (Challenge/Headline/Defs.lean).
"""
import json
import math
import sys


def is_prime(n):
    if n < 2:
        return False
    for p in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37):
        if n % p == 0:
            return n == p
    d, s = n - 1, 0
    while d % 2 == 0:
        d //= 2
        s += 1
    for a in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37):
        x = pow(a, d, n)
        if x in (1, n - 1):
            continue
        for _ in range(s - 1):
            x = x * x % n
            if x == n - 1:
                break
        else:
            return False
    return True


def limb_q(l):
    return int(l["q"]) if isinstance(l, dict) else int(l)


def limb_psi(l):
    return int(l["psi"]) if isinstance(l, dict) and l.get("psi") is not None else None


def lg(x):
    return math.log2(x) if x > 0 else float("-inf")


def params_ok(P):
    N, t = int(P["N"]), int(P["t"])
    limbs = [(limb_q(l), limb_psi(l)) for l in P["limbs"]]
    special = [(limb_q(l), limb_psi(l)) for l in P["special"]]
    allq = limbs + special
    r = {
        "N_pow2": N > 0 and N & (N - 1) == 0,
        "limbs_nonempty": len(limbs) > 0,
        "prime": all(is_prime(q) for q, _ in allq),
        "odd": all(q % 2 == 1 for q, _ in allq),
        "fits_2^32": all(q < 2 ** 32 for q, _ in allq),
        "root": (all(pow(psi, N, q) == q - 1 for q, psi in allq) if all(psi is not None for _, psi in allq)
                 else "psi absent; q = 1 mod 2N: " + str(all(q % (2 * N) == 1 for q, _ in allq))),
        "distinct": len({q for q, _ in allq}) == len(allq),
        "plaintext": t >= 2 and all(math.gcd(t, q) == 1 for q, _ in allq),
        "msgRange t/2<=inputNoise": t // 2 <= int(P["inputNoise"]),
    }
    return r


def digits_at(level, alpha, qs):
    """OpenFHE consecutive digits at `level` limbs: list of (size, product)."""
    out = []
    for j in range(0, level, alpha):
        grp = qs[j:min(j + alpha, level)]
        out.append((len(grp), math.prod(grp)))
    return out


def ks_bound(N, Bk, Bs, t, F, Pp, M):
    return (N * Bk * sum(M) + t * F * (1 + N * Bs)) // (2 * Pp)


def ks_weights(variant, digits, k, Pp):
    """(M_j, F) of FHE.KeySwitch: centred digitWeight / k*P, canonical canonWeight / 2k(P-1)."""
    if variant == "centred":
        return [s * Q for s, Q in digits], k * Pp
    return [2 * (s * (Q - 1)) for s, Q in digits], 2 * (k * (Pp - 1))


OLD_MS = "--old-modswitch" in sys.argv


def run(doc):
    P, prog = doc["params"], doc["program"]
    N, t = int(P["N"]), int(P["t"])
    qs = [limb_q(l) for l in P["limbs"]]
    sp = [limb_q(l) for l in P["special"]]
    Pp = math.prod(sp)
    Bs, Bk, B0 = P["secretBound"], int(P["keyNoise"]), int(P["inputNoise"])
    alpha = doc["keySwitching"]["digits"]["towersPerDigit"]
    mod = lambda l: math.prod(qs[:l])

    # levels of every variable (Source.step's level bookkeeping)
    lev, parts, key = {}, {}, {}
    for d in prog["inputs"]:
        lev[d["name"]], parts[d["name"]], key[d["name"]] = d["level"], d["parts"], d.get("key", 1)
    ks_levels = set()
    for i in prog["body"]:
        a = i["a"]
        if a not in lev:
            return {"verdict": "reject", "reason": f"undefined operand {a}"}
        l = lev[a]
        if i["op"] in ("relin", "keySwitch"):
            ks_levels.add(l)
        if i["op"] in ("modSwitch",):
            l -= 1
        if i["op"] == "dropLimbs":
            l -= i["k"]
        lev[i["dst"]] = l
    variant = doc["keySwitching"].get("variant", "centred")
    E_ks = 0
    for l in ks_levels:
        M, F = ks_weights(variant, digits_at(l, alpha, qs), len(sp), Pp)
        E_ks = max(E_ks, ks_bound(N, Bk, Bs, t, F, Pp, M))
    # Challenge.Trace.stepOK_modSwitch_textbook: ceil(t*(1+N*Bs)/2) for the centred switch.
    # --old-modswitch reproduces the v0 preview's t*(1+N*Bs).
    E_ms = t * (1 + N * Bs) if OLD_MS else -(-t * (1 + N * Bs) // 2)
    # Spec.Budget.msBudgetOne: a 1-part value (plaintext operand) has no secret-dependent term.
    E_ms1 = (t + 1) // 2

    # refAnalyze
    lev, parts, key, beta = {}, {}, {}, {}
    for d in prog["inputs"]:
        n = d["name"]
        lev[n], parts[n], key[n] = d["level"], d["parts"], d.get("key", 1)
        beta[n] = min(int(d["bound"]), B0) if "bound" in d else B0
    steps, worst_margin = [], None
    ext_ops = False
    for idx, i in enumerate(prog["body"]):
        op, dst = i["op"], i["dst"]
        a, b = i["a"], i.get("b")
        x = beta[a]
        la, pa, ka = lev[a], parts[a], key[a]
        if op in ("add", "sub"):
            if lev[b] != la or key[b] != ka:
                return {"verdict": "reject", "reason": f"op {idx}: level/key mismatch"}
            B, l, p, k = x + beta[b], la, max(pa, parts[b]), ka
        elif op == "mul":
            if lev[b] != la or key[b] != ka:
                return {"verdict": "reject", "reason": f"op {idx}: level/key mismatch"}
            B, l, p, k = N * x * beta[b], la, pa + parts[b] - 1, ka
        elif op == "square":
            B, l, p, k = N * x * x, la, 2 * pa - 1, ka
        elif op == "mulConst":
            B, l, p, k = abs(int(i["c"])) * x, la, pa, ka
        elif op == "negate":
            B, l, p, k = x, la, pa, ka
        elif op == "copy":
            B, l, p, k = x, la, pa, ka
        elif op == "automorph":
            B, l, p, k = x, la, pa, (ka * i["g"]) % (2 * N)
        elif op == "relin":
            if not (pa == 3 and ka == 1):
                return {"verdict": "reject", "reason": f"op {idx}: relin needs 3 parts under s"}
            B, l, p, k = x + E_ks, la, 2, 1
        elif op == "keySwitch":
            if pa != 2:
                return {"verdict": "reject", "reason": f"op {idx}: keySwitch needs 2 parts"}
            B, l, p, k = x + E_ks, la, 2, 1
        elif op == "modSwitch":
            if la < 2:
                return {"verdict": "reject", "reason": f"op {idx}: modSwitch at level 1"}
            if pa not in (1, 2):
                return {"verdict": "reject", "reason": f"op {idx}: modSwitch of a {pa}-part "
                        "ciphertext is outside the proved budgets (modSwitch_realizable: 2 parts, _one: 1 part)"}
            B, l, p, k = x // qs[la - 1] + (E_ms1 if pa == 1 else E_ms), la - 1, pa, ka
        elif op in ("addPlain", "subPlain", "mulPlain"):
            q = i["p"]
            if parts[q] != 1 or lev[q] != la:
                return {"verdict": "reject", "reason": f"op {idx}: plaintext operand must have 1 part at the same level"}
            if op == "mulPlain":
                B, l, p, k = N * x * beta[q], la, pa, ka
            else:
                B, l, p, k = x + beta[q], la, max(pa, 1), ka
        elif op == "dropLimbs":
            if not 0 <= i["k"] < la:
                return {"verdict": "reject", "reason": f"op {idx}: dropLimbs must leave a limb"}
            B, l, p, k = x, la - i["k"], pa, ka
        else:
            return {"verdict": "reject", "reason": f"op {idx}: unknown op {op}"}
        Q = mod(l)
        margin = lg(Q) - 1 - lg(B)
        steps.append({"index": idx, "op": op, "dst": dst, "level": l, "log2B": round(lg(B), 2),
                      "log2Q": round(lg(Q), 2), "marginBits": round(margin, 2)})
        if not 2 * B < Q:
            return {"verdict": "reject", "reason": f"op {idx} ({op} -> {dst}): bound 2^{lg(B):.2f} "
                    f"not below Q/2 = 2^{lg(Q) - 1:.2f} at level {l}",
                    "budget": {"keySwitch_log2": round(lg(E_ks), 2), "modSwitch_log2": round(lg(E_ms), 2)},
                    "steps": steps}
        if "expect" in i and (i["expect"]["level"], i["expect"]["parts"]) != (l, p):
            return {"verdict": "reject", "reason": f"op {idx}: frontend says level/parts "
                    f"{i['expect']}, Source.step gives {(l, p)}"}
        lev[dst], parts[dst], key[dst], beta[dst] = l, p, k, B
    outs = []
    switched = doc.get("decryption", {}).get("method") == "switch-to-one-limb"
    for o in prog["outputs"]:
        Q = mod(lev[o])
        outs.append({"output": o, "level": lev[o], "log2B": round(lg(beta[o]), 2),
                     "marginBits": round(lg(Q) - 1 - lg(beta[o]), 2)})
        if switched:
            # Spec.Decrypt.decBound: the phase switched down to q0, floor((B + t*floor(q/2))/q) per limb
            D = beta[o]
            for l in range(lev[o], 1, -1):
                D = (D + t * (qs[l - 1] // 2)) // qs[l - 1]
            outs[-1]["log2DecBound"] = round(lg(D), 2)
            if not 2 * D < qs[0]:
                return {"verdict": "reject", "reason": f"output {o}: switched-decryption bound 2^{lg(D):.2f} "
                        f"not below q0/2 = 2^{lg(qs[0]) - 1:.2f}",
                        "budget": {"keySwitch_log2": round(lg(E_ks), 2), "modSwitch_log2": round(lg(E_ms), 2)}}
    return {"verdict": "accept", "bound": max(beta[o] for o in prog["outputs"]),
            "usesExtensionOps": ext_ops,
            "budget": {"keySwitch_log2": round(lg(E_ks), 2), "modSwitch_log2": round(lg(E_ms), 2)},
            "outputs": outs, "steps": steps}


def main():
    doc = json.load(open(sys.argv[1]))
    if "error" in doc:
        print(json.dumps({"verdict": "extraction-failed", "reason": doc["error"]}, indent=1))
        return
    P = doc["params"]
    rep = {"paramsOK": params_ok(P),
           "limbBits": [round(lg(limb_q(l)), 2) for l in P["limbs"]],
           "specialBits": [round(lg(limb_q(l)), 2) for l in P["special"]],
           "log2_inputNoise": round(lg(int(P["inputNoise"])), 2),
           "log2_keyNoise": round(lg(int(P["keyNoise"])), 2)}
    rep["noise"] = run(doc)
    if "--brief" in sys.argv:
        rep["noise"].pop("steps", None)
    print(json.dumps(rep, indent=1))


if __name__ == "__main__":
    main()
