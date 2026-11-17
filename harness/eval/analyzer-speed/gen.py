#!/usr/bin/env python3
"""Synthetic fhe-check/v1 programs for the analyzer-speed benchmark.

Usage: gen.py BASE.fhecheck.json KIND N OUT.json [--outputs K] [--adjustments]

BASE supplies the parameters (a committed example: BGV or BFV). KIND picks the body:

  add       x_i = add x_{i-1} b                         (N instructions)
  rot       g = automorph a 5; k = keySwitch g; acc = add acc k   (N/3 blocks; "rotate-and-add")
  mulrelin  m = mul a b; r = relin m                    (N/2 blocks; products of the inputs)
  modswitch s_i = modSwitch a                           (N instructions; every one from the top level)
  lincomb   m_i = mulPlain a p_i; acc = add acc m_i     (N/2 blocks, N/2 plaintext INPUTS with bounds:
                                                         a linear combination with N/2 terms)
  mixed     one block of each of the above in turn
  sumsq     N fresh ciphertext INPUTS c_i: t_i = mulConst c_i k_i; acc = add acc t_i; then 44 times
            acc = relin (square acc)        (2N + 87 instructions: the sum of M = N ciphertexts with
                                             integer coefficients followed by squarings, the shape
                                             of the phase-2/3 circuit of ePrint 2026/2546)

Every program is well formed; whether it is CERTIFIED depends on the parameters and N (the
benchmark records the verdict). KIND mulconst is constant multiplications only (use with --adjustments). --adjustments adds a constant multiplication to each block of the kind and declares every one a scale adjustment. --outputs K lists the last K distinct destinations as outputs.
If BASE has scaling data (OpenFHE BGV files), it is rewritten to declare factor 1 for every input
of the generated program, so that the user-level decryption check runs on the whole program as it
does on an extracted one; --no-scaling keeps BASE's (which then names inputs the program does not
have, and that check stops at once).
"""
import json
import sys


def main():
    base, kind, n, out = sys.argv[1], sys.argv[2], int(sys.argv[3]), sys.argv[4]
    k = int(sys.argv[sys.argv.index("--outputs") + 1]) if "--outputs" in sys.argv else 1
    d = json.load(open(base))
    L = len(d["params"]["limbs"])
    bfv = d["params"]["scheme"] == "BFV"
    inputs = [{"name": "a", "parts": 2, "level": L}, {"name": "b", "parts": 2, "level": L}]
    body, dsts = [], []
    c = [0]

    def fresh(p="x"):
        c[0] += 1
        return f"{p}{c[0]}"

    def emit(op, dst, **kw):
        body.append({"op": op, "dst": dst, **kw})
        dsts.append(dst)

    acc = {"add": "a", "rot": "a", "lin": None}
    pbound = str(int(d["params"]["t"]) - 1)

    def blk_add():
        x = fresh()
        emit("add", x, a=acc["add"], b="b")
        acc["add"] = x

    def blk_rot():
        g, s, x = fresh("g"), fresh("k"), fresh()
        emit("automorph", g, a="a", g=5)
        emit("keySwitch", s, a=g)
        emit("add", x, a=acc["rot"], b=s)
        acc["rot"] = x

    def blk_mulrelin():
        m, r = fresh("m"), fresh("r")
        emit("mul", m, a="a", b="b")
        emit("relin", r, a=m)

    def blk_modswitch():
        emit("modSwitch", fresh("s"), a="a")

    def blk_lincomb():
        p, m = fresh("p"), fresh("m")
        inputs.append({"name": p, "parts": 1, "level": L, "bound": pbound})
        emit("mulPlain", m, a="a", p=p)
        if acc["lin"] is None:
            acc["lin"] = m
        else:
            x = fresh()
            emit("add", x, a=acc["lin"], b=m)
            acc["lin"] = x

    blocks = {"add": [blk_add], "rot": [blk_rot], "mulrelin": [blk_mulrelin],
              "modswitch": [blk_modswitch], "lincomb": [blk_lincomb],
              "mixed": [blk_add, blk_rot, blk_mulrelin, blk_modswitch, blk_lincomb],
              "sumsq": [], "mulconst": []}[kind]
    def blk_mulconst():
        emit("mulConst", fresh("c"), a="a", c=3)

    if kind == "mulconst":
        blocks = [blk_mulconst]
    elif "--adjustments" in sys.argv and kind != "sumsq":
        blocks = blocks + [blk_mulconst]
    fresh_inputs = ["a", "b"]
    if kind == "sumsq":
        inputs.clear()
        fresh_inputs = []
        cur = None
        for j in range(n):
            ci = f"c{j}"
            inputs.append({"name": ci, "parts": 2, "level": L})
            fresh_inputs.append(ci)
            t = fresh("t")
            emit("mulConst", t, a=ci, c=(j % 7) - 3 or 1)
            if cur is None:
                cur = t
            else:
                x = fresh()
                emit("add", x, a=cur, b=t)
                cur = x
        for _ in range(44):
            q, r = fresh("q"), fresh("r")
            emit("square", q, a=cur)
            emit("relin", r, a=q)
            cur = r
    i = 0
    while kind != "sumsq" and len(body) < n:
        blocks[i % len(blocks)]()
        i += 1
    outs = []
    for x in reversed(dsts):
        if x not in outs:
            outs.append(x)
        if len(outs) == k:
            break
    d["program"] = {"inputs": inputs, "body": body, "outputs": list(reversed(outs))}
    if "freshEncryption" in d:
        d["freshEncryption"]["inputs"] = fresh_inputs
    if "scaling" in d and "--no-scaling" not in sys.argv:
        # the scaling data (OpenFHE's factor bookkeeping, read by the user-level decryption check)
        # must name this program's inputs: factor 1 for each, no adjustments
        d["scaling"]["inputFactors"] = [{"name": x["name"], "factor": 1} for x in inputs]
        d["scaling"]["adjustments"] = []
        if "--adjustments" in sys.argv:
            # every constant multiplication is declared a scale adjustment: this exercises the
            # decoder's validation of `$.scaling.adjustments` (real OpenFHE extractions have
            # one for about every ninth instruction)
            d["scaling"]["adjustments"] = [i for i, ins in enumerate(body) if ins["op"] == "mulConst"]
    for key in ("provenance", "crossCheck"):
        d.pop(key, None)
    if bfv:
        # the technique's declared internal drops refer to the original program
        m = d.get("bfv", {}).get("multiplication", {})
        for key in ("maxInternalDrop", "maxInternalDropKeySwitch", "maxInternalDropKS"):
            if key in m:
                m[key] = 0
        if "internalDrops" in m or m.get("technique") == "HPSPOVERQLEVELED":
            m["internalDrops"] = [0] * len(body)
    json.dump(d, open(out, "w"), separators=(",", ":"))


main()
