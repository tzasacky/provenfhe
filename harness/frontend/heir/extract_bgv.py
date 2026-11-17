#!/usr/bin/env python3
"""UNTRUSTED HEIR frontend for fhe_check: HEIR `bgv`-dialect MLIR (Lattigo backend) -> fhe-check/v1.

Reads the textual output of
  heir-opt --annotate-module="backend=lattigo scheme=bgv" --mlir-to-bgv=... prog.mlir
(the layer where every ciphertext type names its RNS modulus chain and `current` index, and the
module carries `bgv.schemeParam` with the actual primes Q, P). Only the OpenFHE-free Lattigo path
is supported: on the OpenFHE path HEIR drops the Q chain and OpenFHE picks its own primes
(use the OpenFHE frontend for those programs).

Supported ops: bgv.add, bgv.sub, bgv.mul, bgv.relinearize (3 -> 2 parts), bgv.modulus_switch,
bgv.negate, bgv.rotate_cols {static_shift = k} (-> automorph 5^k mod 2N ; keySwitch, the Galois
element HEIR's Lattigo ConfigureCryptoContext uses), tensor.extract / tensor.insert /
tensor.from_elements of 1-element ciphertext tensors (aliases). bgv.add_plain / sub_plain /
mul_plain become addPlain / subPlain / mulPlain with the plaintext as a one-component input at
the ciphertext's level and declared bound t - 1 (Lattigo lifts plaintexts to [0, t)); bgv.level_reduce
becomes dropLimbs.
Anything else that produces a ciphertext (rotate_rows, dynamic shifts) makes the extraction fail
with a message naming the op.

Fresh-noise and key-noise bounds are NOT in HEIR's output; they depend on the runtime (Lattigo
v6.1.0, pinned by HEIR's go.mod). The constants and formulas, with Lattigo file:line, are in
`noiseDerivation` of the output and in harness/frontend/README.md ("Constants").
"""
import json
import re
import sys

BE_LATTIGO = 19


def find_psi(q, N):
    """A primitive 2N-th root of unity mod q (untrusted; fhe_check verifies psi^N = -1)."""
    if (q - 1) % (2 * N):
        return None
    for x in range(2, 10000):
        y = pow(x, (q - 1) // (2 * N), q)
        if pow(y, N, q) == q - 1:
            return y
    return None

def parse(text):
    sp = re.search(r"bgv\.schemeParam\s*=\s*#bgv\.scheme_param<([^>]*)>", text)
    if not sp:
        raise SystemExit("no bgv.schemeParam (OpenFHE path? use backend=lattigo)")
    body = sp.group(1)
    logN = int(re.search(r"logN\s*=\s*(\d+)", body).group(1))
    Q = [int(x) for x in re.search(r"Q\s*=\s*\[([^\]]*)\]", body).group(1).split(",")]
    P = [int(x) for x in re.search(r"P\s*=\s*\[([^\]]*)\]", body).group(1).split(",")]
    t = int(re.search(r"plaintextModulus\s*=\s*(\d+)", body).group(1))
    enc = re.search(r"encryptionTechnique\s*=\s*(\w+)", body)
    enc = enc.group(1) if enc else "standard"

    chains = {m.group(1): int(m.group(2)) for m in re.finditer(
        r"^(#modulus_chain\w*)\s*=\s*#lwe\.modulus_chain<.*current\s*=\s*(\d+)>", text, re.M)}
    spaces = {}
    for m in re.finditer(r"^(#ciphertext_space\w*)\s*=\s*#lwe\.ciphertext_space<(.*)>$", text, re.M):
        s = re.search(r"size\s*=\s*(\d+)", m.group(2))
        spaces[m.group(1)] = int(s.group(1)) if s else 2
    cttypes = {}
    for m in re.finditer(r"^(!ct\w*)\s*=\s*!lwe\.lwe_ciphertext<(.*)>$", text, re.M):
        cs = re.search(r"ciphertext_space\s*=\s*(#\w+)", m.group(2)).group(1)
        mc = re.search(r"modulus_chain\s*=\s*(#\w+)", m.group(2)).group(1)
        cttypes[m.group(1)] = {"parts": spaces[cs], "level": chains[mc] + 1}
    return {"logN": logN, "Q": Q, "P": P, "t": t, "enc": enc}, cttypes


def extract(text):
    prm, cttypes = parse(text)
    N = 2 ** prm["logN"]
    alias, inputs, body, consumed = {}, [], [], set()
    level_of, heir_bound = {}, {}

    def ct_of(ty):
        m = re.search(r"(!ct\w*)", ty)
        return cttypes.get(m.group(1)) if m else None

    def r(x):
        return alias.get(x, x)

    funcs = list(re.finditer(r"func\.func @(\w+)\((.*?)\)\s*->", text))
    main = [f for f in funcs if f.group(1).endswith("__preprocessed")] or \
        [f for f in funcs if "__" not in f.group(1)]
    if len(main) != 1:
        raise SystemExit(f"expected one non-helper function, found {[f.group(1) for f in funcs]}")
    for m in re.finditer(r"(%\w+):\s*tensor<1x(!ct\w*)>|(%\w+):\s*(!ct\w*)", main[0].group(2)):
        name, ty = (m.group(1), m.group(2)) if m.group(1) else (m.group(3), m.group(4))
        c = cttypes[ty]
        inputs.append({"name": name, "parts": c["parts"], "level": c["level"], "key": 1})
        level_of[name] = c["level"]
    start = main[0].end()
    nxt = text.find("func.func", start)
    consts = {}
    for line in text[start:nxt if nxt >= 0 else None].splitlines():
        line = line.strip()
        if line.startswith("}") and "func" not in line and not line.startswith("})"):
            pass
        m = re.match(r"(%[\w#]+)\s*=\s*([\w.]+)\s+(.*)$", line)
        if not m:
            continue
        dst, op, rest = m.group(1), m.group(2), m.group(3)
        cm = re.match(r"(-?\d+) : index", rest)
        if op == "arith.constant" and cm:
            consts[dst] = int(cm.group(1))
            continue
        operands = re.findall(r"%[\w#]+", rest.split(":")[0].split("{")[0].split("<")[0])
        if op == "tensor.extract":
            alias[dst] = r(operands[0])
            continue
        if op == "tensor.insert":
            alias[dst] = r(operands[0])
            continue
        if op == "tensor.from_elements" and len(operands) == 1:
            alias[dst] = r(operands[0])
            continue
        if not op.startswith("bgv."):
            continue
        res_ty = rest.rsplit("->", 1)[-1] if "->" in rest else rest.rsplit(":", 1)[-1]
        opnds = [r(o) for o in operands]
        consumed.update(opnds)
        kind = op[4:]
        if kind in ("add_plain", "sub_plain", "mul_plain"):
            # functional type `(T1, T2) -> T3`: which operand is the plaintext
            tys = re.search(r":\s*\(([^)]*)\)\s*->", rest)
            tys = [x.strip() for x in tys.group(1).split(",")] if tys else []
            if len(tys) != 2 or len(opnds) != 2:
                raise SystemExit(f"cannot read operand types of {op}: {line}")
            ci = 0 if tys[0].startswith("!ct") else 1
            ct, pt = opnds[ci], opnds[1 - ci]
            if not tys[1 - ci].startswith("!pt"):
                raise SystemExit(f"{op} without a plaintext operand: {line}")
            lvl = level_of.get(ct)
            if lvl is None:
                raise SystemExit(f"{op}: level of {ct} unknown: {line}")
            pname = f"{pt}@L{lvl}"
            if not any(i["name"] == pname for i in inputs):
                inputs.append({"name": pname, "parts": 1, "level": lvl, "key": 1,
                               "bound": str(prm["t"] - 1)})
            if kind == "sub_plain" and ci == 1:
                # plaintext - ciphertext: HEIR's --scheme-to-lattigo lowers it to
                # lattigo.rlwe.negate_new(ct) then lattigo.bgv.add(neg, pt); mapped the same way
                # (negate = multiply every component by -1: the noise bound is unchanged).
                mid = dst + "@neg"
                body.append({"op": "negate", "dst": mid, "a": ct})
                level_of[mid] = lvl
                body.append({"op": "addPlain", "dst": dst, "a": mid, "p": pname})
            else:
                body.append({"op": {"add_plain": "addPlain", "sub_plain": "subPlain",
                                    "mul_plain": "mulPlain"}[kind], "dst": dst, "a": ct, "p": pname})
        elif kind == "level_reduce":
            k = re.search(r"levelToDrop\s*=\s*(\d+)", rest)
            body.append({"op": "dropLimbs", "dst": dst, "a": opnds[0], "k": int(k.group(1)) if k else 1})
        elif kind in ("add", "sub", "mul"):
            body.append({"op": kind, "dst": dst, "a": opnds[0], "b": opnds[1]})
        elif kind == "relinearize":
            if "from_basis = [0, 1, 2]" not in rest:
                raise SystemExit(f"relinearize other than 3 -> 2 parts: {line}")
            body.append({"op": "relin", "dst": dst, "a": opnds[0]})
        elif kind == "modulus_switch":
            body.append({"op": "modSwitch", "dst": dst, "a": opnds[0]})
        elif kind == "negate":
            body.append({"op": "mulConst", "dst": dst, "a": opnds[0], "c": "-1"})
        elif kind == "rotate_cols":
            k = re.search(r"static_shift\s*=\s*(-?\d+)", rest)
            if k:
                k = int(k.group(1))
            elif len(operands) == 2 and operands[1] in consts:
                k = consts[operands[1]]  # shift given by an arith.constant index
                opnds = opnds[:1]
            else:
                raise SystemExit(f"dynamic rotation not supported: {line}")
            k = k % (N // 2)
            g = pow(5, k, 2 * N)
            mid = dst + "@auto"
            body.append({"op": "automorph", "dst": mid, "a": opnds[0], "g": g})
            body.append({"op": "keySwitch", "dst": dst, "a": mid})
        else:
            raise SystemExit(f"unsupported HEIR op {op}: {line}")
        c = ct_of(res_ty)
        if c is not None:
            body[-1]["expect"] = c  # HEIR's own level/parts; the checker re-derives and compares
            level_of[body[-1]["dst"]] = c["level"]
            if body[-1]["dst"] != dst:
                level_of[dst] = c["level"]
        nb = re.search(r'noise\.bound\s*=\s*"([0-9.]+)"', rest)
        if nb:
            heir_bound[dst] = float(nb.group(1))
    outputs = [i["dst"] for i in body if i["dst"] not in consumed and not i["dst"].endswith(("@auto", "@neg"))]
    t = prm["t"]
    Bs = 1
    Be = BE_LATTIGO
    if prm["P"]:
        # Lattigo v6.1.0 always encrypts modulo Q*p0 and divides by p0 (centred) when P exists,
        # whatever HEIR's encryptionTechnique says (core/rlwe/encryptor.go:172-175,205-260). MSB form:
        # e_fresh = (u*e_pk + e0 + e1*s - rho0 - rho1*s)/p0 with |rho| <= (p0-1)/2, an integer, so
        # |e_fresh| <= floor((2*Be*(2N+1) + (N+1)*(p0-1)) / (2*p0)). LSB view: Phi = m + t*e_fresh
        # with m in [0, t) (encoder.go:218-222,361: canonical lift).
        p0 = prm["P"][0]
        ef = (2 * Be * (2 * N + 1) + (N + 1) * (p0 - 1)) // (2 * p0)
        inputNoise = (t - 1) + t * ef
        enc_note = (f"(t-1) + t*floor((2*Be*(2N+1) + (N+1)*(p0-1))/(2*p0)) with p0 = {p0}: Lattigo public-key "
                    "encryption mod Q*p0 then centred division by p0 (encryptor.go:172-260); m lifted to [0,t) (encoder.go:218-222,361)")
    else:
        inputNoise = (t - 1) + t * Be * (1 + 2 * N * Bs)
        enc_note = "(t-1) + t*Be*(1+2N*Bs): Lattigo public-key encryption without P (encryptor.go:287-327)"
    outs_heir = {o: heir_bound.get(o) for o in outputs}
    return {
        "format": "fhe-check/v1",
        "source": {"tool": "heir", "backend": "lattigo", "lattigo": "v6.1.0",
                   "encryptionTechnique": prm["enc"],
                   "heirNoiseBoundLog2": outs_heir,
                   "note": "heirNoiseBoundLog2 is HEIR's own noise.bound annotation (its model), informational"},
        "params": {
            "scheme": "BGV", "N": N, "t": t,
            "limbs": [{"q": str(q), "psi": str(find_psi(q, N))} for q in prm["Q"]],
            "special": [{"q": str(q), "psi": str(find_psi(q, N))} for q in prm["P"]],
            "secretBound": Bs,
            "inputNoise": str(inputNoise),
            "keyNoise": str(t * Be),
        },
        "noiseDerivation": {
            "errorBound": Be,
            "errorBoundSource": "Lattigo v6.1.0 DefaultXe: sigma 3.2, Bound 19.2 (core/rlwe/security.go:10-17), hard rejection v <= 19.2 then rounding, so |e| <= 19 (ring/sampler_gaussian.go:160-166); HEIR emits no Xe/Xs (LattigoEmitter.cpp:1992-2010)",
            "secret": "ternary, density 2/3 (security.go:19; sampler_ternary.go:32-37): |s_i| <= 1",
            "msbForm": "Lattigo BGV keeps ct phase = m*t^-1 + e (encoder.go:376-377); all bounds here are for the LSB view Phi = t*phase = m + t*e",
            "inputNoiseFormula": enc_note,
            "keyNoiseFormula": "t*Be: Lattigo keys carry plain e in MSB form (keygenerator.go:296-310), i.e. t*e in the LSB view",
            "keySwitchingVariant": "centred: Lattigo ModUp is exact and centred (|d_j| <= Q_j/2, ring/basis_extension.go:401-435,498-525) and ModDown is an exact centred rounding (|r| <= 1/2, basis_extension.go:222-256); so its LSB-view error, at most t*(N*Be*sum_j Q_j/2 + P*(1+N)/2)/P, is below the centred reference bound ksBoundAt and hence below the canonical one used here (ASSUMED match, argued from source, not proved)",
            "modSwitch": "Lattigo Rescale = DivRoundByLastModulusNTT, centred (schemes/bgv/evaluator.go:1436-1443, ring/scaling.go:99-107)",
            "plaintextBound": "t-1 (canonical [0,t) lift)",
        },
        # Lattigo's ModUp/ModDown are exact and centred (see keySwitchingVariant above), so the
        # centred layout would do; the canonical budget is never smaller
        # (Challenge.Budget.ksBoundAt_le_canonical) and is the project's conservative default.
        "keySwitching": {"method": "hybrid", "variant": "canonical",
                         # Lattigo core/rlwe/params.go:541-548: digits are groups of |P| consecutive Q primes
                         "digits": {"kind": "consecutive",
                                    "towersPerDigit": max(1, len(prm["P"])),
                                    "dnum": -(-len(prm["Q"]) // max(1, len(prm["P"])))}},
        "modSwitch": {"method": "t-corrected-centred"},
        "program": {"inputs": inputs, "body": body, "outputs": outputs},
    }


if __name__ == "__main__":
    json.dump(extract(open(sys.argv[1]).read()), sys.stdout, indent=1)
    print()
