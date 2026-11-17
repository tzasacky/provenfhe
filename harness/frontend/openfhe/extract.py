#!/usr/bin/env python3
"""UNTRUSTED OpenFHE frontend for fhe_check: OpenFHE BGVrns artifacts -> neutral JSON (fhe-check/v1).

Supported library: upstream OpenFHE v1.6.1 (openfheorg/openfhe-development b59e1f29) with
openfhe/openfhe-v1.6.1-tracer.patch and openfhe/fhecheck-tracer.h (observation hooks only; build
with openfhe/build_openfhe.sh). File:line references below are to that version.

Inputs
  --params params.json   fields of a BGVrns CryptoContext, as printed by `bgv_demo dump cc.json`
                         (or `bgv_demo run`, or the tracer's FHECHECK_TRACE_DIR mode)
  --trace  trace.jsonl   JSON-lines trace from fhecheck-tracer.h (OpenFHE's ENABLE_TRACER hooks).
                         Read as a stream: each top-level call is translated when it ends and then
                         dropped, so traces of several GB need memory for the program only.
  --outputs a,b          optional: output ciphertext ids (default: see "Outputs" below); must
                         include every ciphertext the trace decrypts
  --outputs-from-decrypt outputs = exactly the ciphertexts the program passes to a traced Decrypt
  --no-decrypt-switch    declare textbook decryption at the output's level instead of OpenFHE's
                         Decrypt, which switches the phase to one limb (see below)
  --assume-fresh-inputs  for traces that start after encryption: a 2-part ciphertext that no
                         traced operation produced is taken as a FRESH public-key encryption
                         (an assumption the report prints). Without it such a ciphertext is an
                         extraction error. Only INPUTS can be assumed fresh: the ciphertext must
                         be used before the first traced operation produces a ciphertext, and the
                         trace must contain no traced Encrypt (a trace that starts before
                         encryption has its inputs' encryptions; a traced KeyGen is allowed: keys
                         generated under the trace, inputs built or deserialized outside it, as
                         harness/openfhe-pin's hand-built inputs are); otherwise a ciphertext
                         changed by an untraced call in the middle of the program (it has a new
                         content id) would pass as a fresh encryption. Refused otherwise.
  --assume-single-party-keys
                         for traces that do not contain the key generation (e.g. keys
                         deserialized from another process): skip the key-provenance check and
                         state, as an assumption in the file, that every key is a single-party
                         key of one secret. Without it a key whose generation is not in the
                         trace is an extraction error.
  --cse                  merge instructions that are exact duplicates (same op, operands and
                         constants); see `cse` below for why this cannot change a verdict.
  --compact              write the JSON without indentation (large programs).
  --allow-truncated      for the trace of a run that was killed: extract the top-level calls that
                         completed (a PREFIX of the program; the file says so in crossCheck).
  --assume-default-build for params.json written by an older tracer without the "build" section:
                         ASSUME WITH_REDUCED_NOISE=OFF and NATIVEINT=64 (stated in the file).
  --no-provenance        omit the per-instruction provenance list (it is about half of a large file).

Key provenance (soundness of the noise constants). noise_inputs() declares the constants of a
SINGLE-PARTY key: secret ternary (|s| <= 1), key error t*e with |e| <= 39. They are wrong for a
threshold/multiparty key (joint secret = sum of the parties' secrets, joint key error = sum of
their errors), for proxy re-encryption and for key switching to another key. So the extractor
requires, from the trace:
  - every Encrypt uses a public key output by a traced single-party CryptoContext::KeyGen();
  - every relinearization key used was output by a traced EvalMultKeyGen/EvalMultKeysGen of that
    KeyGen's secret key (for the right power of s), and every rotation key used by
    EvalAutomorphism with index g was generated FOR g from that secret;
  - one secret key for the whole program;
  - no multiparty, proxy re-encryption, key-switch-between-keys or sparse-key call anywhere.
A key that the trace does not show being generated this way (deserialized, inserted, produced by
a multiparty protocol) makes the extraction fail, naming the call. Encrypt with a PRIVATE key
(symmetric encryption, rns-pke.cpp:45-59,115-150: c = (a*s + t*e + m, -a), phase m + t*e) is
declared as a 2-part input WITH a bound (t-1) + t*Be: a worst-case assumption derived from the
source; it is not a fresh public-key encryption, so it is not listed in freshEncryption and
`fhe_check --kappa` answers UNSUPPORTED for such programs (no probabilistic theorem covers it).

All four BGV scaling techniques (FIXEDMANUAL, FIXEDAUTO, FLEXIBLEAUTO, FLEXIBLEAUTOEXT) are
handled the same way: every OpenFHE function that changes a ciphertext's polynomials is traced
(ModReduceInternalInPlace, LevelReduceInternalInPlace, EvalMultCoreInPlace with a NativeInteger,
EvalAddCore/EvalSubCore/EvalMultCore, EvalAutomorphism, EvalMultNoRelinNoCheck); the automatic
modes call them from AdjustLevelsAndDepth*InPlace / EvalSquare, and the walk below translates
them wherever they occur. Untraced cores (EvalSquareCore, the element-level core of a plaintext
operation, KeySwitchCore inside EvalMult) are recognised by their traced wrappers.

Outputs and Decrypt (what is certified is what the program decrypts). Every ciphertext passed to a
traced CryptoContext::Decrypt must be a value of the extracted program (a traced Encrypt output or
the result of a traced operation): its id is its content identity at the time of the Decrypt
(fhecheck-tracer.h recomputes it at every traced use), so a ciphertext changed after the last
traced operation by any call outside the traced API (EvalAddInPlaceNoCheck, EvalMultNoCheck,
GetElements()/SetElements(), SetLevel, SetNoiseScaleDeg, a serialization round trip, ...) has an
id no traced operation produced, and the extraction FAILS. The outputs are the ciphertexts no
instruction consumes PLUS every decrypted one (a superset: every decrypted ciphertext is
certified); with --outputs-from-decrypt exactly the decrypted ones; --outputs must include every
decrypted one. The decryption key must be the program's secret (key provenance). A trace without
a traced Decrypt (bgv_demo, which decrypts with the tracer switched off) certifies the
never-consumed values; crossCheck.outputs says which rule applied.

Plaintext operands (and encrypted plaintexts) must be outputs of a traced CryptoContext::Make*
call of the same trace (one trace per context: the same context), identified by content, so a
plaintext whose element was changed after encoding (GetElement<DCRTPoly>() is a mutable
reference) or one made by another context is refused; the plaintext modulus the tracer records
with it ("t") must be the context's.

Ciphertext inputs come only from traced CryptoContext::Encrypt outputs (or --assume-fresh-inputs):
a ciphertext id that no recognised operation produced makes the extraction fail, so an untraced
mutation (e.g. third-party code multiplying ciphertext components directly) cannot be certified
as a fresh encryption. Calls that are known not to be modelled are refused by name with a
specific message (EvalSum/EvalInnerProduct: v1.6 fuses the rotations, base-advancedshe.cpp:514-637;
EvalFastRotation; the *Mutable ciphertext products; multiparty; PRE; key switching).

Nothing here is trusted: a wrong translation can only make fhe_check certify a different
program than the one OpenFHE ran; the provenance list ties every emitted op to a trace line,
and two cross-checks (scale factors and levels here; plaintext values in value_check.py) test
the translation against OpenFHE's own run.
"""
import argparse
import hashlib
import json
import math
import os
import re
import struct
import sys

OPENFHE_VERSION = ("openfheorg/openfhe-development v1.6.1 (b59e1f291965f14fbee5172cd83a20f5b856204f) + "
                   "harness/frontend/openfhe/openfhe-v1.6.1-tracer.patch, WITH_REDUCED_NOISE=OFF")

# Tracer version (fhecheck-tracer.h, "Tracer version"): params.json records "tracer" =
# FHECHECK_TRACER_VERSION of the header OpenFHE was built with; it must be the version of the
# canonical header next to this file, which is the SHA-256 of that header with the 64 hex digits
# of its #define replaced by '0's (so the version follows the content). params.json without a
# "tracer" field (traces committed before the field existed, or a stale install) is accepted only
# if the SHA-256 pair (params.json bytes, trace bytes) is listed in legacy-traces.tsv (generated
# by tracer_version.py --allowlist from the committed traces).
HERE = os.path.dirname(os.path.abspath(__file__))
TRACER_HEADER = os.path.join(HERE, "fhecheck-tracer.h")
LEGACY_TRACES = os.path.join(HERE, "legacy-traces.tsv")
TRACER_VERSION_RE = re.compile(rb'#define FHECHECK_TRACER_VERSION "([0-9a-f]{64})"')
REBUILD = "rebuild OpenFHE with harness/frontend/openfhe/build_openfhe.sh and re-run the program"


def tracer_header_version(path=TRACER_HEADER):
    """(declared, computed): the FHECHECK_TRACER_VERSION the header declares, and the SHA-256 of the
    header with that value replaced by 64 '0's (what the declared value must be)."""
    data = open(path, "rb").read()
    ms = TRACER_VERSION_RE.findall(data)
    if len(ms) != 1:
        raise Fail(f"{path}: expected exactly one #define FHECHECK_TRACER_VERSION \"<64 hex digits>\"")
    norm = TRACER_VERSION_RE.sub(b'#define FHECHECK_TRACER_VERSION "' + b"0" * 64 + b'"', data)
    return ms[0].decode(), hashlib.sha256(norm).hexdigest()


def current_tracer_version():
    return tracer_header_version()[1]


def stamp_tracer(p):
    """params.json fields `p` as the CURRENT tracer writes them: for tests that derive a params.json /
    trace from a committed one and want the extractor's answer on the derived input itself."""
    return dict(p, tracer=current_tracer_version())


def file_sha256(path):
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for chunk in iter(lambda: f.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def legacy_pairs(path=LEGACY_TRACES):
    pairs = set()
    if os.path.exists(path):
        for line in open(path):
            if line.strip() and not line.startswith("#"):
                ps, ts = line.split("\t")[:2]
                pairs.add((ps, ts))
    return pairs


def check_tracer(params_path, trace_path, p):
    """Refuse a trace not written by the current fhecheck-tracer.h (shared by extract_bfv.py)."""
    try:
        _, cur = tracer_header_version()
    except OSError as e:
        raise Fail(f"cannot read the canonical tracer header {TRACER_HEADER} ({e}); the tracer version of the "
                   "trace cannot be checked")
    rec = p.get("tracer") if isinstance(p, dict) else None
    if rec is None:
        if (file_sha256(params_path), file_sha256(trace_path)) in legacy_pairs():
            return
        raise Fail("trace written by a different fhecheck tracer (params.json records no tracer version: an "
                   f"OpenFHE built with an older fhecheck-tracer.h; current {cur}): {REBUILD}")
    if rec != cur:
        raise Fail(f"trace written by a different fhecheck tracer (recorded {rec}, current {cur}; the installed "
                   f"fhecheck-tracer.h is not harness/frontend/openfhe/fhecheck-tracer.h): {REBUILD}")

# OpenFHE's discrete Gaussian sampler for sigma < 300 (Peikert inversion,
# src/core/include/math/discretegaussiangenerator-impl.h:81-82 table, :94-99 throw) only returns
# values with |e| <= ceil(sigma * 12.00610553538285), and throws otherwise.
DGG_TAIL = 12.00610553538285

# OpenFHE's BGV ModReduce (dcrtpoly-impl.h:786-805) adds t*delta with delta = [-c*t^-1]_q switched
# to a centred representative, so the switch is the one of Challenge.Trace.stepOK_modSwitch_textbook.
MODSWITCH_METHOD = "t-corrected-centred"

# The sampler mean declared in freshEncryption.mean (an ASSUMPTION of `fhe_check --kappa`): a bound
# on the absolute value of the mean of every coefficient of the encryption randomness (u, e1, e2)
# = OpenFHE's (v, e0, e1). The tool declares |mean| <= 3431/2^64 for every coefficient: this is
# the tool's declared assumption for the discrete Gaussian generator at sigma = 3.19f (and mean 0
# for the ternary generator, std::uniform_int_distribution<int32_t>(-1, 1)), not something
# fhe_check checks. The figure is declared for sigma = 3.19f only: noise_inputs refuses any other
# sigma.
DGG_SIGMA = 3.19
DGG_MEAN_NUM, DGG_MEAN_DEN = 3431, 2 ** 64
DGG_MEAN_SOURCE = ("declared assumption for the sigma = 3.19 encryption sampler: |mean| <= 3431/2^64 for every coefficient of "
                   "(u, e1, e2) = OpenFHE's (v, e0, e1), support -27..26; ternary sampler uniform on {-1, 0, 1} (mean 0)")

SCALINGS = ("FIXEDMANUAL", "FIXEDAUTO", "FLEXIBLEAUTO", "FLEXIBLEAUTOEXT")

# Calls whose presence means the keys or ciphertexts are not those of the single-party model
# (prefix match on the traced function name).
KEY_MODEL_CALLS = ("CryptoContext::Multi",  # MultipartyKeyGen/Decrypt*, MultiAdd*, MultiKeySwitchGen, MultiEval*, ...
                   "CryptoContext::ReKeyGen", "CryptoContext::ReEncrypt", "CryptoContext::IntBoot",
                   "CryptoContext::IntMPBoot", "CryptoContext::KeySwitchGen", "CryptoContext::KeySwitch(",
                   "CryptoContext::KeySwitchInPlace", "CryptoContext::KeySwitchDown", "CryptoContext::KeySwitchExt",
                   "CryptoContext::SparseKeyGen")
# Calls that compute ciphertexts by a method this extractor does not model.
UNMODELLED_CALLS = {
    "CryptoContext::EvalSum": "EvalSum / EvalSumRows / EvalSumCols: OpenFHE >= 1.6 computes the rotation sum as a "
                              "fused radix fold with hoisted key switching and one ModDown per level "
                              "(base-advancedshe.cpp:514-637), which is not a sequence of the operations fhe_check "
                              "certifies; write the sum with EvalRotate/EvalAtIndex and EvalAdd instead",
    "CryptoContext::EvalInnerProduct": "EvalInnerProduct calls EvalSum (fused radix fold, base-advancedshe.cpp:514-637), "
                                       "not modelled; write it with EvalMult, EvalRotate/EvalAtIndex and EvalAdd",
    "CryptoContext::EvalFastRotation": "EvalFastRotation / EvalFastRotationExt (hoisted rotation with precomputed digits) "
                                       "is not mapped; use EvalRotate/EvalAtIndex",
    "CryptoContext::EvalMultMutable": "EvalMultMutable / EvalMultMutableInPlace run untraced cores in v1.6.1; not mapped",
    "CryptoContext::EvalSquareMutable": "EvalSquareMutable runs untraced cores; not mapped",
    "CryptoContext::Compress": "Compress is not mapped",
    "CryptoContext::EvalMerge": "EvalMerge uses EvalSum-style rotations; not mapped",
}


class Fail(Exception):
    pass


def check_build(p, assume_build):
    """The build options recorded by fhecheck-tracer.h (params.json "build") that change OpenFHE's
    arithmetic: only the default build is mapped (shared by extract_bfv.py)."""
    build = p.get("build")
    if build is None:
        if not assume_build:
            raise Fail("params.json has no \"build\" section (a tracer older than fhecheck-tracer.h of "
                       "harness/frontend/openfhe): the build options that change OpenFHE's arithmetic are unknown; "
                       "re-run with the current tracer, or pass --assume-default-build to ASSUME "
                       "WITH_REDUCED_NOISE=OFF and NATIVEINT=64")
    else:
        if build.get("WITH_REDUCED_NOISE"):
            raise Fail("OpenFHE built WITH_REDUCED_NOISE: its hybrid key switching uses a centred base "
                       "conversion and halves the noise estimates; the extractor's declarations (canonical "
                       "ModUp, keySwitchBGVOpenFHE_spec) describe the default build only")
        if build.get("HAVE_INT128") is False:
            raise Fail("OpenFHE built without HAVE_INT128: ApproxSwitchCRTBasis takes another code path "
                       "(dcrtpoly-impl.h:943-946) that this extractor's declarations were not checked against")
        if int(build.get("NATIVEINT", 0)) != 64:
            raise Fail(f"OpenFHE built with NATIVEINT={build.get('NATIVEINT')}: only the default 64-bit native "
                       "integers are mapped")


def noise_inputs(p, assume_keys, assume_build=False):
    """ASSUMED noise bounds, from OpenFHE v1.6.1 source (README "Constants")."""
    N, t = p["N"], p["t"]
    if p["secretKeyDist"] not in ("UNIFORM_TERNARY", "SPARSE_TERNARY"):
        raise Fail(f"secret distribution {p['secretKeyDist']}: only UNIFORM_TERNARY and SPARSE_TERNARY secrets are "
                   "mapped (Bs = 1)")
    check_build(p, assume_build)
    if p["scaling"] not in SCALINGS:
        raise Fail(f"scaling technique {p['scaling']}: not a BGV technique this extractor maps")
    if p["scaling"] in ("FIXEDMANUAL", "FIXEDAUTO"):
        # The fixed techniques keep scalingFactorInt = 1 and rely on every prime being 1 mod t (a
        # modulus switch, also the one inside Decrypt, multiplies the message by q^-1 mod t). A context
        # whose primes are not all 1 mod t is outside what this technique's analysis assumes: refused.
        bad = [x["q"] for x in p["qs"] if int(x["q"]) % t != 1]
        if bad:
            raise Fail(f"{p['scaling']} context whose primes are not 1 mod t = {t} ({len(bad)} of {len(p['qs'])}, e.g. "
                       f"{bad[0]}): the technique assumes q = 1 mod t "
                       "for every prime, and fhe_check covers it only then; refused")
    if p.get("encryptionTechnique", "STANDARD") != "STANDARD":
        raise Fail("encryption technique EXTENDED (BFV only) is not mapped")
    if "noiseScale" in p and int(p["noiseScale"]) != t:
        raise Fail(f"noiseScale {p['noiseScale']} != t: the encryption noise is not t*e "
                   "(gen-cryptocontext-bgvrns-internal.h:97 sets it to t)")
    sigma = float(p["sigma"])
    if sigma >= 300:
        raise Fail("sigma >= 300 uses Karney sampling, which has no hard tail cut")
    sigma = struct.unpack("f", struct.pack("f", sigma))[0]  # OpenFHE stores sigma as float
    if sigma != struct.unpack("f", struct.pack("f", DGG_SIGMA))[0]:
        raise Fail(f"sigma = {p['sigma']}: the declared sampler mean applies to sigma = 3.19 only (OpenFHE's default, "
                   "3.19f), so no bound on the mean of the "
                   "encryption errors can be declared for this context (freshEncryption.mean)")
    Be = int(math.ceil(sigma * DGG_TAIL))
    Bs = 1
    # Public-key BGV encryption (rns-pke.cpp:61-75, 152-199): c = v*pk + t*(e0, e1) + m, v ternary,
    # pk error t*e. Phase m + t*(v*e + e0 + e1*s). The same for every scaling technique: the
    # scaling factor is applied to the slot values mod t BEFORE the inverse NTT and the lift to
    # [0, t) (packedencoding.cpp:66-69, 79-90, 119), so |m| <= t - 1 still. FLEXIBLEAUTOEXT
    # encrypts at all L+1 towers (cryptocontext.h:185-212: level 0 = the full chain incl. the
    # extra prime); the input is declared there and the reduction that drops the extra prime is
    # an extracted modSwitch, analysed by fhe_check.
    inputNoise = (t - 1) + t * Be * (1 + 2 * N * Bs)
    keyNoise = t * Be  # keyswitch-hybrid.cpp:104-128: b = -a*s' + t*e (+ P*s on the digit)
    return {
        "errorBound": Be,
        "secretBound": Bs,
        "inputNoise": inputNoise,
        "symmetricInputNoise": (t - 1) + t * Be,
        "keyNoise": keyNoise,
        "plaintextBound": t - 1,
        "derivation": {
            "errorBound": Be,
            "errorBoundSource": f"OpenFHE DGG (Peikert inversion): sigma = 3.19f, |e| <= ceil(sigma*{DGG_TAIL}) = {Be}, "
                                "else OPENFHE_THROW (discretegaussiangenerator-impl.h:81-82,94-99)",
            "inputNoiseFormula": "(t-1) + t*Be*(1 + 2*N*Bs): public-key encryption, v ternary, packed plaintext "
                                 "(scaled mod t) lifted to [0,t) (rns-pke.cpp:61-75,152-199; packedencoding.cpp:66-119)",
            "symmetricInputNoiseFormula": "(t-1) + t*Be: Encrypt with a private key, c = (a*s + t*e + m, -a) "
                                          "(cryptocontext.h:1419-1436; rns-pke.cpp:45-59,115-150); declared as the "
                                          "input's own bound",
            "keyNoiseFormula": "t*Be (keyswitch-hybrid.cpp:104-128)",
            "secret": ("SPARSE_TERNARY: s has 192 nonzero coefficients in {-1, 1} (base-pke.cpp:69-73; "
                       "ternaryuniformgenerator-impl.h:76-107), so |s| <= 1; the encryption ephemeral v is still "
                       "uniform ternary for every non-GAUSSIAN secret (rns-pke.cpp:168-169)"
                       if p["secretKeyDist"] == "SPARSE_TERNARY" else
                       "UNIFORM_TERNARY (base-pke.cpp:66-67)"),
            "build": (p.get("build") or "ASSUMED (--assume-default-build): WITH_REDUCED_NOISE=OFF, NATIVEINT=64"),
            "keyProvenance": ("ASSUMED (--assume-single-party-keys): every key is a single-party key of one ternary "
                              "secret generated by KeyGen/EvalMultKeyGen/EvalRotateKeyGen; NOT checked from the trace"
                              if assume_keys else
                              "checked from the trace: every Encrypt key comes from one traced single-party "
                              "CryptoContext::KeyGen(); every relinearization/rotation key used was generated from its "
                              "secret key by a traced EvalMultKeyGen/EvalMultKeysGen/rotation-key generation for the "
                              "index used; no multiparty, proxy re-encryption or key-switching call in the trace"),
            "plaintextBound": "t-1 (packed encoding, scaling factor applied mod t before the lift to [0,t))",
            "scalingTechnique": p["scaling"],
            "openfheVersion": OPENFHE_VERSION,
        },
    }


def stream_calls(path, truncated=None):
    """Yield every top-level call of the trace as a tree {fn, ins, outs, kids, line}, as soon as
    it ends (the trace is never held in memory as a whole). If `truncated` is a list, a trace that
    ends inside a call (a run that was killed) is accepted: the unfinished call is dropped and its
    first line is appended to `truncated`."""
    stack = []
    with open(path) as f:
        for ln, line in enumerate(f, 1):
            line = line.strip()
            if not line:
                continue
            try:
                o = json.loads(line)
            except json.JSONDecodeError:
                if truncated is not None:
                    break  # a run killed in the middle of writing a line
                raise Fail(f"line {ln}: not JSON")
            ev = o["ev"]
            if ev == "begin":
                n = {"fn": o["fn"], "ins": [], "outs": [], "kids": [], "line": ln}
                if stack:
                    stack[-1]["kids"].append(n)
                stack.append(n)
            elif ev == "end":
                if not stack:
                    raise Fail(f"line {ln}: unbalanced trace")
                n = stack.pop()
                if not stack:
                    yield n
            elif ev in ("in", "out"):
                if not stack:
                    raise Fail(f"line {ln}: an input/output record outside any call")
                stack[-1]["ins" if ev == "in" else "outs"].append(o)
            elif ev == "error":
                raise Fail(f"line {ln}: the tracer reported: {o.get('what')}")
            else:
                raise Fail(f"line {ln}: unknown trace event {ev!r}")
    if stack:
        if truncated is None:
            raise Fail("unbalanced trace (a call never ended: truncated trace? --allow-truncated extracts the "
                       "completed calls only)")
        truncated.append(stack[0]["line"])


def scan_refused(node, unmodelled=None):
    """Refuse, by name, calls outside the single-party key model and calls whose method is not
    modelled (`unmodelled`: name prefix -> reason; default UNMODELLED_CALLS, the BGV table)."""
    unmodelled = UNMODELLED_CALLS if unmodelled is None else unmodelled
    for u in KEY_MODEL_CALLS:
        if node["fn"].startswith(u):
            raise Fail(f"line {node['line']}: {node['fn']}: multiparty / proxy re-encryption / key switching to "
                       "another key / sparse key: the keys or ciphertexts are not those of the single-party noise "
                       "model this extractor declares (refused)")
    for u, why in unmodelled.items():
        if node["fn"].startswith(u) and "KeyGen" not in node["fn"]:
            raise Fail(f"line {node['line']}: {node['fn']}: {why}")
    for k in node["kids"]:
        scan_refused(k, unmodelled)


def cts(lst):
    return [o for o in lst if o.get("kind") == "ct"]


def pts_of(lst):
    return [o for o in lst if o.get("kind") == "pt"]


def keys_of(lst, kind):
    return [o for o in lst if o.get("kind") == kind]


def ints(node, name=None):
    return [o["v"] for o in node["ins"] if o.get("kind") == "int" and (name is None or o["name"] == name)]


def base(fn):
    return fn.split("(")[0]


# The innermost traced function of a ciphertext-plaintext operation (rns-leveledshe.cpp:110-127,
# 176-193, 255-279): it morphs the plaintext into a 1-part ciphertext (MorphPlaintext,
# base-leveledshe.cpp:522-535, untraced), aligns both with AdjustFor*InPlace, then applies the
# untraced element-level core; or, when the adjustment would be a no-op, uses the plaintext
# element directly (v1.6 fast path, rns-leveledshe.cpp:47-71).
PLAIN_OPS = {"LeveledSHERNS::EvalAddInPlace": "addPlain", "LeveledSHERNS::EvalSubInPlace": "subPlain",
             "LeveledSHERNS::EvalMultInPlace": "mulPlain", "LeveledSHERNS::EvalAddMutableInPlace": "addPlain",
             "LeveledSHERNS::EvalSubMutableInPlace": "subPlain", "LeveledSHERNS::EvalMultMutableInPlace": "mulPlain"}

RELIN_FNS = ("LeveledSHEBase::EvalMult", "LeveledSHEBase::EvalSquare", "LeveledSHEBase::EvalMultInPlace",
             "LeveledSHEBase::EvalSquareInPlace")
KEYGEN_PK = "CryptoContext::KeyGen"
MULT_KEYGENS = ("CryptoContext::EvalMultKeyGen", "CryptoContext::EvalMultKeysGen")
AUTO_KEYGENS = ("CryptoContext::EvalAtIndexKeyGen", "CryptoContext::EvalAutomorphismKeyGen",
                "CryptoContext::EvalSumKeyGen", "CryptoContext::EvalSumRowsKeyGen", "CryptoContext::EvalSumColsKeyGen",
                "CryptoContext::EvalRotateKeyGen")


class Extractor:
    def __init__(self, t, assume_fresh, assume_keys, sym_bound):
        self.t = t
        self.assume_fresh = assume_fresh
        self.assume_keys = assume_keys
        self.sym_bound = sym_bound
        self.body, self.prov = [], []
        self.defined = {}      # SSA name -> trace record (None for synthetic names)
        # trace id -> the SSA name of its CURRENT value. Trace ids are content hashes, so an id can
        # recur (x*1, a recomputation, a morphed plaintext equal to an earlier one): every traced
        # output gets a fresh SSA name (`id`, `id#1`, ...) and a use refers to the latest one.
        self.cur = {}
        self.inputs, self.order = {}, []
        self.input_sf = {}
        self.root = {}         # value -> the id it was derived from by unary ops (lineage)
        self.ptinfo = {}       # pt id -> trace record (MakePlaintext / Encrypt)
        self.ptmaker = {}      # pt id -> the CryptoContext::Make* call that made it
        self.no_sf_check = set()
        self.decrypted = []    # SSA names of the ciphertexts passed to CryptoContext::Decrypt, in order
        self.line = None       # trace line of the call being walked (messages)
        self.produced = None   # trace line of the first traced call that produced a ciphertext
        self.encrypt_line = None  # trace line of the first traced Encrypt
        self.assumed = []      # ids taken as fresh inputs (--assume-fresh-inputs)
        # key provenance
        self.kg_pk = {}        # pk id -> sk id, from CryptoContext::KeyGen()
        self.kg_sk = set()     # sk ids from CryptoContext::KeyGen()
        self.gen_ek = {}       # ek id -> (kind "mult"|"auto", index, sk id, trace line)
        self.secret = None     # the one secret key id the program uses
        self.key_uses = 0

    # ---- key provenance -------------------------------------------------------------------
    def use_secret(self, sk, line, what):
        if self.assume_keys:
            return
        if sk not in self.kg_sk:
            raise Fail(f"line {line}: {what}: the key does not come from a traced single-party "
                       "CryptoContext::KeyGen() in this trace (multiparty, deserialized or inserted key?); start the "
                       "trace before KeyGen, or pass --assume-single-party-keys to ASSUME it")
        if self.secret is None:
            self.secret = sk
        elif self.secret != sk:
            raise Fail(f"line {line}: {what}: a second secret key ({sk}, besides {self.secret}): the program mixes "
                       "keys, which the single-secret noise model does not cover")

    def check_eval_key(self, node, ek, kind, index):
        """The evaluation key `ek` (a trace record) is used by `node` for `kind` at `index`."""
        self.key_uses += 1
        if self.assume_keys:
            return
        g = self.gen_ek.get(ek["id"])
        what = f"{node['fn']} uses evaluation key {ek['id']}"
        if g is None:
            raise Fail(f"line {node['line']}: {what}, whose generation is not in the trace (deserialized, inserted "
                       "or multiparty key?); generate keys under the trace, or pass --assume-single-party-keys")
        gk, gi, gsk, gl = g
        if gk != kind or gi != index:
            raise Fail(f"line {node['line']}: {what}, generated at line {gl} as a {gk} key for index {gi}, but used "
                       f"as a {kind} key for index {index}")
        self.use_secret(gsk, node["line"], what)

    def record_keys(self, node):
        """Key generation records of one traced call (key provenance)."""
        name = base(node["fn"])
        if name == KEYGEN_PK:
            pks, sks = keys_of(node["outs"], "pk"), keys_of(node["outs"], "sk")
            if len(pks) == 1 and len(sks) == 1:
                self.kg_pk[pks[0]["id"]] = sks[0]["id"]
                self.kg_sk.add(sks[0]["id"])
        elif name in MULT_KEYGENS or name in AUTO_KEYGENS:
            sks = keys_of(node["ins"], "sk")
            sk = sks[0]["id"] if len(sks) == 1 else None
            for o in keys_of(node["outs"], "ek"):
                if sk is None:
                    continue  # a generated key with no recorded secret: never accepted at use
                if name in MULT_KEYGENS:
                    self.gen_ek[o["id"]] = ("mult", o.get("index", 0), sk, node["line"])
                elif "index" in o:
                    self.gen_ek[o["id"]] = ("auto", o["index"], sk, node["line"])
        for k in node["kids"]:
            self.record_keys(k)

    # ---- values ----------------------------------------------------------------------------
    def fresh_shape(self, o):
        """Why a ciphertext cannot be a fresh encryption by its shape (None: it can)."""
        return None if o["parts"] == 2 else f"it has {o['parts']} parts"

    def use(self, o):
        i = self.cur.get(o["id"])
        if i is not None:
            return i
        i = o["id"]
        if self.assume_fresh:
            # Only an INPUT of the program can be assumed fresh: one seen before any traced call
            # produced a ciphertext, in a trace that does not itself encrypt. A value changed by an
            # untraced call in the middle of the program gets a new content id that no traced
            # operation produced, and would otherwise be laundered as a fresh encryption.
            why = self.fresh_shape(o)
            if why is None and self.produced is not None:
                why = (f"it first appears after the traced call at line {self.produced} produced a ciphertext, so it may "
                       "be an intermediate value changed by an untraced call (an input must be used before the first "
                       "traced operation)")
            if why is None and self.encrypt_line is not None:
                why = (f"the trace contains a traced Encrypt (line {self.encrypt_line}), so it starts before "
                       "encryption and its inputs are the traced encryptions")
            if why is not None:
                raise Fail(f"line {self.line}: ciphertext {o['id']} (towers {o['towers']}, parts {o['parts']}, nsd "
                           f"{o['nsd']}) is used but no traced operation produced it, and --assume-fresh-inputs does not "
                           f"apply: {why} (refused)")
            self.assumed.append(i)
            self.inputs[i] = {"name": i, "parts": 2, "level": o["towers"], "key": 1,
                              "origin": {"openfhe": "assumed fresh encryption (--assume-fresh-inputs)"}}
            self.input_sf[i] = int(o["sf"])
            self.order.append(i)
            self.cur[i] = i
            return i
        raise Fail(f"ciphertext {o['id']} (towers {o['towers']}, parts {o['parts']}) is used but no traced "
                   f"operation produced it (start the trace before KeyGen/Encrypt, or pass --assume-fresh-inputs)")

    @staticmethod
    def out(node, outs):
        """The ciphertext a recognised primitive produced. None recorded means the call did not
        return normally (an exception unwound through it): refused, explicitly."""
        if not outs:
            raise Fail(f"line {node['line']}: {node['fn']} recorded no output ciphertext (the call threw, or its "
                       "hook is incomplete); a trace with a failed operation is not extracted")
        return outs[-1]

    @staticmethod
    def need(node, ins, k):
        if len(ins) < k:
            raise Fail(f"line {node['line']}: {node['fn']}: expected {k} ciphertext operand(s), the trace has "
                       f"{len(ins)}")

    def define(self, o):
        if self.produced is None:
            self.produced = self.line
        name, k = o["id"], 0
        while name in self.defined or name in self.inputs:
            k += 1
            name = f"{o['id']}#{k}"
        self.defined[name] = o
        self.cur[o["id"]] = name
        return name

    def emit(self, node, op, **kw):
        self.body.append({"op": op, **kw})
        self.prov.append({"index": len(self.body) - 1, "openfhe": node["fn"], "traceLine": node["line"]})
        if "a" in kw and op not in ("add", "sub", "mul"):
            self.root[kw["dst"]] = self.root.get(kw["a"], kw["a"])

    def fresh(self, b):
        k = 0
        while f"{b}~{k}" in self.defined:
            k += 1
        return f"{b}~{k}"

    def latest(self, i, since):
        """The last value derived from `i` by unary ops emitted at body index >= since (or `i`)."""
        r = self.root.get(i, i)
        for ins in reversed(self.body[since:]):
            if self.root.get(ins["dst"]) == r:
                return ins["dst"]
        return i

    def check_packed(self, node, p):
        """Only packed plaintexts have the [0, t) lift the bounds assume. A CoefPacked plaintext is
        stored centred and, under FLEXIBLEAUTO(EXT), multiplied by the scaling factor without a
        reduction mod t (coefpackedencoding.cpp:42-83), so its norm can be far above t - 1."""
        enc = p.get("enc")
        if enc is None:  # a tracer without the field: decide by the call that made it
            maker = self.ptmaker.get(p["id"])
            if maker is None or not maker.startswith("CryptoContext::MakePackedPlaintext"):
                raise Fail(f"line {node['line']}: plaintext {p['id']}: its encoding is not recorded and it was not made "
                           f"by a traced MakePackedPlaintext ({maker or 'origin not in the trace'}); only packed "
                           "plaintexts are mapped")
        elif enc != "packed":
            raise Fail(f"line {node['line']}: plaintext {p['id']} has encoding {enc}: only packed plaintexts are "
                       "mapped (a CoefPacked plaintext is stored centred and, under FLEXIBLEAUTO/FLEXIBLEAUTOEXT, "
                       "multiplied by the scaling factor without reduction mod t, coefpackedencoding.cpp:42-83, so "
                       "the bound t-1 does not hold)")

    def check_made(self, node, p):
        """A plaintext operand must be the output of a traced CryptoContext::Make* call of this
        trace (= this context), unchanged since (ids are content identities recomputed at every
        use), encoded for this context's plaintext modulus (the tracer's "t", when recorded)."""
        if p["id"] not in self.ptmaker:
            raise Fail(f"line {node['line']}: plaintext {p['id']} was not produced by a traced CryptoContext::Make*Plaintext "
                       "of this context (its element was changed after encoding, e.g. through GetElement<DCRTPoly>(), or it "
                       "comes from another context or from outside the trace); refused")
        for q in (p, self.ptinfo.get(p["id"], {})):
            if "t" in q and int(q["t"]) != int(self.t):
                raise Fail(f"line {node['line']}: plaintext {p['id']} is encoded for plaintext modulus {q['t']}, the context's "
                           f"is {self.t}; refused")

    def declare_plain(self, node, morphed, p):
        """Bind the morphed (1-part) copy of plaintext `p` to a declared plaintext input."""
        self.check_packed(node, p)
        self.check_made(node, p)
        if morphed["towers"] != p["towers"] or int(morphed["sf"]) != int(p["sf"]) or morphed["nsd"] != p["nsd"]:
            raise Fail(f"line {node['line']}: the 1-part operand {morphed['id']} does not match plaintext {p['id']}")
        name = f"{p['id']}@T{p['towers']}"
        if name not in self.inputs:
            self.inputs[name] = {"name": name, "parts": 1, "level": p["towers"], "key": 1,
                                 "bound": str(self.t - 1), "origin": {"openfhe": p["id"]}}
            self.input_sf[name] = int(p["sf"])
            self.order.append(name)
        self.cur[morphed["id"]] = name
        return name

    def walk_top(self, node):
        scan_refused(node)
        self.record_keys(node)
        self.walk(node)

    def saw_encrypt(self, node):
        """A traced Encrypt: the trace starts before encryption (--assume-fresh-inputs)."""
        if self.encrypt_line is None:
            self.encrypt_line = node["line"]
        if self.assumed:
            raise Fail(f"line {node['line']}: {node['fn']}: --assume-fresh-inputs took {self.assumed[0]} as a fresh "
                       "encryption, but the trace contains a traced Encrypt, so it starts before encryption and "
                       "its inputs are the traced encryptions (refused)")

    def decrypt(self, node):
        """CryptoContext::Decrypt: the decrypted ciphertext must be a value of the extracted program."""
        fn = node["fn"]
        sks = keys_of(node["ins"], "sk")
        if sks:
            self.use_secret(sks[0]["id"], node["line"], f"{fn} with private key {sks[0]['id']}")
        for o in cts(node["ins"]):
            i = self.cur.get(o["id"])
            if i is None:
                raise Fail(f"line {node['line']}: {fn}: the decrypted ciphertext {o['id']} (towers {o['towers']}, parts "
                           f"{o['parts']}) is not a value any traced operation produced: the program changed it after the "
                           "last traced operation (an untraced call such as EvalAddInPlaceNoCheck, EvalMultNoCheck, "
                           "GetElements()/SetElements(), SetLevel, a serialization round trip), or it comes from outside "
                           "the trace; a certificate would not be about what is decrypted (refused)")
            if i not in self.decrypted:
                self.decrypted.append(i)

    def walk(self, node):
        fn = node["fn"]
        name = base(fn)
        ins, outs = cts(node["ins"]), cts(node["outs"])
        self.line = node["line"]

        if name.startswith("CryptoContext::Encrypt"):
            # A fresh encryption: an input of the program. The key decides which kind.
            self.saw_encrypt(node)
            (p,) = pts_of(node["ins"])[:1] or [None]
            if p is None:
                raise Fail(f"line {node['line']}: {fn}: the encrypted plaintext is not recorded")
            self.check_packed(node, p)
            self.check_made(node, p)
            pks, sks = keys_of(node["ins"], "pk"), keys_of(node["ins"], "sk")
            if len(pks) + len(sks) != 1:
                if not self.assume_keys:
                    raise Fail(f"line {node['line']}: {fn}: the encryption key is not recorded in the trace "
                               "(a tracer without key records?)")
                sym = False
            else:
                sym = bool(sks)
                if pks:
                    pk = pks[0]["id"]
                    if not self.assume_keys and pk not in self.kg_pk:
                        raise Fail(f"line {node['line']}: {fn}: public key {pk} was not produced by a traced "
                                   "single-party CryptoContext::KeyGen() (a joint/multiparty or deserialized key?); "
                                   "start the trace before KeyGen, or pass --assume-single-party-keys")
                    self.use_secret(self.kg_pk.get(pk), node["line"], f"{fn} with public key {pk}")
                else:
                    self.use_secret(sks[0]["id"], node["line"], f"{fn} with a private key")
            for o in outs:
                if o["id"] not in self.inputs:
                    if o["parts"] != 2:
                        raise Fail(f"line {node['line']}: Encrypt produced {o['parts']} parts")
                    d = {"name": o["id"], "parts": 2, "level": o["towers"], "key": 1,
                         "origin": {"openfhe": p["id"] if p else None}}
                    if sym:
                        # Not a public-key encryption: its own (smaller) worst-case bound, and not
                        # listed as fresh (no probabilistic theorem covers it).
                        d["bound"] = str(self.sym_bound)
                        d["origin"]["encryption"] = "private-key (symmetric) Encrypt: bound (t-1) + t*Be"
                    self.inputs[o["id"]] = d
                    self.input_sf[o["id"]] = int(o["sf"])
                    self.order.append(o["id"])
                    self.cur[o["id"]] = o["id"]
                    if p and (int(p["sf"]) != int(o["sf"]) or p["towers"] != o["towers"]):
                        raise Fail(f"line {node['line']}: Encrypt output disagrees with its plaintext")
        elif name.startswith("CryptoContext::Make"):
            for p in pts_of(node["outs"]):
                self.ptinfo[p["id"]] = p
                self.ptmaker.setdefault(p["id"], fn)
        elif name in ("LeveledSHEBase::EvalAddCoreInPlace", "LeveledSHEBase::EvalSubCoreInPlace"):
            self.need(node, ins, 2)
            a, b = self.use(ins[0]), self.use(ins[1])
            self.emit(node, "add" if "Add" in name else "sub", dst=self.define(self.out(node, outs)), a=a, b=b)
        elif name in ("LeveledSHEBase::EvalMultCore", "CryptoContext::EvalMultNoRelinNoCheck"):
            # EvalMultNoRelinNoCheck (cryptocontext.h, v1.6): the same tensor product as EvalMultCore,
            # without level/scale alignment; levels are checked by fhe_check (expect) anyway.
            if len(ins) != 2 or len(outs) != 1:
                raise Fail(f"line {node['line']}: {fn}: expected two ciphertexts in and one out")
            a, b = self.use(ins[0]), self.use(ins[1])
            self.emit(node, "mul", dst=self.define(self.out(node, outs)), a=a, b=b)
        elif name == "LeveledSHERNS::EvalSquare":
            self.need(node, ins, 1)
            # The squaring core is not traced; under the auto modes a ModReduce of a degree-2
            # operand comes first (rns-leveledshe.cpp:231-241).
            n0 = len(self.body)
            a0 = self.use(ins[0])
            for k in node["kids"]:
                self.walk(k)
            a = self.latest(a0, n0)
            self.emit(node, "square", dst=self.define(self.out(node, outs)), a=a)
        elif name == "LeveledSHEBGVRNS::EvalMultCoreInPlace":
            self.need(node, ins, 1)
            # cv[i] *= constant, constant in [0, t) (bgvrns-leveledshe.cpp:227-239)
            a = self.use(ins[0])
            (c,) = ints(node, "constant")
            self.emit(node, "mulConst", dst=self.define(self.out(node, outs)), a=a, c=str(c))
        elif name in ("LeveledSHEBase::EvalNegate", "LeveledSHEBase::EvalNegateInPlace"):
            self.need(node, ins, 1)
            # Negation of every component: the user's message is negated and OpenFHE keeps
            # scalingFactorInt (Source `negate` = mulConst -1 on the message; scale unchanged).
            a = self.use(ins[0])
            self.emit(node, "negate", dst=self.define(self.out(node, outs)), a=a)
        elif name == "LeveledSHEBGVRNS::ModReduceInternalInPlace":
            self.need(node, ins, 1)
            (k,) = ints(node, "levels")
            cur = self.use(ins[0])
            for j in range(k):
                dst = self.define(self.out(node, outs)) if j == k - 1 else self.fresh(cur)
                if j < k - 1:
                    self.defined[dst] = None
                self.emit(node, "modSwitch", dst=dst, a=cur)
                cur = dst
        elif name == "LeveledSHEBGVRNS::LevelReduceInternalInPlace":
            self.need(node, ins, 1)
            (k,) = ints(node, "levels")
            a = self.use(ins[0])
            self.emit(node, "dropLimbs", dst=self.define(self.out(node, outs)), a=a, k=k)
        elif name == "LeveledSHEBase::EvalAutomorphism":
            self.need(node, ins, 1)
            # OpenFHE v1.6.1 applies X -> X^g BETWEEN the inner product with the key (over Q_l*P,
            # plus P*c0) and ModDown (base-leveledshe.cpp EvalAutomorphismCore:455-506 with
            # EvalFastKeySwitchCoreExt, keyswitch-hybrid.cpp:389-421); v1.3.1 key-switched first
            # and permuted last. The phase effect equals automorph;keySwitch within the same
            # key-switching bound, with t | e: FHE/Pin/AlgoOpenFHE.lean, rotateOpenFHE161_spec
            # (proved for the v1.6.1 order; rotateOpenFHE161 reproduces the library bit for bit;
            # locked: Challenge.Realize.rotateOpenFHE161_run, the run automorph;keySwitch ending
            # in the v1.6.1 result meets both contracts).
            if ins[0]["parts"] != 2:
                # OpenFHE throws here before it looks up (and the tracer registers) the key:
                # the call has no key input and no output in the trace.
                raise Fail(f"line {node['line']}: {fn} on a {ins[0]['parts']}-part operand: OpenFHE throws "
                           "\"Ciphertext should be relinearized before.\" (base-leveledshe.cpp:441); the call "
                           "produced no ciphertext; relinearize the operand first")
            a = self.use(ins[0])
            (g,) = ints(node, "i")
            eks = keys_of(node["ins"], "ek")
            if len(eks) != 1 and not self.assume_keys:
                raise Fail(f"line {node['line']}: {fn}: the rotation key used is not recorded in the trace")
            if eks:
                self.check_eval_key(node, eks[0], "auto", g)
            mid = self.fresh(a + "@" + str(g))
            self.defined[mid] = None
            self.emit(node, "automorph", dst=mid, a=a, g=g)
            self.emit(node, "keySwitch", dst=self.define(self.out(node, outs)), a=mid)
        elif name in RELIN_FNS and "EvalKey" in fn:
            big = [o for o in ins if o["parts"] > 2]
            if big:
                # base-leveledshe.cpp EvalMult/EvalSquare(..., EvalKey): key-switches cv[2] only and
                # then resize(2); on a 3-part operand the product has 4-5 parts and the result is
                # not an encryption of the product.
                raise Fail(f"line {node['line']}: {fn} on a {big[0]['parts']}-part operand {big[0]['id']}: OpenFHE "
                           "relinearizes only the third component of the product and drops the rest, so the result "
                           "is not an encryption of the product (relinearize the operand first)")
            eks = keys_of(node["ins"], "ek")
            if len(eks) != 1 and not self.assume_keys:
                raise Fail(f"line {node['line']}: {fn}: the relinearization key used is not recorded in the trace")
            if eks:
                self.check_eval_key(node, eks[0], "mult", 0)
            n0 = len(self.body)
            for k in node["kids"]:
                self.walk(k)
            if len(self.body) == n0 or self.body[-1]["op"] not in ("mul", "square"):
                raise Fail(f"line {node['line']}: {fn} produced no product")
            self.emit(node, "relin", dst=self.define(self.out(node, outs)), a=self.body[-1]["dst"])
        elif name in ("LeveledSHEBase::Relinearize", "LeveledSHEBase::RelinearizeInPlace"):
            if node["kids"]:
                # Relinearize calls RelinearizeInPlace on a clone: translate the inner call only.
                for k in node["kids"]:
                    self.walk(k)
                self.use(self.out(node, outs))
                return
            a = self.use(ins[0])
            parts = ins[0]["parts"]
            eks = keys_of(node["ins"], "ek")
            if parts != 3:
                raise Fail(f"line {node['line']}: {fn} of a {parts}-part ciphertext: only 3 parts are mapped")
            if len(eks) != parts - 2 and not self.assume_keys:
                raise Fail(f"line {node['line']}: {fn}: the relinearization keys used are not recorded in the trace")
            for j, ek in enumerate(eks):
                self.check_eval_key(node, ek, "mult", j)
            self.emit(node, "relin", dst=self.define(self.out(node, outs)), a=a)
        elif name in PLAIN_OPS and "plaintext" in fn:
            pts = pts_of(node["ins"])
            if len(ins) != 1 or len(pts) != 1:
                raise Fail(f"line {node['line']}: {fn}: expected one ciphertext and one plaintext")
            p = pts[0]
            adj = [k for k in node["kids"] if base(k["fn"]).startswith("LeveledSHERNS::AdjustFor")]
            if len(adj) > 1:
                raise Fail(f"line {node['line']}: {fn}: expected at most one AdjustFor* call, found {len(adj)}")
            if adj:
                ones = [o for o in cts(adj[0]["ins"]) if o["parts"] == 1]
                if len(ones) != 1:
                    raise Fail(f"line {node['line']}: cannot find the morphed plaintext in {adj[0]['fn']}")
                pname = self.declare_plain(node, ones[0], p)
            else:
                # OpenFHE >= 1.6 (rns-leveledshe.cpp:47-71, 118-127, 184-193, 263-279): when
                # AdjustFor*InPlace would be a no-op (same level, noise-scale degree and tower
                # count, plaintext in EVALUATION form; for a product also FIXEDMANUAL or both of
                # degree 1) the plaintext element is used directly, without MorphPlaintext. The
                # plaintext itself is the 1-part operand: it must have the ciphertext's towers.
                if p["towers"] != ins[0]["towers"]:
                    raise Fail(f"line {node['line']}: {fn}: no AdjustFor* call but plaintext {p['id']} has "
                               f"{p['towers']} towers and the ciphertext {ins[0]['towers']}")
                pname = self.declare_plain(node, {"id": p["id"] + "#direct", "towers": p["towers"],
                                                  "sf": p["sf"], "nsd": p["nsd"]}, p)
            c0 = self.use(ins[0])
            n0 = len(self.body)
            for k in node["kids"]:
                self.walk(k)
            if not adj and len(self.body) != n0:
                raise Fail(f"line {node['line']}: {fn}: unexpected traced operations in the no-adjust path")
            a, pv = self.latest(c0, n0), self.latest(pname, n0)
            op = PLAIN_OPS[name]
            dst = self.define(self.out(node, outs))
            self.emit(node, op, dst=dst, a=a, p=pv)
            if op == "mulPlain":
                # LeveledSHERNS::EvalMultInPlace leaves scalingFactorInt alone; the BGV wrapper
                # sets it afterwards (bgvrns-leveledshe.cpp:241-249). Compare at the wrapper.
                self.no_sf_check.add(dst)
        elif name == "LeveledSHEBGVRNS::EvalMultInPlace":
            for k in node["kids"]:
                self.walk(k)
            last = self.body[-1] if self.body else {"op": None}
            o = self.out(node, outs)
            if last["op"] != "mulPlain":
                raise Fail(f"line {node['line']}: {fn} without a traced plaintext product")
            if self.cur.get(o["id"]) != last["dst"]:
                rec = self.defined[last["dst"]]
                if (rec["towers"], rec["parts"], rec["nsd"]) != (o["towers"], o["parts"], o["nsd"]):
                    raise Fail(f"line {node['line']}: {fn} changed more than the scaling factor")
                # Only the bookkeeping scalingFactorInt changes: the same ciphertext.
                self.emit(node, "copy", dst=self.define(o), a=last["dst"])
            else:
                # The wrapper left the ciphertext id, hence (ids hash the factor) its
                # scalingFactorInt, unchanged: the recorded factor of the inner product IS the
                # final one, so it must be compared after all (without this, a plaintext product
                # whose true factor differs from the tracked one escaped the replay when the
                # tracked factor was 1).
                self.no_sf_check.discard(last["dst"])
        elif name.startswith("CryptoContext::Decrypt"):
            self.decrypt(node)
        elif name.startswith("CryptoContext::") and "KeyGen" in name or name.startswith("CryptoContext::KeysGen"):
            pass  # key generation: recorded by record_keys
        else:
            # Wrappers (CryptoContext::*, LeveledSHERNS::*, Adjust*): recurse. A wrapper whose
            # ciphertext output is not produced by a recognised sub-call is an error.
            for k in node["kids"]:
                self.walk(k)
            in_ids = {o["id"] for o in ins}
            for o in outs:
                if o["id"] in in_ids:
                    self.use(o)  # passed through unchanged: must itself be known
                    continue
                i = self.cur.get(o["id"])
                if i is None:
                    raise Fail(f"line {node['line']}: {fn} outputs {o['id']} via an operation "
                               f"the extractor does not understand")


def choose_outputs(ex, explicit=None, from_decrypt=False, ren=None):
    """The program's outputs (shared by extract_bfv.py). Every ciphertext the trace decrypts
    (ex.decrypted: values of the extracted program, Extractor.decrypt) is an output:
      explicit (--outputs a,b): those, which must include every decrypted one;
      from_decrypt: exactly the decrypted ones;
      otherwise: the values no instruction consumes, plus every decrypted one (a superset).
    Returns (outputs, a description of the rule for crossCheck.outputs)."""
    ren = ren or {}
    r = lambda i: ren.get(i, i)  # noqa: E731
    dec = list(dict.fromkeys(r(i) for i in ex.decrypted))
    if explicit:
        # trace ids name the latest value with that content
        outputs = list(dict.fromkeys(r(ex.cur.get(o, o)) for o in explicit.split(",")))
        miss = [d for d in dec if d not in outputs]
        if miss:
            raise Fail(f"--outputs {explicit} omits {miss}, which the program decrypts (traced Decrypt): every decrypted "
                       "ciphertext must be certified")
        how = "--outputs (includes every decrypted ciphertext)"
    elif from_decrypt:
        if not dec:
            raise Fail("--outputs-from-decrypt: the trace contains no traced CryptoContext::Decrypt")
        outputs, how = dec, "--outputs-from-decrypt: exactly the ciphertexts passed to a traced Decrypt"
    else:
        consumed = set()
        for i in ex.body:
            consumed.update(v for k, v in i.items() if k in ("a", "b", "p"))
        outputs = list(dict.fromkeys([i["dst"] for i in ex.body if i["dst"] not in consumed] + dec))
        how = ("the values no instruction consumes plus every ciphertext passed to a traced Decrypt" if dec else
               "the values no instruction consumes (the trace contains no traced Decrypt: what the program decrypts "
               "after the trace ends is not covered)")
    return outputs, {"rule": how, "decrypted": dec}


def cse(ex):
    """Merge exact duplicates: an instruction with the same op, the same (already merged)
    operands and the same constants as an earlier one is dropped and its dst renamed to the
    earlier dst. UNVERIFIED GLUE. Why it cannot change a verdict: the verified analyzer's bound
    (refBound) and the semantics (Source.step) of an instruction are functions of its op, its
    constants and its operands' bounds/values only, so a duplicate gets exactly the bound, level
    and part count of the original; every check the analyzer makes on the duplicate is the check
    it already made on the original, and every later instruction sees the same operand bounds.
    So the merged program is accepted iff the original is, with the same bound for every output.
    (Dead-code elimination is NOT done: the analyzer also checks values no output depends on,
    and removing one could turn NOT CERTIFIED into CERTIFIED.) Returns the number merged."""
    ren, seen, body, prov = {}, {}, [], []
    for ins, pv in zip(ex.body, ex.prov):
        ins = {k: (ren.get(v, v) if k in ("a", "b", "p") else v) for k, v in ins.items()}
        key = json.dumps({k: v for k, v in ins.items() if k not in ("dst", "expect")}, sort_keys=True)
        if key in seen and seen[key][1] == ins.get("expect"):
            ren[ins["dst"]] = seen[key][0]
            continue
        seen[key] = (ins["dst"], ins.get("expect"))
        pv = dict(pv, index=len(body))
        body.append(ins)
        prov.append(pv)
    n = len(ex.body) - len(body)
    ex.body, ex.prov = body, prov
    return n, ren


def replay(p, ex, outputs):
    """Replay levels and message scale factors through the extracted program and compare them
    with OpenFHE's own towers/scalingFactorInt per ciphertext. Source.step multiplies the message
    by c (mulConst), by q_last^-1 mod t (modSwitch) and multiplies messages (mul, square,
    mulPlain); OpenFHE's scalingFactorInt is the factor by which the stored message differs
    from the user's slots, so the two must agree everywhere. `negate` negates the user's message
    and keeps the factor."""
    t = p["t"]
    qs = [int(x["q"]) for x in p["qs"]]
    sf, lev, mism = {}, {}, []
    for i, d in ex.inputs.items():
        sf[i], lev[i] = ex.input_sf[i], d["level"]
    for ins in ex.body:
        a, d, op = ins["a"], ins["dst"], ins["op"]
        if op == "mul":
            v = sf[a] * sf[ins["b"]] % t
        elif op == "mulPlain":
            v = sf[a] * sf[ins["p"]] % t
        elif op == "square":
            v = sf[a] * sf[a] % t
        elif op == "mulConst":
            v = sf[a] * int(ins["c"]) % t
        elif op == "modSwitch":
            v = sf[a] * pow(qs[lev[a] - 1], -1, t) % t
        elif op in ("add", "sub", "addPlain", "subPlain"):
            o = ins.get("b", ins.get("p"))
            if sf[a] != sf[o]:
                mism.append(f"{op} {d}: operand scales differ ({sf[a]} vs {sf[o]})")
            v = sf[a]
        else:  # negate, copy, relin, automorph, keySwitch, dropLimbs
            v = sf[a]
        sf[d] = v
        lev[d] = lev[a] - (1 if op == "modSwitch" else ins.get("k", 0) if op == "dropLimbs" else 0)
        rec = ex.defined.get(d)
        if rec is not None:
            ins["expect"] = {"level": rec["towers"], "parts": rec["parts"]}
            if d not in ex.no_sf_check and int(rec["sf"]) != v:
                mism.append(f"{d}: Source scale {v} != OpenFHE scalingFactorInt {rec['sf']}")
            if rec["towers"] != lev[d]:
                mism.append(f"{d}: Source level {lev[d]} != OpenFHE towers {rec['towers']}")
    return mism, sf, lev


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--params", required=True)
    ap.add_argument("--trace", required=True)
    ap.add_argument("--outputs")
    ap.add_argument("--outputs-from-decrypt", action="store_true")
    ap.add_argument("--artifact", default="")
    ap.add_argument("--no-decrypt-switch", action="store_true")
    ap.add_argument("--assume-fresh-inputs", action="store_true")
    ap.add_argument("--assume-single-party-keys", action="store_true")
    ap.add_argument("--cse", action="store_true")
    ap.add_argument("--compact", action="store_true")
    ap.add_argument("--no-provenance", action="store_true")
    ap.add_argument("--allow-truncated", action="store_true")
    ap.add_argument("--assume-default-build", action="store_true")
    args = ap.parse_args()
    p = json.load(open(args.params))

    def fail(msg):
        print(json.dumps({"format": "fhe-check/v1", "error": msg}, indent=2))
        sys.exit(1)

    try:
        check_tracer(args.params, args.trace, p)  # first: a stale tracer's output is not read further
    except Fail as e:
        fail(str(e))
    if p["scheme"] != "BGV":
        fail("not a BGV context")
    if p["keySwitch"] != "HYBRID":
        fail("only HYBRID key switching is mapped (BV: open)")
    try:
        nz = noise_inputs(p, args.assume_single_party_keys, args.assume_default_build)
        ex = Extractor(p["t"], args.assume_fresh_inputs, args.assume_single_party_keys, nz["symmetricInputNoise"])
        truncated = [] if args.allow_truncated else None
        for top in stream_calls(args.trace, truncated):
            ex.walk_top(top)
    except Fail as e:
        fail(str(e))
    except (KeyError, IndexError, ValueError, TypeError) as e:
        # never a silent crash: an unexpected trace shape is an explicit refusal
        fail(f"the trace has a shape the extractor does not handle ({type(e).__name__}: {e}); refused")
    if not ex.body:
        fail("the trace contains no homomorphic operation")
    mism, sf, lev = replay(p, ex, None)
    merged, ren = 0, {}
    if args.cse:
        merged, ren = cse(ex)
    try:
        outputs, out_rule = choose_outputs(ex, args.outputs, args.outputs_from_decrypt, ren)
    except Fail as e:
        fail(str(e))
    # Decryption: PKEBGVRNS::Decrypt (bgvrns-pke.cpp:48-102, EVALUATION branch :56-75) computes the
    # phase at the ciphertext's level and ModReduces that ONE polynomial down to one tower before
    # reading it mod q0 (centred) mod t. This is Spec.Decrypt.bgvDecryptSwitched; the file declares
    # it ("decryption": switch-to-one-limb) and fhe_check bounds the switched phase itself
    # (Spec.Decrypt.decBound; Challenge.Decrypt.analyze_decrypt_switched). No operation is appended
    # to the program. Each switch multiplies the message by q_last^-1 mod t: the scale recorded
    # here is compared with Decrypt's scalingFactorInt by value_check.py.
    decrypt = []
    for o in outputs:
        scale = sf[o]
        if not args.no_decrypt_switch:
            for l in range(lev[o], 1, -1):
                scale = scale * pow(int(p["qs"][l - 1]["q"]), -1, p["t"]) % p["t"]
        decrypt.append({"output": o, "fromLevel": lev[o], "toLevel": lev[o] if args.no_decrypt_switch else 1,
                        "scale": scale})
    if mism:
        fail("frontend cross-check failed: " + "; ".join(mism))
    alpha = p["towersPerDigit"]
    fresh = [i for i in ex.order if ex.inputs[i]["parts"] == 2 and "bound" not in ex.inputs[i]]
    doc = {
        "format": "fhe-check/v1",
        "source": {"tool": "openfhe", "artifact": args.artifact,
                   "scaling": p["scaling"], "multiplicativeDepth": p["multiplicativeDepth"],
                   "decryptSwitch": not args.no_decrypt_switch},
        "params": {
            "scheme": "BGV",
            "N": p["N"],
            "t": p["t"],
            "limbs": [{"q": str(x["q"]), "psi": str(x["psi"])} for x in p["qs"]],
            "special": [{"q": str(x["q"]), "psi": str(x["psi"])} for x in p["special"]],
            "secretBound": nz["secretBound"],
            "inputNoise": str(nz["inputNoise"]),
            "keyNoise": str(nz["keyNoise"]),
        },
        "noiseDerivation": nz["derivation"],
        "keySwitching": {
            "method": "hybrid",
            # OpenFHE KeySwitchHYBRID: canonical-representative fast base conversion in ModUp and
            # the BGV ModDown (X - t*FastBConv([X*t^-1]_P))/P: FHE.KeySwitch.keySwitchBGVOpenFHE_spec.
            "variant": "openfhe",
            # digit j at level l = limbs [j*alpha, min((j+1)*alpha, l)), OpenFHE
            # KeySwitchHYBRID::EvalKeySwitchPrecomputeCore (keyswitch-hybrid.cpp:312-316)
            "digits": {"kind": "consecutive", "towersPerDigit": alpha, "dnum": p["dnum"]},
        },
        "modSwitch": {"method": MODSWITCH_METHOD},
        "decryption": ({"method": "at-output-level",
                        "source": "--no-decrypt-switch: textbook decryption at the output's level (NOT what OpenFHE's Decrypt does)"}
                       if args.no_decrypt_switch else
                       {"method": "switch-to-one-limb",
                        "source": "PKEBGVRNS::Decrypt, EVALUATION branch: ModReduce of the phase to one tower (bgvrns-pke.cpp:56-75), not traced"}),
        # ASSUMPTIONS of the probabilistic mode (fhe_check --kappa): which inputs are fresh
        # public-key encryptions (traced CryptoContext::Encrypt outputs with a public key, or
        # --assume-fresh-inputs), and the hard sampler bounds: pk error and e0, e1 from the DGG
        # (|e| <= Be), v ternary.
        "freshEncryption": {
            "inputs": fresh,
            "keyError": nz["errorBound"], "u": 1, "e1": nz["errorBound"], "e2": nz["errorBound"],
            # the stored plaintext polynomial p of an encryption has |p| <= t - 1 (packed encoding,
            # the only one mapped: check_packed); fhe_check's fresh noise is plaintextBound + t*eps
            "plaintextBound": nz["plaintextBound"],
            # |mean| of every coefficient of (u, e1, e2): see DGG_MEAN_NUM above (sigma = 3.19f only)
            "mean": {"num": DGG_MEAN_NUM, "den": DGG_MEAN_DEN, "source": DGG_MEAN_SOURCE},
            "source": "PKERNS::Encrypt with a public key: (b*v + t*e0 + m, a*v + t*e1), b = t*e - a*s "
                      "(rns-pke.cpp:61-75,152-199; base-pke.cpp:66-91); v ternary (TUG), e, e0, e1 from the "
                      f"DGG with |e| <= {nz['errorBound']} (discretegaussiangenerator-impl.h:81-82,94-99)",
        },
        "program": {
            "inputs": [ex.inputs[i] for i in ex.order],
            "body": ex.body,
            "outputs": outputs,
        },
        # The library's scaling-factor bookkeeping, for fhe_check's user-level decryption check
        # (Spec.Scaling.scaleOK?, Challenge.Scaling.certify?_user): the factor OpenFHE recorded
        # with every input (scalingFactorInt; Encrypt copies the plaintext's), whether the
        # technique tracks factors (FLEXIBLEAUTO, FLEXIBLEAUTOEXT: bgvrns-leveledshe.cpp:70-76,
        # 235-238, 245-248; bgvrns-pke.cpp:62-72), and which body instructions are the library's
        # scale adjustments: every `mulConst` this extractor emits comes from
        # LeveledSHEBGVRNS::EvalMultCoreInPlace(ct, NativeInteger), which OpenFHE v1.6.1 calls only
        # from AdjustLevelsAndDepth*InPlace (bgvrns-leveledshe.cpp:86-214). Kept outside "program"
        # so that the recorded conformance fixtures, which compare "program", still reproduce.
        "scaling": {
            "tracks": p["scaling"] in ("FLEXIBLEAUTO", "FLEXIBLEAUTOEXT"),
            "inputFactors": [{"name": i, "factor": ex.input_sf[i] % p["t"]} for i in ex.order],
            "adjustments": [k for k, ins in enumerate(ex.body) if ins["op"] == "mulConst"],
        },
        "provenance": ex.prov,
        "crossCheck": {"what": "message scale factors and levels replayed vs OpenFHE's own "
                               "scalingFactorInt/towers per ciphertext (all scaling techniques)",
                       "mismatches": mism,
                       "decryption": decrypt},
    }
    if ex.decrypted or args.outputs or args.outputs_from_decrypt:
        # only when it says something: keeps the files of traces without Decrypt as they were
        doc["crossCheck"]["outputs"] = out_rule
    if truncated:
        doc["crossCheck"]["truncatedTrace"] = (f"the trace ends inside the call that starts at line {truncated[0]}: "
                                               "this file is the PREFIX of the program before that call")
    if args.cse:
        doc["crossCheck"]["cse"] = {"merged": merged, "note": "exact duplicates merged (extract.py cse(): "
                                    "unverified glue; cannot change the verdict)"}
    if args.no_provenance:
        doc["provenance"] = []
    if args.compact:
        json.dump(doc, sys.stdout, separators=(",", ":"))
    else:
        json.dump(doc, sys.stdout, indent=1)
    print()


if __name__ == "__main__":
    main()
