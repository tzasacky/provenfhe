#!/usr/bin/env python3
"""UNTRUSTED OpenFHE frontend for fhe_check: OpenFHE BFVrns artifacts -> neutral JSON (fhe-check/v1).

Inputs
  --params params.json   fields of a BFVrns CryptoContext, as printed by `bfv_demo dump cc.json`
                         (or `bfv_demo run`); read through OpenFHE's own API
  --trace  trace.jsonl   JSON-lines trace from json_tracer.h (OpenFHE's ENABLE_TRACER hooks)
  --outputs a,b          optional: output ciphertext ids, which must include every ciphertext the
                         trace decrypts (default: the ciphertexts never consumed PLUS every one
                         passed to a traced Decrypt; extract.py "Outputs and Decrypt")
  --outputs-from-decrypt outputs = exactly the ciphertexts passed to a traced Decrypt
  --idealised          HPS-family techniques only: declare bfv.multiplication.floatTolerant = false,
                         i.e. the idealised exact algorithm instead of the library's binary64-assisted
                         one (for comparing the two budgets; it is NOT a description of the library)
  --assume-fresh-inputs  for traces that start after encryption: a 2-part ciphertext that no
                         traced operation produced is taken as a FRESH public-key encryption
                         (an assumption the report prints). Without it such a ciphertext is an
                         extraction error. Only for INPUTS: used before the first traced
                         operation produces a ciphertext, noiseScaleDeg 1, in a trace with no
                         traced Encrypt (extract.py); refused otherwise.

Supported library: upstream OpenFHE v1.6.1 (openfheorg/openfhe-development b59e1f29) with
openfhe/openfhe-v1.6.1-tracer.patch (observation hooks only; build with openfhe/build_openfhe.sh),
the same build as extract.py. File:line references are to PRISTINE v1.6.1, paths relative to src/.

Inputs (besides those above)
  --assume-single-party-keys, --assume-default-build   as for extract.py (key provenance and the
                         params.json "build" section are otherwise checked; see extract.py)

Shared with extract.py (imported, not copied): the streaming trace reader (tracer error events,
unbalanced/truncated traces refused), the SSA value names, key provenance (one single-party
KeyGen secret; relinearization / rotation keys generated from it for the index used; multiparty,
PRE, key-switching and sparse-key calls refused by name), the Decrypt rule (every decrypted
ciphertext is a value of the extracted program and an output), plaintext provenance (every
plaintext operand is an unchanged output of a traced Make*Plaintext of this context, with its t),
the --assume-fresh-inputs rule, the build-flag refusals
(WITH_REDUCED_NOISE, NATIVEINT != 64, no HAVE_INT128), the refusal of EvalSum / EvalInnerProduct /
EvalFastRotation / the *Mutable products, and the sigma checks (sigma >= 300; sigma != 3.19, for
which no sampler mean is declared). BFV-specific refusals:
private-key Encrypt, plaintexts that are neither packed nor CoefPacked with scalingFactorInt = 1
(Extractor.check_packed says why CoefPacked is in [0, t) for BFV), plaintexts at fewer limbs than
the ciphertext,
EvalMultNoRelinNoCheck, a relinearization of more than 3 parts, a GAUSSIAN secret, noiseScale != 1,
threshold contexts, BV with a digit size, a FindLevelsToDrop table that disagrees with the replica
or with the drop the library recorded at run time.

What is extracted:

* parameters: N, t, the primes of Q, the special primes P of HYBRID key switching (none for BV),
  the auxiliary basis of the multiplication technique (HPS: the sizeQ+1 primes R; HPSPOVERQ and
  HPSPOVERQLEVELED: the sizeQ primes R, of which a multiplication on k limbs uses the first k;
  BEHZ: the base B, m_sk; m~ = 2^16), all dumped from the CryptoContext, none recomputed.
* the instruction mapping (class Extractor): every traced function that changes a ciphertext is
  either translated or makes the extraction FAIL.
* for HPSPOVERQLEVELED: the number of limbs the library drops internally before each
  multiplication, relinearization and rotation key switch (FindLevelsToDrop,
  pke/lib/scheme/bfvrns/bfvrns-leveledshe.cpp:98-198), as bfv.multiplication.internalDrops: one
  entry per instruction of program.body (0 at an instruction without an internal drop). This is
  what fhe_check's budget reads (one budget per instruction); it is the same number as
  provenance[].internalDrop. Its maxima are also emitted, as a cross-check fhe_check verifies:
  maxInternalDrop (products, relinearizations) and maxInternalDropKS (rotation key switches).
  THREE-WAY CONSISTENCY: each number is the library's own function evaluated on the context
  (params.json: levelsToDrop), compared with the Python replica below and with the value each
  hooked call recorded at run time (trace: levelsDropped); a disagreement is an extraction
  error. fhe_check cannot detect an understated drop from the file: this check is what the
  declared drops rest on.

Nothing here is trusted: a wrong translation can only make fhe_check certify a different
program than the one OpenFHE ran; the provenance list ties every emitted op to a trace line,
and two cross-checks (levels and parts here; plaintext values in value_check_bfv.py) test the
translation against OpenFHE's own run.
"""
import argparse
import json
import math
import os
import struct
import sys
from fractions import Fraction

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
sys.dont_write_bytecode = True
from extract import (DGG_MEAN_DEN, DGG_MEAN_NUM, DGG_MEAN_SOURCE, DGG_SIGMA, DGG_TAIL, OPENFHE_VERSION, UNMODELLED_CALLS, Fail, base, check_build, check_tracer, cts, ints,  # noqa: E402
                     choose_outputs, keys_of, pts_of, scan_refused, stream_calls)
from extract import Extractor as BGVExtractor  # noqa: E402  (BGV extractor: trace reader, SSA names, key provenance)

TECHNIQUES = ("HPS", "HPSPOVERQ", "HPSPOVERQLEVELED", "BEHZ")
MTILDE = 1 << 16  # pke/include/schemerns/rns-cryptoparameters.h:1927 (m_mtilde; no accessor), dcrtpoly-impl.h:1727
VERSION = OPENFHE_VERSION


def sigma_of(p):
    sigma = float(p["sigma"])
    if sigma >= 300:
        raise Fail("sigma >= 300 uses Karney sampling, which has no hard tail cut")
    return struct.unpack("f", struct.pack("f", sigma))[0]  # OpenFHE stores sigma as float


def find_levels_to_drop(p, mult_depth, dcrt_bits, key_switch):
    """Python replica of lbcrypto::FindLevelsToDrop (OpenFHE v1.6.1 bfvrns-leveledshe.cpp:98-198),
    same floating-point operations in the same order (IEEE doubles; WITH_REDUCED_NOISE undefined).
    v1.6.1 computes in log2 (v1.3.1: natural log, with a different stopping test log(1.001)) and
    cushions the estimate by 3*depth + 16 bits (v1.3.1: 2*depth + 16), so it drops fewer limbs."""
    sigma = sigma_of(p)
    alpha = float(p["assuranceMeasure"])
    pt = float(p["t"])
    n = p["N"]
    relin_window = p["digitSizeBV"]
    hybrid = p["keySwitch"] == "HYBRID"
    k, num_part_q, parties = p["towersPerDigit"], p["dnum"], p["thresholdParties"]
    berr = sigma * math.sqrt(alpha)                                                    # Berr
    bkey = math.sqrt(parties) * berr if p["secretKeyDist"] == "GAUSSIAN" else float(parties)  # Bkey
    w = math.pow(2, dcrt_bits if relin_window == 0 else relin_window)
    delta = 2.0 * math.sqrt(n)
    delta_ms = 4.0 * math.sqrt(n)
    if p["encryptionTechnique"] == "EXTENDED":                                         # Vnorm
        vnorm = (1.0 + delta_ms * bkey) / 2.0
    else:
        vnorm = berr * (1.0 + 2.0 * delta * bkey)

    def noise_ks(logq_prev):
        if hybrid:
            return k * (num_part_q * delta * berr + delta_ms * bkey + 1.0)
        digits_per_tower = 1 if relin_window == 0 else (dcrt_bits // relin_window) + 1
        return delta * digits_per_tower * (math.floor(logq_prev / dcrt_bits) + 1) * w * berr / 2.0

    c1 = delta * delta_ms * pt * bkey

    def c2(logq_prev):
        return delta * delta_ms * bkey * bkey / 2.0 + noise_ks(logq_prev)

    def logq_bfv(logq_prev):
        if mult_depth > 0:
            return math.log2(4 * pt) + (mult_depth - 1) * math.log2(c1) + math.log2(c1 * vnorm + mult_depth * c2(logq_prev))
        return math.log2(pt * (4 * vnorm))

    logq_prev = 6.0 * math.log2(10)
    logq = logq_bfv(logq_prev)
    while abs(logq - logq_prev) > math.log2(1.001):
        logq_prev = logq
        logq = logq_bfv(logq_prev)
    loge = logq - 2 - math.log2(pt)
    log_extra = math.log2(noise_ks(logq)) if key_switch else math.log2(delta_ms)
    levels = math.floor((loge - 3 * mult_depth - 16 - log_extra) / dcrt_bits)
    size_q = len(p["qs"])
    return max(0, min(levels, size_q - 1))


def noise_inputs(p, enc_levels=None, plain_levels=None, assume_keys=False, assume_build=False):
    """ASSUMED noise bounds, from OpenFHE source. BFV noise: e = [phase - floor(Q/t)*m]_Q, m the
    stored plaintext polynomial with coefficients in [0, t)."""
    N, t = p["N"], p["t"]
    if p["secretKeyDist"] not in ("UNIFORM_TERNARY", "SPARSE_TERNARY"):
        raise Fail(f"secret distribution {p['secretKeyDist']}: only UNIFORM_TERNARY and SPARSE_TERNARY secrets are "
                   "mapped (Bs = 1)")
    check_build(p, assume_build)
    if int(p["noiseScale"]) != 1:
        raise Fail(f"BFV noiseScale {p['noiseScale']} != 1: the encryption noise is not e "
                   "(gen-cryptocontext-bfvrns-internal.h sets it to 1)")
    if p["thresholdParties"] != 1:
        raise Fail("threshold (multiparty) contexts are not mapped")
    qs0 = [int(x["q"]) for x in p["qs"]]
    if t - 1 > qs0[0] // 2 or any(t > q for q in qs0):
        raise Fail(f"t = {t} with q0 = {qs0[0]}: the plaintext modulus is outside the packed-encoding window t - 1 <= floor(q0/2) (and t <= every limb) required by the library's encoder; refused")
    if p["multiplicationTechnique"] not in TECHNIQUES:
        raise Fail(f"multiplication technique {p['multiplicationTechnique']}: not mapped")
    enc = p["encryptionTechnique"]
    sigma = sigma_of(p)
    if sigma != struct.unpack("f", struct.pack("f", DGG_SIGMA))[0]:
        # as extract.noise_inputs (BGV): the fresh-noise statement's sampler mean (freshEncryption.mean,
        # read by fhe_check --kappa) is declared for sigma = 3.19f only
        raise Fail(f"sigma = {p['sigma']}: the declared sampler mean applies to sigma = 3.19 only (OpenFHE's default, "
                   "3.19f), so no bound on the mean of the "
                   "encryption errors can be declared for this context (freshEncryption.mean)")
    Be = int(math.ceil(sigma * DGG_TAIL))
    Bs = 1
    qs = [int(x["q"]) for x in p["qs"]]
    # r_l = (q_0 ... q_{l-1}) mod t for every level l = 1..L
    rl, Q = {}, 1
    for l, q in enumerate(qs, 1):
        Q *= q
        rl[l] = Q % t
    # the levels (numbers of limbs) at which the trace encrypts / adds plaintexts; all if unknown
    enc_levels = sorted(enc_levels or rl)
    plain_levels = sorted(plain_levels or rl)
    rs = [rl[l] for l in enc_levels]
    plain_dev = max(-((-rl[l] * (t - 1)) // t) for l in plain_levels)
    E = Be * (1 + 2 * N * Bs)  # |v*e_pk + e0 + e1*s|: v, s ternary; e_pk, e0, e1 from the DGG
    if enc == "STANDARD":
        # c = (b*v + e0 + X, a*v + e1), b = e_pk - a*s, X = TimesQovert(m) = ceil(Q*m/t) for the
        # stored m in [0,t): ceil(Q*m/t) = floor(Q/t)*m + ceil(r*m/t), r = Q mod t.
        dev = max(-((-r * (t - 1)) // t) for r in rs)
        inputNoise = E + dev
        formula = ("Be*(1 + 2*N*Bs) + max_l ceil(r_l*(t-1)/t), r_l = Q_l mod t, l over the numbers of limbs at which the trace encrypts: phase = v*e_pk + e0 + e1*s + ceil(Q*m/t) and "
                   "ceil(Q*m/t) - floor(Q/t)*m = ceil(r*m/t) for m in [0,t)")
    elif enc == "EXTENDED":
        # Encryption modulo Q*px followed by ScaleAndRoundPOverQ (bfvrns-pke.cpp:182-189,197-200,211-214).
        # fhe_check computes the input noise of a fresh encryption from the trusted model
        # Spec.EncryptBFV.encryptBFV, which describes STANDARD only; no derived number is passed instead.
        raise Fail("ENCRYPTION_TECHNIQUE = EXTENDED: the trusted encryption model (Spec.EncryptBFV.encryptBFV) "
                   "describes STANDARD encryption only, and fhe_check computes the input noise from it; refused "
                   "(use the default STANDARD encryption)")
    else:
        raise Fail(f"encryption technique {enc}")
    return {
        "errorBound": Be, "secretBound": Bs, "inputNoise": inputNoise, "keyNoise": Be,
        "plaintextBound": t - 1, "encodingDeviation": dev, "gaussianPart": E,
        "plainAddDeviation": plain_dev, "encLevels": enc_levels, "plainLevels": plain_levels,
        "derivation": {
            "noiseDefinition": "BFV noise e = [c0 + c1*s - floor(Q/t)*m]_Q (centred), m = the stored plaintext polynomial, coefficients in [0, t)",
            "errorBound": Be,
            "errorBoundSource": f"OpenFHE DGG (Peikert inversion): sigma = 3.19f, |e| <= ceil(sigma*{DGG_TAIL}) = {Be}, "
                                "else OPENFHE_THROW (core/include/math/discretegaussiangenerator-impl.h:81-82,94-99)",
            "encryptionTechnique": enc,
            "inputNoiseFormula": formula,
            "inputNoiseTerms": {"Be*(1+2*N*Bs)": E, "maxEncodingDeviation": dev, "encryptionLevels": enc_levels,
                                **({"extendedPrime": str(p["extendedPrime"])} if enc == "EXTENDED" else {})},
            "inputNoiseSource": "PKEBFVRNS::Encrypt(DCRTPoly, PublicKey) (pke/lib/scheme/bfvrns/bfvrns-pke.cpp:167-223): "
                                "EncryptZeroCore (pke/lib/schemerns/rns-pke.cpp:152-200: c0 = pk0*v + ns*e0, c1 = pk1*v + ns*e1, v from the "
                                "ternary generator, ns = 1), pk = (ns*e - a*s, a) (bfvrns-pke.cpp:88-90); then c0 += TimesQovert(ptxt) "
                                "(bfvrns-pke.cpp:204-206; core/include/lattice/hal/default/dcrtpoly-impl.h:918-935: every residue x -> "
                                "[x * (-Q mod t)]_t * t^-1 mod q_i, i.e. the integer (Q*m + [-Q*m]_t)/t = ceil(Q*m/t)); EXTENDED: the same modulo "
                                "Q*px with px = PreviousPrime(q_last) (bfvrns-cryptoparameters.cpp:78,97-122; bfvrns-pke.cpp:182-189,197-200), "
                                "then ScaleAndRoundPOverQ on both components (bfvrns-pke.cpp:211-214; dcrtpoly-impl.h:1699-1714; the lift of the "
                                "px-residue is centred: core/lib/math/hal/intnat/mubintvecnat.cpp:217-237)",
            "keyNoiseFormula": "Be: key-switching keys b = -a*s' + e (+ the key material), noise scale 1 "
                               "(pke/lib/keyswitch/keyswitch-hybrid.cpp:91,120,123; keyswitch-bv.cpp:64,98-101)",
            "secret": ("SPARSE_TERNARY: s has 192 nonzero coefficients in {-1, 1} (base-pke.cpp; "
                       "ternaryuniformgenerator-impl.h), so |s| <= 1; the encryption ephemeral v is still uniform ternary "
                       "for every non-GAUSSIAN secret (rns-pke.cpp EncryptZeroCore)"
                       if p["secretKeyDist"] == "SPARSE_TERNARY" else "UNIFORM_TERNARY"),
            "build": (p.get("build") or "ASSUMED (--assume-default-build): WITH_REDUCED_NOISE=OFF, NATIVEINT=64"),
            "keyProvenance": ("ASSUMED (--assume-single-party-keys): every key is a single-party key of one ternary "
                              "secret generated by KeyGen/EvalMultKeyGen/EvalRotateKeyGen; NOT checked from the trace"
                              if assume_keys else
                              "checked from the trace: every Encrypt key comes from one traced single-party "
                              "CryptoContext::KeyGen(); every relinearization/rotation key used was generated from its "
                              "secret key by a traced EvalMultKeyGen/EvalMultKeysGen/rotation-key generation for the "
                              "index used; no multiparty, proxy re-encryption or key-switching call in the trace"),
            "plaintextBound": "t-1: packed encoding lifts every coefficient of the inverse-NTT'd slot vector to [0, t) and stores the same "
                              "integer in every limb (pke/lib/encoding/packedencoding.cpp:74-86,115-131); EvalMult(ct, pt) multiplies every "
                              "component by that polynomial (pke/lib/schemerns/rns-leveledshe.cpp:263-278, NORESCALE branch), and "
                              "EvalAdd/EvalSub(ct, pt) add TimesQovert of it (bfvrns-leveledshe.cpp:56-96)",
            "openfheVersion": VERSION,
        },
    }


# Calls the BFV extractor refuses by name: the BGV table (extract.UNMODELLED_CALLS: EvalSum and
# EvalInnerProduct, which OpenFHE >= 1.6 fuses; EvalFastRotation; the *Mutable products; EvalMerge)
# without Compress, which BFV maps, plus the componentwise tensor product of CryptoContext.
BFV_UNMODELLED = {k: v for k, v in UNMODELLED_CALLS.items() if k != "CryptoContext::Compress"}
BFV_UNMODELLED["CryptoContext::EvalMultNoRelinNoCheck"] = (
    "EvalMultNoRelinNoCheck multiplies the components directly (cryptocontext.h, CryptoContextImpl::"
    "EvalMultNoRelinNoCheck): for BFV that is not the scale-invariant product (no scaling by t/Q); use EvalMult or "
    "EvalMultNoRelin")

RELIN_CORE = "LeveledSHEBFVRNS::RelinearizeCore(Ciphertext,EvalKey)"


class Extractor(BGVExtractor):
    """The BGV extractor's value tracking (SSA names), key provenance (KeyGen / EvalMultKeyGen /
    rotation-key generation, one secret) and plaintext-encoding check, with the BFV instruction
    mapping in walk()."""

    def __init__(self, p, assume_fresh, assume_keys):
        super().__init__(p["t"], assume_fresh, assume_keys, None)
        self.p = p
        self.L = len(p["qs"])
        self.tech = p["multiplicationTechnique"]
        self.drops = {"mul": [], "keySwitch": []}
        self.mul_levels = set()
        self.coefpacked = set()  # ids of the CoefPacked plaintexts the program uses (check_packed)
        # Variables holding the unrelinearised output of a BFV product (the no-key
        # LeveledSHEBFVRNS::EvalMult / EvalSquare, bfvrns-leveledshe.cpp:200-433, :435-704), and sums,
        # differences and negations of such values only. The library keeps their components in
        # COEFFICIENT representation (:367, :384, :393, :410, :686); every other ciphertext is in
        # EVALUATION representation. Rule (PRODUCT_RULE): such a value may only be added to or
        # subtracted from another such value, negated, or relinearized; any other use, in particular
        # combining it with an ordinary ciphertext or a plaintext, is refused. These are the
        # combinations confirmed on real runs of v1.6.1 to decrypt to the computed message (and to
        # pass the trusted step contract in harness/openfhe-pin); everything else is not supported.
        self.unrelin = set()

    PRODUCT_ALLOWED = ("add", "sub", "relin")

    def product_rule(self, node, op, kw):
        srcs = [kw[k] for k in ("a", "b", "p") if k in kw]
        hit = [v for v in srcs if v in self.unrelin]
        if not hit:
            return False
        neg = op == "mulConst" and str(kw.get("c")) == "-1"
        if not (op in self.PRODUCT_ALLOWED or neg) or (op in ("add", "sub") and len(hit) != len(srcs)):
            raise Fail(f"line {node['line']}: {node['fn']}: operand {hit[0]} is the unrelinearised output of a BFV "
                       f"product (EvalMultNoRelin, or EvalMult/EvalSquare without a key); `{op}` of it"
                       f"{' with an operand that is not such a product' if op in ('add', 'sub') else ''} is not "
                       "supported (relinearize the product first)")
        return op != "relin"

    def emit(self, node, op, extra=None, **kw):
        stays = self.product_rule(node, op, kw)
        super().emit(node, op, **kw)
        if extra:
            self.prov[-1].update(extra)
        if stays or (op in ("mul", "square") and node["fn"] in (
                "LeveledSHEBFVRNS::EvalMult(Ciphertext,Ciphertext)", "LeveledSHEBFVRNS::EvalSquare(Ciphertext)")):
            self.unrelin.add(kw["dst"])

    def walk_top(self, node):
        scan_refused(node, BFV_UNMODELLED)
        self.record_keys(node)
        self.walk(node)

    def drop(self, node, rec, towers, nsd, key_switch):
        """The limbs HPSPOVERQLEVELED drops internally for an operation on a full-size ciphertext
        whose noiseScaleDeg argument is `nsd` (levels = nsd - 1): the library's own table
        (params.json levelsToDrop), which must equal the value the library recorded at run time
        (trace: the int input "levelsDropped" of `rec`, hooked where FindLevelsToDrop is called)."""
        seen = ints(rec, "levelsDropped")
        if self.tech != "HPSPOVERQLEVELED" or towers != self.L:
            if seen:
                raise Fail(f"line {rec['line']}: {rec['fn']} recorded an internal drop where the extractor expects none")
            return {}
        tab = self.p["levelsToDrop"]["keySwitch" if key_switch else "mul"]
        if not 1 <= nsd <= len(tab):
            raise Fail(f"line {node['line']}: noiseScaleDeg {nsd} is outside the dumped FindLevelsToDrop table")
        d = tab[nsd - 1]
        if len(seen) != 1:
            raise Fail(f"line {rec['line']}: {rec['fn']}: the internal drop of HPSPOVERQLEVELED is not recorded in the "
                       "trace (a tracer without the levelsDropped hook?)")
        if seen[0] != d:
            raise Fail(f"line {rec['line']}: {rec['fn']} dropped {seen[0]} limbs, the FindLevelsToDrop table of "
                       f"params.json says {d}")
        self.drops["keySwitch" if key_switch else "mul"].append(d)
        return {"internalDrop": d, "internalLimbs": self.L - d,
                "findLevelsToDrop": {"levels": nsd - 1, "keySwitch": key_switch}}

    def check_packed(self, node, p):
        """The encodings whose STORED polynomial has every coefficient in [0, t), the same integer
        in every limb: what the bound t - 1 of a plaintext operand (Spec.TraceBFV.PlainOK: any
        representative congruent to the message mod t within the declared bound) and the encoding
        deviation ceil((Q mod t)*m/t) of Encrypt / EvalAdd(ct, pt) assume.
          packed      PackedEncoding lifts every coefficient to [0, t) (packedencoding.cpp:74-86,115-131).
          coefpacked  for BFVRNS, CoefPackedEncoding stores a value v in (-t/2, t/2] as v if v >= 0 and
                      as t - |v| if v < 0 (pke/lib/encoding/coefpackedencoding.cpp:46-70, the
                      isBFVRNS branch :58-61; any other value throws, :53-55), then multiplies by
                      scalingFactorInt (:77-90), which no BFV code sets: accepted only if the trace
                      records scalingFactorInt = 1 (then the multiplication is the identity for
                      every noiseScaleDeg). This is the BFV branch only: under BGV a negative value is
                      stored as q - |v| and FLEXIBLEAUTO(EXT) scales it without reduction mod t, so
                      extract.py refuses CoefPacked; this method is not used for BGV contexts.
        Every other encoding (string, unrecorded) is refused. (The name is the BGV extractor's
        hook: extract.Extractor.walk calls self.check_packed for every plaintext it meets.)"""
        enc = p.get("enc")
        if enc == "packed":
            return
        if enc == "coefpacked":
            if p.get("sf") is None or int(p["sf"]) != 1:
                raise Fail(f"line {node['line']}: CoefPacked plaintext {p['id']} has scalingFactorInt {p.get('sf', 'unrecorded')}: "
                           "its coefficients are in [0, t) only for scalingFactorInt = 1 (coefpackedencoding.cpp:77-90 multiplies "
                           "the encoded polynomial by it without reduction mod t)")
            self.coefpacked.add(p["id"])
            return
        raise Fail(f"line {node['line']}: plaintext {p['id']} has encoding {enc or 'unrecorded'}: only packed and CoefPacked "
                   "plaintexts are mapped (the bound t-1 and the encoding deviation are derived for a stored polynomial with "
                   "coefficients in [0, t))")

    def mult_key(self, node, rec):
        """Key provenance of the relinearization key used by RelinearizeCore `rec`."""
        eks = keys_of(rec["ins"], "ek")
        if len(eks) != 1 and not self.assume_keys:
            raise Fail(f"line {rec['line']}: {rec['fn']}: the relinearization key used is not recorded in the trace")
        if eks:
            self.check_eval_key(node, eks[0], "mult", 0)

    def fresh_shape(self, o):
        """--assume-fresh-inputs: a BFV fresh encryption has 2 parts and noiseScaleDeg 1."""
        if o["parts"] != 2:
            return f"it has {o['parts']} parts"
        if o["nsd"] != 1:
            return f"its noiseScaleDeg is {o['nsd']} (a fresh BFV encryption has 1: it is the result of a product)"
        return None

    def declare_plain_bfv(self, node, p, towers):
        self.check_packed(node, p)
        self.check_made(node, p)  # a traced Make*Plaintext of this context, unchanged since, this t
        if p["towers"] != towers:
            raise Fail(f"line {node['line']}: plaintext {p['id']} has {p['towers']} limbs, the ciphertext {towers} "
                       f"(plaintexts encoded at fewer limbs are not mapped)")
        name = p["id"]
        if name not in self.inputs:
            self.inputs[name] = {"name": name, "parts": 1, "level": p["towers"], "key": 1,
                                 "bound": str(self.t - 1), "origin": {"openfhe": p["id"]}}
            self.order.append(name)
        return name

    def walk(self, node):
        fn = node["fn"]
        name = base(fn)
        ins, outs = cts(node["ins"]), cts(node["outs"])

        if name.startswith("CryptoContext::Encrypt"):
            if keys_of(node["ins"], "sk"):
                raise Fail(f"line {node['line']}: {fn}: encryption with the PRIVATE key is not mapped for BFV (the input "
                           "noise bound is derived for PKEBFVRNS::Encrypt with a public key)")
            # key provenance, packed encoding, the input declaration (BGV extractor)
            super().walk(node)
        elif (name.startswith("CryptoContext::Make") or name.startswith("CryptoContext::Decrypt")
              or (name.startswith("CryptoContext::") and "KeyGen" in name) or name.startswith("CryptoContext::KeysGen")
              or name in ("LeveledSHEBase::EvalAddCoreInPlace", "LeveledSHEBase::EvalSubCoreInPlace")):
            super().walk(node)
        elif fn == "LeveledSHEBFVRNS::EvalMult(Ciphertext,Ciphertext)":
            # the scale-invariant product (bfvrns-leveledshe.cpp:200-433); 2 + 2 parts give 3
            self.need(node, ins, 2)
            if ins[0]["towers"] != ins[1]["towers"]:
                raise Fail(f"line {node['line']}: EvalMult of operands with different numbers of limbs")
            a, b = self.use(ins[0]), self.use(ins[1])
            x = self.drop(node, node, ins[0]["towers"], max(ins[0]["nsd"], ins[1]["nsd"]), False)  # :263-272
            self.mul_levels.add(ins[0]["towers"] - x.get("internalDrop", 0))
            self.emit(node, "mul", x, dst=self.define(self.out(node, outs)), a=a, b=b)
        elif fn == "LeveledSHEBFVRNS::EvalSquare(Ciphertext)":
            self.need(node, ins, 1)
            a = self.use(ins[0])
            x = self.drop(node, node, ins[0]["towers"], ins[0]["nsd"], False)                      # :486-492
            self.mul_levels.add(ins[0]["towers"] - x.get("internalDrop", 0))
            dst = self.define(self.out(node, outs))
            if self.tech in ("HPSPOVERQ", "HPSPOVERQLEVELED"):
                # The P-over-Q squaring lifts the SAME operand in two different ways (cv by
                # ExpandCRTBasis, cvPoverQ by FastExpandCRTBasisPloverQ) and multiplies
                # cv[i]*cvPoverQ[j]: it is the two-operand product of x with x, not the `square`
                # contract (one lift). Emitted as mul x x (same message, same bound).
                x = {**x, "note": "EvalSquare under a P-over-Q technique: two different lifts of the operand "
                                  "(bfvrns-leveledshe.cpp:459-524,626-636), emitted as mul a a"}
                self.emit(node, "mul", x, dst=dst, a=a, b=a)
            else:
                self.emit(node, "square", x, dst=dst, a=a)
        elif fn == RELIN_CORE:
            # bfvrns-leveledshe.cpp:856-900. With 3 parts: relinearization of c2 (FindLevelsToDrop with
            # keySwitch = false). With 2 parts it is the key switch inside EvalAutomorphism, which is
            # translated at EvalAutomorphism and never reached here.
            self.need(node, ins, 1)
            if ins[0]["parts"] != 3:
                raise Fail(f"line {node['line']}: RelinearizeCore of a {ins[0]['parts']}-part ciphertext outside "
                           "EvalAutomorphism: OpenFHE key-switches only the third component and drops the rest, so the "
                           "result is not an encryption of the product (relinearize the operand first)")
            self.mult_key(node, node)
            a = self.use(ins[0])
            x = self.drop(node, node, ins[0]["towers"], ins[0]["nsd"], False)
            self.emit(node, "relin", x, dst=self.define(self.out(node, outs)), a=a)
        elif name in ("LeveledSHEBase::Relinearize", "LeveledSHEBase::RelinearizeInPlace"):
            if node["kids"]:
                # Relinearize calls RelinearizeInPlace on a clone: translate the inner call only.
                for k in node["kids"]:
                    self.walk(k)
                self.use(self.out(node, outs))
                return
            # pke/lib/schemebase/base-leveledshe.cpp:315-329: KeySwitchCore on c2 at the ciphertext's own
            # level (no internal drop, also under HPSPOVERQLEVELED)
            self.need(node, ins, 1)
            parts = ins[0]["parts"]
            if parts != 3:
                raise Fail(f"line {node['line']}: {fn} of a {parts}-part ciphertext: only 3 parts are mapped")
            eks = keys_of(node["ins"], "ek")
            if len(eks) != 1 and not self.assume_keys:
                raise Fail(f"line {node['line']}: {fn}: the relinearization key used is not recorded in the trace")
            for j, ek in enumerate(eks):
                self.check_eval_key(node, ek, "mult", j)
            a = self.use(ins[0])
            self.emit(node, "relin", {"internalDrop": 0} if self.tech == "HPSPOVERQLEVELED" else None,
                      dst=self.define(self.out(node, outs)), a=a)
        elif name == "LeveledSHEBFVRNS::EvalAutomorphism":
            # bfvrns-leveledshe.cpp:744-757: RelinearizeCore with the automorphism key (a key switch of
            # the 2-part ciphertext: FindLevelsToDrop with keySwitch = true), THEN the permutation.
            # The phase effect equals automorph;keySwitch: X -> X^g is an isometry of the infinity norm.
            self.need(node, ins, 1)
            if ins[0]["parts"] != 2:
                raise Fail(f"line {node['line']}: EvalAutomorphism of a {ins[0]['parts']}-part ciphertext")
            core = [k for k in node["kids"] if k["fn"] == RELIN_CORE]
            if len(core) != 1 or len(node["kids"]) != 1:
                raise Fail(f"line {node['line']}: {fn}: expected exactly one traced RelinearizeCore (the key switch)")
            (g,) = ints(node, "index")
            eks = keys_of(core[0]["ins"], "ek")
            if len(eks) != 1 and not self.assume_keys:
                raise Fail(f"line {node['line']}: {fn}: the rotation key used is not recorded in the trace")
            if eks:
                self.check_eval_key(node, eks[0], "auto", g)
            a = self.use(ins[0])
            x = self.drop(node, core[0], ins[0]["towers"], ins[0]["nsd"], True)
            mid = self.fresh(a + "@" + str(g))
            self.defined[mid] = None
            self.emit(node, "automorph", dst=mid, a=a, g=g)
            self.emit(node, "keySwitch", x, dst=self.define(self.out(node, outs)), a=mid)
        elif name in ("LeveledSHEBase::EvalNegate", "LeveledSHEBase::EvalNegateInPlace"):
            self.need(node, ins, 1)
            a = self.use(ins[0])
            self.emit(node, "mulConst", dst=self.define(self.out(node, outs)), a=a, c="-1")
        elif fn in ("LeveledSHEBFVRNS::EvalAddInPlace(Ciphertext,Plaintext)",
                    "LeveledSHEBFVRNS::EvalSubInPlace(Ciphertext,Plaintext)",
                    "LeveledSHERNS::EvalMultInPlace(ciphertext, plaintext)"):
            # EvalAdd/EvalSub: c0 +-= TimesQovert(p) (bfvrns-leveledshe.cpp:56-96); EvalMult: NORESCALE
            # branch, every component times the plaintext element (rns-leveledshe.cpp:263-278)
            pts = pts_of(node["ins"])
            if len(ins) != 1 or len(pts) != 1:
                raise Fail(f"line {node['line']}: {fn}: expected one ciphertext and one plaintext")
            a = self.use(ins[0])
            pname = self.declare_plain_bfv(node, pts[0], ins[0]["towers"])
            op = "addPlain" if "EvalAdd" in fn else "subPlain" if "EvalSub" in fn else "mulPlain"
            self.emit(node, op, dst=self.define(self.out(node, outs)), a=a, p=pname)
        elif name == "LeveledSHEBFVRNS::Compress":
            # bfvrns-leveledshe.cpp:902-932: DropLastElementAndScale of every component, once per
            # dropped limb: c -> (c - [c]_{q_last})/q_last with [c] centred = round(c/q_last)
            self.need(node, ins, 1)
            (left,) = ints(node, "towersLeft")
            k = ins[0]["towers"] - left
            cur = self.use(ins[0])
            if k < 0:
                raise Fail(f"line {node['line']}: Compress to more limbs than the ciphertext has")
            o = self.out(node, outs)
            if k == 0:
                self.emit(node, "copy", dst=self.define(o), a=cur)
            for j in range(k):
                if j == k - 1:
                    dst = self.define(o)
                else:
                    dst = self.fresh(cur)
                    self.defined[dst] = None
                self.emit(node, "modSwitch", dst=dst, a=cur)
                cur = dst
        else:
            # Wrappers (CryptoContext::*, LeveledSHERNS::*, the *EvalKey variants of EvalMult and
            # EvalSquare): recurse. A wrapper whose ciphertext output is not produced by a recognised
            # sub-call is an error (EvalMultCoreInPlace with a constant, an untraced core, ...).
            for k in node["kids"]:
                self.walk(k)
            in_ids = {o["id"] for o in ins}
            for o in outs:
                if o["id"] in in_ids:
                    self.use(o)
                    continue
                if self.cur.get(o["id"]) is None:
                    raise Fail(f"line {node['line']}: {fn} outputs {o['id']} via an operation "
                               f"the extractor does not understand")


def replay(ex):
    """Replay levels and parts through the extracted program (the rules of Spec.Source.step) and
    compare them with OpenFHE's own towers/parts per ciphertext."""
    lev, parts, mism = {}, {}, []
    for i, d in ex.inputs.items():
        lev[i], parts[i] = d["level"], d["parts"]
    for ins in ex.body:
        a, d, op = ins["a"], ins["dst"], ins["op"]
        lev[d] = lev[a] - (1 if op == "modSwitch" else 0)
        if op in ("mul", "square"):
            parts[d] = parts[a] + parts[ins.get("b", a)] - 1
        elif op == "relin":
            parts[d] = 2
        elif op in ("add", "sub"):
            parts[d] = max(parts[a], parts[ins["b"]])
        else:
            parts[d] = parts[a]
        rec = ex.defined.get(d)
        if rec is not None:
            ins["expect"] = {"level": rec["towers"], "parts": rec["parts"]}
            if rec["towers"] != lev[d]:
                mism.append(f"{d}: Source level {lev[d]} != OpenFHE towers {rec['towers']}")
            if rec["parts"] != parts[d]:
                mism.append(f"{d}: Source parts {parts[d]} != OpenFHE parts {rec['parts']}")
    return mism, lev


def key_switching(p):
    L = len(p["qs"])
    if p["keySwitch"] == "HYBRID":
        if not p["special"]:
            raise Fail("HYBRID key switching without special primes")
        return {
            "method": "hybrid",
            # canonical-representative fast base conversion in ModUp, as for BGV
            "variant": "openfhe",
            "digits": {"kind": "consecutive", "towersPerDigit": p["towersPerDigit"], "dnum": p["dnum"]},
            "source": "KeySwitchHYBRID (pke/lib/keyswitch/keyswitch-hybrid.cpp): keys b = -a*s' + e + P*s on the digit's limbs, noise scale 1 "
                      "(:91-123); digit j at l limbs = limbs [j*alpha, min((j+1)*alpha, l)), numPartQl = ceil(l/alpha) (:300-314); ModUp by the "
                      "canonical-representative fast base conversion; ModDown is ApproxModDown with t = 0 (:256-269: noise scale 1), i.e. "
                      "(X - FastBConv([X]_P))/P without the BGV t-correction. Under HPSPOVERQLEVELED the switch runs on the first "
                      "L - internalDrop limbs and the result is multiplied by Q/Q_l (provenance: internalDrop)",
        }
    if p["digitSizeBV"] != 0:
        raise Fail(f"UNSUPPORTED: BV key switching with digit size {p['digitSizeBV']} != 0 (base-2^w digits) is not mapped")
    return {
        "method": "hybrid",
        # the digit of limb i is the centred representative of [c]_{q_i}
        "variant": "centred",
        "digits": {"kind": "consecutive", "towersPerDigit": 1, "dnum": L},
        "technique": "BV",
        "source": "KeySwitchBV with digit size 0 (CRT digits), MODELLED as hybrid key switching with no special prime (P = 1) and one limb "
                  "per digit: the key of limb i is b_i = F_i*s' - (a_i*s + e_i), F_i*s' = s' on limb i and 0 on the others, i.e. the CRT "
                  "idempotent (Q/q_i)*[(Q/q_i)^-1]_{q_i} times s' (pke/lib/keyswitch/keyswitch-bv.cpp:93-103); the digits are "
                  "CRTDecompose(0): digit i = the residue [c]_{q_i}, extended to the other limbs by NativeVector::SwitchModulus, which "
                  "maps v > q_i/2 to v - q_i: the CENTRED representative (keyswitch-bv.cpp:251-255; "
                  "core/include/lattice/hal/default/dcrtpoly-impl.h:249-273; core/lib/math/hal/intnat/mubintvecnat.cpp:191-215); the result "
                  "is sum_i digit_i*(b_i, a_i) with the keys truncated to the ciphertext's limbs (keyswitch-bv.cpp:257-330). Error: "
                  "sum_i digit_i*e_i, |.| <= N*Be*sum_i q_i/2; there is no ModDown (the hybrid formula's rounding term with P = 1 "
                  "over-approximates). Under HPSPOVERQLEVELED the switch runs on the first L - internalDrop limbs and the result is "
                  "multiplied by Q/Q_l (provenance: internalDrop)",
    }


def multiplication(p, ex, idealised=False):
    tech = p["multiplicationTechnique"]
    L = len(p["qs"])
    out = {"technique": tech}
    if tech == "BEHZ":
        bsk = [str(x) for x in p["behzBsk"]]
        if len(bsk) != L + 1:
            raise Fail("BEHZ: expected sizeQ + 1 moduli in Bsk")
        out.update(auxBasis=bsk[:-1], mSk=bsk[-1], mTilde=str(MTILDE), floatTolerant=False,
                   gamma=str(p["behzGamma"]),
                   source="BEHZ (Bajard-Eynard-Hasan-Zucca): base B = sizeQ primes PreviousPrime below q_last, m_sk the next one (enlarged "
                          "until B*m_sk >= 2*N*t*Q), read from GetModuliBsk() = B u {m_sk} "
                          "(pke/lib/scheme/bfvrns/bfvrns-cryptoparameters.cpp:661-703); m~ = 2^16 is a constant with no accessor "
                          "(pke/include/schemerns/rns-cryptoparameters.h:1927; dcrtpoly-impl.h:1727); EvalMult: FastBaseConvqToBskMontgomery, "
                          "tensor in Q u Bsk, FastRNSFloorq, FastBaseConvSK (bfvrns-leveledshe.cpp:302-323,406-427); integer arithmetic only. "
                          "gamma (decryption only) = 2^26 (rns-cryptoparameters.h:2014)")
    else:
        aux = [str(x["q"]) for x in p["auxR"]]
        want = L + 1 if tech == "HPS" else L
        if len(aux) != want:
            raise Fail(f"{tech}: expected {want} auxiliary primes, params.json has {len(aux)}")
        out.update(auxBasis=aux, floatTolerant=not idealised)
        common = ("auxiliary primes R = PreviousPrime chain below q_last, read from GetParamsRl "
                  "(pke/lib/scheme/bfvrns/bfvrns-cryptoparameters.cpp:78-79,128-142); the base extensions and the scaling use "
                  "double-precision estimates of the overflow/quotient (dcrtpoly-impl.h ExpandCRTBasis/SwitchCRTBasis/ScaleAndRound with the "
                  "*Frac tables and m_qInv, bfvrns-cryptoparameters.cpp:263-289)")
        if tech == "HPS":
            out["source"] = ("HPS (Halevi-Polyakov-Shoup): sizeQ + 1 " + common + "; EvalMult: ExpandCRTBasis of both operands to Q u R, "
                             "tensor, ScaleAndRound by t/Q into R, SwitchCRTBasis R -> Q (bfvrns-leveledshe.cpp:224-237,364-379)")
        else:
            out["auxBasisRule"] = "prefix"
            out["source"] = (tech + ": sizeQ " + common + "; a multiplication on k limbs uses P_k = the FIRST k primes of auxBasis "
                             "(m_paramsRl[k-1], bfvrns-cryptoparameters.cpp:243-255): operand 1 is ExpandCRTBasis'd to Q_k u P_k, operand 2 is "
                             "switched Q -> P_k (scaled by P_k/Q) and extended, tensor, ScaleAndRound by t/P_k into Q_k "
                             "(bfvrns-leveledshe.cpp:238-262,380-390)")
        if tech == "HPSPOVERQLEVELED":
            mx = {k: max(v, default=0) for k, v in ex.drops.items()}
            # two maxima: FindLevelsToDrop's keySwitch flag gives different drops
            out["maxInternalDrop"] = mx["mul"]          # EvalMult, EvalSquare, relinearization of 3 components
            out["maxInternalDropKS"] = mx["keySwitch"]  # 2-component key switches (rotations)
            # what the budget reads: the drop of every instruction of the body, in order
            drops = [pr.get("internalDrop", 0) for pr in ex.prov]
            if len(drops) != len(ex.body) or [pr["index"] for pr in ex.prov] != list(range(len(ex.body))):
                raise Fail("internal error: the provenance list does not have one entry per instruction")
            if (max([d for d, i in zip(drops, ex.body) if i["op"] != "keySwitch"], default=0) != mx["mul"]
                    or max([d for d, i in zip(drops, ex.body) if i["op"] == "keySwitch"], default=0) != mx["keySwitch"]
                    or any(d and i["op"] not in ("mul", "square", "relin", "keySwitch") for d, i in zip(drops, ex.body))):
                raise Fail("internal error: the per-instruction internal drops disagree with the drops recorded while walking the trace")
            out["internalDrops"] = drops
            out["source"] += ("; LEVELED: on a ciphertext with all L limbs the library first drops d = FindLevelsToDrop(noiseScaleDeg - 1, "
                              "params, MSB(q_0), keySwitch) limbs (bfvrns-leveledshe.cpp:98-198): EvalMult/EvalSquare scale operand 1 by "
                              "Q_l/Q with rounding (ScaleAndRound), multiply on l = L - d limbs with P_l and expand the result by Q/Q_l "
                              "(ExpandCRTBasisQlHat) (:263-301,391-405,485-524,667-681); RelinearizeCore scales c2 (or c1 for a rotation) by "
                              "Q_l/Q, key-switches on l limbs and multiplies the result by Q/Q_l (:869-889); keySwitch = true only for the "
                              "2-part (rotation) case (:860,874). internalDrops lists d for every instruction of program.body (0 where the library drops nothing), "
                              "each equal to the value the library recorded at run time, to its dumped FindLevelsToDrop table and to a Python replica; "
                              "maxInternalDrop is the largest d over the traced multiplications, squarings and relinearizations of 3 components, "
                              "maxInternalDropKS the largest over the traced 2-component key switches (rotations) (cross-checks); the "
                              "per-operation values are also in provenance[].internalDrop. A ciphertext with fewer than L limbs (after Compress) "
                              "is multiplied as HPSPOVERQ at its own level, with no drop (:238-239)")
    if idealised and tech != "BEHZ":
        out["source"] = ("--idealised: floatTolerant = false declares the IDEALISED exact algorithm (every base extension and scaling "
                         "computed exactly), which is NOT what the library runs: its binary64 estimates can be off. " + out["source"])
    out["mulLimbs"] = sorted(ex.mul_levels)
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--params", required=True)
    ap.add_argument("--trace", required=True)
    ap.add_argument("--outputs")
    ap.add_argument("--outputs-from-decrypt", action="store_true")
    ap.add_argument("--artifact", default="")
    ap.add_argument("--assume-fresh-inputs", action="store_true")
    ap.add_argument("--assume-single-party-keys", action="store_true")
    ap.add_argument("--assume-default-build", action="store_true")
    ap.add_argument("--idealised", action="store_true")
    args = ap.parse_args()
    p = json.load(open(args.params))

    def fail(msg):
        print(json.dumps({"format": "fhe-check/v1", "error": msg}, indent=2))
        sys.exit(1)

    try:
        check_tracer(args.params, args.trace, p)  # first: a stale tracer's output is not read further
    except Fail as e:
        fail(str(e))
    if p.get("scheme") != "BFV":
        fail("not a BFV context")
    try:
        # parameter-only refusals first
        noise_inputs(p, assume_keys=args.assume_single_party_keys, assume_build=args.assume_default_build)
        ks = key_switching(p)
        # the library's FindLevelsToDrop table (params.json) vs the Python replica
        tab = p["levelsToDrop"]
        bad = [(ksw, d) for ksw in (False, True) for d in range(len(tab["mul"]))
               if find_levels_to_drop(p, d, tab["dcrtBits"], ksw) != tab["keySwitch" if ksw else "mul"][d]]
        if bad and p["multiplicationTechnique"] == "HPSPOVERQLEVELED":
            raise Fail(f"FindLevelsToDrop: the Python replica disagrees with the library at (keySwitch, levels) = {bad[:4]}")
        ex = Extractor(p, args.assume_fresh_inputs, args.assume_single_party_keys)
        for top in stream_calls(args.trace):
            ex.walk_top(top)
        nz = noise_inputs(p, {d["level"] for d in ex.inputs.values() if d["parts"] == 2},
                          {d["level"] for d in ex.inputs.values() if d["parts"] == 1},
                          args.assume_single_party_keys, args.assume_default_build)
        if not ex.body:
            raise Fail("the trace contains no homomorphic operation")
        mism, lev = replay(ex)
        if mism:
            raise Fail("frontend cross-check failed: " + "; ".join(mism))
        mul = multiplication(p, ex, args.idealised)
    except Fail as e:
        fail(str(e))
    except (KeyError, IndexError, ValueError, TypeError) as e:
        # never a silent crash: an unexpected trace shape is an explicit refusal
        fail(f"the trace has a shape the extractor does not handle ({type(e).__name__}: {e}); refused")
    try:
        # every ciphertext the trace decrypts is an output (extract.choose_outputs)
        outputs, out_rule = choose_outputs(ex, args.outputs, args.outputs_from_decrypt)
    except Fail as e:
        fail(str(e))
    # How OpenFHE adds a plaintext. The method ("ceil") is neither of the two the format named
    # first ("delta", "rounded"); bfv.plainAdd is emitted only when the program adds or subtracts a
    # plaintext (a program without such an operation does not depend on it), and the description
    # is always in noiseDerivation.plainAdd.
    plain_add_decl = {
        "method": "ceil",
        "deviationBound": str(nz["plainAddDeviation"]),
        "source": "LeveledSHEBFVRNS::EvalAddInPlace/EvalSubInPlace(Ciphertext, Plaintext) "
                  "(pke/lib/scheme/bfvrns/bfvrns-leveledshe.cpp:56-96) add TimesQovert(p) to c0 "
                  "(core/include/lattice/hal/default/dcrtpoly-impl.h:918-935): residue-wise [p*(-Q mod t)]_t * t^-1 mod q_i, which is "
                  "the integer (Q*p + [-Q*p]_t)/t = CEIL(Q*p/t) for the stored p in [0,t) -- not floor(Q/t)*p ('delta') and not "
                  "the rounding to nearest ('rounded'): ceil(Q*p/t) - floor(Q/t)*p = ceil((Q mod t)*p/t), which exceeds the "
                  "'rounded' deviation floor(((Q mod t)*p + t/2)/t) by one whenever the fractional part of (Q mod t)*p/t lies in "
                  "(0, 1/2). deviationBound = max of ceil((Q_l mod t)*(t-1)/t) over the numbers of limbs l of the plaintext operands "
                  f"of this trace ({nz['plainLevels']}; every level if there is none)",
    }
    plain_add = {"plainAdd": plain_add_decl} if any(i["op"] in ("addPlain", "subPlain") for i in ex.body) else {}
    nz["derivation"]["plainAdd"] = plain_add_decl
    if ex.coefpacked:
        # only when the program uses one (files of packed-only programs are unchanged)
        nz["derivation"]["coefPackedPlaintexts"] = {
            "ids": sorted(ex.coefpacked),
            "source": "CoefPackedEncoding for BFVRNS stores a value v in (-t/2, t/2] as v if v >= 0 and as t - |v| if v < 0 "
                      "(pke/lib/encoding/coefpackedencoding.cpp:46-70, the isBFVRNS branch :58-61; any other value throws, "
                      ":53-55), the same integer in [0, t) in every limb, and multiplies it by scalingFactorInt (:77-90), "
                      "which the trace records as 1 for each of these plaintexts: the plaintext bound t-1 and the encoding "
                      "deviation ceil((Q mod t)*m/t) declared for packed plaintexts hold for them as well",
        }
    L = len(p["qs"])
    compressed = [o for o in outputs if lev.get(o, L) != L]
    doc = {
        "format": "fhe-check/v1",
        "source": {"tool": "openfhe", "artifact": args.artifact, "scheme": "BFVRNS",
                   "multiplicationTechnique": p["multiplicationTechnique"], "keySwitchTechnique": p["keySwitch"],
                   "encryptionTechnique": p["encryptionTechnique"], "multiplicativeDepth": p["multiplicativeDepth"],
                   **({"idealised": True} if args.idealised else {})},
        "params": {
            "scheme": "BFV",
            "N": p["N"],
            "t": p["t"],
            "limbs": [{"q": str(x["q"]), "psi": str(x["psi"])} for x in p["qs"]],
            "special": [{"q": str(x["q"]), "psi": str(x["psi"])} for x in p["special"]],
            "secretBound": nz["secretBound"],
            "inputNoise": str(nz["inputNoise"]),
            "keyNoise": str(nz["keyNoise"]),
        },
        "noiseDerivation": nz["derivation"],
        "keySwitching": ks,
        "modSwitch": {"method": "round",
                      "source": "LeveledSHEBFVRNS::Compress (pke/lib/scheme/bfvrns/bfvrns-leveledshe.cpp:902-932): per dropped limb, "
                                "DropLastElementAndScale of every component (dcrtpoly-impl.h:737-755): (c - [c]_{q_last})/q_last with the "
                                "centred [c]_{q_last} (mubintvecnat.cpp:191-215), i.e. round(c/q_last)"},
        "decryption": {
            "method": "at-output-level",
            "source": "PKEBFVRNS::Decrypt (pke/lib/scheme/bfvrns/bfvrns-pke.cpp:225-278) computes round(t*[c0 + c1*s]_Q/Q) mod t. IDEALISED "
                      "here as the exact rounding at the output's level. What the library does: (a) an output with all L limbs: the RNS "
                      "ScaleAndRound (:238-253), for the HPS techniques with a double-precision sum of the fractional parts "
                      "(dcrtpoly-impl.h:1220-1388; the comments there bound the float error by 1/4), for BEHZ with the gamma-corrected "
                      "integer procedure (dcrtpoly-impl.h:1652-1696; gamma = 2^26); neither is exact rounding when the phase is within "
                      "the procedure's error of a rounding boundary. (b) an output with fewer limbs (after Compress): the PHASE is "
                      "switched down to one limb by DropLastElementAndScale and then rounded with MultiplyAndRound(t, q_0) (:254-275); "
                      "each switch adds at most 1/2 to the phase error, which this declaration does not account for"
                      + (f" (outputs with fewer than L limbs here: {compressed})" if compressed else ""),
        },
        # The fresh public-key encryptions (Spec.EncryptBFV.encryptBFV, STANDARD): fhe_check computes the
        # input noise from these bounds (Challenge.BFVEncrypt.certifyBFVFresh?) and does not use
        # params.inputNoise. ASSUMPTIONS: which inputs are fresh encryptions (traced Encrypt with a public
        # key, or --assume-fresh-inputs) and the hard sampler bounds (pk error, e0, e1 from the DGG,
        # |e| <= Be; v ternary).
        "freshEncryption": {
            "inputs": [i for i in ex.order if ex.inputs[i]["parts"] == 2],
            "keyError": nz["errorBound"], "u": 1, "e1": nz["errorBound"], "e2": nz["errorBound"],
            # sigma = 3.19f (noise_inputs refuses any other)
            "mean": {"num": DGG_MEAN_NUM, "den": DGG_MEAN_DEN, "source": DGG_MEAN_SOURCE},
            "source": "PKEBFVRNS::Encrypt(DCRTPoly, PublicKey), STANDARD (bfvrns-pke.cpp:167-223; rns-pke.cpp:152-200): "
                      "(b*v + e0 + ceil(Q*m/t), a*v + e1), b = e - a*s (bfvrns-pke.cpp:88-90, noise scale 1); v ternary (TUG), "
                      f"e, e0, e1 from the DGG with |e| <= {nz['errorBound']} (discretegaussiangenerator-impl.h:81-82,94-99)",
        },
        "bfv": {
            "multiplication": mul,
            **plain_add,
            "encryption": {
                "technique": p["encryptionTechnique"],
                "inputs": [i for i in ex.order if ex.inputs[i]["parts"] == 2],
                "keyError": nz["errorBound"], "u": 1, "e0": nz["errorBound"], "e1": nz["errorBound"],
                "encoding": "ceil(Q*m/t)", "encodingDeviation": str(nz["encodingDeviation"]),
                **({"extraPrime": str(p["extendedPrime"])} if p["encryptionTechnique"] == "EXTENDED" else {}),
                "source": nz["derivation"]["inputNoiseSource"],
            },
        },
        "program": {
            "inputs": [ex.inputs[i] for i in ex.order],
            "body": ex.body,
            "outputs": outputs,
        },
        "provenance": ex.prov,
        "crossCheck": {"what": "levels and parts replayed vs OpenFHE's own towers/parts per ciphertext; for HPSPOVERQLEVELED the "
                               "library's FindLevelsToDrop table vs the Python replica",
                       "mismatches": mism,
                       "findLevelsToDropReplicaAgrees": not bad},
    }
    if ex.decrypted or args.outputs or args.outputs_from_decrypt:
        doc["crossCheck"]["outputs"] = out_rule
    json.dump(doc, sys.stdout, indent=1)
    print()


if __name__ == "__main__":
    main()
