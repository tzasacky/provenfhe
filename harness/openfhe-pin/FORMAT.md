# openfhe-pin dump format (`openfhe-pin/v1`)

One **case** is one BGV run of upstream OpenFHE v1.6.1 with the frontend's tracer (the exporter
`cpp/pin_export.cpp`, built by `export/build_cpp.sh`). A case is a directory with five files. Everything is exact
integers in decimal; no floating point anywhere except the informational `sigma`.

| file | written by | read by |
|---|---|---|
| `params.json` | exporter (`fhecheck::paramsJson` of `harness/frontend/openfhe/fhecheck-tracer.h`, as `bgv_demo` writes it) | `harness/frontend/openfhe/extract.py` |
| `trace.jsonl` | the frontend's `fhecheck::JsonTracer` itself (`fhecheck-tracer.h`; the exporter subclasses it only to capture every object), attached before `KeyGen` | `extract.py` |
| `prog.fhecheck.json` | `extract.py --params params.json --trace trace.jsonl --artifact <case>` (unmodified, run by the export script as the frontend's tests run it) | Lean checker, through `FHE.Check.Decode` |
| `pin.json` | exporter | Lean checker |
| `polys.txt` | exporter | Lean checker |

If `extract.py` refuses the trace, `prog.fhecheck.json` holds its `{"format": ..., "error": ...}`
object; the case is kept. The checker then requires the refusal to be an expected one (`x.refusal`:
a known message and the reason visible in the data) and still runs the checks a, c, d and
`algo.*` (b, e, f need the program).

## `polys.txt`

One polynomial limb per line, fields separated by single spaces:

```
<name> <limb> <modulus> <c_0> <c_1> ... <c_{N-1}>
```

* `<name>`: no spaces. `<limb>`: 0-based index of the RNS limb, in OpenFHE's tower order (for a
  ciphertext or plaintext: `q_0, q_1, …` of its current towers; for a key over `Q·P`: all `q_i`
  of the full chain, then the special primes `p_0, p_1, …`). The limbs of one name appear on
  consecutive lines, in order.
* `<modulus>` > 0: the limb's modulus; the coefficients are canonical residues in `[0, modulus)`,
  **in coefficient representation** (the exporter copies the element and calls
  `SetFormat(Format::COEFFICIENT)`; `c_i` is the coefficient of `X^i`).
* `<modulus>` = `0`: an exact signed integer polynomial (one line, limb 0): secrets, sampler
  outputs. Coefficients may be negative (`-1`).
* Exactly `N` coefficients per line.

## `pin.json`

```
{
 "format": "openfhe-pin/v1",
 "case": "<directory name>",
 "seed": "<decimal: pin_prng seed of this run>",
 "generator": "<free text: which program / how it was generated>",
 "N": 16, "t": "65537",
 "qs": ["<q_0>", ...],            // full ciphertext chain (same as params.json qs)
 "special": ["<p_0>", ...],
 "scaling": "FIXEDMANUAL" | "FIXEDAUTO" | "FLEXIBLEAUTO" | "FLEXIBLEAUTOEXT",
 "dnum": 3, "towersPerDigit": 1,
 "secret": "s",                   // polys.txt name, modulus-0 line: the secret key, coefficients in {-1,0,1}
 "secretRns": "s.rns",            // the same key as OpenFHE stores it (all its limbs), for a consistency check
 "public": {"b": "pk.b", "a": "pk.a",       // OpenFHE's public key elements [0] and [1], over their limbs
            "e": "pk.e" | null},            // modulus-0: the key-generation error, if captured (how: "randomness")
 "evalKeys": [
   {"kind": "relin",                         // OpenFHE EvalMultKey (s^2 -> s)
    "digits": [{"b": "<name>", "a": "<name>"}, ...]},   // per digit j: OpenFHE's GetBVector()[j], GetAVector()[j]; limbs q_0..q_{L-1}, p_0..p_{k-1}
   {"kind": "rot", "index": 5,               // the automorphism index OpenFHE stores this key under (EvalAutomorphismKey map key)
    "digits": [...]}
 ],
 "encryptions": [
   {"ct": "ct_1", "pt": "pt_1",              // trace ids
    "u": "enc1.u", "e1": "enc1.e1", "e2": "enc1.e2",   // modulus-0 lines; null if not captured
    "randomness": "prng-replay" | "scripted" | "none"} // how (u, e1, e2) were obtained
 ],
 "objects": {
   "ct_1": {"kind": "ct", "towers": 3, "parts": 2, "nsd": 1, "sf": "1", "level": 0,
            "polys": ["ct_1.0", "ct_1.1"],   // polys.txt names of the components c_0, c_1, (c_2)
            "decrypt": {"raw": "ct_1.dec",   // polys.txt line with modulus t: OpenFHE's PKEBGVRNS::Decrypt output (the NativePoly, reduced mod t), before Decode
                        "rawQ0": "ct_1.decq" | null,  // optional: the same NativePoly before reduction mod t, modulus = its own modulus
                        "sf": "<DecryptResult.scalingFactorInt>"}
                       | null},               // null: not decrypted (1-part value, or Decrypt threw: then "decryptError": "<what>")
   "pt_1": {"kind": "pt", "towers": 3, "nsd": 1, "sf": "1", "level": 0,
            "encoding": "packed" | "coefpacked" | "string",   // as the tracer names it ("enc")
            "poly": "pt_1.p"}                // the plaintext's DCRTPoly element, all its limbs: the STORED
                                             // plaintext polynomial that Encrypt adds to c_0
 },
 "build": {"WITH_REDUCED_NOISE": false, "WITH_OPENMP": false, "NATIVEINT": 64, "HAVE_INT128": true, "MATHBACKEND": 4},
                                             // compile-time flags of the OpenFHE binary (they select branches of
                                             // ApproxSwitchCRTBasis / ApproxModDown); informational
 "ksInfo": {"numPartQ": 3, "numPerPartQ": 1,  // cp->GetNumPartQ(), cp->GetNumPerPartQ()
            "perLevel": [{"towers": 1, "numPartitions": 1}, ...]},  // digits OpenFHE itself uses with l towers
 "inputsArbitrary": false,                   // true: the ciphertext inputs are hand-built (adversarial suite), not
                                             // encryptions; the input-noise premise of check f does not hold
 "final": ["ct_9"],                          // ids the program returns
 "notes": ["..."]                            // anything the exporter wants a human to know (e.g. a patch, a skipped item)
}
```

Rules.

* Object ids are exactly the ids in `trace.jsonl` (`ct_<n>`, `pt_<n>`: 64-bit FNV-1a content hashes
  numbered in order of first appearance, by `fhecheck-tracer.h`; key ids `pk_<n>`, `sk_<n>`,
  `ek_<n>` appear in the trace but have no entry in `objects`). **Every** ciphertext and plaintext id that
  appears anywhere in `trace.jsonl` has an entry in `objects`, dumped at its first appearance
  (ids are content hashes, so the content is fixed). This includes the 1-part ciphertexts OpenFHE
  makes from plaintexts (`MorphPlaintext`) and every intermediate the automatic scaling modes
  create.
* `decrypt` is OpenFHE's own decryption of that ciphertext with the secret key
  (`cc->GetScheme()->Decrypt(ct, sk, &raw)` as in `bgv_demo.cpp`), attempted for every ciphertext
  with 2 or 3 parts. It must not appear in `trace.jsonl` and must not disturb the PRNG stream.
* Big integers (`t`, moduli, `sf`, `seed`) are decimal strings. Small structural integers (`N`,
  `towers`, `parts`, `nsd`, `level`, `index`, `dnum`) are JSON numbers.
* Randomness capture (`"prng-replay"`): the exporter snapshots the `pin_prng` state before the
  library call, lets OpenFHE run, rewinds to the snapshot, and draws the same samplers in the same
  order the library does (v1.6.1 `rns-pke.cpp:152-200`: `v` from the ternary generator, then `e0`,
  `e1` from the DGG; `base-pke.cpp:49-103` for key generation: `s`, `a`, `e`, then the key tags),
  then restores the post-call state. The checker never trusts this: it recomputes the ciphertext
  from `(b, a, p, u, e1, e2)` with `Spec.Encrypt.encrypt` (`p` the stored plaintext polynomial)
  and compares with OpenFHE's ciphertext, so a wrong replay shows up as a mismatch.

## Result lines (Lean checker → `results.jsonl`)

One JSON object per line:

```
{"case": "...", "check": "a.textbook" | "a.switched" | "b.eval" | "c.encrypt" | "c.stored" |
                         "d.key" | "e.step" | "f.bound" | "x.refusal" | "algo.relin" | ...,
 "id": "<variable / key / instruction index>", "op": "<instr or kind>",
 "ok": true | false | null,            // null: not checkable, with "why"
 "impl": "literal" | "forced",         // literal trusted definition, or the memoised form
 "measured": "<int>", "bound": "<int>",   // where a bound is involved
 ...check-specific fields (level, depth, parts, N, scaling, why)}
```

## BFV cases (`"scheme": "BFV"`)

A BFV case is one run of a `CryptoContextBFVRNS` of the same OpenFHE build, exported by
`cpp/pin_export_bfv.cpp`; `prog.fhecheck.json` is written by `harness/frontend/openfhe/extract_bfv.py`
(or holds its refusal). The five files, `polys.txt` and the result lines are as above. `pin.json`
has `"scheme": "BFV"` (a file without `scheme` is a BGV case) and differs as follows.

```
{
 "format": "openfhe-pin/v1", "scheme": "BFV",
 "case", "seed", "generator", "N", "t",
 "qs": ["<q_0>", ...],             // the ciphertext chain Q (GetElementParams), all L limbs
 "special": ["<p_0>", ...],        // HYBRID: the key-switching primes P (GetParamsP); BV: []
 "bfv": {
   "mult": "HPS" | "HPSPOVERQ" | "HPSPOVERQLEVELED" | "BEHZ",
   "multDefault": true | false,    // true: SetMultiplicationTechnique was never called
   "ks": "HYBRID" | "BV", "ksDefault": true | false,
   "enc": "STANDARD" | "EXTENDED", "encDefault": true | false,
   "dnum": 2, "towersPerDigit": 1, // HYBRID: GetNumPartQ, GetNumPerPartQ (BV: dnum = L, 1)
   "digitSizeBV": 0,               // BV: GetDigitSize (0: one key per limb, RNS digits only)
   "auxR": ["<r_0>", ...],         // HPS family: the moduli of GetParamsRl() in the library's order
                                   // (HPS: the basis R; P-over-Q: P_k = the first k entries); BEHZ: []
   "behzBsk": ["<b_0>", ..., "<m_sk>"],  // BEHZ: GetModuliBsk() (the base B followed by m_sk); else []
   "behzMtilde": "65536",          // BEHZ: m~ (2^16 in v1.6.1); else "0"
   "behzGamma": "<gamma>",         // BEHZ: the decryption modulus gamma; else "0"
   "extendedPrime": "<p>" | "0",   // EXTENDED encryption: the extra prime; else "0"
   "levelsToDrop": {"dcrtBits": 60, "mul": [...], "keySwitch": [...]},  // as params.json
   "multiplicativeDepth": 2, "maxRelinSkDeg": 2,
   "secretKeyDist": "UNIFORM_TERNARY"
 },
 "secret": "s", "secretRns": "s.rns",
 "public": {"b": "pk.b", "a": "pk.a", "e": "pk.e" | null, "randomness": ...},
                                   // b = e - a*s over Q (noise scale 1, bfvrns-pke.cpp:88-90)
 "evalKeys": [{"kind": "relin" | "rot", "index": g, "digits": [{"b": name, "a": name}, ...]}],
                                   // GetBVector()[j], GetAVector()[j].
                                   // HYBRID: digit j over the limbs q_0..q_{L-1}, p_0..p_{k-1};
                                   //   b_j = -a_j*s + e_j + P*[Qhat_j^-1]*Qhat_j * target (keyswitch-hybrid.cpp:91-123)
                                   // BV, digitSizeBV = 0: digit j over q_0..q_{L-1};
                                   //   b_j = -a_j*s + e_j + (target in limb j, 0 in the others) (keyswitch-bv.cpp:95-102)
                                   // BV, digitSizeBV = w > 0: per limb i, ceil(MSB(q_i)/w) keys, in limb order,
                                   //   key (i, k) holding 2^(w*k)*target in limb i (keyswitch-bv.cpp:70-90);
                                   //   each entry then also has "limb": i, "power": k
 "encryptions": [{"ct", "pt", "u", "e1", "e2", "randomness"}],
                                   // STANDARD (bfvrns-pke.cpp:167-223, rns-pke.cpp:152-200), over the limbs
                                   // of the plaintext's own parameters (a prefix q_0..q_{k-1} of Q):
                                   //   c_0 = b*u + e1 + TimesQovert(p),  c_1 = a*u + e2
                                   // with p the stored plaintext polynomial and TimesQovert(p) the integer
                                   // ceil(Q_k*p/t) coefficientwise (dcrtpoly-impl.h:918-935).
                                   // EXTENDED: (u, e1, e2) are the draws over Q*extendedPrime; the entry has
                                   //   "extended": true and no closed relation is claimed by the exporter
 "objects": {
   "ct_n": {"kind": "ct", "towers", "parts", "nsd", "sf", "level", "polys": [...],
            "decrypt": {"raw": "<name>"} | null},
                                   // raw: polys.txt line with modulus t = PKEBFVRNS::Decrypt's NativePoly
                                   // (bfvrns-pke.cpp:225-278), before Decode; attempted for every ciphertext
                                   // with 2 or 3 parts; "decryptError" if it threw
   "pt_n": {"kind": "pt", "towers", "nsd", "sf", "level", "encoding", "poly": "<name>"}
                                   // the STORED plaintext element (its own limbs, coefficient form),
                                   // NOT multiplied by Q/t
 },
 "build": {..., "float": {"FLT_EVAL_METHOD": 0, "fastMath": false, "fmaContraction": false,
                          "how": "<how each was determined for the OpenFHE library binary>"}},
 "inputsArbitrary": false, "final": [...], "notes": [...]
}
```

Everything a ciphertext-producing traced call returns is in `objects` under its trace id, so the
3-component product inside `EvalMult(ct, ct)` (the nested `LeveledSHEBFVRNS::EvalMult(Ciphertext,
Ciphertext)` call) and the input and output of every `RelinearizeCore`/`EvalAutomorphism` are
dumped. The internal drop of HPSPOVERQLEVELED is the traced `levelsDropped` input of those calls.

### BFV format changes (what `cpp/pin_export_bfv.cpp` writes, where it differs from or adds to the block above)

Field names of the block above are unchanged. Differences, all found while recording real runs:

* **Extra fields** (a reader may ignore them): top-level `dnum`, `towersPerDigit` (copies of
  `bfv.dnum`, `bfv.towersPerDigit`) and `ksInfo` (as for BGV; `perLevel` entries have `towers`,
  `numPartitions`, `digitTowers` only); `bfv.noiseScale` (decimal string, 1); in `build.float`
  besides the three facts and `how`: `cxxFlags`, `fpContract`, `march`, `fmaInstructions`,
  `x87Instructions`, `LDBL_MANT_DIG`; `public.randomness` and an encryption's `randomness` may be
  `"scripted"` (adversarial suite); an evalKeys entry of kind `relin` has `"index": 0`.
* **Rotation keys are keys under the permuted secret.** `evalKeys[kind = rot, index = g]` is OpenFHE's
  `KeySwitchGen(s, s')` with `s' = s(X^(g^-1 mod 2N))` (`base-leveledshe.cpp:419-427`): in the
  three relations of the block above read `b_j = -a_j*s' + e_j + (factor) * s` for a rotation key
  (target `s`, key secret `s'`) and `b_j = -a_j*s + e_j + (factor) * s^2` for the relinearization
  key (target `s^2`, key secret `s`). `LeveledSHEBFVRNS::EvalAutomorphism` key-switches first and
  applies `X -> X^g` afterwards (`bfvrns-leveledshe.cpp:777-849`), so the traced output of the
  inner `RelinearizeCore` (an object like every other) is a ciphertext under `s'`, not under `s`:
  its `decrypt.raw` is OpenFHE's `Decrypt` with `s` of a value that `s` does not decrypt.
* **EXTENDED encryption changes the key material**, not only the encryption: `GetParamsPK` and the
  stored secret are over `Q*r` (`r = extendedPrime`), so `s.rns`, `pk.b`, `pk.a` have `L + 1` limbs
  (`q_0..q_{L-1}, r`); BV evaluation keys are over those `L + 1` limbs and have `L + 1` entries
  (entry `j` = limb `j` of `Q*r`); HYBRID keys are over `Q` then `P` as usual (in every context
  recorded, `r` equals the first special prime). An EXTENDED entry of `encryptions` has
  `"extended": true` and its `(u, e1, e2)` over `Q*r`; the exporter does check a closed relation in
  C++ before recording them: lift the stored plaintext to `Q*r` (CRT), `x0 = b*u + e1 +
  ceil(Q*r*p/t)`, `x1 = a*u + e2` modulo `Q*r`, then `c_i = (x_i - [x_i]_r)/r` with the centred
  `[x_i]_r`, modulo `Q` (`bfvrns-pke.cpp:182-214`; `export/selftest_bfv.py` re-checks it with
  Python integers).
* **`decrypt.raw` is stored exactly as the library returns it** (`"rawReduced": false` in every
  `decrypt` object; the exporter never reduces it). For BEHZ, `DCRTPoly::ScaleAndRound`
  (`dcrtpoly-impl.h:1652-1696`) returns `(s + (s mod 2^26)) >> 26` with `s` in `[0, t*2^26)`, a
  value in `[0, t]`: the library's NativePoly can hold the non-canonical value `t` (where the
  result is 0 mod t). A `raw` line is therefore a modulus-`t` line when every coefficient is below
  `t`, and otherwise an exact integer line (`<modulus>` = 0, values in `[0, t]`); `notes` counts
  such coefficients. (Fixtures made before this change stored them reduced mod `t` and had no
  `rawReduced` field.)
* **`"decryptTables"`** (top level; `null` for BEHZ contexts, which do not compute them:
  `bfvrns-cryptoparameters.cpp:128` guards the block with `multTech != BEHZ`, and a note says so):
  `{"t": "<t>", "qs": [...], "intLo": [...], "fracLo": [...], "intHi": [...], "fracHi": [...]}`, read
  from the context with `GettQHatInvModqDivqModt`, `GettQHatInvModqDivqFrac`,
  `GettQHatInvModqBDivqModt`, `GettQHatInvModqBDivqFrac` (`bfvrns-cryptoparameters.cpp:432-481`, the
  tables of `Spec/DecryptBFV.lean` `tables`). Integers as decimal strings; the doubles as 16 hex
  digits, their IEEE-754 bit pattern (big-endian hex of the 64-bit word). `intHi`/`fracHi` are `[]`
  when the library leaves them empty (no split path: `qMSB + MSB(sizeQ) < 52`).
* **`"timesQovert": "encK.tqt"`** on every `encryptions` entry: the library's own `TimesQovert` of the
  stored plaintext, computed by the exporter with the same calls as `PKEBFVRNS::Encrypt`
  (`bfvrns-pke.cpp:176-205`; untraced, no PRNG draw): over the plaintext's own limbs (STANDARD;
  `NegQModt(level)` of its level), or of the plaintext CRT-lifted to `Q*r` (EXTENDED); coefficient
  form, all limbs. Equals `ceil(Q'*p/t) mod q_i` with `Q'` the product of its limbs
  (`export/selftest_bfv.py` checks this and recomputes `decryptTables`).
* **`decrypt.raw` is not exact rounding of the phase.** For the HPS family and `t` not a power of
  two the library adds the binary64 sum of fractional parts to an integer sum of up to about 2^49
  before rounding (`dcrtpoly-impl.h:1356-1480`), so `raw` differs from `round(t*phase/Q) mod t`
  when `t*phase/Q` is close to a rounding boundary (distances observed: see
  `fixtures/README-bfv.md`; the library's comments claim an error below 1/4). It shows on
  ciphertexts whose phase is not close to a multiple of `Q/t`: the rotation intermediates above
  and outputs whose noise overflowed.
* **Optional decryption intermediates** (new fields; a reader of the block above is unaffected). Inside
  every `decrypt` object:
  * `"phase": "<id>.phase" | null`: the DCRTPoly `c0 + c1*s (+ c2*s^2)` over the ciphertext's own limbs,
    coefficient form, i.e. the output of `PKERNS::DecryptCore` right before the scale-and-round. The
    scheme's `DecryptCore` is not reachable from outside, so the exporter RECOMPUTES it with the
    library's own DCRTPoly calls in the same order (`rns-pke.cpp:202-221`) and then replays the rest
    of `PKEBFVRNS::Decrypt` on it; `phase` is exported only if that replay returns exactly the
    library's NativePoly (else `null` and a note). No case recorded so far has `null`.
  * `"branch": "hps-float" | "behz-gamma" | "compressed"`: which branch of `PKEBFVRNS::Decrypt`
    (`bfvrns-pke.cpp:238-275`) ran: all `L` limbs and an HPS-family technique
    (`DCRTPoly::ScaleAndRound` with the binary64 tables), all `L` limbs and BEHZ (the integer
    gamma-corrected `ScaleAndRound`), fewer than `L` limbs (any technique).
  * `"switched": "<id>.sw"` (branch `compressed` only): the one-limb polynomial (modulus `q_0`) after
    the `DropLastElementAndScale` loop, on which the library computes `MultiplyAndRound(t, q_0)`.
  * `"decoded": ["<v_0>", ...]` and `"encoding": "packed" | "coefpacked"`, for the ciphertexts of
    `final` and every fresh encryption: the values of `cc->Decrypt(sk, ct, &pt)` after `Decode`, as
    the library returns them (packed: `GetPackedValue()`, the slot values, signed decimal strings;
    coefpacked: `GetCoefPackedValue()`); `null` if the decode call threw.
* **`"extendedPre": ["encK.pre0", "encK.pre1"]`** on an EXTENDED entry of `encryptions` whose
  randomness was captured: the pair over `Q*r` (`L + 1` limbs, coefficient form) right before
  `ScaleAndRoundPOverQ`, i.e. `(b*u + e1 + TimesQovert_{Q*r}(p), a*u + e2)`, from the replay that
  reproduces the ciphertext.
* **`"format": "COEFFICIENT"`** on a ciphertext object whose components OpenFHE held in COEFFICIENT
  representation when it was captured (absent: EVALUATION; the dump is in coefficient form either
  way, as for BGV). The 3-part outputs of `LeveledSHEBFVRNS::EvalMult`/`EvalSquare` carry it.
  Checks that compare a recorded result with an operation on recorded operands use the recorded
  residues as they are.
* Program `mixadd` (new): `Relinearize(EvalMultNoRelin(a,b) + c)` and `c - EvalMultNoRelin(a,b)`
  (refused by `extract_bfv.py`; the refusal is tested). With `PIN_CLEARTEXT_NOTES=1` in the
  environment (never for the committed fixtures) its notes record a comparison of `cc->Decrypt` of
  each result with the cleartext computation.
* `decrypt` is attempted for 2 and 3 parts only; a 4-part value (program `threepart`) has
  `"decrypt": null` and no `decryptError`.
* An encryption with the private key (program `symenc`) has an `encryptions` entry with
  `u = e1 = e2 = null`, `randomness: "none"`.
* Plaintexts and fresh encryptions at fewer limbs occur (program `compress`: `MakePackedPlaintext(v,
  1, level)`): `towers < L`, and the encryption relation is over those `towers` limbs with
  `Q_k = q_0 ... q_{towers-1}`.
* `encoding` is the tracer's name: `"packed"` or `"coefpacked"`. A CoefPacked plaintext stores a
  negative value `v` as `q_i - |v|` in limb `i` (not a residue below `t`), and `Encrypt` applies
  `TimesQovert` to those residues; no relation is claimed for such encryptions beyond the PRNG
  replay of `(u, e1, e2)`, whose C++ self-check uses the library's own `TimesQovert`.
