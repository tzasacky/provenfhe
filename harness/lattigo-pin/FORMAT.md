# lattigo-pin dump format (`lattigo-pin/v1`)

One **case** is one run of a small BGV program in Lattigo v6.2.0 (`schemes/bgv`, `Base2 = 0` unless
the case says otherwise) with the secret key available. A case is ONE JSON file `<case>.json`.
Everything is exact integers; big integers are decimal strings, small structural integers are
JSON numbers. This is a minimal variant of `harness/openfhe-pin/FORMAT.md`: there is no
`trace.jsonl` and no extracted program; the exporter writes the operation list itself.

```
{
 "format": "lattigo-pin/v1",
 "case": "<file stem>", "generator": "<free text>", "lattigo": "v6.2.0",
 "seed": <int: seed of the cleartext message PRNG (Lattigo's own key/encryption randomness is not seeded)>,
 "logN": 4, "N": 16, "t": "65537",
 "qs": ["<q_0>", ...],               // the full ciphertext chain, Lattigo's order (level j uses q_0..q_j)
 "ps": ["<p_0>", ...],               // special primes P ([] allowed)
 "base2": 0,                         // EvaluationKeyParameters.BaseTwoDecomposition used for ALL eval keys
 "secret": [s_0, ..., s_{N-1}],      // secret key, coefficient form, signed (centred), JSON numbers
 "keys": {
   "relin": {"digits": [{"b": <QP poly>, "a": <QP poly>}, ...]},        // GadgetCiphertext.Value[i][0] (base2 = 0)
   "galois": [{"g": "<galois element>", "digits": [...]}]               // same, per Galois key
 },
 "objects": {
   "<id>": {"kind": "ct", "level": <number of Q limbs = Lattigo Level()+1>, "parts": <Degree()+1>,
            "scale": "<ct.Scale as an exact integer mod t (Scale.Uint64())>",
            "comps": [<Q poly over level limbs>, ...]},                  // c_0, c_1, (c_2)
   "<id>": {"kind": "pt", "level": <n limbs>, "scale": "...", "poly": <Q poly>}   // the stored plaintext (what Encrypt adds)
 },
 "ops": [                            // in execution order
   {"op": "encSk" | "encPk", "pt": "<id>", "out": "<id>"},
   {"op": "add" | "sub" | "mul", "a": "<id>", "b": "<id>", "out": "<id>"},   // Lattigo Add/Sub/Mul (Mul: no relin, 3 parts)
   {"op": "mulConst", "a": "<id>", "c": "<k>", "out": "<id>", "call": "<which Lattigo call>"},
   {"op": "relin", "a": "<id>", "out": "<id>"},                            // Relinearize
   {"op": "rotate", "a": "<id>", "g": "<galois element>", "out": "<id>",   // Automorphism(a, g) = RotateColumns/RotateRows
    "call": "RotateColumns k=1" | "RotateRows"},
   {"op": "rescale", "a": "<id>", "out": "<id>"}                           // Rescale
 ],
 "slots": {"<id>": {"expected": ["<v>", ...], "decoded": ["<v>", ...]}},   // per ciphertext: cleartext evaluation
                                     // of the program mod t, and Lattigo's Decrypt+Decode (tracked scale) output
 "notes": ["..."]
}
```

A **poly** is a list of limbs, each a list of exactly `N` canonical residues in `[0, modulus)`
(decimal strings), **coefficient form, not Montgomery** (the exporter applies INTT / IMForm when
Lattigo holds the element in NTT / Montgomery form). A Q poly at level `ℓ` has `ℓ` limbs
`q_0..q_{ℓ-1}`; a QP poly has the limbs of the key's Q level then `p_0..` .

Reading (done by the checker, never by the exporter): Lattigo's BGV ciphertexts are in MSB form
(`schemes/bgv/README.md`); the checker multiplies every limb by `t mod q_i` (the *t-reading*) and
then CRT-reconstructs, which gives a textbook (LSB) BGV ciphertext whose phase is `p + t·e`.
