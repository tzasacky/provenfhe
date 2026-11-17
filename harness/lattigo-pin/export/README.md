# lattigo-pin exporter

`main.go` runs small BGV programs in Lattigo v6.2.0 (commit `c1fd095f08602e2d4ef571db015fc553fdd2d845`,
`schemes/bgv`, ring degree 16 or 32). It writes each run as one `lattigo-pin/v1` JSON case
(`../FORMAT.md`). Every value is an exact integer. Ciphertexts, plaintexts and keys are copied,
moved out of NTT form (INTT) and out of Montgomery form (IMForm) according to each object's flags,
and written as canonical residues per limb. Gadget ciphertexts and secret keys carry no flags.
Lattigo always builds them in NTT+Montgomery form, and the key self-check below confirms the
conversion. The secret is limb 0 of `sk.Value.Q`, centred. The exporter checks that it is the same
small integer in every Q and P limb.

## Run

    ./gen.sh [OUT_DIR]      # default OUT_DIR: harness/lattigo-pin/out/cases (not committed); -nofilter: record every step, self-check failures only noted

`gen.sh` builds offline (`GOFLAGS=-mod=mod GOPROXY=off`, module cache, no `replace`) and wipes
`OUT_DIR/{honest,defectB,defectN,scale}`. It then writes `OUT_DIR/<suite>/<case>.json`. Flags:
`-suite NAME` runs only one suite, and `-per-set K` sets the number of honest cases per parameter
set (default 32). Lattigo's key and encryption randomness is not seeded, so reruns give different
bytes. The cleartext PRNG (`math/rand/v2` PCG) is seeded, and the seed is recorded as `seed`.

## Self-checks (run before a case is written, on exactly the residues that are serialised)

- **Phase.** For every ciphertext, the exporter computes `t·(c0 + c1·s + c2·s²) mod Q_level`,
  centred. Its log2 maximum is stored as the extra field `tPhaseLog2`. In the `honest` and `scale`
  suites the case is fatal unless this value is `< Q_level/4`.
- **Slots.** The exporter tracks the expected slot vector through the program. `decoded` is
  Lattigo's own `Decrypt` + `Decode`, using the ciphertext's own `Scale` metadata. In `honest` and
  `scale` the case is fatal on a mismatch. The one exception is the deliberately wrong `MulNew` in
  `scale`.
- **Scale.** The exporter tracks the correct scale: product on `mul`, times `q_last⁻¹ mod t` on
  `rescale`. It must equal Lattigo's `Scale`, except for the `MulNew` demonstration.
- **Keys (informational, recorded in `notes`).** For every digit `(i, j)` of the relinearisation
  key and of each Galois key, the exporter checks every QP limb. It verifies
  `b + a·s_key − P·2^{w·j}·target·[limb ∈ digit i] = e` with one common small `e`. This is the CRT
  form of `b + a·s_key − P·Q̂_i·[Q̂_i⁻¹]_{Q_i}·2^{wj}·target`. Relinearisation key: `s_key = s`,
  `target = s²`. Galois key `g`: `s_key = π_{g⁻¹}(s) = s(X^{g⁻¹})`, `target = s`. The exporter
  tries both `π_g` and `π_{g⁻¹}` and records which one works.

## Conventions found

- **Galois key `g`.** It encrypts `s` under `π_{g⁻¹}(s)` (`keygenerator.go` GenGaloisKey).
  `Automorphism(ct, g)` first key-switches `c1` with that key, which gives a ciphertext under
  `π_{g⁻¹}(s)` with the same phase. It then adds `c0` and applies `π_g` (X → X^g) to both parts
  (`evaluator_automorphism.go`). So the automorphism comes after the key switch, and the output is
  under `s`.
- **`RotateColumns(ct, 1, out)`.** It uses `g = GaloisElement(1)` (5 here). Output slot `i` of row
  `ρ` is input slot `(i+1) mod n/2` of row `ρ`. `RotateRows` uses
  `g = GaloisElementOrderTwoOrthogonalSubgroup() = 2N−1` and swaps the two rows.
- **Fresh encryptions.** `t·pt` centred mod Q is below t, and `phase − pt` is the encryption noise
  (MSB form).

## Suites

| suite | cases | content |
|---|---|---|
| `honest` | 128 | 4 library-generated parameter sets × 32, Base2 = 0 (see below) |
| `defectB` | 5 | LogN 4, LogQ [40,40,40], **no P**, Base2 = 0: mul → relin, RotateColumns, RotateRows |
| `defectN` | 5 + 2 | LogN 4, explicit Q = [q0 ≈ 2^40, q1, q2], Base2 = 20. Cases 000–002 have one ~40-bit P, 003–004 have no P. `q1, q2 ∈ (2^20, √2·2^20)` (`defectN-control-*`: `q1, q2 ∈ (√2·2^19, 2^20)`), same ops as defectB |
| `scale` | 3 | mul → relin → rescale (Scale ≠ 1), then `MulNew(ct, uint64(k))` (defect A) and the correct in-place `Mul(c, k, c)` on `ct.CopyNew()` |

Honest parameter sets (P from LogP, all with default Xs/Xe):

- H1: LogN 4, LogQ [30,25,25,25], LogP [30], t 65537
- H2: LogN 4, LogQ [32,22,22,22,22], LogP [25,25], t 65537 (two P primes, so digits span two limbs and the last digit is partial)
- H3: LogN 5, LogQ [35,30,30], LogP [30,30,30], t 257
- H4: LogN 5, LogQ [45,28,28,28], LogP [35], t 786433

In H2 and H4, q0 was enlarged (from 28 and 40 bits) so the multiplicative chain reaches level 0.

Honest program:

1. Two `encPk` and two `encSk` at the top level, one of each at the next level.
2. `add` and `sub`; `mul` (3 parts) → `relin`; RotateColumns(1) and RotateRows of the result;
   `mulConst`.
3. `rescale` of the 2-part result and of the 3-part `mul` output (output `NewCiphertext(params, 2,
   level−1)`), then `relin` of that, plus `add`/`sub` between the two rescaled results.
4. A chain down to level 0:
   - Each step is `mul` by a fresh `encPk`/`encSk` at the current level, then `relin`, `rescale`,
     `rotate`, `add`, `rotate`, `mulConst`.
   - A step that would push some ciphertext to `|t·phase| ≥ Q_level/4` is discarded. A plain
     `rescale` of the current ciphertext replaces it.
5. `mulConst` is `Mul(c, k, c)` in place on `ct.CopyNew()`, with `k < 2^12`. It is dropped and
   noted when it alone would cross the threshold.

Every output is a fresh `bgv.NewCiphertext(params, degree, level)` and never aliases an input.
`add`/`sub` only combine ciphertexts of equal level and equal `Scale`. Honest suites never call
`MulRelin`. These rules keep the honest suites clear of probe defects C, D and E.

## Fields added to FORMAT.md (all optional for a reader)

- `suite`: the suite the case belongs to.
- `objects.<ct>.tPhaseLog2`: log2 of the maximum centred `t·phase` coefficient.
- `slots.<id>.match`: whether `decoded` equals `expected`.
- `keys.*.keySecret` and `keys.*.target`: the secret each key is encrypted under, and the secret it
  encrypts.
- `keys.galois[].gInv`: `g⁻¹ mod 2N`.
- `keys.*.gadget`: only when `base2 ≠ 0`. It holds the full `GadgetCiphertext.Value[i][j]` matrix.
  Row `i` is the limb (no P, or one P), and entry `j` carries `2^{base2·j}`. `digits` stays
  `Value[i][0]` as the format specifies.
