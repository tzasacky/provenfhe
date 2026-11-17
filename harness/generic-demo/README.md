# Generic demo: certificates with no OpenFHE involved

This directory shows that `fhe_check` and the trusted core it runs (`Spec/`, and the locked
`Challenge.Certify.certify?` and `Challenge.CertifyBFV.certifyBFV?`) need no OpenFHE. Neither the
parameters nor the programs come from OpenFHE.

Run it from the repository root (it needs `.lake/build/bin/fhe_check`, built with `lake build fhe_check`):

    harness/generic-demo/run.sh            # compares with expected/
    UPDATE=1 harness/generic-demo/run.sh   # rewrites expected/

`run.sh` takes about one second and needs `python3` and `ldd`. Its steps:
- **0.** `ldd` shows that `fhe_check` links only the C runtime: libc, libm, libpthread, libdl
  and librt.
- **1.** The hand-written inputs regenerate byte for byte from `make_inputs.py`. That script
  searches for NTT-friendly primes by deterministic Miller–Rabin and writes every other number
  from textbook formulas.
- **2.** The HEIR input re-extracts byte for byte from the committed HEIR output
  (`harness/frontend/examples/heir_dot_product_8.lattigo.worstcase.mlir`). The tools are HEIR
  nightly-2026.11.11 on its Lattigo backend and the extractor `harness/frontend/heir/extract_bgv.py`.
  No `heir-opt` is needed to re-run this step.
- **3.** `fhe_check --no-suggest` runs on each input. The exit code, the `VERDICT` line and the
  per-output bound lines are compared with `expected/*.summary`. The full reports are in
  `expected/*.txt` for reading.

## The inputs and the results

| input | what | verdict | per-output bound |
|---|---|---|---|
| `bgv_textbook_chain` | BGV. N = 2¹⁴, t = 65537; chain of a 60-bit prime and three 50-bit primes; one 61-bit special prime; one limb per digit (uniform layout); centred key switching. Input noise is the textbook fresh-encryption worst case `(t−1) + t·19·(2N+1)`; key noise is `19·t`. Program: `(a·b + rot₅(a·b)) · c · p`, using relin, two modulus switches, `dropLimbs` and `mulPlain`. | CERTIFIED AT PHASE LEVEL (exit 0) | `2^84.20` against Q/2 = `2^109`: margin 24.8 bits |
| `bgv_textbook_chain_too_deep` | the same, with two further squarings | NOT CERTIFIED (exit 1) | overflows at `body[12]` by 72.8 bits |
| `bfv_behz` | BFV. N = 2¹³, t = 65537; three 50-bit primes; one 55-bit special prime (HYBRID key switching with canonical representatives, one limb per digit); BEHZ multiplication with a base of four 52-bit primes, a 53-bit `m_sk` and `m̃ = 2¹⁶`; textbook plaintext addition `⌊Q/t⌋·p`; rounding modulus switch. Program: `(a·b + rot₅(a·b)) + p`, then two modulus switches (the output has one limb). | CERTIFIED (exit 0), with the declared technique and the floating-point model of the library's decryption printed; REALIZABILITY: PROVED, nothing assumed about the multiplication or key switching, only `binary64Dec` (the library's decryption conforms to IEEE binary64); library decryption: PROVED | `53247` (`2^15.70`) against `2^33`: margin 17.3 bits |
| `bfv_tiny_behz_guard` | `Challenge.CertifyBFV.tinyIn mulProg behzTech`, written as JSON (no special prime: BV key switching, one limb per digit) | CERTIFIED (exit 0), with the declared technique printed | `109100936`, equal to the locked `#guard` in `Challenge/CertifyBFV.lean` (`summary (certifyBFV? (tinyIn mulProg (some behzTech) true))`) |
| `heir_dot_product_8.worstcase` | HEIR `dot_product_8` compiled for BGV on Lattigo (worst-case noise model); Lattigo's parameters and constants | CERTIFIED AT PHASE LEVEL (exit 0) | `2^28.34` against Q/2 = `2^31`: margin 2.66 bits |

The BGV input at N = 2¹³ also certifies, with a 31-bit margin. But `fhe_check` then prints a
SECURITY warning: log₂ QP = 271 is above the 128-bit cap of 218 bits in the HE standard. So the
committed inputs use the larger N. The certificate is about correctness only.

**Why BGV says "AT PHASE LEVEL" and BFV does not.** For BGV, `fhe_check` prints the plain
CERTIFIED ("every output decrypts correctly") only when the statement covers what the user reads,
i.e. for an input extracted from a library whose user-level decryption is covered. An input that
no library produced (hand-written, HEIR) gets `CERTIFIED AT PHASE LEVEL`: the raw decryption of
every output is proved correct, and user-level decryption, which depends on the backend, is not
covered. The BFV report has no such mode: it treats every BFV input as a program OpenFHE runs.
It requires the declared key-switching layout to be OpenFHE's (`Challenge.RealizeBFV.ksDeclOK?`:
canonical representatives with special primes, one limb per digit without; a centred HYBRID layout
is refused), and it certifies only if OpenFHE's own decryption of every output is proved
(`Challenge.BFVDecryptLib.decryptLibExtOK?`). That is why `bfv_behz` switches down to one limb: at
two of three limbs OpenFHE's BEHZ decryption reads a table that is empty under BEHZ, and the
answer there is UNSUPPORTED. The locked statement behind the BFV verdict,
`Challenge.CertifyBFV.certifyBFV?_sound`, is still about any implementation of the contracts; only
these two report-layer conditions are OpenFHE's.

## What is and is not claimed for such inputs

**Claimed.** For each CERTIFIED input, the locked statement named in its report
(`Challenge.Certify.certify?_sound` / `worst_certified` for BGV, `Challenge.CertifyBFV.certifyBFV?_sound`
for BFV) states the following. Take every secret key (the soundness statements have no hypothesis on
the secret; `secretBound` enters only the budget and the realizability pins), every input within
the declared bounds, and every run in which each operation meets its phase contract
(`Spec.Trace.StepOK`, `Spec.TraceBFV.StepOK`) within the budget `fhe_check` computed from the
parameters. Then every output decrypts with the secret key itself, at its own level, to the value
the program computes, with noise at most the printed bound.

Since no run of any library was recorded or checked for these inputs, CERTIFIED means: **correct
for any implementation meeting the contracts.** The contracts can be met: the realizability pins
prove it for the textbook operations, for hybrid key switching (centred and canonical
representatives), and, for `bfv_behz`, for the BEHZ limb-level algorithm in integers
(`Challenge.CertifyBFV.certifyBFV?_behz_mul`).

**Not claimed.**
- That any particular library meets the contracts with these numbers. HEIR's Lattigo backend
  declares `canonical` representatives as a conservative choice; that Lattigo stays within that
  bound is argued from its source, not proved.
- That the declared noise numbers hold. The error bound 19, the input noise and the key noise are
  ASSUMPTIONS printed in each report. The secret bound 1 is used only by the budget and by the
  realizability pins: if a real secret exceeds it, the certificate is still sound, but a run may
  not stay within the budget. Here they come from textbook formulas
  in `make_inputs.py`, not from a sampler.
- That the program is what some library executes. For the hand-written inputs it is the program
  as written.
- Security. Correctness of decryption only.
- For the BGV inputs, that any of this holds for a library's own decryption routine. Textbook
  decryption with the secret key is covered (hence "AT PHASE LEVEL"). BGV's switched decryption
  is covered only when an input declares `decryption.method: switch-to-one-limb`, and none here
  does. For the BFV inputs, OpenFHE's decryption is proved for the routine each output takes
  (see the reports' "Library decryption" line), on the condition that OpenFHE ran these
  parameters, which it did not: nothing was executed.

## Which binary

The expected outputs were regenerated with `UPDATE=1 harness/generic-demo/run.sh` by the
`fhe_check` built from this repository's tree (`lake build fhe_check`) on 2026-11-14, after the
verdict policy for library-agnostic BGV inputs ("CERTIFIED AT PHASE LEVEL") and the BFV checks of
the declared key-switching layout and of OpenFHE's own decryption landed. `bfv_tiny_behz_guard`'s
bound 109100936 equals the `#guard` in `Challenge/CertifyBFV.lean`; the other bounds are unchanged
from the earlier run except `bfv_behz`, whose layout (canonical) and program (a second modulus
switch) were changed so that it certifies under those checks.

`run.sh` compares only the verdict, the exit code and the bound lines, so wording changes in the
reports do not fail it. A changed bound or verdict does fail it.

## Files

- `make_inputs.py`: writes `inputs/*.json`, except the HEIR file, which is a copy of the committed example.
- `inputs/`: the five `fhe-check/v1` inputs.
- `expected/*.summary`: what `run.sh` compares. `expected/*.txt`: full reports.
- `run.sh`: the demo.
