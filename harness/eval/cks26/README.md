# The Choe-Kang-Stehle attack circuits

`fhe_check` on the evaluation circuits of attacks 2 (plaintext-ciphertext products) and 3
(ciphertext squarings) of Choe, Kang and Stehle, "New IND-CPA-D Attacks on BFV and BGV"
(CCS 2026), re-implemented from their paper and a reading of their code: no key recovery, no
skewed-encryption search. The checker's verdicts, bounds and certified depths are what the
top-level `README.md` ("The Choe-Kang-Stehle attack circuits") reports. Untrusted evaluation glue.

| file | what |
|---|---|
| `cks26.cpp`, `build.sh` | the circuits against the traced OpenFHE v1.6.1 (`harness/frontend/openfhe/build_openfhe.sh`) |
| `run.py`, `run.sh` | runs every case: build, trace, extract, `fhe_check`; writes `out/` and `cases/` |
| `cases/*.fhecheck.json.gz` | the extracted programs of the headline cases |
| `out/*.summary.json` | per run: the parameters and the checker's output (verdict line, exit code, first failing instruction, per-output bounds) |
| `out/cost_*.result.json` | the cost of certifying the full depth of a squaring circuit: the probed depths and the smallest certified one |
| `recheck.py` | re-runs `fhe_check` on `cases/` and compares with `out/` |
| `relabel.py` | a cross-check: relabels the plaintexts of a trace as packed |
| `many_inputs.py` | reproduces the checker's running time on a program with many inputs |

## How to re-check

Without OpenFHE, from the repository root:

    lake build fhe_check
    harness/eval/cks26/run.sh --committed

It re-runs the checker on every committed case and compares the verdict line, exit code, first
failing instruction and bounds with the committed summaries (exit 1 on a difference). Verdicts and
bounds are deterministic: they depend on the parameters and the program only.

`harness/eval/cks26/run.sh` (no argument) regenerates everything; it needs the traced OpenFHE
v1.6.1 and takes about 1.5 h on 12 cores. The runs of the squaring attack at t = 786433 are not
part of this release.
