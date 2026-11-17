# What a default OpenFHE user sees (BGV)

The data behind "What a default user sees" (top-level `README.md`, "Evidence about libraries"): `fhe_check` on a chain of
products of depth D = 1..8 in the context OpenFHE v1.6.1 builds itself for each of its four BGV
scaling techniques (only the depth and t = 65537 set), in the worst case and with `--kappa` 128, 64
and 40.

| file | what |
|---|---|
| `default_table_upstream.csv` | one row per (D, technique): ring dimension, limb and special-prime sizes, the verdict and margin (or overflow, in bits) per mode, the value check of the run, whether the file carries the scaling data |
| `out/default_table/*.fhecheck.json` | the 32 extracted programs the table was computed from |
| `kappa_max.json` | per file: the values of `--kappa` in 1..160 that certify, and t |
| `default_table.sh` | regenerates the CSV and the extracted files (needs the traced OpenFHE build) |
| `kappa_max.py` | regenerates `kappa_max.json` from the committed files (needs only `fhe_check`) |

## How to regenerate

Without OpenFHE (re-checks the committed extracted files):

    lake build fhe_check
    python3 -I harness/eval/openfhe-upstream/kappa_max.py --kmax 160 > harness/eval/openfhe-upstream/kappa_max.json
    for f in harness/eval/openfhe-upstream/out/default_table/*.fhecheck.json; do .lake/build/bin/fhe_check "$f"; done

From scratch (traced OpenFHE v1.6.1: `harness/frontend/openfhe/build_openfhe.sh`, then
`harness/frontend/openfhe/build.sh` for `bgv_demo`):

    harness/eval/openfhe-upstream/default_table.sh > harness/eval/openfhe-upstream/default_table_upstream.csv

The pipeline is the repository's own: the traced build's `bgv_demo`, the extractor
`harness/frontend/openfhe/extract.py` (which records the scaling data, so `fhe_check` can decide
the user-level verdict), its value check, and `.lake/build/bin/fhe_check`. Untrusted evaluation
glue.
