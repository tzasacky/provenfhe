# BFV depth table: OpenFHE's default BFV context under the per-instruction certificate (untrusted)

`depth_table.md` (raw data `depth_table.json`) answers: for OpenFHE v1.6.1's default BFV context,
at which depths does `fhe_check` certify a chain of products, and what does the smallest certified
context cost in evaluation time? The top-level `README.md` ("Evidence about libraries", "What a
default user sees") points to it.

Context: `CCParams<CryptoContextBFVRNS>` with only the plaintext modulus t and the multiplicative
depth set (multiplication `HPSPOVERQLEVELED`, 60-bit primes, `HEStd_128_classic`), key switching
BV (the library default) or HYBRID, t in {65537, 1099512938497}. Program: `chain` of depth
d = 1..5 (`EvalMult(a, b)`, then d - 1 `EvalSquare`, each relinearized). For each (t, ks, d) the
table gives the verdict at the parameters OpenFHE generates for depth d, the smallest j such that
the parameters generated for depth d + j are CERTIFIED, and the measured evaluation-time ratio of
the two contexts.

The certificate charges each instruction its own budget (`Challenge.CertifyBFV.budgetBFV`), and,
under `HPSPOVERQLEVELED`, the internal drop the extractor declares for it
(`bfv.multiplication.internalDrops`, an input hypothesis that the OpenFHE extractor checks against
the library's own record).

## Files

* `depth_table.py`: runs `fhe_check --json` on every context and writes `depth_table.md` and
  `depth_table.json` (verdicts, margins, the hypotheses each certificate records, timings).
* `inputs/*.fhecheck.json`: the extracted programs it reads (`gen_inputs.py`); a context not in
  `inputs/` is produced on the fly with `bfv_demo` and `../openfhe/extract_bfv.py`.
* `gen_inputs.py`: produces `inputs/` (`bfv_demo` on traced OpenFHE v1.6.1, `extract_bfv.py`,
  `value_check_bfv.py`), and `inputs/meta.tsv` (N, limbs, log2 Q, the observed output noise of
  that one run and the decryption limit). The inputs were extracted before the extractor wrote
  `bfv.multiplication.internalDrops`; that field was filled in afterwards from
  `provenance[].internalDrop` of the same file (the traces were not kept).
* `bfv_time.cpp`: the timing driver, built against an OpenFHE v1.6.1 install; it times the
  homomorphic evaluation only, single-threaded, in interleaved rounds (see the header of
  `depth_table.py` for the load rule).

## Regenerate

From this directory:

    # verdicts only (needs fhe_check; uses the committed inputs and keeps the committed timings;
    # a context not in inputs/ also needs BFV_DEMO)
    FHE_CHECK=/path/to/fhe_check python3 -I depth_table.py --keep-time

    # everything (needs bfv_demo on traced OpenFHE v1.6.1 and an OpenFHE install for the timings)
    BFV_DEMO=/path/to/bfv_demo python3 -I gen_inputs.py --jobs 12
    BFV_DEMO=/path/to/bfv_demo python3 -I depth_table.py --build-time /path/to/openfhe/install

The timings depend on the machine; the ratio of interleaved runs is the robust figure.
