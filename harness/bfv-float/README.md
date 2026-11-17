# harness/bfv-float — the binary64 sums of OpenFHE's HPS-family BFV multiplication, measured

Untrusted evidence for `Challenge/BFVMul/Float.lean` (nothing here is used by a proof):

* that the Lean transcription `Fl.qInv`, `Fl.frac`, `Fl.nuSw`, `Fl.nuSr`, `Fl.switch1`, `Fl.scale1`
  is what OpenFHE v1.6.1 computes, and
* that the proved error bounds `doubleSw k / 2^53`, `doubleSr ms / 2^53`
  (`Challenge.BFVMul.nuSw_tol`, `nuSr_tol`) hold on real binary64 arithmetic, with how much room.

Recording configuration: `fixtures/SOURCE.txt` states the build the committed dumps came from; they
reproduce byte for byte only from the build configuration they were recorded with (single-threaded).

| file | contents |
|---|---|
| `check.py` | Python model of the transcription (standard library only). `float` is IEEE binary64, round to nearest; the fused multiply-add variant is computed exactly in `Fraction` and rounded once; exact values in `Fraction`. `synth`: parameter sets of the committed OpenFHE BFV examples and synthetic ones (30/45/60/64-bit moduli, mixed sizes, 40 limbs). `real`: dumps of the real functions. |
| `dump.cpp` | Links an installed OpenFHE v1.6.1, creates BFVrns contexts with the library's own parameter generation, calls the real `DCRTPoly::SwitchCRTBasis` and `DCRTPoly::ScaleAndRound` with the library's own tables on polynomials with extreme and uniform residues, and writes inputs, outputs and the `double` tables (bit patterns). |
| `run.sh` | Both, in order. `run.sh [INSTALL]`; the comparison with the real functions is skipped if there is no install (`harness/frontend/openfhe/build_openfhe.sh` builds one). `TRIALS=n` sets the number of synthetic trials per parameter set (default 2000). |

## Result of the run of 2026-11-13

x86-64 Linux, GCC 13.3. `dump.cpp` was linked against the install at
`harness/build/frontend-openfhe/install` (`libOPENFHEcore.so.1.6.1`, `libOPENFHEpke.so.1.6.1`),
built by `harness/frontend/openfhe/build_openfhe.sh` from upstream OpenFHE tag `v1.6.1`, commit
`b59e1f291965f14fbee5172cd83a20f5b856204f`, plus the observation-only tracer patch (`-O3`, no
`-march=native`). Its `dcrtpoly-impl.h` (source and installed header) and
`bfvrns-cryptoparameters.cpp` are byte-identical to a pristine checkout of that commit (compared
with `cmp`). `TRIALS=500 run.sh`, 15 contexts (`HPS`, `HPSPOVERQ`, `HPSPOVERQLEVELED` × ring
dimension 1024/2048, depth 2–8, 30/45/60-bit moduli); synthetic part re-run with `--trials 2000`.

* **Tables**: `m_qInv`, `m_rInv`, `m_tRSHatInvModsDivsFrac`, `m_tQlSlHatInvModsDivsFrac[l]`,
  `m_QlQHatInvModqDivqFrac[l]` are bit-for-bit the values of `Fl.qInv`, `Fl.frac` on the numerators
  `Fl.fracNums` (every entry of every context).
* **Functions**: the output of `SwitchCRTBasis` (Q→R and R→Q) and of `ScaleAndRound` (QR→R,
  QR→Q, and Q→Q_l with one limb dropped) equals `Fl.switch1` / `Fl.scale1` with the uncontracted
  binary64 sums on every coefficient of every context (this build does not contract; a build that
  does is detected and reported as such by `check.py real`).
* **Errors** (maximum over all samples, as a multiple of `2^-53`):
  overflow sum `nuSw`: worst ratio to the proved bound `k(k+5)` is **0.654**, at one limb
  (`k = 1`, bound 6, measured 3.92; 54-bit modulus drawn at random in its binade, digit near
  `q - 1`, no contraction; found by the targeted search in `check.py synth`; an independent review
  found 0.628 the same way). With two or more limbs the ratio is at most 0.31 (e.g. 4.4 against
  14 at `k = 2`, 13.2 against 84 at `k = 7`). Scaling sum `nuSr`: at most 0.11 of the proved
  bound `(k+6)(1+Σm)` (e.g. `1.4e18` against `1.8e19` at two 60-bit limbs, i.e. an absolute error
  of about 150 units). No bound violated, with or without fused multiply-add. The synthetic sets
  include 64-bit moduli and 40 limbs, which are outside `floatBasisOK` (below `2^60`, at most 128
  limbs) as far as the moduli go: the tolerance statements hold there too, the library's integer
  steps are not claimed to.
* The truncated scaling sum differs from the exact rounding on almost every coefficient with
  60-bit limbs (the "floor moved" column), and the truncated overflow count on about one in a
  thousand coefficients with extreme residues: the idealised algorithms of
  `Challenge/BFVMul/HPS.lean`, `POverQ.lean` are *not* what the library computes, which is why the
  statements of `Challenge/BFVMul/Float.lean` are needed.

What this does not show: other compilers, targets or flags (see the docstring of `Spec/Float.lean`
for what must hold of a build); only the two functions and five tables above were compared with
the library, not a whole `EvalMult`.
