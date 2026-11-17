# Analyzer speed: the fast path of `fhe_check`

How `fhe_check` decides in time near-linear in the program length, and what it measures. Scripts:
`profile.sh` (time split and peak memory by program size), `bench.sh` (wall time and peak memory
per instruction kind), `gen.py` (the synthetic programs; see their headers), `real/run.sh` (the
real third-party programs). Every run is `fhe_check --no-suggest --max-instructions 0 FILE` unless
said otherwise.

## How the check is near-linear

**The locked decisions are quadratic as written.** `Challenge.Headline.refAnalyze` and
`Challenge.BFV.refAnalyzeBFV` keep both environments (values, bounds) as functions: every
instruction wraps the previous one in a closure (`Env.set`, `fun y => if y = dst then …`), so a
lookup walks back through every earlier instruction. `certify?`/`certifyBFV?` run the analysis once
for the whole program and again for every output; `Spec.Encrypt.certOK?` (`outputKey?`,
`outputLevel?`) and `mulLevels` replay `Source.step` again per output. Measured with the
reference decision in the tool, on synthetic programs of every instruction kind (`gen.py`), one
process at a time on a 128-core AMD EPYC 7742 shared with other jobs (load average 25 to 45).
At 10,000 instructions the
check took 3.6 to 13 s (BGV), 8.6 to 36 s (BFV); at 30,000, 43 to 135 s and 103 to 470 s.

**The fast path.** `FHE/Noise/Fast.lean`, `FHE/Noise/FastBFV.lean` and `FHE/Noise/FastScaling.lean`
(untrusted) are the reference analyses with the environments in `Std.TreeMap` keyed by variable
name, the body run **once**, the per-output bounds, keys and levels read from the final
environments, and the name lookups of `Spec.Encrypt.freshOK?`, `Program.boundOf` and
`TraceBFV.inputBound` done in trees. They call the locked `Source.step`, `refBound`, `refBoundBFV`,
`domainOK`, `bndOK` and `stepChecks` themselves. Eight locked statements in `Challenge/Fast.lean`
say they are **equal**, on every input, to `refAnalyze`, `certify?`, `refAnalyzeBFVAt` (one budget
per instruction), `certifyBFV?`, `certifyBFVFresh?`, `decryptLibOK?`, `decryptLibExtOK?` and
`Spec.Scaling.scaleOK?`; `fhe_check` computes its verdict with them and says so in its report.
Inside them:

* the BFV per-instruction budget and side conditions are tree-backed (`budgetsGo`/`checksGo`) and
  memoised by `(level, drop, kind)` (`budgetsGoM`, `checksGoM`; for a `mul` they evaluate the
  technique's slack and its locked side conditions, the dominant cost), proved equal
  (`budgetsGoM_eq`, `checksGoM_eq`);
* the `declaredDrops` assumption of BFV uses `FHE.Noise.FastBFV.opLevelsGo`/`opLevelsFast` (tree
  environment) in place of the locked `Challenge.CertifyBFV.opLevels`, proved equal
  (`Validation.FastBFV.Aux2.opLevelsFast_eq`);
* the moduli `Q_ℓ` of the levels are computed once per check (`FHE.Noise.Fast.modsOf`; the
  reference recomputes the product of the chain at every instruction), proved equal
  (`Validation.Fast.Aux.modAt_modsOf`, `Validation.FastBFV.Aux.refBoundBFVQ_eq`);
* the fresh-input check is `FHE.Noise.Fast.freshOK` (`Validation.Fast.Aux.freshOK_eq`), and the
  BGV user-level decryption check is `FHE.Noise.FastScaling.scaleOK`/`factors`
  (`Validation.FastScaling.scaleOK_eq`, `factors_eq`).

The fresh-encryption decision `certifyBFVFresh?` checks names with list searches, quadratic in the
number of fresh inputs, and has a fast equal of its own; spot check after it: BFV `sumsq` with 2^18
fresh inputs, 524,375 instructions, in the fresh-encryption mode `--kappa 128`, 35.6 s and 0.9 GB.

**Untrusted glue.** The diagnostic replays of the report (`replay`, `switchSites`; BFV `replay`,
`sites`) keep their environments in persistent search trees. The decision (`certifyFast`,
`certifyBFVFast`/`certifyBFVFreshFast`) runs in a `Task` of its own, concurrently with the budget,
the diagnostic replay and the informational textbook analysis (BFV) or the replay (BGV); the two
prefix runs that confirm a refusal's location run in parallel; the BFV report reads the analyzer's
value from its one run of the body (by definition the same: `FHE.Check.BFV.analyzer_eq_run`,
`rfl`). `fhe_check` exits as soon as its report is printed, so a task a refusal no longer needs does
not delay it. Tasks hold their own trees, which costs memory. The report lists the first 20
declared input bounds and a count, and the BGV rendering reuses the user-level check computed for
the verdict.

**The decoder** validates the scale adjustments of `$.scaling.adjustments` by indexing the body
array and marking the adjusted instructions in an `Array Bool` (`FHE/Check/Decode.lean`): linear in
the number of instructions and adjustments. Its name-uniqueness checks use hash sets.

**Regression guard.** Section 10 of `harness/frontend/tests/run.sh` requires linear growth: BGV
`mixed`, BFV `mulrelin` and BFV `mixed` at 15,000, 30,000 and 60,000 instructions (at most 15 s at
30,000, and at most 9 times the time for 4 times the length), a BGV program in which every
instruction is a declared scale adjustment at 20,000, 40,000 and 80,000 instructions (at most 6 s
at 80,000, the same growth rule), and profile mode (`mixed`, BGV and BFV, at the emitted
profile and BFV also at a uniform one) with the same budgets.

## Measurements

### Profile, 10^4 to 10^7 instructions (`profile.sh`)

Quiet machine, one process at a time, no other heavy job on the machine. The programs are
SYNTHETIC (`gen.py`: `mixed` for "certified", `sumsq` for "refused"), not extracted from a real
library run; real extracted programs are in "Real programs" below. Flags: `--no-suggest`, and
`--max-instructions 0` (the limit lifted; it is 2,000,000 by default). Each row: wall time of the
whole process and peak resident memory (GNU time), and the split from a second run with `--time`
(ms). 10^4, 10^5, 10^6 instructions: median of three runs (columns "runs", "wall s min to max");
10^7: one run (4 programs, 14 to 19 GB each, 3 to 7 minutes per process; the `--time` run is a
second process). The machine was otherwise idle (load 1.2 to 2.7), the load being the desktop
background of this machine plus the run itself (the checker uses about 3 to 4 cores at most).
`gen.py` writes no scale adjustments unless given `--adjustments`, so these programs do not
exercise the decoder's adjustment validation.

machine: 128 cores, AMD EPYC 7742 64-Core Processor, 283 GB RAM; load average at start 1.79 1.99 4.90
binary: `.lake/build/bin/fhe_check`, sha256 9eb36da57ca83c8078c206bcb92a3db5bf92c0f73adfa46d03edd6c66b0d8e24.

| scheme | path | instructions | MB file | verdict | wall s | peak MB | read+lex | parse | decode | check | render | runs | wall s min to max |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| BGV | certified | 10002 | 0 | CERTIFIED | 0.16 | 99 | 2 | 10 | 10 | 88 | 0 | 3 | 0.16 to 0.17 |
| BFV | certified | 10002 | 0 | CERTIFIED (qualified) | 0.33 | 101 | 2 | 11 | 12 | 235 | 4 | 3 | 0.33 to 0.34 |
| BGV | refused | 10087 | 0 | NOT CERTIFIED | 0.27 | 107 | 5 | 16 | 19 | 173 | 0 | 3 | 0.26 to 0.27 |
| BFV | refused | 10087 | 0 | NOT CERTIFIED | 0.33 | 121 | 4 | 14 | 14 | 262 | 3 | 3 | 0.32 to 0.38 |
| BGV | certified | 100002 | 5 | CERTIFIED | 1.51 | 219 | 36 | 107 | 120 | 1203 | 0 | 3 | 1.48 to 1.65 |
| BFV | certified | 100002 | 5 | CERTIFIED (qualified) | 2.62 | 264 | 36 | 104 | 115 | 2331 | 44 | 3 | 2.50 to 2.66 |
| BGV | refused | 100087 | 8 | NOT CERTIFIED | 2.88 | 262 | 58 | 168 | 231 | 2440 | 0 | 3 | 2.82 to 2.89 |
| BFV | refused | 100087 | 7 | NOT CERTIFIED | 3.42 | 293 | 48 | 139 | 167 | 3202 | 45 | 3 | 3.32 to 3.53 |
| BGV | certified | 1000002 | 56 | CERTIFIED | 17.76 | 1460 | 384 | 1051 | 1243 | 14878 | 1 | 3 | 16.92 to 17.93 |
| BFV | certified | 1000002 | 55 | CERTIFIED (qualified) | 28.95 | 2035 | 377 | 1079 | 1234 | 27280 | 523 | 3 | 28.21 to 30.10 |
| BGV | refused | 1000087 | 90 | NOT CERTIFIED | 35.81 | 1896 | 601 | 1645 | 2782 | 30604 | 0 | 3 | 35.38 to 36.71 |
| BFV | refused | 1000087 | 75 | NOT CERTIFIED | 38.90 | 2527 | 503 | 1406 | 2157 | 34257 | 486 | 3 | 37.65 to 39.28 |
| BGV | certified | 10000002 | 589 | CERTIFIED | 196.87 | 13755 | 3865 | 10906 | 14179 | 168015 | 6 | 1 | one run |
| BFV | certified | 10000002 | 575 | CERTIFIED (qualified) | 308.67 | 18979 | 3778 | 10882 | 12339 | 282757 | 5976 | 1 | one run |
| BGV | refused | 10000087 | 939 | NOT CERTIFIED | 391.57 | 14145 | 6042 | 17410 | 35542 | 332811 | 0 | 1 | one run |
| BFV | refused | 10000087 | 793 | NOT CERTIFIED | 395.05 | 19002 | 5121 | 14799 | 22312 | 388331 | 4208 | 1 | one run |

At 10^7: BGV 3.3 / 6.5 minutes (certified / refused), BFV 5.1 / 6.6 minutes, 14 to 19 GB. Split
columns in ms, medians of the `--time` runs (one run at 10^7); BFV "check" is the whole check run
after its parts were timed (decode included), so the split of a BFV row does not add up to its wall
time.

Growth: wall seconds at 10^4 / 10^5 / 10^6 / 10^7 instructions: BGV certified 0.16 / 1.51 / 17.76 /
196.9 (16, 15, 18, 20 µs per instruction; start-up amortised at the small end); BFV certified 0.33 /
2.62 / 28.95 / 308.7 (33, 26, 29, 31 µs); BGV refused 0.27 / 2.88 / 35.81 / 391.6; BFV refused
0.33 / 3.42 / 38.90 / 395.1. Growth factor 10^6 to 10^7: 11.1 (BGV certified), 10.7 (BFV
certified), 10.9 (BGV refused), 10.2 (BFV refused); local exponents 1.04, 1.03, 1.04, 1.01
(10^5 to 10^6: 1.07, 1.04, 1.09, 1.06): consistent with n log n (search trees keyed by variable
names, log2 n from 17 to 23) plus memory effects at 14 to 19 GB, not with n^2 (exponent 2). Per
instruction at 10^6: 18 µs (BGV certified), 29 µs (BFV certified), 36 to 39 µs (refused: the
location of the failure is confirmed by two more runs on prefixes). Run-to-run spread at 10^6:
2 to 7 % (min to max against the median). Wall times of a process that runs a few tasks in
parallel. Peak memory at 10^6 and 10^7: 1.4 to 2.5 kB per instruction.

### N does not matter

The same 200,000-instruction `mixed` program with only `params.N` changed (2^10, 2^15, 2^16): the
same verdict (CERTIFIED in all 18 runs), whole-process wall time, three runs each on the quiet
machine (load 1.3 to 2.3): BGV 3.13 to 3.40 s / 3.11 to 3.36 s / 3.09 to 3.35 s; BFV 5.36 to 5.51
s / 5.17 to 5.61 s / 5.22 to 5.41 s. The differences between ring dimensions are inside the
run-to-run spread. The analysis works on bounds (integers of a few hundred bits) and levels; N
enters only as a factor in the bound formulas.

### Every instruction kind at 10^6 (shared machine)

`bench.sh` on an earlier build of the fast path than the profile above, one process at a time on
the same machine while it was shared with other jobs (load average 60 to 75; times vary by up to
50 % with the load). Parameters: BGV = `examples/openfhe_depth8_q55_fixedmanual` (N = 2^15, nine
55-bit primes); BFV = `examples/openfhe_bfv_default_chain_d3` (N = 2^13, HPSPOVERQLEVELED,
binary64, one internal-drop entry per instruction, all 0), one output.

| scheme | program | instructions | verdict | s | MB |
|---|---|---|---|---|---|
| BGV | add | 1000000 | CERTIFIED | 16.66 | 1211 |
| BGV | rot | 1000002 | CERTIFIED | 14.39 | 891 |
| BGV | mulrelin | 1000000 | CERTIFIED | 14.61 | 1105 |
| BGV | modswitch | 1000000 | CERTIFIED | 12.97 | 1082 |
| BGV | lincomb | 1000001 | CERTIFIED | 23.60 | 1629 |
| BGV | mixed | 1000002 | CERTIFIED | 16.43 | 1171 |
| BFV | add | 1000000 | CERTIFIED | 42.09 | 1446 |
| BFV | rot | 1000002 | CERTIFIED | 35.71 | 1112 |
| BFV | mulrelin | 1000000 | CERTIFIED (binary64) | 69.58 | 1235 |
| BFV | modswitch | 1000000 | CERTIFIED | 24.06 | 863 |
| BFV | lincomb | 1000001 | CERTIFIED | 77.33 | 1704 |
| BFV | mixed | 1000002 | CERTIFIED (binary64) | 59.63 | 1282 |

## Real programs

Real extracted programs (not synthetic). Driver, parameter patch, results and report excerpts:
`harness/eval/analyzer-speed/real/` (`results.tsv`: one row per driver run, with the sha256 of its
trace; `reports/`: excerpts of the fhe_check reports). Every run, trace included, is regenerated by
`harness/eval/analyzer-speed/real/run.sh CASE SETTING` (CASE compare, sign or division; SETTING
upstream, depth11 or n128); a new trace has a different sha256 (see "Run to run").

The program is third-party and not in this repository: julenbernabe/bgv-extend-openfhe at
be4d8d10892445d8720c0f067588999404c78117 (fetched by `run.sh`; no LICENSE file), built unmodified
except for `bgv-extend-params.diff` (environment variables that raise OpenFHE's own parameter
inputs; with none set the program is the upstream one), with a two-line include shim for a header
OpenFHE removed after v1.0 and one compiler call in place of the program's CMake build, run on the
single-threaded build of upstream OpenFHE v1.6.1 with the tracer
(`harness/build/frontend-openfhe-noomp/install`), `OMP_NUM_THREADS=1`, extracted by
`harness/frontend/openfhe/extract.py --outputs-from-decrypt`, checked by
`fhe_check --no-suggest --max-instructions 0` (worst case).

**`fhe_check recommend` does not apply.** It answers UNSUPPORTED (exit 2) for both the FHERMA
max-element program (FLEXIBLEAUTOEXT) and the bgv-extend compare (FIXEDAUTO; the division uses the
same mode): only FIXEDMANUAL programs keep their meaning when the primes change. This is not "no
certifying parameters found" (exit 1); recommend does not search. The route its message gives for
these modes, raising the library's own parameter inputs and re-tracing, is what `real/run.sh` does,
with the settings chosen by hand.

### The comparison (59,894 instructions)

`bgv-compare`, menu "integer comparison" with 40 and -25: seven encrypted results (==, >, >=, <,
<=, max, min) from Lagrange interpolation over t = 257 (powers of the difference up to 256). One
traced context, 59,894 instructions (modSwitch 23,867, mul 11,614, relin 11,614, mulConst 6,430,
dropLimbs 4,045, add 2,315, sub 9), 4,602 fresh inputs, 7 outputs. Its parameters as written:
t = 257, ring dimension 2, `HEStd_NotSet`, FIXEDAUTO, HYBRID key switching (dnum 3), multiplicative
depth 10. With t = 257, packed encoding needs 2N | 256, so no ring dimension above 128 can run this
program: **no secure parameter set exists for it**, and every verdict below carries fhe_check's
SECURITY warning (N below 1024: not secure per the standard). What is certified is correctness
(exact decryption) only.

| setting | N | depth | SetEvalAddCount | limbs, log2 Q / log2 P | instructions | verdict | library run (traced) |
|---|---|---|---|---|---|---|---|
| upstream (as written) | 2 | 10 | default | 11, 239.13 / 120 | 59,894 | NOT CERTIFIED at body[46568] (a `mul`, by 0.17 bits) | 3.8 s |
| depth11 (depth + 1) | 2 | 11 | default | 12, 261.15 / 120 | 59,894 | **CERTIFIED** | 4.0 to 4.1 s |
| n128 | 128 | 11 | 256 | 12, 456.00 / 180 | 59,894 | **CERTIFIED** | 41.2 s |

`fhe_check` on the depth11 file, one run with the binary of the division timings below: decode 0.18 s, decision 0.60 s, total 1.10 s, wall 1.17 s, 233,020 kB peak (row
`depth11-after-fix` of `real/results.tsv`).

Smallest output margins: depth11 20.83 bits below Q/2 (11.01 bits for the phase switched to one
limb); n128 the same structure, 19.00 bits for the switched phase. The search (all at N = 2 unless
said): SetEvalAddCount 2 and 8 NOT CERTIFIED (body[46568], body[46576]); 64: OpenFHE throws an
exception during setup, before the program reads its inputs (not investigated); 1024 CERTIFIED;
depth + 1 CERTIFIED; SetKeySwitchCount 64 NOT CERTIFIED. At N = 128: depth + 1 alone NOT CERTIFIED
(body[25]), SetEvalAddCount 1024 or 16384 alone NOT CERTIFIED (body[46568]); depth + 1 with
SetEvalAddCount 256, 1024 or 16384 CERTIFIED.

**Output check.** The library's decrypted results at both certified settings (and as written):
40 == -25: 0, >: 1, >=: 1, <: 0, <=: 0, max 40, min -25, which is the plaintext answer. The same
program's "sign" menu (input -17, decrypted -1, correct) is a separate run of 6,651 instructions,
CERTIFIED as written and at both settings. The two menus are traced separately: run together they
generate two key pairs in one context, which the extractor refuses.

**Run to run.** The trace differs between runs (keys and value identifiers), its sha256 with it
(`results.tsv` names the ones checked; the traces are kept outside the repository). Two depth11 runs
of the comparison gave the same instruction sequence, op by op; value names differed, and the
number of declared inputs differed by one (4,603 and 4,602; not investigated). Both CERTIFIED.

### The integer division (2,183,887 instructions): CERTIFIED

`bgv-int-division`, menu "integer division" with 100 and 7: the quotient by a public divisor and by
an encrypted divisor (both by interpolation over t = 257). Same parameter patch, same settings as
the comparison, both at N = 2 (the program's own), so the same SECURITY warning: correctness only.

| setting | depth | limbs, log2 Q / log2 P | instructions | verdict | library run (traced) | trace |
|---|---|---|---|---|---|---|
| upstream (as written) | 10 | 11, 239.13 / 120 | 2,183,887 | NOT CERTIFIED at body[24797] | 2 min 59 s | 2.1 GB |
| depth11 (depth + 1) | 11 | 12, 261.15 / 120 | 2,183,887 | **CERTIFIED** | 3 min 07 s to 3 min 10 s (two runs) | 2.1 GB |

A run at depth 12 outside the driver (same patch, same library build) is CERTIFIED as well. Outputs:
both quotients decrypt to 14 (100 div 7) in every run. Smallest margin 13.82 bits below Q/2 (10.82
bits for the phase switched to one limb). Extraction of the trace by `extract.py` takes about 6
minutes (5 min 42 s and 5 min 49 s in two driver runs) and writes a 631 MB file with 252,237 scale
adjustments.

`fhe_check --no-suggest --max-instructions 0 --time` on the depth11 file (sha256 of its trace
e3a843f3…1aa4, 630.9 MB extracted), binary `.lake/build/bin/fhe_check` with sha256
b1776d26a2f121e0216150e76e0962044eca3fa3046eaa9971486c3759abb245, three runs one after the other,
the machine otherwise idle (1-minute load average 1.2 to 1.5 at the start of each run):

| run | read | lex | JSON parse | decode | decision (check) | total | wall | peak memory |
|---|---|---|---|---|---|---|---|---|
| 1 | 2.04 s | 1.98 s | 7.34 s | 7.39 s | 34.33 s | 53.08 s | 53.88 s | 4,678,260 kB |
| 2 | 2.04 s | 1.93 s | 7.37 s | 6.61 s | 33.79 s | 51.74 s | 52.40 s | 4,678,776 kB |
| 3 | 2.04 s | 1.97 s | 7.31 s | 7.45 s | 35.09 s | 53.85 s | 54.71 s | 4,679,632 kB |

Verdict CERTIFIED in all three; the reports are identical to each other apart from the timing line,
and equal to the recorded excerpt (`real/reports/division.depth11.txt`) in verdict, warnings,
parameters and every bound and margin; only the names of two ciphertext variables differ
(`ct_5513`, `ct_1573806` against `ct_5506`, `ct_1573904`), as the trace is a different run of the
library. The whole check takes 52 to 54 s, of which the proved decision takes 34 to 35 s and
decoding 6.6 to 7.5 s (row `depth11-after-fix` of `real/results.tsv`).

**The decoder against its quadratic version.** A version of the decoder that converted the body to
a list once per scale adjustment and searched the adjustment list once per instruction (quadratic)
took 24 min 07 s on a depth11 division file, and a `--time` run on it gave read 2.1 s, lex 1.9 s,
JSON parse 7.2 s, decode 1,413 s, check 33.2 s, render 0 (machine shared, 1-minute load 6 to 22). On synthetic
programs with adjustments (`gen.py ... mixed N --adjustments`, BGV example, N = 32768, one
adjustment per ten instructions; `fhe_check --no-suggest --max-instructions 0 --time`, one run
each, machine shared, 1-minute load 17 to 22 at the start of each run; indicative only), the
quadratic and the current decoder give the same report (compared byte for byte at 100,000
instructions) and these times:

| instructions (adjustments) | decoder | decode | check | total |
|---|---|---|---|---|
| 100,000 (10,000) | quadratic | 2.30 s | 1.19 s | 3.63 s |
| 100,000 (10,000) | current | 0.13 s | 1.19 s | 1.46 s |
| 1,000,000 (100,000) | quadratic | 250.9 s | 15.2 s | 267.6 s |
| 1,000,000 (100,000) | current | 1.19 s | 13.4 s | 16.0 s |

### FHERMA max-element (35,196 instructions)

Traced at N = 65536, 128-bit security, FLEXIBLEAUTOEXT, log2(Q*P) = 1361 (24 limbs, 6 special
primes); NOT CERTIFIED at body[410], by 25.66 bits; `fhe_check` 0.46 to 0.49 s (three runs on the
quiet machine), 173 MB peak. No certifying setting was searched for: recommend answers UNSUPPORTED
(above), and the traced chain alone (1361 bits) is above the 128-bit cap at N = 32768 (881 bits),
so a library-in-the-loop search stays at N = 65536 (cap 1747 bits, OpenFHE's extension of the
table), where one traced library run of this program takes about two hours single-threaded
(6,996 s). Whether a certifying setting exists for it is open.

## The instruction limit

Default `--max-instructions` 2,000,000 (0 = none), for BGV and BFV alike. By the profile above, a
check at the limit takes about twice the time of the 10^6 rows (18 to 39 s there) and 1.4 to 2.5
kB of memory per instruction, dominated by the decoded program and the JSON tree, which are held
whole. It is a resource guard, not a time-out for the analysis; `--max-instructions 0` checks
anything that fits in memory.

## Where the time goes, and what is not done

* **Input handling.** On the 2.18M-instruction division, reading, lexing, JSON parsing and decoding
  take 18 to 19 s of the 52 to 54 s. Lean's `Json.parse` builds the whole tree (about 3.3 µs per
  instruction) and the decoder walks it (about 3 µs). A streaming reader that decodes
  instructions directly from the text would remove most of both; it is not implemented (the
  decoder's validation is long and every refusal message is covered by the tests).
* **Several passes over the body** in the proved fast decision (BFV: checks, budgets, the run, the
  multiplication levels, the operand levels; each a `Source.step` replay with tree lookups on
  string names). Fusing them, or numbering the variables once, needs new equality proofs. A
  prototype that numbers the variables once and keeps the environments in arrays (BGV `mixed`,
  10^6 instructions, compiled): tree run 6.8 s, array run 7.2 s, numbering alone 1.9 s. Numbering
  costs as much as the tree operations it replaces (about 1.5 s for all of them); the rest of the
  run is the locked `Source.step` and bound rules themselves.
* **Memory**: 1.4 to 2.5 kB per instruction (10^6: 1.5 to 2.5 GB; 10^7: 14 to 19 GB).
