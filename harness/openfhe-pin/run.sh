#!/usr/bin/env bash
# openfhe-pin: run the trusted Lean BGV definitions and the proved reference algorithms on exact
# data dumped from upstream OpenFHE v1.6.1.
#
#   harness/openfhe-pin/run.sh            # committed fixtures (no OpenFHE needed)
#   OPENFHE_PIN=<exe> harness/openfhe-pin/run.sh     # use an already built checker
#   LIVE=1 harness/openfhe-pin/run.sh     # rebuild the exporter, regenerate the suites, run on them
#   LIVE=1 SUITES="smoke fixtures" harness/openfhe-pin/run.sh
#   harness/openfhe-pin/difftest.sh       # the gate: the default mode, one summary line
#
# Default mode, everything from the committed fixtures: unpack fixtures/fixtures.tar.xz to a
# temporary directory; build openfhe_pin (`lake build openfhe_pin`, lean/build_lean.sh); then
#   1. the checks a-f and the bit-exact algorithm comparisons `algo.*` on every fixture
#      (`openfhe_pin --with-algo`), judged by lean/verdict.py;
#   2. the extractor on every fixture's recorded params.json + trace.jsonl (export/refusals.py):
#      every recorded refusal is refused again with the recorded message, every recorded program
#      is extracted again;
#   3. the mutation test of the checks (lean/mutation.sh) and of the algorithm comparisons
#      (algo/mutation.sh) on the subset fixtures/mutation.list (skipped with MUTANTS=0, which
#      difftest.sh sets: the gate runs mutation tests as its own step 7, mutants.sh);
#   BFV (fixtures/fixtures-bfv.tar.xz): the BFV checks and algo.* (FHE/Pin/BFV/), judged by
#   lean/verdict_bfv.py against fixtures/EXPECTED_REFUSALS-bfv.tsv, and lean/coverage.py (every
#   instruction shape the BFV extractor can emit has an accepting e.step line).
# Exit status 0 iff
#   * every failing check is one listed in fixtures/EXPECTED_FAIL.tsv (`check<TAB>case`; the list
#     is EMPTY, and GATE=1 requires it to be), and every listed one still fails;
#   * every case the extractor refused has a passing `x.refusal` line, with the class listed in
#     fixtures/EXPECTED_REFUSALS.tsv, and step 2 reproduces every refusal and every program;
#   * both mutation baselines pass and every mutant is caught.
# LIVE=1 needs upstream OpenFHE v1.6.1 + tracer built by harness/frontend/openfhe/build_openfhe.sh
# (OPENFHE_INSTALL, default harness/build/frontend-openfhe/install); products go to
# OPENFHE_PIN_BUILD (default harness/build/openfhe-pin).
# Environment: THREADS (default: the number of cores, at most 48), KEEP=1 (keep the temporary directory), GATE=1 (quiet; the
# expected-fail list must be empty).
set -uo pipefail
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(cd "$HERE/../.." && pwd)"
NCPU="$(getconf _NPROCESSORS_ONLN 2>/dev/null || nproc 2>/dev/null || echo 1)"
if [ -z "${THREADS:-}" ]; then THREADS=$NCPU; [ "$THREADS" -gt 48 ] && THREADS=48; [ "$THREADS" -lt 1 ] && THREADS=1; fi
JOBS_REFUSALS=$(( NCPU < 16 ? NCPU : 16 ))
GATE="${GATE:-0}"
PB="${OPENFHE_PIN_BUILD:-$ROOT/harness/build/openfhe-pin}"
TMP="$(mktemp -d "${TMPDIR:-/tmp}/openfhe-pin.XXXXXX")"
[ "${KEEP:-0}" = 1 ] || trap 'rm -rf "$TMP"' EXIT
T0=$(date +%s.%N)
say() { [ "$GATE" = 1 ] || echo "$@"; }
if [ -n "${OPENFHE_PIN:-}" ]; then EXE="$OPENFHE_PIN"; else
  EXE="$("$HERE/lean/build_lean.sh")" || { echo "run.sh: building openfhe_pin failed" >&2; exit 2; }
fi
rc=0
VARGS=()
BVARGS=()
: > "$TMP/bfv.list"
if [ "${LIVE:-0}" = 1 ]; then
  "$HERE/export/build_cpp.sh" >/dev/null || { echo "run.sh: building the exporter failed" >&2; exit 2; }
  CASES="$PB/cases"
  : > "$TMP/all.list"
  for s in ${SUITES:-smoke fixtures}; do
    python3 "$HERE/export/gen_matrix.py" --suite "$s" --out "$CASES/$s" --jobs "$THREADS" >"$TMP/gen-$s.log" 2>&1 \
      || { echo "run.sh: gen_matrix.py --suite $s failed (see $TMP/gen-$s.log)" >&2; rc=1; }
    ls -d "$CASES/$s"/*/ >> "$TMP/all.list"
  done
  : > "$TMP/expected.tsv"
  ls -d "$CASES"/smoke/*/ > "$TMP/mutation.list" 2>/dev/null || head -12 "$TMP/all.list" > "$TMP/mutation.list"
  VARGS+=(--live)
else
  tar -xJf "$HERE/fixtures/fixtures.tar.xz" -C "$TMP" || { echo "run.sh: cannot unpack fixtures" >&2; exit 2; }
  ls -d "$TMP"/fixtures/*/ > "$TMP/all.list"
  sed "s|^|$TMP/fixtures/|" "$HERE/fixtures/mutation.list" > "$TMP/mutation.list"
  cp "$HERE/fixtures/EXPECTED_FAIL.tsv" "$TMP/expected.tsv"
  VARGS+=(--refusals "$HERE/fixtures/EXPECTED_REFUSALS.tsv")
  # BFV (fixtures-bfv.tar.xz): its own list, verdict and refusal file
  tar -xJf "$HERE/fixtures/fixtures-bfv.tar.xz" -C "$TMP" || { echo "run.sh: cannot unpack BFV fixtures" >&2; exit 2; }
  ls -d "$TMP"/bfv-fixtures/*/ > "$TMP/bfv.list"
  sed "s|^|$TMP/bfv-fixtures/|" "$HERE/fixtures/mutation-bfv.list" > "$TMP/mutation-bfv.list"
  BVARGS+=(--refusals "$HERE/fixtures/EXPECTED_REFUSALS-bfv.tsv")
fi
[ "$GATE" = 1 ] && BVARGS+=(--gate)
[ "$GATE" = 1 ] && VARGS+=(--gate)
say "openfhe_pin on $(wc -l < "$TMP/all.list") cases (checks a-f and algo.*)"
# the three steps run concurrently
( "$EXE" --threads "$THREADS" --with-algo --out "$TMP/results.jsonl" --list "$TMP/all.list" > "$TMP/run.log" 2>&1
  python3 -I "$HERE/lean/verdict.py" "$TMP/results.jsonl" "$TMP/expected.tsv" "${VARGS[@]}" \
    --summary "$TMP/summary.json" > "$TMP/verdict.txt" 2>&1; echo $? > "$TMP/verdict.rc" ) &
if [ -s "$TMP/bfv.list" ]; then
( "$EXE" --threads "$THREADS" --with-algo --out "$TMP/bfv.jsonl" --list "$TMP/bfv.list" > "$TMP/bfv-run.log" 2>&1
  python3 -I "$HERE/lean/verdict_bfv.py" "$TMP/bfv.jsonl" "$TMP/expected.tsv" "${BVARGS[@]}" \
    --summary "$TMP/bfv-summary.json" > "$TMP/bfv-verdict.txt" 2>&1; r=$?
  python3 -I "$HERE/lean/coverage.py" "$TMP/bfv.jsonl" > "$TMP/coverage.txt" 2>&1 || r=1
  echo $r > "$TMP/bfv-verdict.rc" ) &
fi
( cat "$TMP/all.list" "$TMP/bfv.list" > "$TMP/both.list"
  python3 -I "$HERE/export/refusals.py" --jobs "$JOBS_REFUSALS" --list "$TMP/both.list" > "$TMP/extractor.txt" 2>&1
  echo $? > "$TMP/extractor.rc" ) &
# mutation tests: not in the gate's step 6 (difftest.sh sets MUTANTS=0); mutants.sh is step 7
if [ "${MUTANTS:-1}" = 1 ]; then
( MUTATION_OUT="$TMP/mutation" THREADS=$(( THREADS < 8 ? THREADS : 8 )) "$HERE/lean/mutation.sh" "$TMP/mutation.list" "$EXE" > "$TMP/mutation.txt" 2>&1
  echo $? > "$TMP/mutation.rc" ) &
( MUTATION_OUT="$TMP/algo-mutation" THREADS=$(( THREADS < 8 ? THREADS : 8 )) "$HERE/algo/mutation.sh" "$TMP/mutation.list" "$EXE" > "$TMP/algo-mutation.txt" 2>&1
  echo $? > "$TMP/algo-mutation.rc" ) &
fi
wait
if [ "$GATE" != 1 ]; then
  sed -n '/^--- summary/,$p' "$TMP/run.log"
  cat "$TMP/verdict.txt"
  echo "--- algorithm comparisons (algo/summarize.py) ---"
  python3 -I "$HERE/algo/summarize.py" "$TMP/results.jsonl" | sed -n '1,/^coverage/p'
  echo "--- the extractor on the recorded traces ---"
  cat "$TMP/extractor.txt"
  if [ -s "$TMP/bfv.list" ]; then
    echo "--- BFV ($(wc -l < "$TMP/bfv.list") cases): verdict_bfv.py, coverage.py, summarize_bfv.py ---"
    sed -n '/^--- summary/,$p' "$TMP/bfv-run.log"; cat "$TMP/bfv-verdict.txt" "$TMP/coverage.txt"
    python3 -I "$HERE/lean/summarize_bfv.py" "$TMP/bfv.jsonl" 2>/dev/null | head -80
  fi
  echo "--- mutation test of the checks on $(wc -l < "$TMP/mutation.list") cases ---"
  cat "$TMP/mutation.txt"
  echo "--- mutation test of the algorithm comparisons on $(wc -l < "$TMP/mutation.list") cases ---"
  cat "$TMP/algo-mutation.txt"
fi
steps="verdict extractor"
[ -s "$TMP/bfv.list" ] && steps="$steps bfv-verdict"
[ "${MUTANTS:-1}" = 1 ] && steps="$steps mutation algo-mutation"
for step in $steps; do
  if [ "$(cat "$TMP/$step.rc" 2>/dev/null)" != 0 ]; then
    rc=1
    if [ "$GATE" = 1 ]; then echo "--- $step FAILED ---"; cat "$TMP/$step.txt"; [ "$step" = bfv-verdict ] && cat "$TMP/coverage.txt"; fi
  fi
done
# machine-readable counts (lean/counts.py; COUNTS_JSON=<path> keeps a copy: counts.sh)
python3 -I "$HERE/lean/counts.py" "$TMP" > "$TMP/counts.json" 2> "$TMP/counts.err" || echo "counts.py failed: $(head -c 300 "$TMP/counts.err")" >&2
[ -n "${COUNTS_JSON:-}" ] && cp "$TMP/counts.json" "$COUNTS_JSON"
T1=$(date +%s.%N)
python3 -I - "$TMP" "$rc" "$T0" "$T1" <<'PY'
import json, re, sys
tmp, rc, t0, t1 = sys.argv[1], int(sys.argv[2]), float(sys.argv[3]), float(sys.argv[4])
try:
    s = json.load(open(tmp + "/summary.json"))
except Exception:
    s = None
def last(name, pat):
    try:
        m = re.findall(pat, open(f"{tmp}/{name}.txt").read())
        return m[-1] if m else None
    except Exception:
        return None
lm = last("mutation", r"lean mutants: (\d+) caught of (\d+)")
am = last("algo-mutation", r"algo mutants: (\d+) killed of (\d+)")
ex = last("extractor", r"extractor: (\d+) refusals reproduced of (\d+), (\d+) programs reproduced of (\d+)")
load = open("/proc/loadavg").read().split()[0]
bfv = None
try:
    b = json.load(open(tmp + "/bfv-summary.json"))
    cov = last("coverage", r"coverage: (\d+) emittable BFV shapes, (\d+) covered")
    algo = [d for d in (json.loads(l) for l in open(tmp + "/bfv.jsonl")) if d.get("check", "").startswith("algo.")]
    aok = sum(1 for d in algo if d.get("ok") is True); afail = sum(1 for d in algo if d.get("ok") is False)
    bfv = (f"BFV: {b['cases']} cases ({b['programs']} programs, {b['refused']} refusals tested), {b['lines']} check lines "
           f"({b['ok']} ok / {b['fail']} fail / {b['null']} null), {b['certified']} CERTIFIED with "
           f"{b['certifiedWithViolation']} violated, {b['notCertified']} NOT CERTIFIED, "
           f"algo {aok} ok / {afail} differing, coverage {cov[1] + '/' + cov[0] if cov else '?'} shapes")
except Exception:
    pass
if s is None:
    print(f"openfhe-pin: FAIL (no verdict) in {t1 - t0:.1f} s")
else:
    print(f"openfhe-pin: {'PASS' if rc == 0 else 'FAIL'}: {s['cases']} cases, {s['lines']} check lines "
          f"({s['ok']} ok / {s['fail']} fail / {s['null']} null), expected-fail list {s['expectedFail']}, "
          f"{s['refused']} extractor refusals tested ({ex[0] + '/' + ex[1] if ex else '?'} reproduced, "
          f"{ex[2] + '/' + ex[3] if ex else '?'} programs reproduced), "
          f"{s['encryptRelationHolds']}/{s['encryptions']} encryptions = encrypt t b a p u e1 e2 "
          f"({s['storedExceedsTMinus1']} with |p| > t-1), "
          f"algo: {s['algoOps']} operations / {s['algoCoeffs']} coefficients bit-exact ({s['algoFailing']} differing), "
          + (f"mutants caught: {lm[0] + '/' + lm[1] if lm else '?'} checks + {am[0] + '/' + am[1] if am else '?'} algo; "
             if lm or am else "mutants: harness/openfhe-pin/mutants.sh; ")
          + (bfv + "; " if bfv else "")
          + f"{t1 - t0:.1f} s, load {load}")
PY
exit $rc
