#!/usr/bin/env bash
# realsize/run.sh -- the real-size conformance suite of openfhe-pin. The full run is NOT part of the
# gate (hours); the sample (SAMPLE=1, no OpenFHE, about a minute) is: harness/openfhe-pin/difftest.sh runs it.
#
#   harness/openfhe-pin/realsize/run.sh            # record the whole suite, verify, check, summarize
#   SAMPLE=1 harness/openfhe-pin/realsize/run.sh   # only the committed sample (sample/*.tar.xz; no OpenFHE)
#
# Full mode, from a traced SINGLE-THREADED OpenFHE v1.6.1 build (harness/frontend/openfhe/build_openfhe.sh,
# WITH_OPENMP=OFF; export/build_cpp.sh refuses any other build):
#   1. builds the exporters (export/build_cpp.sh, build_cpp_bfv.sh) into $WORK/pinbuild;
#   2. records every case of suite.py (seeds from the case names) into $WORK/suite (about 17 GB);
#   3. compares every recorded file with MANIFEST.sha256.tsv (sha256 of the five files of every case);
#   4. builds the checker (lake build openfhe_pin);
#   5. runs one checker process per case: openfhe_pin --threads 1 --with-algo --forced-max-n 32768
#      (wall time and peak memory per case by /usr/bin/time), JOBS at a time;
#   6. summarize.py -> $WORK/summary.json, $WORK/table.md; compares the totals with summary.json.
# Exit status 0 iff every recording matches the manifest, every case finished, no result line has
# "ok": false, and the totals equal the committed ones.
#
# Environment: OPENFHE_INSTALL (default harness/build/frontend-openfhe-noomp/install), WORK (default
# build/realsize under the repository root), JOBS (default 16; each checker process needs 1-7 GB), ONLY
# (substring of case names), SKIP_RECORD=1 (reuse $WORK/suite), OPENFHE_PIN (an already built checker),
# CASE_TIMEOUT (default 21600: wall seconds per case; a case still running then is terminated and
# summarized as unfinished, which makes the final comparison fail; 0 = no limit).
# Time on a 128-core machine with JOBS=24: recording about 2 minutes, checking a few hours
# (the largest cases, N = 32768 with 11-13 limbs, take the longest).
set -uo pipefail
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(cd "$HERE/../../.." && pwd)"
WORK="${WORK:-$ROOT/build/realsize}"
JOBS="${JOBS:-16}"
CASE_TIMEOUT="${CASE_TIMEOUT:-21600}"
ONLY="${ONLY:-}"
mkdir -p "$WORK"

build_checker() {
  if [ -n "${OPENFHE_PIN:-}" ]; then echo "$OPENFHE_PIN"; return; fi
  (cd "$ROOT" && lake build openfhe_pin >&2) || { echo "realsize/run.sh: lake build openfhe_pin failed" >&2; exit 2; }
  echo "$ROOT/.lake/build/bin/openfhe_pin"
}

check_cases() {  # check_cases EXE SUITE_DIR RESULTS_DIR
  local exe="$1" suite="$2" res="$3"
  mkdir -p "$res"
  for d in "$suite"/*/; do
    n="$(basename "$d")"
    [ -z "$ONLY" ] || [[ "$n" == *"$ONLY"* ]] || continue
    echo "$(du -sb "$d" | cut -f1) $n"
  done | sort -rn | awk '{print $2}' > "$res/order.txt"
  # largest first; one process per case
  xargs -P "$JOBS" -I{} sh -c "/usr/bin/time -f '{}\t%e\t%M' -o '$res/{}.time' timeout -s TERM '$CASE_TIMEOUT' '$exe' --threads 1 --with-algo \
      --forced-max-n 32768 --out '$res/{}.jsonl' '$suite/{}' > '$res/{}.log' 2>&1" < "$res/order.txt"
}

if [ "${SAMPLE:-0}" = 1 ]; then
  EXE="$(build_checker)"
  S="$WORK/sample"; rm -rf "$S"; mkdir -p "$S/cases"
  for f in "$HERE"/sample/*.tar.xz; do tar -C "$S/cases" -xJf "$f"; done
  check_cases "$EXE" "$S/cases" "$S/results"
  python3 "$HERE/summarize.py" --suite "$S/cases" --results "$S/results" --json "$S/summary.json" --md "$S/table.md"
  python3 - "$S/summary.json" "$HERE/sample/summary.json" <<'PY'
import json, sys
got, want = json.load(open(sys.argv[1])), json.load(open(sys.argv[2]))
keys = ("lines", "ok", "fail", "null", "ops", "coeffs", "mism")
g = {k: got["totals"].get(k) for k in keys}; w = {k: want["totals"].get(k) for k in keys}
ok = g == w and got["finished"] == got["cases"] and not got["failures"]
print(("realsize sample: PASS " if ok else "realsize sample: FAIL ") + json.dumps(g) + ("" if ok else " expected " + json.dumps(w)))
sys.exit(0 if ok else 1)
PY
  exit $?
fi

I="${OPENFHE_INSTALL:-$ROOT/harness/build/frontend-openfhe-noomp/install}"
export OPENFHE_INSTALL="$I" OPENFHE_PIN_BUILD="$WORK/pinbuild"
if [ "${SKIP_RECORD:-0}" != 1 ]; then
  "$ROOT/harness/openfhe-pin/export/build_cpp.sh" > /dev/null || { echo "realsize/run.sh: exporter build failed" >&2; exit 2; }
  "$ROOT/harness/openfhe-pin/export/build_cpp_bfv.sh" > /dev/null || { echo "realsize/run.sh: BFV exporter build failed" >&2; exit 2; }
  rm -rf "$WORK/suite"
  python3 "$HERE/suite.py" --out "$WORK/suite" --jobs "$JOBS" ${ONLY:+--only "$ONLY"} || exit 2
fi
rc=0
python3 "$ROOT/harness/openfhe-pin/export/sha_manifest.py" "$WORK/suite" > "$WORK/MANIFEST.sha256.tsv"
python3 - "$WORK/MANIFEST.sha256.tsv" "$HERE/MANIFEST.sha256.tsv" <<'PY' || rc=1
import sys
def rows(p):
    # case -> (N, bytes, sha256 x 5); the export wall time (column 4) is not compared
    return {r[0]: (r[1], r[2]) + tuple(r[4:]) for r in (l.rstrip("\n").split("\t") for l in open(p))
            if r and not r[0].startswith("#")}
got, want = rows(sys.argv[1]), rows(sys.argv[2])
bad = sorted(c for c in got if c in want and got[c] != want[c])
missing = sorted(c for c in want if c not in got)
print(f"recordings: {len(got)} cases, {len(got) - len(bad)} byte-identical to MANIFEST.sha256.tsv, "
      f"{len(bad)} differing {bad[:5]}, {len(missing)} not recorded")
sys.exit(1 if bad else 0)
PY
EXE="$(build_checker)"
check_cases "$EXE" "$WORK/suite" "$WORK/results"
python3 "$HERE/summarize.py" --suite "$WORK/suite" --results "$WORK/results" --json "$WORK/summary.json" \
  --md "$WORK/table.md" || rc=1
python3 - "$WORK/summary.json" "$HERE/summary.json" <<'PY' || rc=1
import json, sys
got, want = json.load(open(sys.argv[1])), json.load(open(sys.argv[2]))
keys = ("lines", "ok", "fail", "null", "ops", "coeffs", "mism")
g = {k: got["totals"].get(k) for k in keys}; w = {k: want["totals"].get(k) for k in keys}
ok = g == w and got["finished"] == got["cases"] and not got["failures"]
print(("realsize: PASS " if ok else "realsize: FAIL ") + json.dumps(g) + ("" if ok else " expected " + json.dumps(w)))
sys.exit(0 if ok else 1)
PY
exit $rc
