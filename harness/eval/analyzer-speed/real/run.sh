#!/usr/bin/env bash
# Real (not synthetic) programs through a full accepting analysis: the third-party OpenFHE BGV
# programs of julenbernabe/bgv-extend-openfhe (comparison, sign, integer division), fetched at a
# pinned commit, run traced on the single-threaded build of upstream OpenFHE v1.6.1 with the
# tracer, extracted, and checked by fhe_check. Results: ../RESULTS.md, "Real programs".
#
#   harness/eval/analyzer-speed/real/run.sh CASE SETTING [OUTDIR]
#     CASE     compare   bgv-compare, menu "IC" with 40 and -25 (==, >, >=, <, <=, max, min)
#              sign      bgv-compare, menu "S" with -17
#              division  bgv-int-division, menu "ID" with 100 and 7 (public and private divisor)
#     SETTING  upstream  the program's own parameters (ring dimension 2, HEStd_NotSet, t = 257,
#                        FIXEDAUTO, depth 10)
#              depth11   the same with SetMultiplicativeDepth one higher (BGVEXT_EXTRA_DEPTH=1)
#              n128      ring dimension 128 (the largest for which t = 257 allows packed
#                        encoding), depth one higher, SetEvalAddCount(256)
#     OUTDIR   default $WORK/runs/CASE/SETTING
#
# Environment:
#   WORK            work directory (default build/analyzer-speed-real under the repository root): source,
#                   binaries, traces (each trace is 0.1 to 2 GB; not committed)
#   OPENFHE_PREFIX  the traced OpenFHE install (default harness/build/frontend-openfhe-noomp/install,
#                   the single-threaded build of harness/frontend/openfhe/build_openfhe.sh)
#   FHE_CHECK       default .lake/build/bin/fhe_check
#
# The program source is not in this repository. It is fetched from GitHub at the commit below
# (the repository has no LICENSE file) and changed only by bgv-extend-params.diff, which lets
# environment variables raise OpenFHE's own parameter inputs (SetMultiplicativeDepth,
# SetEvalAddCount, SetKeySwitchCount, SetRingDim); with none of them set the program is the
# upstream one. The include shim replaces a header removed from OpenFHE after v1.0.
set -euo pipefail
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(cd "$HERE/../../../.." && pwd)"
URL=https://github.com/julenbernabe/bgv-extend-openfhe
COMMIT=be4d8d10892445d8720c0f067588999404c78117
WORK="${WORK:-$ROOT/build/analyzer-speed-real}"
I="${OPENFHE_PREFIX:-$ROOT/harness/build/frontend-openfhe-noomp/install}"
FC="${FHE_CHECK:-$ROOT/.lake/build/bin/fhe_check}"
[ $# -ge 2 ] || { sed -n '2,30p' "$0"; exit 4; }
CASE=$1; SETTING=$2

# 1. fetch and patch (once)
S="$WORK/src/bgv-extend"
if [ ! -d "$S/.git" ]; then
  mkdir -p "$S"; git -C "$S" init -q; git -C "$S" remote add origin "$URL"
  git -C "$S" fetch -q --depth 1 origin "$COMMIT"; git -C "$S" checkout -q --detach FETCH_HEAD
  git -C "$S" apply --unidiff-zero "$HERE/bgv-extend-params.diff"
fi
[ "$(git -C "$S" rev-parse HEAD)" = "$COMMIT" ] || { echo "commit mismatch in $S" >&2; exit 5; }
git -C "$S" diff --quiet -- . ':!lib/bgv/bgv-basics.cpp' || { echo "$S has changes besides the diff" >&2; exit 5; }

# 2. build against the traced install (once)
"$ROOT/harness/frontend/openfhe/check_install.sh" "$I"
mkdir -p "$WORK/shims/scheme/bgvrns" "$WORK/bin"
printf '#pragma once\n#include "openfhe.h"\n' > "$WORK/shims/scheme/bgvrns/cryptocontext-bgvrns.h"
for p in bgv-compare bgv-int-division; do
  [ -x "$WORK/bin/$p" ] && continue
  c++ -std=gnu++17 -O2 -w -I"$I/include/openfhe" -I"$I/include/openfhe/core" -I"$I/include/openfhe/pke" \
    -I"$I/include/openfhe/binfhe" -I"$I/include/openfhe/cereal" -I"$I/include" \
    -I"$S/lib" -I"$S/lib/bgv" -I"$WORK/shims" "$S/src/$p.cpp" -o "$WORK/bin/$p" \
    -L"$I/lib" -Wl,-rpath,"$I/lib" -lOPENFHEpke -lOPENFHEbinfhe -lOPENFHEcore
done

# 3. run traced
case $CASE in
  compare)  BIN=bgv-compare;      IN='IC\n40\n-25\nQ\n';;
  sign)     BIN=bgv-compare;      IN='S\n-17\nQ\n';;
  division) BIN=bgv-int-division; IN='ID\n100\n7\nQ\n';;
  *) echo "unknown case $CASE" >&2; exit 4;;
esac
unset BGVEXT_EXTRA_DEPTH BGVEXT_EVAL_ADD_COUNT BGVEXT_KEY_SWITCH_COUNT BGVEXT_RING_DIM
case $SETTING in
  upstream) ;;
  depth11)  export BGVEXT_EXTRA_DEPTH=1;;
  n128)     export BGVEXT_RING_DIM=128 BGVEXT_EXTRA_DEPTH=1 BGVEXT_EVAL_ADD_COUNT=256;;
  *) echo "unknown setting $SETTING" >&2; exit 4;;
esac
D="${3:-$WORK/runs/$CASE/$SETTING}"; rm -rf "$D"; mkdir -p "$D/trace"
printf "$IN" > "$D/in.txt"
( cd "$D" && FHECHECK_TRACE_DIR="$D/trace" OMP_NUM_THREADS=1 /usr/bin/time -v "$WORK/bin/$BIN" < in.txt \
    > stdout.txt 2> library.time )
echo "library: $(grep Elapsed "$D/library.time" | awk '{print $NF}') wall"
grep -E ' (==|>|>=|<|<=) |^max|^min|Result|division result' "$D/stdout.txt" || true

# 4. extract and check every traced context
rc=0
for p in "$D"/trace/*.params.json; do
  b="${p%.params.json}"; c="$(basename "$b")"
  python3 -I "$ROOT/harness/frontend/openfhe/extract.py" --params "$p" --trace "$b.trace.jsonl" \
    --outputs-from-decrypt > "$D/$c.fhecheck.json"
  n="$(python3 -I -c 'import json,sys; print(len(json.load(open(sys.argv[1]))["program"]["body"]))' "$D/$c.fhecheck.json")"
  set +e
  /usr/bin/time -v "$FC" --no-suggest --max-instructions 0 "$D/$c.fhecheck.json" > "$D/$c.report.txt" 2> "$D/$c.check.time"
  r=$?; set -e; [ $r -gt $rc ] && rc=$r
  # the excerpt committed under reports/: verdict, warnings, parameters, per-output bounds and margins
  grep -E '^(VERDICT|WARNING|NOTE|user-level|Parameters|Outputs)|limb bits|^  Spec\.(schemeParamsOK|Budget\.specialOK)|log2\(Q\*P\) =|^  ct_|phase switched|^First failing|^  overflow' \
    "$D/$c.report.txt" > "$D/$c.excerpt.txt" || true
  echo "$c: $n instructions; $(grep -m1 '^VERDICT' "$D/$c.report.txt")"
  echo "  fhe_check: $(grep Elapsed "$D/$c.check.time" | awk '{print $NF}') wall, $(grep 'Maximum res' "$D/$c.check.time" | awk '{print $NF}') kB peak"
  echo "  trace sha256: $(sha256sum "$b.trace.jsonl" | cut -d' ' -f1)"
done
exit $rc
