#!/usr/bin/env bash
# check_openfhe.sh: from an OpenFHE C++ program to fhe_check's verdict, in one command.
#
#   harness/quickstart/check_openfhe.sh PROGRAM.cpp [-- ARGS...]
#
# 1. builds the supported OpenFHE (upstream v1.6.1 with the observation-only tracer:
#    harness/frontend/openfhe/build_openfhe.sh) into $PROVENFHE_WORK/openfhe, once; later runs reuse it;
# 2. compiles PROGRAM.cpp against it, unmodified (the flags of harness/frontend/openfhe/build.sh);
# 3. runs it with tracing switched on by the environment (FHECHECK_TRACE_DIR, OMP_NUM_THREADS=1),
#    so every BGV or BFV CryptoContext it creates writes a trace and its parameters;
# 4. extracts each context (extract.py for BGV, extract_bfv.py for BFV; outputs = the ciphertexts
#    the program decrypts) and runs fhe_check on it, printing the verdict line of each.
# Exit status: the largest fhe_check exit code over the contexts (0 = every context CERTIFIED,
# 1 NOT CERTIFIED, 2 UNSUPPORTED, 3 INVALID INPUT); 5 if the build, the program or an extraction fails.
#
# Environment:
#   PROVENFHE_WORK  work directory (default ./provenfhe-work): openfhe/ (source, build, install),
#                   runs/<program>/ (binary, traces, extracted files, reports)
#   FHE_CHECK       the fhe_check executable (default: fhe_check on PATH, else
#                   .lake/build/bin/fhe_check of this checkout)
#   OPENFHE_SRC     an existing clone of openfhe-development to build from (default: clone GitHub)
#   JOBS            parallel build jobs (default: nproc)
#   KAPPA           also run fhe_check --kappa KAPPA on each context (e.g. KAPPA=128)
#   CXXFLAGS_EXTRA  extra compiler flags for PROGRAM.cpp
#
# Needs: git, a C++17 compiler, python3; cmake (>= 3.22, < 4) and ninja on PATH, else they are
# installed into $PROVENFHE_WORK/venv with pip (needs network).
set -euo pipefail
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(cd "$HERE/../.." && pwd)"
OF="$ROOT/harness/frontend/openfhe"
[ $# -ge 1 ] || { sed -n '2,30p' "$0"; exit 4; }
PROG="$(cd "$(dirname "$1")" && pwd)/$(basename "$1")"; shift
[ "${1:-}" = "--" ] && shift
[ -f "$PROG" ] || { echo "no such file: $PROG" >&2; exit 4; }
WORK="${PROVENFHE_WORK:-$PWD/provenfhe-work}"; mkdir -p "$WORK"; WORK="$(cd "$WORK" && pwd)"
W="$WORK/openfhe"
NAME="$(basename "$PROG" .cpp)"
RUN="$WORK/runs/$NAME"
t0=$(date +%s)
say() { echo "[check_openfhe $(( $(date +%s) - t0 ))s] $*"; }

# fhe_check
if [ -z "${FHE_CHECK:-}" ]; then
  if command -v fhe_check >/dev/null; then FHE_CHECK="$(command -v fhe_check)"
  elif [ -x "$ROOT/.lake/build/bin/fhe_check" ]; then FHE_CHECK="$ROOT/.lake/build/bin/fhe_check"
  else echo "no fhe_check: put the prebuilt one on PATH (docs/QUICKSTART.md), set FHE_CHECK, or 'lake build fhe_check'" >&2; exit 4; fi
fi

# cmake < 4 and ninja
cmake_ok() { command -v cmake >/dev/null && command -v ninja >/dev/null &&
  cmake --version | awk 'NR==1 { split($3, v, "."); exit !((v[1] == 3 && v[2] >= 22)) }'; }
[ -d "$ROOT/harness/.venv-cpp/bin" ] && export PATH="$ROOT/harness/.venv-cpp/bin:$PATH"
[ -d "$WORK/venv/bin" ] && export PATH="$WORK/venv/bin:$PATH"
if ! cmake_ok; then
  say "cmake >= 3.22 and < 4 with ninja not found: installing them into $WORK/venv (pip)"
  python3 -m venv "$WORK/venv" && "$WORK/venv/bin/pip" -q install "cmake>=3.22,<4" ninja
  export PATH="$WORK/venv/bin:$PATH"
  cmake_ok || { echo "could not provide cmake >= 3.22, < 4 and ninja" >&2; exit 5; }
fi

# 1. the traced library (once)
if [ -f "$W/install/include/openfhe/core/config_core.h" ] && "$OF/check_install.sh" "$W/install" >/dev/null 2>&1; then
  say "traced OpenFHE v1.6.1: reusing $W/install"
else
  say "building the traced OpenFHE v1.6.1 into $W (once; log: $W/build.log)"
  "$OF/build_openfhe.sh" "$W" >"$WORK/build_openfhe.out" 2>&1 || {
    tail -20 "$WORK/build_openfhe.out" >&2; echo "build_openfhe.sh failed (see $WORK/build_openfhe.out)" >&2; exit 5; }
  say "built"
fi
I="$W/install"

# 2. compile the program, unmodified
rm -rf "$RUN"; mkdir -p "$RUN/trace"
say "compiling $PROG"
# shellcheck disable=SC2086
c++ -std=gnu++17 -O2 -fopenmp ${CXXFLAGS_EXTRA:-} \
  -I"$I/include/openfhe" -I"$I/include/openfhe/core" -I"$I/include/openfhe/pke" -I"$I/include/openfhe/binfhe" \
  -I"$I/include/openfhe/cereal" \
  "$PROG" -o "$RUN/$NAME" \
  -L"$I/lib" -Wl,-rpath,"$I/lib" -lOPENFHEpke -lOPENFHEcore -lOPENFHEbinfhe || { echo "compilation failed" >&2; exit 5; }

# 3. run it, traced
say "running $NAME $* (traced; output in $RUN/program.out)"
( cd "$RUN" && FHECHECK_TRACE_DIR="$RUN/trace" OMP_NUM_THREADS=1 "./$NAME" "$@" ) >"$RUN/program.out" 2>&1 || {
  tail -20 "$RUN/program.out" >&2; echo "the program failed (exit $?)" >&2; exit 5; }
shopt -s nullglob
params=("$RUN"/trace/*.params.json)
[ ${#params[@]} -gt 0 ] || { echo "no BGV or BFV CryptoContext was traced (CKKS, BinFHE and schemes other than BGV and BFV are not checked)" >&2; exit 5; }

# 4. extract and check each context
worst=0
for p in "${params[@]}"; do
  base="${p%.params.json}"; ctx="$(basename "$base")"
  scheme="$(python3 -I -c 'import json,sys; d=json.load(open(sys.argv[1])); print(d.get("scheme", "BGV"))' "$p" 2>/dev/null || echo BGV)"
  case "$scheme" in *BFV*|*bfv*) ex="$OF/extract_bfv.py"; scheme=BFV;; *) ex="$OF/extract.py"; scheme=BGV;; esac
  out="$RUN/$ctx.fhecheck.json"
  if ! python3 -I "$ex" --params "$p" --trace "$base.trace.jsonl" --outputs-from-decrypt >"$out" 2>"$RUN/$ctx.extract.err"; then
    # no traced Decrypt: fall back to the extractor's default outputs
    python3 -I "$ex" --params "$p" --trace "$base.trace.jsonl" >"$out" 2>"$RUN/$ctx.extract.err" || {
      echo "$ctx ($scheme): extraction refused: $(tail -3 "$RUN/$ctx.extract.err")"; worst=5; continue; }
  fi
  n="$(python3 -I -c 'import json,sys; print(len(json.load(open(sys.argv[1]))["program"]["body"]))' "$out")"
  set +e
  "$FHE_CHECK" "$out" >"$RUN/$ctx.report.txt"; rc=$?
  set -e
  say "$ctx ($scheme, $n instructions): $(grep -m1 '^VERDICT' "$RUN/$ctx.report.txt")"
  echo "    full report: $RUN/$ctx.report.txt"
  if [ -n "${KAPPA:-}" ]; then
    set +e; "$FHE_CHECK" --kappa "$KAPPA" "$out" >"$RUN/$ctx.kappa$KAPPA.txt"; set -e
    echo "    with --kappa $KAPPA: $(grep -m1 '^VERDICT' "$RUN/$ctx.kappa$KAPPA.txt")"
  fi
  [ $rc -gt $worst ] && worst=$rc
done
say "done"
exit $worst
