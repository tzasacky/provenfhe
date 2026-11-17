#!/usr/bin/env bash
# check_heir.sh: from a HEIR program to fhe_check's verdict, in one command.
#
#   harness/quickstart/check_heir.sh PROG.mlir [NOISE_MODEL]
#
# PROG.mlir is either
#   * a HEIR INPUT program (e.g. HEIR's tests/Examples/common/*.mlir): it is compiled for BGV on the
#     Lattigo backend with HEIR's pinned nightly heir-opt (downloaded into $PROVENFHE_WORK once and
#     checked against its sha256), with NOISE_MODEL (default bgv-noise-by-bound-coeff-worst-case,
#     the model whose parameters are meant to meet a worst-case analysis; HEIR's own default is
#     bgv-noise-kpz21); or
#   * HEIR's OUTPUT for that path (bgv dialect with lattigo types, e.g.
#     harness/frontend/examples/heir_*.lattigo.*.mlir): used as it is.
# Then harness/frontend/heir/extract_bgv.py writes the fhe-check/v1 file and fhe_check prints the
# verdict. Exit status: fhe_check's (0 CERTIFIED, 1 NOT CERTIFIED, 2 UNSUPPORTED, 3 INVALID INPUT);
# 5 if compiling or extracting fails.
#
# Environment: PROVENFHE_WORK (default ./provenfhe-work; holds heir-opt and runs/<name>/),
# FHE_CHECK (default fhe_check on PATH, else .lake/build/bin/fhe_check), HEIR_OPT (an existing
# heir-opt). Needs python3 and, for an input program, curl (Linux x86-64, glibc >= 2.28 for heir-opt).
set -euo pipefail
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(cd "$HERE/../.." && pwd)"
[ $# -ge 1 ] || { sed -n '2,22p' "$0"; exit 4; }
SRC="$(cd "$(dirname "$1")" && pwd)/$(basename "$1")"
MODEL="${2:-bgv-noise-by-bound-coeff-worst-case}"
[ -f "$SRC" ] || { echo "no such file: $SRC" >&2; exit 4; }
WORK="${PROVENFHE_WORK:-$PWD/provenfhe-work}"; mkdir -p "$WORK"; WORK="$(cd "$WORK" && pwd)"
NAME="$(basename "$SRC" .mlir)"; RUN="$WORK/runs/$NAME${2:+.$2}"; rm -rf "$RUN"; mkdir -p "$RUN"
NIGHTLY=nightly-2026.11.11   # HEIR commit 86d9fc0acd760bee21003830a6cfba54d6182bec
SHA=ff9a597eb115dcf6ad29d21ee599b25a6b9d278d70dec6abdb0a9b93bc5f078b
t0=$(date +%s)
say() { echo "[check_heir $(( $(date +%s) - t0 ))s] $*"; }
if [ -z "${FHE_CHECK:-}" ]; then
  if command -v fhe_check >/dev/null; then FHE_CHECK="$(command -v fhe_check)"
  elif [ -x "$ROOT/.lake/build/bin/fhe_check" ]; then FHE_CHECK="$ROOT/.lake/build/bin/fhe_check"
  else echo "no fhe_check: put the prebuilt one on PATH (docs/QUICKSTART.md), set FHE_CHECK, or 'lake build fhe_check'" >&2; exit 4; fi
fi
if grep -q 'lattigo\|bgv\.schemeParam\|#bgv\.scheme_param' "$SRC"; then
  say "$NAME: already HEIR output (bgv dialect, Lattigo backend)"
  cp "$SRC" "$RUN/prog.bgv.mlir"
else
  HEIR="${HEIR_OPT:-$WORK/heir-opt}"
  if [ ! -x "$HEIR" ]; then
    say "downloading heir-opt $NIGHTLY (once)"
    curl -sfL -o "$WORK/heir-opt.tmp" "https://github.com/google/heir/releases/download/$NIGHTLY/heir-opt-manylinux_2_28_x86_64"
    echo "$SHA  $WORK/heir-opt.tmp" | sha256sum -c --quiet || { echo "heir-opt: sha256 mismatch" >&2; exit 5; }
    chmod +x "$WORK/heir-opt.tmp"; mv "$WORK/heir-opt.tmp" "$WORK/heir-opt"; HEIR="$WORK/heir-opt"
  fi
  say "compiling $NAME with heir-opt (BGV, Lattigo backend, noise model $MODEL)"
  # loops are unrolled, as HEIR's own tests do for the examples with loops
  "$HEIR" --annotate-module="backend=lattigo scheme=bgv" \
    --mlir-to-bgv="noise-model=$MODEL annotate-noise-bound=true unroll-fhe-kernel-loops=true" \
    "$SRC" >"$RUN/prog.bgv.mlir" 2>"$RUN/heir.err" || {
      tail -5 "$RUN/heir.err" >&2; echo "heir-opt failed (see $RUN/heir.err)" >&2; exit 5; }
fi
python3 -I "$ROOT/harness/frontend/heir/extract_bgv.py" "$RUN/prog.bgv.mlir" >"$RUN/prog.fhecheck.json" 2>"$RUN/extract.err" || {
  tail -3 "$RUN/extract.err" >&2; echo "extraction failed (see $RUN/extract.err)" >&2; exit 5; }
n="$(python3 -I -c 'import json,sys; print(len(json.load(open(sys.argv[1]))["program"]["body"]))' "$RUN/prog.fhecheck.json")"
set +e; "$FHE_CHECK" "$RUN/prog.fhecheck.json" >"$RUN/report.txt"; rc=$?; set -e
say "$NAME ($n instructions): $(grep -m1 '^VERDICT' "$RUN/report.txt")"
echo "    full report: $RUN/report.txt"
[ $rc = 1 ] && echo "    parameters that certify: fhe_check recommend $RUN/prog.fhecheck.json"
exit $rc
