#!/usr/bin/env bash
# Builds the evaluation driver cks26 against the traced OpenFHE v1.6.1 of
# harness/frontend/openfhe/build_openfhe.sh (default work directory harness/build/frontend-openfhe).
#   build.sh [OUTDIR]     default OUTDIR: harness/build/cks26 (gitignored)
set -euo pipefail
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(cd "$HERE/../../.." && pwd)"
I="${OPENFHE_INSTALL:-$ROOT/harness/build/frontend-openfhe/install}"
O="${1:-$ROOT/harness/build/cks26}"
[ -f "$I/include/openfhe/pke/utils/fhecheck-tracer.h" ] || { echo "no traced OpenFHE at $I: run harness/frontend/openfhe/build_openfhe.sh" >&2; exit 1; }
cmp -s "$I/include/openfhe/pke/utils/fhecheck-tracer.h" "$ROOT/harness/frontend/openfhe/fhecheck-tracer.h" || {
  echo "$I was built with another fhecheck-tracer.h than this checkout's: rebuild it" >&2; exit 1; }
mkdir -p "$O"
c++ -std=gnu++17 -O2 -fopenmp \
  -I"$I/include/openfhe" -I"$I/include/openfhe/core" -I"$I/include/openfhe/pke" -I"$I/include/openfhe/binfhe" \
  -I"$I/include/openfhe/cereal" \
  "$HERE/cks26.cpp" -o "$O/cks26" \
  -L"$I/lib" -Wl,-rpath,"$I/lib" -lOPENFHEpke -lOPENFHEcore
echo "$O/cks26"
