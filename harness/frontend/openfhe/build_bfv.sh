#!/usr/bin/env bash
# Builds bfv_demo (the BFV driver of the fhe_check OpenFHE frontend) against the traced OpenFHE
# v1.6.1 installed by build_openfhe.sh (which calls this script).
#   build_bfv.sh [WORKDIR]     default WORKDIR: harness/build/frontend-openfhe (bfv_demo is written there)
# Your own BFV program is compiled with the same flags as build.sh describes; FHECHECK_TRACE_DIR
# traces every BFVRNS context as well (params in the format of `bfv_demo dump`).
set -euo pipefail
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(cd "$HERE/../../.." && pwd)"
W="${1:-$ROOT/harness/build/frontend-openfhe}"
I="$W/install"
[ -f "$I/include/openfhe/core/config_core.h" ] || { echo "no traced OpenFHE at $I: run build_openfhe.sh" >&2; exit 1; }
grep -q '#define ENABLE_TRACER' "$I/include/openfhe/core/config_core.h" || { echo "$I was built without ENABLE_TRACER" >&2; exit 1; }
"$HERE/check_install.sh" "$I"
c++ -std=gnu++17 -O2 -fopenmp \
  -I"$I/include/openfhe" -I"$I/include/openfhe/core" -I"$I/include/openfhe/pke" -I"$I/include/openfhe/binfhe" \
  -I"$I/include/openfhe/cereal" \
  "$HERE/bfv_demo.cpp" -o "$W/bfv_demo" \
  -L"$I/lib" -Wl,-rpath,"$I/lib" -lOPENFHEpke -lOPENFHEcore
echo "$W/bfv_demo"
