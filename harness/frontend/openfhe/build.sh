#!/usr/bin/env bash
# Builds bgv_demo against the traced OpenFHE v1.6.1 installed by build_openfhe.sh.
#   build.sh [WORKDIR]     default WORKDIR: harness/build/frontend-openfhe (bgv_demo is written there)
# To compile YOUR OWN program for tracing, use the same flags: -std=gnu++17 -fopenmp, the include
# directories below, and -lOPENFHEpke -lOPENFHEcore with the rpath. ENABLE_TRACER is defined by the
# installed config_core.h. Then run it with FHECHECK_TRACE_DIR=<dir> OMP_NUM_THREADS=1 (every BGV
# context writes <dir>/p<pid>.ctx<k>.{trace.jsonl,params.json}), or call setTracer yourself as
# bgv_demo.cpp does, BEFORE KeyGen.
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
  "$HERE/bgv_demo.cpp" -o "$W/bgv_demo" \
  -L"$I/lib" -Wl,-rpath,"$I/lib" -lOPENFHEpke -lOPENFHEcore
echo "$W/bgv_demo"
