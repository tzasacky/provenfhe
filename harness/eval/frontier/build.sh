#!/usr/bin/env bash
# Builds the frontier drivers.
#   build.sh OUTDIR [TRACED_INSTALL] [PRISTINE_INSTALL]
# TRACED_INSTALL   OpenFHE v1.6.1 with the fhe_check tracer, built single-threaded
#                  (default harness/build/frontend-openfhe-noomp/install)
# PRISTINE_INSTALL unmodified OpenFHE v1.6.1 (default harness/build/reports-openfhe/install)
# Writes OUTDIR/frontier_bgv, OUTDIR/frontier_bfv (traced runs) and OUTDIR/frontier_time (timing).
set -euo pipefail
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(cd "$HERE/../../.." && pwd)"
OUT="${1:?usage: build.sh OUTDIR [TRACED_INSTALL] [PRISTINE_INSTALL]}"
T="${2:-$ROOT/harness/build/frontend-openfhe-noomp/install}"
P="${3:-$ROOT/harness/build/reports-openfhe/install}"
mkdir -p "$OUT"
grep -q '#define ENABLE_TRACER' "$T/include/openfhe/core/config_core.h" || { echo "$T: not a traced build" >&2; exit 1; }
if grep -q '#define ENABLE_TRACER' "$P/include/openfhe/core/config_core.h" 2>/dev/null; then
  echo "$P: has the tracer; the timing install must be pristine" >&2; exit 1
fi
inc() { echo -I"$1/include/openfhe" -I"$1/include/openfhe/core" -I"$1/include/openfhe/pke" -I"$1/include/openfhe/binfhe" -I"$1/include/openfhe/cereal"; }
pids=()
for s in bgv bfv; do
  c++ -std=gnu++17 -O2 $(inc "$T") "$HERE/src/frontier_$s.cpp" -o "$OUT/frontier_$s" \
    -L"$T/lib" -Wl,-rpath,"$T/lib" -lOPENFHEpke -lOPENFHEcore & pids+=($!)
done
c++ -std=gnu++17 -O2 -fopenmp $(inc "$P") "$HERE/src/frontier_time.cpp" -o "$OUT/frontier_time" \
  -L"$P/lib" -Wl,-rpath,"$P/lib" -lOPENFHEpke -lOPENFHEcore & pids+=($!)
for p in "${pids[@]}"; do wait "$p"; done
echo "built $OUT/frontier_bgv $OUT/frontier_bfv $OUT/frontier_time"
