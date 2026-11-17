#!/usr/bin/env bash
# Builds libpin_prng.so (if missing or stale) and pin_export_bfv against UPSTREAM OpenFHE v1.6.1
# (commit b59e1f291965f14fbee5172cd83a20f5b856204f) with the frontend's observation-only tracer, as
# installed by harness/frontend/openfhe/build_openfhe.sh [WORKDIR], and writes float_facts.json
# (export/float_facts.sh: the floating-point facts of the library binary, copied into every
# pin.json "build.float") next to the binary. Prints the binary path.
#   OPENFHE_INSTALL   the install prefix (default: harness/build/frontend-openfhe/install)
#   OPENFHE_BUILD     the library's CMake build directory (default: <install>/../build)
#   OPENFHE_PIN_BUILD where bin/ is written (default: harness/build/openfhe-pin)
set -euo pipefail
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(cd "$HERE/../../.." && pwd)"
I="${OPENFHE_INSTALL:-$ROOT/harness/build/frontend-openfhe/install}"
SRC="$ROOT/harness/openfhe-pin/cpp"
OUT="${OPENFHE_PIN_BUILD:-$ROOT/harness/build/openfhe-pin}/bin"
[ -f "$I/include/openfhe/core/config_core.h" ] || { echo "no traced OpenFHE at $I: run harness/frontend/openfhe/build_openfhe.sh" >&2; exit 1; }
grep -q '#define ENABLE_TRACER' "$I/include/openfhe/core/config_core.h" || { echo "$I was built without ENABLE_TRACER" >&2; exit 1; }
! grep -q '^#define WITH_OPENMP' "$I/include/openfhe/core/config_core.h" || { echo "$I was built with WITH_OPENMP=ON; the committed recordings reproduce byte for byte only from the build configuration they were recorded with (single-threaded: build_openfhe.sh, WITH_OPENMP=OFF): rebuild it" >&2; exit 1; }
"$ROOT/harness/frontend/openfhe/check_install.sh" "$I"
[ -f "$I/include/openfhe/pke/utils/fhecheck-tracer.h" ] || { echo "$I has no utils/fhecheck-tracer.h (not built by build_openfhe.sh)" >&2; exit 1; }
mkdir -p "$OUT"
INC=(-I"$I/include/openfhe" -I"$I/include/openfhe/core" -I"$I/include/openfhe/pke" -I"$I/include/openfhe/binfhe" -I"$I/include/openfhe/cereal")
if [ ! -e "$OUT/libpin_prng.so" ] || [ "$SRC/pin_prng.cpp" -nt "$OUT/libpin_prng.so" ]; then
  c++ -std=gnu++17 -O2 -fPIC -shared "${INC[@]}" "$SRC/pin_prng.cpp" -o "$OUT/libpin_prng.so"
fi
c++ -std=gnu++17 -O2 -fopenmp "${INC[@]}" \
  "$SRC/pin_export_bfv.cpp" -o "$OUT/pin_export_bfv.tmp" \
  -L"$I/lib" -Wl,-rpath,"$I/lib" -lOPENFHEpke -lOPENFHEcore -ldl
mv "$OUT/pin_export_bfv.tmp" "$OUT/pin_export_bfv"
OPENFHE_INSTALL="$I" "$HERE/float_facts.sh" --json > "$OUT/float_facts.json.tmp"
mv "$OUT/float_facts.json.tmp" "$OUT/float_facts.json"
echo "$OUT/pin_export_bfv"
