#!/usr/bin/env bash
# Records the tamper fixtures harness/frontend/tests/tamper/<scheme>_<mode>/{params.json,trace.jsonl}:
# real runs of tamper_demo.cpp (small unmodified-style OpenFHE programs that change a ciphertext,
# plaintext, key or parameter through the public API OUTSIDE the traced calls), traced through
# FHECHECK_TRACE_DIR on the traced OpenFHE v1.6.1 of build_openfhe.sh. tests/run.sh (section 6c)
# requires the extractors to refuse every one except `honest` (tests/tamper/expected.tsv).
#   make_tamper.sh [WORKDIR] [OUTROOT]   WORKDIR: the build_openfhe.sh work directory
#                                         (default harness/build/frontend-openfhe); OUTROOT: default
#                                         the repository's harness/frontend/tests/tamper
set -euo pipefail
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(cd "$HERE/../../.." && pwd)"
W="${1:-$ROOT/harness/build/frontend-openfhe}"
OUT="${2:-$ROOT/harness/frontend/tests/tamper}"
I="$W/install"
[ -f "$I/include/openfhe/pke/utils/fhecheck-tracer.h" ] || { echo "no traced OpenFHE at $I: run build_openfhe.sh" >&2; exit 1; }
cmp -s "$HERE/fhecheck-tracer.h" "$I/include/openfhe/pke/utils/fhecheck-tracer.h" \
  || { echo "$I was built with another fhecheck-tracer.h: rebuild with build_openfhe.sh" >&2; exit 1; }
c++ -std=gnu++17 -O2 -fopenmp \
  -I"$I/include/openfhe" -I"$I/include/openfhe/core" -I"$I/include/openfhe/pke" -I"$I/include/openfhe/binfhe" \
  -I"$I/include/openfhe/cereal" "$HERE/tamper_demo.cpp" -o "$W/tamper_demo" \
  -L"$I/lib" -Wl,-rpath,"$I/lib" -lOPENFHEpke -lOPENFHEcore
export OMP_NUM_THREADS=1
TMP="$(mktemp -d)"; trap 'rm -rf "$TMP"' EXIT
for s in bfv bgv; do
  for m in honest nocheck addnocheck elements setlevel midmutate ptelement ptother relinkey setparam; do
    # BGV ptother: OpenFHE itself throws (modulus mismatch), so there is nothing to refuse
    [ "$s/$m" = bgv/ptother ] && continue
    d="$TMP/${s}_$m"; mkdir -p "$d"
    FHECHECK_TRACE_DIR="$d" "$W/tamper_demo" "$s" "$m" > "$d/log" 2>&1
    mkdir -p "$OUT/${s}_$m"
    # the first context's files (ptother also writes the second context's, which is not the program's)
    cp "$d"/p*.ctx1.params.json "$OUT/${s}_$m/params.json"
    cp "$d"/p*.ctx1.trace.jsonl "$OUT/${s}_$m/trace.jsonl"
    echo "${s}_$m: $(wc -l < "$OUT/${s}_$m/trace.jsonl") trace lines"
  done
done
