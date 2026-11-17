#!/usr/bin/env bash
# The gate entry of the proved reference implementation (docs/REFERENCE-IMPLEMENTATION.md): one seed
# of `provenfhe_ref all` at N = 2^13 (about 15 s): for BGV and BFV, key generation, encryption,
# the accepted example circuits evaluated and decrypted and compared with `sem`, the rejected ones
# refused. Prints ONE line, `ref: PASS: ...` or `ref: FAIL: ...`; exit 0 iff the run says ALL PASS.
#   PROVENFHE_REF=<exe> harness/ref/difftest.sh     use an already built executable
set -uo pipefail
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(cd "$HERE/../.." && pwd)"
EXE="${PROVENFHE_REF:-}"
if [ -z "$EXE" ]; then
  (cd "$ROOT" && lake build provenfhe_ref) >/dev/null 2>&1 || { echo "ref: FAIL: lake build provenfhe_ref"; exit 1; }
  EXE="$ROOT/.lake/build/bin/provenfhe_ref"
fi
out="$("$EXE" all 1 1 13 2>&1)"; rc=$?
last="$(tail -n 1 <<<"$out")"
if [ $rc -eq 0 ] && [[ "$last" == *"ALL PASS" ]]; then echo "ref: PASS: seed 1, N = 2^13: $last"; exit 0; fi
tail -n 20 <<<"$out"; echo "ref: FAIL: exit $rc: $last"; exit 1
