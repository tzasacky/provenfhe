#!/usr/bin/env bash
# Cross-check of Challenge/BFVMul/Float.lean (UNTRUSTED; evidence, not proof).
#   run.sh [INSTALL]    INSTALL: an OpenFHE v1.6.1 install prefix
#                       (default: harness/build/frontend-openfhe/install, built by
#                       harness/frontend/openfhe/build_openfhe.sh; skipped if absent)
# 1. check.py synth: the binary64 sums against the proved bounds, on the parameter sets of the
#    committed OpenFHE BFV examples and synthetic ones.
# 2. dump.cpp + check.py real: the real DCRTPoly::SwitchCRTBasis / ScaleAndRound and the
#    library's double tables against the transcription.
set -euo pipefail
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(cd "$HERE/../.." && pwd)"
I="${1:-$ROOT/harness/build/frontend-openfhe/install}"
W="${WORK:-$(mktemp -d)}"
python3 "$HERE/check.py" synth --trials "${TRIALS:-2000}"
if [ ! -f "$I/include/openfhe/core/config_core.h" ]; then
  echo "no OpenFHE install at $I: the comparison with the real functions is SKIPPED"; exit 0
fi
c++ -std=gnu++17 -O2 -fopenmp \
  -I"$I/include/openfhe" -I"$I/include/openfhe/core" -I"$I/include/openfhe/pke" -I"$I/include/openfhe/binfhe" \
  -I"$I/include/openfhe/cereal" "$HERE/dump.cpp" -o "$W/dump" \
  -L"$I/lib" -Wl,-rpath,"$I/lib" -lOPENFHEpke -lOPENFHEcore
n=0
for tech in HPS HPSPOVERQ HPSPOVERQLEVELED; do
  for cfg in "1024 2 60" "1024 4 60" "1024 2 45" "1024 3 30" "2048 8 60"; do
    set -- $cfg
    n=$((n + 1))
    "$W/dump" "$tech" "$1" "$2" "$3" "$n" >"$W/dump_${tech}_$1_$2_$3.json"
  done
done
python3 "$HERE/check.py" real "$W"/dump_*.json
