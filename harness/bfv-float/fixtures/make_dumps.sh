#!/usr/bin/env bash
# Regenerates fixtures/dumps.tar.xz and fixtures/SOURCE.txt (needs the OpenFHE v1.6.1 install of
# harness/frontend/openfhe/build_openfhe.sh). The same 15 contexts as run.sh; deterministic archive.
#   fixtures/make_dumps.sh [INSTALL]
set -euo pipefail
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(cd "$HERE/../../.." && pwd)"
I="${1:-$ROOT/harness/build/frontend-openfhe/install}"
W="$(mktemp -d)"
trap 'rm -rf "$W"' EXIT
c++ -std=gnu++17 -O2 -fopenmp \
  -I"$I/include/openfhe" -I"$I/include/openfhe/core" -I"$I/include/openfhe/pke" -I"$I/include/openfhe/binfhe" \
  -I"$I/include/openfhe/cereal" "$HERE/../dump.cpp" -o "$W/dump" \
  -L"$I/lib" -Wl,-rpath,"$I/lib" -lOPENFHEpke -lOPENFHEcore
n=0
for tech in HPS HPSPOVERQ HPSPOVERQLEVELED; do
  for cfg in "1024 2 60" "1024 4 60" "1024 2 45" "1024 3 30" "2048 8 60"; do
    set -- $cfg
    n=$((n + 1))
    OMP_NUM_THREADS=1 "$W/dump" "$tech" "$1" "$2" "$3" "$n" >"$W/dump_${tech}_$1_$2_$3.json"
  done
done
( cd "$W" && LC_ALL=C tar --sort=name --mtime='2026-01-01 00:00:00Z' --owner=0 --group=0 --numeric-owner \
    -cf - dump_*.json | xz -9e -T1 > "$HERE/dumps.tar.xz" )
{
  echo "OpenFHE: upstream openfheorg/openfhe-development v1.6.1, commit b59e1f291965f14fbee5172cd83a20f5b856204f"
  echo "build: harness/frontend/openfhe/build_openfhe.sh (Release, WITH_REDUCED_NOISE=OFF, NATIVEINT 64; observation-only tracer patch, not on these code paths), $(c++ --version | head -1)"
  echo "library flags: -O3 -DNDEBUG -std=gnu++17 -fopenmp (no -march, no -ffast-math); FLT_EVAL_METHOD 0; no FMA instruction in libOPENFHEcore/pke (harness/openfhe-pin/export/float_facts.sh)"
  echo "dumper: harness/bfv-float/dump.cpp (sha256 $(sha256sum "$HERE/../dump.cpp" | cut -d' ' -f1)), 15 contexts: {HPS, HPSPOVERQ, HPSPOVERQLEVELED} x {1024/2/60, 1024/4/60, 1024/2/45, 1024/3/30, 2048/8/60}"
} > "$HERE/SOURCE.txt"
ls -l "$HERE/dumps.tar.xz"
