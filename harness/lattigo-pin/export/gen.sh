#!/bin/bash
# Build the exporter offline against Lattigo v6.2.0 from the Go module cache and write all suites.
# usage: gen.sh [OUT_DIR]   (default harness/lattigo-pin/out/cases, not committed)
set -euo pipefail
HERE="$(cd "$(dirname "$0")" && pwd)"
OUT="${1:-$HERE/../out/cases}"
BIN="${LATTIGOPIN_BIN:-$HERE/../out/lattigopin}"
export PATH="/usr/local/go/bin:$PATH" GOFLAGS=-mod=mod GOPROXY=off GOTOOLCHAIN=local
mkdir -p "$(dirname "$BIN")" "$OUT"
(cd "$HERE" && go vet . && go build -o "$BIN" .)
rm -rf "$OUT/honest" "$OUT/defectB" "$OUT/defectN" "$OUT/scale"
"$BIN" -out "$OUT"
for s in honest defectB defectN scale; do
  echo "$s: $(ls "$OUT/$s"/*.json | wc -l) files"
done
