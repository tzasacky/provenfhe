#!/usr/bin/env bash
# make_dist.sh: the prebuilt fhe_check for Linux x86-64 (docs/QUICKSTART.md, path 1).
#
#   harness/quickstart/make_dist.sh [OUTDIR]      default OUTDIR: harness/build/dist
#
# Builds fhe_check (lake build fhe_check) unless FHE_CHECK names an executable, and writes
#   OUTDIR/fhe_check-linux-x86_64/            fhe_check (stripped), examples/, run-examples.sh,
#                                             QUICKSTART.md, LICENSE, NOTICE, SOURCE (commit)
#   OUTDIR/fhe_check-linux-x86_64.tar.gz      the same directory, packed (and .tar.xz, smaller)
#   OUTDIR/fhe_check-linux-x86_64.sha256      sha256 of both archives
# The executable is the one Lean's toolchain links: dynamically linked against glibc only
# (libc, libm, libpthread, libdl, librt; symbol versions up to GLIBC_2.17, checked below), no
# other library; it reads no file besides its input. Needs: lake (unless FHE_CHECK), strip, gzip, xz,
# sha256sum, objdump.
set -euo pipefail
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(cd "$HERE/../.." && pwd)"
OUT="${1:-$ROOT/harness/build/dist}"
NAME=fhe_check-linux-x86_64
D="$OUT/$NAME"
if [ -z "${FHE_CHECK:-}" ]; then
  (cd "$ROOT" && lake build fhe_check)
  FHE_CHECK="$ROOT/.lake/build/bin/fhe_check"
fi
rm -rf "$D"; mkdir -p "$D/examples"
strip -o "$D/fhe_check" "$FHE_CHECK"
# the dynamic dependencies: glibc only, symbol versions <= 2.17
deps="$(objdump -p "$D/fhe_check" | awk '/NEEDED/ {print $2}' | sort | tr '\n' ' ')"
case "$deps" in "ld-linux-x86-64.so.2 libc.so.6 libdl.so.2 libm.so.6 libpthread.so.0 librt.so.1 "|"libc.so.6 libdl.so.2 libm.so.6 libpthread.so.0 librt.so.1 ") ;;
  *) echo "unexpected dynamic dependencies: $deps" >&2; exit 1;; esac
maxg="$(objdump -T "$D/fhe_check" | grep -o 'GLIBC_[0-9.]*' | sort -uV | tail -1)"
[ "$(printf '%s\n%s\n' "$maxg" GLIBC_2.17 | sort -V | tail -1)" = GLIBC_2.17 ] || {
  echo "the executable needs $maxg (more than GLIBC_2.17)" >&2; exit 1; }
EX="$ROOT/harness/frontend/examples"
cp "$EX/openfhe_dot_depth2.fhecheck.json"         "$D/examples/bgv_certified.fhecheck.json"
cp "$EX/openfhe_bfv_default_dot_d2.fhecheck.json" "$D/examples/bfv_certified.fhecheck.json"
cp "$EX/openfhe_depth2_fixedmanual.fhecheck.json" "$D/examples/bgv_refused.fhecheck.json"
cp "$HERE/run-examples.sh" "$D/run-examples.sh"
cp "$ROOT/docs/QUICKSTART.md" "$ROOT/LICENSE" "$ROOT/NOTICE" "$D/"
cp "$ROOT/harness/frontend/fhe-check-v1.schema.json" "$D/"
commit="$(git -C "$ROOT" rev-parse HEAD 2>/dev/null || echo "unknown (not a git checkout)")"
dirty="$(git -C "$ROOT" diff --quiet HEAD -- FHE FheCheck.lean Spec Challenge 2>/dev/null || echo ' (with uncommitted changes, or not a git checkout)')"
{ echo "fhe_check built from commit $commit$dirty";
  echo "dynamic dependencies: $deps(symbol versions up to $maxg)";
  echo "examples: bgv_certified = harness/frontend/examples/openfhe_dot_depth2, bfv_certified = openfhe_bfv_default_dot_d2, bgv_refused = openfhe_depth2_fixedmanual"; } >"$D/SOURCE"
# .tar.gz: gzip is in every base image (minimal images such as ubuntu-base lack xz); .tar.xz: smaller
tar -C "$OUT" -czf "$OUT/$NAME.tar.gz" "$NAME"
tar -C "$OUT" -cJf "$OUT/$NAME.tar.xz" "$NAME"
(cd "$OUT" && sha256sum "$NAME.tar.gz" "$NAME.tar.xz" >"$NAME.sha256")
ls -l "$OUT/$NAME.tar.gz" "$OUT/$NAME.tar.xz" "$D/fhe_check"
cat "$OUT/$NAME.sha256"
