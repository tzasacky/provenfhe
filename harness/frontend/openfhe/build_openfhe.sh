#!/usr/bin/env bash
# Builds the OpenFHE the frontend supports: UPSTREAM OpenFHE v1.6.1 (openfheorg/openfhe-development,
# tag v1.6.1, commit b59e1f291965f14fbee5172cd83a20f5b856204f) with the observation-only tracer:
#   openfhe-v1.6.1-tracer.patch   ENABLE_TRACER hooks (what each hook records: README "Tracer patch"),
#                                 including src/pke/include/utils/fhecheck-tracer.h as a new file
#                                 (its provenance and sha256: harness/frontend/README.md)
#   fhecheck-tracer.h             the editable source of that header: the patched tree must contain
#                                 exactly this file (checked below; after editing it, regenerate the
#                                 patch with `git diff` in WORKDIR/src, new files added with -N)
# then builds bgv_demo (build.sh) and bfv_demo (build_bfv.sh).
#
#   build_openfhe.sh [WORKDIR]     default WORKDIR: harness/build/frontend-openfhe
#     WORKDIR/src       the patched checkout (cloned once; an existing one is reused, its patch
#                       state is checked)
#     WORKDIR/build     the CMake build tree
#     WORKDIR/install   the install prefix build.sh compiles against
# Environment: OPENFHE_SRC=<path> uses an existing clone of openfhe-development instead of
# cloning from GitHub (it must contain commit b59e1f29); JOBS (default: nproc).
#
# Needs: git, a C++17 compiler (gcc 13.3 used; the programs built against the install use OpenMP's omp.h), cmake >= 3.22 (< 4) and ninja on PATH
# (no sudo: `uv venv harness/.venv-cpp && uv pip install -p harness/.venv-cpp "cmake<4" ninja`;
# this script puts harness/.venv-cpp/bin on PATH if it exists), python3. About 2 minutes on
# 128 cores (library + examples); the library alone is ~20 s there.
set -euo pipefail
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(cd "$HERE/../../.." && pwd)"
W="${1:-$ROOT/harness/build/frontend-openfhe}"
COMMIT=b59e1f291965f14fbee5172cd83a20f5b856204f
SRC="$W/src"
[ -d "$ROOT/harness/.venv-cpp/bin" ] && export PATH="$ROOT/harness/.venv-cpp/bin:$PATH"
mkdir -p "$W"
if [ ! -d "$SRC/.git" ]; then
  git clone -q "${OPENFHE_SRC:-https://github.com/openfheorg/openfhe-development.git}" "$SRC"
  git -C "$SRC" checkout -q "$COMMIT"
  git -C "$SRC" submodule update --init --quiet third-party/cereal third-party/google-test third-party/google-benchmark
fi
test "$(git -C "$SRC" rev-parse HEAD)" = "$COMMIT" || { echo "$SRC is not at $COMMIT" >&2; exit 1; }
if git -C "$SRC" apply --check "$HERE/openfhe-v1.6.1-tracer.patch" 2>/dev/null; then
  git -C "$SRC" apply "$HERE/openfhe-v1.6.1-tracer.patch"
elif git -C "$SRC" apply --check -R "$HERE/openfhe-v1.6.1-tracer.patch" 2>/dev/null; then
  :  # applied
elif git -C "$SRC" apply --check -R --exclude=src/pke/include/utils/fhecheck-tracer.h "$HERE/openfhe-v1.6.1-tracer.patch" 2>/dev/null; then
  # the hooks are applied but the header is an older fhecheck-tracer.h (a stale WORKDIR): update it
  echo "$SRC: updating src/pke/include/utils/fhecheck-tracer.h to the current header" >&2
  cp "$HERE/fhecheck-tracer.h" "$SRC/src/pke/include/utils/fhecheck-tracer.h"
else
  echo "$SRC: the tracer patch neither applies nor is applied (local changes?)" >&2; exit 1
fi
cmp -s "$HERE/fhecheck-tracer.h" "$SRC/src/pke/include/utils/fhecheck-tracer.h" || {
  echo "openfhe-v1.6.1-tracer.patch does not contain the current fhecheck-tracer.h: regenerate the patch" >&2; exit 1; }
# WITH_OPENMP=OFF (OpenFHE's documented CMake option): the committed recordings reproduce byte for byte
# only from the build configuration they were recorded with (single-threaded)
cmake -S "$SRC" -B "$W/build" -G Ninja -DCMAKE_INSTALL_PREFIX="$W/install" -DENABLE_TRACER=ON -DWITH_OPENMP=OFF \
  -DWITH_REDUCED_NOISE=OFF -DBUILD_EXAMPLES=ON -DBUILD_UNITTESTS=OFF -DBUILD_BENCHMARKS=OFF \
  -DCMAKE_BUILD_TYPE=Release -DGIT_SUBMOD_AUTO=OFF > "$W/cmake.log"
cmake --build "$W/build" -j "${JOBS:-$(nproc)}" > "$W/build.log"
cmake --install "$W/build" > "$W/install.log"
"$HERE/build.sh" "$W"
"$HERE/build_bfv.sh" "$W"
