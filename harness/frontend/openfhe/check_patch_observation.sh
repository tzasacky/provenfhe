#!/usr/bin/env bash
# check_patch_observation.sh -- UNTRUSTED. Is openfhe-v1.6.1-tracer.patch observation-only?
#
#   check_patch_observation.sh [WORKDIR]        default WORKDIR: harness/build/patch-observation
#   check_patch_observation.sh --static-only    only part A (seconds; needs a pristine clone)
#
# Writes harness/frontend/openfhe/patch-observation.json (OUT=<path> to write elsewhere) and exits 0
# iff both parts pass. Two independent checks:
#
# A. STATIC (check_patch_observation.py). On a pristine checkout of upstream v1.6.1 (b59e1f29) and a
#    copy with the patch applied, every file the patch touches is classified: a modified source
#    file is compared with the pristine one after deleting comments, whitespace and the hook macros
#    (`IF_TRACE(...)`, `IF_TRACE_(...)` deleted, `REGISTER_IF_TRACE([t,] x)` replaced by `x`: what
#    they expand to with ENABLE_TRACER=OFF, utils/tracing.h). A file is IDENTICAL, or its remaining
#    differences must equal, statement for statement, the residue listed with a reason in
#    patch-residue-allowlist.json; anything else fails. Every hunk is counted by kind. In addition
#    the definitions the ON expansion reaches are checked syntactically: every `registerOutput`
#    definition in tracing.h, simpletracer.h and fhecheck-tracer.h returns its parameter
#    unchanged (`return x;`), and no added line outside the tracer headers calls a non-const
#    mutator on a hooked value (heuristic list in the .py).
#    What A establishes: with ENABLE_TRACER=OFF the patched library computes what v1.6.1 computes
#    (up to the listed residue). What it does NOT establish: that the hooks, when ON, have no
#    effect (the tracer code runs and could in principle write to what it reads); that is B.
#
# B. BEHAVIOURAL (patch_obs_driver.cpp). Builds pristine v1.6.1 and the patched tree with
#    ENABLE_TRACER=ON (same CMake flags as build_openfhe.sh otherwise: Release,
#    WITH_REDUCED_NOISE=OFF, no examples/tests), then runs the same deterministic program against
#    each: OpenFHE's own external-PRNG hook loaded with harness/openfhe-pin/cpp/pin_prng.cpp (no
#    patch needed for it), fixed seed, OMP_NUM_THREADS=1. The program exercises BGV (4 scaling
#    techniques x BV/HYBRID), BFV (4 multiplication techniques x BV/HYBRID) and CKKS (2 scaling
#    techniques): key generation, encryption, every traced evaluation entry point it can reach
#    (add/sub/negate/mult/square/relin/rotate/sum/mod-reduce/level-reduce/rescale/compress/
#    plaintext operations/key switch) and decryption, and prints a 64-bit digest of every resulting
#    ciphertext (every coefficient of every tower plus format, level, noiseScaleDeg) and every
#    decrypted value. Three runs: pristine; patched with no tracer; patched with the fhecheck
#    JsonTracer recording every context (setTracer before KeyGen, as bgv_demo does). The three
#    digest lists must be identical line for line.
#    What B establishes: on these programs and parameters, the patch with tracing ON or OFF changes
#    no value and no PRNG draw. It does not cover programs or parameter sets not run.
#
# A fourth run, when the frontend's own install (harness/build/frontend-openfhe/install, built by
# build_openfhe.sh; FRONTEND_INSTALL=<prefix> to name another) exists: the patched driver against
# it, tracing; also compared line for line.
#
# Environment: OPENFHE_SRC (a clone containing b59e1f29; default: harness/build/frontend-openfhe/src
# if present, else GitHub), JOBS (default 32).
set -euo pipefail
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(cd "$HERE/../../.." && pwd)"
STATIC_ONLY=0
if [ "${1:-}" = "--static-only" ]; then STATIC_ONLY=1; shift; fi
W="${1:-$ROOT/harness/build/patch-observation}"
OUT="${OUT:-$HERE/patch-observation.json}"
COMMIT=b59e1f291965f14fbee5172cd83a20f5b856204f
JOBS="${JOBS:-32}"
[ -d "$ROOT/harness/.venv-cpp/bin" ] && export PATH="$ROOT/harness/.venv-cpp/bin:$PATH"
SRC0="${OPENFHE_SRC:-}"
if [ -z "$SRC0" ]; then
  if [ -d "$ROOT/harness/build/frontend-openfhe/src/.git" ]; then SRC0="$ROOT/harness/build/frontend-openfhe/src"
  else SRC0=https://github.com/openfheorg/openfhe-development.git; fi
fi
mkdir -p "$W"

# a clean checkout of b59e1f29 at $1 (local clones read the source repository only); the submodule
# trees are copied from $SRC0's working tree when it has them, else fetched
checkout() {
  local d="$1"
  if [ ! -d "$d/.git" ]; then
    git clone -q --no-checkout "$SRC0" "$d"
    git -C "$d" checkout -q "$COMMIT"
    for s in third-party/cereal third-party/google-test third-party/google-benchmark; do
      if [ -d "$SRC0/$s" ] && [ -n "$(ls -A "$SRC0/$s" 2>/dev/null)" ]; then
        rm -rf "${d:?}/$s"; mkdir -p "$d/$s"; (cd "$SRC0/$s" && tar --exclude=.git -cf - .) | (cd "$d/$s" && tar -xf -)
      else
        git -C "$d" submodule update --init --quiet "$s"
      fi
    done
  fi
  test "$(git -C "$d" rev-parse HEAD)" = "$COMMIT"
}
checkout "$W/pristine-src"
test -z "$(git -C "$W/pristine-src" status --porcelain --untracked-files=no)" || { echo "$W/pristine-src has local changes" >&2; exit 1; }
checkout "$W/patched-src"
if git -C "$W/patched-src" apply --check "$HERE/openfhe-v1.6.1-tracer.patch" 2>/dev/null; then
  git -C "$W/patched-src" apply "$HERE/openfhe-v1.6.1-tracer.patch"
else
  git -C "$W/patched-src" apply --check -R "$HERE/openfhe-v1.6.1-tracer.patch" 2>/dev/null \
    || { echo "$W/patched-src: the patch neither applies nor is applied" >&2; exit 1; }
fi

STATIC_JSON="$W/static.json"
python3 -I "$HERE/check_patch_observation.py" --pristine "$W/pristine-src" --patched "$W/patched-src" \
  --patch "$HERE/openfhe-v1.6.1-tracer.patch" --allowlist "$HERE/patch-residue-allowlist.json" \
  --out "$STATIC_JSON" || true
if [ "$STATIC_ONLY" = 1 ]; then
  python3 -I "$HERE/check_patch_observation.py" --combine "$STATIC_JSON" --out "$OUT"
  exit $?
fi

# B: two library builds (pristine; patched with ENABLE_TRACER=ON), library only
build() {
  local src="$1" b="$2" i="$3" tr="$4"
  if [ ! -f "$i/lib/libOPENFHEpke.so" ]; then
    cmake -S "$src" -B "$b" -G Ninja -DCMAKE_INSTALL_PREFIX="$i" $tr -DWITH_REDUCED_NOISE=OFF \
      -DBUILD_EXAMPLES=OFF -DBUILD_UNITTESTS=OFF -DBUILD_BENCHMARKS=OFF -DBUILD_EXTRAS=OFF \
      -DCMAKE_BUILD_TYPE=Release -DGIT_SUBMOD_AUTO=OFF > "$b.cmake.log" 2>&1
    cmake --build "$b" -j "$JOBS" > "$b.build.log" 2>&1
    cmake --install "$b" > "$b.install.log" 2>&1
  fi
}
build "$W/pristine-src" "$W/pristine-build" "$W/pristine-install" ""
build "$W/patched-src" "$W/patched-build" "$W/patched-install" "-DENABLE_TRACER=ON"
grep -q '#define ENABLE_TRACER' "$W/patched-install/include/openfhe/core/config_core.h"
! grep -q '#define ENABLE_TRACER' "$W/pristine-install/include/openfhe/core/config_core.h"

# the PRNG engine (against the pristine headers: it uses only utils/prng/prng.h, which the patch
# does not touch) and the driver, compiled once per install with identical flags
I0="$W/pristine-install"
c++ -std=gnu++17 -O2 -fPIC -shared -I"$I0/include/openfhe/core" "$ROOT/harness/openfhe-pin/cpp/pin_prng.cpp" -o "$W/libpinprng.so"
for v in pristine patched; do
  I="$W/$v-install"
  c++ -std=gnu++17 -O2 -fopenmp \
    -I"$I/include/openfhe" -I"$I/include/openfhe/core" -I"$I/include/openfhe/pke" -I"$I/include/openfhe/binfhe" \
    -I"$I/include/openfhe/cereal" "$HERE/patch_obs_driver.cpp" -o "$W/driver-$v" \
    -L"$I/lib" -Wl,-rpath,"$I/lib" -lOPENFHEpke -lOPENFHEcore -ldl
done
export OMP_NUM_THREADS=1
unset FHECHECK_TRACE_DIR || true
"$W/driver-pristine" "$W/libpinprng.so" none > "$W/digests-pristine.txt"
"$W/driver-patched" "$W/libpinprng.so" none > "$W/digests-patched-null.txt"
rm -rf "$W/traces"; mkdir -p "$W/traces"
"$W/driver-patched" "$W/libpinprng.so" json "$W/traces" > "$W/digests-patched-json.txt"
D=("$W/digests-pristine.txt" "$W/digests-patched-null.txt" "$W/digests-patched-json.txt")
# the install the frontend actually uses (build_openfhe.sh), if present: the same patched driver
# against it (RUNPATH, so LD_LIBRARY_PATH takes precedence), tracing every context
FI="${FRONTEND_INSTALL:-$ROOT/harness/build/frontend-openfhe/install}"
if [ -f "$FI/lib/libOPENFHEpke.so" ]; then
  rm -rf "$W/traces-frontend"; mkdir -p "$W/traces-frontend"
  LD_LIBRARY_PATH="$FI/lib" "$W/driver-patched" "$W/libpinprng.so" json "$W/traces-frontend" > "$W/digests-frontend-json.txt"
  D+=("$W/digests-frontend-json.txt")
fi
python3 -I "$HERE/check_patch_observation.py" --combine "$STATIC_JSON" --digests "${D[@]}" \
  --traces "$W/traces" --out "$OUT"
