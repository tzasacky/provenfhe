#!/usr/bin/env bash
# float_facts.sh [--json|--text]
# Floating-point facts of the OpenFHE LIBRARY BINARY the BFV cases are recorded from (the HPS-family
# multiplication and decryption use binary64 sums: DCRTPolyImpl::ScaleAndRound, SwitchCRTBasis,
# ExpandCRTBasis..., core/include/lattice/hal/default/dcrtpoly-impl.h). Determined, not assumed:
#   flags      the compile FLAGS/DEFINES lines of the library objects, read from the CMake build
#              directory's build.ninja (OPENFHE_BUILD, default <install>/../build)
#   FLT_EVAL_METHOD, __FAST_MATH__, __FMA__, -ffp-contract
#              a probe compiled with exactly those flags by the same compiler
#   fma        objdump -d of libOPENFHEcore.so / libOPENFHEpke.so: number of vfmadd/vfnmadd/vfmsub/
#              vfnmsub instructions in the whole library (the float code of the DCRTPoly templates
#              is instantiated in libOPENFHEcore.so and inlined copies live in libOPENFHEpke.so)
#   x87        number of x87 arithmetic instructions, and the functions holding ANY x87 instruction
#              (loads, stores, conversions, arithmetic: objdump -d -C, by symbol); on the recorded
#              build they are all in DiscreteGaussianGeneratorGeneric (not the sampler BFVRNS uses,
#              and not in the multiplication or decryption sums)
# Output: one JSON object (--json, default) or key: value lines (--text).
set -euo pipefail
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(cd "$HERE/../../.." && pwd)"
I="${OPENFHE_INSTALL:-$ROOT/harness/build/frontend-openfhe/install}"
B="${OPENFHE_BUILD:-$I/../build}"
MODE="${1:---json}"
TMP="$(mktemp -d)"
trap 'rm -rf "$TMP"' EXIT
NINJA="$B/build.ninja"
[ -f "$NINJA" ] || { echo "no $NINJA (set OPENFHE_BUILD)" >&2; exit 1; }
# the distinct flag sets of the core and pke library objects
flagsOf() {
  awk -v pat="$1" '
    /^build / { hit = index($0, pat) > 0 && index($0, ".cpp.o:") > 0 }
    hit && /^  FLAGS = / { sub(/^  FLAGS = /, ""); f[$0]++ }
    hit && /^  DEFINES = / { sub(/^  DEFINES = /, ""); d[$0]++ }
    END { for (x in f) for (y in d) print x " | " y }' "$NINJA" | LC_ALL=C sort -u
}
CORE_FLAGS="$(flagsOf 'src/core/CMakeFiles/coreobj.dir/')"
PKE_FLAGS="$(flagsOf 'src/pke/CMakeFiles/pkeobj.dir/')"
[ "$(printf '%s\n' "$CORE_FLAGS" | wc -l)" = 1 ] || { echo "core objects have more than one flag set:" >&2; echo "$CORE_FLAGS" >&2; exit 1; }
[ "$(printf '%s\n' "$PKE_FLAGS" | wc -l)" = 1 ] || { echo "pke objects have more than one flag set:" >&2; echo "$PKE_FLAGS" >&2; exit 1; }
FLAGS="${CORE_FLAGS%% | *}"
CXX="$(sed -n 's/^CMAKE_CXX_COMPILER:[A-Z]*=//p' "$B/CMakeCache.txt")"
cat > "$TMP/probe.cpp" <<'EOF'
#include <cfloat>
#include <cstdio>
int main() {
    printf("%d", (int)FLT_EVAL_METHOD);
#ifdef __FAST_MATH__
    printf(" 1");
#else
    printf(" 0");
#endif
#ifdef __FMA__
    printf(" 1");
#else
    printf(" 0");
#endif
#ifdef __SSE2_MATH__
    printf(" 1");
#else
    printf(" 0");
#endif
    printf(" %d %d\n", LDBL_MANT_DIG, DBL_MANT_DIG);
    return 0;
}
EOF
# shellcheck disable=SC2086
"$CXX" $FLAGS "$TMP/probe.cpp" -o "$TMP/probe"
read -r FEM FAST FMAMACRO SSE2 LDM DBM < <("$TMP/probe")
# shellcheck disable=SC2086
CONTRACT="$("$CXX" $FLAGS -Q --help=optimizers 2>/dev/null | awk '/-ffp-contract=/ { print $2 }' || true)"
# shellcheck disable=SC2086
MARCH="$("$CXX" $FLAGS -Q --help=target 2>/dev/null | awk '$1 == "-march=" { print $2 }' || true)"
count() { objdump -d --no-show-raw-insn "$1" | grep -cE "$2" || true; }
CORE="$(readlink -f "$I/lib/libOPENFHEcore.so")"
PKE="$(readlink -f "$I/lib/libOPENFHEpke.so")"
FMA_CORE="$(count "$CORE" '[[:space:]]vfn?m(add|sub)[0-9]+[ps][sd][[:space:]]')"
FMA_PKE="$(count "$PKE" '[[:space:]]vfn?m(add|sub)[0-9]+[ps][sd][[:space:]]')"
X87_CORE="$(count "$CORE" '[[:space:]]f(mul|add|sub|div)[a-z]*[[:space:]]')"
X87_PKE="$(count "$PKE" '[[:space:]]f(mul|add|sub|div)[a-z]*[[:space:]]')"
SSE_CORE="$(count "$CORE" '[[:space:]](mulsd|addsd|subsd|divsd)[[:space:]]')"
SSE_PKE="$(count "$PKE" '[[:space:]](mulsd|addsd|subsd|divsd)[[:space:]]')"
x87fns() {
  objdump -d -C --no-show-raw-insn "$1" | awk '/^[0-9a-f]+ <.*>:$/ { sym = $0; sub(/^[0-9a-f]+ </, "", sym); sub(/>:$/, "", sym); sub(/\(.*/, "", sym) }
    /\t(fld|fstp|fild|fistp|fisttp|fmul|fadd|fsub|fdiv|fxch|fucom|fcom|fchs|fabs)[a-z0-9]*( |$)/ { c[sym]++ }
    END { for (s in c) printf "%s (%d); ", s, c[s] }'
}
X87FN_CORE="$(x87fns "$CORE")"
X87FN_PKE="$(x87fns "$PKE")"
unsafe=false
case " $FLAGS " in *" -ffast-math "*|*" -Ofast "*|*" -funsafe-math-optimizations "*|*" -ffinite-math-only "*|*" -fassociative-math "*) unsafe=true;; esac
native=false
case " $FLAGS " in *" -march="*|*" -mfma "*|*" -mavx2 "*|*" -mtune=native "*) native=true;; esac
fastMath=false; { [ "$FAST" = 1 ] || [ $unsafe = true ]; } && fastMath=true
fmaC=false; { [ "$FMA_CORE" != 0 ] || [ "$FMA_PKE" != 0 ] || [ "$FMAMACRO" = 1 ]; } && fmaC=true
HOW="flags: FLAGS/DEFINES of the coreobj and pkeobj objects in the CMake build.ninja (one flag set each); FLT_EVAL_METHOD, __FAST_MATH__, __FMA__: a probe compiled by the same compiler with exactly those flags; fmaContraction: -ffp-contract=$CONTRACT is the compiler default but no -march/-mfma is given (target $MARCH, __FMA__ = $FMAMACRO) and objdump -d of the installed libOPENFHEcore.so and libOPENFHEpke.so finds $FMA_CORE and $FMA_PKE vfmadd/vfnmadd/vfmsub/vfnmsub instructions (scalar SSE2 mulsd/addsd/subsd/divsd: $SSE_CORE and $SSE_PKE; x87 fmul/fadd/fsub/fdiv, i.e. long double arithmetic: $X87_CORE and $X87_PKE; functions with any x87 instruction: libOPENFHEcore: ${X87FN_CORE:-none}libOPENFHEpke: ${X87FN_PKE:-none})"
if [ "$MODE" = --text ]; then
  echo "compiler: $("$CXX" --version | head -1)"
  echo "cxx flags (libOPENFHEcore objects): $CORE_FLAGS"
  echo "cxx flags (libOPENFHEpke objects): $PKE_FLAGS"
  echo "float: FLT_EVAL_METHOD=$FEM fastMath=$fastMath (-ffast-math/-Ofast/-funsafe-math-optimizations in flags: $unsafe; __FAST_MATH__=$FAST) -ffp-contract=$CONTRACT march=$MARCH -march/-mfma in flags: $native __FMA__=$FMAMACRO __SSE2_MATH__=$SSE2 LDBL_MANT_DIG=$LDM DBL_MANT_DIG=$DBM"
  echo "float: fmaContraction=$fmaC; FMA instructions: libOPENFHEcore $FMA_CORE, libOPENFHEpke $FMA_PKE; SSE2 scalar double arithmetic: $SSE_CORE, $SSE_PKE; x87 arithmetic (long double): $X87_CORE, $X87_PKE"
  echo "float: how: $HOW"
else
  python3 -I - "$FEM" "$fastMath" "$fmaC" "$FLAGS" "$CONTRACT" "$MARCH" "$FMA_CORE" "$FMA_PKE" "$X87_CORE" "$X87_PKE" "$LDM" "$HOW" <<'PY'
import json, sys
a = sys.argv[1:]
print(json.dumps({"FLT_EVAL_METHOD": int(a[0]), "fastMath": a[1] == "true", "fmaContraction": a[2] == "true",
                  "cxxFlags": a[3], "fpContract": a[4], "march": a[5],
                  "fmaInstructions": {"libOPENFHEcore": int(a[6]), "libOPENFHEpke": int(a[7])},
                  "x87Instructions": {"libOPENFHEcore": int(a[8]), "libOPENFHEpke": int(a[9])},
                  "LDBL_MANT_DIG": int(a[10]), "how": a[11]}))
PY
fi
