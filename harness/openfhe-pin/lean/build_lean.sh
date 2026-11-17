#!/usr/bin/env bash
# Build openfhe_pin (OpenfhePin.lean over FHE/Pin/*.lean and the trusted Spec/ and Challenge/
# definitions). Prints the executable's path. Exit 0 iff the build succeeds.
#
#   harness/openfhe-pin/lean/build_lean.sh
#       `lake build openfhe_pin` in the repository (lakefile.toml has the `openfhe_pin` target);
#       prints <repo>/.lake/build/bin/openfhe_pin.
#   harness/openfhe-pin/lean/build_lean.sh DIR --subst REL FILE [--subst REL FILE ...]
#       builds in the scratch Lake project DIR with the repository file REL replaced by FILE
#       (e.g. --subst Spec/Ring.lean /tmp/mutated.lean: a mutated TRUSTED definition), without
#       touching the repository or its build directory. The top-level directory holding REL is
#       copied, everything else is symlinked; Mathlib is not rebuilt (.lake/packages is a symlink).
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../../.." && pwd)"
export PATH="$HOME/.elan/bin:$PATH"
if [ $# -eq 0 ]; then
  LOG="$(mktemp "${TMPDIR:-/tmp}/openfhe_pin.build.XXXXXX")"
  if ! ( cd "$ROOT" && lake build openfhe_pin >"$LOG" 2>&1 ); then
    grep -v "^warning\|module system" "$LOG" | tail -40 >&2
    rm -f "$LOG"
    exit 1
  fi
  rm -f "$LOG"
  echo "$ROOT/.lake/build/bin/openfhe_pin"
  exit 0
fi
D="$1"; shift
SUBST=()
while [ $# -gt 0 ]; do
  case "$1" in
    --subst) SUBST+=("$2" "$(realpath "$3")"); shift 3 ;;
    *) echo "unknown option $1" >&2; exit 2 ;;
  esac
done
[ -d "$ROOT/.lake/packages/mathlib" ] || { echo "the repository has no .lake/packages/mathlib (build the repo once first)" >&2; exit 1; }
mkdir -p "$D/.lake"
D="$(cd "$D" && pwd)"
for x in Spec Challenge FHE Validation Spec.lean Challenge.lean FHE.lean Validation.lean lean-toolchain OpenfhePin.lean; do
  [ -e "$ROOT/$x" ] || continue
  top="${x%%/*}"
  copy=0
  for ((i = 0; i < ${#SUBST[@]}; i += 2)); do
    [ "${SUBST[i]%%/*}" = "$top" ] && copy=1
  done
  if [ "$copy" = 1 ]; then
    # a substituted file lives under this top-level directory: copy it (never edit the repo)
    rm -rf "${D:?}/${x:?}"; cp -r "$ROOT/$x" "$D/$x"
  else
    if [ -e "$D/$x" ] && [ ! -L "$D/$x" ]; then rm -rf "${D:?}/${x:?}"; fi
    ln -sfn "$ROOT/$x" "$D/$x"
  fi
done
for ((i = 0; i < ${#SUBST[@]}; i += 2)); do
  cp "${SUBST[i + 1]}" "$D/${SUBST[i]}"
done
ln -sfn "$(realpath "$ROOT/.lake/packages")" "$D/.lake/packages"
cp "$ROOT/lake-manifest.json" "$D/lake-manifest.json"
cat > "$D/lakefile.toml" <<'EOT'
name = "provenfhe"
[leanOptions]
autoImplicit = false
relaxedAutoImplicit = false
[[require]]
name = "mathlib"
git = "https://github.com/leanprover-community/mathlib4"
rev = "v4.35.0"
[[lean_lib]]
name = "Spec"
[[lean_lib]]
name = "Challenge"
[[lean_lib]]
name = "Validation"
[[lean_lib]]
name = "FHE"
[[lean_exe]]
name = "openfhe_pin"
root = "OpenfhePin"
EOT
( cd "$D" && lake build openfhe_pin >"$D/build.log" 2>&1 ) || { grep -v "^warning\|module system" "$D/build.log" | tail -40 >&2; exit 1; }
echo "$D/.lake/build/bin/openfhe_pin"
