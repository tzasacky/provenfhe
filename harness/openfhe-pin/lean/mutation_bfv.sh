#!/usr/bin/env bash
# Mutation test of the BFV checks of openfhe_pin: the unmutated executable must pass on the given
# BFV cases, and `--mutate NAME` (ONE trusted BFV definition or ONE number of the budget
# `Challenge.CertifyBFV.budgetBFV` replaced by a wrong copy, FHE/Pin/BFV/Mutants.lean) must make
# some check fail.
#   harness/openfhe-pin/lean/mutation_bfv.sh CASELIST [EXE] [SURVIVORS.tsv]
# CASELIST: one BFV case directory per line. SURVIVORS.tsv (default
# fixtures/MUTANTS_SURVIVING-bfv.tsv if it exists): `mutant<TAB>reason`, the mutants that are
# EXPECTED to survive on this case list. A surviving BUDGET mutant is a measurement, not a hole in
# the harness: the recorded executions stay below the perturbed number, and the table prints by
# how much (largest measured value against the smallest perturbed bound, in bits).
# Prints a table mutant -> verdict, number of failing checks, failing checks; then every survivor
# with its headroom; the last line is `bfv mutants: C caught of M (S surviving: …)`.
# Exit 0 iff the baseline passes, every mutant not listed in SURVIVORS.tsv is caught, and every
# listed one survives. Environment: MUTATION_OUT (output directory), THREADS (per run, default 4),
# JOBS (runs in parallel, default 4).
set -uo pipefail
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(cd "$HERE/../../.." && pwd)"
LIST="${1:?usage: mutation_bfv.sh CASELIST [EXE] [SURVIVORS.tsv]}"
EXE="${2:-$ROOT/.lake/build/bin/openfhe_pin}"
SURV="${3:-$HERE/../fixtures/MUTANTS_SURVIVING-bfv.tsv}"
OUT="${MUTATION_OUT:-${OPENFHE_PIN_BUILD:-$ROOT/harness/build/openfhe-pin}/mutation-bfv}"
THREADS="${THREADS:-4}"
JOBS="${JOBS:-4}"
MUTANTS="delta-round delta-ceil enc-floor mul-no-t mulround-half mulround-textbook mulround-zero mullift-zero mullift-half ks-half ks-zero ks-noleveled ms-half ms-zero plainadd-zero plainadd-rounded wrong-technique slack-idealised fresh-half decrypt-floor automorph-index mul-cyclic bound-no-carry bound-mul-k0"
mkdir -p "$OUT"
run() {  # name
  local m="$1" a=()
  [ "$m" = none ] || a=(--mutate "$m")
  "$EXE" --threads "$THREADS" "${a[@]}" --out "$OUT/$m.jsonl" --list "$LIST" > "$OUT/$m.log" 2>&1
  echo $? > "$OUT/$m.rc"
}
n=0
for m in none $MUTANTS; do
  run "$m" &
  n=$((n + 1))
  if [ $((n % JOBS)) -eq 0 ]; then wait; fi
done
wait
python3 -I "$HERE/mutation_bfv.py" "$OUT" "$SURV" $MUTANTS
