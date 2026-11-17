#!/usr/bin/env bash
# The step-7 (mutation) suite of the OpenFHE conformance harness, from the COMMITTED fixtures only
# (no OpenFHE). Every mutant is a deliberately wrong copy of one trusted definition (or of one
# convention of a proved reference algorithm) swapped into the checker; each must make the checks
# fail on the case lists below, and the unmutated checker must pass them.
#
#   harness/openfhe-pin/mutants.sh                     # builds with `lake build openfhe_pin`
#   OPENFHE_PIN=<exe> harness/openfhe-pin/mutants.sh
#
# Families (each prints its own table; the last line is the summary):
#   BGV checks  lean/mutation.sh   on fixtures/mutation.list      (FHE/Pin/Mutants.lean)
#   BGV algo    algo/mutation.sh   on fixtures/mutation.list      (FHE/Pin/AlgoMutants.lean)
#   BFV checks  lean/mutation_bfv.sh on fixtures/mutation-bfv.list (FHE/Pin/BFV/Mutants.lean), if present
#   BFV algo    algo/mutation_bfv.sh on fixtures/mutation-bfv.list (FHE/Pin/BFV/AlgoMutants), if present
# Documented survivors (a mutant the recorded executions cannot distinguish, with the measured
# margin) are listed in fixtures/MUTANTS_SURVIVING*.tsv and are not failures; any other survivor is.
# They are not silent: each one is printed by name as "survived (accepted, listed)" with its
# reason, and the summary of a family that has such a list reads "K caught of N; S listed
# survivors (names)" (the wording of the counts, "caught"/"killed", is the family's own, which paper/gen parses). The families without a list keep their one-line counts unchanged.
# Environment: THREADS (per run) and JOBS (runs in parallel) default from the core count, 8 and 4 on
# a machine of 32 or more cores (fewer on a smaller one); KEEP=1.
set -uo pipefail
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
TMP="$(mktemp -d "${TMPDIR:-/tmp}/openfhe-pin-mut.XXXXXX")"
[ "${KEEP:-0}" = 1 ] || trap 'rm -rf "$TMP"' EXIT
T0=$(date +%s)
if [ -n "${OPENFHE_PIN:-}" ]; then EXE="$OPENFHE_PIN"; else
  EXE="$("$HERE/lean/build_lean.sh")" || { echo "mutants.sh: building openfhe_pin failed" >&2; exit 2; }
fi
tar -xJf "$HERE/fixtures/fixtures.tar.xz" -C "$TMP" || { echo "mutants.sh: cannot unpack BGV fixtures" >&2; exit 2; }
sed "s|^|$TMP/fixtures/|" "$HERE/fixtures/mutation.list" > "$TMP/mutation.list"
fams=("lean/mutation.sh:$TMP/mutation.list" "algo/mutation.sh:$TMP/mutation.list")
if [ -f "$HERE/fixtures/fixtures-bfv.tar.xz" ] && [ -f "$HERE/fixtures/mutation-bfv.list" ]; then
  tar -xJf "$HERE/fixtures/fixtures-bfv.tar.xz" -C "$TMP" || { echo "mutants.sh: cannot unpack BFV fixtures" >&2; exit 2; }
  sed "s|^|$TMP/bfv-fixtures/|" "$HERE/fixtures/mutation-bfv.list" > "$TMP/mutation-bfv.list"
  [ -x "$HERE/lean/mutation_bfv.sh" ] && fams+=("lean/mutation_bfv.sh:$TMP/mutation-bfv.list")
  [ -x "$HERE/algo/mutation_bfv.sh" ] && fams+=("algo/mutation_bfv.sh:$TMP/mutation-bfv.list")
fi
ncpu="$(getconf _NPROCESSORS_ONLN 2>/dev/null || nproc 2>/dev/null || echo 1)"
if [ -z "${JOBS:-}" ]; then JOBS=$(( ncpu / 2 )); [ "$JOBS" -gt 4 ] && JOBS=4; [ "$JOBS" -lt 1 ] && JOBS=1; fi
if [ -z "${THREADS:-}" ]; then THREADS=$(( ncpu / JOBS )); [ "$THREADS" -gt 8 ] && THREADS=8; [ "$THREADS" -lt 1 ] && THREADS=1; fi
rc=0; sums=(); survivors=()
for f in "${fams[@]}"; do
  s="${f%%:*}"; l="${f#*:}"; n="$(echo "$s" | tr '/.' '__')"
  echo "--- $s ($(wc -l < "$l") cases) ---"
  extra=()
  [ "$s" = lean/mutation_bfv.sh ] && extra=("$HERE/fixtures/MUTANTS_SURVIVING-bfv.tsv")
  [ "$s" = algo/mutation_bfv.sh ] && [ -f "$HERE/fixtures/MUTANTS_SURVIVING-bfv-algo.tsv" ] && extra=("$HERE/fixtures/MUTANTS_SURVIVING-bfv-algo.tsv")
  MUTATION_OUT="$TMP/$n" THREADS="$THREADS" JOBS="$JOBS" "$HERE/$s" "$l" "$EXE" "${extra[@]}" > "$TMP/$n.txt" 2>&1 || rc=1
  cat "$TMP/$n.txt"
  line="$(grep -E 'mutants: [0-9]+ (caught|killed) of [0-9]+' "$TMP/$n.txt" | tail -1)"
  case "$s" in
    *_bfv.sh)   # the families that have a MUTANTS_SURVIVING list: name every survivor, count them
      label="$(echo "$line" | sed -E 's/^([a-z ]*mutants):.*/\1/')"
      k="$(echo "$line" | sed -E 's/^.*mutants: ([0-9]+) (caught|killed) of ([0-9]+).*$/\1/')"
      verb="$(echo "$line" | sed -E 's/^.*mutants: ([0-9]+) (caught|killed) of ([0-9]+).*$/\2/')"
      tot="$(echo "$line" | sed -E 's/^.*mutants: ([0-9]+) (caught|killed) of ([0-9]+).*$/\3/')"
      names=(); unlisted=0
      while IFS= read -r sv; do
        nm="${sv#SURVIVOR }"; nm="${nm%%[: ]*}"
        if [[ "$sv" == *"NOT "* ]]; then unlisted=$((unlisted + 1)); echo "  SURVIVED (NOT LISTED, a failure): $nm"
        else
          names+=("$nm"); why="${sv#SURVIVOR $nm: }"; why="${why#no new difference in * (listed: }"; why="${why%)}"
          echo "  survived (accepted, listed): $nm: $(echo "$why" | cut -c1-110)"
        fi
      done < <(grep '^SURVIVOR ' "$TMP/$n.txt")
      [ ${#names[@]} -eq 0 ] || survivors+=("${names[@]}")
      line="$label: $k $verb of $tot; ${#names[@]} listed survivors$([ ${#names[@]} -gt 0 ] && echo " ($(IFS=,; echo "${names[*]}" | sed 's/,/, /g'))")$([ $unlisted -gt 0 ] && echo "; $unlisted UNLISTED survivors")"
      echo "  => $line" ;;
  esac
  sums+=("$line")
done
st=PASS; [ $rc = 0 ] || st=FAIL
joined="$(printf '%s; ' "${sums[@]}")"
[ ${#survivors[@]} -eq 0 ] || echo "(${#survivors[@]} mutants survived and are accepted because they are listed in fixtures/MUTANTS_SURVIVING*.tsv: ${survivors[*]})"
echo "openfhe-pin mutants: $st: ${joined}$(( $(date +%s) - T0 )) s"
exit $rc
