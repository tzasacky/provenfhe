#!/usr/bin/env bash
# Mutation test of harness/bfv-float/difftest.sh (gate step 7): each mutant perturbs one step of the
# Python transcription of Challenge/BFVMul/Float.lean in a scratch copy of check.py; difftest.sh on
# the committed dumps must FAIL for every mutant. (The Lean definitions themselves are mutated by
# harness/openfhe-pin/mutants.sh, algo family.) Exit 0 iff the baseline passes and every mutant is
# caught. (Replacing a product+sum by one fused step is NOT a mutant: check.py accepts a build with
# contraction, reported as such. Replacing 1.0/float(q) by the correctly rounded 1/q is invisible on
# these dumps, i.e. the dumps do not distinguish the two.)
set -uo pipefail
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
W="$(mktemp -d "${TMPDIR:-/tmp}/bfv-float-mut.XXXXXX")"
trap 'rm -rf "$W"' EXIT
# name|python replacement (old -> new, exactly once in check.py)
MUTANTS=(
  "sw-no-half|    s = 0.5\n    for q, yi in zip(qs, y):|    s = 0.0\n    for q, yi in zip(qs, y):"
  "sr-no-half|    s = 0.5\n    for m, n, xi in zip(ms, ns, x):|    s = 0.0\n    for m, n, xi in zip(ms, ns, x):"
  "qinv-coarse|    return 1.0 / float(q)|    return (1.0 / float(q)) * (1 + 2.0 ** -44)"
  "frac-swap|    return float(n) / float(m)|    return float(Fr(n, m)) * (1 + 2.0 ** -40)"
  "sw-round|    v = int(nu_sw(qs, y, fused))        # truncation|    v = round(nu_sw(qs, y, fused) - 0.5)  # truncation"
  "sr-exact|int(nu_sr(qs, frac_nums(t, qs, ps), xq, fused))) % p|int(float(exact_sr(qs, frac_nums(t, qs, ps), xq)))) % p"
  "sr-om-floor-off|    om = t * P * inv_mod(Q * P // p, p) // p % p|    om = (t * P * inv_mod(Q * P // p, p) // p + 1) % p"
)
run() { "$1/difftest.sh" > "$2" 2>&1; }
# The baseline and the mutants are independent (each in its own copy, each difftest.sh unpacks the
# dumps into its own temporary directory): they run BFV_FLOAT_JOBS at a time (default from the core
# count and the load, 4 to 8 on 8 or more cores; 1 = one after the other), and are reported in the fixed order.
if [ -n "${BFV_FLOAT_JOBS:-}" ]; then JOBS=$BFV_FLOAT_JOBS
else JOBS=$(awk -v c="$(getconf _NPROCESSORS_ONLN 2>/dev/null || echo 1)" -v l="$(cut -d' ' -f1 /proc/loadavg 2>/dev/null || echo 0)" \
  'BEGIN { f = (c - l) / 8; if (f > 8) f = 8; m = int(c / 2); if (m > 4) m = 4; if (m < 1) m = 1; if (f < m) f = m; print int(f) }'); fi
case "$JOBS" in ''|*[!0-9]*|0) echo "BFV_FLOAT_JOBS must be a positive integer"; exit 2;; esac
mutant() {  # NAME OLD NEW: writes one result line to $W/NAME.res
  local name=$1 old=$2 new=$3 d="$W/m-$1"
  cp -r "$HERE" "$d"
  if ! python3 -I - "$d/check.py" "$old" "$new" <<'PY'
import sys
p, old, new = sys.argv[1], sys.argv[2].replace("\\n", "\n"), sys.argv[3].replace("\\n", "\n")
s = open(p).read()
if s.count(old) != 1:
    sys.exit(f"mutation point not found exactly once: {old!r}")
open(p, "w").write(s.replace(old, new))
PY
  then echo "MUTANT $name: cannot apply" >"$W/$name.res"; return; fi
  # caught = difftest.sh ran its checks (its summary line counts the dumps) and failed; a crash or
  # an unpacking error before the checks is not evidence that the mutant is detected
  if run "$d" "$W/$name.log"; then echo "SURVIVED $name" >"$W/$name.res"
  elif grep -qE '^bfv-float: FAIL: [1-9][0-9]* dumps' "$W/$name.log"; then echo "caught   $name" >"$W/$name.res"
  else echo "MUTANT $name: difftest.sh did not run to its verdict (see the log)" >"$W/$name.res"; fi
}
cp -r "$HERE" "$W/base"
( run "$W/base" "$W/base.log"; echo $? >"$W/base.rc" ) &
names=()
for m in "${MUTANTS[@]}"; do
  IFS='|' read -r name old new <<<"$m"
  names+=("$name")
  while [ "$(jobs -rp | wc -l)" -ge "$JOBS" ]; do wait -n; done
  mutant "$name" "$old" "$new" &
done
wait
[ "$(cat "$W/base.rc" 2>/dev/null)" = 0 ] || { echo "bfv-float mutants: baseline FAILS"; tail -3 "$W/base.log"; exit 1; }
caught=0; total=0; rc=0
for name in "${names[@]}"; do
  total=$((total + 1))
  r="$(cat "$W/$name.res" 2>/dev/null)" || r="MUTANT $name: did not finish"
  [ -n "$r" ] || r="MUTANT $name: did not finish"
  echo "$r"
  case "$r" in "caught   $name") caught=$((caught + 1));; *) rc=1;; esac
done
echo "bfv-float mutants: $caught caught of $total; 0 listed survivors (every survivor is a failure)"
[ "$caught" = "$total" ] && [ $rc = 0 ]
