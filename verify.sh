#!/usr/bin/env bash
# verify.sh: check this repository from a fresh clone, with one command.
#
#   ./verify.sh                        fast path: prebuilt Mathlib from Mathlib's cache server
#   VERIFY_FROM_SOURCE=1 ./verify.sh   strict path: build the needed Mathlib modules from source
#                                      (hours on a laptop; no prebuilt .olean is downloaded;
#                                      needs node/npm for ProofWidgets; not yet tested end to end)
#
# Other switches (environment variables):
#   VERIFY_STRICT=1|0    run the gate with STRICT=1 (default: 1 when the bwrap sandbox works, else 0)
#   VERIFY_FRONTEND=0    skip the fhe_check frontend tests (harness/frontend/tests/run.sh)
#   VERIFY_SKIP_MUTANTS=1  quick check for CI on small machines: has the gate skip the mutation
#                        suites (SKIP_MUTANTS=1, which the gate counts as a failure under STRICT=1),
#                        runs it non-strict, and then re-imposes the other strict conditions itself
#                        (no unproved pin, sandboxed build, trust/LOCK committed). Not a release check.
#   SANDBOX=0            passed to the gate: build without bwrap (the result is then not strict)
#
# What it does: (1) checks prerequisites, (2) fetches Mathlib and its dependencies at the commits
# pinned in lake-manifest.json, (3) runs the gate scripts/check-spec.sh (lock, banned constructs,
# hole audit, sandboxed build, kernel replay of every locked statement, differential and mutation
# suites against committed recorded runs and goldens), (4) builds fhe_check and runs its tests, and
# (5) prints a summary. Exit status 0 iff every step passed.
#
# It needs no OpenFHE or HEIR build: the differential suites compare against recorded OpenFHE runs
# and goldens committed under harness/. Re-recording them (LIVE=1) is a separate, optional
# procedure described in harness/*/README.md.
#
# Requirements: Linux or macOS, elan (https://github.com/leanprover/elan), git, python3 >= 3.10
# (standard library only), curl (fast path), tar and xz (the recorded fixtures are .tar.xz), and
# bubblewrap (`bwrap`) for the sandboxed, strict gate (Linux only). flock (util-linux) is optional:
# without it the gate cannot stop two runs in one checkout from overlapping and says so.
# Measured: a from-scratch strict ./verify.sh took 817 s on a 128-core machine that was otherwise
# idle when the run started, with 7.2 GB peak memory in its largest process (the kernel replay);
# 8.4 GB on disk including the dependencies; a 453 MB Mathlib cache download. On a hosted CI runner
# (4 vCPU, 16 GB) a quick run (VERIFY_SKIP_MUTANTS=1) completed in 1 h 2 min. Nothing was measured
# on a laptop. The script warns below 9 GB of free disk.
set -uo pipefail
cd "$(dirname "$0")"
ROOT="$PWD"
export PATH="$HOME/.elan/bin:$PATH"
export LC_ALL=C
LOG=build/verify
mkdir -p "$LOG"
t0=$(date +%s)

say()  { printf '\n### %s\n' "$*"; }
die()  { printf '\nverify.sh: ERROR: %s\n' "$*" >&2; exit 1; }
warn() { printf 'verify.sh: WARNING: %s\n' "$*" >&2; }

# ---------------------------------------------------------------------------------------------
say "1/5 Prerequisites"
command -v git >/dev/null || die "git not found"
command -v python3 >/dev/null || die "python3 not found (3.10 or newer; standard library only)"
command -v tar >/dev/null || die "tar not found (the recorded fixtures are .tar.xz archives)"
command -v xz >/dev/null || die "xz not found (Debian/Ubuntu: apt install xz-utils; Fedora: dnf install xz): the recorded fixtures are .tar.xz archives"
command -v flock >/dev/null || warn "flock not found: the gate cannot prevent two runs in one checkout from overlapping (Debian/Ubuntu: util-linux; macOS: not available)"
python3 -I -c 'import sys, lzma, json, concurrent.futures; sys.exit(sys.version_info < (3, 10))' \
  || die "python3 >= 3.10 with the lzma module is required (found: $(python3 --version 2>&1))"
want="$(tr -d '[:space:]' < lean-toolchain)"
if ! command -v lake >/dev/null; then
  die "lake not found. Install elan (it reads lean-toolchain and fetches $want), following https://github.com/leanprover/elan,
  for example (read the script first):
    curl -sSfL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -o elan-init.sh
    sh elan-init.sh -y --default-toolchain none
  then open a new shell (or add \$HOME/.elan/bin to PATH) and rerun ./verify.sh"
fi
# With elan, the first `lean` call installs the pinned toolchain if it is missing.
# That first call prints elan's download progress, so it is made once on its own and the version is
# read from a second call.
lean --version >/dev/null 2>&1 || die "lean --version failed (toolchain $want could not be installed or run)"
have="$(lean --version 2>/dev/null | head -1)" || die "lean --version failed: $have"
case "$have" in
  *"version ${want##*:v},"*) ;;
  *) die "toolchain mismatch: lean-toolchain pins $want but lean reports: $have" ;;
esac
echo "lean: $have"
echo "python3: $(python3 --version 2>&1)   git: $(git --version | awk '{print $3}')"

sandbox_ok=0
if [ "${SANDBOX:-1}" = 1 ]; then
  if command -v bwrap >/dev/null && bwrap --ro-bind / / --dev /dev --unshare-net true 2>/dev/null; then
    sandbox_ok=1; echo "bwrap: works (the gate's build step will be sandboxed)"
  elif command -v bwrap >/dev/null; then
    warn "bwrap is installed but cannot create a sandbox here (unprivileged user namespaces disabled?
    On Ubuntu 24.04: sudo sysctl -w kernel.apparmor_restrict_unprivileged_userns=0).
    The gate will build unsandboxed and the result is NOT strict."
  else
    warn "bwrap not found (Debian/Ubuntu: apt install bubblewrap; Fedora: dnf install bubblewrap).
    The gate will build unsandboxed and the result is NOT strict."
  fi
else
  echo "SANDBOX=0: build will not be sandboxed; the result is NOT strict"
fi
STRICT_RUN="${VERIFY_STRICT:-$sandbox_ok}"
if [ "$STRICT_RUN" = 1 ] && [ $sandbox_ok = 0 ]; then
  die "VERIFY_STRICT=1 needs a working bwrap sandbox (see the warning above)"
fi
SKIP_MUT="${VERIFY_SKIP_MUTANTS:-0}"
WANT_STRICT="$STRICT_RUN"   # with SKIP_MUT, strict conditions other than mutants are checked below
[ "$SKIP_MUT" = 1 ] && STRICT_RUN=0
avail_kb=$(df -Pk . | awk 'NR==2{print $4}')
[ -n "$avail_kb" ] && [ "$avail_kb" -lt 9000000 ] && warn "only $((avail_kb/1024)) MB free here; about 9 GB is needed"

# ---------------------------------------------------------------------------------------------
if [ "${VERIFY_FROM_SOURCE:-0}" = 1 ]; then
  say "2/5 Mathlib from source (VERIFY_FROM_SOURCE=1)"
  echo "The next step compiles, unsandboxed, only the Mathlib modules this project imports (and"
  echo "their imports) from the commits pinned in lake-manifest.json; no prebuilt .olean is"
  echo "downloaded. ProofWidgets (a Mathlib dependency) builds its JavaScript with npm, which"
  echo "downloads npm packages. Expect one to several hours. (This path is not yet tested.)"
  command -v npm >/dev/null || die "VERIFY_FROM_SOURCE=1 needs node and npm (ProofWidgets builds its widget JavaScript with npm)"
  [ -d .lake/packages/mathlib/.lake/build ] && warn ".lake/packages/mathlib already has build outputs (possibly from the cache);
    for a clean from-source check use a fresh clone"
  lake env true >"$LOG/lake-env.log" 2>&1 || { cat "$LOG/lake-env.log"; die "lake could not fetch the dependencies"; }
  mathlib_mode="built from source"
else
  say "2/5 Mathlib from the cache (fast path; VERIFY_FROM_SOURCE=1 for the strict path)"
  cat <<'EOF'
`lake exe cache get` downloads Mathlib's prebuilt .olean files from Mathlib's cache server. What
you trust by doing so: that those files are what Mathlib's CI built from the commit pinned in
lake-manifest.json. The gate's kernel replay (step 5) re-checks, from an empty environment, every
Mathlib constant that a locked statement's proof uses, so the cache cannot make a false proof
pass; it could, in principle, change what a Mathlib definition used in a statement says, or an
attribute. To exclude that too, rerun with VERIFY_FROM_SOURCE=1.
EOF
  command -v curl >/dev/null || die "curl not found (needed by lake exe cache get)"
  lake exe cache get >"$LOG/cache-get.log" 2>&1 \
    || { tail -40 "$LOG/cache-get.log"; die "lake exe cache get failed (log: $LOG/cache-get.log)"; }
  tail -3 "$LOG/cache-get.log"
  mathlib_mode="prebuilt cache (lake exe cache get)"
fi
for p in mathlib plausible; do
  [ -d ".lake/packages/$p" ] || die ".lake/packages/$p is missing after the fetch"
done
# The gate's sandbox lets the build write only the project's .lake/build; dependencies are
# read-only inside it. So the dependency closure (the Mathlib modules the project imports, and
# ProofWidgets etc. below them) is brought up to date here, unsandboxed. This runs only Lake and
# dependency code, never this project's code. On the cache path it only replays cached results
# and writes Lake's trace/hash files (seconds to minutes); with VERIFY_FROM_SOURCE=1 it compiles.
mods=$(grep -rhoE '^(public )?import Mathlib[A-Za-z0-9_.]*' Spec Challenge Validation FHE ./*.lean \
         2>/dev/null | awk '{print $NF}' | sort -u)
[ -n "$mods" ] || die "found no Mathlib imports (unexpected)"
echo "preparing $(echo "$mods" | wc -l) imported Mathlib modules and their dependencies (unsandboxed; log: $LOG/deps-build.log)"
# shellcheck disable=SC2086
lake build $mods >"$LOG/deps-build.log" 2>&1 \
  || { tail -40 "$LOG/deps-build.log"; die "building the Mathlib dependencies failed (log: $LOG/deps-build.log)"; }
tail -1 "$LOG/deps-build.log"
if [ "${VERIFY_FROM_SOURCE:-0}" != 1 ] && grep -qE '\] Built Mathlib\.' "$LOG/deps-build.log"; then
  warn "some Mathlib modules were compiled locally, not taken from the cache (see $LOG/deps-build.log)"
fi

# ---------------------------------------------------------------------------------------------
say "3/5 Gate: STRICT=$STRICT_RUN SKIP_MUTANTS=$SKIP_MUT scripts/check-spec.sh (see the header for the measured time of the whole script; longer on a small machine)"
t_gate=$(date +%s)
# With VERIFY_SKIP_MUTANTS=1 the gate runs non-strict, which would let it use the development
# replay cache (build/gate-cache); a check that re-imposes the strict conditions turns it off.
REPLAY="${REPLAY_CACHE:-1}"; [ "$SKIP_MUT" = 1 ] && [ "$WANT_STRICT" = 1 ] && REPLAY=0
STRICT="$STRICT_RUN" SKIP_MUTANTS="$SKIP_MUT" REPLAY_CACHE="$REPLAY" scripts/check-spec.sh 2>&1 | tee "$LOG/gate.log"
gate_rc=${PIPESTATUS[0]}
if [ "$SKIP_MUT" = 1 ] && [ "$WANT_STRICT" = 1 ]; then
  # The strict conditions except the mutation suites, checked from the gate's own output.
  grep -q ' MISSING$' build/check-spec/pins-short.txt 2>/dev/null && { echo "verify.sh: unproved pins"; gate_rc=1; }
  grep -qE 'NOT sandboxed|build not sandboxed' "$LOG/gate.log" && { echo "verify.sh: build not sandboxed"; gate_rc=1; }
  grep -q '^ok (trust/LOCK matches HEAD)' "$LOG/gate.log" || { echo "verify.sh: trust/LOCK not committed or differs from HEAD"; gate_rc=1; }
  grep -q '^ok (trust/EVIDENCE matches HEAD)' "$LOG/gate.log" || { echo "verify.sh: trust/EVIDENCE not committed or differs from HEAD"; gate_rc=1; }
  grep -qE '^(ok|FAIL) +harness/.*difftest.sh' "$LOG/gate.log" || { echo "verify.sh: no differential suite ran"; gate_rc=1; }
  grep -qE 'UNREVIEWED in trust/SOURCE-DRIFT.tsv' "$LOG/gate.log" && { echo "verify.sh: recorded SOURCE hashes differ from the tree and the difference is unreviewed (trust/SOURCE-DRIFT.tsv)"; gate_rc=1; }
  grep -q '^KERNEL cache: off' build/check-spec/pins.txt 2>/dev/null || { echo "verify.sh: kernel replay not complete"; gate_rc=1; }
fi
gate_s=$(( $(date +%s) - t_gate ))

# ---------------------------------------------------------------------------------------------
front_rc=skipped
if [ "${VERIFY_FRONTEND:-1}" = 1 ]; then
  say "4/5 fhe_check: build and frontend tests (harness/frontend/tests/run.sh)"
  # Note: this builds the untrusted FHE library unsandboxed (it is not part of the gate's result).
  if lake build fhe_check >"$LOG/fhe_check-build.log" 2>&1; then
    FHE_CHECK="$ROOT/.lake/build/bin/fhe_check" harness/frontend/tests/run.sh >"$LOG/frontend-tests.log" 2>&1
    front_rc=$?
    tail -3 "$LOG/frontend-tests.log"
  else
    tail -20 "$LOG/fhe_check-build.log"; front_rc=1
  fi
else
  say "4/5 fhe_check tests skipped (VERIFY_FRONTEND=0)"
fi

# ---------------------------------------------------------------------------------------------
say "5/5 Summary"
C=build/check-spec
pick() { grep -hE "$1" "$2" 2>/dev/null | tail -1; }
pins=$(pick '^SUMMARY' "$C/pins-short.txt"); pins=${pins#SUMMARY }
# The gate's SUMMARY line also counts `projections_skipped`: field projections of Prop structures
# declared in Challenge/, which are not locked statements and are not counted in `total`. It is
# bookkeeping, so it is not shown here (it stays in build/check-spec/pins.txt).
pins=$(printf '%s' "$pins" | sed -E 's/ projections_skipped=[0-9]+//')
clip() { local l="$1" n="$2"; [ "${#l}" -gt "$n" ] && l="${l:0:$n}..."; printf '%s' "$l"; }
kern=$(grep -E '^KERNEL' "$C/pins.txt" 2>/dev/null | cut -c1-120 | paste -sd'|' - | sed 's/|/\n              /g')
lock=$(sed -n '/^== 1\./,/^== 2\./p' "$LOG/gate.log" | grep -E '^(ok|FAILED|WARNING|STRICT)' | cut -c1-90 | tr '\n' ' ')
echo "commit:       $(git rev-parse --short HEAD 2>/dev/null)$(git diff --quiet HEAD 2>/dev/null || echo ' (working tree modified)')"
echo "toolchain:    $want; Mathlib $mathlib_mode"
echo "mode:         strict=$([ "$STRICT_RUN" = 1 ] && echo yes || { [ "$SKIP_MUT" = 1 ] && [ "$WANT_STRICT" = 1 ] && echo "yes except mutants (VERIFY_SKIP_MUTANTS=1)" || echo no; }), sandboxed=$(grep -q 'NOT sandboxed\|build not sandboxed' "$LOG/gate.log" && echo no || echo yes)"
echo "lock:         ${lock:-see $LOG/gate.log}"
echo "pins:         ${pins:-see $C/pins.txt}"
printf 'kernel:       %b\n' "${kern:-see $C/pins.txt}"
# Only the suites THIS run's gate output reports (build/check-spec also holds logs of earlier runs).
suites_of() { sed -n "s#^\(ok\|FAIL\) \+harness/\([^/]*\)/$1\.sh.*#\2#p" "$LOG/gate.log"; }
dts=$(suites_of difftest); [ -n "$dts" ] || echo "differential: none ran"
for n in $dts; do
  f="$C/$n-difftest.log"
  line=$(grep -E 'cases agree|disagreements|failures|^passed [0-9]+, failed|^[a-z-]+: (PASS|FAIL)' "$f" 2>/dev/null | tail -1)
  printf 'differential: %-11s %s\n' "$n" "$(clip "${line:-see $f}" 110)"
done
mts=$(suites_of mutants); [ -n "$mts" ] || echo "mutants:      none ran"
for n in $mts; do
  f="$C/$n-mutants.log"
  line=$(grep -E '^[a-z-]+ mutants: ' "$f" 2>/dev/null | tail -1)
  printf 'mutants:      %-11s %s\n' "$n" "$(clip "${line:-see $f}" 230)"
done
echo "gate:         $(tail -1 "$LOG/gate.log") (exit $gate_rc, ${gate_s} s)"
echo "fhe_check:    $( [ "$front_rc" = skipped ] && echo skipped || { [ "$front_rc" = 0 ] && echo PASS || echo "FAIL (see $LOG/frontend-tests.log)"; })"
echo "total time:   $(( $(date +%s) - t0 )) s; logs in $LOG/ and $C/"
if [ "$gate_rc" = 0 ] && { [ "$front_rc" = 0 ] || [ "$front_rc" = skipped ]; }; then
  [ "$SKIP_MUT" = 1 ] && echo "NOTE: mutation suites skipped on request; this is not the release check."
  [ "$WANT_STRICT" = 1 ] || echo "NOTE: passed in NON-STRICT mode (no working bwrap sandbox); this is not the release check."
  echo "VERIFY: PASS"; exit 0
else
  echo "VERIFY: FAIL"; exit 1
fi
