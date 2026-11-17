#!/usr/bin/env bash
# Definition of "the Spec works". Prints a report and exits 0 only if every check passes.
# Run from anywhere: scripts/check-spec.sh            (development: reports gaps, fails on errors)
#                    STRICT=1 scripts/check-spec.sh   (release: also fails on unproved pins, missing
#                                                      differential/mutation suites, an uncommitted
#                                                      trust/LOCK, or an unsandboxed build)
# SANDBOX=0 builds without the bwrap sandbox (step 4; e.g. after a lakefile change, which needs
# Lake to write .lake/config). SKIP_MUTANTS=1 skips step 7 (quick CI); under STRICT=1 a skipped
# step 7 is a failure, so a strict PASS always includes the mutation suites.
# On a fresh clone, bring the dependencies up to date unsandboxed first (`./verify.sh` does this:
# it fetches the packages pinned in lake-manifest.json and Mathlib's build): the sandbox mounts
# .lake/packages read-only, so the gate cannot fetch or build them itself. The whole script is one function, so bash has parsed all of it
# before any step runs: editing this file during a run (e.g. from code executed by the build)
# cannot change what the run does.
#
# This is the full gate. The steps are listed below; STRICT=1 is the setting that makes a pass
# mean the whole claim (nothing skipped, nothing cached, no warning accepted).
#
# Concurrency and cost. Step 5 always runs alone after the build (the suites run untrusted code
# unsandboxed, which must not overlap the audit of the build). The suites of steps 6 and 7 then
# run as GATE_JOBS parallel jobs (default: from the core count and the current load, 1 on small
# machines; GATE_JOBS=1 is the old sequential order); results are printed in the fixed order. Only one gate runs at a time per checkout (flock on build/gate.lock; a second one
# waits, or fails with GATE_NOWAIT=1); a separate checkout has its own lock.
# Step 5's kernel replay runs REPLAY_JOBS kernel checks at a time (default: a quarter of the idle
# cores, 2 to 16; REPLAY_JOBS=1 is the serial replay; scripts/PinStatus.lean, "Parallel kernel
# replay", says why the verdicts are the same), in strict and development runs alike.
# Kernel replay cache (step 5): without STRICT=1, a root whose replay an earlier run accepted, and
# whose import closure's .olean files are byte-identical since (SHA-256), is not replayed again
# (scripts/PinStatus.lean, "Replay cache", says why that is sound; REPLAY_CACHE=0 turns it off).
# Under STRICT=1 every root is replayed from an empty environment, as before the cache existed; the
# strict run only records its results there. Records are shared between the checkouts of a
# machine through GATE_SHARED_CACHE (default ~/.cache/lean-fhe-gate; empty = per checkout only):
# each run publishes the record its PinStatus wrote, and a development run starts from the record,
# local or shared, that matches its .olean files best (scripts/olean_sha.py); the stat-keyed
# SHA-256 memo of the .olean files is shared there too. The strict run reads neither.
# Development knobs, all refused under STRICT=1: GATE_OUT (output directory),
# LOCK_WARN_ONLY=1 (step 1(a) warns instead of failing), DIFFTESTS="openfhe-pin frontend" (only these
# suites in step 6), SKIP_LEAN=1 (skip steps 4 and 5: no Lean or build input changed).
# FAIL_FAST=1 stops after the first failing step (sequential order).
main() {
set -uo pipefail
cd "$(dirname "$0")/.."
export PATH="$HOME/.elan/bin:$PATH"
export LC_ALL=C
OUT="${GATE_OUT:-build/check-spec}"
mkdir -p "$OUT"
fail=0
step() { printf '\n== %s\n' "$1"; }
strict() { [ "${STRICT:-0}" = 1 ]; }
t_start=$(date +%s)
stopped() {  # FAIL_FAST=1 and something failed: print the result now
  if [ $fail -ne 0 ] && [ "${FAIL_FAST:-0}" = 1 ]; then
    printf '\n== Result\n(%s s)\nFAIL (FAIL_FAST=1: stopped at the first failing step; the later steps did not run)\n' \
      "$(( $(date +%s) - t_start ))"
    return 0
  fi
  return 1
}
if strict; then
  for v in GATE_OUT LOCK_WARN_ONLY DIFFTESTS SKIP_LEAN; do
    if [ -n "${!v+x}" ]; then
      echo "check-spec.sh: $v is a development knob and is refused under STRICT=1"; return 2
    fi
  done
fi
# One gate at a time in this checkout.
mkdir -p build
if command -v flock >/dev/null; then
  # fd 9 already open on the lock file: inherited from a calling script that already holds the lock
  # (a flock is per open file, so taking it again on the inherited descriptor succeeds at once).
  if ! { [ -e "/proc/$$/fd/9" ] && [ "/proc/$$/fd/9" -ef build/gate.lock ]; }; then exec 9>>build/gate.lock; fi
  if ! flock -n 9; then
    echo "check-spec.sh: another gate is running in this checkout ($(cat build/gate.lock.owner 2>/dev/null || echo 'owner unknown'))."
    if [ "${GATE_NOWAIT:-0}" = 1 ]; then echo "GATE_NOWAIT=1: not waiting"; return 3; fi
    echo "Waiting for it to finish (GATE_NOWAIT=1 fails instead; a separate checkout has its own lock) ..."
    flock 9
  fi
  echo "pid $$, started $(date '+%F %T'), STRICT=${STRICT:-0}, output $OUT" >build/gate.lock.owner
else
  echo "note: flock not found; concurrent gates in this checkout are not prevented"
fi
# Parallel jobs for the suites of steps 6-7.
ncpu=$(getconf _NPROCESSORS_ONLN 2>/dev/null || echo 1)
load1=$(cut -d' ' -f1 /proc/loadavg 2>/dev/null || echo 0)
if [ -n "${GATE_JOBS:-}" ]; then
  jobs_n=$GATE_JOBS; jobs_why="GATE_JOBS"
else
  jobs_n=$(awk -v c="$ncpu" -v l="$load1" 'BEGIN { f = (c - l) / 16; if (f > 4) f = 4; m = (c >= 16) ? 2 : 1; if (f < m) f = m; print int(f) }')
  jobs_why="default for $ncpu cores at load $load1; set GATE_JOBS to override"
fi
echo "parallel jobs for steps 6-7: $jobs_n ($jobs_why)"
# Kernel checks at a time in step 5 (scripts/PinStatus.lean, "Parallel kernel replay"; 1 = the
# serial replay). Default: a quarter of the idle cores, between 2 and 16 (1 below 4 cores).
if [ -n "${REPLAY_JOBS:-}" ]; then
  replay_jobs=$REPLAY_JOBS
else
  replay_jobs=$(awk -v c="$ncpu" -v l="$load1" 'BEGIN { if (c < 4) { print 1; exit } f = (c - l) / 4; if (f > 16) f = 16; if (f < 2) f = 2; print int(f) }')
fi
case "$replay_jobs" in ''|*[!0-9]*|0) echo "check-spec.sh: REPLAY_JOBS must be a positive integer"; return 2 ;; esac

step "1. Lock: locked files match trust/LOCK, conformance evidence matches trust/EVIDENCE, and both match git HEAD"
# Locked: Spec/, Challenge/, scripts/, lakefile.toml, lean-toolchain, lake-manifest.json, Spec.lean,
# Challenge.lean (scripts/lock.sh). Evidence (trust/EVIDENCE, scripts/lock.sh --evidence): the
# recorded fixtures and their lists and tables, the suite drivers and verdict scripts, the frontend
# tests, the tracer patch and header and the extractors. The real protection is that only the
# project maintainer commits; this step makes any drift visible. (a) is always an error. (b) is a
# warning in development and an error under STRICT=1: a contributor could regenerate a manifest,
# but not commit it.
check_manifest() {  # LABEL FILE NOW-SUFFIX HOW-TO-REGENERATE PRINT-COMMAND...
  local label=$1 file=$2 suffix=$3 regen=$4; shift 4
  "$@" >"$OUT/$suffix-now.txt"
  if [ ! -f "$file" ]; then
    echo "FAILED: $file is missing (the maintainer creates it with $regen)"; fail=1
  elif ! diff -u "$file" "$OUT/$suffix-now.txt" >"$OUT/$suffix-diff.txt"; then
    if [ "${LOCK_WARN_ONLY:-0}" = 1 ]; then
      echo "WARNING (LOCK_WARN_ONLY=1, not a failure here; the full gate fails until the maintainer regenerates $file): the working tree differs from $file in these $label files:"
    else
      echo "FAILED: the working tree differs from $file in these $label files:"
      fail=1
    fi
    grep -E '^[-+][0-9a-fM]' "$OUT/$suffix-diff.txt" | awk '{print $NF}' | sort -u | sed 's/^/  /'
  else
    echo "ok (working tree matches $file: $(grep -vc '^#' "$file") files)"
  fi
  if ! git show "HEAD:$file" >"$OUT/$suffix-head.txt" 2>/dev/null; then
    echo "WARNING: $file is not committed in HEAD; $label files are unprotected until the maintainer commits it"
    strict && { echo "STRICT: uncommitted $file"; fail=1; }
  elif ! cmp -s "$OUT/$suffix-head.txt" "$file"; then
    echo "WARNING: $file differs from git HEAD. $label files changed since the last commit by the maintainer:"
    diff "$OUT/$suffix-head.txt" "$file" | grep -E '^[<>] [0-9a-fM]' | awk '{print $NF}' | sort -u | sed 's/^/  /'
    strict && { echo "STRICT: $file differs from HEAD"; fail=1; }
  else
    echo "ok ($file matches HEAD)"
  fi
}
check_manifest locked trust/LOCK lock "scripts/lock.sh" scripts/lock.sh --print
check_manifest evidence trust/EVIDENCE evidence "scripts/lock.sh --evidence" scripts/lock.sh --evidence --print
# The hashes that the fixtures' SOURCE*.txt record (tracer patch and header, extractors, dumper)
# against the files in the tree; a difference must be listed in trust/SOURCE-DRIFT.tsv
# (scripts/source_hashes.py says how).
strict_arg=(); strict && strict_arg=(--strict)
if python3 -I -B scripts/source_hashes.py "${strict_arg[@]}" >"$OUT/source-hashes.txt" 2>&1; then
  cat "$OUT/source-hashes.txt"
elif [ "${LOCK_WARN_ONLY:-0}" = 1 ]; then
  echo "WARNING (LOCK_WARN_ONLY=1, not a failure here):"; sed 's/^FAILED/not ok/' "$OUT/source-hashes.txt"
else
  cat "$OUT/source-hashes.txt"; fail=1
fi
stopped && return 1

step "2. Banned constructs in trusted and locked code (Spec/, Challenge/)"
# Comments are not exempt: banned words in docstrings are cheap to rephrase and keep the grep simple.
# `opaque` hides a body from proofs while tests run it; no new syntax in trusted or locked code.
# Spec/: no `sorry` at all; `noncomputable` only on the two Mathlib anchors in Spec/Ring.lean.
# Challenge/ (locked statements AND locked executable definitions: the reference analyzers, the
# textbook operations, the kernel corpus) is scanned with the same list. Exactly two allowances:
#   (a) `sorry` as the whole body of a locked theorem: a line ending in `:= sorry`, or a line that
#       is only `sorry` (the body on its own line after a `:=`). Any other occurrence of the word
#       fails. Step 5 checks the semantic side on the build: no locked definition and no locked
#       *statement* depends on sorryAx (PinStatus, `LOCKED sorry` line).
#   (b) `noncomputable` only as `noncomputable def` in Challenge/FreshNoise*.lean (probability
#       statements: measures and real-valued tail bounds have no compiled code). Nowhere else.
# `mod` is anything that may precede a declaration keyword on its line: a doc comment on one line,
# attributes (`@[...]`), and modifiers (`private axiom`, `local notation`, `scoped[NS] infixl`,
# `@[simp] opaque`, `protected unsafe ...`). A declaration keyword after `... in` (`open Foo in notation`)
# is caught too.
mod='^\s*(/--.*-/\s*)?(@\[[^]]*\]\s*)*((private|protected|noncomputable|local|scoped(\[[^]]*\])?|nonrec|unsafe|partial|public|meta)\s+)*'
kw='axiom|opaque|macro|syntax|notation|elab|macro_rules|elab_rules|infix|infixl|infixr|prefix|postfix'
banned="\\badmit\\b|implemented_by|@\\[extern|\\bunsafe\\b|native_decide|bv_decide|decide \\+native|set_option debug|skipKernelTC|addDecl|\\brun_cmd\\b|\\brun_elab\\b|\\brun_meta\\b|\\binitialize\\b|\\bpartial def\\b|${mod}(${kw})\\b|\\bin\\s+(${kw})\\b"
step2=0
if grep -rnE "\\bsorry\\b|$banned" Spec/ --include='*.lean' >"$OUT/banned.txt"; then
  echo "FAILED (Spec/):"; cat "$OUT/banned.txt"; step2=1
fi
if grep -rn 'noncomputable' Spec/ --include='*.lean' \
     | grep -vE '^Spec/Ring.lean:[0-9]+:noncomputable def (toPolynomial|toQuot) ' >"$OUT/noncomputable.txt"; then
  echo "FAILED: noncomputable outside the anchors:"; cat "$OUT/noncomputable.txt"; step2=1
fi
if grep -rnE "$banned" Challenge/ Challenge.lean --include='*.lean' >"$OUT/banned-challenge.txt"; then
  echo "FAILED (Challenge/):"; cat "$OUT/banned-challenge.txt"; step2=1
fi
if grep -rnE '\bsorry\b' Challenge/ Challenge.lean --include='*.lean' \
     | grep -vE '^[^:]+:[0-9]+:(.*:= sorry|\s*sorry)\s*$' >"$OUT/sorry-challenge.txt"; then
  echo "FAILED: sorry in Challenge/ other than as the body of a locked theorem:"
  cat "$OUT/sorry-challenge.txt"; step2=1
fi
if grep -rn 'noncomputable' Challenge/ Challenge.lean --include='*.lean' \
     | grep -vE '^Challenge/FreshNoise[A-Za-z0-9]*\.lean:[0-9]+:noncomputable def ' >"$OUT/noncomputable-challenge.txt"; then
  echo "FAILED: noncomputable in Challenge/ outside the probability statements:"
  cat "$OUT/noncomputable-challenge.txt"; step2=1
fi
if [ $step2 = 0 ]; then echo "ok"; else fail=1; fi
stopped && return 1

step "3. Definition holes, textual audit (FHE/Holes.lean and its FHE-tree imports)"
# Defence in depth; the structural checks are in step 5, on the build. scripts/holes_audit.py strips comments and
# strings, parses imports (public/private/meta/all, «names», trailing comments), follows the FHE
# tree, and fails on banned constructs (raw text, comments not exempt), syntax extensions,
# instances, compile-time commands, and imports outside Lean/Mathlib, locked Spec/Challenge modules
# and FHE. HOLES_FILE overrides the root (used to test this step).
if python3 -I -B scripts/holes_audit.py "${HOLES_FILE:-FHE/Holes.lean}" "$OUT"; then :; else fail=1; fi
stopped && return 1

step "4. Build Spec, Challenge (every file, by name), Validation and the whole FHE library (sandboxed, two phases)"
# Code run by the build (elaborators, `run_cmd`, `initialize`, tactics) runs inside bwrap: the file
# system is read-only except .lake/build, there is no network, and nothing survives the build. It
# cannot edit this script, trust/, the sources or git. Mathlib's .lake is read-only too (it is never
# rebuilt here). Phase 1 builds Spec and Challenge (with FHE.Holes and its closure) and, by name,
# every .lean file under Spec/ and Challenge/: a file that Spec.lean does not import (step 5 fails
# on one unless it is on PinStatus's experimental allowlist, empty today) is a trusted-tree file
# too and must not stop compiling unnoticed. Phase 2 builds
# Validation with the phase-1 outputs mounted read-only, so proof code cannot rewrite the .olean
# files of the locked statements or of the holes. Step 5 checks that the holes' import closure in
# the .olean headers is exactly the file list step 3 audited (and phase 2 protected).
# Phase 2 also builds the whole untrusted FHE library: the root `FHE` and every .lean file under
# FHE/ by name (so a file that FHE.lean does not import is built too). Step 5 loads all of them.
fhe_targets=$(find FHE -name '*.lean' | sort | sed 's/\.lean$//; s#/#.#g; s/^/+/')
# ... and the independent re-specification with its equivalence proofs (library `Respec`, every
# file under Respec/ by name); step 5 puts Respec/Equiv under the FHE axiom scan and replay.
respec_targets=$(find Respec -name '*.lean' | sort | sed 's/\.lean$//; s#/#.#g; s/^/+/')
locked_targets=$(find Spec Challenge -name '*.lean' | sort | sed 's/\.lean$//; s#/#.#g; s/^/+/')
sandboxed=0
if [ "${SANDBOX:-1}" = 1 ] && command -v bwrap >/dev/null && bwrap --ro-bind / / --dev /dev true 2>/dev/null; then
  sandboxed=1
fi
sb() {  # run "$@" in the sandbox, with extra bwrap args from the array `ro`
  if [ $sandboxed = 1 ]; then
    bwrap --ro-bind / / --dev /dev --proc /proc --bind "$PWD/.lake/build" "$PWD/.lake/build" "${ro[@]}" \
      --unshare-net --unshare-pid --die-with-parent --new-session --chdir "$PWD" "$@"
  else
    "$@"
  fi
}
if [ "${SKIP_LEAN:-0}" = 1 ]; then
  echo "skipped (SKIP_LEAN=1: no Lean source or build input changed; development only)"
else
if [ $sandboxed = 1 ] && [ ! -d .lake/config ]; then
  echo "note: .lake/config is missing (a fresh checkout?). Lake writes it on its first run, which the"
  echo "      sandbox forbids: run \`lake env true\` once, unsandboxed, then rerun the gate."
fi
mkdir -p .lake/build
ro=()
# shellcheck disable=SC2086
if sb lake build Spec Challenge $locked_targets >"$OUT/build.log" 2>&1; then
  lib=.lake/build/lib/lean; ir=.lake/build/ir
  for p in Spec Challenge $(sed -n 's/\.lean$//p' "$OUT/holes-files.txt"); do   # every module under Spec/: "$lib/Spec" is the directory
    for f in "$lib/$p" "$lib/$p".* "$ir/$p" "$ir/$p".*; do
      [ -e "$f" ] && ro+=(--ro-bind "$PWD/$f" "$PWD/$f")
    done
  done
  # shellcheck disable=SC2086
  if sb lake build Validation FHE $fhe_targets $respec_targets >>"$OUT/build.log" 2>&1; then
    echo "ok ($([ $sandboxed = 1 ] && echo "sandboxed; phase 2 with $(( ${#ro[@]} / 3 )) locked build outputs read-only" || echo "NOT sandboxed"))"
  else
    echo "FAILED in phase 2, Validation/FHE (see $OUT/build.log)"; grep -E "error" "$OUT/build.log" | head -20; fail=1
  fi
else
  echo "FAILED in phase 1, Spec/Challenge (see $OUT/build.log)"; grep -E "error" "$OUT/build.log" | head -20; fail=1
fi
if grep -q "Read-only file system\|read-only file system" "$OUT/build.log"; then
  echo "note: something in the build tried to write outside .lake/build (grep -n 'read-only' $OUT/build.log);"
  echo "      a lakefile change needs one unsandboxed run (SANDBOX=0)"
fi
# (Challenge/ pins are sorry by design.)
if grep -E "declaration uses .sorry." "$OUT/build.log" | grep -v ' Challenge/' | sort -u >"$OUT/build-sorry.txt" && [ -s "$OUT/build-sorry.txt" ]; then
  echo "note: the build reports declarations outside Challenge/ that use sorry (step 5 decides whether that fails):"
  sed 's/^/  /' "$OUT/build-sorry.txt" | head -10
fi
if [ $sandboxed = 0 ]; then
  echo "WARNING: build not sandboxed (bwrap unavailable or SANDBOX=0)"; strict && fail=1
fi
fi
stopped && return 1

# Step 5 runs alone right after the build (see below). The suites of steps 6 and 7 are
# independent of each other: with GATE_JOBS > 1 they run in parallel (mutants first) and are
# reported below in the usual order; with GATE_JOBS=1 everything runs in order, one at a time.
rm -f "$OUT"/.job-*
run_job() {  # NAME LOG CMD...: run CMD with output to LOG; record exit status and seconds
  local name=$1 log=$2 s; shift 2; s=$(date +%s)
  "$@" >"$log" 2>&1
  echo "$? $(( $(date +%s) - s ))" >"$OUT/.job-$name"
}
start_job() {
  if [ "$jobs_n" -gt 1 ]; then
    while [ "$(jobs -rp | wc -l)" -ge "$jobs_n" ]; do wait -n; done
    run_job "$@" &
  else
    run_job "$@"
  fi
}
job_rc() { cut -d' ' -f1 "$OUT/.job-$1" 2>/dev/null || echo 99; }
job_s() { cut -d' ' -f2 "$OUT/.job-$1" 2>/dev/null || echo '?'; }
# Step 5's program and its replay cache (non-strict: read and write; strict: write only).
cache="${GATE_CACHE:-build/gate-cache}"
pin_args=("$OUT"); use_cache=0
if [ "${SKIP_LEAN:-0}" != 1 ] && [ "${REPLAY_CACHE:-1}" = 1 ]; then
  if strict; then sha_mode=--fresh; else sha_mode=--memo; fi
  if lake env python3 -I -B scripts/olean_sha.py "$sha_mode" "$cache" scripts/PinStatus.lean >"$OUT/olean-sha.log" 2>&1; then
    if strict; then pin_args+=(--replay-cache-write "$cache"); else pin_args+=(--replay-cache "$cache"); fi
    use_cache=1
  else
    echo "note: scripts/olean_sha.py failed (see $OUT/olean-sha.log); step 5 runs without the replay cache"
  fi
fi
pin_args+=(--replay-jobs "$replay_jobs")
pin_job() {
  lake env lean --run scripts/PinStatus.lean "${pin_args[@]}" >"$OUT/pins.txt" 2>"$OUT/pins.err"
  local rc=$?
  # Offer what this run accepted to the other checkouts on this machine (scripts/olean_sha.py --publish); only a
  # record PinStatus wrote in this run, after its replay, is published.
  if [ "$use_cache" = 1 ] && [ -f "$cache/replay-accepted.txt" ] && [ "$cache/replay-accepted.txt" -nt "$OUT/olean-sha.log" ]; then
    python3 -I -B scripts/olean_sha.py --publish "$cache" >>"$OUT/olean-sha.log" 2>&1
  fi
  return $rc
}
# Step 6 and 7 suites. DIFFTESTS (development only) selects suites by directory name.
selected() { [ -z "${DIFFTESTS+x}" ] || [[ " $DIFFTESTS " == *" $1 "* ]]; }
difftests=(); unselected=(); found6=0
for t in harness/*/difftest.sh; do
  [ -x "$t" ] || continue
  found6=1
  selected "$(basename "$(dirname "$t")")" || unselected+=("$t")
done
if [ -n "${DIFFTESTS+x}" ]; then   # in the order given (cheapest first)
  for n in $DIFFTESTS; do [ -x "harness/$n/difftest.sh" ] && difftests+=("harness/$n/difftest.sh"); done
else
  for t in harness/*/difftest.sh; do [ -x "$t" ] && difftests+=("$t"); done
fi
mutants=(); found7=0
if [ "${SKIP_MUTANTS:-0}" != 1 ]; then
  for t in harness/*/mutants.sh; do [ -x "$t" ] && { mutants+=("$t"); found7=1; }; done
fi
prebuild_exes() {
  # Parallel suites must not each run `lake build` on this checkout: build their executables once
  # here (unsandboxed, exactly as the suites' own difftest.sh would) and hand them over.
  [ ${#difftests[@]} -gt 0 ] || return 0
  local x s exe var
  for x in frontend:fhe_check:FHE_CHECK openfhe-pin:openfhe_pin:OPENFHE_PIN; do
    IFS=: read -r s exe var <<<"$x"
    [[ " ${difftests[*]} " == *" harness/$s/difftest.sh "* ]] || continue
    grep -q "name = \"$exe\"" lakefile.toml || continue
    [ -n "${!var:-}" ] && continue
    if lake build "$exe" >>"$OUT/exe-build.log" 2>&1; then export "$var=$PWD/.lake/build/bin/$exe"; fi
  done
}
name_of() { basename "$(dirname "$1")"; }

report5() {
step "5. Pins, headlines, holes, file coverage, FHE axiom scan; kernel replay (scripts/PinStatus.lean)"
# PinStatus loads the build as data (it imports only Lean, so nothing in Validation/FHE can change
# how it runs), checks statement identity, axioms, the headline statements and the holes (tables in PinStatus.lean)
# structurally, and re-checks the closure of every proved pin and of every hole with the Lean kernel
# in a fresh environment (catches declarations added with debug.skipKernelTC / without checking).
# It also checks that every .lean file under Challenge/ and Spec/ is in the import closure of
# Challenge.lean / Spec.lean (or on the printed allowlist of experimental unpinned Spec modules),
# and puts the whole FHE library under the same axiom audit and kernel replay as the pins.
# Generated field projections of Prop structures in Challenge are listed, not counted as pins.
# Without STRICT=1 it is given the replay cache (see the top of this file); under STRICT=1 it
# replays every root and the gate requires its "KERNEL cache: off" line.
if [ "${SKIP_LEAN:-0}" = 1 ]; then echo "skipped (SKIP_LEAN=1)"; return; fi
pin_rc=$(job_rc pins)
grep -E "^(PIN|SUMMARY)" "$OUT/pins.txt" | sort | uniq >"$OUT/pins-short.txt"
grep -c ' PROVEN$' "$OUT/pins-short.txt" | xargs printf 'proven: %s\n'
grep -c ' MISSING$' "$OUT/pins-short.txt" | xargs printf 'missing: %s\n'
grep -E "^(KERNEL|MODULES holes|MODULES files|FHE axioms|LOCKED|PROJECTION)" "$OUT/pins.txt" | cut -c1-600
for need in "MODULES files:" "FHE axioms:" "KERNEL FHE replayed" "KERNEL cache:" "LOCKED sorry:" "CLASSES total="; do
  grep -q "^$need" "$OUT/pins.txt" || { echo "FAILED: no \"$need\" line from PinStatus"; fail=1; }
done
if strict && ! grep -q "^KERNEL cache: off" "$OUT/pins.txt"; then
  echo "STRICT: kernel replay was not complete (no \"KERNEL cache: off\" line)"; fail=1
fi
if [ "$pin_rc" -ne 0 ] || grep -qE "^PIN .* (MISMATCH|AXIOMS|KERNEL-REJECTED|BAD-STATEMENT)|BAD|FAILED" "$OUT/pins.txt"; then
  echo "FAILED:"
  grep -E "MISMATCH|AXIOMS|KERNEL-REJECTED|BAD|FAILED" "$OUT/pins.txt" | cut -c1-400 | head -20
  [ -s "$OUT/pins.err" ] && grep -v '^\[PinStatus\]' "$OUT/pins.err" | head -20
  fail=1
fi
# The textual audit (step 3) must have covered exactly the FHE modules the .olean headers import.
if [ -f "$OUT/holes-modules.txt" ]; then
  if ! diff <(sort -u "$OUT/holes-modules.txt") <(sort -u "$OUT/holes-modules-text.txt") >"$OUT/holes-modules.diff"; then
    echo "FAILED: step 3 audited a different set of FHE modules than the holes import (< .olean, > text):"
    cat "$OUT/holes-modules.diff"; fail=1
  fi
fi
grep SUMMARY "$OUT/pins-short.txt"
# Honest counting: what kind of statement each locked statement is (scripts/PinStatus.lean,
# "Classification"). The per-pin lines are in $OUT/pins.txt (`CLASS <pin> <class> (<why>)`).
grep -E "^CLASS " "$OUT/pins.txt" | sort >"$OUT/pin-classes.txt"
echo "Locked statements by kind (one class each; per-pin list in $OUT/pin-classes.txt):"
grep -E "^CLASSES " "$OUT/pins.txt" | tr ' ' '\n' | sed -n 's/^\([a-z]*\)=\([0-9]*\)$/\1 \2/p' | while read -r k v; do
  case "$k" in
    total)          printf '  %4s  locked statements in all\n' "$v" ;;
    substantive)    printf '  %4s  substantive theorems (universally quantified; none of the kinds below)\n' "$v" ;;
    realizability)  printf '  %4s  realizability witnesses (a step or run meeting the contracts exists)\n' "$v" ;;
    discrimination) printf '  %4s  discrimination pins (something wrong is rejected or is proved wrong)\n' "$v" ;;
    closed)         printf '  %4s  closed computations (no quantified variable or hypothesis; decided by evaluation)\n' "$v" ;;
    unfolding)      printf '  %4s  true by unfolding definitions\n' "$v" ;;
    instance)       printf '  %4s  instances or immediate corollaries of other pins\n' "$v" ;;
  esac
done
echo "($(job_s pins) s; kernel replay with $replay_jobs parallel checks)"
if strict && grep -q ' MISSING$' "$OUT/pins-short.txt"; then echo "STRICT: unproved pins"; fail=1; fi
}

report6() {
step "6. Differential tests (fhe_check + frontend fixtures: frontend; recorded OpenFHE runs: openfhe-pin; OpenFHE's BFV floating-point steps: bfv-float)"
local t
for t in "${difftests[@]}"; do
  if [ ! -f "$OUT/.job-difftest-$(name_of "$t")" ]; then echo "not run: $t (FAIL_FAST=1: an earlier suite failed)"; continue; fi
  if [ "$(job_rc "difftest-$(name_of "$t")")" = 0 ]; then echo "ok   $t ($(job_s "difftest-$(name_of "$t")") s)"
  else echo "FAIL $t ($(job_s "difftest-$(name_of "$t")") s; see $OUT/$(name_of "$t")-difftest.log)"; fail=1; fi
done
for t in "${unselected[@]}"; do echo "not run: $t (DIFFTESTS=\"$DIFFTESTS\"; development only)"; done
[ $found6 -eq 1 ] || { echo "none registered yet"; strict && fail=1; }
}

report7() {
step "7. Mutation tests (each injected Spec bug must be caught by step 6 or a pin)"
if [ "${SKIP_MUTANTS:-0}" = 1 ]; then
  rm -f "$OUT"/*-mutants.log
  echo "skipped (SKIP_MUTANTS=1)"
  strict && { echo "STRICT: mutation tests skipped"; fail=1; }
  return
fi
local t
for t in "${mutants[@]}"; do
  if [ "$(job_rc "mutants-$(name_of "$t")")" = 0 ]; then echo "ok   $t ($(job_s "mutants-$(name_of "$t")") s)"
  else echo "FAIL $t ($(job_s "mutants-$(name_of "$t")") s; see $OUT/$(name_of "$t")-mutants.log)"; fail=1; fi
  # Mutants that survive and are accepted because a fixtures/MUTANTS_SURVIVING*.tsv lists them are
  # named here, with the suite's own counts ("caught K of N; S listed survivors").
  grep -E '^  (survived \(accepted, listed\)|SURVIVED \(NOT LISTED)' "$OUT/$(name_of "$t")-mutants.log" 2>/dev/null | cut -c1-150
  grep -E '^[a-z-]+ mutants: ' "$OUT/$(name_of "$t")-mutants.log" 2>/dev/null | tail -1 | sed 's/^/     /' | cut -c1-600
done
[ $found7 -eq 1 ] || { echo "none registered yet"; strict && fail=1; }
}

rm -f "$OUT/holes-modules.txt"
if [ "$jobs_n" -gt 1 ]; then
  # Step 5 runs ALONE, before anything else: the suites of steps 6 and 7 (and the executable
  # builds they need) run untrusted code unsandboxed, which could rewrite .lake/build while
  # PinStatus reads it. As in the sequential order, nothing runs between the sandboxed build and
  # the audit. Only steps 6 and 7 run in parallel with each other.
  [ "${SKIP_LEAN:-0}" = 1 ] || run_job pins /dev/null pin_job
  prebuild_exes
  echo
  echo "(steps 6-7: running $(( ${#mutants[@]} + ${#difftests[@]} )) suites, at most $jobs_n at a time, after step 5)"
  # Longest first (measured 2026-11-14), then the rest in the usual order; every suite exactly once.
  queue=()
  for k in difftest:frontend difftest:openfhe-pin mutants:bfv-float mutants:openfhe-pin; do
    for t in "${mutants[@]}" "${difftests[@]}"; do
      [ "$(basename "$t" .sh):$(name_of "$t")" = "$k" ] && queue+=("$t")
    done
  done
  for t in "${mutants[@]}" "${difftests[@]}"; do
    [[ " ${queue[*]} " == *" $t "* ]] || queue+=("$t")
  done
  for t in "${queue[@]}"; do
    start_job "$(basename "$t" .sh)-$(name_of "$t")" "$OUT/$(name_of "$t")-$(basename "$t" .sh).log" "$t"
  done
  wait
  report5; report6; report7
else
  [ "${SKIP_LEAN:-0}" = 1 ] || start_job pins /dev/null pin_job
  report5; stopped && return 1
  for t in "${difftests[@]}"; do
    start_job "difftest-$(name_of "$t")" "$OUT/$(name_of "$t")-difftest.log" "$t"
    [ "${FAIL_FAST:-0}" = 1 ] && [ "$(job_rc "difftest-$(name_of "$t")")" != 0 ] && break
  done
  report6; stopped && return 1
  for t in "${mutants[@]}"; do start_job "mutants-$(name_of "$t")" "$OUT/$(name_of "$t")-mutants.log" "$t"; done
  report7
fi
stopped && return 1

step "8. Lock re-check (nothing changed a locked or evidence file during this run)"
scripts/lock.sh --print >"$OUT/lock-end.txt"
scripts/lock.sh --evidence --print >"$OUT/evidence-end.txt"
if cmp -s "$OUT/lock-now.txt" "$OUT/lock-end.txt" && cmp -s "$OUT/evidence-now.txt" "$OUT/evidence-end.txt"; then
  echo "ok"
else
  echo "FAILED: locked or evidence files changed while the gate ran:"
  { diff "$OUT/lock-now.txt" "$OUT/lock-end.txt"; diff "$OUT/evidence-now.txt" "$OUT/evidence-end.txt"; } \
    | grep -E '^[<>] [0-9a-fM]' | awk '{print $NF}' | sort -u | sed 's/^/  /'
  fail=1
fi

step "Result"
echo "($(( $(date +%s) - t_start )) s)"
# A development run that skipped part of the gate says so on the result line itself.
notrun=()
[ "${SKIP_LEAN:-0}" = 1 ] && notrun+=("steps 4-5 (SKIP_LEAN=1)")
[ ${#unselected[@]} -gt 0 ] && notrun+=("step 6 suites: $(for t in "${unselected[@]}"; do printf '%s ' "$(name_of "$t")"; done | sed 's/ $//')")
[ "${SKIP_MUTANTS:-0}" = 1 ] && notrun+=("step 7 (SKIP_MUTANTS=1)")
partial=""
if [ ${#notrun[@]} -gt 0 ]; then partial=" (partial, not run: $(IFS=';'; echo "${notrun[*]}" | sed 's/;/; /g'))"; fi
if [ $fail -eq 0 ]; then echo "PASS$partial"; else echo "FAIL$partial"; fi
return $fail
}
main "$@"
exit $?
