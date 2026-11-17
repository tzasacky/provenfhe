#!/usr/bin/env bash
# trust/LOCK: SHA-256 manifest of the locked files (trusted definitions, locked statements, the gate,
# the build configuration). Regenerate ONLY when a trusted change is intended, and only as the
# project maintainer, then commit trust/LOCK together with the change:
#
#   scripts/lock.sh                      write trust/LOCK from the working tree
#   scripts/lock.sh --print              print the manifest of the working tree to stdout (used by the gate)
#   scripts/lock.sh --evidence           write trust/EVIDENCE (the second manifest, below)
#   scripts/lock.sh --evidence --print   print that manifest to stdout (used by the gate)
#
# trust/EVIDENCE: the same kind of manifest (sha256, same step-1 semantics in the gate) over the
# files the conformance evidence rests on, which trust/LOCK does not cover: the recorded fixtures
# and their lists and expected/surviving-mutant tables (harness/openfhe-pin/fixtures,
# harness/bfv-float/fixtures), the suite drivers and verdict scripts, the frontend tests (runner,
# examples, goldens), the tracer patch and header and the extractors that the fixtures' SOURCE*.txt
# record, and trust/SOURCE-DRIFT.tsv. The file set is found by globbing, and a file that is not
# in the tree is simply absent from the manifest (a deleted evidence file shows up as a
# difference to the committed trust/EVIDENCE). Anything that regenerates trust/LOCK in another
# tree (the public release) regenerates trust/EVIDENCE the same way, after its last edit to the tree.
#
# What this does and does not protect. The gate (scripts/check-spec.sh, step 1) fails if the working
# tree differs from trust/LOCK, and warns (fails under STRICT=1) if trust/LOCK differs from the
# version committed in git HEAD. A contributor can still edit a locked file and rerun this script; what
# stops that from counting is that only the maintainer commits, and the maintainer reviews any diff to
# trust/LOCK. The lock makes drift visible; it is not access control.
set -euo pipefail
cd "$(dirname "$0")/.."
export LC_ALL=C
mode=lock; print=0
for a in "$@"; do
  case "$a" in
    --print) print=1 ;;
    --evidence) mode=evidence ;;
    *) echo "usage: scripts/lock.sh [--evidence] [--print]" >&2; exit 2 ;;
  esac
done

manifest() {
  echo "# trust/LOCK: sha256 of locked files. Regenerate with scripts/lock.sh (maintainer only)."
  {
    find Spec Challenge scripts -type f ! -name '*.pyc' ! -path '*/__pycache__/*' -print
    for f in lakefile.toml lean-toolchain lake-manifest.json Spec.lean Challenge.lean; do
      echo "$f"
    done
  } | sort -u | while IFS= read -r f; do
    if [ -f "$f" ]; then sha256sum -- "$f"; else echo "MISSING  $f"; fi
  done
}

evidence_files() {
  local d
  for d in harness/openfhe-pin/fixtures harness/bfv-float/fixtures \
    harness/lattigo-pin/fixtures harness/lattigo-pin/fixtures-defects; do
    [ -d "$d" ] && find "$d" -type f ! -name '*.md' ! -name '*.pyc' ! -path '*/__pycache__/*' -print
  done
  for d in harness/frontend/tests harness/frontend/examples; do
    [ -d "$d" ] && find "$d" -type f ! -name '*.pyc' ! -path '*/__pycache__/*' -print
  done
  for f in \
    harness/openfhe-pin/difftest.sh harness/openfhe-pin/mutants.sh harness/openfhe-pin/run.sh \
    harness/openfhe-pin/counts.sh harness/openfhe-pin/lean/build_lean.sh \
    harness/openfhe-pin/lean/mutation.sh harness/openfhe-pin/lean/mutation_bfv.sh \
    harness/openfhe-pin/lean/mutation_bfv.py harness/openfhe-pin/lean/verdict.py \
    harness/openfhe-pin/lean/verdict_bfv.py harness/openfhe-pin/lean/coverage.py \
    harness/openfhe-pin/algo/mutation.sh harness/openfhe-pin/algo/mutation_bfv.sh \
    harness/openfhe-pin/export/refusals.py \
    harness/bfv-float/difftest.sh harness/bfv-float/mutants.sh harness/bfv-float/run.sh \
    harness/bfv-float/check.py harness/bfv-float/dump.cpp \
    harness/frontend/difftest.sh harness/frontend/heir/extract_bgv.py \
    harness/frontend/openfhe/openfhe-v1.6.1-tracer.patch harness/frontend/openfhe/fhecheck-tracer.h \
    harness/frontend/openfhe/extract.py harness/frontend/openfhe/extract_bfv.py \
    harness/frontend/openfhe/tracer_version.py harness/frontend/openfhe/legacy-traces.tsv \
    harness/frontend/openfhe/value_check.py harness/frontend/openfhe/value_check_bfv.py \
    harness/openfhe-pin/realsize/README.md harness/openfhe-pin/realsize/suite.py \
    harness/openfhe-pin/realsize/run.sh harness/openfhe-pin/realsize/summarize.py \
    harness/openfhe-pin/realsize/CASES.tsv harness/openfhe-pin/realsize/MANIFEST.sha256.tsv \
    harness/openfhe-pin/realsize/summary.json harness/openfhe-pin/realsize/table.md \
    harness/openfhe-pin/realsize/library.json harness/openfhe-pin/realsize/library.md harness/ref/difftest.sh \
    harness/openfhe-pin/realsize/sample/summary.json \
    harness/lattigo-pin/run.sh harness/lattigo-pin/lean/LattigoPin.lean harness/lattigo-pin/lean/summarize.py \
    trust/SOURCE-DRIFT.tsv; do
    [ -f "$f" ] && echo "$f"
  done
}

evidence_manifest() {
  echo "# trust/EVIDENCE: sha256 of the conformance evidence (fixtures, drivers, goldens, tracer). Regenerate with scripts/lock.sh --evidence (maintainer only)."
  evidence_files | sort -u | while IFS= read -r f; do sha256sum -- "$f"; done
}

if [ "$mode" = evidence ]; then
  if [ $print = 1 ]; then evidence_manifest; exit 0; fi
  mkdir -p trust
  evidence_manifest >trust/EVIDENCE.tmp
  mv trust/EVIDENCE.tmp trust/EVIDENCE
  echo "wrote trust/EVIDENCE ($(grep -vc '^#' trust/EVIDENCE) files). Commit it with the change it locks."
else
  if [ $print = 1 ]; then manifest; exit 0; fi
  mkdir -p trust
  manifest >trust/LOCK.tmp
  mv trust/LOCK.tmp trust/LOCK
  echo "wrote trust/LOCK ($(grep -vc '^#' trust/LOCK) files). Commit it with the change it locks."
fi
