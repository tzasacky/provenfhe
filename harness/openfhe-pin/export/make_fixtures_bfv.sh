#!/usr/bin/env bash
# make_fixtures_bfv.sh [RESULTS.jsonl]
# Regenerates the COMMITTED BFV fixtures of harness/openfhe-pin/fixtures/ from a live OpenFHE:
#   fixtures-bfv.tar.xz          every case of `gen_matrix_bfv.py --suite bfv-fixtures`
#                                (params.json, trace.jsonl, prog.fhecheck.json, pin.json, polys.txt each),
#                                under the directory name bfv-fixtures/
#   EXPECTED_REFUSALS-bfv.tsv    case <TAB> class <TAB> message of every case extract_bfv.py refuses. The class
#                                is the Lean checker's (its `x.refusal` result lines, field "class"), read from
#                                RESULTS.jsonl if given (or $OPENFHE_PIN_RESULTS), else `?`
#   SOURCE-bfv.txt               which OpenFHE the cases were recorded from: commit, patch / tracer / extractor
#                                hashes, compiler, the exact CXX flags of the library and its floating-point facts
#                                (export/float_facts.sh)
# Needs: upstream OpenFHE v1.6.1 + tracer (harness/frontend/openfhe/build_openfhe.sh; its install prefix in
# OPENFHE_INSTALL, default harness/build/frontend-openfhe/install; its CMake build directory in OPENFHE_BUILD,
# default <install>/../build). Work directory: $OPENFHE_PIN_BUILD/cases/bfv-fixtures (OPENFHE_PIN_BUILD
# defaults to harness/build/openfhe-pin); CASES=<dir> uses an existing generated suite instead.
# The archive is deterministic for a given OpenFHE build and extractor: seeds are derived from the case
# names; sorted names, fixed mtime/owner; no absolute path in any archived file (checked).
set -euo pipefail
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(cd "$HERE/../../.." && pwd)"
PB="${OPENFHE_PIN_BUILD:-$ROOT/harness/build/openfhe-pin}"
I="${OPENFHE_INSTALL:-$ROOT/harness/build/frontend-openfhe/install}"
FX="$ROOT/harness/openfhe-pin/fixtures"
RESULTS="${1:-${OPENFHE_PIN_RESULTS:-}}"
if [ -n "${CASES:-}" ]; then
  W="$(cd "$CASES/.." && pwd)"
  [ "$(basename "$CASES")" = bfv-fixtures ] || { echo "CASES must be a directory named bfv-fixtures" >&2; exit 1; }
else
  W="$PB/cases"
  "$HERE/build_cpp_bfv.sh" > /dev/null
  mkdir -p "$W"
  rm -rf "$W/bfv-fixtures"
  python3 "$HERE/gen_matrix_bfv.py" --suite bfv-fixtures --out "$W/bfv-fixtures" --jobs "${JOBS:-16}" --selftest
fi
M="$W/bfv-fixtures/MANIFEST.tsv"
if awk -F'\t' 'NR > 1 && ($3 != "0" || $8 != "ok") { bad = 1 } END { exit !bad }' "$M"; then
  echo "make_fixtures_bfv.sh: an export or a selftest failed (see $M)" >&2; exit 1
fi
awk -F'\t' 'NR > 1 { print "bfv-fixtures/" $1 }' "$M" | LC_ALL=C sort > "$W/bfv-fixtures.names"
# nothing that is archived may carry a local absolute path
if ( cd "$W" && while read -r c; do cat "$c/params.json" "$c/trace.jsonl" "$c/prog.fhecheck.json" "$c/pin.json"; done < "$W/bfv-fixtures.names" ) \
     | grep -n -E '/home/|/tmp/|/Users/|/root/|/build/' | head -3 | grep .; then
  echo "make_fixtures_bfv.sh: an archived file contains an absolute local path" >&2; exit 1
fi
( cd "$W" && LC_ALL=C tar --sort=name --mtime='2026-01-01 00:00:00Z' --owner=0 --group=0 --numeric-owner \
    --exclude=export.log --exclude=selftest.json --exclude=extract.err \
    -cf - -T "$W/bfv-fixtures.names" | xz -9e -T1 > "$FX/fixtures-bfv.tar.xz" )
python3 -I - "$W" "$W/bfv-fixtures.names" "$RESULTS" > "$FX/EXPECTED_REFUSALS-bfv.tsv" <<'PY'
import json, os, sys
w, names, results = sys.argv[1], sys.argv[2], sys.argv[3]
cls = {}
if results:
    for l in open(results):
        try:
            d = json.loads(l)
        except Exception:
            continue
        if d.get("check") == "x.refusal":
            cls[d["case"]] = d.get("class", "?")
rows = []
for n in open(names).read().split():
    d = json.load(open(os.path.join(w, n, "prog.fhecheck.json")))
    if "error" in d:
        c = os.path.basename(n)
        rows.append((c, cls.get(c, "?"), d["error"].replace("\t", " ").replace("\n", " ")))
print("# case<TAB>class<TAB>message : the cases of fixtures-bfv.tar.xz that harness/frontend/openfhe/extract_bfv.py REFUSES.")
print("# Written by export/make_fixtures_bfv.sh. class = the Lean checker's x.refusal class (from its results.jsonl), or ?")
print("# when the script was run without one; message = the extractor's error, as recorded in prog.fhecheck.json.")
for r in sorted(rows):
    print("\t".join(r))
PY
SRCGIT="$I/../src/.git"
COMMIT=unknown
if [ -f "$SRCGIT/HEAD" ]; then
  COMMIT="$(cat "$SRCGIT/HEAD")"
  case "$COMMIT" in "ref: "*) COMMIT="$(cat "$SRCGIT/${COMMIT#ref: }" 2>/dev/null || echo unknown)";; esac
fi
sha() { sha256sum "$1" | cut -d' ' -f1; }
{
  echo "OpenFHE: upstream openfheorg/openfhe-development v1.6.1"
  echo "commit: $COMMIT"
  echo "patch: harness/frontend/openfhe/openfhe-v1.6.1-tracer.patch (sha256 $(sha "$ROOT/harness/frontend/openfhe/openfhe-v1.6.1-tracer.patch")), observation-only ENABLE_TRACER hooks"
  echo "tracer: harness/frontend/openfhe/fhecheck-tracer.h (sha256 $(sha "$ROOT/harness/frontend/openfhe/fhecheck-tracer.h"))"
  echo "build: harness/frontend/openfhe/build_openfhe.sh (Release, ENABLE_TRACER=ON, WITH_OPENMP=OFF, WITH_REDUCED_NOISE=OFF, NATIVEINT 64)"
  OPENFHE_INSTALL="$I" "$HERE/float_facts.sh" --text
  echo "exporter: harness/openfhe-pin/cpp/pin_export_bfv.cpp + pin_adv_bfv.h + pin_dump_bfv.h + pin_dump.h + pin_prng.cpp (export/build_cpp_bfv.sh), OMP_NUM_THREADS=1"
  echo "extractor: harness/frontend/openfhe/extract_bfv.py (sha256 $(sha "$ROOT/harness/frontend/openfhe/extract_bfv.py")), which imports extract.py (sha256 $(sha "$ROOT/harness/frontend/openfhe/extract.py"))"
  echo "suite: export/gen_matrix_bfv.py --suite bfv-fixtures; archived: $(wc -l < "$W/bfv-fixtures.names") cases; refused by the extractor: $(grep -vc '^#' "$FX/EXPECTED_REFUSALS-bfv.tsv")"
} > "$FX/SOURCE-bfv.txt"
ls -l "$FX/fixtures-bfv.tar.xz"
cat "$FX/SOURCE-bfv.txt"
