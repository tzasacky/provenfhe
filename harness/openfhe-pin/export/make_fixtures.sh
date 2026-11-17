#!/usr/bin/env bash
# Regenerates the COMMITTED fixtures of harness/openfhe-pin/fixtures/ from a live OpenFHE:
#   fixtures.tar.xz          every N = 16 and N = 64 case of `gen_matrix.py --suite fixtures`
#                            (params.json, trace.jsonl, prog.fhecheck.json, pin.json, polys.txt)
#   EXPECTED_REFUSALS.tsv    case <TAB> refusal class (the checker's x.refusal line) <TAB> message
#   SOURCE.txt               which OpenFHE the cases were recorded from
# Needs: upstream OpenFHE v1.6.1 + tracer (harness/frontend/openfhe/build_openfhe.sh; its install
# prefix in OPENFHE_INSTALL, default harness/build/frontend-openfhe/install) and openfhe_pin
# (`lake build openfhe_pin`, or OPENFHE_PIN=<exe>). Work directory: $OPENFHE_PIN_BUILD/cases/fixtures
# (OPENFHE_PIN_BUILD defaults to harness/build/openfhe-pin).
# The archive is deterministic for a given OpenFHE build and extractor: sorted names, fixed
# mtime/owner. fixtures/mutation.list and fixtures/EXPECTED_FAIL.tsv are maintained by hand.
set -euo pipefail
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(cd "$HERE/../../.." && pwd)"
PB="${OPENFHE_PIN_BUILD:-$ROOT/harness/build/openfhe-pin}"
I="${OPENFHE_INSTALL:-$ROOT/harness/build/frontend-openfhe/install}"
EXE="${OPENFHE_PIN:-$ROOT/.lake/build/bin/openfhe_pin}"
FX="$ROOT/harness/openfhe-pin/fixtures"
W="$PB/cases"
"$HERE/build_cpp.sh" > /dev/null
mkdir -p "$W"
python3 "$HERE/gen_matrix.py" --suite fixtures --out "$W/fixtures" --jobs "${JOBS:-32}" --selftest
if awk -F'\t' 'NR > 1 && ($3 != "0" || $8 != "ok") { bad = 1 } END { exit !bad }' "$W/fixtures/MANIFEST.tsv"; then
  echo "make_fixtures.sh: an export or a selftest failed (see $W/fixtures/MANIFEST.tsv)" >&2; exit 1
fi
# the archived cases, by name from the manifest (stale directories of earlier runs are ignored)
awk -F'\t' 'NR > 1 && $1 ~ /^n(16|64)_/ { print "fixtures/" $1 }' "$W/fixtures/MANIFEST.tsv" | LC_ALL=C sort > "$W/fixtures.names"
( cd "$W" && LC_ALL=C tar --sort=name --mtime='2026-01-01 00:00:00Z' --owner=0 --group=0 --numeric-owner \
    --exclude=export.log --exclude=selftest.json --exclude=extract.err \
    -cf - -T "$W/fixtures.names" | xz -9e -T1 > "$FX/fixtures.tar.xz" )
# the refusal classes, from the checker's own x.refusal lines
sed "s|^|$W/|" "$W/fixtures.names" > "$W/fixtures.list"
"$EXE" --threads "${JOBS:-32}" --only x --out "$W/fixtures.load.jsonl" --list "$W/fixtures.list" > /dev/null || true
python3 -I - "$W/fixtures.load.jsonl" > "$FX/EXPECTED_REFUSALS.tsv" <<'PY'
import json, sys
rows = []
for l in open(sys.argv[1]):
    d = json.loads(l)
    if d["check"] == "x.refusal":
        rows.append((d["case"], d.get("class", "?"), d.get("message", "").replace("\t", " ")))
print("# case<TAB>class<TAB>message : the cases of fixtures.tar.xz that harness/frontend/openfhe/extract.py REFUSES.")
print("# Written by export/make_fixtures.sh. run.sh / difftest.sh fail unless the checker's x.refusal line of")
print("# exactly these cases passes with this class (FHE/Pin/ChecksA.lean, refusalClasses), and export/refusals.py")
print("# re-runs the extractor on the recorded trace of each and requires the recorded message.")
for r in sorted(rows):
    print("\t".join(r))
PY
{
  echo "OpenFHE: upstream openfheorg/openfhe-development v1.6.1"
  echo "commit: $(git -C "$I/../src" rev-parse HEAD 2>/dev/null || echo unknown)"
  echo "patch: harness/frontend/openfhe/openfhe-v1.6.1-tracer.patch (sha256 $(sha256sum "$ROOT/harness/frontend/openfhe/openfhe-v1.6.1-tracer.patch" | cut -d' ' -f1)), observation-only ENABLE_TRACER hooks"
  echo "tracer: harness/frontend/openfhe/fhecheck-tracer.h (sha256 $(sha256sum "$ROOT/harness/frontend/openfhe/fhecheck-tracer.h" | cut -d' ' -f1))"
  echo "build: harness/frontend/openfhe/build_openfhe.sh (Release, ENABLE_TRACER=ON, WITH_OPENMP=OFF, WITH_REDUCED_NOISE=OFF, NATIVEINT 64), $(c++ --version | head -1)"
  echo "exporter: harness/openfhe-pin/cpp/pin_export.cpp + pin_dump.h + pin_prng.cpp (export/build_cpp.sh), OMP_NUM_THREADS=1"
  echo "extractor: harness/frontend/openfhe/extract.py (sha256 $(sha256sum "$ROOT/harness/frontend/openfhe/extract.py" | cut -d' ' -f1))"
  echo "suite: export/gen_matrix.py --suite fixtures; archived: $(wc -l < "$W/fixtures.names") cases (N = 16 and N = 64) of $(($(wc -l < "$W/fixtures/MANIFEST.tsv") - 1))"
} > "$FX/SOURCE.txt"
ls -l "$FX/fixtures.tar.xz"
cat "$FX/SOURCE.txt"
