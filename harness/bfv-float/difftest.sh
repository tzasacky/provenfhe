#!/usr/bin/env bash
# The gate entry of harness/bfv-float (UNTRUSTED evidence for Challenge/BFVMul/Float.lean), from the
# COMMITTED dumps only (no OpenFHE needed):
#   1. check.py real on fixtures/dumps.tar.xz: the library's double tables (m_qInv, m_rInv, the
#      *Frac tables) bit for bit, and the outputs of the real DCRTPoly::SwitchCRTBasis and
#      ScaleAndRound (QR->R, QR->Q, Q->Q_l) coefficient by coefficient, against the transcription
#      Fl.qInv / Fl.frac / Fl.switch1 / Fl.scale1 (Python model of the Lean definitions), and every
#      measured error against the proved bounds doubleSw / doubleSr;
#   2. check.py synth --trials 200 (fixed seed): the bounds on synthetic parameter sets.
# The Lean definitions themselves are compared with the library's whole EvalMult outputs by the
# algo.* family of harness/openfhe-pin (BFV fixtures). The dumps were written by dump.cpp against
# upstream OpenFHE v1.6.1 (commit b59e1f29) built by harness/frontend/openfhe/build_openfhe.sh;
# fixtures/SOURCE.txt says how; fixtures/make_dumps.sh regenerates them.
# Prints one summary line; exit 0 iff both pass.
set -uo pipefail
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
TMP="$(mktemp -d "${TMPDIR:-/tmp}/bfv-float.XXXXXX")"
trap 'rm -rf "$TMP"' EXIT
T0=$(date +%s)
tar -xJf "$HERE/fixtures/dumps.tar.xz" -C "$TMP" || { echo "bfv-float: FAIL (cannot unpack dumps)"; exit 1; }
rc=0
python3 -I "$HERE/check.py" real "$TMP"/dump_*.json > "$TMP/real.txt" 2>&1 || rc=1
python3 -I "$HERE/check.py" synth --trials 200 > "$TMP/synth.txt" 2>&1 || rc=1
nd=$(ls "$TMP"/dump_*.json | wc -l)
tabs=$(grep -c "table .*identical" "$TMP/real.txt")
outs=$(grep -c "model (no contraction) == library on all" "$TMP/real.txt")
if [ $rc -ne 0 ]; then
  echo "--- check.py real ---"; grep -v " k=" "$TMP/real.txt" | tail -40
  echo "--- check.py synth ---"; tail -5 "$TMP/synth.txt"
fi
st=PASS; [ $rc = 0 ] || st=FAIL
echo "bfv-float: $st: $nd dumps, $tabs tables bit-identical, $outs function outputs equal to the uncontracted transcription on every coefficient, every measured error within doubleSw/doubleSr (real + synthetic); $(( $(date +%s) - T0 )) s"
exit $rc
