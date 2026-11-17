#!/bin/sh
# run-examples.sh: fhe_check on the three examples shipped with the prebuilt executable
# (docs/QUICKSTART.md). Prints each verdict line; the full reports are in examples/*.report.txt.
cd "$(dirname "$0")" || exit 4
for f in bgv_certified bfv_certified bgv_refused; do
  ./fhe_check "examples/$f.fhecheck.json" >"examples/$f.report.txt"
  echo "$f (exit $?): $(grep -m1 '^VERDICT' "examples/$f.report.txt" | cut -c1-200)"
done
echo
echo "bgv_refused: the smallest change, and parameters that certify (fhe_check recommend):"
sed -n '/^SUGGESTIONS/,/^$/p' examples/bgv_refused.report.txt | sed -n '1,6p' | cut -c1-160
./fhe_check recommend --emit examples/bgv_fixed.fhecheck.json examples/bgv_refused.fhecheck.json >examples/bgv_recommend.txt
grep -m1 '^RECOMMENDATION' examples/bgv_recommend.txt
sed -n '/^  CCParams/,/GenCryptoContext/p' examples/bgv_recommend.txt
echo
echo "re-check of the recommended parameters (examples/bgv_fixed.fhecheck.json):"
./fhe_check examples/bgv_fixed.fhecheck.json | grep -m1 '^VERDICT'
