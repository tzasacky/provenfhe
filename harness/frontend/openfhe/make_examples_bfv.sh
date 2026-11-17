#!/usr/bin/env bash
# Regenerates the OpenFHE BFV examples (harness/frontend/examples/openfhe_bfv_*), the small-ring
# value-check fixtures (harness/frontend/tests/values-bfv/*) and the refusal fixtures
# (harness/frontend/tests/refused-bfv/*: programs extract_bfv.py must refuse) with bfv_demo on
# traced upstream OpenFHE v1.6.1 (build_openfhe.sh builds it; BFV_DEMO overrides the path).
# Runs single-threaded (OMP_NUM_THREADS=1): the tracer refuses calls from parallel regions.
#   make_examples_bfv.sh [OUTROOT]   default: write into the repository
# Every run is followed by the level/parts cross-check (extract_bfv.py) and the plaintext-value
# cross-check (value_check_bfv.py); any mismatch stops the script. Examples marked DECFAIL are
# runs whose output does not match the cleartext prediction (bfv_demo exits 3, value_check_bfv.py
# exits 3): they are kept as examples a checker must not certify.
set -euo pipefail
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
FRONT="$(cd "$HERE/.." && pwd)"
ROOT="$(cd "$FRONT/../.." && pwd)"
B="${BFV_DEMO:-$ROOT/harness/build/frontend-openfhe/bfv_demo}"
EX="${1:-$FRONT}/examples"
VA="${1:-$FRONT}/tests/values-bfv"
RF="${1:-$FRONT}/tests/refused-bfv"
export OMP_NUM_THREADS=1
TMP="$(mktemp -d)"
trap 'rm -rf "$TMP"' EXIT
mkdir -p "$EX" "$VA" "$RF"

# name | bfv_demo arguments | OK or DECFAIL
EXAMPLES=()
# every multiplication technique x {HYBRID, BV}, chain at depth 1 and 2, OpenFHE's own parameters
# (HEStd_128_classic, t = 65537, 60-bit primes)
for m in HPS HPSPOVERQ HPSPOVERQLEVELED BEHZ; do
  for k in HYBRID BV; do
    for d in 1 2; do
      EXAMPLES+=("openfhe_bfv_$(echo ${m}_${k} | tr A-Z a-z)_chain_d$d|--mult $m --ks $k --prog chain --depth $d|OK")
    done
  done
done
EXAMPLES+=(
  # OpenFHE's defaults (no technique setter called: HPSPOVERQLEVELED, BV, STANDARD)
  "openfhe_bfv_default_chain_d3|--prog chain --depth 3|OK"
  "openfhe_bfv_default_dot_d2|--prog dot --depth 2|OK"
  "openfhe_bfv_default_rot_d1|--prog rot --depth 1|OK"
  "openfhe_bfv_default_plain_d2|--prog plain --depth 2|OK"
  "openfhe_bfv_default_rotsum_d2|--prog rotsum --depth 2|OK"
  "openfhe_bfv_default_norelin_d2|--prog norelin --depth 2|OK"
  "openfhe_bfv_default_neg_d1|--prog neg --depth 1|OK"
  # CoefPacked plaintexts (encrypted, and operands of EvalMult/EvalAdd/EvalSub), negative and extreme coefficients
  "openfhe_bfv_default_coefpk_d2|--prog coefpk --depth 2|OK"
  "openfhe_bfv_behz_hybrid_coefpk_d2|--mult BEHZ --ks HYBRID --prog coefpk --depth 2|OK"
  # other techniques on programs with rotations, plaintext operations, Compress (EXTENDED encryption:
  # refusal fixtures below)
  "openfhe_bfv_hps_hybrid_plain_d2|--mult HPS --ks HYBRID --prog plain --depth 2|OK"
  "openfhe_bfv_behz_hybrid_rotsum_d2|--mult BEHZ --ks HYBRID --prog rotsum --depth 2|OK"
  "openfhe_bfv_hpspoverq_hybrid_compress_d2|--mult HPSPOVERQ --ks HYBRID --prog compress --depth 2|OK"
  "openfhe_bfv_hpspoverqleveled_hybrid_compress_d3|--mult HPSPOVERQLEVELED --ks HYBRID --prog compress --depth 3|OK"
  "openfhe_bfv_hpspoverqleveled_hybrid_chain_d4|--mult HPSPOVERQLEVELED --ks HYBRID --prog chain --depth 4|OK"
  # NOT secure (ring dimension 1024, HEStd_NotSet): OpenFHE's default technique with BV at depth 2
  # is not certified; the same parameters with HYBRID are
  "openfhe_bfv_n1024_default_chain_d2|--n 1024 --prog chain --depth 2|DECFAIL"
  "openfhe_bfv_n1024_hybrid_chain_d2|--n 1024 --ks HYBRID --prog chain --depth 2|OK"
)

run_one() {  # name args status outdir mode (0: example, 1: value fixture, 2: refusal fixture)
  local name=$1 args=$2 status=$3 out=$4 keep=$5 d="$TMP/$1" rc=0 want=0
  [ "$status" = DECFAIL ] && want=3
  mkdir -p "$d"
  # shellcheck disable=SC2086
  "$B" run "$d" $args > /dev/null || rc=$?
  [ "$keep" = 2 ] && [ "$status" = ANY ] && want=$rc
  [ "$rc" = "$want" ] || { echo "bfv_demo exit $rc (expected $want): $name"; exit 1; }
  if [ "$keep" = 2 ]; then
    if python3 -I "$HERE/extract_bfv.py" --params "$d/params.json" --trace "$d/trace.jsonl" > "$d/prog.json"; then
      echo "expected a refusal: $name"; exit 1; fi
    mkdir -p "$out/$name"
    cp "$d/params.json" "$d/trace.jsonl" "$out/$name/"
    python3 -I -c "import json,sys; print(json.load(open(sys.argv[1]))['error'])" "$d/prog.json" > "$out/$name/refusal.txt"
    echo "$name: refused: $(cat "$out/$name/refusal.txt")"
    return
  fi
  python3 -I "$HERE/extract_bfv.py" --params "$d/params.json" --trace "$d/trace.jsonl" --artifact "$name" > "$d/prog.json" || {
    cat "$d/prog.json"; echo "extraction failed: $name"; exit 1; }
  rc=0
  python3 -I "$HERE/value_check_bfv.py" "$d/prog.json" "$d/values.json" > "$d/value_check.txt" || rc=$?
  [ "$rc" = "$want" ] || { cat "$d/value_check.txt"; echo "value check exit $rc (expected $want): $name"; exit 1; }
  if [ "$keep" = 1 ]; then
    mkdir -p "$out/$name"
    cp "$d/params.json" "$d/trace.jsonl" "$d/values.json" "$out/$name/"
  else
    cp "$d/params.json" "$out/$name.params.json"
    cp "$d/trace.jsonl" "$out/$name.trace.jsonl"
    cp "$d/prog.json" "$out/$name.fhecheck.json"
  fi
  echo "$name: $(tail -1 "$d/value_check.txt")"
}

for e in "${EXAMPLES[@]}"; do
  IFS='|' read -r name args status <<<"$e"
  run_one "$name" "$args" "$status" "$EX" 0
done
# Tiny ring (N = 16, HEStd_NotSet: NOT secure; only the value cross-check uses them), so that the
# raw decryptions can be committed: every program under every multiplication technique and both
# key-switching techniques, EXTENDED encryption, and a leveled run with internal drops.
for m in HPS HPSPOVERQ HPSPOVERQLEVELED BEHZ; do
  l=$(echo $m | tr A-Z a-z)
  for p in chain dot rot plain rotsum norelin neg coefpk; do
    run_one "n16_${l}_hybrid_${p}" "--n 16 --mult $m --ks HYBRID --prog $p --depth 2" OK "$VA" 1
  done
  for p in chain rotsum plain; do
    [ $m = HPSPOVERQLEVELED ] && continue  # with BV at depth 2 the library's decryption fails (above)
    run_one "n16_${l}_bv_${p}" "--n 16 --mult $m --ks BV --prog $p --depth 2" OK "$VA" 1
  done
done
run_one "n16_hpspoverqleveled_bv_rotsum_d1" "--n 16 --prog rotsum --depth 1" OK "$VA" 1
run_one "n16_hpspoverq_hybrid_compress" "--n 16 --mult HPSPOVERQ --ks HYBRID --prog compress --depth 2" OK "$VA" 1
run_one "n16_hpspoverqleveled_hybrid_compress_d3" "--n 16 --ks HYBRID --prog compress --depth 3" OK "$VA" 1
run_one "n16_behz_bv_coefpk" "--n 16 --mult BEHZ --ks BV --prog coefpk --depth 2" OK "$VA" 1
run_one "n16_hpspoverqleveled_hybrid_chain_d4_q30" "--n 16 --ks HYBRID --prog chain --depth 4 --qbits 30" OK "$VA" 1
# Refusal fixtures (N = 16): EvalInnerProduct (= EvalMult + EvalSum; OpenFHE >= 1.6 fuses the
# rotation sum), Encrypt with the private key, EvalMult with a key on a
# 3-part operand, EvalMultNoRelinNoCheck (no BFV scaling); the last two are not decrypted
# correctly or not decrypted at all by bfv_demo, hence status ANY
run_one "innerprod_hpspoverqleveled" "--n 16 --prog innerprod --depth 2" OK "$RF" 2
run_one "innerprod_behz" "--n 16 --mult BEHZ --ks HYBRID --prog innerprod --depth 2" OK "$RF" 2
run_one "symenc_hps" "--n 16 --mult HPS --ks HYBRID --prog symenc --depth 2" OK "$RF" 2
run_one "threepart_hps" "--n 16 --mult HPS --ks HYBRID --prog threepart --depth 3" ANY "$RF" 2
run_one "nocheck_hps" "--n 16 --mult HPS --ks HYBRID --prog nocheck --depth 2" ANY "$RF" 2
run_one "mixadd_hps" "--n 16 --mult HPS --ks HYBRID --prog mixadd --depth 2" ANY "$RF" 2
run_one "mixadd_default" "--n 16 --prog mixadd --depth 2" ANY "$RF" 2
# t - 1 > floor(q0/2): the packed encoder stores x - q0 in the limbs after the first;
# bfv_demo stops at its own encoding check, after the trace is written
run_one "packed_window_rot" "--t 1179649 --qbits 21 --depth 2 --n 8192 --prog rot" ANY "$RF" 2
# EXTENDED encryption: the trusted model Spec.EncryptBFV is STANDARD only, so extract_bfv.py refuses it
run_one "extended_hps_dot" "--n 16 --mult HPS --ks HYBRID --enc EXTENDED --prog dot --depth 2" OK "$RF" 2
run_one "extended_behz_plain" "--n 16 --mult BEHZ --ks BV --enc EXTENDED --prog plain --depth 2" OK "$RF" 2
run_one "extended_coefpk_hps" "--n 16 --mult HPS --ks HYBRID --enc EXTENDED --prog coefpk --depth 2" OK "$RF" 2
run_one "extended_hps_hybrid_dot_d2" "--mult HPS --ks HYBRID --enc EXTENDED --prog dot --depth 2" OK "$RF" 2
