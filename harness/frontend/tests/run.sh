#!/usr/bin/env bash
# Tests for fhe_check and its frontends. Run from anywhere:
#   harness/frontend/tests/run.sh            # check
#   harness/frontend/tests/run.sh --update   # rewrite the golden outputs (review the diff!)
#   harness/frontend/tests/run.sh --update-bfv   # rewrite only tests/expected-bfv.tsv and the goldens of BFV files
#   harness/frontend/tests/run.sh --live     # also re-run OpenFHE (needs bgv_demo, openfhe/build.sh)
# FHE_CHECK overrides the executable (default: .lake/build/bin/fhe_check from `lake build fhe_check`).
set -uo pipefail
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
FRONT="$(cd "$HERE/.." && pwd)"
ROOT="$(cd "$FRONT/../.." && pwd)"
FHE_CHECK="${FHE_CHECK:-$ROOT/.lake/build/bin/fhe_check}"
# A relative FHE_CHECK is relative to the caller's directory: make it absolute before the cd below.
case "$FHE_CHECK" in /*) ;; *) FHE_CHECK="$PWD/$FHE_CHECK";; esac
UPDATE=0; LIVE=0
for a in "$@"; do case "$a" in --update) UPDATE=1;; --live) LIVE=1;; --print-fhe-check) echo "$FHE_CHECK"; exit 0;; esac; done
[ -x "$FHE_CHECK" ] || { echo "no executable at $FHE_CHECK (lake build fhe_check, or set FHE_CHECK)"; exit 2; }
cd "$FRONT"
fail=0; pass=0
ok() { pass=$((pass+1)); }
bad() { echo "FAIL: $*"; fail=$((fail+1)); }
mkdir -p tests/golden
# --- BFV (begin): files with params.scheme = "BFV" are tested in section 9; the BGV-only checks skip them
is_bfv() { case "$(basename "$1")" in bfv_*|openfhe_bfv_*) return 0;; *) return 1;; esac; }
BGV_FILES=(); for f in examples/*.fhecheck.json tests/negative/*.json; do is_bfv "$f" || BGV_FILES+=("$f"); done
# --update-bfv rewrites only tests/expected-bfv.tsv and the goldens of BFV files (--update implies it)
UPDATE_BFV=$UPDATE; for a in "$@"; do [ "$a" = --update-bfv ] && UPDATE_BFV=1; done
# --- BFV (end)

# The sections below are independent functions (none reads a variable another one sets; each
# writes only temporary files, except with --update/--update-bfv/--live). They run
# FRONTEND_JOBS at a time (default: from the core count and the load, at most 8 and at least 4 on 8 or more cores, since the gate's own suites raise the load; 1 with
# --update, --update-bfv or --live: the old sequential order in this shell), each in a subshell
# with its own counters and its output buffered; outputs are printed and counts summed in the
# fixed order, so the log reads as a sequential run. A section that does not finish (killed,
# `exit`, missing count file) counts as a failure.
if [ -n "${FRONTEND_JOBS:-}" ]; then
  JOBS=$FRONTEND_JOBS
else
  JOBS=$(awk -v c="$(getconf _NPROCESSORS_ONLN 2>/dev/null || echo 1)" -v l="$(cut -d' ' -f1 /proc/loadavg 2>/dev/null || echo 0)" \
    'BEGIN { f = (c - l) / 8; if (f > 8) f = 8; m = int(c / 2); if (m > 4) m = 4; if (m < 1) m = 1; if (f < m) f = m; print int(f) }')
fi
case "$JOBS" in ''|*[!0-9]*|0) echo "FRONTEND_JOBS must be a positive integer"; exit 2;; esac
{ [ $UPDATE = 1 ] || [ $UPDATE_BFV = 1 ] || [ $LIVE = 1 ]; } && JOBS=1
run_sections() {
  local s i n=$# names=("$@") tmp p f
  if [ "$JOBS" -le 1 ]; then
    for s in "$@"; do "$s"; done
    return
  fi
  tmp="$(mktemp -d)"
  for ((i = n - 1; i >= 0; i--)); do   # the long sections (8, 9) are last: start them first
    while [ "$(jobs -rp | wc -l)" -ge "$JOBS" ]; do wait -n; done
    ( pass=0; fail=0; "${names[$i]}"; echo "$pass $fail" >"$tmp/$i.count" ) >"$tmp/$i.out" 2>&1 </dev/null &
  done
  wait
  for ((i = 0; i < n; i++)); do
    cat "$tmp/$i.out"
    if read -r p f <"$tmp/$i.count" 2>/dev/null && [ -n "$p" ] && [ -n "$f" ]; then
      pass=$((pass + p)); fail=$((fail + f))
    else
      bad "section ${names[$i]} did not finish"
    fi
  done
  rm -rf "$tmp"
}

s_1() {
echo "== 1. extractors reproduce the committed examples"
for pj in examples/openfhe_*.params.json; do
  n=$(basename "$pj" .params.json)
  is_bfv "$pj" && continue  # BFV: section 9
  if python3 -I openfhe/extract.py --params examples/$n.params.json --trace examples/$n.trace.jsonl \
       --artifact $n 2>/dev/null | cmp -s - examples/$n.fhecheck.json; then ok; else bad "openfhe extractor drifted: $n"; fi
done
for nm in mult_dep_8.worstcase mult_dep_8.default dot_product_8.worstcase cmux.worstcase; do
  n=${nm%.*}; m=${nm#*.}
  if python3 -I heir/extract_bgv.py examples/heir_$n.lattigo.$m.mlir | cmp -s - examples/heir_$n.$m.fhecheck.json
  then ok; else bad "heir extractor drifted: $nm"; fi
done
}

s_2() {
echo "== 2. verdicts, exit codes and key figures (tests/expected.tsv)"
while IFS=$'\t' read -r f code verdict text; do
  case "$f" in ''|\#*) continue;; esac
  out="$("$FHE_CHECK" "$f")"; rc=$?
  [ "$rc" = "$code" ] || bad "$f: exit $rc, expected $code"
  grep -qE "^VERDICT: $verdict( \([^:]*\))?:" <<<"$out" || bad "$f: verdict is not $verdict"
  grep -qF -- "$text" <<<"$out" && ok || bad "$f: missing text: $text"
  # JSON mode agrees on the verdict
  j="$("$FHE_CHECK" --json "$f")"
  python3 -I -c "import json,sys; sys.exit((lambda d: sys.argv[1] != d['verdict'] and not (d.get('verdictLabel') or '').startswith(sys.argv[1]))(json.load(sys.stdin)))" "$verdict" <<<"$j" \
    && ok || bad "$f: --json verdict differs"
done < tests/expected.tsv
}

s_2b() {
echo "== 2b. probabilistic mode: fhe_check --kappa K (tests/expected-kappa.tsv)"
while IFS=$'\t' read -r f kappa code verdict text; do
  case "$f" in ''|\#*) continue;; esac
  out="$("$FHE_CHECK" --kappa "$kappa" "$f")"; rc=$?
  [ "$rc" = "$code" ] || bad "$f --kappa $kappa: exit $rc, expected $code"
  grep -qE "^VERDICT: $verdict( \([^:]*\))?:" <<<"$out" || bad "$f --kappa $kappa: verdict is not $verdict"
  grep -qF -- "$text" <<<"$out" && ok || bad "$f --kappa $kappa: missing text: $text"
  j="$("$FHE_CHECK" --kappa "$kappa" --json "$f")"
  python3 -I -c "import json,sys; sys.exit((lambda d: sys.argv[1] != d['verdict'] and not (d.get('verdictLabel') or '').startswith(sys.argv[1]))(json.load(sys.stdin)))" "$verdict" <<<"$j" \
    && ok || bad "$f --kappa $kappa: --json verdict differs"
done < tests/expected-kappa.tsv
# monotone in kappa: a file certified at K is certified at every smaller K tried
for f in examples/openfhe_*.fhecheck.json; do
  is_bfv "$f" && continue  # BFV: --kappa rows in tests/expected-kappa.tsv (kept out of this loop for time)
  prev=0
  for k in 128 64 40; do
    "$FHE_CHECK" --no-suggest --kappa $k "$f" >/dev/null; rc=$?
    [ $prev = 1 ] && [ $rc != 0 ] && bad "$f: certified at a larger kappa but not at $k"
    [ $rc = 0 ] && prev=1
  done
  ok
done
"$FHE_CHECK" --kappa notanumber examples/openfhe_depth2_fixedmanual.fhecheck.json >/dev/null 2>&1
[ $? = 4 ] && ok || bad "--kappa with a non-number is not a usage error"
# K = 0 (failure probability <= 1: says nothing) and absurd K are usage errors
for k in 0 00 1000001 99999999999999999999999999; do
  e="$("$FHE_CHECK" --kappa $k examples/openfhe_depth2_fixedmanual.fhecheck.json 2>&1 >/dev/null)"; rc=$?
  [ $rc = 4 ] && grep -q -- "--kappa" <<<"$e" && ok || bad "--kappa $k is not a usage error (exit $rc)"
done
# K below the floor (40): a prominent warning directly under the verdict; none at 40
out="$("$FHE_CHECK" --no-suggest --kappa 39 examples/openfhe_depth2_fixedmanual.fhecheck.json)"
sed -n 3p <<<"$out" | grep -q "^WARNING: --kappa 39 IS BELOW 40" && ok || bad "--kappa 39: no warning under the verdict"
k40out="$("$FHE_CHECK" --no-suggest --kappa 40 examples/openfhe_depth2_fixedmanual.fhecheck.json)"
grep -q "IS BELOW" <<<"$k40out" \
  && bad "--kappa 40 carries the below-floor warning" || ok
}

s_2c() {
echo "== 2c. red-team regressions (tests/expected-redteam.tsv; every run under a 30 s timeout)"
# Each line: a witness of a past wrong verdict or hang (described in the .tsv) and what the tool
# must say now. `args` is "-" or a --kappa value. A timeout (exit 124) is a failure.
while IFS=$'\t' read -r f args code verdict text; do
  case "$f" in ''|\#*) continue;; esac
  if [ "$args" = "-" ]; then a=(); else a=(--kappa "$args"); fi
  out="$(timeout 30 "$FHE_CHECK" --no-suggest "${a[@]}" "$f")"; rc=$?
  [ "$rc" = 124 ] && { bad "$f ${a[*]}: TIMEOUT (30 s)"; continue; }
  [ "$rc" = "$code" ] || bad "$f ${a[*]}: exit $rc, expected $code"
  grep -qE "^VERDICT: $verdict( \([^:]*\))?:" <<<"$out" || bad "$f ${a[*]}: verdict is not $verdict"
  grep -qF -- "$text" <<<"$out" && ok || bad "$f ${a[*]}: missing text: $text"
  j="$(timeout 30 "$FHE_CHECK" --no-suggest --json "${a[@]}" "$f")"
  python3 -I -c "import json,sys; sys.exit((lambda d: sys.argv[1] != d['verdict'] and not (d.get('verdictLabel') or '').startswith(sys.argv[1]))(json.load(sys.stdin)))" "$verdict" <<<"$j" \
    && ok || bad "$f ${a[*]}: --json verdict differs"
done < tests/expected-redteam.tsv
# No red-team input may be CERTIFIED with a probabilistic claim unless listed as such above; and
# every committed example and negative finishes within the timeout in both modes.
for f in examples/*.fhecheck.json tests/negative/*.json tests/redteam/*.json; do
  timeout 60 "$FHE_CHECK" --no-suggest "$f" >/dev/null 2>&1; [ $? = 124 ] && bad "$f: TIMEOUT" || ok
  timeout 60 "$FHE_CHECK" --no-suggest --kappa 128 "$f" >/dev/null 2>&1; [ $? = 124 ] && bad "$f --kappa 128: TIMEOUT" || ok
done
}

s_2d() {
echo "== 2d. security note (--json) and the program-size limit"
# --json carries the security note as data, never as part of the verdict
"$FHE_CHECK" --json tests/negative/security_above_cap.json | python3 -I -c '
import json, sys
d = json.load(sys.stdin); s = d["security"]
assert d["verdict"] == "CERTIFIED" and d["certifiedProperty"] == "correctness (exact decryption), not security"
assert s["partOfVerdict"] is False and s["log2QP"] == 254.99 and s["caps"]["128"] == 218 and s["exceeds128"] is True
assert any(w.startswith("SECURITY") for w in d["warnings"])' && ok || bad "--json security note (above the cap)"
"$FHE_CHECK" --json tests/negative/security_toy_n.json | python3 -I -c '
import json, sys
s = json.load(sys.stdin)["security"]
assert s["caps"] is None and s["row"] == "none" and "below the standard" in s["noEntry"] and s["exceeds128"] is None' \
  && ok || bad "--json security note (toy N)"
"$FHE_CHECK" --json examples/openfhe_depth8_q55_fixedmanual.fhecheck.json | python3 -I -c '
import json, sys
d = json.load(sys.stdin)
assert d["security"]["exceeds128"] is False and "warnings" not in d' && ok || bad "--json security note (within the cap)"
# a program above --max-instructions is UNSUPPORTED (exit 2) before any analysis, with an estimate;
# 0 removes the limit
f=examples/openfhe_depth8_q55_fixedmanual.fhecheck.json
out="$("$FHE_CHECK" --max-instructions 5 "$f")"; rc=$?
[ $rc = 2 ] && grep -qF "VERDICT: UNSUPPORTED: program too large:" <<<"$out" && grep -qF "above the limit of 5 (--max-instructions N; 0 = no limit)" <<<"$out" \
  && ok || bad "--max-instructions 5: not refused as too large (exit $rc)"
mi0out="$("$FHE_CHECK" --max-instructions 0 "$f")"
grep -q "^VERDICT: CERTIFIED:" <<<"$mi0out" && ok || bad "--max-instructions 0 does not remove the limit"
# a closed pipe (the reader of standard output went away): exit 141 quietly, no uncaught exception
bpe="$( { "$FHE_CHECK" --no-suggest examples/openfhe_depth2_fixedmanual.fhecheck.json | (exec <&-; true); echo "rc=${PIPESTATUS[0]}"; } 2>&1 )"
grep -q "rc=141" <<<"$bpe" && ! grep -q "uncaught exception" <<<"$bpe" && ok || bad "closed stdout: expected exit 141 without an uncaught exception, got: $bpe"
# the same limit for BFV (a BFV file goes through its own pipeline)
out="$("$FHE_CHECK" --max-instructions 3 examples/openfhe_bfv_default_chain_d3.fhecheck.json)"; rc=$?
[ $rc = 2 ] && grep -qF "VERDICT: UNSUPPORTED: program too large: 6 instructions, above the limit of 3" <<<"$out" \
  && ok || bad "BFV --max-instructions 3: not refused as too large (exit $rc)"
"$FHE_CHECK" --max-instructions x "$f" >/dev/null 2>&1; [ $? = 4 ] && ok || bad "--max-instructions x is not a usage error"
# the default limit, on a program generated here (rotate-and-add, just above the limit; refused
# after decoding, so it takes seconds)
big="$(mktemp)"
lim="$("$FHE_CHECK" --help | sed -n 's/^ *\([0-9][0-9]*\); 0 = no limit.*/\1/p' | head -1)"
python3 -I - "$f" "$big" "$lim" <<'PY'
import json, sys
d = json.load(open(sys.argv[1])); n = int(sys.argv[3]) + 1
L = len(d["params"]["limbs"])
body = []
for i in range(n):
    body.append({"op": "add", "dst": f"x{i}", "a": f"x{i-1}" if i else "ct_1", "b": "ct_2"})
d["program"].update(inputs=[{"name": "ct_1", "parts": 2, "level": L}, {"name": "ct_2", "parts": 2, "level": L}],
                    body=body, outputs=[f"x{n-1}"])
d["freshEncryption"]["inputs"] = ["ct_1", "ct_2"]
d.pop("provenance", None)
json.dump(d, open(sys.argv[2], "w"))
PY
out="$(timeout 120 "$FHE_CHECK" "$big")"; rc=$?
[ $rc = 2 ] && grep -qF "program too large: $((lim + 1)) instructions, above the limit of $lim" <<<"$out" \
  && ok || bad "a program of $((lim + 1)) instructions is not refused by the default limit $lim (exit $rc)"
rm -f "$big"
}

s_2e() {
echo "== 2e. the l2 description of fresh encryptions (--kappa K --l2; Challenge.Certify.fresh_l2_certified)"
# nothing supplied: every l2 value computed from the support bounds, so eps is the support model's
out="$("$FHE_CHECK" --no-suggest --kappa 128 --l2 examples/openfhe_depth2_fixedmanual.fhecheck.json)"; rc=$?
[ $rc = 0 ] && grep -qF "(computed), S2 = 16384 (computed), Vu = 1 (computed), V1 = 1521 (computed), V2 = 1521 (computed)" <<<"$out" \
  && [ "$(grep -o 'Spec.Encrypt.epsFor = [0-9]*' <<<"$out")" = "$("$FHE_CHECK" --no-suggest --kappa 128 examples/openfhe_depth2_fixedmanual.fhecheck.json | grep -o 'Spec.Encrypt.epsFor = [0-9]*')" ] \
  && ok || bad "--kappa 128 --l2 with computed values is not the support model (exit $rc)"
# values supplied by the input: ASSUMPTIONS, named in the certificate; a smaller eps
out="$("$FHE_CHECK" --no-suggest --kappa 128 --l2 tests/negative/l2_supplied.json)"; rc=$?
[ $rc = 0 ] && grep -qF "E2 = 180224 (input), S2 = 16384 (computed), Vu = 1 (input), V1 = 11 (input), V2 = 11 (input)" <<<"$out" \
  && grep -qF "error bound eps = Spec.Encrypt.epsFor + drift = 8514" <<<"$out" \
  && grep -qF "drift = Spec.Encrypt.meanDrift (E2+1+S2) = 1" <<<"$out" \
  && grep -qF "The ONE Lean theorem instantiated is Challenge.Certify.fresh_l2_certified" <<<"$out" \
  && grep -qF "ASSUMED: supplied by the input" <<<"$out" && grep -qF "NOT proved here (an assumption whenever a proxy is below" <<<"$out" \
  && ok || bad "--kappa 128 --l2 with supplied values (exit $rc)"
"$FHE_CHECK" --no-suggest --json --kappa 128 --l2 tests/negative/l2_supplied.json | python3 -I -c '
import json, sys
d = json.load(sys.stdin); m = d["mode"]
assert d["verdict"] == "CERTIFIED" and d["certificateTheorem"] == "Challenge.Certify.fresh_l2_certified"
assert m["kind"] == "fresh-noise-probabilistic-l2" and m["eps"] == "8514" and m["meanDrift"] == "1"
assert m["l2"]["suppliedByInput"] == {"keyErrorSq": True, "secretSq": False, "uProxy": True, "e1Proxy": True, "e2Proxy": True}' \
  && ok || bad "--json --kappa 128 --l2"
# not certified in this mode; a malformed l2 field; no freshEncryption; --l2 without --kappa
out="$("$FHE_CHECK" --no-suggest --kappa 128 --l2 examples/openfhe_fixedauto_chain.fhecheck.json)"; rc=$?
[ $rc = 1 ] && grep -q "^VERDICT: NOT CERTIFIED:" <<<"$out" && ok || bad "--kappa 128 --l2: an automatic-mode chain is certified (exit $rc)"
out="$("$FHE_CHECK" --no-suggest --kappa 128 --l2 tests/negative/l2_malformed.json)"; rc=$?
[ $rc = 3 ] && grep -qF 'VERDICT: INVALID INPUT: $.freshEncryption.l2.e1Proxy: "eleven" is not a decimal natural number' <<<"$out" \
  && ok || bad "--l2: a malformed l2 field is not INVALID INPUT (exit $rc)"
"$FHE_CHECK" --no-suggest --kappa 128 --l2 examples/heir_mult_dep_8.worstcase.fhecheck.json >/dev/null; [ $? = 2 ] \
  && ok || bad "--l2 on a file without freshEncryption is not UNSUPPORTED"
"$FHE_CHECK" --l2 examples/openfhe_depth2_fixedmanual.fhecheck.json >/dev/null 2>&1; [ $? = 4 ] \
  && ok || bad "--l2 without --kappa is not a usage error"
}

s_3() {
echo "== 3. golden outputs (human and --json; OpenFHE examples also with --kappa 128)"
# The tool never cites a theorem about an analyzer it did not run: the only analyzer named in a
# report's theorem list is refAnalyze.
"$FHE_CHECK" --json examples/openfhe_depth8_q55_fixedmanual.fhecheck.json | python3 -I -c '
import json, sys
d = json.load(sys.stdin)
assert d["analyzer"] == "Challenge.Headline.refAnalyze", d["analyzer"]
assert d["certificateTheorem"] == "Challenge.Certify.worst_certified"
assert not any("analyze_sound" in t["name"] for t in d["theorems"])' && ok || bad "report cites a theorem about another analyzer"
for f in examples/*.fhecheck.json tests/negative/*.json; do
  g="tests/golden/$(basename "$f" .json)"
  upd=$UPDATE; is_bfv "$f" && upd=$UPDATE_BFV  # BFV: --update-bfv
  for mode in txt json; do
    if [ $mode = json ]; then out="$("$FHE_CHECK" --json "$f")"; else out="$("$FHE_CHECK" --steps "$f")"; fi
    if [ $upd = 1 ]; then printf '%s\n' "$out" > "$g.$mode"; ok
    elif printf '%s\n' "$out" | cmp -s - "$g.$mode"; then ok
    else bad "golden differs: $g.$mode (diff <($FHE_CHECK $f) $g.$mode)"; fi
  done
done
for f in examples/openfhe_*.fhecheck.json; do
  is_bfv "$f" && continue  # BFV: --kappa rows in tests/expected-kappa.tsv (kept out of this loop for time)
  g="tests/golden/$(basename "$f" .json).kappa128"
  for mode in txt json; do
    if [ $mode = json ]; then out="$("$FHE_CHECK" --kappa 128 --json "$f")"; else out="$("$FHE_CHECK" --kappa 128 --steps "$f")"; fi
    if [ $UPDATE = 1 ]; then printf '%s\n' "$out" > "$g.$mode"; ok
    elif printf '%s\n' "$out" | cmp -s - "$g.$mode"; then ok
    else bad "golden differs: $g.$mode (diff <($FHE_CHECK --kappa 128 $f) $g.$mode)"; fi
  done
done
}

s_4() {
echo "== 4. agreement with the untrusted preview_check.py"
python3 -I tests/compare_preview.py "$FHE_CHECK" "${BGV_FILES[@]}" && ok || bad "preview disagreement"
}

s_5() {
echo "== 5. the certificate statement names the theorems and does not overclaim"
out="$("$FHE_CHECK" examples/openfhe_depth8_q55_fixedmanual.fhecheck.json)"
for s in "Challenge.Certify.worst_certified" "Challenge.Certify.certify?" "Challenge.Budget.certified_sound" \
         "HOW THE VERDICT WAS COMPUTED: by FHE.Holes.certifyFast" "Challenge.Fast.certifyFast_eq" \
         "Challenge.Headline.refAnalyze (the reference worst-case BGV" \
         "the hole FHE.Holes.analyze of the headline theorem is defined as this same" \
         "Outputs (bound = Challenge.Headline.refAnalyze on the program with this output alone)" \
         "Spec.Encrypt.certOK?" "an output left under a rotated key sigma_g(s) is refused" \
         "Challenge.Budget.relin_realizable" "Challenge.Budget.modSwitch_realizable_parts" \
         "Challenge.Budget.modSwitch_realizable" "Challenge.Budget.modSwitch_realizable_one" \
         "Spec.Budget.specialOK?" "DECRYPTION COVERED: decryption with the PHASE switched to one limb" \
         "By the certificate theorem each output then decrypts" "NOT covered: the COEFFICIENT-format branch" \
         "NOT for" "No security claim" "Neither OpenFHE, nor HEIR, nor Lattigo has been verified" \
         "inputNoise = 167508901927"; do
  grep -qF -- "$s" <<<"$out" && ok || bad "statement lacks: $s"
done

out="$("$FHE_CHECK" --kappa 128 examples/openfhe_depth2_fixedmanual.fhecheck.json | tr '\n' ' ')"
for s in "CERTIFIED (fresh-noise failure probability at most 2^-128; evaluation worst-case). For every secret and public key within the stated bounds and every choice of the 3 input messages: if each encryption draws its coefficients independently, within the sampler bounds and with means within the stated mean bound, then with probability at least 1 - 2^-128 over the encryption randomness alone, every output of this program decrypts exactly. Assumed, not verified: the library's samplers meet that description; the library's operations meet the per-operation contracts. No probability is taken over messages, keys or rounding. No security claim." \
         "The ONE Lean theorem instantiated is Challenge.Certify.fresh_kappa_certified" \
         "it declares NO bound of its own" "The analysis is Challenge.Headline.refAnalyze" "Challenge.Fast.certifyFast_eq" \
         "freshError_tail" "epsFor_spec" \
         "Challenge.FreshNoise.SamplerOK" "fhe_check did not check them" \
         "What it does NOT say" "Neither OpenFHE, nor HEIR, nor Lattigo has been verified"; do
  grep -qF -- "$s" <<<"$out" && ok || bad "--kappa statement lacks: $s"
done
# worst-case reports must not contain the probabilistic claim, and failures must mark suggestions
out="$("$FHE_CHECK" examples/openfhe_depth2_fixedmanual.fhecheck.json)"
grep -qF "fresh-noise failure probability" <<<"$out" && bad "worst-case report makes a probabilistic claim" || ok
grep -qF "NOT a theorem, not proved minimal" <<<"$out" && ok || bad "suggestions are not marked as non-theorems"
grep -qF "SUGGESTIONS" <<<"$("$FHE_CHECK" --no-suggest examples/openfhe_depth2_fixedmanual.fhecheck.json)" \
  && bad "--no-suggest still prints suggestions" || ok
}

s_6() {
echo "== 6. OpenFHE: plaintext-value cross-check on the committed small-ring runs (tests/values)"
# Each fixture is a bgv_demo run at N = 1024 (all programs x all scaling techniques): the
# extraction must succeed with zero scale/level mismatches, and the untrusted message-level
# evaluator (openfhe/value_check.py) must reproduce OpenFHE's raw decryption exactly.
for d in tests/values/*/; do
  n=$(basename "$d")
  j="$(python3 -I openfhe/extract.py --params "$d/params.json" --trace "$d/trace.jsonl" --artifact "$n")"
  if python3 -I -c "import json,sys; d=json.load(sys.stdin); sys.exit('error' in d or d['crossCheck']['mismatches'] != [])" <<<"$j"
  then ok; else bad "extraction or scale/level cross-check failed: $n"; continue; fi
  vcout="$(python3 -I openfhe/value_check.py /dev/stdin "$d/values.json" <<<"$j")"
  if grep -q "value_check: OK" <<<"$vcout"
  then ok; else bad "value cross-check failed: $n"; fi
done
# The value check must catch a wrong operation mapping (mutants of one fixture).
python3 -I - "tests/values/n1024_flexibleautoext_rotsum" <<'PY' && ok || bad "value_check accepted a mutant"
import copy, json, subprocess, sys
d = sys.argv[1]
doc = json.loads(subprocess.run([sys.executable, "-I", "openfhe/extract.py", "--params", d + "/params.json",
                                 "--trace", d + "/trace.jsonl"], capture_output=True, text=True).stdout)
muts = []
for i, ins in enumerate(doc["program"]["body"]):
    if ins["op"] == "mulConst": muts.append((i, "c", str(int(ins["c"]) + 1)))
    if ins["op"] == "automorph": muts.append((i, "g", ins["g"] + 2))
    if ins["op"] == "modSwitch": muts.append((i, "op", "copy"))
    if ins["op"] == "sub": muts.append((i, "op", "add"))
assert len(muts) >= 4, muts
for i, k, v in muts:
    m = copy.deepcopy(doc); m["program"]["body"][i][k] = v
    r = subprocess.run([sys.executable, "-I", "openfhe/value_check.py", "/dev/stdin", d + "/values.json"],
                       input=json.dumps(m), capture_output=True, text=True)
    if r.returncode != 1:
        sys.exit(f"mutant body[{i}].{k}={v} not caught")
PY
# The factor of a plaintext product is compared even when OpenFHE's BGV wrapper leaves the
# ciphertext (and its scalingFactorInt) unchanged: a hand-made trace in which the plaintext
# carries factor 2 (as after a user SetScalingFactorInt) while the product keeps the tracked
# factor 1, cut after the product so nothing downstream catches it, must be refused. (Before the
# fix the extractor accepted it: the true factor 2 escaped the replay, and Decode would divide by 1.)
python3 -I - examples/openfhe_fixedmanual_plain <<'PY' && ok || bad "extractor accepted a plaintext product whose true factor differs from the tracked one"
import json, subprocess, sys, tempfile
sys.path.insert(0, "openfhe"); sys.dont_write_bytecode = True
from extract import stamp_tracer  # the derived trace is no committed one: stamp its params with the current tracer
n = sys.argv[1]
lines, inside = [], False
for line in open(n + ".trace.jsonl"):
    o = json.loads(line)
    if o.get("id") in ("pt_4", "ct_7", "ct_8"): o["sf"] = 2
    lines.append(json.dumps(o, separators=(",", ":")))
    if o["ev"] == "begin" and o["d"] == 0 and o["fn"] == "CryptoContext::EvalMult(Ciphertext,Plaintext)": inside = True
    if inside and o["ev"] == "end" and o["d"] == 0: break
with tempfile.NamedTemporaryFile("w", suffix=".jsonl", delete=False) as f:
    f.write("\n".join(lines) + "\n")
with tempfile.NamedTemporaryFile("w", suffix=".json", delete=False) as pf:
    json.dump(stamp_tracer(json.load(open(n + ".params.json"))), pf)
r = subprocess.run([sys.executable, "-I", "openfhe/extract.py", "--params", pf.name, "--trace", f.name],
                   capture_output=True, text=True)
d = json.loads(r.stdout)
sys.exit(not (r.returncode == 1 and "Source scale 2 != OpenFHE scalingFactorInt 1" in d.get("error", "")))
PY
# Soundness of the input rule: a ciphertext no traced operation produced is an extraction error
# (here: the trace with its Encrypt calls removed), and --assume-fresh-inputs does not apply to an
# unknown ciphertext first used after a traced operation produced one (this program's second input);
# its positive cases are in 6c and 9g.
d=tests/values/n1024_flexibleauto_dot
strip="$(mktemp)"
python3 -I - "$d/trace.jsonl" > "$strip" <<'PY'
import json, sys
out, skip = [], None
for line in open(sys.argv[1]):
    o = json.loads(line)
    if skip is None and o["ev"] == "begin" and o["fn"].startswith("CryptoContext::Encrypt"):
        skip = o["d"]; continue
    if skip is not None:
        if o["ev"] == "end" and o["d"] == skip: skip = None
        continue
    print(line, end="")
PY
# the stripped trace is no committed one: its params.json is stamped with the current tracer version
sp="$(mktemp)"; python3 -I openfhe/tracer_version.py --stamp "$d/params.json" > "$sp"
e="$(python3 -I openfhe/extract.py --params "$sp" --trace "$strip")"  # exits 1 by design
grep -q "no traced operation produced it" <<<"$e" \
  && ok || bad "extractor accepted a ciphertext that no traced operation produced"
e="$(python3 -I openfhe/extract.py --params "$sp" --trace "$strip" --assume-fresh-inputs)"  # exits 1 by design
grep -q 'assume-fresh-inputs does not apply' <<<"$e" \
  && ok || bad "--assume-fresh-inputs was applied to a ciphertext first used mid-program"
rm -f "$strip" "$sp"
}

s_6c() {
echo "== 6c. what is certified is what is decrypted, from traced values (tests/tamper/: real runs + trace mutations, strict schema, --idealised label)"
FHE_CHECK="$FHE_CHECK" python3 -I tests/tamper/check.py && ok || bad "tamper / hardening checks (tests/tamper/check.py)"
python3 -I tests/tamper/sha256_test.py && ok || bad "the tracer's SHA-256 disagrees with hashlib (tests/tamper/sha256_test.py)"
}

s_6b() {
echo "== 6b. OpenFHE key provenance and refusals (tests/keyprov/expected.tsv, tests/refused/)"
# Threshold/multiparty witness, keys without traced generation, a rotation key used for another
# index, two secrets, a trace written from another thread, an operand with no traced origin, and
# programs the extractor must refuse by name (EvalInnerProduct/EvalSum on OpenFHE >= 1.6).
FHE_CHECK="$FHE_CHECK" python3 -I tests/keyprov/check.py && ok || bad "key-provenance / refusal checks (tests/keyprov/check.py)"
# run.sh itself: a RELATIVE FHE_CHECK given from the repository root must resolve (it used to be
# resolved after the cd below and failed 631 tests)
rel="$(python3 -I -c 'import os,sys; print(os.path.relpath(sys.argv[1], sys.argv[2]))' "$FHE_CHECK" "$ROOT")"
got="$(cd "$ROOT" && FHE_CHECK="$rel" harness/frontend/tests/run.sh --print-fhe-check)"
[ "$got" = "$FHE_CHECK" ] && [ -x "$got" ] && ok || bad "a relative FHE_CHECK ($rel) resolves to '$got'"
}

s_6d() {
echo "== 6d. tracer version: traces of another fhecheck-tracer.h are refused (openfhe/tracer_version.py, legacy-traces.tsv)"
# the header's FHECHECK_TRACER_VERSION is the SHA-256 of its content (with the value zeroed), and
# legacy-traces.tsv lists exactly the committed unversioned traces
python3 -I openfhe/tracer_version.py >/dev/null && ok || bad "fhecheck-tracer.h: FHECHECK_TRACER_VERSION is stale (run openfhe/tracer_version.py --update-header)"
python3 -I openfhe/tracer_version.py --allowlist --check >/dev/null && ok || bad "openfhe/legacy-traces.tsv is not the list of committed unversioned traces"
python3 -I - <<'PY' && ok || bad "a trace of another tracer version, or an unversioned trace that is not committed, was not refused"
import json, os, re, shutil, subprocess, sys, tempfile
sys.path.insert(0, "openfhe"); sys.dont_write_bytecode = True
from extract import stamp_tracer, tracer_header_version
REBUILD = "rebuild OpenFHE with harness/frontend/openfhe/build_openfhe.sh"
cases = [("openfhe/extract.py", "examples/openfhe_dot_depth2.params.json", "examples/openfhe_dot_depth2.trace.jsonl"),
         ("openfhe/extract_bfv.py", "tests/values-bfv/n16_hpspoverqleveled_hybrid_chain_d4_q30/params.json",
          "tests/values-bfv/n16_hpspoverqleveled_hybrid_chain_d4_q30/trace.jsonl")]
def run(script, ptext, trace):
    with tempfile.NamedTemporaryFile("w", suffix=".json", delete=False) as f:
        f.write(ptext)
    try:
        r = subprocess.run([sys.executable, "-I", script, "--params", f.name, "--trace", trace], capture_output=True, text=True)
    finally:
        os.unlink(f.name)
    return r.returncode, json.loads(r.stdout)
for script, params, trace in cases:
    raw = open(params).read()
    p = json.loads(raw)
    assert "tracer" not in p, params
    # the committed (unversioned, listed) pair is accepted as it is
    rc, d = run(script, raw, trace)
    assert rc == 0 and "error" not in d, (script, "committed", d.get("error"))
    # a JSON-insignificant change (one extra space) makes it an unlisted unversioned trace: refused ...
    rc, d = run(script, raw.replace("{", "{ ", 1), trace)
    e = d.get("error", "")
    assert rc == 1 and "trace written by a different fhecheck tracer" in e and "records no tracer version" in e and REBUILD in e, (script, e)
    # ... and the same file with the current version is accepted (so the refusal came from the tracer check)
    rc, d = run(script, json.dumps(stamp_tracer(json.loads(raw.replace("{", "{ ", 1)))), trace)
    assert rc == 0 and "error" not in d, (script, "stamped", d.get("error"))
    # another recorded version: refused, naming both versions
    rc, d = run(script, json.dumps(dict(p, tracer="0" * 64)), trace)
    e = d.get("error", "")
    _, cur = tracer_header_version()
    assert rc == 1 and f"recorded {'0' * 64}, current {cur}" in e and REBUILD in e, (script, e)
# editing the header without updating the version changes the computed version (fail closed)
with tempfile.TemporaryDirectory() as tmp:
    h = open("openfhe/fhecheck-tracer.h").read()
    open(tmp + "/h", "w").write(h.replace("It only OBSERVES", "It only observes", 1))
    declared, computed = tracer_header_version(tmp + "/h")
    assert declared == tracer_header_version()[0] and computed != declared
PY
}

s_8a() {
echo "== 8. fhe_check recommend (tests/recommend/; every run under a 120 s timeout)"
# (a) A recommendation for every committed example: golden human and --json outputs; when one is
#     found, the emitted file is CERTIFIED by a PLAIN fhe_check run (exit 0) and carries exactly
#     the primes the report names; when none is found, nothing is emitted.
mkdir -p tests/recommend/golden
for f in examples/*.fhecheck.json; do
  is_bfv "$f" && continue  # recommend answers UNSUPPORTED for BFV: one check in section 9
  n=$(basename "$f" .fhecheck.json); g="tests/recommend/golden/$n"
  em="$(mktemp)"; rm -f "$em"
  out="$(timeout 120 "$FHE_CHECK" recommend "$f")"; rc=$?
  j="$(timeout 120 "$FHE_CHECK" recommend --json --emit "$em" "$f")"; rcj=$?
  { [ $rc = 124 ] || [ $rcj = 124 ]; } && { bad "recommend $f: TIMEOUT"; continue; }
  [ "$rc" = "$rcj" ] && ok || bad "recommend $f: exit $rc in text mode, $rcj with --json"
  for mode in txt json; do
    if [ $mode = json ]; then o="$j"; else o="$out"; fi
    if [ $UPDATE = 1 ]; then printf '%s\n' "$o" > "$g.$mode"; ok
    elif printf '%s\n' "$o" | cmp -s - "$g.$mode"; then ok
    else bad "golden differs: $g.$mode (diff <($FHE_CHECK recommend $f) $g.$mode)"; fi
  done
  if [ "$rc" = 0 ]; then
    "$FHE_CHECK" --no-suggest "$em" > /dev/null && ok || bad "recommend $f: the emitted file is not CERTIFIED by a plain check"
    printf '%s' "$j" > "$em.report"
    python3 -I - "$em" "$em.report" <<'PY' && ok || bad "recommend $f: emitted primes differ from the report"
import json, sys
e = json.load(open(sys.argv[1])); r = json.load(open(sys.argv[2]))
q = [l["q"] for l in e["params"]["limbs"]]; p = [l["q"] for l in e["params"]["special"]]
sys.exit(not (r["verdict"] == "CERTIFIED" and q == r["limbs"] and p == r["special"] and e["params"]["N"] == r["N"]))
PY
  else
    [ ! -e "$em" ] && ok || bad "recommend $f: a file was emitted without a recommendation"
  fi
  rm -f "$em" "$em.report"
done
}

s_8b() {
# (b) The prime mirror reproduces the library's own primes: with the sizes, digits and N of each
#     committed OpenFHE FIXEDMANUAL and HEIR example, `--sizes` predicts exactly the file's primes.
python3 -I - "$FHE_CHECK" <<'PY' && ok || bad "the prime mirror does not reproduce a library's primes"
import glob, json, subprocess, sys
fhe = sys.argv[1]
files = [f for f in sorted(glob.glob("examples/*.fhecheck.json"))
         if json.load(open(f))["source"].get("tool") == "heir"
         or json.load(open(f))["source"].get("scaling") == "FIXEDMANUAL"]
assert len(files) >= 10, files
for f in files:
    d = json.load(open(f)); p = d["params"]
    q = [int(l["q"] if isinstance(l, dict) else l) for l in p["limbs"]]
    s = [int(l["q"] if isinstance(l, dict) else l) for l in p["special"]]
    if d["source"]["tool"] == "heir":   # HEIR: FirstPrime(b, 2N), b + 1 bits
        args = ["--sizes", ",".join(str(x.bit_length() - 1) for x in q), "--special-size", str(s[0].bit_length() - 1)]
    else:                               # OpenFHE: LastPrime(f), PreviousPrime(LastPrime(s))
        args = ["--sizes", f"{q[0].bit_length()},{q[1].bit_length()}"]
    r = subprocess.run([fhe, "recommend", "--json", "--ring-dim", str(p["N"]), *args, f], capture_output=True, text=True)
    j = json.loads(r.stdout)
    if j["limbs"] != [str(x) for x in q] or j["special"] != [str(x) for x in s]:
        sys.exit(f"{f}: predicted {j['limbs']} {j['special']}")
print(f"prime mirror: {len(files)} files reproduced")
PY
# (b2) With --kappa K the emitted file is CERTIFIED by `fhe_check --kappa K` (the mode it was found in).
em="$(mktemp)"; rm -f "$em"
"$FHE_CHECK" recommend --kappa 128 --emit "$em" examples/openfhe_depth2_fixedmanual.fhecheck.json > /dev/null \
  && kout="$("$FHE_CHECK" --no-suggest --kappa 128 "$em")" \
  && grep -q "^VERDICT: CERTIFIED (\|^VERDICT: CERTIFIED:" <<<"$kout" && ok \
  || bad "recommend --kappa 128: the emitted file is not CERTIFIED by fhe_check --kappa 128"
grep -q '"checkWith": "fhe_check --kappa 128 THIS_FILE"' "$em" && ok || bad "recommend --kappa: the emitted file does not say how to check it"
rm -f "$em"
# (c) Negative and option cases (tests/recommend/expected.tsv).
while IFS=$'\t' read -r args f code text; do
  case "$args" in ''|\#*) continue;; esac
  if [ "$args" = "-" ]; then a=(); else read -ra a <<<"$args"; fi
  out="$(timeout 120 "$FHE_CHECK" recommend "${a[@]}" "$f" 2>&1)"; rc=$?
  [ "$rc" = 124 ] && { bad "recommend $args $f: TIMEOUT"; continue; }
  [ "$rc" = "$code" ] || bad "recommend $args $f: exit $rc, expected $code"
  grep -qF -- "$text" <<<"$out" && ok || bad "recommend $args $f: missing text: $text"
done < tests/recommend/expected.tsv

if [ $LIVE = 1 ]; then
  echo "== 7. live: re-run OpenFHE, re-extract, compare with the committed examples, value-check"
  live="$(mktemp -d)"
  if openfhe/make_examples.sh "$live" > "$live/log" 2>&1; then ok; else bad "make_examples.sh failed (see $live/log)"; fi
  for f in "$live"/examples/*.fhecheck.json; do
    cmp -s "$f" "examples/$(basename "$f")" && ok || bad "live extraction differs from examples/$(basename "$f")"
  done
fi
}

s_9a() {
# ===================================== BFV (begin) =====================================
echo "== 9. BFV: extractor, verdicts (tests/expected-bfv.tsv), negatives, value cross-check, refusals"
# 9a. the OpenFHE BFV extractor reproduces the committed examples
for pj in examples/openfhe_bfv_*.params.json; do
  n=$(basename "$pj" .params.json)
  if python3 -I openfhe/extract_bfv.py --params examples/$n.params.json --trace examples/$n.trace.jsonl \
       --artifact $n 2>/dev/null | cmp -s - examples/$n.fhecheck.json; then ok; else bad "openfhe BFV extractor drifted: $n"; fi
done
# the tracer patch carries exactly openfhe/fhecheck-tracer.h (build_openfhe.sh checks the applied tree)
python3 -I - openfhe/openfhe-v1.6.1-tracer.patch openfhe/fhecheck-tracer.h <<'PY' && ok || bad "the tracer patch does not carry the current openfhe/fhecheck-tracer.h"
import sys
lines, out, on = open(sys.argv[1]).read().split("\n"), [], False
for ln in lines:
    if ln.startswith("diff --git"):
        on = ln.endswith("b/src/pke/include/utils/fhecheck-tracer.h")
    elif on and ln.startswith("+") and not ln.startswith("+++"):
        out.append(ln[1:])
sys.exit(("\n".join(out) + "\n") != open(sys.argv[2]).read())
PY
# 9b. every extracted file has the neutral BFV shape (names the checker reads) and its own cross-checks are clean
python3 -I - examples/openfhe_bfv_*.fhecheck.json <<'PY' && ok || bad "an extracted BFV file lacks a field of the neutral format"
import json, sys
for f in sys.argv[1:]:
    d = json.load(open(f))
    assert d["format"] == "fhe-check/v1" and d["params"]["scheme"] == "BFV", f
    assert all(k in d["params"] for k in ("N", "t", "limbs", "special", "secretBound", "inputNoise", "keyNoise")), f
    ks = d["keySwitching"]
    assert ks["method"] == "hybrid" and ks["variant"] in ("openfhe", "centred") and ks["digits"]["kind"] == "consecutive" and ks["source"], f
    assert (ks["variant"] == "centred") == (d["params"]["special"] == []), f  # BV <-> no special prime, centred digits
    assert d["modSwitch"]["method"] == "round" and d["decryption"]["method"] == "at-output-level", f
    m = d["bfv"]["multiplication"]
    assert m["technique"] in ("HPS", "HPSPOVERQ", "HPSPOVERQLEVELED", "BEHZ") and m["auxBasis"] and m["source"], f
    L = len(d["params"]["limbs"])
    assert len(m["auxBasis"]) == {"HPS": L + 1}.get(m["technique"], L), f
    assert ("mSk" in m and "mTilde" in m) == (m["technique"] == "BEHZ") and m["floatTolerant"] == (m["technique"] != "BEHZ"), f
    assert ("maxInternalDrop" in m and "maxInternalDropKS" in m) == (m["technique"] == "HPSPOVERQLEVELED"), f
    assert ("internalDrops" in m) == (m["technique"] == "HPSPOVERQLEVELED"), f
    ops = [i["op"] for i in d["program"]["body"]]
    assert ("plainAdd" in d["bfv"]) == any(o in ("addPlain", "subPlain") for o in ops), f
    assert not ("square" in ops and m["technique"] in ("HPSPOVERQ", "HPSPOVERQLEVELED")), f  # emitted as mul a a
    assert all(i["parts"] in (1, 2) and (i["parts"] == 2 or "bound" in i) for i in d["program"]["inputs"]), f
    assert d["crossCheck"]["mismatches"] == [] and d["crossCheck"]["findLevelsToDropReplicaAgrees"], f
    if m["technique"] == "HPSPOVERQLEVELED":
        # one declared drop per instruction, equal to the per-instruction provenance (0 where it records none)
        assert len(m["internalDrops"]) == len(ops) == len(d["provenance"]), f
        assert m["internalDrops"] == [p.get("internalDrop", 0) for p in d["provenance"]], f
        assert all(x == 0 or o in ("mul", "square", "relin", "keySwitch") for x, o in zip(m["internalDrops"], ops)), f
        # the declared maxima are those of the per-instruction provenance
        mul = [p["internalDrop"] for p, o in zip(d["provenance"], ops) if "internalDrop" in p and o != "keySwitch"]
        ksd = [p["internalDrop"] for p, o in zip(d["provenance"], ops) if "internalDrop" in p and o == "keySwitch"]
        assert m["maxInternalDrop"] == max(mul, default=0) and m["maxInternalDropKS"] == max(ksd, default=0), f
PY
# 9c. OpenFHE's own FindLevelsToDrop (recorded in every params.json) agrees with the Python replicas
python3 -I tests/check_find_levels_to_drop.py examples/openfhe_bfv_*.params.json tests/values-bfv/*/params.json >/dev/null \
  && ok || bad "FindLevelsToDrop: a replica disagrees with the library's table"
}

s_9d() {
# 9d. verdicts, exit codes and key text (tests/expected-bfv.tsv; --update rewrites it: review the diff)
[ $UPDATE_BFV = 1 ] && python3 -I tests/make_expected_bfv.py "$FHE_CHECK" >/dev/null
while IFS=$'\t' read -r f code verdict text; do
  case "$f" in ''|\#*) continue;; esac
  out="$(timeout 300 "$FHE_CHECK" --no-suggest "$f")"; rc=$?
  [ "$rc" = "$code" ] || bad "$f: exit $rc, expected $code"
  grep -qE "^VERDICT: $verdict( \([^:]*\))?:" <<<"$out" || bad "$f: verdict is not $verdict"
  grep -qF -- "$text" <<<"$out" && ok || bad "$f: missing text: $text"
  j="$(timeout 300 "$FHE_CHECK" --no-suggest --json "$f")"
  python3 -I -c "import json,sys; sys.exit((lambda d: sys.argv[1] != d['verdict'] and not (d.get('verdictLabel') or '').startswith(sys.argv[1]))(json.load(sys.stdin)))" "$verdict" <<<"$j" \
    && ok || bad "$f: --json verdict differs"
done < tests/expected-bfv.tsv
# every BFV example and negative is listed there
for f in examples/openfhe_bfv_*.fhecheck.json tests/negative-bfv/*.json; do
  grep -q "^$f"$'\t' tests/expected-bfv.tsv && ok || bad "$f is not in tests/expected-bfv.tsv"
done
# referee C, F1: a real OpenFHE run (t ~ 2^54, Compress) whose low-limb output is outside the proved decryption condition
f1out="$("$FHE_CHECK" --no-suggest tests/negative-bfv/bfv_f1_compress_t2pow54.json)"
grep -q "^VERDICT: CERTIFIED" <<<"$f1out" \
  && bad "the run of referee C F1 (low-limb decryption outside the proved condition) is CERTIFIED" || ok
# a run whose decryption is outside the proved condition must never be CERTIFIED
n1024out="$("$FHE_CHECK" --no-suggest examples/openfhe_bfv_n1024_default_chain_d2.fhecheck.json)"
grep -q "^VERDICT: CERTIFIED" <<<"$n1024out" \
  && bad "the run with a decryption outside the proved condition (openfhe_bfv_n1024_default_chain_d2) is CERTIFIED" || ok
# 9e. golden outputs of the BFV negatives (the examples' goldens are made in section 3)
for f in tests/negative-bfv/*.json; do
  g="tests/golden/$(basename "$f" .json)"
  for mode in txt json; do
    if [ $mode = json ]; then out="$("$FHE_CHECK" --json "$f")"; else out="$("$FHE_CHECK" --steps "$f")"; fi
    if [ $UPDATE_BFV = 1 ]; then printf '%s\n' "$out" > "$g.$mode"; ok
    elif printf '%s\n' "$out" | cmp -s - "$g.$mode"; then ok
    else bad "golden differs: $g.$mode (diff <($FHE_CHECK $f) $g.$mode)"; fi
  done
done
}

s_9f() {
# 9f. plaintext-value cross-check on the committed tiny-ring runs (tests/values-bfv, N = 16): the
# extraction succeeds with no level/parts mismatch, the untrusted message-level evaluator
# (openfhe/value_check_bfv.py) reproduces OpenFHE's raw decryption, and every observed fresh
# noise is within the derived params.inputNoise
for d in tests/values-bfv/*/; do
  n=$(basename "$d")
  j="$(python3 -I openfhe/extract_bfv.py --params "$d/params.json" --trace "$d/trace.jsonl" --artifact "$n")"
  if python3 -I -c "import json,sys; d=json.load(sys.stdin); sys.exit('error' in d or d['crossCheck']['mismatches'] != [])" <<<"$j"
  then ok; else bad "BFV extraction or level/parts cross-check failed: $n"; continue; fi
  vcout="$(python3 -I openfhe/value_check_bfv.py /dev/stdin "$d/values.json" <<<"$j")"
  if grep -q "value_check_bfv: OK" <<<"$vcout"
  then ok; else bad "BFV value cross-check failed: $n"; fi
done
# the value check must catch a wrong operation mapping (mutants of two fixtures)
python3 -I - tests/values-bfv/n16_hps_hybrid_rotsum tests/values-bfv/n16_hpspoverq_hybrid_plain <<'PY' && ok || bad "value_check_bfv accepted a mutant"
import copy, json, subprocess, sys
n = 0
for d in sys.argv[1:]:
    doc = json.loads(subprocess.run([sys.executable, "-I", "openfhe/extract_bfv.py", "--params", d + "/params.json",
                                     "--trace", d + "/trace.jsonl"], capture_output=True, text=True).stdout)
    muts = []
    for i, ins in enumerate(doc["program"]["body"]):
        if ins["op"] == "automorph": muts.append((i, "g", ins["g"] + 2))
        if ins["op"] == "sub": muts.append((i, "op", "add"))
        if ins["op"] == "add": muts.append((i, "op", "sub"))
        if ins["op"] == "addPlain": muts.append((i, "op", "subPlain"))
        if ins["op"] == "mulPlain": muts.append((i, "op", "addPlain"))
        if ins["op"] == "mul": muts.append((i, "b", ins["a"]) if ins["a"] != ins["b"] else (i, "op", "copy"))
    for i, k, v in muts:
        m = copy.deepcopy(doc); m["program"]["body"][i][k] = v
        r = subprocess.run([sys.executable, "-I", "openfhe/value_check_bfv.py", "/dev/stdin", d + "/values.json"],
                           input=json.dumps(m), capture_output=True, text=True)
        if r.returncode != 1:
            sys.exit(f"{d}: mutant body[{i}].{k}={v} not caught")
        n += 1
assert n >= 8, n
PY
}

s_9g() {
# 9g. the extractor refuses what it does not understand (each mutant of one fixture must give an error document)
python3 -I - tests/values-bfv/n16_hpspoverqleveled_hybrid_chain_d4_q30 <<'PY' && ok || bad "extract_bfv.py accepted an input it must refuse"
import json, os, subprocess, sys, tempfile
d = sys.argv[1]
params = json.load(open(d + "/params.json"))
trace = open(d + "/trace.jsonl").read()
sys.path.insert(0, "openfhe"); sys.dont_write_bytecode = True
from extract import stamp_tracer
def extract(p, t, *extra):
    with tempfile.TemporaryDirectory() as tmp:  # mutants are no committed traces: stamped with the current tracer
        json.dump(stamp_tracer(p), open(tmp + "/p.json", "w")); open(tmp + "/t.jsonl", "w").write(t)
        r = subprocess.run([sys.executable, "-I", "openfhe/extract_bfv.py", "--params", tmp + "/p.json", "--trace", tmp + "/t.jsonl", *extra],
                           capture_output=True, text=True)
        return r.returncode, json.loads(r.stdout)
rc, doc = extract(params, trace)
assert rc == 0 and "error" not in doc and doc["bfv"]["multiplication"]["maxInternalDrop"] == 2, "baseline"
drops0 = doc["bfv"]["multiplication"]["internalDrops"]
assert len(drops0) == len(doc["program"]["body"]) and max(drops0) == 2 and 1 in drops0, "baseline internalDrops"
def strip_encrypt(t):
    out, skip = [], None
    for line in t.splitlines(True):
        o = json.loads(line)
        if skip is None and o["ev"] == "begin" and o["fn"].startswith("CryptoContext::Encrypt"):
            skip = o["d"]; continue
        if skip is not None:
            if o["ev"] == "end" and o["d"] == skip: skip = None
            continue
        out.append(line)
    return "".join(out)
drop1 = json.loads(json.dumps(params)); drop1["levelsToDrop"]["mul"][3] += 1
cases = [
    ("BV digit size", dict(params, keySwitch="BV", digitSizeBV=20, special=[]), trace, "UNSUPPORTED: BV key switching with digit size 20"),
    ("unknown traced operation", params, trace.replace("LeveledSHEBFVRNS::EvalSquare(Ciphertext)", "LeveledSHEBFVRNS::EvalCube(Ciphertext)"), "does not understand"),
    ("untraced constant multiplication", params, trace.replace("LeveledSHEBFVRNS::RelinearizeCore(Ciphertext,EvalKey)", "LeveledSHEBFVRNS::EvalMultCoreInPlace(Ciphertext,NativeInteger)"), "does not understand"),
    ("ciphertext no traced operation produced", params, strip_encrypt(trace), "no traced operation produced it"),
    ("FindLevelsToDrop table differs from the replica", drop1, trace, "the Python replica disagrees with the library"),
    ("Gaussian secret", dict(params, secretKeyDist="GAUSSIAN"), trace, "only UNIFORM_TERNARY"),
    ("unknown multiplication technique", dict(params, multiplicationTechnique="OTHER"), trace, "not mapped"),
    ("threshold context", dict(params, thresholdParties=2), trace, "threshold"),
    ("BGV context", dict(params, scheme="BGV"), trace, "not a BFV context"),
    ("missing auxiliary prime", dict(params, auxR=params["auxR"][:-1]), trace, "auxiliary primes"),
    # the internal drop is observed at run time (levelsDropped hook) and must equal params.json's table
    ("internal drop not recorded", params, "".join(l for l in trace.splitlines(True) if '"levelsDropped"' not in l),
     "the internal drop of HPSPOVERQLEVELED is not recorded"),
    ("internal drop differs from the table", params, "".join(
        l.replace('"name":"levelsDropped","kind":"int","v":2', '"name":"levelsDropped","kind":"int","v":1')
        for l in trace.splitlines(True)), "the FindLevelsToDrop table of params.json says 2"),
    # an UNDERSTATED drop (0 where the library dropped 1): fhe_check could not detect it in the
    # extracted file (tests/negative-bfv/bfv_leveled_understated_drop.json), so the extractor must
    ("internal drop understated in the trace", params, "".join(
        l.replace('"name":"levelsDropped","kind":"int","v":1', '"name":"levelsDropped","kind":"int","v":0')
        for l in trace.splitlines(True)), "the FindLevelsToDrop table of params.json says 1"),
    # ... and the same tampering of the dumped table alone (the replica and the run disagree with it)
    ("internal drop understated in the table", dict(params, levelsToDrop=dict(params["levelsToDrop"], mul=[
        max(0, x - 1) for x in params["levelsToDrop"]["mul"]])), trace, "the Python replica disagrees with the library"),
    ("a tracer reporting an error", params, '{"ev":"error","what":"x"}\n' + trace, "the tracer reported"),
    ("truncated trace", params, trace[: len(trace) // 2].rsplit("\n", 1)[0] + "\n", "unbalanced trace"),
]
for name, p, t, want in cases:
    rc, doc = extract(p, t)
    if rc != 1 or want not in doc.get("error", ""):
        sys.exit(f"{name}: exit {rc}, {str(doc.get('error'))[:200]}")
rc, doc = extract(params, strip_encrypt(trace), "--assume-fresh-inputs")
assert rc == 0 and "assumed fresh encryption" in json.dumps(doc["program"]["inputs"]), "--assume-fresh-inputs"
PY
# 9g2. CoefPacked plaintexts under BFV: accepted exactly when the stored polynomial is in [0, t)
# (BFVRNS, scalingFactorInt = 1); the fixture has negative coefficients and the extremes +-t/2
python3 -I - tests/values-bfv/n16_behz_hybrid_coefpk <<'PY' && ok || bad "extract_bfv.py: CoefPacked plaintexts (accept in [0, t), refuse otherwise)"
import json, os, subprocess, sys, tempfile
d = sys.argv[1]
params = json.load(open(d + "/params.json"))
trace = open(d + "/trace.jsonl").read()
vals = json.load(open(d + "/values.json"))
sys.path.insert(0, "openfhe"); sys.dont_write_bytecode = True
from extract import stamp_tracer
def extract(p, t, script="openfhe/extract_bfv.py"):
    with tempfile.TemporaryDirectory() as tmp:  # mutants are no committed traces: stamped with the current tracer
        json.dump(stamp_tracer(p), open(tmp + "/p.json", "w")); open(tmp + "/t.jsonl", "w").write(t)
        r = subprocess.run([sys.executable, "-I", script, "--params", tmp + "/p.json", "--trace", tmp + "/t.jsonl"],
                           capture_output=True, text=True)
        return r.returncode, json.loads(r.stdout)
t = params["t"]
rc, doc = extract(params, trace)
assert rc == 0 and "error" not in doc, "baseline"
cp = doc["noiseDerivation"]["coefPackedPlaintexts"]["ids"]
ops = [i["op"] for i in doc["program"]["body"]]
assert len(cp) == 4 and {"mulPlain", "addPlain", "subPlain", "mul", "add"} <= set(ops), (cp, ops)
# every CoefPacked plaintext operand is declared with bound t - 1, and the recorded stored coefficients are in
# [0, t), with some >= t/2 (negative values) and the extremes t/2 and t - t/2
plain = [i for i in doc["program"]["inputs"] if i["parts"] == 1]
assert plain and all(i["bound"] == str(t - 1) and i["origin"]["openfhe"] in cp for i in plain), plain
stored = [c for k in cp for c in vals["plaintexts"][k]]
assert all(0 <= c < t for c in stored) and any(2 * c >= t for c in stored) and t // 2 in stored and t - t // 2 in stored
# fresh encryptions of CoefPacked plaintexts: the observed noise is within the declared input noise
fresh = [i["name"] for i in doc["program"]["inputs"] if i["parts"] == 2 and i["origin"]["openfhe"] in cp]
assert len(fresh) == 3 and all(int(vals["fresh"][n]["noise"]) <= int(doc["params"]["inputNoise"]) for n in fresh)
# relabelling the plaintexts as packed gives the same parameters and program (only the derivation note goes)
rc, rel = extract(params, trace.replace('"enc":"coefpacked"', '"enc":"packed"'))
assert rc == 0 and "coefPackedPlaintexts" not in rel["noiseDerivation"]
assert all(doc[k] == rel[k] for k in doc if k != "noiseDerivation"), "relabelled extraction differs"
cases = [
    ("scalingFactorInt 3", trace.replace('"sf":1,"level":0,"enc":"coefpacked"', '"sf":3,"level":0,"enc":"coefpacked"'), "has scalingFactorInt 3"),
    ("scalingFactorInt not recorded", trace.replace('"sf":1,"level":0,"enc":"coefpacked"', '"level":0,"enc":"coefpacked"'), "scalingFactorInt unrecorded"),
    ("string encoding", trace.replace('"enc":"coefpacked"', '"enc":"string"'), "only packed and CoefPacked plaintexts are mapped"),
    ("encoding not recorded", trace.replace(',"enc":"coefpacked"', ''), "has encoding unrecorded"),
]
for name, tr, want in cases:
    assert tr != trace, name
    rc, e = extract(params, tr)
    if rc != 1 or want not in e.get("error", ""):
        sys.exit(f"{name}: exit {rc}, {str(e.get('error'))[:200]}")
# the BGV extractor keeps refusing CoefPacked (negative values stored as q - |v|; FLEXIBLE* scaling): its fixtures,
# each with the message recorded in its refusal.txt
bgv = sorted(x for x in os.listdir("tests/refused") if x.startswith("coefpk"))
assert len(bgv) >= 4, bgv
for x in bgv:
    r = subprocess.run([sys.executable, "-I", "openfhe/extract.py", "--params", f"tests/refused/{x}/params.json", "--trace",
                        f"tests/refused/{x}/trace.jsonl"], capture_output=True, text=True)
    # compared with the fixture's own refusal.txt (section 6b owns the message), not a fixed string
    want = open(f"tests/refused/{x}/refusal.txt").read().strip()
    assert r.returncode == 1 and json.loads(r.stdout)["error"].strip() == want, x
PY
}

s_9h() {
# 9h. the release bar for a technique whose multiplication slacks are PROVED and integer-only (BEHZ):
# on real OpenFHE runs with HYBRID and with BV key switching, the extracted program is CERTIFIED,
# the report says the slacks are proved (budget.slacksProved, pins stepOK_mul_behz / stepOK_square_behz)
# and, on the same run, the value cross-check against OpenFHE's own decryption passes.
nbar=0
for d in tests/values-bfv/n16_behz_*/; do
  n=$(basename "$d"); tmpj="$(mktemp)"
  python3 -I openfhe/extract_bfv.py --params "$d/params.json" --trace "$d/trace.jsonl" --artifact "$n" > "$tmpj"
  if grep -q '"op": "\(mul\|square\)"' "$tmpj"; then
    nbar=$((nbar+1))
    vcout="$(python3 -I openfhe/value_check_bfv.py "$tmpj" "$d/values.json")"
    grep -q "value_check_bfv: OK" <<<"$vcout" \
      && ok || bad "release bar (BEHZ) $n: value cross-check against OpenFHE's decryption"
    out="$("$FHE_CHECK" --no-suggest "$tmpj")"; rc=$?
    # the multiplication is proved, and so is OpenFHE's BEHZ decryption (Spec/DecryptBFVBEHZ.lean)
    grep -q "^VERDICT: CERTIFIED" <<<"$out" && grep -qF "Library decryption: PROVED" <<<"$out" && grep -qF "BEHZ ScaleAndRound" <<<"$out" && ok || bad "release bar (BEHZ) $n: not CERTIFIED with the BEHZ decryption proved (exit $rc)"
    grep -qF "Challenge.BFVMul.stepOK_mul_behz" <<<"$out" && ok || bad "release bar (BEHZ) $n: the report does not name stepOK_mul_behz"
    jb="$("$FHE_CHECK" --no-suggest --json "$tmpj")"
    python3 -I -c "
import json, sys
b = json.load(sys.stdin)['budget']
sys.exit(not (b['slacksProved'] is True and 'Challenge.BFVMul.stepOK_mul_behz' in b['mulPins']))" <<<"$jb" \
      && ok || bad "release bar (BEHZ) $n: budget.slacksProved is not true"
  fi
  rm -f "$tmpj"
done
ls -d tests/values-bfv/n16_behz_hybrid_* tests/values-bfv/n16_behz_bv_* >/dev/null 2>&1 && [ $nbar -ge 8 ] && ok || bad "release bar (BEHZ): fewer than 8 runs with a multiplication, or a key-switching technique is missing"
# the same at OpenFHE's secure default parameters (the value check of these runs is make_examples_bfv.sh / --live)
for n in openfhe_bfv_behz_bv_chain_d1 openfhe_bfv_behz_bv_chain_d2 openfhe_bfv_behz_hybrid_chain_d1 openfhe_bfv_behz_hybrid_rotsum_d2; do
  out="$("$FHE_CHECK" --no-suggest examples/$n.fhecheck.json)"
  grep -q "^VERDICT: CERTIFIED" <<<"$out" && grep -qF "Challenge.BFVMul.stepOK_mul_behz" <<<"$out" && grep -qF "Library decryption: PROVED" <<<"$out" && ok || bad "release bar (BEHZ) $n: not CERTIFIED with proved slacks and proved BEHZ decryption"
done
# 9i. --idealised changes only the floatTolerant declaration (and says so); recommend has no BFV mode
python3 -I - <<'PY' && ok || bad "extract_bfv.py --idealised changes more than the floatTolerant declaration"
import json, subprocess, sys
for n in ("openfhe_bfv_hps_hybrid_chain_d1", "openfhe_bfv_hpspoverqleveled_bv_chain_d2", "openfhe_bfv_behz_bv_chain_d1"):
    a = json.load(open(f"examples/{n}.fhecheck.json"))
    b = json.loads(subprocess.run([sys.executable, "-I", "openfhe/extract_bfv.py", "--idealised", "--params", f"examples/{n}.params.json",
                                   "--trace", f"examples/{n}.trace.jsonl", "--artifact", n], capture_output=True, text=True).stdout)
    behz = a["bfv"]["multiplication"]["technique"] == "BEHZ"
    assert b["bfv"]["multiplication"]["floatTolerant"] is False and b["source"]["idealised"] is True, n
    assert behz or "NOT what the library runs" in b["bfv"]["multiplication"]["source"], n
    for d in (a, b):
        d["source"].pop("idealised", None); d["bfv"]["multiplication"].pop("floatTolerant"); d["bfv"]["multiplication"].pop("source")
    assert a == b, n
PY
out="$("$FHE_CHECK" recommend examples/openfhe_bfv_hps_hybrid_chain_d2.fhecheck.json)"
grep -q "^RECOMMENDATION: UNSUPPORTED: fhe_check recommend has no BFV mode" <<<"$out" && grep -qF "FindLevelsToDrop" <<<"$out" \
  && ok || bad "recommend on a BFV file is not answered UNSUPPORTED"
if [ $LIVE = 1 ]; then
  echo "== 9j. live (BFV): re-run OpenFHE, re-extract, compare with the committed examples, value-check"
  live="$(mktemp -d)"
  if openfhe/make_examples_bfv.sh "$live" > "$live/log" 2>&1; then ok; else bad "make_examples_bfv.sh failed (see $live/log)"; fi
  for f in "$live"/examples/*.fhecheck.json "$live"/examples/*.params.json "$live"/examples/*.trace.jsonl; do
    cmp -s "$f" "examples/$(basename "$f")" && ok || bad "live BFV run differs from examples/$(basename "$f")"
  done
fi
# ====================================== BFV (end) ======================================
}

s_10() {
# The check stays linear in the program length (a regression guard: a locked closure-based
# helper called from the fast path made BFV quadratic once; 30,000 instructions then took 20 s).
# Budgets are generous for a loaded machine: an absolute ceiling at 30,000 instructions
# (measured 0.6 to 1.7 s) and a growth ratio from 15,000 to 60,000 instructions (linear: about 4;
# quadratic: about 16), each time the faster of two runs.
echo "== 10. speed guard: linear growth at 15,000 / 30,000 / 60,000 instructions (BGV and BFV; table and profile mode)"
local g tmp; g="$ROOT/harness/eval/analyzer-speed/gen.py"; tmp="$(mktemp -d)"
best() { # FILE -> the smaller wall time in ms of two runs
  local a b s e
  for k in 1 2; do
    s=$(date +%s%N); "$FHE_CHECK" --no-suggest --max-instructions 0 "$1" >/dev/null 2>&1; e=$(date +%s%N)
    if [ $k = 1 ]; then a=$(( (e - s) / 1000000 )); else b=$(( (e - s) / 1000000 )); fi
  done
  echo $(( a < b ? a : b ))
}
for spec in "BGV:examples/openfhe_depth8_q55_fixedmanual.fhecheck.json:mixed" \
            "BFV:examples/openfhe_bfv_default_chain_d3.fhecheck.json:mulrelin" \
            "BFV:examples/openfhe_bfv_default_chain_d3.fhecheck.json:mixed"; do
  IFS=: read -r sch base kind <<<"$spec"
  for n in 15000 30000 60000; do python3 -I "$g" "$base" "$kind" $n "$tmp/$n.json" || bad "gen.py $kind $n"; done
  t15=$(best "$tmp/15000.json"); t30=$(best "$tmp/30000.json"); t60=$(best "$tmp/60000.json")
  echo "  $sch $kind: 15000 ${t15} ms, 30000 ${t30} ms, 60000 ${t60} ms"
  [ "$t30" -le 15000 ] && ok || bad "$sch $kind: 30,000 instructions took $t30 ms (budget 15000 ms)"
  # ratio, with 200 ms of slack on the small run for start-up noise
  [ $(( t60 * 10 )) -le $(( (t15 + 200) * 90 )) ] && ok || bad "$sch $kind: 60,000 instructions took $t60 ms, 15,000 took $t15 ms: growth above 9x for 4x the length (not linear)"
done
# the decoder's validation of $.scaling.adjustments (a real OpenFHE extraction declares one for about
# every ninth instruction; gen.py writes none unless given --adjustments): it was quadratic (a list
# index and a list search per adjustment; 2.18M instructions took 1,413 s to decode). Constant
# multiplications only, every one an adjustment, 20,000 / 40,000 / 80,000 instructions: linear about
# 1 s at 80,000 (the verdict is NOT CERTIFIED, exit 1: only the time is read); the quadratic decoder took 11 s.
for n in 20000 40000 80000; do python3 -I "$g" examples/openfhe_depth8_q55_fixedmanual.fhecheck.json mulconst $n "$tmp/m$n.json" --adjustments || bad "gen.py mulconst $n"; done
t20=$(best "$tmp/m20000.json"); t40=$(best "$tmp/m40000.json"); t80=$(best "$tmp/m80000.json")
echo "  BGV scale adjustments: 20000 ${t20} ms, 40000 ${t40} ms, 80000 ${t80} ms"
[ "$t80" -le 6000 ] && ok || bad "BGV scale adjustments: 80,000 instructions took $t80 ms (budget 6000 ms): the decode of \$.scaling.adjustments is not linear"
[ $(( t80 * 10 )) -le $(( (t20 + 200) * 90 )) ] && ok || bad "BGV scale adjustments: 80,000 instructions took $t80 ms, 20,000 took $t20 ms: growth above 9x for 4x the length (not linear)"
# profile mode (--profile): BGV at the profile --emit-profile writes for the program, and BFV at a
# per-instruction profile (the emitted one) and at a uniform one; same budgets
bestp() { # PROFILE FILE -> the smaller wall time in ms of two runs
  local a b s e
  for k in 1 2; do
    s=$(date +%s%N); "$FHE_CHECK" --max-instructions 0 --profile "$1" "$2" >/dev/null 2>&1; e=$(date +%s%N)
    if [ $k = 1 ]; then a=$(( (e - s) / 1000000 )); else b=$(( (e - s) / 1000000 )); fi
  done
  echo $(( a < b ? a : b ))
}
printf '{"format":"fhe-check-profile/v1","scheme":"BFV","uniform":{"keySwitch":"100000","modSwitch":"10000","mulLift":"10000","mulRound":"1000000000000","plainAdd":"0"}}' >"$tmp/uniform.json"
for spec in "BGV:examples/openfhe_depth8_q55_fixedmanual.fhecheck.json:mixed:emit" \
            "BFV:examples/openfhe_bfv_default_chain_d3.fhecheck.json:mixed:emit" \
            "BFV:examples/openfhe_bfv_default_chain_d3.fhecheck.json:mixed:uniform"; do
  IFS=: read -r sch base kind prof <<<"$spec"
  for n in 15000 30000 60000; do
    python3 -I "$g" "$base" "$kind" $n "$tmp/$n.json" || bad "gen.py $kind $n"
    if [ "$prof" = emit ]; then "$FHE_CHECK" --emit-profile "$tmp/$n.json" >"$tmp/p$n.json" || bad "--emit-profile $n"
    else cp "$tmp/uniform.json" "$tmp/p$n.json"; fi
  done
  t15=$(bestp "$tmp/p15000.json" "$tmp/15000.json"); t30=$(bestp "$tmp/p30000.json" "$tmp/30000.json"); t60=$(bestp "$tmp/p60000.json" "$tmp/60000.json")
  echo "  profile mode $sch $kind ($prof profile): 15000 ${t15} ms, 30000 ${t30} ms, 60000 ${t60} ms"
  [ "$t30" -le 15000 ] && ok || bad "profile mode $sch $kind $prof: 30,000 instructions took $t30 ms (budget 15000 ms)"
  [ $(( t60 * 10 )) -le $(( (t15 + 200) * 90 )) ] && ok || bad "profile mode $sch $kind $prof: 60,000 instructions took $t60 ms, 15,000 took $t15 ms: growth above 9x for 4x the length (not linear)"
done
rm -rf "$tmp"
}

s_11() {
# Profile mode (fhe_check --profile FILE, --emit-profile; FHE/Check/Profile.lean): round trip of the
# emitted profile on every table-certified file (same bounds; BFV: the same per-instruction
# budget), a larger budget flipping the verdict at the expected instruction, certified but not
# covered, the Lattigo-shaped profile, malformed profiles and usage errors (tests/profile/check_profile.py).
echo "== 11. profile mode (--profile, --emit-profile; Challenge.Fast.Profile)"
local line
while IFS= read -r line; do
  case "$line" in
    "ok "*) ok ;;
    *) bad "$line" ;;
  esac
done < <(python3 -I tests/profile/check_profile.py "$FHE_CHECK" 2>&1 || echo "FAIL check_profile.py exited with an error")
}

run_sections s_1 s_2 s_2b s_2c s_2d s_2e s_3 s_4 s_5 s_6 s_6c s_6b s_6d s_8a s_8b s_9a s_9d s_9f s_9g s_9h s_10 s_11
echo "passed $pass, failed $fail"
[ $fail = 0 ]
