# The proved reference implementation (`provenfhe_ref`)

`provenfhe_ref` runs leveled BGV and BFV end to end at N = 2^13: key generation (public key,
relinearization keys, rotation keys), public-key encryption, homomorphic evaluation with
relinearization, key switching after an automorphism, modulus switching and plaintext operations,
and textbook decryption. Each of these steps is computed by a Lean function that is proved
equal, on all inputs, to the locked or trusted definition that the correctness theorems are
about. The proofs are kernel-checked, use no `sorry` and no `native_decide`, and depend only on
the axioms `propext`, `Classical.choice` and `Quot.sound`.

This is a reference implementation to compare against. It is not a library to deploy.

## What runs, and which theorem covers each step

An array `arr : Array ℤ` stands for the trusted polynomial `FHE.Pin.ofArr arr`, whose coefficient
`i` is `arr[i]!`. Every polynomial is `ofArr` of some array (`FHE.Pin.ofArr_toArr`), so an equality
stated through `ofArr` covers every input of the trusted function. The functions return the same
integers as the definitions: no reduction modulo `Q` is added, and none is removed.

| step | executable function | equal to (locked/trusted) | equality theorem |
|---|---|---|---|
| negacyclic product | `FHE.Ref.mulA` (Kronecker substitution, one big-integer product) | `*` of `Spec.NPoly` | `ofArr_mulA` (from `FHE.Pin.Kron.mulNeg_eq`) |
| automorphism | `FHE.Ref.autoA` (linear scatter) | `Spec.NPoly.automorph` | `ofArr_autoA` (from `Kron.autoL_eq`) |
| hybrid key switch of one component | `FHE.Ref.ksA` | `Challenge.Realize.ksOpenFHE` | `ksA_eq` |
| BGV relinearization / key switch | `relinA`, `keySwitchA` | `relinOpenFHE`, `keySwitchOpenFHE` | `wC_relinA`, `wC_keySwitchA` |
| BFV key switch (BV and HYBRID branches) | `ksBFVA`, `relinBFVA`, `keySwitchBFVA` | `Challenge.RealizeBFV.ksBFV`, `relinBFV`, `keySwitchBFV` | `ksBFVA_eq`, `wC_relinBFVA`, `wC_keySwitchBFVA` |
| BGV evaluator | `FHE.Ref.ksEvalA` | `Challenge.IndCpaDProfile.ksEval` | `ksEvalA_eq` |
| BFV evaluator | `FHE.Ref.bfvEvalA` | `Challenge.IndCpaDLM.interpEval` of `bfvStepFn` | `bfvEvalA_eq` |
| BGV key generation | `FHE.Ref.keyGenA` | `Challenge.IndCpaDProfile.keyGen` | `keyGenA_eq` |
| BFV key generation | `FHE.Ref.bfvKeyGenA` | `Challenge.IndCpaDLM.bfvKeyGen` | `bfvKeyGenA_eq` |
| BGV encryption | `FHE.Ref.encA` | `.enc` of `bgvKSData` (`Spec.Encrypt.encrypt` of `liftMsg m`) | `encBGVA_eq`, `encA_eq` |
| BFV encryption | `FHE.Ref.encBFVA` | `.enc` of `bfvKSData` (`Spec.EncryptBFV.encryptBFV`) | `encBFVA_eq`, `encBFVA_spec` |
| BGV decryption | `FHE.Ref.decBGVA` | `AbsScheme.decBGV` (textbook) | `decBGVA_eq` |
| BFV decryption | `FHE.Ref.decBFVA` | `AbsScheme.decBFV` (textbook) | `decBFVA_eq` |
| what a circuit computes | `FHE.Ref.semA` | `AbsScheme.sem` | `semA_eq` |
| key tables computed once | `FHE.Ref.memoAt` | the key function itself | `memoAt_eq` |

The two evaluator theorems, verbatim:

```lean
theorem ksEvalA_eq (D : AbsScheme) (lay : KSLayout) (rk : List (Array ℤ × Array ℤ))
    (gk : ℕ → List (Array ℤ × Array ℤ)) (C : D.Circ) (cs : List (ℕ × List (Array ℤ))) :
    wIn D.P.src.N (ksEvalA D lay rk gk C cs) =
      ksEval D lay (wK D.P.src.N rk) (fun g => wK D.P.src.N (gk g)) C (wIn D.P.src.N cs)

theorem bfvEvalA_eq (D : AbsScheme) (lay : KSLayout)
    (rkF : D.PK → ℕ → List (IntPoly D.P.src.N × IntPoly D.P.src.N))
    (gkF : D.PK → ℕ → ℕ → List (IntPoly D.P.src.N × IntPoly D.P.src.N)) (pk : D.PK)
    (rk : ℕ → List (Array ℤ × Array ℤ)) (gk : ℕ → ℕ → List (Array ℤ × Array ℤ))
    (hrk : rkF pk = fun ℓ => wK D.P.src.N (rk ℓ)) (hgk : gkF pk = fun g ℓ => wK D.P.src.N (gk g ℓ))
    (C : D.Circ) (cs : List (ℕ × List (Array ℤ))) :
    wIn D.P.src.N (bfvEvalA D lay rk gk C cs) =
      interpEval D (bfvStepFn D lay rkF gkF) pk C (wIn D.P.src.N cs)
```

Both cover every instruction of the source language: `add`, `sub`, `mul`, `square`, `mulConst`,
`copy`, `toEval`, `toCoeff`, `dropLimbs`, `automorph`, `addPlain`, `subPlain`, `mulPlain`,
`relin`, `keySwitch` and `modSwitch`. They hold for every abstract scheme `D`, layout, key,
circuit and input, not only at the parameters run here.

Each run then rests on these locked theorems:

- **BGV at `bgvKSSeal`.** `correct_ksEval_bgvKSSeal` (perfect correctness of `ksEval` on
  `ksClass`), `keyGen_keysOK` (generated keys are good) and `encOK_bgvKSData`.
- **BFV at `sealBFV`.** `correct_lm_bfvSeal` (fresh-only perfect correctness of `interpEval` of
  `bfvStepFn` on `admBFVSeal`) and `bfvKeyGen_keysOK`.

The driver checks the hypotheses of these theorems on the sampled data before using it:

- the secret within `secretBound`;
- the public-key error within 21;
- every key error `eⱼ` with `t·‖eⱼ‖∞ ≤ keyNoise` (BGV) or `‖eⱼ‖∞ ≤ keyNoise` (BFV), and
  `2·… < Q_ℓ·P`;
- `GoodE` for `u`, `e₁`, `e₂`;
- class membership.

**Class membership.** At `LOGN = 13` the driver's scheme data, class predicates and parameters are, by kernel-checked `example … := rfl` in `ProvenfheRef.lean`, exactly `bgvKSSealData`, `bfvSealData`, `admSeal` (= `ksClass … bgvKSSealProfile`), `admBFVSeal`, `bgvKSSeal` and `sealBFV`. Before evaluating, the driver calls the locked class predicate:
`ksClass … [5] …` for BGV, `bfvClass … [5] …` (= `admBFVSeal`) for BFV, and `admLM` for the two
stages. A circuit the predicate rejects is refused and never evaluated.

The circuits run (N = 2^13; "kernel" means the class verdict is a kernel-checked locked theorem,
"compiled" means it is decided only by the compiled predicate at run time):

| scheme | circuit | class verdict | correctness statement |
|---|---|---|---|
| BGV | `bgvKSSealCirc`: mul, relin, automorph 5, keySwitch, modSwitch, addPlain | accept, kernel (`ksClass_bgvKSSeal`) | `correct_ksEval_bgvKSSeal` |
| BGV | the same program with a random plaintext constant | accept, compiled | `correct_ksEval_bgvKSSeal` |
| BGV | two-stage `lmStage1` (mul, relin), then `lmStage2` (automorph 5, keySwitch, modSwitch) on stage 1's output | accept, kernel (`lm_two_stage_kernel`) | see below |
| BGV | `bgvKSSealCirc` with rotation keys for g = 3 only | reject, the `#guard` in `ProfileBGVKS` | refused |
| BGV | the three rejections of `lm_reject_kernel` | reject, kernel | refused |
| BFV | `bfvStage1` and `bfvStage2` inlined into one program | accept, compiled | `correct_lm_bfvSeal` |
| BFV | the inlined program + addPlain + mulPlain (random constants) | accept, compiled | `correct_lm_bfvSeal` |
| BFV | two-stage `bfvStage1`, then `bfvStage2` on stage 1's output | accept, kernel (`lm_two_stage_bfv_kernel`) | see below |
| BFV | rotation keys for g = 3 only; the three `lm_reject_kernel` analogues | reject, compiled | refused |

**The two-stage runs.** Stage 2 is evaluated on the output of stage 1, as the oracle of
`Spec.IndCpaDLM.gameLM` does. No locked theorem states the decryption of that result directly.
It is covered inside the reduction `gameLM_eq_gameCPA`, through the interpreter's locality
(`InterpOK`) and the correctness of the inlined program.

**Checks.** For every accepted circuit, every output is decrypted and compared, coefficient by
coefficient, with `sem` on the plaintexts. A control on the first circuit checks that the
comparison can fail: the decryption must differ from `sem` evaluated on a perturbed input.

## Measurements

Machine: AMD EPYC 7742 (x86_64, Linux), shared with other jobs (maxima are inflated by them); single-threaded; times are wall
clock per operation, mean over 20 seeds (seeds 1–20). The memory figure is the maximum resident
set of the whole process (`/usr/bin/time -v`). All runs PASS.

**N = 2^13** (`bgvKSSeal`, `sealBFV`; the parameters of the locked concrete theorems), 20 seeds,
181/181 PASS lines per scheme (4 accepted circuits + 1 control + 4 refusals per seed), 0 FAIL:

| phase (ms, mean / max) | BGV | BFV |
|---|---|---|
| key generation: public key (+ BGV top-level relinearization keys) | 280 / 490 | 59 / 63 |
| relinearization keys, BFV 4 levels | (in the row above) | 461 / 490 |
| rotation keys g = 5 (BGV top level; BFV 4 levels) | 212 / 369 | 458 / 479 |
| encryption, one ciphertext | 108 / 178 | 104 / 107 |
| class check (compiled locked predicate) | 0.7 / 1.2 | 0.6 / 0.6 |
| eval: BGV `bgvKSSealCirc` / BFV inlined stages (mul, relin, automorph, keySwitch, modSwitch[, addPlain]) | 2157 / 3680 | 1745 / 1789 |
| eval: same + plaintext constant(s) (BFV: + addPlain + mulPlain) | 2177 / 3763 | 1852 / 1904 |
| eval: two-stage, stage 1 (mul, relin) | 1147 / 1937 | 1032 / 1076 |
| eval: two-stage, stage 2 on stage 1's output (automorph, keySwitch, modSwitch) | 1003 / 1708 | 716 / 740 |
| textbook decryption, one output | 107 / 181 | 106 / 116 |
| `sem` (message level, fast form) | 64 / 127 | 45 / 94 |
| whole run, 20 seeds (wall clock) | 165 s | 153 s |
| maximum resident set | 117.5 MB | 134.4 MB |

**N = 2^12 and N = 2^14** (the same moduli with `N := 2^LOGN`; NOT the parameters of the locked
concrete theorems: the generic theorems `correct_ksEval`, `correct_bfvEval`, `keyGen_keysOK`,
`bfvKeyGen_keysOK`, `encOK_bgvKSData`, `encOK_bfvKSData` apply, and their closed side conditions
and every class verdict, including those of the example circuits, are decided by compiled code
only). 20 seeds, both schemes in one process each, 361/361 PASS lines, 0 FAIL:

| phase (ms, mean) | BGV 2^12 | BFV 2^12 | BGV 2^14 | BFV 2^14 |
|---|---|---|---|---|
| keygen pk (+ BGV relin keys) | 121 | 28 | 524 | 118 |
| BFV relin keys, 4 levels | – | 224 | – | 936 |
| rotation keys g = 5 | 92 | 220 | 397 | 928 |
| encryption, one | 47 | 50 | 198 | 211 |
| eval, main circuit | 904 | 845 | 3818 | 3564 |
| eval, with plaintext operations | 903 | 892 | 3799 | 3795 |
| eval, two-stage stage 1 / stage 2 | 482 / 423 | 497 / 347 | 2042 / 1745 | 2130 / 1448 |
| decryption, one output | 52 | 53 | 179 | 201 |
| whole run, 20 seeds, both schemes | 145 s | | 602 s | |
| maximum resident set | 107.5 MB | | 181.9 MB | |

**Where the time goes.** Per instruction of the BFV inlined program (`provenfhe_ref profile`):

| instruction | time |
|---|---|
| mul | ≈ 0.33 s |
| relin | ≈ 0.70 s |
| automorph | ≈ 2 ms |
| keySwitch | ≈ 0.70 s |
| modSwitch | ≈ 10 ms |

Key switching dominates. A switch does ModUp of each of the 4 digits and the per-coefficient CRT
lifts (`fbc`), computed with generic `ZMod m` arithmetic; then 8 big-integer Kronecker products
of the ~44-bit digits with the ~220-bit keys; then ModDown. Nothing runs in residue-number-system
form and there is no NTT. A faster form would need a proved RNS/NTT key switch with integer
outputs equal to these definitions. The staged RNS key switch already in `FHE/Pin/AlgoLocked.lean`
is proved equal only limb for limb, i.e. modulo `Q_ℓ`, not as integers.

## What is NOT claimed

- **Not constant-time and not side-channel hardened.** Big-integer arithmetic (GMP through the
  Lean runtime) is data-dependent in time and memory.
- **Not optimised.** There is no NTT and no RNS. Products use Kronecker substitution on unreduced
  integer representatives, exactly the integers the definitions compute; ciphertext
  coefficients are not reduced modulo `Q`, so they grow, e.g. to a few hundred bits after a
  product.
- **Decryption is textbook** (`AbsScheme.decBGV`, `decBFV`), not a library's decryption routine.
- **Evaluation keys are as in the theorems.**
  - BGV: one top-level key set for relinearization and one per Galois element, gadget keys
    `(t·eⱼ − aⱼ·s + gⱼ·T(s), aⱼ)`.
  - BFV: one key set per level (relinearization, and rotation per Galois element and level),
    `(eⱼ − aⱼ·s + gⱼ·T(s), aⱼ)`.
  - Rotation is the automorphism followed by the key switch with keys for `σ_g(s)`. This is the
    convention of the theorems, not a library's stored-key rotation.
- **The pseudo-random generator is a test harness.** It is a seeded splitmix64 written in the
  driver, used to pick a secret, errors in `[−21, 21]`, ternary `u`, uniform parts in `[0, Q)` or
  `[0, Q_ℓ·P)`, and messages. The theorems hold for every key and every randomness within the
  declared bounds, and the driver checks those bounds. Nothing here says anything about the
  distribution of keys or errors, or about security.
- **The compiler and runtime are trusted.** The equality theorems are about the Lean definitions.
  That the binary computes those definitions trusts the Lean compiler, its runtime and GMP, as
  for `fhe_check` and `openfhe_pin`.
- **Not all class verdicts are kernel-checked.** Verdicts marked "compiled" above are decided
  by compiled evaluation of the locked predicate at run time.
- **The driver is not proved.** Sampling, timing, the key tables and the coefficient comparison
  are untrusted glue. The key tables are filled by `memoAt` from the key function itself, which
  `memoAt_eq` proves changes nothing.
- **The equality theorems are in the gate's scope, but are not locked statements.** `FHE.lean`
  imports `FHE.Ref.BFV` (which imports the other `FHE.Ref` modules), so `lake build FHE` builds
  them and the gate's step 5 puts them under the same axiom scan and kernel replay as the rest of
  the FHE library; the gate also runs one seed of `provenfhe_ref all` at N = 2^13 as a suite
  (`harness/ref/difftest.sh`). They are not locked because `FHE.Pin.Kron` and `FHE.Pin.Force`
  import `Validation.*`: a Challenge statement about them would have to go through `FHE.Holes`,
  whose import closure must not include `Validation`.
- **Not covered:**
  - the exact-only evaluator `exactEval`. Its instructions are covered as part of `ksEvalA`, but
    `exactEval` itself is not restated.
  - the BFV library transcription `runLibrary` / `textEval`, and `rotateOpenFHE161` /
    `rotateBFV`. They are not the evaluators of the correctness theorems.
  - the IND-CPA-D game itself.

## How to run

```sh
lake build provenfhe_ref
.lake/build/bin/provenfhe_ref all 20 1 13   # [bgv|bfv|all] SEEDS FIRST_SEED LOGN
.lake/build/bin/provenfhe_ref profile       # per-instruction time, BFV
harness/ref/run.sh 2                        # build, 2 seeds of each scheme, summary; exit code = verdict
```

The output has one line per circuit with eval/decrypt/sem times and PASS/FAIL, one line per
negative control ("refused by the class, not evaluated: PASS"), and a summary of mean and max per
phase. The exit code is 1 on any mismatch, any violated bound, or any unexpected class verdict.

With `LOGN ≠ 13` the moduli are the same and `N := 2^LOGN`. These are not the parameters of the
locked concrete theorems. The generic theorems (`correct_ksEval`, `correct_bfvEval`,
`keyGen_keysOK`, `bfvKeyGen_keysOK`, `encOK_*`) still apply, but their closed side conditions and
the class verdicts are decided by compiled code, not by the kernel.

Source: `FHE/Ref/Arr.lean`, `FHE/Ref/KeySwitch.lean`, `FHE/Ref/Run.lean`, `FHE/Ref/BGV.lean`,
`FHE/Ref/BFV.lean`, `ProvenfheRef.lean`, `harness/ref/run.sh`.
