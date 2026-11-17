# ProvenFHE

IND-CPA-D attacks recover BFV keys from a library whose noise estimates hold only for typical
inputs, and their authors recommend worst-case noise bounds instead. ProvenFHE makes that
countermeasure checkable for RNS BGV and BFV. `fhe_check` decides whether a program decrypts
correctly in the worst case, and its CERTIFIED verdict has a soundness theorem, machine-checked in
Lean 4, that covers the RNS algorithms libraries run. On the circuits it accepts, IND-CPA-D reduces
to IND-CPA, for BGV and BFV, in the fresh-only game and with evaluation on earlier results. The
cost of certified parameters is measured on OpenFHE. A reference implementation is proved to
compute the definitions the theorems are about; existing libraries (OpenFHE, Lattigo) are tested
instances, not verified ones.

## Why it matters

- **Wrong decryptions are silent.** Every BGV or BFV ciphertext carries noise that grows with each
  operation. Past a threshold fixed by the parameters, decryption returns a wrong plaintext, and
  nothing in the output says so.
- **Average-case estimates are an attack surface.** Libraries choose parameters with noise
  estimates that hold for typical inputs. In the IND-CPA-D model the adversary chooses the inputs
  and sees decryptions, and a wrong decryption leaks the key: Cheon et al. (CCS 2024, ePrint
  2024/127) and Choe, Kang and Stehlé (CCS 2026, ePrint 2026/2546) recover BFV keys in OpenFHE.
  The latter recommend that "noise-analysis frameworks should adopt worst-case error bounds rather
  than average-case behavior".
- **Libraries do not compute in the textbook ring.** They split the modulus into residues modulo
  small primes (RNS), switch bases, and compute two sums of the HPS-family BFV multiplication in
  binary64 floating point. A worst-case bound that can be trusted has to cover that arithmetic.
  This one does, and the repository measures what certified parameters cost on OpenFHE.

## What is proved

681 locked statements (theorem statements fixed and hash-locked in `Challenge/` before their
proofs, proved in `Validation/`) are proved and replayed through the Lean kernel. The gate
classifies each one: 300 substantive theorems, 146 realisability witnesses, 56 discrimination
statements, 40 closed computations, 28 true by unfolding and 111 instances of another statement
(`build/check-spec/pin-classes.txt`, rule in `scripts/PinStatus.lean`). The headline statements,
keyed on the paper's theorems and the groups H1-H4 of `docs/TRUSTED-CORE.md`:

| Paper | H | Statements (namespace `Challenge.` omitted; file under `Challenge/`) | What it says |
|---|---|---|---|
| Thm `sound` | H1 | `Profile.certifyProfile?_sound` (`Profile.lean:58`), `Profile.certifyBFVProfile?_sound` (`:69`) | accepted at any declared budget ⇒ every output of every in-budget run decrypts correctly |
| default mode (what `fhe_check` prints) | H2 | `Certify.certify?_sound` (`Certify.lean:311`), `certify?_decrypts` (`:321`), `worst_certified` (`:333`); `CertifyBFV.certifyBFV?_sound` (`CertifyBFV.lean:184`), `certifyBFV?_decrypts` (`:190`) | the same at the budget computed from the parameters |
| Thm `cover` | - | `Profile.coversBFV?_mul`, `_square`, `_modSwitch` (`Profile.lean:151,173,226`); `ProfileNamed.coversBFVAt?_relinBFV`, `coversBGV?_relinOpenFHE` (`Profile/Named.lean:124,160`); `Realize.relinOpenFHE_stepOK` (`Realize.lean:56`); `RealizeBFV.relinBFV_stepOK` (`RealizeBFV.lean:69`) | the named RNS algorithms meet the budget |
| Thm `mulapprox`, `hpsfloat` | - | `BFVMul.stepOK_mul_approx`, `stepOK_square_approx` (`BFVMul.lean:56,78`); `BFVMul.stepOK_mul_hps_tol`, `stepOK_mul_hps_float` (`BFVMul/Float.lean:371,481`) and the P-over-Q, leveled and squaring forms | approximate and HPS-family products, binary64 sums included, meet the contract |
| BEHZ; MSB transfer | H4 | `BFVMul.stepOK_mul_behz` (`BFVMul.lean:271`); `MSB.certifyProfile?_sound_msb` (`MSB.lean:257`) | BEHZ multiplication meets the contract; profile soundness for BGV in most-significant-bit (MSB) form |
| Thm `indcpad` | H3 | `IndCpaDProfile.correct_bfv`, `bfv_prob_eq` (`IndCpaD/Profile.lean:93,103`), `correct_bgv`, `bgv_prob_eq` (`IndCpaD/ProfileBGV.lean:90,97`), `bfv_adv_le`, `bgv_adv_le` (`IndCpaD/ProfileAdv.lean:41,63`); `IndCpaDLM.gameLM_eq_gameCPA`, `advLM_le` (`IndCpaD/LM.lean:92,139`); not H3 roots: the BFV and BGV compositions `advLM_le_bfv`, `advLM_le_bgv` (`IndCpaD/LMCompose.lean:98,181`) | IND-CPA-D advantage ≤ IND-CPA advantage + 2·Pr[bad] on the certified class; fresh-only game and the game with evaluation on earlier results |
| Thm `librun` | - | `CertifyBFV.certifyBFV?_library_run`, `certifyBFV?_library_decrypts` (`CertifyBFV/Library.lean:230,246`) | the transcribed OpenFHE BFV execution of an accepted program is an in-budget run |
| reference implementation (not locked) | - | `FHE.Ref.ksEvalA_eq` (`FHE/Ref/BGV.lean:138`), `FHE.Ref.bfvEvalA_eq` (`FHE/Ref/BFV.lean:212`) | `provenfhe_ref` computes the definitions |

The 681 statements by group (files under `Challenge/`):

| Group | Files | Statements |
|---|---|---|
| Trusted-definition pins | `Ring`, `Scheme`, `Params`, `Source`, `Trace`, `Decrypt`, `Corpus` | 73 |
| Budgets and realisability | `Budget*`, `Realize*`, `Word`, `BFV`, `BFV/*`, `BFVMul*` | 125 |
| The library's BFV decryption | `BFVDecrypt*` | 32 |
| Decisions and fast paths | `Certify*`, `CertifyBFV*`, `Scaling`, `FreshNoise*`, `BFVEncrypt`, `Fast*`, `Headline*` | 149 |
| Profiles and other libraries | `Profile*`, `Families/*`, `MSB*`, `Instances/*` | 118 |
| Security | `IndCpaD`, `IndCpaD/*` except `Sanity*` | 124 |
| Sanity and diligence | `Sanity/*`, `IndCpaD/Sanity*` | 60 |

`Challenge/IndCpaD/` holds six namespaces: `Challenge.IndCpaD` (`IndCpaD.lean`, `Defs`, `Generic`,
`Textbook`: the fresh-only game and OpenFHE-shaped instances), `Challenge.IndCpaDProfile`
(`Profile*`: the library-free BFV and BGV scheme), `Challenge.IndCpaDLM` (`LM*`: the game with
evaluation on earlier results), `Challenge.IndCpaDSanity` (`Sanity*`), `Challenge.IndCpaDBad`
(`BadEvent`) and `Challenge.IndCpaDAttack` (`Attack`). "Profile" means two things: the
certificate at a declared budget (`Challenge.Profile`) and the security scheme over that class
(`Challenge.IndCpaDProfile`). `sealBFV`, `bgvSeal` and `bgvKSSeal` name variants of one
parameter set (N = 2^13, t = 65537, a 174-bit modulus); the names are historical, not a claim
about any library's defaults (`Challenge/BFV.lean:92`). `docs/SPEC.md` section 3 describes each
group.

## Check it yourself

```
./verify.sh        # dependencies, the strict gate, the fhe_check tests, a summary; exit 0 iff all pass
```

Prerequisites: [elan](https://github.com/leanprover/elan) (the repository pins Lean 4.35.0), git,
python3 3.10 or later, curl, tar and xz, and bubblewrap (`bwrap`) for the sandboxed, strict gate
(Linux). `./verify.sh` fetches Mathlib's prebuilt cache; `VERIFY_FROM_SOURCE=1 ./verify.sh` builds
the needed Mathlib modules from source instead (not yet tested end to end).

Cost, as measured: from scratch and strict, `./verify.sh` took 817 s on a 128-core machine that was
otherwise idle when the run started, with 7.2 GB peak memory in its largest process (the kernel
replay). The checkout with all packages and build outputs occupies about 8.4 GB, and the Mathlib
cache download is 453 MB. On a hosted CI runner (4 vCPU, 16 GB), a quick-mode run (mutation
suites skipped) completed in 1 h 2 min. Nothing was measured on a laptop. The header of
`verify.sh` lists its other switches.

`scripts/check-spec.sh` is the gate (`STRICT=1` for release mode). Its eight steps:

1. the locked files match `trust/LOCK`;
2. no `sorry`, axiom, `native_decide` or similar in `Spec/`;
3. a text audit of the definition holes (`FHE/Holes.lean` and its imports);
4. a sandboxed two-phase build of `Spec`, `Challenge`, `Validation` and the `FHE` library;
5. every pin proved with the identical statement from the three standard axioms, its closure and
   the whole `FHE` library replayed through the kernel in a fresh environment;
6. the differential suites: trusted definitions and proved algorithms on recorded OpenFHE runs
   (`harness/openfhe-pin`, `harness/bfv-float`), the `fhe_check` frontend tests
   (`harness/frontend`) and the reference implementation (`harness/ref`);
7. mutation tests: wrong copies of trusted operations must be caught by step 6;
8. a lock re-check. Output goes to `build/check-spec/`.

## Use it

**`fhe_check`.** It reads a program with its parameters (BGV and BFV recorded from OpenFHE, BGV
compiled by Google HEIR, or a hand-written file) and answers CERTIFIED, NOT CERTIFIED or
UNSUPPORTED. The default mode is worst case; `--kappa K` makes only the noise of fresh
encryptions probabilistic (failure probability at most 2^-K per execution). On a refusal it
suggests the smallest change, and `fhe_check recommend` searches for parameters that certify
(BGV). `--profile` checks against a declared budget for any implementation. Build it with
`lake exe cache get && lake build fhe_check`; `docs/QUICKSTART.md` has the three tested ways in
(no library, an unmodified OpenFHE program, a HEIR program) and `harness/frontend/README.md` the
full manual.

**`provenfhe_ref`.** Leveled BGV and BFV at N = 2^13, key generation through decryption, every step
computed by a function proved equal to the definition the theorems are about. It is unoptimised
and not constant-time: a reference to compare against, not a library to deploy.
`lake build provenfhe_ref && .lake/build/bin/provenfhe_ref all 20 1 13`; see
`docs/REFERENCE-IMPLEMENTATION.md`.

## Evidence about libraries

Testing on recorded runs, not proof:

- **Conformance with OpenFHE v1.6.1.** The trusted definitions and the proved algorithms reproduce
  263 BGV and 241 BFV recorded cases at N = 16 and 64 bit for bit (in the gate), and 80 of 82
  executions in contexts OpenFHE chose at 128-bit security, N = 8192 to 32768, run outside the gate
  (two 11-limb BFV cases did not finish; a two-case sample is gated): `harness/openfhe-pin`, `harness/openfhe-pin/realsize`,
  `harness/bfv-float`. One compiler and platform (GCC 13.3.0, x86-64).
- **Lattigo v6.2.0** BGV is a second instance of the same interface: its budget is a function of its
  parameters, coverage is proved at its 128-bit `LogN = 14` example, and its recorded outputs at
  small ring dimension stay within it (`harness/lattigo-pin`).
- **What a default user sees.** On a multiplication chain at the parameters OpenFHE generates, in
  the worst case, BGV FIXEDMANUAL is certified at depth 1 only and the automatic modes at no depth from 1 to 8
  (`harness/eval/openfhe-upstream`); BFV by depth: `harness/frontend/levelbfv/depth_table.md`. HEIR's
  default noise model on `mult_dep_8` is 51.05 bits over the worst-case bound.
- **The cost of certified parameters.** A setting of OpenFHE's public parameters that the checker
  accepts exists in all but one of 384 benchmark cells; the cheapest one, traced, certified and
  timed against the default (`harness/eval/frontier`).
- **The Choe-Kang-Stehle attack circuits**, re-implemented from their paper and a reading of their
  code (no key recovery). For the five parameter sets of the plaintext-ciphertext attack the checker
  certifies at most 6, 5, 4, 4, 5 of the 8, 7, 6, 6, 7 products, and the full depth with one more
  60-bit prime; for the squaring attack it certifies 0 of 35, 31 of 45 and 32 of 48 squarings
  (t = 786433, 1153, 257; at t = 786433 the margin under which the library's floating-point
  decryption is proved correct fails, a limit of the proof's reach, not a statement about the
  library). `harness/eval/cks26`; the squaring-attack runs at t = 786433 (cases and summaries) are
  not in this release.
- **Real programs.** Two third-party OpenFHE BGV programs, a 2,183,887-instruction integer division
  and a 59,894-instruction comparison, are certified after raising their multiplicative depth from
  10 to 11, and a 6,651-instruction sign function as written, at the toy N = 2 and t = 257 they fix
  (`harness/eval/analyzer-speed/real`).

## What is not claimed

- No library is verified. That OpenFHE, HEIR or Lattigo meets the per-operation contracts is an
  assumption, tested on recorded runs; the constants the frontends supply are read from library
  source.
- The floating-point results hold for arithmetic that conforms to the standard binary64 model
  (`Spec/Float.lean`); machine-word arithmetic and the NTT are modelled as exact.
- The security games use textbook decryption and public evaluation keys, and assume IND-CPA with
  evaluation keys public (circular security). The game with evaluation on earlier results is proved
  for local step-by-step interpreters. These are statements about the modelled scheme, not about a
  library.
- No key recovery is implemented, no constant-time claim is made, and no parameter set is claimed
  secure. CKKS and bootstrapping are out of scope. NOT CERTIFIED is not "fails".
- Not "first verified FHE": other Lean 4 projects prove textbook-level or phase-level results.

## How to read the trust story

- `docs/TRUSTED-CORE.md`: what the headline theorems claim, the trusted definitions in reading
  order (section 2), where a definition could be wrong without any proof failing, and a challenge.
- `docs/SPEC.md`: the design, the root of trust and the statement groups.
- `docs/TRUSTED-DEFINITIONS.md`, `docs/TRUSTED-DEFINITIONS-BFV.md`: the evidence for each trusted
  definition (agreement with Mathlib, equality with the independent re-specification `Respec/`,
  execution against OpenFHE, or realisability theorems).
- `SECURITY.md`: what counts as a soundness bug, and the disclosure note on what the tool refuses.

## Reproducing the paper's numbers

| Claim | How | Needs |
|---|---|---|
| Locked statements, classes, kernel replay | `./verify.sh` (`build/check-spec/`, classes in `pin-classes.txt`) | Lean, Mathlib cache |
| Conformance and mutation tests | the gate, steps 6 and 7; counts in `harness/openfhe-pin/results/difftest-counts.json` | the gate |
| Real-size conformance (82 executions) | `SAMPLE=1 harness/openfhe-pin/realsize/run.sh` (the gated sample) | Lean; a traced OpenFHE for the full suite |
| Lattigo instance | `harness/lattigo-pin/run.sh` | Lean (Go only to re-record) |
| Reference implementation | `harness/ref/run.sh 2` (one seed is gated: `harness/ref/difftest.sh`) | Lean |
| `fhe_check` frontend tests | `harness/frontend/tests/run.sh` (run by `./verify.sh`) | `fhe_check` |
| No library at all | `harness/generic-demo/run.sh` | `fhe_check` |
| Default OpenFHE user (BGV) | `harness/eval/openfhe-upstream/README.md` | `fhe_check`; OpenFHE to regenerate |
| BFV defaults by depth | `harness/frontend/levelbfv/README.md` | `fhe_check`; OpenFHE for timings |
| HEIR `mult_dep_8` | `harness/frontend/examples/heir_mult_dep_8.*`, checked by the frontend tests | `fhe_check` |
| Choe-Kang-Stehle circuits | `harness/eval/cks26/run.sh --committed` | `fhe_check`; OpenFHE to regenerate |
| Cost of certified parameters | `harness/eval/frontier/README.md` (tables from `data/`) | OpenFHE |
| Checker speed | `harness/eval/analyzer-speed/bench.sh` | `fhe_check` |
| Real programs | `harness/eval/analyzer-speed/real/run.sh CASE SETTING` (results in `results.tsv`, `reports/`) | OpenFHE, the third-party program |
| Trusted-core size; generic vs library lines | `python3 -I paper/gen/trusted_core.py`, `python3 -I paper/gen/audit_generic.py --lean` | a built tree |

## Layout

```
Spec/              trusted definitions (no sorry)
Challenge/         locked statements: pins, non-vacuity, the headline theorems, certificates
Validation/        proofs of the Challenge statements, checked by the Lean kernel
Respec/            independent re-specification; Respec/Equiv/: the equivalence proofs
FHE/               untrusted proof libraries, the checkers, fhe_check's core; FHE/Ref/: provenfhe_ref
FheCheck.lean      root of the fhe_check executable
ProvenfheRef.lean  root of the provenfhe_ref executable
OpenfhePin.lean    root of the openfhe_pin conformance checker (harness/openfhe-pin)
harness/           fhe_check frontends, conformance suites (openfhe-pin, bfv-float, lattigo-pin),
                   the reference-implementation suite (ref), evaluation harnesses (eval)
scripts/           the gate: check-spec.sh, lock.sh, the pin-status reporter and helpers
trust/             LOCK (locked files), EVIDENCE (conformance evidence), SOURCE-DRIFT.tsv
docs/              TRUSTED-CORE.md, SPEC.md, TRUSTED-DEFINITIONS*.md, QUICKSTART.md,
                   REFERENCE-IMPLEMENTATION.md, trusted-core.json and audit-generic.json (computed)
paper/gen/         the scripts that regenerate docs/trusted-core.json and docs/audit-generic.json
```

## How AI is used

Definitions, statements, proofs, test harnesses and most of the text were written by AI coding
assistants, with the author setting goals and scope.

- **What the kernel and the scripts decide.** Whether a proof of a fixed statement is accepted:
  only the Lean kernel and deterministic scripts such as `scripts/check-spec.sh` decide that.
- **What they do not decide.** Whether a statement means what is intended, whether a trusted
  definition is right, and what to merge were decided by the assistants (including AI review) and,
  for scope, by the author. A model does decide things here; the gate only decides
  whether a proof is accepted.
- **No human expert has reviewed the development.** Read the trusted statements listed in
  `docs/TRUSTED-CORE.md` section 2 as you would any specification, and treat them as unreviewed.

## Licence and attribution

Apache-2.0; see `LICENSE` and `NOTICE`. This project uses OpenFHE, Google HEIR and Lattigo as
references and test oracles. It is not affiliated with or endorsed by their authors.
