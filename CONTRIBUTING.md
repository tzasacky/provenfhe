# Contributing to ProvenFHE

Thank you for looking. This project is a Lean 4 development whose results are decided by a machine
check, not by trust in whoever wrote the code. That shapes how contributions work.

## The short version

- Before you open a pull request, run `./verify.sh` (or `scripts/check-spec.sh` once your checkout
  is set up) and paste its final summary into the PR.
- Proofs are accepted only through the gate. If the gate passes and no locked file changed, a proof
  contribution is judged on whether it is maintainable, not on who or what wrote it.
- Changes to locked files (`Spec/`, `Challenge/`, `scripts/`, `lakefile.toml`, `lean-toolchain`,
  `lake-manifest.json`, `Spec.lean`, `Challenge.lean`) need the maintainer's review and an update
  of `trust/LOCK` by the maintainer. Say in the PR why the change is needed.
- No `sorry` outside the bodies of the locked statements in `Challenge/` (which are `sorry` by
  design and proved in `Validation/`), no new `axiom`, no `native_decide` or other ways around the
  kernel.
- If you used an AI tool, say so in the PR (see "AI-assisted contributions").

## Running the checks

Toolchain: Lean `v4.35.0` with Mathlib `v4.35.0`, pinned in `lean-toolchain` and `lake-manifest.json`.
Do not run `lake update` in a PR; dependency bumps are the maintainer's.

- **Everything, from a fresh clone:** `./verify.sh`. It fetches Mathlib's prebuilt cache, runs the
  strict gate and the `fhe_check` tests, and prints a summary. Prerequisites and the time and disk it
  needs are in `README.md` ("Check it yourself").
- **The full gate alone:** `STRICT=1 scripts/check-spec.sh`. Run it before a pull request that
  touches `Spec/`, `Challenge/`, `Validation/` or a harness. A from-scratch strict `./verify.sh`
  took 817 s on a 128-core machine that was otherwise idle when the run started (7.2 GB peak
  memory in its largest process); nothing was measured on a laptop.
- **The `fhe_check` tests:** `lake build fhe_check && harness/frontend/tests/run.sh`.
- **Library tools.** OpenFHE and HEIR are needed only to re-record the committed runs (`LIVE=1`,
  see `harness/*/README.md`), never for the normal check.

## How the gate works

`scripts/check-spec.sh` is the definition of "the work is correct". It runs eight steps:

1. **Lock.** The locked files listed above must match the SHA-256 manifest `trust/LOCK`, and that
   manifest must match the one committed in git. Only the maintainer regenerates it
   (`scripts/lock.sh`), in the same commit as the reviewed change.
2. **Banned constructs** in the trusted definitions (`Spec/`): `sorry`, axioms, `native_decide`,
   `implemented_by`, `unsafe`, new syntax and similar.
3. **Text audit of the definition holes** (`FHE/Holes.lean` and what it imports).
4. **Sandboxed build** of `Spec`, `Challenge`, `Validation` and every file of the `FHE` library under
   `bwrap`: no network, only the build directory writable, and the locked statements' build outputs
   read-only while proofs are compiled.
5. **Pins, coverage and kernel replay.** Each locked statement in `Challenge/` must be proved in
   `Validation/` by a theorem with the identical statement, using only the three standard axioms;
   every file under `Spec/` and `Challenge/` must be imported by its root; the whole `FHE` library
   is put under the same axiom audit; and every constant in these closures is re-checked by the Lean
   kernel from an empty environment.
6. **Differential tests**: the trusted definitions and proved algorithms against recorded OpenFHE
   runs (`harness/openfhe-pin`, `harness/bfv-float`), the `fhe_check` frontend tests
   (`harness/frontend`), and the proved reference implementation `provenfhe_ref` (`harness/ref`).
7. **Mutation tests**: injected bugs in scratch copies of the models must be caught by step 6.
8. **Lock re-check**: nothing changed a locked file during the run.

`STRICT=1` (what `./verify.sh` uses when the sandbox is available) also fails on any unproved
statement, a missing suite, an uncommitted lock or an unsandboxed build.

What a human must read to know what is proved is listed in `docs/TRUSTED-CORE.md` section 2.
Everything else (`Validation/`, most of `FHE/`, the harness) is untrusted: it is checked, not
believed.

## Where contributions help most

- Reviews of the locked statements: is a statement vacuous, too weak, or not what its comment says?
  This is the most valuable review there is.
- Simplifications of existing proofs (`Validation/`, `FHE/`).
- New frontends or examples for `fhe_check` (`harness/frontend/`), with their tests.
- Reports of anything that weakens a claim: see `SECURITY.md` for soundness problems, and the issue
  forms.

## Changes to locked statements and trusted definitions

A change to `Spec/` or `Challenge/` changes what the project claims. It needs:

- a written reason in the PR (what was wrong or missing, and why the new statement is right);
- for a trusted definition, its pin: a locked statement relating it to Mathlib, or a differential
  test against recorded library runs with mutants showing the test can fail, or an equality proof
  with the independent re-specification (`Respec/Equiv`);
- review and merge by the maintainer, who regenerates `trust/LOCK` in the merge.

Changes to `scripts/` (the gate itself) follow the same rule, because the gate decides what counts.
`docs/TRUSTED-DEFINITIONS.md` and `docs/TRUSTED-DEFINITIONS-BFV.md` list each trusted definition
with the evidence for it; update the row when you change the definition.

## AI-assisted contributions

Most of this repository was written by AI coding assistants under its author's direction (see
"How AI is used" in `README.md`). Acceptance of a proof has never depended on that: the Lean kernel
and the gate decide whether a proof of a fixed statement is accepted. So AI-assisted contributions
are welcome, on these conditions:

- **Disclose it** in the PR (the template asks): which tools, and for which parts. Do not name a
  vendor or model in files or commit messages; the PR description is the place for it.
- **The human who submits is responsible for it.** If the PR changes a locked statement or a trusted
  definition, the submitter must have read every changed locked line and be able to explain, in their
  own words, what it says and why it is right. You will be asked.
- **No unattended agents.** Do not let an agent open PRs, issues or comments on its own.
- Proofs are judged by the gate like any other proof. Long, machine-written proofs may be asked to be
  shortened or split before merging, for maintainability.

## Practicalities

- Keep commits focused, and describe the "why" in the message.
- By contributing you agree that your contribution is licensed under Apache-2.0 (`LICENSE`).
