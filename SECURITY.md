# Security and soundness reports

ProvenFHE is research software. It makes worst-case noise bounds, the countermeasure the
IND-CPA-D attack papers recommend, checkable; it makes **no security claim about any deployment**:
no claim that any parameter set is secure, no constant-time claim, no claim about the security of
OpenFHE or any other implementation, and no warranty (see `LICENSE`). The theorems of a security
kind reduce IND-CPA-D to IND-CPA on the circuit classes the certificate accepts, for BGV and BFV,
with textbook decryption and public evaluation keys: in the fresh-only game for every evaluator
within the budget, and in the game with evaluation on earlier results for local step-by-step
interpreters. They are about the modelled scheme and their stated assumptions (`README.md`, "What
is proved" and "What is not claimed"). Do not use the tool's verdicts as the only basis for
deploying a homomorphic-encryption system.

What it does claim is narrower and checkable: the locked statements in `Challenge/` are proved
(as reported by the gate `scripts/check-spec.sh`), and `fhe_check` answers CERTIFIED only when
a proved theorem shows that every output decrypts correctly in the worst case, under the
assumptions it prints. A failure of one of those claims is the most serious kind of bug this
project can have. We want to hear about it.

## What counts

Report privately (below) anything that makes one of these false:

1. **Gate bypass.** A way to make `scripts/check-spec.sh` (or `./verify.sh`) report a statement as
   PROVEN, or report PASS, when the statement is not actually proved by the Lean kernel from the
   three standard axioms: for example a proof that smuggles in an axiom, skips kernel checking,
   escapes the build sandbox to change locked files or build outputs, or exploits the way the
   gate reads `.olean` files.
2. **A false locked statement.** A locked statement in `Challenge/` that is proved but says
   something other than what `docs/SPEC.md` and the comments say it means (for example, it is
   vacuous, or a trusted definition in `Spec/` does not model what it claims to model), so that a
   reader would be misled about what was proved.
3. **A wrong CERTIFIED verdict.** An input on which `fhe_check` says CERTIFIED, the program and
   parameters satisfy every assumption the report lists, and yet some output can decrypt
   incorrectly. Include the `.fhecheck.json` input and, if you have one, a concrete failing
   execution.
4. **A differential suite that cannot fail.** A way in which the conformance comparisons in
   `harness/` would report agreement for a definition or algorithm that disagrees with the
   recorded library runs.

Not in scope for private reporting (open a normal issue instead): NOT CERTIFIED or UNSUPPORTED
verdicts you believe are too conservative, crashes of `fhe_check` on malformed input, build
problems, documentation errors, and disagreements between our definitions and a library's
recorded behaviour.

Findings about third-party tools (OpenFHE, HEIR, Lattigo) belong to those projects; please report
them to them under their own security policy.

## Library behaviour and what the tool refuses (disclosure note)

This is the repository's statement about the limits of `fhe_check`'s guarantees where they depend
on a third-party library. Other files refer to it as "the disclosure note".

A CERTIFIED verdict rests on the assumption that each library operation meets its per-operation
contract (see `docs/SPEC.md`). While building and testing `fhe_check` against OpenFHE v1.6.1, earlier
versions of the tool printed a false CERTIFIED on some programs: the certificate assumed a contract
that was not established for those parameters or programs. Each such path is closed by a check that
refuses the affected programs or parameters, and the test suites of the gate exercise each
refusal. None of them was found by the proof checker; they were found by checking recorded
library runs against the contracts, by adversarial review and by red-team testing.
The refusals are in the code and the tests (the parameter checks and extractor refusals of
`fhe_check`). They are sufficient conditions for the tool's guarantees, not exact descriptions of
where a library fails, and a refusal is not a statement that the library is wrong. The fixes close
the paths we found; they do not show that there are no others.

Observations about OpenFHE made during this work were reported to its maintainers.

- Public reports: thirteen issues with reproducers, twelve of them with a tested fix, at
  <https://github.com/tzasacky/openfhe-development/issues> (the upstream tracker accepts issues from
  collaborators only), announced in the Bug Reports category of the OpenFHE forum
  (<https://openfhe.discourse.group/t/five-bfv-bgv-bug-reports-for-v1-6-1-with-reproducers-and-fixes/2412>
  and a second topic for issues 6 to 13).
- One further observation was reported privately to the maintainers on 2026-11-14 (before this
  repository was published). It is security-relevant: no detail of it is given anywhere in this
  repository or the accompanying paper until it is fixed upstream or the agreed date has passed.

## How to report

Use GitHub's private vulnerability reporting for this repository: the "Security" tab, then
"Report a vulnerability". Do not open a public issue, pull request or discussion for an item in
the list above until it is fixed.

Please include: the commit you tested, the exact command and its output (the gate prints a report
and writes its logs to `build/check-spec/`), and the smallest input or Lean file that shows the
problem.

## What happens next

This project is maintained by a single maintainer without a service-level commitment. I aim to
acknowledge a report within 7 days. A confirmed soundness problem is treated as the top priority:
the fix, the affected statements or verdicts, and credit to the reporter (if wanted) are
published in the repository history and the release notes. Soundness fixes are made in public
once a fix is ready, because the point of this project is that anyone can re-check it.
