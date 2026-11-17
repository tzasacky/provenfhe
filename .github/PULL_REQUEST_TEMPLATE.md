## What and why

<!-- What does this change, and why is it needed? -->

## Checklist

- [ ] I ran `./verify.sh` (or `STRICT=1 scripts/check-spec.sh`) on this branch and pasted the
      final summary below.
- [ ] No `sorry` (except the bodies of locked statements in `Challenge/`), no new `axiom`, no
      `native_decide` / `implemented_by` / kernel-skipping options.
- Locked files (`Spec/`, `Challenge/`, `scripts/`, `lakefile.toml`, `lean-toolchain`,
  `lake-manifest.json`, `Spec.lean`, `Challenge.lean`):
  - [ ] not changed, **or**
  - [ ] changed: the reason is written above, and I understand a maintainer must review it and
        regenerate `trust/LOCK` (do not regenerate it yourself).
- AI assistance (see CONTRIBUTING.md):
  - [ ] none, **or**
  - [ ] used: tools and the parts they wrote are listed below, and if any LOCKED statement or
        trusted definition changed, I have read every changed line and can explain it.

AI tools used, and for what:

## Gate output

```
<!-- paste the summary printed by ./verify.sh (or the end of scripts/check-spec.sh) -->
```
