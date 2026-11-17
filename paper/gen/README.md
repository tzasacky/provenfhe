# paper/gen: regenerating the computed counts in docs/

Four scripts of this directory ship with the repository; each needs a built tree (`lake build`) and
rewrites one machine-readable file that `docs/` and the paper quote:

| script | regenerates |
|---|---|
| `trusted_core.py` (runs the Lean helper `trusted_core.lean`) | `docs/trusted-core.json`: the reading closure of the headline theorems (`docs/TRUSTED-CORE.md`) |
| `audit_generic.py` (with `--lean`, runs the Lean helper `audit_closure.lean`) | `docs/audit-generic.json`: generic vs library-specific lines of the trusted text |

Usage: `python3 -I paper/gen/trusted_core.py` and `python3 -I paper/gen/audit_generic.py --lean`,
from the repository root. Both are untrusted: they count, they prove nothing.
