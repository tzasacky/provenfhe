import Respec.Basic
import Respec.RNS
import Respec.BGV
import Respec.Noise
import Respec.BFV
import Respec.BGVTest
import Respec.BFVTest

/-!
# Respec — an independent re-specification of BGV / BFV / RNS

Written from the primary literature and library source code, without access to the other
formalization in this repository, sharing only `Spec/Ring.lean`.

* `Respec.Basic`   — conventions (centred/canonical lifts, rounding), strict polynomial operations.
* `Respec.RNS`     — CRT bases, fast/exact base conversion and its overflow, ModDown (plain and
                     BGV), BGV mod-switch and rescaling on limbs, hybrid key switching.
* `Respec.BGV`     — keys, encryption, decryption, invariants, gadget and key-switching keys,
                     modulus-switching variants, automorphisms, bookkeeping state.
* `Respec.Noise`   — worst-case BGV noise rules (functions and `Prop`-valued statements).
* `Respec.BFV`     — decryption, the two noise forms, textbook / HPS / BEHZ multiplication.
* `Respec.BGVTest`, `Respec.BFVTest` — executed sanity tests (`#guard`).

## `Respec/Equiv/`: the comparison with `Spec`

The files under `Respec/Equiv/` (not imported here; the gate builds each by name, scans it for
axioms and replays it through the kernel) prove where this re-specification and the trusted
definitions agree. Their headers call the trusted side **A** (`Spec`, `Challenge`) and this
re-specification **B** (`Respec`), and number the compared topics as **items**:

1. decryption (`Decrypt.lean`); 2. the BGV encryption invariant (`Decrypt.lean`);
3. public-key encryption and the fresh-noise constants (`Encrypt.lean`); 4. key-switching keys and
the gadget (`Gadget.lean`); 5. ModUp and hybrid key switching, limb for limb (`KeySwitch.lean`);
6. the key-switching noise bound (`KsBound.lean`); 7. modulus switching (`ModSwitch.lean`);
8. message-level bookkeeping and 9. decryption as OpenFHE performs it (`Bookkeeping.lean`);
10. B's worst-case noise rules derived from A's theorems (`Rules.lean`, `MulRule.lean`,
`ModSwitchRule.lean`); 11. fast base conversion (`KeySwitch.lean`); 12. BFV decryption
(`BFV.lean`). `Test.lean` holds executed checks (`#guard`), not proofs.
-/
