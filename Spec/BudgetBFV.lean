import Spec.Budget
import Spec.TraceBFV

/-!
# Spec.BudgetBFV — the BFV error budget, from the parameters   (TRUSTED)

`Spec.TraceBFV.Budget` is five numbers a backend declares. This file computes them, for the
textbook algorithms, from what the user supplies (`FullParams`) and the key-switching layout.

* **Key switching.** BFV uses the same hybrid key switching as BGV (`Spec.Budget`: same digits,
  same gadget, same keys `GadgetKeysOK`, whose errors need not be multiples of `t`), with plain
  rounding in ModDown instead of the `t`-corrected one. Its error is the BGV bound with `t = 1`:
  `‖e‖∞ ≤ ⌊(N·B_k·Σⱼ ℓⱼ·Qⱼ + k·P·(1 + N·B_s)) / (2P)⌋` (centred representatives).
  `ksBoundAt` is that number at one level, `ksBudget` its maximum over the chain.
* **Modulus switching.** Rounding every component, `c ↦ ⌊c/q_last⌉`, of a two-component
  ciphertext: `msBudget = ⌈(1 + N·B_s)/2⌉`.
* **Multiplication** (textbook: centred lift, integer tensor product, exact rounding of `t·c/Q`;
  two-component operands): `mulLift = ⌊(2 + N·B_s)/2⌋`, `mulRound = 1 + N·B_s + (N·B_s)²`.
* **Plaintext addition** of exactly `Δ·p`: `plainAdd = 0`.

**Domain.** `msBudget`, `mulLift` and `mulRound` are the numbers of *two-component* operands:
`Challenge.BFV` pins that the textbook algorithms achieve them there, from the ciphertexts and
the keys alone (`stepOK_mul_textbook`, `stepOK_square_textbook`, `stepOK_modSwitch_textbook`,
`relin_realizable`, `keySwitch_realizable`). For a value with more components the rounding
errors and the lift are larger (they grow with the powers of `N·B_s` up to the number of
components minus one), and this budget does not cover them: the reference analyzer
(`Challenge.BFV.refAnalyzeBFV`) rejects a `mul`, `square` or `modSwitch` of such a value
(`Challenge.BFV.domainOK`, `refAnalyzeBFV_rejects_unrelinearized`), and
`Challenge.BFV.certified_run_exists` pins that every program it accepts at this budget has a
run within it. A budget that depends on the number of components is future work. The
key-switching budget does not depend on it (`relin` takes three components, `keySwitch` two).
-/

namespace Spec.BudgetBFV
open NPoly Scheme Source

/-- The parameters with plaintext modulus `1`: `Spec.Budget.ksBoundAt` at these is the bound of
hybrid key switching without the `t`-correction. -/
def unitPlain (P : FullParams) : FullParams := { P with src := { P.src with t := 1 } }

/-- The worst-case phase error of one BFV hybrid key switch at level `ℓ`. -/
def ksBoundAt (P : FullParams) (lay : Budget.KSLayout) (ℓ : ℕ) : ℕ :=
  Budget.ksBoundAt (unitPlain P) lay ℓ

/-- The key-switching budget: the largest `ksBoundAt` over the levels `1, …, L` of the chain. -/
def ksBudget (P : FullParams) (lay : Budget.KSLayout) : ℕ :=
  ((List.range P.src.qs.length).map fun i => ksBoundAt P lay (i + 1)).foldl max 0

/-- The modulus-switching budget `⌈(1 + N · secretBound) / 2⌉` (two-component ciphertexts). -/
def msBudget (P : FullParams) : ℕ := (1 + P.src.N * P.secretBound + 1) / 2

/-- The lift budget of textbook multiplication, `⌊(2 + N · secretBound) / 2⌋` (two-component
operands). -/
def mulLift (P : FullParams) : ℕ := (2 + P.src.N * P.secretBound) / 2

/-- The rounding budget of textbook multiplication, `1 + N·B_s + (N·B_s)²` (twice the phase
error `(1 + N·B_s + (N·B_s)²)/2` of rounding three components). -/
def mulRound (P : FullParams) : ℕ :=
  1 + P.src.N * P.secretBound + (P.src.N * P.secretBound) * (P.src.N * P.secretBound)

/-- The certified budget of a BFV parameter set and a key-switching layout, for the textbook
operations; `modSwitch`, `mulLift` and `mulRound` are for two-component operands (module
docstring). -/
def certified (P : FullParams) (lay : Budget.KSLayout) : TraceBFV.Budget :=
  { keySwitch := ksBudget P lay, modSwitch := msBudget P, mulLift := mulLift P,
    mulRound := mulRound P, plainAdd := 0 }

end Spec.BudgetBFV
