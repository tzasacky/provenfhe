import Spec.Budget
import Spec.Encrypt
import Spec.Certify
import Challenge.Headline.Defs

/-!
# Challenge.Certify.Defs — the function that decides a certificate   (LOCKED definitions)

`certify?` is the whole decision of `fhe_check`: it takes exactly the decoded data (parameters,
key-switching layout, program, which decryption the library performs, the mode, and the
declared modulus-switching method) and performs
every check a certificate rests on itself. The statements about it are in `Challenge.Certify`
(`certify? x = some c → …`), so a tool that prints "certified" exactly when `certify?` returns a
certificate composes nothing: what remains outside is reading the input and printing.

**What `certify?` checks** (`some` only if all hold; `c.params` is the parameter set analysed):

0. the declared modulus-switching method is the centred one (`x.msMethod = .centred`): the
   certified modulus-switching budgets hold for no other (`Spec.Budget`, module docstring);
1. the mode. Worst case: `c.params = x.P` (the declared input noise). Fresh encryptions: the
   variance proxy `varProxy` is positive and the denominator `md` of the declared mean bound is
   positive; `ε` is `epsFor V (n·2N) κ + meanDrift …`, or `worstError` if that is not larger
   (`freshEps`; then nothing is probabilistic); `c.params` is `x.P` with the input noise
   **replaced** by `freshNoise t Bp ε` (the declared input noise is not used), `Bp` the declared
   bound of the stored plaintext polynomials; and `Spec.Encrypt.freshOK?` holds of the inputs at
   `c.params`. Fresh encryptions described in `ℓ₂` (`freshL2`): the same with
   `V = varProxyL2 E2 S2 Vu V1 V2` and `ε = epsFor V (n·2N) κ + meanDrift (E2 + 1 + S2) mn md`
   (no fallback);
2. `Spec.schemeParamsOK?` and `Spec.Budget.specialOK?` (odd special primes) at `c.params`;
3. the key-switching layout restricts from the top level to every level `1, …, L` of the chain
   (`layoutOK?`: usable at every level, and the digits of each level are the top-level digits
   cut down), and the key noise is small enough for a top-level key to be a key at every level
   (`keysRestrict?`): a certificate is about one key set generated at the top level, as
   libraries generate it (`Challenge.Certify.certify?_keys_restrict`);
4. the program has at least one output, and every input can hold every message
   (`inputsMsgOK?`): every input's level has a modulus above `t`, and every declared bound of an
   input is at least `⌊t/2⌋`. Without these, some messages have no input ciphertext meeting the
   input hypotheses, and the certificate would be about no inputs for them
   (`Challenge.Profile.Inputs`);
5. `Challenge.Headline.refAnalyze` accepts the program at the budget
   `Spec.Budget.certified c.params x.lay`;
6. for **each** output `o`: `refAnalyze` accepts the program with `o` as its only output, with a
   bound `B_o`, and `Spec.Encrypt.certOK?` accepts that one-output program at `B_o` (the output
   is under the secret key itself; if `x.switched`, the switched decryption is exact at `B_o`).

**Why it is defined here and not in `Spec/`.** The analyzer it runs, `refAnalyze`, is a locked
definition of `Challenge.Headline.Defs`, and trusted modules cannot import locked ones. The
alternative, a function in `Spec/` with the analyzer as a parameter, would make the trusted
function something no one runs, and every statement would be about its instance at `refAnalyze`
anyway. The data it reads and returns (`Input`, `Mode`, `MSMethod`, `Certificate`, `NoiseUsed`)
and the analyzer-independent computations (`freshDrift`, `freshEps`, `layoutOK?`,
`keysRestrict?`) are trusted definitions of `Spec.Certify`. This file imports trusted modules and that one locked module only (no
probability theory), so the tool can import it without the statements.
-/

namespace Challenge.Certify
open Spec Spec.Source Spec.Budget Spec.Encrypt Spec.Certify Challenge.Headline

/-- **Every input can hold every message** (item 4): for every input declaration `d`, the
modulus of its level exceeds `t` (else some message has no encryption at that level within any
bound) and its declared bound, if any, is at least `⌊t/2⌋` (else the message `⌊t/2⌋` has no
encryption within it). -/
def inputsMsgOK? (P : FullParams) (prog : Program) : Bool :=
  prog.inputs.all fun d => decide (P.src.t < P.src.modulus d.level) &&
    (prog.boundOf d.name).all fun b => decide (P.src.t / 2 ≤ b)

/-- The noise bound of one output: `refAnalyze` on the program with `o` as its only output, if
`certOK?` accepts that program at that bound. -/
def outputBound? (P : FullParams) (E : Trace.Budget) (prog : Program) (switched : Bool)
    (o : Var) : Option ℕ := do
  let b ← refAnalyze P E { prog with outputs := [o] }
  guard (certOK? P { prog with outputs := [o] } b switched)
  pure b

/-- The checks common to both modes, at the parameters `P` to be analysed: the whole-program
bound and the per-output bounds. -/
def checked? (P : FullParams) (lay : KSLayout) (prog : Program) (switched : Bool) :
    Option (ℕ × List (Var × ℕ)) := do
  guard (schemeParamsOK? P)
  guard (specialOK? P)
  guard (layoutOK? P lay)
  guard (keysRestrict? P)
  guard (!prog.outputs.isEmpty)
  guard (inputsMsgOK? P prog)
  let B ← refAnalyze P (certified P lay) prog
  let outs ← prog.outputs.mapM fun o =>
    (outputBound? P (certified P lay) prog switched o).map fun b => (o, b)
  pure (B, outs)

/-- **The decision.** See the module docstring for the list of checks. -/
def certify? (x : Input) : Option Certificate :=
  if x.msMethod ≠ .centred then none else
  match x.mode with
  | .worstCase => do
    let (B, outs) ← checked? x.P x.lay x.prog x.switched
    pure ⟨x.P, certified x.P x.lay, .declared, 0, 0, B, outs⟩
  | .fresh fresh Bp Bk Bu B1 B2 mn md κ => do
    guard (0 < varProxy x.P.src.N x.P.secretBound Bk Bu B1 B2)
    guard (0 < md)
    let (ε, used, drift) := freshEps x.P fresh.length Bk Bu B1 B2 mn md κ
    let P' : FullParams := { x.P with inputNoise := freshNoise x.P.src.t Bp ε }
    guard (freshOK? P' x.prog fresh)
    let (B, outs) ← checked? P' x.lay x.prog x.switched
    pure ⟨P', certified P' x.lay, used, ε, drift, B, outs⟩
  | .freshL2 fresh Bp E2 S2 Vu V1 V2 mn md κ => do
    guard (0 < varProxyL2 E2 S2 Vu V1 V2)
    guard (0 < md)
    let drift := meanDrift (E2 + 1 + S2) mn md
    let ε := epsFor (varProxyL2 E2 S2 Vu V1 V2) (fresh.length * (2 * x.P.src.N)) κ + drift
    let P' : FullParams := { x.P with inputNoise := freshNoise x.P.src.t Bp ε }
    guard (freshOK? P' x.prog fresh)
    let (B, outs) ← checked? P' x.lay x.prog x.switched
    pure ⟨P', certified P' x.lay, .freshKappaL2, ε, drift, B, outs⟩

end Challenge.Certify
