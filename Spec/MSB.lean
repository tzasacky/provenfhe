import Spec.Budget

/-!
# Spec.MSB — BGV in MSB form, and its t-reading   (TRUSTED)

`Spec.Scheme`, `Spec.Trace` and `Spec.Budget` state BGV in the **LSB form** of the textbook: the
phase of a ciphertext is `p + t·e`, the message in the low digits, and key-switching keys carry
errors that are multiples of `t`. Some libraries implement BGV in the **MSB form** (Lattigo,
`schemes/bgv/README.md`, after Appendix A of ePrint 2013/372): the plaintext is stored scaled by
`t⁻¹ mod Q`, so the phase is `t⁻¹·p + e`, and errors are not multiplied by `t`. This file states
that form and its operations, and the map between the two forms; `Challenge.MSB` pins that the
map carries every MSB statement here onto the LSB statements the certificates are about.

Source citations are to Lattigo v6.2.0 (`github.com/tuneinsight/lattigo`, commit `c1fd095f`) as
one implementation of the form: `file:line` in that tree. Nothing below depends on Lattigo; the
citations say where the convention can be read.

## The form

* **Encoding** (`schemes/bgv/encoder.go:378-410`, `RingT2Q` with `scaleUp`): a plaintext
  `p ∈ Z_t[X]/(X^N+1)` is stored as `t⁻¹·p mod Q` (`p` with coefficients in `[0, t)`). An
  encryption of it has phase `t⁻¹·p + e (mod Q)`.
* **Decryption** (`encoder.go:412-468`, `RingQ2T` with `scaleDown`): the phase is multiplied by
  `t` modulo `Q`, lifted to its centred representative and reduced modulo `t` (`msbDecrypt`).
  (`encoder.go:341-345` then divides by the tracked scale; that bookkeeping is not stated here:
  `Challenge.MSB`, module docstring.)
* **Noise** (`MSBEncrypts`): the error `e = [phase − t⁻¹·m̃]_Q`, centred, with `m̃` the centred
  representative of the message (the MSB "noise" bounds this error alone, not the message).
  A library stores some representative `p` of the message (Lattigo: `p ∈ [0, t)`), and its
  fresh encryptions are described by `p` and `e` (`MSBEncryptsRep`, bounding `‖p‖∞ + t·‖e‖∞`,
  the LSB noise of the t-reading); for `p > t/2` the centred error is `e + 1`, so the two
  descriptions differ by one unit of `t`.

## The t-reading

`toLSB t ct` multiplies every component by `t`. Its phase is `t` times the MSB phase:
`t·(t⁻¹·p + e) = p + t·e`, an LSB ciphertext of the same message whose noise (in the sense of
`Spec.Scheme.BGVEncrypts`, message included) is at most `⌊t/2⌋ + t·B` for MSB noise `B`, and
conversely (`Challenge.MSB.msbEncrypts_toLSB`, `toLSB_msbEncrypts`; these need `gcd(t, Q) = 1`
and that the bounds stay below `Q/2`). The components are integer representatives, as in
`Spec.Trace`; `t·c` is not reduced (every statement reads it modulo a modulus).

## The operations

* **Products** carry a factor `t` (`schemes/bgv/evaluator.go:633-635` and `:677-679`, "multiply
  by T"): the product of `t⁻¹p₁ + e₁` and `t⁻¹p₂ + e₂` is rescaled to `t⁻¹(p₁p₂) + …` by one
  extra multiplication by `t`. So the MSB contract of `mul`, `square`, `mulPlain` is
  `ψ = t·ψ_a·ψ_b`. Additions, constants, automorphisms, copies and dropped limbs have the same
  contracts as in `Spec.Trace`.
* **Key switching** (`gadgetProduct`, `keySwitch`, `relin`): hybrid, on the digits of a
  `Spec.Budget.KSLayout` with the special modulus `P = specialProd`. A component `c` is split
  into its centred residues `Dⱼ = [c]_{Qⱼ}` modulo the digit moduli
  (`ring/basis_extension.go:381-470`, `DecomposeAndSplit`, offset by `⌊Qⱼ/2⌋`), the integer
  inner products `Σⱼ Dⱼ·(bⱼ, aⱼ)` with the keys are formed, and each is divided by `P` with
  centred rounding, `(x − [x]_P)/P` (`ModDown`, `core/rlwe/evaluator_gadget_product.go:39-60`,
  `ring/basis_extension.go:215-256`: the exact `ModUpPtoQ` of `[x]_P`, offset by `⌊P/2⌋`, then
  `(x − ·)·P⁻¹`). The key for digit `j` encrypts `gⱼ·target(s)` with the gadget factor of
  `Spec.Budget.gadgetReq` (`core/rlwe/gadgetciphertext.go:169-235`: `P·target` added in the limbs
  of digit `j`, zero elsewhere and modulo `P`), with an error **not** multiplied by `t`
  (`core/rlwe/keygenerator.go:287-329`, an `EncryptZero` with the secret key): `KeyValidMSB`.
  Relinearization (`core/rlwe/evaluator_evaluationkey.go:120-155`) switches `c₂` and adds the
  result to `(c₀, c₁)`; applying a key (`:99-108`) switches `c₁` and adds the first output to
  `c₀`. The MSB contract has no `t ∣ e` clause, and its bound is read through `t`:
  `t·‖e‖∞ ≤ E.keySwitch`.
* **Rescaling** (`rescale`; `evaluator.go:1363-1393`, `Rescale`, and `ring/scaling.go:101-122`,
  `DivRoundByLastModulusNTT`): every component `c` becomes `(c − [c]_q)/q`, `q` the last prime
  of the level and `[·]_q` centred (offset by `(q − 1)/2`). No `t`-correction. The MSB contract
  `ψ = (Ψ_a + δ)/q` with `q ∣ Ψ_a + δ` has no `t ∣ δ` clause, and its bound is read through `t`:
  `t·‖δ‖∞ ≤ q·E.modSwitchAt k`.

**One budget for both forms.** The MSB contracts take the same `Spec.Trace.Budget` as the LSB
ones, in LSB units: an MSB error `e` counts as `t·e`. This is what the t-reading makes of it,
and it is why an LSB profile (`Spec.Budget.certified`, a library profile) applies unchanged.

What is not stated: the floating-point basis extension Lattigo uses to compute the exact
residues (`ring/basis_extension.go:282-308`, `ModUpExact`) is taken to compute them exactly;
`BaseTwoDecomposition ≠ 0`; the scale-invariant (BFV-style) product `MulScaleInvariant`; and
the fused rotation (`core/rlwe/evaluator_automorphism.go:13-60`: key switching first, the
automorphism after it), which is a different decomposition from `automorph; keySwitch`.
-/

namespace Spec.MSB
open NPoly Scheme Source Correct

section Form
variable {N : ℕ}

/-- **The t-reading**: every component multiplied by `t` (integer representatives). -/
def toLSB (t : ℕ) (ct : List (IntPoly N)) : List (IntPoly N) := ct.map ((t : ℤ) • ·)

/-- **MSB decryption**: `[[t·⟨ct, s⟩]_Q]_t` (`encoder.go:412-468`, `RingQ2T` with
`scaleDown`). -/
def msbDecrypt (t : ℕ) {Q : ℕ} (s : IntPoly N) (ct : List (Poly Q N)) : Poly t N :=
  ofInt t (centered ((t : ZMod Q) • phase (ofInt Q s) ct))

/-- `ct` is an MSB encryption of `m` under `s` with noise at most `B`: it MSB-decrypts to `m`,
and its phase is `t⁻¹·m̃ + e (mod Q)` with `‖e‖∞ ≤ B`, where `m̃` is the centred representative
of `m` and `e` the centred error. The bound is on the error alone. -/
def MSBEncrypts (t B : ℕ) {Q : ℕ} (s : IntPoly N) (ct : List (Poly Q N)) (m : Poly t N) :
    Prop :=
  msbDecrypt t s ct = m ∧
    normInf (centered (phase (ofInt Q s) ct - (t : ZMod Q)⁻¹ • ofInt Q (centered m))) ≤ B

/-- `ct` MSB-encrypts `m` under `s` **through a stored representative**: its phase is
`t⁻¹·p + e (mod Q)` for some integer polynomials `p` with `p ≡ m (mod t)` and `e`, with
`‖p‖∞ + t·‖e‖∞ ≤ B`. The bound is in LSB units (it is what the t-reading's noise is), so that a
library's fresh-encryption bound (`‖p‖∞ ≤ t − 1` for `p ∈ [0, t)`, plus `t` times its error
bound) is `B` itself. -/
def MSBEncryptsRep (t B : ℕ) {Q : ℕ} (s : IntPoly N) (ct : List (Poly Q N)) (m : Poly t N) :
    Prop :=
  ∃ p e : IntPoly N, phase (ofInt Q s) ct = (t : ZMod Q)⁻¹ • ofInt Q p + ofInt Q e ∧
    ofInt t p = m ∧ normInf p + t * normInf e ≤ B

/-- `(b, a)` is a valid MSB key for `req` under `s` with error at most `B`:
`b + a·s = factor·target(s) + e (mod modulus)` with `‖e‖∞ ≤ B`, and no condition on `t`
(`keygenerator.go:287-329`). -/
def KeyValidMSB (B : ℕ) (s : IntPoly N) (req : KeyReq N) (b a : Poly req.modulus N) : Prop :=
  normInf (centered (b + a * ofInt req.modulus s -
    req.factor * ofInt req.modulus (req.target.eval s))) ≤ B

/-- Centred division by `p`: `(x − [x]_p)/p` coefficientwise, `[·]_p` the centred residue. The
division is exact. -/
def divRound (p : ℕ) (x : IntPoly N) : IntPoly N :=
  ⟨fun i => (x.coeff i - ((x.coeff i : ℤ) : ZMod p).valMinAbs) / p⟩

/-- **MSB rescaling** by the prime `q`: `divRound q` on every component. -/
def rescale (q : ℕ) (ct : List (IntPoly N)) : List (IntPoly N) := ct.map (divRound q)

/-- **The MSB tensor product** of two two-component ciphertexts: the first operand multiplied by
`t`, then the textbook tensor product (`evaluator.go:633-650`, `tensorStandard`: `c00 = T·a₀`,
`c01 = T·a₁`, then `c00·b₀`, `c00·b₁ + c01·b₀`, `c01·b₁`). Any other shape gives `[]`. -/
def mulTensor (t : ℕ) (ca cb : List (IntPoly N)) : List (IntPoly N) :=
  match ca, cb with
  | [a0, a1], [b0, b1] =>
    [((t : ℤ) • a0) * b0, ((t : ℤ) • a0) * b1 + ((t : ℤ) • a1) * b0, ((t : ℤ) • a1) * b1]
  | _, _ => []

end Form

variable (P : FullParams)

/-- One MSB key per digit (integer representatives), each valid for `s` with error at most `B`
for its gadget requirement (`Spec.Budget.gadgetReq`). The MSB counterpart of
`Spec.Budget.GadgetKeysOK`, without the `t ∣ e` clause and with its own error bound. -/
def GadgetKeysOK (lay : Budget.KSLayout) (ℓ : ℕ) (tgt : KeyTarget) (B : ℕ)
    (s : IntPoly P.src.N) (keys : List (IntPoly P.src.N × IntPoly P.src.N)) : Prop :=
  keys.length = (lay.sizes ℓ).length ∧
    ∀ j (h : j < keys.length),
      KeyValidMSB B s (Budget.gadgetReq P lay ℓ tgt j) (ofInt _ keys[j].1) (ofInt _ keys[j].2)

/-- **The MSB gadget product** of one component `c` at level `ℓ`: centred digits
`Dⱼ = [c]_{Qⱼ}`, the integer inner products `Σⱼ Dⱼ·bⱼ` and `Σⱼ Dⱼ·aⱼ` with the keys (one pair
per digit, in order), each divided by `P` with centred rounding. -/
def gadgetProduct (lay : Budget.KSLayout) (ℓ : ℕ) (c : IntPoly P.src.N)
    (keys : List (IntPoly P.src.N × IntPoly P.src.N)) : IntPoly P.src.N × IntPoly P.src.N :=
  let D := (Budget.digitModuli P lay ℓ).map fun Qj => centered (ofInt Qj c)
  (divRound (Budget.specialProd P) (List.zipWith (fun d k => d * k.1) D keys).sum,
   divRound (Budget.specialProd P) (List.zipWith (fun d k => d * k.2) D keys).sum)

/-- **MSB key switching** of a two-component ciphertext `[c₀, c₁]`:
`[c₀ + y₀, y₁]` with `(y₀, y₁)` the gadget product of `c₁` (`evaluator_evaluationkey.go:99-108`).
Any other shape gives `[]`. -/
def keySwitch (lay : Budget.KSLayout) (ℓ : ℕ) (ct : List (IntPoly P.src.N))
    (keys : List (IntPoly P.src.N × IntPoly P.src.N)) : List (IntPoly P.src.N) :=
  match ct with
  | [c0, c1] => [c0 + (gadgetProduct P lay ℓ c1 keys).1, (gadgetProduct P lay ℓ c1 keys).2]
  | _ => []

/-- **MSB relinearization** of a three-component ciphertext `[c₀, c₁, c₂]`:
`[c₀ + y₀, c₁ + y₁]` with `(y₀, y₁)` the gadget product of `c₂`
(`evaluator_evaluationkey.go:120-155`). Any other shape gives `[]`. -/
def relin (lay : Budget.KSLayout) (ℓ : ℕ) (ct : List (IntPoly P.src.N))
    (keys : List (IntPoly P.src.N × IntPoly P.src.N)) : List (IntPoly P.src.N) :=
  match ct with
  | [c0, c1, c2] =>
    [c0 + (gadgetProduct P lay ℓ c2 keys).1, c1 + (gadgetProduct P lay ℓ c2 keys).2]
  | _ => []

/-- The t-reading of a ciphertext environment. -/
def toLSBEnv (σ : Trace.CtEnv P) : Trace.CtEnv P := fun x => (σ x).map (toLSB P.src.t)

/-- `ct` (integer representatives) MSB-encrypts the value `v` under `s` through a stored
representative with bound `B` (`MSBEncryptsRep`, LSB units), at the level's modulus and under the
key `σ_key(s)`: the MSB counterpart of `Spec.Correct.Encrypts` (BGV). -/
def Encrypts (s : IntPoly P.src.N) (B : ℕ) (v : Val P.src) (ct : List (IntPoly P.src.N)) :
    Prop :=
  ct.length = v.parts ∧
  match v.msg with
  | .exact m =>
    MSBEncryptsRep P.src.t B (automorph v.key s) (ct.map (ofInt (P.src.modulus v.level))) m

/-- Every input ciphertext MSB-encrypts its message with bound `B` (`Encrypts`), as declared by
the first declaration of its name (as `Spec.Correct.InputsOK`). -/
def InputsOK (s : IntPoly P.src.N) (B : ℕ) (prog : Program) (msgs : Var → Msg P.src.t P.src.N)
    (cts : Var → List (IntPoly P.src.N)) : Prop :=
  ∀ x d, prog.inputs.find? (·.name = x) = some d → Encrypts P s B (inputVal P msgs d) (cts x)

/-- **One step of an MSB ciphertext-level run**: `Spec.Trace.StepOK` with the three differences
of the module docstring (products carry `t`; key switching and modulus switching have no `t ∣ ·`
clause and their errors are read through `t` against the same budget `E`). -/
def StepOK (E : Trace.Budget) (s : IntPoly P.src.N) (ρ ρ' : Env P.src) (σ σ' : Trace.CtEnv P)
    (i : Instr) : Prop :=
  ∃ v ct, ρ' (Trace.dst i) = some v ∧ ct.length = v.parts ∧ σ' = σ.set (Trace.dst i) ct ∧
    let Q := P.src.modulus v.level
    let φ := Trace.phaseAt P Q v.key s ct
    match i with
    | .add _ a b | .addPlain _ a b => ∃ x y ca cb, ρ a = some x ∧ ρ b = some y ∧ σ a = some ca ∧ σ b = some cb ∧
        φ = Trace.phaseAt P Q x.key s ca + Trace.phaseAt P Q y.key s cb
    | .sub _ a b | .subPlain _ a b => ∃ x y ca cb, ρ a = some x ∧ ρ b = some y ∧ σ a = some ca ∧ σ b = some cb ∧
        φ = Trace.phaseAt P Q x.key s ca - Trace.phaseAt P Q y.key s cb
    | .mul _ a b | .mulPlain _ a b => ∃ x y ca cb, ρ a = some x ∧ ρ b = some y ∧ σ a = some ca ∧ σ b = some cb ∧
        φ = (P.src.t : ZMod Q) • (Trace.phaseAt P Q x.key s ca * Trace.phaseAt P Q y.key s cb)
    | .square _ a => ∃ x ca, ρ a = some x ∧ σ a = some ca ∧
        φ = (P.src.t : ZMod Q) • (Trace.phaseAt P Q x.key s ca * Trace.phaseAt P Q x.key s ca)
    | .mulConst _ a c => ∃ x ca, ρ a = some x ∧ σ a = some ca ∧
        φ = (c : ZMod Q) • Trace.phaseAt P Q x.key s ca
    | .copy _ a | .toEval _ a | .toCoeff _ a => ∃ x ca, ρ a = some x ∧ σ a = some ca ∧
        φ = Trace.phaseAt P Q x.key s ca
    | .automorph _ a g => ∃ x ca, ρ a = some x ∧ σ a = some ca ∧
        φ = automorph g (Trace.phaseAt P Q x.key s ca)
    | .relin _ a | .keySwitch _ a => ∃ x ca e, ρ a = some x ∧ σ a = some ca ∧
        P.src.t * normInf e ≤ E.keySwitch ∧
        φ = Trace.phaseAt P Q x.key s ca + ofInt Q e
    | .modSwitch _ a => ∃ x ca δ q, ρ a = some x ∧ σ a = some ca ∧
        P.src.qs[x.level - 1]? = some q ∧
        let Ψ := centered (Trace.phaseAt P (P.src.modulus x.level) x.key s ca)
        P.src.t * normInf δ ≤ q * E.modSwitchAt x.parts ∧
        (∀ j, (q : ℤ) ∣ Ψ.coeff j + δ.coeff j) ∧
        φ = ofInt Q ⟨fun j => (Ψ.coeff j + δ.coeff j) / q⟩
    | .dropLimbs _ a _ => ∃ x ca, ρ a = some x ∧ σ a = some ca ∧
        φ = ofInt Q (centered (Trace.phaseAt P (P.src.modulus x.level) x.key s ca))

/-- An MSB ciphertext-level run of `body` in which every step meets its MSB contract
(as `Spec.Trace.Run`). -/
def Run (E : Trace.Budget) (s : IntPoly P.src.N) : List Instr → Env P.src → Trace.CtEnv P →
    Trace.CtEnv P → Prop
  | [], _, σ, σf => σf = σ
  | i :: is, ρ, σ, σf =>
    ∃ ρ' σ', step P.src ρ i = some ρ' ∧ StepOK P E s ρ ρ' σ σ' i ∧ Run E s is ρ' σ' σf

end Spec.MSB
