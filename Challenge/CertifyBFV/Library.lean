import Challenge.CertifyBFV
import Challenge.RealizeBFV

/-!
# Challenge.CertifyBFV.Library — OpenFHE's algorithms, composed, stay within the certified budget   (LOCKED definitions and statements; proofs in `Validation/CertifyBFV/Library.lean`)

`Challenge.CertifyBFV.certifyBFV?_sound` covers every run in `Spec.TraceBFV.RunAt … c.budget`, and
the realizability statements of `Challenge.CertifyBFV` say, instruction by instruction, that some
algorithm meets each contract. Neither says that **executing the library's algorithms, one
instruction after the other,** is such a run. This file defines that execution, `runLibrary`, and
states that it is one (`certifyBFV?_library_run`), so `certifyBFV?_sound` and
`certifyBFV?_decrypts` apply to its outputs.

## `runLibrary`: the declared technique's algorithms, instruction by instruction

From the input ciphertexts, along the body (replaying `Source.step` on all-zero messages for the
levels, numbers of components and keys, which do not depend on the messages), each instruction's
destination gets what the library computes from the ciphertexts of its operands (`libStep`):

* `add`, `sub`: componentwise, the shorter operand padded with zeros (`EvalAdd`, `EvalSub`).
* `addPlain`, `subPlain`: by the declared method (`InputBFV.plainAdd`): `c₀ ± ⌊Q/t⌋·p`
  (`.delta`), `c₀ ± ⌊Q·p/t⌉` (`.rounded`), `c₀ ± ⌈Q·p/t⌉` (`.scaled`: OpenFHE's `TimesQovert`,
  `bfvrns-leveledshe.cpp:56-96`, which computes `(Q·p + [−Q·p]_t)/t` on a plaintext stored in
  `[0, t)`), with `p` the centred representative modulo `Q` of the stored plaintext (the result is
  the same modulo `Q` for every representative congruent modulo `t`).
* `mulPlain`: every component times the plaintext polynomial; `mulConst`: times the constant.
* `mul`, `square`: the declared technique (`libMul`): `Fl.hpsMul`, `Fl.poverqMul`,
  `Fl.leveledMul` (with the declared drop of the instruction at the top level) with the
  binary64 sums `Fl.floatSums A`, `behzMul`, or the textbook `bfvMul`.
* `relin`, `keySwitch`: `RelinearizeCore` (`libKS`): under `HPSPOVERQLEVELED` on a top-level
  operand, `Fl.leveledKS (Fl.floatSums A)` with the declared drop and **the transcribed key
  switch** `Challenge.RealizeBFV.ksBFV` at the reduced level as its core; otherwise `ksBFV` at the
  operand's level (`relinBFV`, `keySwitchBFV`). A `keySwitch` of an operand under the key `g` is
  OpenFHE's rotation (`EvalAutomorphism`: key switch, then `σ_g`) of the operand rotated back,
  `σ_g⁻¹` of every component (`rotInv`): on the frontend's mapping of a rotation,
  `automorph m a g; keySwitch d m` with `m = σ_g(a)`, this is exactly the library's rotation of
  `a` (`σ_g⁻¹ ∘ σ_g = id`); the keys are those stored for `g` (`gk g`).
* `modSwitch`: rounding of every component, `⌊c/q_last⌉` (`InputBFV.msRound`).
* `copy`, `toEval`, `toCoeff`: the operand; `automorph g`: `σ_g` of every component.

Keys: one relinearization key set `rk` and one rotation key set `gk g` per automorphism index,
all generated once at the top level, as OpenFHE does.

## `certifyBFV?_library_run`

For an accepted input, it is a `RunAt … c.budget` for every secret within `secretBound`, every
relinearization key set valid at the top level, every rotation key set valid at the top level for
`(s', σ_g(s'))` with `σ_g(s') = s`, all inputs meeting `Spec.TraceBFV.InputsOK`, and every
arithmetic `A` conforming to the binary64 model **when the certificate records `binary64`**.
Hypotheses that no check discharges, all explicit:

* `hid : AssumptionBFV.idealised ∉ c.assumed`: the budget is the library's, not the idealised
  one (the certificate records `idealised` exactly when `floatTol = false` and some binary64 step
  would round: `certifyBFV?_assumed`); the tool prints a certificate recording `idealised` as such;
* `hA : AssumptionBFV.binary64 ∈ c.assumed → Spec.Float.Conforms A`: the platform hypothesis
  exactly when the certificate records it;
* the declared key-switching layout is the library's: CHECKED by `certifyBFV?`
  (`Challenge.RealizeBFV.ksDeclOK?`, item 5b of its checks), so it is not a hypothesis;
* the declared drops (`x.drops`) and the declared technique and plaintext-addition method are
  the library's (they define `runLibrary`; that they match a given OpenFHE execution is what the
  conformance harness compares, not something proved here).

**What remains idealised** (modelled, not proved of the library's code): machine words and the NTT
as exact modular arithmetic; `FindLevelsToDrop` (the drops are an input); the frontend's mapping
of OpenFHE calls to instructions; key generation (the keys are hypotheses).
-/

namespace Challenge.CertifyBFV
open Spec NPoly Scheme Source Correct Spec.BudgetBFV Spec.CertifyBFV Challenge.BFV Challenge.BFVMul
  Challenge.RealizeBFV

/-- The inverse of `g` modulo `2N` (for odd `g`, `σ_{rotInv N g} ∘ σ_g = id`). -/
def rotInv (N g : ℕ) : ℕ := ((g : ZMod (2 * N))⁻¹).val

/-- `⌈Q·p/t⌉`, coefficient by coefficient (OpenFHE's `TimesQovert` on a plaintext stored in
`[0, t)`: `(Q·p + [−Q·p]_t)/t`). -/
def ceilScale {N : ℕ} (t Q : ℕ) (p : IntPoly N) : IntPoly N :=
  ⟨fun i => -((-((Q : ℤ) * p.coeff i)) / (t : ℤ))⟩

/-- **Plaintext addition or subtraction (`f`) by the declared method** at modulus `Q`, of the
stored plaintext `c` (module docstring). -/
def libPlain (x : InputBFV) (Q : ℕ) (f : IntPoly x.P.src.N → IntPoly x.P.src.N → IntPoly x.P.src.N)
    (ca : List (IntPoly x.P.src.N)) (c : IntPoly x.P.src.N) : List (IntPoly x.P.src.N) :=
  match x.plainAdd with
  | some .rounded => Challenge.Source.padZip f ca [scaleUp x.P.src.t Q (centered (ofInt Q c))]
  | some .scaled => Challenge.Source.padZip f ca [ceilScale x.P.src.t Q (centered (ofInt Q c))]
  | _ => Challenge.Source.padZip f ca [((Q / x.P.src.t : ℕ) : ℤ) • c]

/-- **The declared technique's multiplication** of `ca` and `cb` at level `ℓ`, instruction `n`,
with the binary64 sums in the arithmetic `A`. -/
def libMul (x : InputBFV) (A : Spec.Float.Arith) (n ℓ : ℕ) (ca cb : List (IntPoly x.P.src.N)) :
    List (IntPoly x.P.src.N) :=
  let t := x.P.src.t
  let qs := x.P.src.qs.take ℓ
  match x.mul with
  | some (.hps R) => Fl.hpsMul (Fl.floatSums A) t qs R ca cb
  | some (.poverq Ps) => Fl.poverqMul (Fl.floatSums A) t qs (Ps.take ℓ) ca cb
  | some (.leveled Ps) =>
    if ℓ = x.P.src.qs.length ∧ x.drops.getD n 0 ≠ 0 then
      Fl.leveledMul (Fl.floatSums A) t qs Ps (x.drops.getD n 0) ca cb
    else Fl.poverqMul (Fl.floatSums A) t qs (Ps.take ℓ) ca cb
  | some (.behz B msk mt) => behzMul t qs B msk mt ca cb
  | _ => bfvMul t (x.P.src.modulus ℓ) ca cb

/-- **`RelinearizeCore`** at level `ℓ`, instruction `n`, with the keys `keys` (three components:
relinearization; two: key switch): under `HPSPOVERQLEVELED` at the top level, the scaling with
the declared drop around the transcribed key switch at the reduced level; otherwise the
transcribed key switch at `ℓ`. -/
def libKS (x : InputBFV) (A : Spec.Float.Arith) (n ℓ : ℕ) (ca : List (IntPoly x.P.src.N))
    (keys : List (IntPoly x.P.src.N × IntPoly x.P.src.N)) : List (IntPoly x.P.src.N) :=
  let dr := x.drops.getD n 0
  let plain := if ca.length = 3 then relinBFV x.P x.lay ℓ ca keys
    else keySwitchBFV x.P x.lay ℓ ca keys
  match x.mul with
  | some (.leveled _) =>
    if ℓ = x.P.src.qs.length then
      Fl.leveledKS (Fl.floatSums A) (x.P.src.qs.take ℓ) dr (fun c => ksBFV x.P x.lay (ℓ - dr) c keys)
        ca
    else plain
  | _ => plain

/-- **A key switch of an operand under the key `g`**: OpenFHE's rotation by `g` (key switch with
the keys stored for `g`, then `σ_g`) of the operand rotated back by `σ_g⁻¹`. -/
def libKeySwitch (x : InputBFV) (A : Spec.Float.Arith) (n ℓ g : ℕ)
    (ca : List (IntPoly x.P.src.N)) (keys : List (IntPoly x.P.src.N × IntPoly x.P.src.N)) :
    List (IntPoly x.P.src.N) :=
  (libKS x A n ℓ (ca.map (automorph (rotInv x.P.src.N g))) keys).map (automorph g)

/-- **What the library computes at instruction `n`**, `i`, in front of the (message-independent)
environment `ρ` and the ciphertexts `σ` (module docstring). An undefined operand reads as no
component. -/
def libStep (x : InputBFV) (A : Spec.Float.Arith)
    (rk : List (IntPoly x.P.src.N × IntPoly x.P.src.N))
    (gk : ℕ → List (IntPoly x.P.src.N × IntPoly x.P.src.N)) (n : ℕ) (ρ : Env x.P.src)
    (σ : Trace.CtEnv x.P) (i : Instr) : List (IntPoly x.P.src.N) :=
  let get := fun v => (σ v).getD []
  let ℓ := levelOf ρ (operand i)
  let Q := x.P.src.modulus ℓ
  match i with
  | .add _ a b => Challenge.Source.padZip (· + ·) (get a) (get b)
  | .sub _ a b => Challenge.Source.padZip (· - ·) (get a) (get b)
  | .addPlain _ a p => libPlain x Q (· + ·) (get a) ((get p).headD 0)
  | .subPlain _ a p => libPlain x Q (· - ·) (get a) ((get p).headD 0)
  | .mulPlain _ a p => (get a).map (((get p).headD 0) * ·)
  | .mul _ a b => libMul x A n ℓ (get a) (get b)
  | .square _ a => libMul x A n ℓ (get a) (get a)
  | .mulConst _ a c => (get a).map (c • ·)
  | .copy _ a | .toEval _ a | .toCoeff _ a => get a
  | .automorph _ a g => (get a).map (automorph g)
  | .relin _ a => libKS x A n ℓ (get a) rk
  | .keySwitch _ a =>
    let g := ((ρ a).map (·.key)).getD 1
    libKeySwitch x A n ℓ g (get a) (gk g)
  | .modSwitch _ a => (get a).map (bfvModSwitchComp x.P.src.qs[ℓ - 1]!)
  | .dropLimbs .. => []

/-- The execution of a body from instruction `n` on, in front of `ρ` and `σ`; it stops at the
first instruction `Source.step` rejects. -/
def runLibraryAux (x : InputBFV) (A : Spec.Float.Arith)
    (rk : List (IntPoly x.P.src.N × IntPoly x.P.src.N))
    (gk : ℕ → List (IntPoly x.P.src.N × IntPoly x.P.src.N)) :
    ℕ → List Instr → Env x.P.src → Trace.CtEnv x.P → Trace.CtEnv x.P
  | _, [], _, σ => σ
  | n, i :: is, ρ, σ =>
    match step x.P.src ρ i with
    | some ρ' => runLibraryAux x A rk gk (n + 1) is ρ' (σ.set (Trace.dst i) (libStep x A rk gk n ρ σ i))
    | none => σ

/-- **`runLibrary x A rk gk cts`**: the ciphertexts at the end of the library's execution of the
program on the input ciphertexts `cts` (module docstring). -/
def runLibrary (x : InputBFV) (A : Spec.Float.Arith)
    (rk : List (IntPoly x.P.src.N × IntPoly x.P.src.N))
    (gk : ℕ → List (IntPoly x.P.src.N × IntPoly x.P.src.N))
    (cts : Var → List (IntPoly x.P.src.N)) : Trace.CtEnv x.P :=
  runLibraryAux x A rk gk 0 x.prog.body (initEnv x.P.src x.prog fun _ => .exact 0)
    (Trace.initCt x.P x.prog cts)

/-! ## The key switch at the certified budget, instruction by instruction -/

/-- **OpenFHE's relinearization (`RelinearizeCore` with the transcribed key switch, and under
`HPSPOVERQLEVELED` at the top level the declared drop) meets the `relin` contract** within the
budget of the instruction, from one relinearization key set generated at the top level. `Conforms
A` is needed only for a nonzero drop (with drop `0` the scaling rounds nothing). -/
theorem certifyBFV?_libRelin (x : InputBFV) (c : CertificateBFV) (h : certifyBFV? x = some c)
    (A : Spec.Float.Arith) (n : ℕ)
    (hA : (∃ Ps, x.mul = some (.leveled Ps)) → x.drops.getD n 0 ≠ 0 → Spec.Float.Conforms A)
    (s : IntPoly x.P.src.N) (hs : SecretOK x.P.secretBound s)
    (rk : List (IntPoly x.P.src.N × IntPoly x.P.src.N))
    (hrk : Budget.GadgetKeysOK x.P x.lay x.P.src.qs.length .square s rk)
    (msgs : Var → Msg x.P.src.t x.P.src.N) (cts : Var → List (IntPoly x.P.src.N))
    (hin : TraceBFV.InputsOK x.P s x.prog msgs cts) (d a : Var) (ρ ρ' : Env x.P.src)
    (hat : AtInstr x msgs n (.relin d a) ρ) (σ : Trace.CtEnv x.P) (xa : Val x.P.src)
    (ca : List (IntPoly x.P.src.N))
    (hstep : step x.P.src ρ (.relin d a) = some ρ') (hx : ρ a = some xa) (ha : σ a = some ca)
    (hla : ca.length = xa.parts) (h1 : 1 ≤ xa.level) (hL : xa.level ≤ x.P.src.qs.length) :
    TraceBFV.StepOK x.P (c.budget n) s ρ ρ' σ (σ.set d (libKS x A n xa.level ca rk))
      (.relin d a) := sorry

/-- **OpenFHE's rotation, read as the key switch of an operand under the key `g`, meets the
`keySwitch` contract** within the budget of the instruction, from the rotation keys stored for
`g` (gadget keys for `s'` with `σ_g(s') = s` and the target `σ_g(s')`, generated at the top
level). -/
theorem certifyBFV?_libKeySwitch (x : InputBFV) (c : CertificateBFV) (h : certifyBFV? x = some c)
    (A : Spec.Float.Arith) (n : ℕ)
    (hA : (∃ Ps, x.mul = some (.leveled Ps)) → x.drops.getD n 0 ≠ 0 → Spec.Float.Conforms A)
    (s : IntPoly x.P.src.N) (hs : SecretOK x.P.secretBound s)
    (msgs : Var → Msg x.P.src.t x.P.src.N) (cts : Var → List (IntPoly x.P.src.N))
    (hin : TraceBFV.InputsOK x.P s x.prog msgs cts) (d a : Var) (ρ ρ' : Env x.P.src)
    (hat : AtInstr x msgs n (.keySwitch d a) ρ) (σ : Trace.CtEnv x.P) (xa : Val x.P.src)
    (ca : List (IntPoly x.P.src.N))
    (hstep : step x.P.src ρ (.keySwitch d a) = some ρ') (hx : ρ a = some xa) (ha : σ a = some ca)
    (hla : ca.length = xa.parts) (hodd : xa.key % 2 = 1) (h1 : 1 ≤ xa.level)
    (hL : xa.level ≤ x.P.src.qs.length)
    (s' : IntPoly x.P.src.N) (hs' : automorph xa.key s' = s)
    (keys : List (IntPoly x.P.src.N × IntPoly x.P.src.N))
    (hkeys : Budget.GadgetKeysOK x.P x.lay x.P.src.qs.length (.galois xa.key) s' keys) :
    TraceBFV.StepOK x.P (c.budget n) s ρ ρ' σ
      (σ.set d (libKeySwitch x A n xa.level xa.key ca keys)) (.keySwitch d a) := sorry

/-! ## The composition -/

/-- **OpenFHE's algorithms, composed, stay within the certified bounds.** If `certifyBFV?`
accepts `x`, then for every secret within `secretBound`, every top-level relinearization key set
`rk` and rotation key sets `gk g` (for `(s', σ_g(s'))`, `σ_g(s') = s`), all inputs meeting
`InputsOK`, and every arithmetic `A` conforming to the binary64 model when the certificate records
`binary64`, the library's execution `runLibrary x A rk gk cts` is a run of the program within
`c.budget`: by `certifyBFV?_sound` its outputs decrypt with `s` to the messages the program
computes, with noise at most their certified bounds. The remaining hypothesis (`hid`) is in the
module docstring. -/
theorem certifyBFV?_library_run (x : InputBFV) (c : CertificateBFV) (h : certifyBFV? x = some c)
    (hid : AssumptionBFV.idealised ∉ c.assumed)
    (A : Spec.Float.Arith) (hA : AssumptionBFV.binary64 ∈ c.assumed → Spec.Float.Conforms A)
    (s : IntPoly x.P.src.N) (hs : SecretOK x.P.secretBound s)
    (rk : List (IntPoly x.P.src.N × IntPoly x.P.src.N))
    (hrk : Budget.GadgetKeysOK x.P x.lay x.P.src.qs.length .square s rk)
    (gk : ℕ → List (IntPoly x.P.src.N × IntPoly x.P.src.N))
    (hgk : ∀ g s', g % 2 = 1 → automorph g s' = s →
      Budget.GadgetKeysOK x.P x.lay x.P.src.qs.length (.galois g) s' (gk g))
    (msgs : Var → Msg x.P.src.t x.P.src.N) (cts : Var → List (IntPoly x.P.src.N))
    (hin : TraceBFV.InputsOK x.P s x.prog msgs cts) :
    TraceBFV.RunAt x.P c.budget s 0 x.prog.body (initEnv x.P.src x.prog msgs)
      (Trace.initCt x.P x.prog cts) (runLibrary x A rk gk cts) := sorry

/-- **Hence every output of the library's execution decrypts correctly**: `certifyBFV?_sound`
applied to `runLibrary` (same hypotheses as `certifyBFV?_library_run`). -/
theorem certifyBFV?_library_decrypts (x : InputBFV) (c : CertificateBFV)
    (h : certifyBFV? x = some c) (hid : AssumptionBFV.idealised ∉ c.assumed)
    (A : Spec.Float.Arith) (hA : AssumptionBFV.binary64 ∈ c.assumed → Spec.Float.Conforms A)
    (s : IntPoly x.P.src.N) (hs : SecretOK x.P.secretBound s)
    (rk : List (IntPoly x.P.src.N × IntPoly x.P.src.N))
    (hrk : Budget.GadgetKeysOK x.P x.lay x.P.src.qs.length .square s rk)
    (gk : ℕ → List (IntPoly x.P.src.N × IntPoly x.P.src.N))
    (hgk : ∀ g s', g % 2 = 1 → automorph g s' = s →
      Budget.GadgetKeysOK x.P x.lay x.P.src.qs.length (.galois g) s' (gk g))
    (msgs : Var → Msg x.P.src.t x.P.src.N) (cts : Var → List (IntPoly x.P.src.N))
    (hin : TraceBFV.InputsOK x.P s x.prog msgs cts) :
    ∃ ρ, Source.eval x.P.src x.prog msgs = some ρ ∧
      ∀ o ∈ x.prog.outputs, ∃ v ct m B, ρ o = some v ∧ runLibrary x A rk gk cts o = some ct ∧
        c.outputs.lookup o = some B ∧ Encrypts x.P s B v ct ∧ v.msg = .exact m ∧ v.key = 1 ∧
        bfvDecrypt x.P.src.t s (ct.map (ofInt (x.P.src.modulus v.level))) = m := sorry

end Challenge.CertifyBFV
