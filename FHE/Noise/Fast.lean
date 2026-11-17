import Std.Data.TreeMap
import Challenge.Certify.Defs

/-!
# FHE.Noise.Fast — the BGV analysis and certificate decision in near-linear time
(UNTRUSTED, audited as part of the holes)

`Challenge.Headline.refAnalyze` keeps its two environments (values, bounds) as functions: every
instruction wraps the previous environment in one more closure, so a lookup costs time linear in
the number of earlier instructions and the analysis is quadratic in the program length.
`Challenge.Certify.certify?` moreover runs it once for the whole program and once for every
output, and `Spec.Encrypt.certOK?` evaluates the program again for every output.

Here the environments are balanced search trees (`Std.TreeMap` on variable names, compared with
`compare`), and the body is run **once**:

* `runBody` calls the locked `Source.step` and `Challenge.Headline.refBound` themselves, on lookup
  functions backed by the trees; `step` changes only the destination of the instruction, whose
  new value is read back and stored;
* `analyze` is `refAnalyze`; `certify` is `certify?`, with the per-output bounds, keys and
  levels read from the final environments of that one run, and the name lookups of
  `Spec.Encrypt.freshOK?` (input names, declared bounds, the list of fresh inputs) done in trees.

Nothing here is trusted: `Challenge.Fast` states, and `Validation.Fast` proves, that both
functions are **equal** to the locked ones on every input. Everything is structural recursion on
lists and `Std.TreeMap` (no hashing, which the kernel cannot evaluate on strings), so closed
instances still reduce in the kernel.

Cost: `O((n + inputs + outputs) · log(n + inputs))` tree operations and string comparisons for
`n` instructions, plus the arithmetic of `refBound` on the bounds themselves.
-/

namespace FHE.Noise.Fast
open Spec Spec.Source Spec.Budget Spec.Encrypt Spec.Certify Challenge.Headline
open Challenge.Corpus (addProg)

/-- A finite map on variable names. -/
abbrev VMap (α : Type) : Type := Std.TreeMap Var α

/-- The map sending `key a` to `val a` for the **first** `a` of the list with that key (as
`List.find?` reads a list of declarations). -/
def mapOf {α β : Type} (key : α → Var) (val : α → β) (l : List α) : VMap β :=
  l.foldr (fun a m => m.insert (key a) (val a)) ∅

/-- The declared bounds: `prog.boundOf x = (boundMap prog)[x]?`. -/
def boundMap (prog : Program) : VMap ℕ := mapOf (·.1) (·.2) prog.bounds

/-- `Source.initEnv` on all-zero messages. -/
def initEnvMap (Pr : Params) (prog : Program) : VMap (Val Pr) :=
  mapOf (·.name) (fun d => { msg := .exact 0, parts := d.parts, level := d.level, key := d.key,
                              scale := d.scale }) prog.inputs

/-- The initial bounds of `refAnalyze`: the declared bound if smaller than the input noise. -/
def initBoundMap (P : FullParams) (prog : Program) : VMap ℕ :=
  let bm := boundMap prog
  mapOf (·.name) (fun d => match bm[d.name]? with
    | some b => min b P.inputNoise
    | none => P.inputNoise) prog.inputs

/-- The moduli `Q_ℓ = q₀⋯q_{ℓ−1}` of the levels `0, …, L`, computed once (the reference recomputes
the product at every instruction). -/
def modsOf (P : FullParams) : Array ℕ :=
  ((List.range (P.src.qs.length + 1)).map P.src.modulus).toArray

/-- `P.src.modulus ℓ`, read from the table (`Validation.Fast.Aux.modAt_modsOf`). -/
def modAt (P : FullParams) (mods : Array ℕ) (ℓ : ℕ) : ℕ :=
  match mods[ℓ]? with
  | some q => q
  | none => P.src.modulus ℓ

/-- `Challenge.Headline.refRun` with the environments in trees; `Q ℓ` is the modulus at level `ℓ`
(`P.src.modulus ℓ`, from a table). -/
def runBody (P : FullParams) (E : Trace.Budget) (Q : ℕ → ℕ) :
    List Instr → VMap (Val P.src) → VMap ℕ → Option (VMap (Val P.src) × VMap ℕ)
  | [], ρ, β => some (ρ, β)
  | i :: is, ρ, β => do
    let ρ' ← step P.src (fun x => ρ[x]?) i
    let b ← refBound P E (fun x => ρ[x]?) (fun x => β[x]?) i
    let v ← ρ' (Trace.dst i)
    guard (2 * b < Q v.level)
    runBody P E Q is (ρ.insert (Trace.dst i) v) (β.insert (Trace.dst i) b)

/-- The part of `refAnalyze` that does not depend on the outputs: the scheme, the input
declarations and the run of the body. -/
def run (P : FullParams) (E : Trace.Budget) (prog : Program) :
    Option (VMap (Val P.src) × VMap ℕ) := do
  guard (P.src.kind = .bgv)
  guard (prog.inputs.all fun d => d.ok P.src)
  runBody P E (modAt P (modsOf P)) prog.body (initEnvMap P.src prog) (initBoundMap P prog)

/-- The part of `refAnalyze` that reads the outputs from the final environments. -/
def outBound {Pr : Params} (r : VMap (Val Pr) × VMap ℕ) (outputs : List Var) : Option ℕ := do
  guard (outputs.all fun o => (r.1[o]?).isSome)
  let bs ← outputs.mapM fun o => r.2[o]?
  pure (bs.foldl max 0)

/-- **The fast BGV analyzer**: equal to `Challenge.Headline.refAnalyze`
(`Challenge.Fast.analyzeFast_eq`). -/
def analyze : NoiseAnalyzer := fun P E prog => do
  let r ← run P E prog
  outBound r prog.outputs

/-- `Spec.Encrypt.certOK?` on the program with `o` as its only output, read from the final
environment: the output is under the Galois element 1, and, if `switched`, the switched
decryption is exact at its level. -/
def certOK (P : FullParams) (r : VMap (Val P.src) × VMap ℕ) (o : Var) (b : ℕ)
    (switched : Bool) : Bool :=
  ((r.1[o]?).map (·.key) == some 1) &&
    (!switched || match r.1[o]? with
      | some v => Decrypt.decryptOK? P.src v.level b
      | none => false)

/-- `Challenge.Certify.outputBound?`, from the final environments of the one run. -/
def outputBound (P : FullParams) (r : VMap (Val P.src) × VMap ℕ) (switched : Bool) (o : Var) :
    Option ℕ := do
  let b ← outBound r [o]
  guard (certOK P r o b switched)
  pure b

/-- `Challenge.Certify.inputsMsgOK?` with the moduli from the table and the declared bounds from
the tree. -/
def inputsMsgOK (P : FullParams) (prog : Program) : Bool :=
  let mods := modsOf P
  let bm := boundMap prog
  prog.inputs.all fun d => decide (P.src.t < modAt P mods d.level) &&
    (bm[d.name]?).all fun b => decide (P.src.t / 2 ≤ b)

/-- `Challenge.Certify.checked?` with one run of the body. -/
def checked (P : FullParams) (lay : KSLayout) (prog : Program) (switched : Bool) :
    Option (ℕ × List (Var × ℕ)) := do
  guard (schemeParamsOK? P)
  guard (specialOK? P)
  guard (layoutOK? P lay)
  guard (keysRestrict? P)
  guard (!prog.outputs.isEmpty)
  guard (inputsMsgOK P prog)
  let r ← run P (certified P lay) prog
  let B ← outBound r prog.outputs
  let outs ← prog.outputs.mapM fun o => (outputBound P r switched o).map fun b => (o, b)
  pure (B, outs)

/-- `Spec.Encrypt.freshOK?` with the name lookups in trees. -/
def freshOK (P : FullParams) (prog : Program) (fresh : List Var) : Bool :=
  let names : VMap Unit := mapOf (·.name) (fun _ => ()) prog.inputs
  let fs : VMap Unit := mapOf (fun x => x) (fun _ => ()) fresh
  let bm := boundMap prog
  !fresh.isEmpty && (fresh.all fun x => (names[x]?).isSome) &&
  prog.inputs.all fun d =>
    if (fs[d.name]?).isSome then
      d.parts == 2 && d.key == 1 && (bm[d.name]?).isNone &&
        decide (2 * P.inputNoise < P.src.modulus d.level)
    else
      d.parts == 1 &&
        match bm[d.name]? with
        | some b => decide (b ≤ P.inputNoise)
        | none => false

/-- **The fast BGV certificate decision**: equal to `Challenge.Certify.certify?`
(`Challenge.Fast.certifyFast_eq`). The same text as `certify?`, with `checked` for `checked?`
and `freshOK` for `freshOK?`. -/
def certify (x : Input) : Option Certificate :=
  if x.msMethod ≠ .centred then none else
  match x.mode with
  | .worstCase => do
    let (B, outs) ← checked x.P x.lay x.prog x.switched
    pure ⟨x.P, certified x.P x.lay, .declared, 0, 0, B, outs⟩
  | .fresh fresh Bp Bk Bu B1 B2 mn md κ => do
    guard (0 < varProxy x.P.src.N x.P.secretBound Bk Bu B1 B2)
    guard (0 < md)
    let (ε, used, drift) := freshEps x.P fresh.length Bk Bu B1 B2 mn md κ
    let P' : FullParams := { x.P with inputNoise := freshNoise x.P.src.t Bp ε }
    guard (freshOK P' x.prog fresh)
    let (B, outs) ← checked P' x.lay x.prog x.switched
    pure ⟨P', certified P' x.lay, used, ε, drift, B, outs⟩
  | .freshL2 fresh Bp E2 S2 Vu V1 V2 mn md κ => do
    guard (0 < varProxyL2 E2 S2 Vu V1 V2)
    guard (0 < md)
    let drift := meanDrift (E2 + 1 + S2) mn md
    let ε := epsFor (varProxyL2 E2 S2 Vu V1 V2) (fresh.length * (2 * x.P.src.N)) κ + drift
    let P' : FullParams := { x.P with inputNoise := freshNoise x.P.src.t Bp ε }
    guard (freshOK P' x.prog fresh)
    let (B, outs) ← checked P' x.lay x.prog x.switched
    pure ⟨P', certified P' x.lay, .freshKappaL2, ε, drift, B, outs⟩

-- Compiled evaluation against the reference, on the corpus of `Challenge.Headline.Defs`.
#guard analyze FullParams.tinyBGV noBudget addProg == refAnalyze FullParams.tinyBGV noBudget addProg
#guard analyze .exampleBGV31 noBudget addMulProg == some (2 ^ 57)
#guard analyze .exampleBGV31 (Budget.certified .exampleBGV31 (Budget.uniformLayout 1)) mulSwitchProg
  == none
#guard analyze FullParams.tinyBGV (Budget.certified FullParams.tinyBGV (Budget.uniformLayout 1)) mulSwitchProg
  == some 179
#guard analyze FullParams.tinyBGV noBudget
  { inputs := [⟨"a", 2, 2, 1, 1⟩, ⟨"p", 1, 2, 1, 1⟩, ⟨"p", 1, 2, 1, 1⟩],
    bounds := [("p", 8), ("p", 1)], body := [.mulPlain "c" "a" "p"], outputs := ["c"] }
  == some 2048

end FHE.Noise.Fast
