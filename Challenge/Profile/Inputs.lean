import Challenge.Profile.Tool
import Challenge.Params

/-!
# Challenge.Profile.Inputs — every accepted program has inputs for every message   (LOCKED statements; proofs in `Validation/Profile/Inputs.lean`)

The soundness statements (`certifyProfile?_sound`, `certifyBFVProfile?_sound`,
`Challenge.Certify.certify?_sound`, `Challenge.CertifyBFV.certifyBFV?_sound`) assume input
ciphertexts meeting the input hypotheses (`Spec.Correct.InputsOK` and `Spec.Trace.BoundsOK` for
BGV, `Spec.TraceBFV.InputsOK` for BFV). The statements here say that for EVERY program a decision
accepts, for every secret and every assignment of messages, such inputs exist, with no further
hypothesis: the certificates are never about an empty set of inputs.

* **What makes this true** is one check in each decision: `Challenge.Certify.inputsMsgOK?` (BGV,
  in `certifyProfile?` and `Challenge.Certify.checked?`): every input's level has a modulus above
  `t`, and every declared bound of an input is at least `⌊t/2⌋`;
  `Challenge.CertifyBFV.plainBoundsOK` (BFV, in `certifyBFVProfile?` and
  `Challenge.CertifyBFV.checksOK`): every plaintext input's bound is at least `⌊t/2⌋` (a BFV input
  ciphertext's bound already passes the decryption condition, and the encoding condition
  `t − 1 ≤ ⌊q₀/2⌋` already puts every level's modulus above `t`). `certifyProfile?_inputs_checked`,
  `certifyBFVProfile?_plain_checked`: acceptance gives these conditions.
* **The checks are the weakest per declaration.** With a declared bound `b < ⌊t/2⌋`, the message
  `⌊t/2⌋` has no encryption (BGV) or plaintext (BFV, the same phase condition) within `b`
  (`Challenge.Params.bgv_small_noise_excludes`). At a level whose modulus `Q > 0` has
  `⌊Q/2⌋ < ⌊t/2⌋` (every odd `Q < t`), the message `⌊t/2⌋` has no BGV encryption within ANY bound
  (`bgv_low_level_excludes`, for `N > 0`); for `Q < t` some message has none, since the centred
  phase takes at most `Q` values modulo `t`. Before these checks the decisions accepted such
  programs; the `#guard`s below show them rejected now.
* The witness is the ciphertext whose first component is the centred message and whose other
  components are zero: its phase does not depend on the secret or the Galois key.
-/

namespace Challenge.ProfileInputs
open Spec NPoly Scheme Source Correct Challenge.Profile

/-! ## What acceptance checks -/

/-- **Acceptance by `certifyProfile?` gives the input conditions**: every input's level has a
modulus above `t`, and every declared bound of an input is at least `⌊t/2⌋`. -/
theorem certifyProfile?_inputs_checked (P : FullParams) (E : Trace.Budget) (prog : Program)
    (sw : Bool) (B : ℕ) (outs : List (Var × ℕ)) (h : certifyProfile? P E prog sw = some (B, outs))
    (d : Decl) (hd : d ∈ prog.inputs) :
    P.src.t < P.src.modulus d.level ∧ ∀ b, prog.boundOf d.name = some b → P.src.t / 2 ≤ b :=
  sorry

/-- **Acceptance by `certifyBFVProfile?` gives the plaintext condition**: every plaintext input's
bound is at least `⌊t/2⌋`. -/
theorem certifyBFVProfile?_plain_checked (P : FullParams) (E : ℕ → TraceBFV.Budget)
    (prog : Program) (B : ℕ) (outs : List (Var × ℕ))
    (h : certifyBFVProfile? P E prog = some (B, outs)) (d : Decl) (hd : d ∈ prog.inputs)
    (hp : d.parts = 1) : P.src.t / 2 ≤ TraceBFV.inputBound P prog d := sorry

/-! ## The inputs exist, unconditionally -/

/-- **The BGV input hypotheses are satisfiable for every accepted program, every secret and every
message.** -/
theorem certifyProfile?_inputs_exist_all (P : FullParams) (E : Trace.Budget) (prog : Program)
    (sw : Bool) (B : ℕ) (outs : List (Var × ℕ)) (h : certifyProfile? P E prog sw = some (B, outs))
    (s : IntPoly P.src.N) (m : Var → Poly P.src.t P.src.N) :
    ∃ cts, InputsOK P s prog (fun x => .exact (m x)) cts ∧
      Trace.BoundsOK P s prog (fun x => .exact (m x)) cts := sorry

/-- **The same for the default-mode BGV decision `certify?`**, at the parameters it analyses. -/
theorem certify?_inputs_exist (x : Certify.Input) (c : Certify.Certificate)
    (h : Challenge.Certify.certify? x = some c) (s : IntPoly c.params.src.N)
    (m : Var → Poly c.params.src.t c.params.src.N) :
    ∃ cts, InputsOK c.params s x.prog (fun y => .exact (m y)) cts ∧
      Trace.BoundsOK c.params s x.prog (fun y => .exact (m y)) cts := sorry

/-- **The BFV input hypothesis is satisfiable for every accepted program, every secret and every
message.** -/
theorem certifyBFVProfile?_inputs_exist_all (P : FullParams) (E : ℕ → TraceBFV.Budget)
    (prog : Program) (B : ℕ) (outs : List (Var × ℕ))
    (h : certifyBFVProfile? P E prog = some (B, outs))
    (s : IntPoly P.src.N) (m : Var → Poly P.src.t P.src.N) :
    ∃ cts, TraceBFV.InputsOK P s prog (fun x => .exact (m x)) cts := sorry

/-- **The same for the BFV decision `certifyBFV?`.** -/
theorem certifyBFV?_inputs_exist (x : CertifyBFV.InputBFV) (c : CertifyBFV.CertificateBFV)
    (h : Challenge.CertifyBFV.certifyBFV? x = some c) (s : IntPoly x.P.src.N)
    (m : Var → Poly x.P.src.t x.P.src.N) :
    ∃ cts, TraceBFV.InputsOK x.P s x.prog (fun y => .exact (m y)) cts := sorry

/-! ## The checks cannot be weakened -/

/-- **No BGV encryption at a small modulus.** If the modulus `Q` of the value's level is positive
with `⌊Q/2⌋ < ⌊t/2⌋`, the constant message `⌊t/2⌋` has no encryption within any bound. -/
theorem bgv_low_level_excludes (P : FullParams) (hk : P.src.kind = .bgv) (hN : 0 < P.src.N)
    (ht : 2 ≤ P.src.t) (s : IntPoly P.src.N) (B : ℕ) (v : Val P.src)
    (hQ0 : 0 < P.src.modulus v.level) (hQ : P.src.modulus v.level / 2 < P.src.t / 2)
    (hm : v.msg = .exact (NPoly.const ((P.src.t / 2 : ℕ) : ZMod P.src.t)))
    (ct : List (IntPoly P.src.N)) : ¬ Encrypts P s B v ct := sorry

/-- Parameters with `t = 17` whose first prime is `13 < t` (`tinyBGV` otherwise, key noise 1 so
that the default-mode key-restriction check passes). -/
def lowFirstPrime : FullParams :=
  { { FullParams.tinyBGV with src := { kind := .bgv, N := 4, qs := [13, 786433], t := 17 } } with
    keyNoise := 1 }

/-- An input `u` at level 1 (modulus 13 < t) that no output reads. -/
def lowLevelProg : Program :=
  { inputs := [⟨"a", 2, 2, 1, 1⟩, ⟨"u", 2, 1, 1, 1⟩], body := [.copy "c" "a"], outputs := ["c"] }

/-- A declared input bound 3 < ⌊17/2⌋. -/
def smallBoundProg : Program :=
  { inputs := [⟨"a", 2, 2, 1, 1⟩], body := [.copy "c" "a"], outputs := ["c"],
    bounds := [("a", 3)] }

-- REJECTED (both were accepted before the input checks), by the profile decision and by `certify?`.
#guard schemeParamsOK? lowFirstPrime
#guard (certifyProfile? lowFirstPrime ⟨0, 0, 0, fun _ => 0⟩ lowLevelProg false).isNone
#guard (Challenge.Certify.certify? ⟨lowFirstPrime, Budget.uniformLayout 1 true, lowLevelProg,
  false, .worstCase, .centred⟩).isNone
#guard (certifyProfile? FullParams.tinyBGV ⟨0, 0, 0, fun _ => 0⟩ smallBoundProg false).isNone
#guard (Challenge.Certify.certify? ⟨FullParams.tinyBGV, Budget.uniformLayout 1 true,
  smallBoundProg, false, .worstCase, .centred⟩).isNone
-- Accepted with the bound raised to ⌊17/2⌋ = 8, and with `u` moved to level 2.
#guard (certifyProfile? FullParams.tinyBGV ⟨0, 0, 0, fun _ => 0⟩
  { smallBoundProg with bounds := [("a", 8)] } false).isSome
#guard (Challenge.Certify.certify? ⟨lowFirstPrime, Budget.uniformLayout 1 true,
  { lowLevelProg with inputs := [⟨"a", 2, 2, 1, 1⟩, ⟨"u", 2, 2, 1, 1⟩] }, false, .worstCase,
  .centred⟩).isSome

/-- A BFV plaintext input declared at bound `b`, added to a ciphertext at level 2 of `sealBFV`. -/
def plainProg (b : ℕ) : Program :=
  { inputs := [⟨"a", 2, 2, 3, 1⟩, ⟨"p", 1, 2, 3, 1⟩], body := [.addPlain "c" "a" "p"],
    outputs := ["c"], bounds := [("p", b)] }

-- BFV: REJECTED at plaintext bound 3 < ⌊65537/2⌋ (accepted before), accepted at ⌊65537/2⌋.
#guard (certifyBFVProfile? Challenge.BFV.sealBFV
  (fun _ => BudgetBFV.certified Challenge.BFV.sealBFV (Budget.uniformLayout 1))
  (plainProg 3)).isNone
#guard (Challenge.CertifyBFV.certifyBFV? ⟨Challenge.BFV.sealBFV,
  { Budget.uniformLayout 1 with canonical := true }, plainProg 3, some .textbook, false,
  some .delta, true, []⟩).isNone
#guard (Challenge.CertifyBFV.certifyBFV? ⟨Challenge.BFV.sealBFV,
  { Budget.uniformLayout 1 with canonical := true }, plainProg 32768, some .textbook, false,
  some .delta, true, []⟩).isSome

end Challenge.ProfileInputs
