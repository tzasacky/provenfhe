import Spec.MSB
import Challenge.Profile

/-!
# Challenge.MSB — the BGV results hold in MSB form   (LOCKED statements; proofs in `Validation/MSB.lean`)

`Spec.MSB` states BGV in the MSB form (phase `t⁻¹·p + e`, errors not multiplied by `t`), its
operations, and the t-reading `toLSB` (every component times `t`). These pins say that the
t-reading carries the MSB form onto the LSB form the certificates are about, so every BGV result
stated for `Spec.Trace` holds for an MSB implementation, with no library named.

1. **Decryption and noise** (`msbDecrypt_toLSB`, `msbDecrypt_iff`, `msbEncrypts_toLSB`,
   `toLSB_msbEncrypts`, `toLSB_encrypts_of_rep`, `msbEncryptsRep_toLSB`): MSB decryption of `ct` IS LSB decryption of
   `toLSB t ct` (no hypothesis). For noise, with `gcd(t, Q) = 1`: MSB noise `B` (the error
   alone) gives LSB noise `⌊t/2⌋ + t·B` (the whole phase `m̃ + t·e`, message included), and LSB
   noise `B'` gives MSB noise `⌊(B' + ⌊t/2⌋)/t⌋`; each direction needs the bound it produces to
   stay below `Q/2` (no wrap-around). For a phase `t⁻¹·p + e` with any representative `p` of the
   message (a library storing `p ∈ [0, t)`), the LSB noise is `‖p‖∞ + t·‖e‖∞`: for Lattigo's
   fresh secret-key encryptions `(t − 1) + 19·t`, the input noise of its profile (the centred
   reading would give `⌊t/2⌋ + 20·t`, since for `p > t/2` the centred error is `e + 1`).
2. **Keys** (`keyValidMSB_iff`, `gadgetKeysOK_iff`, `keyValidMSB_toLSB`, `gadgetKeys_restrict`):
   an MSB key with error at most `B` is exactly an LSB key (`Spec.Scheme.KeyValid`, BGV) at
   plaintext modulus `1` with key noise `B`; so MSB gadget keys are `Spec.Budget.GadgetKeysOK` at
   the parameters with `t := 1`, `keyNoise := B`. Their t-reading `(t·b, t·a)` is an LSB key with
   noise `t·B` (a multiple of `t`) **for the factor `t·gⱼ`** (`keyValidMSB_toLSB`), not the
   factor `gⱼ` that `Spec.Budget.gadgetReq` asks for, so the LSB realizability pins of
   `Challenge.Budget` (keys for `gadgetReq`) are not applied to it; and MSB key switching does
   not commute with the t-reading componentwise (it decomposes `c`, not `t·c`). Item 4 is
   therefore proved through the phase, by the integer core the LSB proofs share. One top-level MSB key
   set restricts to every level of a restricting layout when `2·B < Q_ℓ·P`.
3. **Steps** (`stepOK_toLSB`, `run_toLSB`): every MSB step meeting its MSB contract
   (`Spec.MSB.StepOK`) has a t-reading meeting the LSB contract (`Spec.Trace.StepOK`) **at the same
   budget**, for every instruction; so an MSB run is, read through `t`, an LSB run. No hypothesis
   on the parameters.
4. **The MSB algorithms meet their contracts** (`keySwitch_stepOK`, `relin_stepOK`,
   `rescale_stepOK`, `mulTensor_stepOK`; and with item 3 their t-readings meet the LSB
   contracts: `keySwitch_toLSB`, `relin_toLSB`, `rescale_toLSB`). MSB hybrid key switching on
   the digits of any usable layout (centred digits, centred ModDown, no `t`-correction) with MSB
   keys of error at most `B` meets
   the key-switching contract at every budget of at least `Spec.Budget.ksBoundAt P lay ℓ` when
   `t·B ≤ keyNoise` (centred or canonical layout alike: the centred MSB algorithm is within
   both). MSB rescaling of any number `k` of components meets the modulus-switching contract at
   every budget of at least `Spec.Budget.msBudgetAt P k`. These are the LSB budgets: the same
   profiles cover both forms. The MSB tensor product (first operand times `t`) meets the MSB
   product contract exactly.
5. **Certificates** (`certifyProfile?_sound_msb`): if `certifyProfile?` accepts at `E`, every
   output of every MSB run within `E` from MSB inputs with stored-representative bound `B_in`
   (within the input bounds and below `Q/2`) MSB-decrypts to what the program computes, and its
   t-reading has noise at most its certified bound.
   `Challenge.Profile.certifyProfile?_sound` pulled back along `toLSB`.

**What differs from the LSB pins.** The MSB key switch has no `t`-correction: its proof uses
`SpecialOK` only for `pⱼ ≥ 2` (not `gcd(t, pⱼ) = 1`, oddness, or coprimality with the `qᵢ`),
and its keys carry no `t ∣ e` clause; instead the key error `B` must satisfy `t·B ≤ keyNoise`
(Lattigo: `keyNoise = t·19`). The decryption correspondence needs `gcd(t, Q) = 1` only for the
noise (a `SchemeParamsOK` clause), not for decryption; item 3 needs nothing.

**What this does not say.** It is about phases, not about the plaintext scale an MSB library
tracks per ciphertext (Lattigo's `MetaData.Scale`): the message the t-reading decrypts to is the
message `Spec.Source.eval` computes (with its `q⁻¹ mod t` factors), and how a library's scale
relates to it is a separate bookkeeping statement (`Spec.Scaling` is OpenFHE's). It does not
cover the fused rotation of `Spec.MSB` (module docstring), BFV-style products, or the floating-
point exactness of the basis extension a library uses to compute the centred residues.
-/

namespace Challenge.MSB
open Spec NPoly Scheme Source Correct Spec.Budget Spec.MSB Challenge.Profile Challenge.Certify

/-! ## 1. Decryption and noise -/

/-- **MSB decryption is LSB decryption of the t-reading.** -/
theorem msbDecrypt_toLSB {N : ℕ} (t Q : ℕ) (s : IntPoly N) (ct : List (IntPoly N)) :
    msbDecrypt t s (ct.map (ofInt Q)) = bgvDecrypt t s ((toLSB t ct).map (ofInt Q)) := sorry

/-- An MSB ciphertext decrypts to `m` iff its t-reading does. -/
theorem msbDecrypt_iff {N : ℕ} (t Q : ℕ) (s : IntPoly N) (ct : List (IntPoly N))
    (m : Poly t N) :
    msbDecrypt t s (ct.map (ofInt Q)) = m ↔ bgvDecrypt t s ((toLSB t ct).map (ofInt Q)) = m :=
  sorry

/-- **MSB noise `B` is LSB noise `⌊t/2⌋ + t·B`**, when `gcd(t, Q) = 1`, `t > 0` and that bound
stays below `Q/2`. -/
theorem msbEncrypts_toLSB {N : ℕ} (t Q B : ℕ) (ht : 0 < t) (hcop : Nat.Coprime t Q)
    (hQ : 2 * (t / 2 + t * B) < Q) (s : IntPoly N) (ct : List (IntPoly N)) (m : Poly t N)
    (h : MSBEncrypts t B s (ct.map (ofInt Q)) m) :
    BGVEncrypts t (t / 2 + t * B) s ((toLSB t ct).map (ofInt Q)) m := sorry

/-- **LSB noise `B` of the t-reading is MSB noise `⌊(B + ⌊t/2⌋)/t⌋`**, when `gcd(t, Q) = 1`,
`t > 0` and that bound stays below `Q/2`. -/
theorem toLSB_msbEncrypts {N : ℕ} (t Q B : ℕ) (ht : 0 < t) (hcop : Nat.Coprime t Q)
    (hQ : 2 * ((B + t / 2) / t) < Q) (s : IntPoly N) (ct : List (IntPoly N)) (m : Poly t N)
    (h : BGVEncrypts t B s ((toLSB t ct).map (ofInt Q)) m) :
    MSBEncrypts t ((B + t / 2) / t) s (ct.map (ofInt Q)) m := sorry

/-- **Any stored representative.** If the phase of `ct` is `t⁻¹·p + e (mod Q)` with `p` any
representative of `m` (Lattigo stores `p ∈ [0, t)`), its t-reading encrypts `m` with LSB noise
`‖p‖∞ + t·‖e‖∞`, when `gcd(t, Q) = 1` and that stays below `Q/2`. -/
theorem toLSB_encrypts_of_rep {N : ℕ} (t Q : ℕ) (hcop : Nat.Coprime t Q) (s : IntPoly N)
    (ct : List (IntPoly N)) (m : Poly t N) (p e : IntPoly N)
    (hφ : phase (ofInt Q s) (ct.map (ofInt Q)) = (t : ZMod Q)⁻¹ • ofInt Q p + ofInt Q e)
    (hp : ofInt t p = m) (hQ : 2 * (normInf p + t * normInf e) < Q) :
    BGVEncrypts t (normInf p + t * normInf e) s ((toLSB t ct).map (ofInt Q)) m := sorry

/-- **A stored-representative MSB encryption with bound `B` has a t-reading with LSB noise at
most `B`**, when `gcd(t, Q) = 1` and `2·B < Q`. -/
theorem msbEncryptsRep_toLSB {N : ℕ} (t Q B : ℕ) (hcop : Nat.Coprime t Q) (hQ : 2 * B < Q)
    (s : IntPoly N) (ct : List (IntPoly N)) (m : Poly t N)
    (h : MSBEncryptsRep t B s (ct.map (ofInt Q)) m) :
    BGVEncrypts t B s ((toLSB t ct).map (ofInt Q)) m := sorry

/-! ## 2. Keys -/

/-- **An MSB key is an LSB key at plaintext modulus `1`.** -/
theorem keyValidMSB_iff {N : ℕ} (B : ℕ) (s : IntPoly N) (req : KeyReq N)
    (b a : Poly req.modulus N) :
    KeyValidMSB B s req b a ↔ KeyValid .bgv 1 B s req b a := sorry

/-- **MSB gadget keys are LSB gadget keys** at the parameters with `t := 1` and
`keyNoise := B`. -/
theorem gadgetKeysOK_iff (P : FullParams) (lay : KSLayout) (ℓ : ℕ) (tgt : KeyTarget) (B : ℕ)
    (s : IntPoly P.src.N) (keys : List (IntPoly P.src.N × IntPoly P.src.N)) :
    MSB.GadgetKeysOK P lay ℓ tgt B s keys ↔
      Budget.GadgetKeysOK { P with src := { P.src with t := 1 }, keyNoise := B } lay ℓ tgt s
        keys := sorry

/-- **The t-reading of an MSB key** with error at most `B` is an LSB key with noise `t·B` (a
multiple of `t`) for the factor `t·g`, when `2·t·B < M`. -/
theorem keyValidMSB_toLSB {N : ℕ} (t B M : ℕ) (hM : 2 * (t * B) < M) (s : IntPoly N)
    (g : ZMod M) (tgt : KeyTarget) (b a : IntPoly N)
    (h : KeyValidMSB B s ⟨M, const g, tgt⟩ (ofInt M b) (ofInt M a)) :
    KeyValid .bgv t (t * B) s ⟨M, const ((t : ZMod M) * g), tgt⟩
      ((t : ZMod M) • ofInt M b) ((t : ZMod M) • ofInt M a) := sorry

/-- **One top-level MSB key set serves every level** of a layout that restricts, when
`2·B < Q_ℓ·P`. -/
theorem gadgetKeys_restrict (P : FullParams) (lay : KSLayout) (tgt : KeyTarget)
    (hP : SchemeParamsOK P) (ℓ : ℕ) (hℓ : ℓ ≤ P.src.qs.length)
    (hlay : restrictsTo lay P.src.qs.length ℓ = true) (B : ℕ)
    (hB : 2 * B < P.src.modulus ℓ * specialProd P)
    (s : IntPoly P.src.N) (keys : List (IntPoly P.src.N × IntPoly P.src.N))
    (hkeys : MSB.GadgetKeysOK P lay P.src.qs.length tgt B s keys) :
    MSB.GadgetKeysOK P lay ℓ tgt B s (keys.take (lay.sizes ℓ).length) := sorry

/-! ## 3. Steps and runs -/

/-- **An MSB step is, read through `t`, an LSB step at the same budget.** -/
theorem stepOK_toLSB (P : FullParams) (E : Trace.Budget) (s : IntPoly P.src.N)
    (ρ ρ' : Env P.src) (σ σ' : Trace.CtEnv P) (i : Instr) (hstep : step P.src ρ i = some ρ')
    (h : MSB.StepOK P E s ρ ρ' σ σ' i) :
    Trace.StepOK P E s ρ ρ' (toLSBEnv P σ) (toLSBEnv P σ') i := sorry

/-- **An MSB run is, read through `t`, an LSB run at the same budget.** -/
theorem run_toLSB (P : FullParams) (E : Trace.Budget) (s : IntPoly P.src.N) (body : List Instr)
    (ρ : Env P.src) (σ σf : Trace.CtEnv P) (h : MSB.Run P E s body ρ σ σf) :
    Trace.Run P E s body ρ (toLSBEnv P σ) (toLSBEnv P σf) := sorry

/-! ## 4. The MSB algorithms -/

/-- **MSB key switching meets the MSB `keySwitch` contract within `ksBoundAt`.** The operand is
under `σ_g(s)`, `g` its recorded key; the MSB keys (error at most `B`, `t·B ≤ keyNoise`) are for
the target `σ_g(s)`. -/
theorem keySwitch_stepOK (P : FullParams) (lay : KSLayout) (hP : SchemeParamsOK P)
    (hS : SpecialOK P) (ℓ : ℕ) (hℓ : ℓ ≤ P.src.qs.length) (hlay : lay.okAt ℓ = true)
    (E : Trace.Budget) (hE : ksBoundAt P lay ℓ ≤ E.keySwitch) (B : ℕ)
    (hB : P.src.t * B ≤ P.keyNoise) (s : IntPoly P.src.N) (hs : SecretOK P.secretBound s)
    (ρ ρ' : Env P.src) (σ : Trace.CtEnv P) (d a : Var) (x : Val P.src)
    (ca : List (IntPoly P.src.N))
    (hstep : step P.src ρ (.keySwitch d a) = some ρ') (hx : ρ a = some x) (hca : σ a = some ca)
    (hl : x.level = ℓ) (hlen : ca.length = x.parts)
    (keys : List (IntPoly P.src.N × IntPoly P.src.N))
    (hkeys : MSB.GadgetKeysOK P lay ℓ (.galois x.key) B s keys) :
    MSB.StepOK P E s ρ ρ' σ (σ.set d (MSB.keySwitch P lay ℓ ca keys)) (.keySwitch d a) := sorry

/-- **MSB relinearization meets the MSB `relin` contract within `ksBoundAt`.** -/
theorem relin_stepOK (P : FullParams) (lay : KSLayout) (hP : SchemeParamsOK P)
    (hS : SpecialOK P) (ℓ : ℕ) (hℓ : ℓ ≤ P.src.qs.length) (hlay : lay.okAt ℓ = true)
    (E : Trace.Budget) (hE : ksBoundAt P lay ℓ ≤ E.keySwitch) (B : ℕ)
    (hB : P.src.t * B ≤ P.keyNoise) (s : IntPoly P.src.N) (hs : SecretOK P.secretBound s)
    (keys : List (IntPoly P.src.N × IntPoly P.src.N))
    (hkeys : MSB.GadgetKeysOK P lay ℓ .square B s keys)
    (ρ ρ' : Env P.src) (σ : Trace.CtEnv P) (d a : Var) (x : Val P.src)
    (ca : List (IntPoly P.src.N))
    (hstep : step P.src ρ (.relin d a) = some ρ') (hx : ρ a = some x) (hca : σ a = some ca)
    (hl : x.level = ℓ) (hlen : ca.length = x.parts) :
    MSB.StepOK P E s ρ ρ' σ (σ.set d (MSB.relin P lay ℓ ca keys)) (.relin d a) := sorry

/-- **MSB rescaling of any number of components meets the MSB `modSwitch` contract within
`msBudgetAt`.** -/
theorem rescale_stepOK (P : FullParams) (hP : SchemeParamsOK P) (E : Trace.Budget)
    (s : IntPoly P.src.N) (hs : SecretOK P.secretBound s) (ρ ρ' : Env P.src)
    (σ : Trace.CtEnv P) (d a : Var) (x : Val P.src) (ca : List (IntPoly P.src.N))
    (hE : msBudgetAt P x.parts ≤ E.modSwitchAt x.parts)
    (hstep : step P.src ρ (.modSwitch d a) = some ρ') (hx : ρ a = some x)
    (hca : σ a = some ca) (hlen : ca.length = x.parts) :
    MSB.StepOK P E s ρ ρ' σ (σ.set d (MSB.rescale P.src.qs[x.level - 1]! ca)) (.modSwitch d a) :=
  sorry

/-- **The MSB tensor product meets the MSB `mul` contract** (exactly: `ψ = t·ψ_a·ψ_b`), for two
two-component operands. -/
theorem mulTensor_stepOK (P : FullParams) (E : Trace.Budget) (s : IntPoly P.src.N)
    (ρ ρ' : Env P.src) (σ : Trace.CtEnv P) (d a b : Var) (x y : Val P.src)
    (ca cb : List (IntPoly P.src.N))
    (hstep : step P.src ρ (.mul d a b) = some ρ') (hx : ρ a = some x) (hy : ρ b = some y)
    (ha : σ a = some ca) (hb : σ b = some cb)
    (hla : ca.length = 2) (hlb : cb.length = 2) (h2x : x.parts = 2) (h2y : y.parts = 2) :
    MSB.StepOK P E s ρ ρ' σ (σ.set d (MSB.mulTensor P.src.t ca cb)) (.mul d a b) := sorry

/-- **The t-reading of MSB key switching meets the LSB `keySwitch` contract within
`ksBoundAt`** (the error is `t` times the MSB error: a multiple of `t`). -/
theorem keySwitch_toLSB (P : FullParams) (lay : KSLayout) (hP : SchemeParamsOK P)
    (hS : SpecialOK P) (ℓ : ℕ) (hℓ : ℓ ≤ P.src.qs.length) (hlay : lay.okAt ℓ = true)
    (E : Trace.Budget) (hE : ksBoundAt P lay ℓ ≤ E.keySwitch) (B : ℕ)
    (hB : P.src.t * B ≤ P.keyNoise) (s : IntPoly P.src.N) (hs : SecretOK P.secretBound s)
    (ρ ρ' : Env P.src) (σ : Trace.CtEnv P) (d a : Var) (x : Val P.src)
    (ca : List (IntPoly P.src.N))
    (hstep : step P.src ρ (.keySwitch d a) = some ρ') (hx : ρ a = some x) (hca : σ a = some ca)
    (hl : x.level = ℓ) (hlen : ca.length = x.parts)
    (keys : List (IntPoly P.src.N × IntPoly P.src.N))
    (hkeys : MSB.GadgetKeysOK P lay ℓ (.galois x.key) B s keys) :
    Trace.StepOK P E s ρ ρ' (toLSBEnv P σ)
      (toLSBEnv P (σ.set d (MSB.keySwitch P lay ℓ ca keys))) (.keySwitch d a) := sorry

/-- **The t-reading of MSB relinearization meets the LSB `relin` contract within
`ksBoundAt`.** -/
theorem relin_toLSB (P : FullParams) (lay : KSLayout) (hP : SchemeParamsOK P)
    (hS : SpecialOK P) (ℓ : ℕ) (hℓ : ℓ ≤ P.src.qs.length) (hlay : lay.okAt ℓ = true)
    (E : Trace.Budget) (hE : ksBoundAt P lay ℓ ≤ E.keySwitch) (B : ℕ)
    (hB : P.src.t * B ≤ P.keyNoise) (s : IntPoly P.src.N) (hs : SecretOK P.secretBound s)
    (keys : List (IntPoly P.src.N × IntPoly P.src.N))
    (hkeys : MSB.GadgetKeysOK P lay ℓ .square B s keys)
    (ρ ρ' : Env P.src) (σ : Trace.CtEnv P) (d a : Var) (x : Val P.src)
    (ca : List (IntPoly P.src.N))
    (hstep : step P.src ρ (.relin d a) = some ρ') (hx : ρ a = some x) (hca : σ a = some ca)
    (hl : x.level = ℓ) (hlen : ca.length = x.parts) :
    Trace.StepOK P E s ρ ρ' (toLSBEnv P σ)
      (toLSBEnv P (σ.set d (MSB.relin P lay ℓ ca keys))) (.relin d a) := sorry

/-- **The t-reading of MSB rescaling is the centred t-corrected modulus switch, in contract:** it
meets the LSB `modSwitch` contract within `msBudgetAt P k` for `k` components. -/
theorem rescale_toLSB (P : FullParams) (hP : SchemeParamsOK P) (E : Trace.Budget)
    (s : IntPoly P.src.N) (hs : SecretOK P.secretBound s) (ρ ρ' : Env P.src)
    (σ : Trace.CtEnv P) (d a : Var) (x : Val P.src) (ca : List (IntPoly P.src.N))
    (hE : msBudgetAt P x.parts ≤ E.modSwitchAt x.parts)
    (hstep : step P.src ρ (.modSwitch d a) = some ρ') (hx : ρ a = some x)
    (hca : σ a = some ca) (hlen : ca.length = x.parts) :
    Trace.StepOK P E s ρ ρ' (toLSBEnv P σ)
      (toLSBEnv P (σ.set d (MSB.rescale P.src.qs[x.level - 1]! ca))) (.modSwitch d a) := sorry

/-! ## 5. Certificates -/

/-- **Profile soundness in MSB form.** If `certifyProfile?` accepts at `E`, then for every
integer polynomial `s` as the secret, all messages and all MSB input ciphertexts with
stored-representative bound `Bin` (`Spec.MSB.MSBEncryptsRep`: `‖p‖∞ + t·‖e‖∞ ≤ Bin`, within the
input noise and every declared input bound, and below half the modulus of every input's level),
every output of every MSB run within `E` MSB-decrypts with `s` to what the program computes, and
its t-reading has LSB noise at most its bound in `outs`. -/
theorem certifyProfile?_sound_msb (P : FullParams) (E : Trace.Budget) (prog : Program)
    (sw : Bool) (B : ℕ) (outs : List (Var × ℕ)) (h : certifyProfile? P E prog sw = some (B, outs))
    (Bin : ℕ) (hBin : Bin ≤ P.inputNoise) (hbnd : ∀ x b, prog.boundOf x = some b → Bin ≤ b)
    (hwrap : ∀ d ∈ prog.inputs, 2 * Bin < P.src.modulus d.level)
    (s : IntPoly P.src.N) (msgs : Var → Msg P.src.t P.src.N)
    (cts : Var → List (IntPoly P.src.N)) (hin : MSB.InputsOK P s Bin prog msgs cts) :
    ∃ ρ, Source.eval P.src prog msgs = some ρ ∧
      ∀ σ, MSB.Run P E s prog.body (initEnv P.src prog msgs) (Trace.initCt P prog cts) σ →
        ∀ o ∈ prog.outputs, ∃ v ct m b, ρ o = some v ∧ σ o = some ct ∧
          outs.lookup o = some b ∧ v.msg = .exact m ∧ v.key = 1 ∧
          msbDecrypt P.src.t s (ct.map (ofInt (P.src.modulus v.level))) = m ∧
          BGVEncrypts P.src.t b s ((toLSB P.src.t ct).map (ofInt (P.src.modulus v.level))) m :=
  sorry

end Challenge.MSB
