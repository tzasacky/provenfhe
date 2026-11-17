# The trusted core: what the headline theorems claim, and where to attack them

Machine-checked proofs cannot be wrong, but they can prove a statement that says less than it
appears to. What a theorem says is fixed by its statement and by the definitions the statement
mentions, read transitively. This document lists the smallest such set for the headline theorems,
in an order a reader can follow, and records where a definition could be subtly wrong without any
proof failing.

The definitions were written with AI coding assistants and have not been reviewed by an independent expert; this document exists to make that review as cheap as possible.

All counts below are computed, not estimated: `paper/gen/trusted_core.lean` walks the statement of
each headline (its type; the bodies of every definition, inductive type and structure it reaches
in `Spec/` and `Challenge/`; not proofs, and not the statements of lemmas used inside proof terms)
and `paper/gen/trusted_core.py` writes `docs/trusted-core.json` with each declaration's file, line
range (Lean's declaration ranges, docstring included) and depth from the headline. Lines are
distinct source lines; an auxiliary constant (`f.match_1`) counts as its owner; a constructor or a
structure field counts as part of its structure. Lean core and Mathlib are outside the count.

| Headline group | Declarations | Lines | of which `Spec/` | `Challenge/` |
|---|---|---|---|---|
| H1 profile soundness (BGV, BFV) | 102 | 908 | 631 | 277 |
| H2 default-mode decision soundness | 202 | 1,741 | 1,099 | 642 |
| H3 security (fresh-only; evaluation on earlier results) | 160 | 1,354 | 925 | 429 |
| H4 BEHZ multiplication contract; MSB transfer | 106 | 850 | 630 | 220 |
| H1 ∪ H3 (the reading order of section 2) | 173 | 1,465 | 982 | 483 |
| H1 ∪ H3 without the bodies of the two profile decisions | 141 | 1,190 | 904 | 286 |
| H1 ∪ H2 (decisions and what they depend on) | 207 | 1,792 | 1,099 | 693 |
| All four | 308 | 2,575 | 1,546 | 1,029 |
| `certify?`, `certifyBFV?` and everything they call (no theorem) | 165 | 1,412 | 885 | 527 |

These counts differ from the `closure` field of `docs/audit-generic.json` (162 and 233 `Spec/`
declarations for `certify?_sound`) because that older count lists every auxiliary constant
separately, follows the statements of theorems met inside definitions, and counts `Spec/` only.

Mathlib notions the statements rely on directly: `ZMod n` (its ring structure, `ZMod.val`,
`ZMod.valMinAbs`, and its inverse, which Mathlib defines for non-units too), `Finset.univ`,
`Finset.sum` and `Finset.sup` over `Fin N`, `Nat.Prime` and (H2) `Nat.clog`, and, for H3 only, `MeasureTheory.Measure`,
`MeasurableSpace`, `MeasureTheory.ae` (almost everywhere), `IsFiniteMeasure`, `ENNReal`,
`ENNReal.toReal`, `Real` and `abs`. The ring `NPoly` is the project's own; `Challenge/Ring.lean`
proves it isomorphic to Mathlib's `R[X] ⧸ (X^N + 1)`.

## 1. What you are asked to believe

**H1, profile soundness.** `Challenge.Profile.certifyProfile?_sound` (`Challenge/Profile.lean:58`,
BGV) and `certifyBFVProfile?_sound` (`:69`, BFV). For any parameters `P`, any budget `E` (BGV: one
`Trace.Budget`; BFV: one `TraceBFV.Budget` per instruction position) and any program: if the
decision returns `some (B, outs)` (`h`), then for every integer polynomial `s` as the secret, all
messages `msgs` and all input ciphertexts `cts` that encrypt them under `s` within the input noise
(`hin : InputsOK`; BGV also `hb : Trace.BoundsOK`, the per-input declared bounds), the program
evaluates on the messages, and at the end of every ciphertext-level run in which each operation
meets its contract within `E`, every output is under `s`, has noise at most its bound in `outs`,
and decrypts with `s` to the message the program computes (`OutputsCertified`,
`OutputsCertifiedBFV`); for BGV with `sw = true`, it also decrypts by OpenFHE's switched routine to
that message times `decScale`. Nothing is assumed of `s` or of `E`. The decisions include one check per input declaration, `Challenge.Certify.inputsMsgOK?` (BGV) and `Challenge.CertifyBFV.plainBoundsOK` (BFV), without which some message would have no input ciphertext and the statement would be about no inputs for it (section 3, F4).

**H2, the default-mode decisions.** `Challenge.Certify.certify?_sound` (`Challenge/Certify.lean:311`),
`certify?_decrypts` (`:321`), `worst_certified` (`:333`), `Challenge.CertifyBFV.certifyBFV?_sound`
(`Challenge/CertifyBFV.lean:184`), `certifyBFV?_decrypts` (`:190`). The same conclusion (for
`_decrypts`, its decryption part) at the budget the decision computes from the parameters, with
hypotheses `h` (the decision returned the certificate `c`), `hin` and (BGV) `hb`; for BGV they are
stated at the certificate's parameters `c.params`, whose `inputNoise` the fresh-encryption modes
compute.

**H3, security.** For an abstract RNS BGV or BFV scheme `D` (no library), an evaluator `ev` and a
class `adm`: `Challenge.IndCpaDProfile.correct_bfv` (`Challenge/IndCpaD/Profile.lean:93`) gives
perfect correctness on the class from (i) `henc : D.EncOKBFV` (good keys and randomness give a
fresh two-component encryption with noise ≤ `eps`), (ii) `hev : EvalMeetsBFV` (for good keys, the
evaluator's outputs are those of some run within the circuit's profile) and (iii) `hadm` (the class
is inside the profile class). `bfv_prob_eq` (`:103`) adds a measure `μ` and an adversary `A` and,
with `hgood` (keys and every encryption good almost surely), equates the winning probabilities of
the fresh-only IND-CPA-D game and of the IND-CPA game played by the reduction; `bfv_adv_le`
(`Challenge/IndCpaD/ProfileAdv.lean:41`), under `[IsFiniteMeasure μ]` and `hq` (at most `q`
encryption queries), bounds the IND-CPA-D advantage by the IND-CPA advantage plus `2·μ(bad)`. The
BGV twins are `correct_bgv` and `bgv_prob_eq` (`Challenge/IndCpaD/ProfileBGV.lean:90`, `:97`) and
`bgv_adv_le` (`ProfileAdv.lean:63`). With evaluation on earlier results,
`Challenge.IndCpaDLM.gameLM_eq_gameCPA` (`Challenge/IndCpaD/LM.lean:92`) and `advLM_le` (`:139`)
assume `hmk` (circuits built by `mk` carry their program), `hI : InterpOK` (the evaluator is a
local interpreter), `hC` (perfect correctness of the fresh-only scheme on the class; discharged for the instances
in section 3, F4), `[DecidableEq]` on messages, and: for the pointwise equality, `hk : KeysOK` and
`ht : TapeOKLM` (good randomness on the run); for `advLM_le`, a measure with `[IsFiniteMeasure μ]`
and `hq : BoundedLM` (at most `q` encryption queries). What is proved about `μ(bad)` and about
the measurability of the events is in section 3 (F1, F2).

**H4, algorithm level.** `Challenge.BFVMul.stepOK_mul_behz` (`Challenge/BFVMul.lean:271`): under
`SchemeParamsOK P`, a secret within `secretBound` (`SecretOK`), the side condition `behzAuxOK?` on
the BEHZ bases (`haux`), and a budget whose `mulLift` is at least the lift norm of
`Spec.BudgetBFV.behzSlack` (`hL`) and whose `mulRound` is at least `mulRoundApprox P (2·ℓ)` (`hR`),
the product `behzMul` of two two-component ciphertexts at a level `ℓ` with `1 ≤ ℓ ≤ L` (BEHZ
multiplication as OpenFHE runs it, integers only) meets the BFV `mul` contract
`Spec.TraceBFV.StepOK`. `Challenge.MSB.certifyProfile?_sound_msb` (`Challenge/MSB.lean:257`): if
`certifyProfile?` accepts at `E`, then for every integer polynomial `s` as the secret, all messages
and all MSB-form input ciphertexts whose stored-representative bound `Bin` is at most the input
noise and every declared input bound and below half the modulus of each input's level (`hBin`,
`hbnd`, `hwrap`, `hin : MSB.InputsOK`), every output of every MSB run within `E` MSB-decrypts with
`s` to the message the program computes, and its t-reading (`toLSB`) has LSB noise at most its
bound in `outs`. The first ties the multiplication contract to a named RNS algorithm; the second
carries H1 for BGV to the MSB form (`Spec/MSB.lean`).

## 2. Reading order

The closure of H1 ∪ H3: 173 declarations, 1,465 lines in 25 files, grouped by layer, each layer in
dependency order. Each entry gives the declarations, their location, their line count (docstrings
included), a mark, what they say, and what to compare them with. The bracketed citations are
listed at the end of this section. The marks:

* *code* (472 lines): a function or a record; compare it with the textbook or library function
  named, line by line.
* *judgment* (718 lines): a relation or a statement shape where the question is whether it says
  the right thing; this needs mathematical or cryptographic judgment.
* *skip first* (275 lines): the declarations reached only through the bodies of the two profile
  decisions (computed: H1 ∪ H3 minus the closure that does not unfold those bodies). A soundness
  statement is true of whatever the decision accepts, so these bodies say how often a certificate
  is issued, not what it means. Without them the closure is 141 declarations, 1,190 lines.

A reader with a few hours should read the *judgment* entries in full and skim the rest. The layer
totals are distinct lines of the layer's declarations.

### Ring and parameters (20 declarations, 106 lines)

1. `NPoly`, `Poly`, `IntPoly`. `Spec/Ring.lean:21-31`, 9 lines, *code*. A polynomial of degree < N as its coefficient vector `Fin N → R`; `Poly q N` is Z_q[X]/(X^N+1), `IntPoly N` integer polynomials, never reduced. Compare: The ring R_q of [BGV12, FV12]. `Spec/Ring.lean` also defines `toQuot` into Mathlib's `R[X] ⧸ (X^N + 1)`; the pins of `Challenge/Ring.lean` say the operations below are that ring's.

2. `instZero`, `instAdd`, `instSub`, `instSMul`, `instMul`. `Spec/Ring.lean:40-56`, 13 lines, *code*. Coefficientwise zero, sum, difference, scalar product; the product is the negacyclic convolution (`X^N = −1`). Compare: Schoolbook multiplication modulo X^N+1.

3. `automorph`. `Spec/Ring.lean:64-71`, 8 lines, *code*. The Galois map X ↦ X^g: monomial X^i goes to ±X^{(i·g) mod 2N}. Compare: σ_g of [GHS12] (rotations); meaningful for odd g.

4. `ofInt`, `centered`, `normInf`. `Spec/Ring.lean:96-106`, 6 lines, *judgment*. Reduction of an integer polynomial mod q; the centred lift by Mathlib's `ZMod.valMinAbs` (representatives in (−q/2, q/2]); the infinity norm (`Finset.sup` of `natAbs`). Compare: Mathlib's `ZMod.valMinAbs` docstring. All bounds in the development are on centred representatives in the infinity norm.

5. `FullParams`, `LimbParams`, `StoreParams`. `Spec/Params.lean:16-37` `Spec/Layout.lean:17-33`, 38 lines, *code*. The parameter record: the source parameters (`kind`, `N`, `qs`, `t`), storage data, and the bounds `secretBound`, `inputNoise`, `keyNoise` (`outputNoise` is read by no statement). Compare: The docstring of `FullParams` lists which fields a certificate reads.

6. `schemeParamsOK?`, `primeOK?`, `powMod`, `noDivisorFrom`, `twoPart`. `Spec/Params.lean:107-142`, 32 lines, *skip first*. The check of `SchemeParamsOK` (N a power of two, distinct primes, t ≥ 2 coprime to them, BGV `inputNoise ≥ ⌊t/2⌋`) with a primality test that is sound for every input. Note: read only to know which parameters are accepted; proved sound by `Challenge.Params.schemeParamsOK?_sound`.


### Ciphertexts and the Encrypts relations (11 declarations, 52 lines)

7. `Kind`, `phase`, `centeredPhase`. `Spec/Scheme.lean:29-43`, 13 lines, *code*. The phase ⟨ct, (1, s, s², …)⟩ by Horner's rule, and its centred lift. Compare: Decryption in [BGV12] and [FV12] for ciphertexts of any length.

8. `bgvDecrypt`, `BGVEncrypts`. `Spec/Scheme.lean:47-55`, 8 lines, *judgment*. BGV decryption `[[⟨ct, s⟩]_Q]_t`; `BGVEncrypts t B` = decrypts to m and the centred phase m + t·e has norm ≤ B. The bound includes the message. Compare: [BGV12]. Unusual unit: most papers bound e or t·e; here B bounds m + t·e (docstring of `Spec/Scheme.lean`).

9. `roundDiv`, `bfvDecrypt`, `BFVEncrypts`. `Spec/Scheme.lean:59-71`, 11 lines, *judgment*. `roundDiv a b = ⌊(2a + b)/(2b)⌋` (round half up; Lean's `Int` division is floor division for b > 0); BFV decryption `[⌊t·[⟨ct, s⟩]_Q / Q⌉]_t`; `BFVEncrypts t B` = decrypts to m and phase − ⌊Q/t⌋·m has centred norm ≤ B, with m's representative in [0, t). Compare: [FV12], decryption and the invariant. The noise is measured before any scaling by t.

10. `Encrypts`, `inputVal`, `InputsOK`. `Spec/Correct.lean:18-39`, 20 lines, *judgment*. A list of integer polynomials encrypts a source value: it has `parts` components and, reduced mod `q₀⋯q_{ℓ−1}` under the key `σ_key(s)`, satisfies the scheme's relation. `InputsOK`: every declared input (first declaration of its name) encrypts its message with noise ≤ `inputNoise`. Compare: the two relations above; and check that `InputsOK` constrains every input the program reads.


### Decryption (9 declarations, 46 lines)

11. `switchPhase`, `switchDownRev`, `bgvDecryptSwitched`, `decScale`. `Spec/Decrypt.lean:26-60`, 21 lines, *code*. OpenFHE's BGV decryption: switch the phase polynomial down to one limb by t-corrected switches, then reduce mod t; the message comes out times `decScale` = (q₁⋯q_{ℓ−1})⁻¹ mod t. Compare: OpenFHE `PKEBGVRNS::Decrypt` (`bgvrns-pke.cpp:44-99`, cited in the file). Enters `OutputsCertified` only when `switched = true`.

12. `decBoundRev`, `decBound`, `decryptOK?`, `outputLevel?`, `decryptAllOK?`. `Spec/Decrypt.lean:48-79`, 25 lines, *skip first*. The check that the switched decryption is exact for a given bound. Note: decision internals.


### Source language and its semantics (18 declarations, 208 lines)

13. `Var`, `Params`, `modulus`, `Msg`, `Val`. `Spec/Source.lean:54-89`, 32 lines, *code*. Variable names are strings; `modulus ℓ` is the product of the first ℓ primes; a value is a message in Z_t[X]/(X^N+1) with its number of components, level and key (`scale` is carried and read by nothing).

14. `Instr`, `Decl`, `ok`, `Program`, `boundOf`. `Spec/Source.lean:91-165`, 71 lines, *code*. The 16 instructions; an input declaration (name, parts, level, key) and its well-formedness (1 ≤ level ≤ L, odd key < 2N); a straight-line program with outputs and optional per-input bounds. Compare: OpenFHE's `EvalAdd`, `EvalMult`, `Relinearize`, `KeySwitch`, `EvalAutomorphism`, `ModReduce`, `LevelReduce`, and their plaintext forms.

15. `Env`, `set`, `lift₂`, `lift₁`, `fits`. `Spec/Source.lean:167-188`, 13 lines, *code*. Environments and message plumbing (`Msg` has one constructor, so `lift₂` never fails and `fits` is always true).

16. `step`. `Spec/Source.lean:190-268`, 79 lines, *judgment*. The meaning of each instruction on messages, with the guards that make a program ill formed (`none`): levels and keys must match, `relin` needs 3 parts under key 1, `modSwitch` needs level ≥ 2 and multiplies a BGV message by q_last⁻¹ mod t, `dropLimbs` is BGV only. Compare: What a library's operation does to the plaintext. The q_last⁻¹ factor is the exact effect of the t-corrected switch [GHS12]; libraries hide it by bookkeeping.

17. `initEnv`, `eval`. `Spec/Source.lean:270-283`, 13 lines, *code*. Run the program on messages; `none` if a declaration is not well formed, a step fails, or an output is undefined.


### Per-operation contracts (StepOK) and runs (13 declarations, 157 lines)

18. `dst`, `CtEnv`, `set`, `phaseAt`, `initCt`. `Spec/Trace.lean:47-101`, 20 lines, *code*. The destination of an instruction; ciphertext environments; the phase mod Q under σ_key(s); the initial ciphertext environment.

19. `BoundsOK`. `Spec/Trace.lean:103-110`, 8 lines, *judgment*. Every input with a declared bound meets it (on top of `InputsOK`, so a declared bound can only tighten `inputNoise`).

20. `StepOK`. `Spec/Trace.lean:112-147`, 36 lines, *judgment*. **The BGV contracts.** Each instruction assigns its destination some ciphertext with the recorded number of components whose phase is: the sum/difference/product/σ_g of the operands' phases; the operand's phase plus an error e with ‖e‖ ≤ `E.keySwitch` and t ∣ e (relin, keySwitch); (Φ + δ)/q_last with t ∣ δ, q_last ∣ Φ + δ, ‖δ‖ ≤ q_last·`E.modSwitchAt parts` (modSwitch). Compare: textbook BGV homomorphic operations [BGV12] and the t-corrected modulus switch [GHS12]; check that each clause is what the textbook operation does to the phase, no more and no less.

21. `Run`. `Spec/Trace.lean:149-154`, 6 lines, *code*. A run: a sequence of steps, each accepted by `Source.step` and meeting its contract.

22. `PlainOK`, `inputBound`, `InputsOK`. `Spec/TraceBFV.lean:95-117`, 21 lines, *judgment*. BFV inputs: a one-component input is a plaintext [p] with p ≡ m (mod t) and ‖p‖ ≤ its bound; any other input satisfies `Encrypts`. The bound is the declared one, else `inputNoise` (ciphertext) or t − 1 (plaintext). Compare: unlike BGV, a declared BFV bound replaces `inputNoise` (section 3, F6).

23. `StepOK`. `Spec/TraceBFV.lean:119-170`, 52 lines, *judgment*. **The BFV contracts.** As BGV for add, sub, mulConst, copy, automorph; plaintext addition adds ⌊Q/t⌋·p plus δ with ‖δ‖ ≤ `E.plainAdd`; key switching adds e with no divisibility; modSwitch rounds without t-correction; mul/square: Q·X = t·(Φ_a + Q·k_a)(Φ_b + Q·k_b) + D with ‖k‖ ≤ `mulLift`, 2‖D‖ ≤ Q·`mulRound`; dropLimbs is `False`. Compare: FV.SH.Mul of [FV12] §4, and its RNS variants [BEHZ, HPS]: the module docstring derives the contract from the textbook algorithm.

24. `RunAt`. `Spec/TraceBFV.lean:181-194`, 14 lines, *code*. A BFV run with one budget per instruction position.


### Budgets and profiles (4 declarations, 48 lines)

25. `Budget`, `modSwitchAt`, `Budget`. `Spec/Trace.lean:54-81` `Spec/TraceBFV.lean:70-83`, 41 lines, *code*. What a backend declares: BGV key-switch error and modulus-switch error by number of components; BFV key-switch, modulus-switch, the two multiplication numbers and the plaintext-addition deviation. In H1 and H3 the budget is arbitrary. Compare: the profile theorems quantify over every budget; check only the units in the field docstrings.

26. `Bnd`. `Spec/TraceBFV.lean:85-91`, 7 lines, *skip first*. What the BFV analysis tracks per variable: a ciphertext bound or a plaintext bound. Note: decision internals.


### Encryption helpers (4 declarations, 16 lines)

27. `liftMsg`. `Spec/Encrypt.lean:74-75`, 2 lines, *code*. The representative of a message in [0, t): how the games store a plaintext constant.

28. `outputKey?`, `outputsUnderS?`, `certOK?`. `Spec/Encrypt.lean:167-182`, 14 lines, *skip first*. The check that every output is under key 1; `certOK?` adds the switched-decryption check. Note: decision internals.


### Certificate functions (24 declarations, 277 lines)

29. `OutputsCertified`. `Challenge/Certify.lean:253-273`, 21 lines, *judgment*. **The BGV conclusion.** `Source.eval` succeeds, and for every run σ (`Trace.Run` at E from the inputs), every output o in `prog.outputs` has a ciphertext that `Encrypts` its value with the bound listed for o, is under key 1, decrypts with s at its level to the message, and (if `switched`) decrypts by the switched routine to the message times `decScale`. Compare: the sentence you would write yourself. Check the quantifier order, that it ranges over `prog.outputs` (not over the returned list), and that it requires key 1.

30. `OutputsCertifiedBFV`. `Challenge/CertifyBFV.lean:163-176`, 14 lines, *judgment*. The same for BFV with `RunAt` and textbook BFV decryption. Compare: As above.

31. `certifyProfile?`, `certifyBFVProfile?`. `Challenge/Profile/Defs.lean:53-86`, 26 lines, *code*. The profile decisions. Their types are what H1 needs (they return a whole-program bound and a list of per-output bounds); their bodies (parameter check, scheme kind, nonempty outputs, the per-declaration input checks `inputsMsgOK?` and `plainBoundsOK`, the reference analysis of the whole program and of each output alone, the output-key and decryption checks) say when a certificate is issued. Compare: the guards are short; the analyses they call are the next entries.

32. `inputsDecOK`, `outputBound?`, `inputsMsgOK?`, `plainBoundsOK`. `Challenge/Profile/Defs.lean:66-71` `Challenge/Certify/Defs.lean:59-73` `Challenge/CertifyBFV/Defs.lean:227-231`, 25 lines, *skip first*. The BFV input-decryption check and the per-output bound of the BGV decision, and the two per-declaration input checks: `inputsMsgOK?` (BGV: every input's level has a modulus above `t`, and every declared bound is at least `⌊t/2⌋`) and `plainBoundsOK` (BFV: every plaintext input's bound is at least `⌊t/2⌋`). Without them the decisions accepted programs for which some message has no input ciphertext (section 3, F4). Note: decision internals.

33. `NoiseAnalyzer`, `refBound`, `refRun`, `refAnalyze`. `Challenge/Headline/Defs.lean:30-126`, 54 lines, *skip first*. The BGV reference analysis: sums add bounds, products multiply them by N, key switching adds `E.keySwitch`, modSwitch maps B to ⌊B/q⌋ + `E.modSwitchAt`, and every bound must stay below Q/2. Note: textbook worst-case noise growth (infinity norm, expansion factor N).

34. `mulBound`, `decOK`, `refBoundBFV`, `bndOK`, `domainOK`, `ctBound`, `refAnalyzeBFV`, `refRunBFVAt`, `NoiseAnalyzerBFVAt`, `refAnalyzeBFVAt`. `Challenge/BFV/Defs.lean:106-253`, 118 lines, *skip first*. The BFV reference analysis, with the product bound `mulBound` and the decryption condition 2(t·B + (Q mod t)(t−1)) < Q. Note: the FV noise analysis [FV12]; decision internals.

35. `certifyProfile?_sound`, `certifyBFVProfile?_sound`. `Challenge/Profile.lean:54-73`, 19 lines, *judgment*. The H1 statements (section 1).


### Security games (70 declarations, 555 lines)

36. `HEScheme`, `Correct`. `Spec/IndCpaD.lean:51-85`, 32 lines, *judgment*. An abstract scheme with a deterministic public evaluator, message semantics `sem`, a decidable class and predicates `KeysOK`, `GoodE`; perfect correctness on the class for good keys and randomness. Compare: Correctness in [LiMicciancio21] (exact schemes), restricted to a class as in [AlexandruAAHE].

37. `Entry`, `Adv`, `CpaAdv`, `pick`, `Bounded`. `Spec/IndCpaD.lean:87-148`, 24 lines, *code*. Table entries (m₀, m₁, c, fresh); adversaries as well-founded query trees (no running time); `Bounded q`: at most q encryption queries on every path.

38. `freshAt`, `evalStep`, `decAns`, `simAns`, `gameD`, `gameCPA`. `Spec/IndCpaD.lean:111-176`, 45 lines, *judgment*. The fresh-only IND-CPA-D game: encryption of m_b, evaluation of a class circuit on fresh entries, decryption only of entries with m₀ = m₁; and multi-query left-or-right IND-CPA. Compare: [LiMicciancio21], Definition of IND-CPA-D: the decryption oracle's condition and the message tracking. Differences are listed in the module docstring.

39. `reduce`, `reduction`. `Spec/IndCpaD.lean:178-195`, 17 lines, *code*. The reduction: forwards encryptions, runs `evalStep` itself, answers decryptions from the table. Its arguments are the public key and the adversary. Compare: no argument may carry the secret key or the bit.

40. `AbsScheme`, `Pe`, `msg`, `cts`, `outLevel`, `decBFV`, `decBGV`, `sem`, `inputsFit`. `Spec/IndCpaDProfile.lean:46-138`, 66 lines, *judgment*. The abstract BGV/BFV scheme: parameters, fresh noise `eps`, encryption level, abstract keys, randomness, encryption and circuits (program, fresh-input names, constants); textbook decryption at the ciphertext's level; `sem` = `Source.eval` on the messages. Compare: the defaults: `msg` and `cts` fall back to 0 and [] for a missing index, `outLevel` to 0, `sem` to [] (section 3, F5).

41. `EncOKBFV`, `EncOKBGV`. `Spec/IndCpaDProfile.lean:112-127`, 15 lines, *judgment*. Hypothesis (i): for good keys and randomness, a fresh ciphertext is at level `lvl`, has two components and encrypts m with noise ≤ `eps`. Compare: what a real encryption satisfies with high probability, not always (section 3, F1).

42. `admBFV`, `schemeBFV`, `EvalMeetsBFV`, `admBGV`, `schemeBGV`, `EvalMeetsBGV`. `Challenge/IndCpaD/Profile.lean:54-89` `Challenge/IndCpaD/ProfileBGV.lean:51-86`, 68 lines, *judgment*. The profile class (the profile certificate accepts at input noise `eps`); the assembled scheme (the evaluator is called only with the right number of inputs); hypothesis (ii): for good keys, every class circuit and good fresh inputs, the evaluator's outputs are those of some run within the circuit's profile under `sec sk`. Compare: the quantifier order: the evaluator and profile are fixed before the keys.

43. `M`, `CT`, `QCirc`, `Global`, `prog`, `names`, `empty`, `freshDecl`, `link`, `constNames`, `extend`, `composite`, `replay`, `metaOK`. `Spec/IndCpaDLM.lean:57-118`, 47 lines, *code*. The global program that records the provenance of every entry and the declared bounds of the plaintext constants of every inlined query (`Global.bounds`), and the inlined program `composite` a query is judged on.

44. `admLM`, `LEntry`, `evalLM`, `LAdv`, `decAnsLM`, `simAnsLM`, `gameLM`. `Spec/IndCpaDLM.lean:122-232`, 59 lines, *judgment*. The game with evaluation on earlier results: a query on any entries is answered if the inlined program (whole history with its carried constant bounds, then the query) is in the class; the evaluator runs on the selected ciphertexts. Compare: [LiMicciancio21]: their evaluation oracle accepts any entries and any circuit; the differences are in the module docstring.

45. `freshScheme`, `TapeOKLM`, `BoundedLM`, `reduceLM`, `reductionLM`. `Spec/IndCpaDLM.lean:179-250`, 44 lines, *code*. The fresh-only scheme the IND-CPA game is played against; good-tape and query-count predicates; the reduction (public key and adversary only).

46. `StepFn`, `irun`, `interpEval`, `InterpOK`. `Challenge/IndCpaD/LM.lean:64-87`, 21 lines, *judgment*. An evaluator given by a step function of the public key (`interpEval`), and `InterpOK`: a step writes only its destination, depends only on what it reads, and does not get stuck on well-formed programs. Compare: The locality that makes evaluation on earlier outputs equal to running the inlined program.

47. `correct_bfv`, `bfv_prob_eq`, `bfv_adv_le`, `correct_bgv`, `bgv_prob_eq`, `bgv_adv_le`, `gameLM_eq_gameCPA`, `advLM_le`. `Challenge/IndCpaD/Profile.lean:91-116` `Challenge/IndCpaD/ProfileAdv.lean:39-80` `Challenge/IndCpaD/ProfileBGV.lean:88-109` `Challenge/IndCpaD/LM.lean:91-156`, 117 lines, *judgment*. The H3 statements (section 1).

Total: 173 declarations, 1,465 lines (1,118 without docstrings): 982 in `Spec/`, 483 in
`Challenge/`. H2 adds the budgets computed from the parameters (`Spec/Budget.lean`,
`Spec/BudgetBFV*.lean`), the fresh-encryption mode (`Spec/Encrypt.lean`) and the default-mode
decisions (`Challenge/Certify/Defs.lean`, `Challenge/CertifyBFV/Defs.lean`): 105 declarations not
in H1 ∪ H3 (135 with H4); `docs/trusted-core.json` lists them with depths. `docs/SPEC.md` explains the design and
`docs/TRUSTED-DEFINITIONS.md` the evidence for each trusted definition.

References. [BGV12] Brakerski, Gentry, Vaikuntanathan, (Leveled) Fully Homomorphic Encryption
without Bootstrapping, ITCS 2012. [FV12] Fan, Vercauteren, Somewhat Practical Fully Homomorphic
Encryption, ePrint 2012/144. [GHS12] Gentry, Halevi, Smart, Homomorphic Evaluation of the AES
Circuit, CRYPTO 2012. [BEHZ] Bajard, Eynard, Hasan, Zucca, A Full RNS Variant of FV like Somewhat
Homomorphic Encryption Schemes, SAC 2016. [HPS] Halevi, Polyakov, Shoup, An Improved RNS Variant
of the BFV Homomorphic Encryption Scheme, CT-RSA 2019. [LiMicciancio21] Li, Micciancio, On the
Security of Homomorphic Encryption on Approximate Numbers, EUROCRYPT 2021. [AlexandruAAHE]
Alexandru, Al Badawi, Micciancio, Polyakov, Application-Aware Approximate Homomorphic Encryption,
IACR Communications in Cryptology. [CheonCCS24] Cheon, Choe, Passelègue, Stehlé, Suvanto,
Attacks Against the IND-CPA-D Security of Exact FHE Schemes, CCS 2024.

**Trusted but outside the closure.** `Spec/IndCpaDSanity.lean` is a trusted file that no headline
statement reads: it holds `CpaBounded` and the `swap` maps, which only let the sanity statements of
`Challenge/IndCpaD/Sanity.lean` be stated, and no game, reduction or earlier statement uses it. It is
not in any of the counts above (the closure of every headline is unchanged by it).

## 3. Where a definition could be wrong without any proof failing

An adversarial read of the closure, done for this document. Each item says whether it is a real
weakness, already disclosed, or new. Severity is for the claim as the paper states it.

**F1. The bad event of H3: reduced to coefficient tails, no tail evaluated for any distribution
(low; partly disclosed).** `KeysOK` and `GoodE` are fields of the abstract scheme
(`Spec/IndCpaDProfile.lean:62-63`), arbitrary predicates. `bfv_adv_le` and its twins bound the
advantage by the IND-CPA advantage plus `2·μ(bad)`, where `bad` is "the keys or one of the first
`q` encryptions are not good"; `bfv_prob_eq` assumes that the keys and every encryption are good
almost surely. What is proved about `μ(bad)`:
* *Union bound.* `bad_le_sum` (`Challenge/IndCpaD/BadEvent.lean:38`): `μ(bad) ≤ μ{keys not good}
  + Σ_{i<q} μ{encryption i not good}`, for arbitrary predicates, key and randomness maps and any
  measure, with no measurability assumed. The advantage bounds with that sum: `adv_le_sum` (`:48`;
  the fresh-only game, any scheme perfectly correct on its class, so the profile schemes through
  `correct_bfv` and `correct_bgv`), `advLM_le_sum` (`:73`), `advLM_le_sum_bfv` (`:115`),
  `advLM_le_sum_bgv` (`:139`); equal advantages when everything is good almost surely: `adv_eq`
  (`:61`), `advLM_eq` (`:94`).
* *Coefficient tails.* In the instances `GoodE` says that the three sampled polynomials of an
  encryption are within the declared coefficient bounds `Bu`, `B1`, `B2`
  (`Spec/IndCpaDBFV.lean:141`, `Challenge/IndCpaD/ProfileBGVInstances.lean:100`,
  `Challenge/IndCpaD/ProfileBGVKS.lean:168`, `Challenge/IndCpaD/LMBFV.lean:185`).
  `goodE_bad_le_bgvData`, `goodE_bad_le_bgvKSData`, `goodE_bad_le_bfvKSData` and
  `goodE_bad_le_dataOf` (`Challenge/IndCpaD/BadEvent.lean:177-216`, through `normInf_bad_le` and
  `goodE3_bad_le`) bound `μ{encryption i not good}` by the sum of the `3N` coefficient tail masses
  `μ{|coefficient| > its bound}`, under any measure. Conversely `GoodE` is exactly these
  coefficient bounds (`goodE_bgvData_iff`, `goodE_bgvKSData_iff`, `goodE_bfvKSData_iff`,
  `Challenge/IndCpaD/SanityInstances.lean:47-70`).
* *Truncated samplers.* `bad_null_bgvKSData`, `bad_null_bfvKSData`
  (`Challenge/IndCpaD/SanityInstances.lean:75`, `:86`): if the keys are good almost surely and,
  for each of the first `q` encryptions, every coefficient of the three samples is within its bound
  almost surely, then `μ(bad) = 0` and the advantage bound holds with no loss.

What remains open:
* No statement evaluates a coefficient tail mass for any distribution. The tail statements hold
  for every measure and reduce the encryption term to `3N` per-coefficient tails per query; for a
  sampler that is not truncated at the declared bounds, no theorem gives their size. The tail
  bounds of `Challenge/FreshNoise.lean` and `Challenge/FreshNoiseL2.lean` serve the
  fresh-encryption mode of `certify?` and are not connected to `GoodE`.
* The key term `μ{keys not good}` is not bounded by any probabilistic statement: `keyGen_keysOK`
  and `bfvKeyGen_keysOK` are pointwise statements about generated keys, and `bad_null_*` assume
  good keys almost surely.
* The null bad event is stated for `bgvKSData` and `bfvKSData` only, not for `bgvData` or the
  OpenFHE-shaped `dataOf` (whose tail bounds are stated).
* No statement is about any library's sampler.

Disclosed: the paper's security section states the union bound, the coefficient tails under any
measure, `Pr[bad] = 0` when keys are good and samples within bounds almost surely, and that the key
term is not reduced further; it gives no value for a tail.

**F2. Measurability of the events of H3 (low; proved for discrete samplers).** `pk`, `sk`, `tape`
and `coins` are arbitrary functions of `ω` and the adversary an arbitrary tree, and the headline
statements assume no measurability: for a non-measurable set `μ` is its outer measure, and the
equalities and inequalities remain true but are then not probabilities in the usual sense.
`Challenge/IndCpaD/Sanity.lean` proves measurability for discrete samplers: if the keys, the coins
and the first `q` encryption samples are functions of one measurable map into a countable space
with measurable singletons (the sample space itself may be anything, for instance an infinite
sequence of samples) and the adversary makes at most `q` encryption queries, then the event of the
fresh-only game (`gameD_measurableSet`, `:236`), the IND-CPA event of its reduction
(`gameCPA_reduction_measurableSet`, `:249`), the bad event (`bad_measurableSet`, `:261`, stated for
every `HEScheme`, so also for `freshScheme`, whose `KeysOK` and `GoodE` are those of the abstract
scheme, `Spec/IndCpaDLM.lean:193-194`), the event of the game with evaluation on earlier results
(`gameLM_measurableSet`, `:341`) and the IND-CPA event of its reduction (`gameCPA` of
`freshScheme` against `reductionLM`, the right-hand side of `advLM_le`;
`gameCPA_reductionLM_measurableSet`, `:357`) are measurable sets. At the instance `bgvKSSeal`, on
a countable sample space with measurable singletons, the `gameLM` event and the bad event of
`advLM_le_bgvKSSeal` are measurable for every adversary (`bgvKSSeal_events_measurable`,
`Challenge/IndCpaD/SanityInstances.lean:155`).

What remains open: (a) nothing is stated for samplers that are not discrete; (b) measurability is
a separate statement, not a hypothesis or conclusion of the headlines. Disclosed: the module
docstring of `Challenge/IndCpaD/Sanity.lean` (items 6 and 10) and the paper's security section
("Probabilities").

**F3. H1 holds at every budget, including budgets no algorithm meets (low; disclosed).** `E` is
universally quantified and `OutputsCertified` speaks of every run within `E`
(`Challenge/Certify.lean:261-273`). At `E = 0` a modulus switch generally has no run, and the
conclusion is vacuous; the zero profile is accepted. The content is in the realisability theorems
(H4 and `Challenge/BFVMul*`). Disclosed: the paper's setting section (soundness "holds even at
error budgets no algorithm meets") and its realisability section ("Acceptance alone is not
achievability": a toy program is accepted at the zero profile, `tiny_accepts`).

**F4. Non-vacuity of the hypotheses: what exists.**

| Hypothesis | Shown satisfiable by |
|---|---|
| acceptance `h` (H1) | BFV: `tiny_accepts`, `Challenge/Profile.lean:296` (the `#guard` examples after it are evaluated by the compiler, not the kernel); BGV: `ksClass_bgvKSSeal` (`Challenge/IndCpaD/ProfileBGVKS.lean:251`; `ksClass` includes `admBGV`, hence acceptance) |
| BFV `hin` (H1) | `certifyBFVProfile?_inputs_exist_all` (`Challenge/Profile/Inputs.lean:72`) and `certifyBFV?_inputs_exist` (`:79`): for every accepted program, every secret and every assignment of messages, no further hypothesis |
| BGV `hin ∧ hb` (H1) | `certifyProfile?_inputs_exist_all` (`Challenge/Profile/Inputs.lean:57`) and `certify?_inputs_exist` (`:64`): for every accepted program, every secret and every assignment of messages, no further hypothesis (the witness is the ciphertext whose first component is the centred message, so its phase does not depend on the secret or a Galois key) |
| a run exists (H2) | `Challenge.Budget.certified_run_exists` (`Challenge/Budget.lean:391`), `certifyBFV?_textbook_run_exists` (`Challenge/CertifyBFV.lean:361`), for secrets within `secretBound` |
| (i) `EncOK` | `encOK_dataOf` (`Challenge/IndCpaD/ProfileInstances.lean:67`) |
| (ii) `EvalMeets` | `libEval_meets` (`Challenge/IndCpaD/Generic.lean:126`), `textEval_meets` (`Challenge/IndCpaD/Textbook.lean:55`), `ksEval_meets` (`Challenge/IndCpaD/ProfileBGVKS.lean:121`) |
| (iii) a nonempty class | `admBFV_tiny` (`ProfileInstances.lean:115`), `sealCirc_kernel` (`ProfileKernel.lean:21`), `ksClass_bgvKSSeal` (`ProfileBGVKS.lean:251`) |
| `KeysOK` | `keyGen_keysOK` (`ProfileBGVKS.lean:191`), `bfvKeyGen_keysOK` (`LMBFV.lean:209`) |
| all hypotheses of H1 and H2 at once | `certify?_end_to_end` (`Challenge/Sanity/EndToEnd.lean:173`), `certifyBFV?_end_to_end` (`:160`): for every accepted input, every secret within `secretBound` and every assignment of messages, inputs meeting the input hypotheses and a run within `c.budget` exist, no further hypothesis; profile mode: `certifyProfile?_end_to_end` (`:132`), `certifyBFVProfile?_end_to_end` (`:74`), under the coverage check and the further conditions their statements list |
| `μ(bad)` small | `μ(bad) ≤` key term `+` the coefficient tails of the first `q` encryptions: `bad_le_sum`, `goodE_bad_le_*` (`Challenge/IndCpaD/BadEvent.lean:38`, `:177-216`); `μ(bad) = 0` for samples within their bounds and keys good almost surely: `bad_null_bgvKSData`, `bad_null_bfvKSData` (`Challenge/IndCpaD/SanityInstances.lean:75`, `:86`); no tail is evaluated for any distribution and the key term is not bounded (F1) |
| the events of H3 are measurable | for discrete samplers: `gameD_measurableSet`, `gameCPA_reduction_measurableSet`, `bad_measurableSet`, `gameLM_measurableSet`, `gameCPA_reductionLM_measurableSet` (`Challenge/IndCpaD/Sanity.lean:236`, `:249`, `:261`, `:341`, `:357`) (F2) |
| all hypotheses of H3 at once | `bgvKSSeal_jointly` (`Challenge/IndCpaD/SanityInstances.lean:100`), `bfvSeal_jointly` (`:114`): at `N = 2¹³`, one public key, secret state and encryption randomness, all non-zero, with good keys, good randomness, a circuit in the class, and the textbook decryptions of the evaluator's outputs on two encryptions of any two messages equal to what the program computes |
| the class agrees with the game's oracle (LM) | `admLM_fresh_bgv`, `admLM_fresh_exact`, `admLM_fresh_ks`, `admLM_fresh_bfv`, `admLM_fresh_bfvClass` (`Challenge/IndCpaD/LMAgree.lean`), and the instances `admLM_fresh_bgvKSSeal`, `admLM_fresh_bgvSealExact`, `admLM_fresh_bfvSeal`; declared constant bounds are carried: `lm_bounds_kernel`, `lm_bounds_bfv_kernel` (`LMBounds.lean`) |
| `hC`, `hI` (LM) | `correct_lm_exact` (`LMExact.lean:36`), `correct_lm_bgvKSSeal` (`LM.lean:196`), `ksStep_interpOK` (`LM.lean:168`); an accepted two-stage query, `lm_two_stage_kernel` (`LM.lean:253`) |

**The input checks.** The decisions include two per-declaration input checks, `inputsMsgOK?` (BGV)
and `plainBoundsOK` (BFV). Without them a decision would accept programs with a declared input
bound `b < ⌊t/2⌋` (the message `⌊t/2⌋` has no encryption within `b`:
`Challenge.Params.bgv_small_noise_excludes`) or with an input at a level whose modulus is at most
`t` (`bgv_low_level_excludes`, `Challenge/Profile/Inputs.lean:88`), and the soundness statements
would be about no input for some messages. `certifyProfile?_inputs_checked` and
`certifyBFVProfile?_plain_checked` state what acceptance gives, and the `#guard`s of
`Challenge/Profile/Inputs.lean` evaluate the rejections. The checks are the weakest
per-declaration ones: `bgv_small_noise_excludes` and `bgv_low_level_excludes` show that a program
they reject has a message with no input. That inputs and a run exist together for every accepted
program is the row "all hypotheses of H1 and H2 at once" of the table above.

**F5. Silent defaults (none makes a contract trivially true).** Every default in the closure was
checked:
* `AbsScheme.msg`, `.cts` (`Spec/IndCpaDProfile.lean:75`, `:82`) fall back to `0` and `[]` for a
  missing index; `.sem` (`:101`) returns `[]` when the number of messages is wrong. The schemes'
  `eval` returns `[]` in the same case, so a wrong-arity query gives no entries in either game, and
  `EvalMeets*` require the right arity.
* `AbsScheme.outLevel` (`:89`) defaults to level 0, where every ciphertext decrypts to 0. It is
  reached only for circuits the class accepts, which evaluate on zero messages.
* `interpEval` (`Challenge/IndCpaD/LM.lean:76`) returns `[]` if the interpreter gets stuck and
  `[]` for an unset output; this would make `hC` false, and `hC` is a hypothesis discharged by the
  instances.
* `TraceBFV.inputBound` (`Spec/TraceBFV.lean:105`) defaults to `inputNoise` or `t − 1`: an
  assumption on inputs, intended.
* `Decrypt.decryptOK?` and `certifyBFVProfile?` read `qs.headD 0`; with no primes they reject, and
  `schemeParamsOK?` rejects that case first.
* `Source.step` (`Spec/Source.lean:247`) multiplies a BGV message by `(q_last : ZMod t)⁻¹`. Mathlib
  defines this inverse for non-units (it is not an inverse then). Every decision checks that `t` is
  coprime to every prime, so no theorem is about that case; but `step` alone is meaningful only
  under `SchemeParamsOK`.
* An undeclared variable is `none` in `initEnv` and makes `step` fail, so no instruction can read a
  default ciphertext; `Msg` has one constructor, so `Msg.lift₂` never fails and `Msg.fits` is
  always true.

**F6. Declared input bounds behave differently in BGV and BFV (low; documented).** For BGV,
`InputsOK` and `BoundsOK` both apply, so a declared bound can only tighten `inputNoise`. For BFV,
`TraceBFV.inputBound` *replaces* `inputNoise` by the declared bound, which may be larger. Neither is
unsound (each theorem assumes what its analysis uses). The docstring of `Program`
(`Spec/Source.lean:149-155`) says exactly this.

**F7. Units and conventions (no defect; disclosed).**
* BGV "noise" is the norm of the whole centred phase `m + t·e`, message included, not `e` or
  `t·e` (`Spec/Scheme.lean:14-21`, `:51-55`). `SchemeParamsOK.msgRange` requires
  `inputNoise ≥ ⌊t/2⌋` so that every message is admissible.
* BFV noise is `phase − ⌊Q/t⌋·m` with `m` in `[0, t)` (`Spec/Scheme.lean:66-71`), measured before
  scaling. With the centred representative instead, a coefficient's noise would differ by at most
  `Q mod t < t`.
* `centered` uses `ZMod.valMinAbs`, range `(−q/2, q/2]`; the moduli are odd primes, so no tie.
  `roundDiv` rounds halves up; with `Q` odd and coprime to `t`, `t·x/Q` is never a half-integer.
* All norms are infinity norms of centred representatives; products are bounded with the expansion
  factor `N`.

**F8. The games differ from Li–Micciancio's in disclosed ways (disclosed).** Compared with
[LiMicciancio21] (`Spec/IndCpaD.lean:1-47`, `Spec/IndCpaDLM.lean:3-50`, the paper's security
section): the
evaluation oracle accepts only circuits of a declared class; the fresh-only game evaluates on fresh
entries only; in the game with evaluation on earlier results, a query is judged on the inlined
program of the whole history, with the declared constant bounds of every inlined query carried
(`Global.bounds`; the reachable global programs are the inductive `Reach`). For a query on fresh
entries alone and a certificate class at a constant budget the oracle accepts exactly what the
fresh-only class accepts, whatever the history (`admLM_fresh_bgv`, `admLM_fresh_exact`,
`admLM_fresh_ks`, `admLM_fresh_bfv`, `admLM_fresh_bfvClass`, `Challenge/IndCpaD/LMAgree.lean`); this
is not claimed for queries on derived entries, for budgets that depend on the circuit, or for
per-instruction BFV budgets. For regular adversaries (in every admitted query with as many indices
as fresh inputs: the fresh input names are distinct, the indices are distinct, every fresh input is
declared at scale 0, and the body writes no fresh input) the fresh-only game embeds in the game with
evaluation on earlier results with identical outcomes on every tape (`embed_exact`, `embed_ks`,
`embed_bfv`; instances `embed_bgvSealExact`, `embed_bgvKSSeal`, `embed_bfvSeal`; winning
probabilities `embedProb_*`; `Challenge/IndCpaD/LMEmbed.lean`), for the three interpreter classes at
a constant budget. Nothing is claimed for irregular adversaries, for circuit- or
instruction-dependent budgets, or for adversaries with local names; queries use global names, and
the translation from adversaries with local names is not formalised; decryption is textbook; the
evaluation keys are public and IND-CPA with them (circular security) is assumed; the adversary's
coins may be correlated with the keys in the statements, and only independent coins make the
reduction an IND-CPA adversary; no running time. The decryption condition (`m₀ = m₁`,
`Spec/IndCpaD.lean:152-156`) is Li–Micciancio's for exact schemes. Quantifier order checked: `ev`,
`adm`, `prof` are fixed before the keys; the reductions (`Spec/IndCpaD.lean:182`,
`Spec/IndCpaDLM.lean:236`) take the public key and the adversary only; the step function of an
interpreter takes the public key only (`Challenge/IndCpaD/LM.lean:64-66`).

**F9. What the contracts leave open (disclosed).** The key-switching contract bounds only the
added error; no key validity, key noise or secret bound appears in H1 (key material enters through
`E.keySwitch` only; `Spec/Trace.lean:40-41`). H1 and H2 hold for every secret; the budgets are
realisable only for secrets within `secretBound` (`Challenge/Certify.lean` module docstring, "For
which secrets"). That a library's execution is a `Run` is an assumption (paper, limits, items 3
and 6). In H2 the hypotheses are at `c.params`, which in the fresh-encryption modes replaces
`inputNoise` with a computed value.

**F10. What was looked for and not found.** No hypothesis of H1–H3 that is unsatisfiable for all
parameters; no definition in the closure that uses `implemented_by`, `extern`, `opaque`, `partial`
or `unsafe` (the gate's step 2 bans them in `Spec/` and `Challenge/`); no conclusion quantified over the list the decision
returns instead of the program's outputs (`OutputsCertified` ranges over `prog.outputs` and
requires the returned list to have an entry for each); no output condition that omits the key (key
1 is required); no secret or key quantified after the evaluator.

## 4. How to check the proofs yourself

```
./verify.sh                        # dependencies, the strict gate, fhe_check tests, a summary
STRICT=1 scripts/check-spec.sh     # the gate alone, release mode (after verify.sh has fetched dependencies)
lake env lean --run scripts/PinStatus.lean   # step 5 alone, after `lake build Challenge Validation`
python3 -I paper/gen/trusted_core.py         # recompute docs/trusted-core.json (needs a built tree)
```

What they establish. The gate (`scripts/check-spec.sh`, eight steps, listed in `README.md`,
"Check it yourself") checks that the locked files match `trust/LOCK`; that `Spec/` and
`Challenge/` contain no banned construct (`sorry` other than as the body of a locked theorem,
`axiom`, `opaque`, `implemented_by`, `extern`, `unsafe`, `partial def`, `native_decide`, new
notation or syntax); builds everything in a sandbox; and, in `scripts/PinStatus.lean`, checks for every locked
theorem `Challenge.X` (stated with `:= sorry`) that `Validation.X` exists, has the same type
(syntactically, else by the kernel's definitional equality), uses only `propext`, `Quot.sound` and
`Classical.choice`, and that every constant in its closure is accepted by the Lean kernel replayed
in a fresh environment. It then runs the differential and mutation suites against recorded OpenFHE
runs, and one seed of the reference implementation (`harness/ref/difftest.sh`). To look at one
headline by hand: `#print axioms Validation.Profile.certifyProfile?_sound` in
a file that imports `Validation`.

What they do not establish.
* That the definitions mean what this document says: no tool checks that (sections 2 and 3).
* The verdict of `fhe_check`. The tool is compiled Lean code run by Lean's compiler and runtime; no
  verdict is re-checked by the kernel. The functions it runs are proved equal to the locked
  decisions (`Challenge/Fast.lean`, `Challenge/Fast/Profile.lean`), but the compiled code that
  executes them is trusted.
* That a library computes the transcribed algorithms, and that the extractors read the right
  program (paper, limits, items 3 and 6). These are tested, not proved.
* Anything about Mathlib or the Lean kernel themselves; no second proof checker was run.

## 5. A challenge

Five questions, each meant for about an hour of an expert's time. A "yes, this is wrong" answer
to any of them would matter, and would be acknowledged in the repository.

1. **Contracts.** Is there a step in `Spec.Trace.StepOK` (`Spec/Trace.lean:112-147`) or
   `Spec.TraceBFV.StepOK` (`Spec/TraceBFV.lean:119-170`) whose clause a correct textbook
   implementation of that operation violates, or which a ciphertext meets that does not decrypt
   to what `Source.step` (`Spec/Source.lean:190-268`) says? The BFV multiplication clause
   (`Q·X = t·(Φ_a + Q·k_a)(Φ_b + Q·k_b) + D`) and the BGV modulus switch are the places to look.
2. **The conclusion.** Can `OutputsCertified` (`Challenge/Certify.lean:253-273`) or
   `OutputsCertifiedBFV` (`Challenge/CertifyBFV.lean:163-176`) hold for a program whose output a
   user would say decrypts wrongly, for instance because the `Encrypts` relations
   (`Spec/Correct.lean:18-26`, `Spec/Scheme.lean:47-71`) or the message semantics differ from the
   textbook definitions in [BGV12, FV12]?
3. **The game with evaluation on earlier results.** Is there an attack on exact schemes in the
   IND-CPA-D literature ([LiMicciancio21, CheonCCS24]) that uses only circuits a profile
   certificate accepts, but whose queries `gameLM` (`Spec/IndCpaDLM.lean:220-232`, admissibility
   `admLM` at `:122-133`) refuses, so that the theorem excludes it by construction?
4. **The measure.** `bfv_adv_le` (`Challenge/IndCpaD/ProfileAdv.lean:41`) bounds the advantage
   by the IND-CPA advantage plus `2·μ(bad)`; `Challenge/IndCpaD/BadEvent.lean` reduces `μ(bad)` to a
   key term plus `3N` coefficient tails per encryption query, and `Challenge/IndCpaD/Sanity.lean`
   makes the events measurable for discrete samplers (F1, F2). For a standard sampler, does this
   say less than "IND-CPA-D advantage ≤ IND-CPA advantage + 2·Pr[keys or noise outside the
   bounds]", for instance because the hypothesis of `gameD_measurableSet` (one measurable map into
   a countable space with measurable singletons) does not hold for it, or because coefficient
   bounds are the wrong notion of a good sample? Should measurability be a hypothesis of the
   headline statements rather than a separate statement?
5. **Vacuity.** Is any hypothesis of H1–H3 unsatisfiable for parameters that the paper's
   evaluation uses, beyond those listed in F4, for instance `InterpOK`
   (`Challenge/IndCpaD/LM.lean:81-87`) together with `hC` for an evaluator that key-switches?

Answers, with a counterexample or a pointer, are welcome as issues in the repository.
