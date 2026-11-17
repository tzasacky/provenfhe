import Challenge.IndCpaD.LMBFV
import Challenge.IndCpaD.LMAgree

/-!
# Challenge.IndCpaD.Attack — the plaintext–ciphertext attack circuit of Choe, Kang and Stehlé: refused at the published parameters, in a class with an IND-CPA-D reduction one prime later   (LOCKED statements; proofs in `Validation/IndCpaD/Attack.lean`)

Choe, Kang and Stehlé ("New IND-CPA-D Attacks on BFV and BGV", ACM CCS 2026) give IND-CPA-D
key-recovery attacks on BFV as implemented in OpenFHE and recommend worst-case noise bounds as the
countermeasure. Their plaintext–ciphertext attack evaluates a chain of `K` plaintext–ciphertext
products on a fresh encryption. `harness/eval/cks26` runs `fhe_check` on OUR re-implementation of
that circuit (written from the paper's description and a reading of its public code; not the
authors' code) at the five parameter sets of the paper's Table 3. This file states, as theorems
checked by the kernel, what that evaluation reports for each of the five sets:

* **Refusal** (`AttackRefused`): at the attack's own parameter set (ring dimension, the four
  ciphertext primes and the plaintext modulus of the case file; no special prime) the attack
  circuit at the attack's depth `K` is not in the class of the BFV evaluator of
  `Challenge.IndCpaD.LMBFV` at the certified budget, for every plaintext; the game's oracle refuses
  the query in every reachable state; and the failing check is the noise bound: the first `K′`
  products are accepted, with the bound `ptctNoise … K′` that the plaintext-product rule of
  `Challenge.BFV.refBoundBFV` gives, and the product `K′ + 1` is refused because
  `ptctNoise … (K′ + 1)` fails the decryption condition `decOK` (the bound exceeds what the
  modulus allows). `K′ = K − 2` in every row; the refused bound is the one `fhe_check` reports.
* **The countermeasure, as a security statement** (`AttackReduces`): at the same ring dimension
  and plaintext modulus with ONE more 60-bit prime, the same circuit at the same depth is in the
  class for every plaintext and the oracle accepts it on a fresh entry in every reachable state;
  fresh encryptions meet the encryption hypothesis; the scheme is perfectly correct on the class
  (`Correct`: every output of every circuit of the class, the attack circuit included, decrypts to
  what the circuit computes, for good keys and encryption randomness, i.e. every secret within
  the bound and all errors within the assumed bounds); key generation with non-zero key errors
  gives good keys; and therefore the locked reduction applies: for every adversary of the game
  with evaluation on earlier results (`Spec.IndCpaDLM.gameLM`) whose queries the oracle checks
  against this class (a class that CONTAINS the attack circuit), making at most `q` encryption
  queries, `Adv^{IND-CPA-D} ≤ Adv^{IND-CPA} + 2·Pr[bad]` (`Challenge.IndCpaDLM.advLM_le`).

**The model** (what the statements are about, and what they are not about):
* the circuit is our re-implementation, transcribed from the case files `cases/ptct_n*_coef`
  (`ptctProg`); a claim about a circuit and a parameter set, not about the authors' code;
* the evaluator is ours (`Challenge.IndCpaDLM.bfvStep`: the plaintext product multiplies every
  component by the plaintext polynomial), a proved model, not the library's code; the evaluation
  keys are in the public key; decryption is textbook BFV decryption at the ciphertext's level
  (not the library's floating-point decryption);
* encryption is textbook BFV public-key encryption (`Spec.EncryptBFV.encryptBFV`), and every
  error coefficient is ASSUMED to lie in `[−39, 39]` (ternary secret and `u`); with this bound the
  fresh-noise bound `eps` of the data is the input noise `fhe_check` used in the recorded runs
  (`out/ptct_n*_coef.summary.json`, `fheCheck.inputNoise`, and for the certified sets
  `out/cost_ptct_n*_sameN_d*.summary.json`). The statements say nothing about how any library
  samples errors;
* what remains assumed is what the reduction assumes (`Challenge.IndCpaD.Profile`'s docstring):
  that the abstract scheme is IND-CPA with the evaluation keys public (with a circular-security
  assumption), no running-time model, textbook decryption by the oracle.

**The parameter sets** (every number from `harness/eval/cks26`):
* `cksN12` … `cksN16`: the paper publishes `N`, `t`, `log2 Q = 240` and `K`; the four 60-bit
  ciphertext primes are the ones OpenFHE v1.6.1 generates for that context, as recorded in
  `cases/ptct_n12_coef.fhecheck.json.gz` … `cases/ptct_n16_coef.fhecheck.json.gz`
  (`params.N`, `params.t`, `params.limbs[].q`, `params.limbs[].psi`; `params.special` is empty);
  the depth `K` is the number of instructions of the case file's `program.body` (8, 7, 6, 6, 7),
  the plaintext bound the case file's declared bound of `pt_2` (`t − 1`).
* `cksN12Plus` … `cksN16Plus`: the same with a fifth prime. The 5-limb primes of the certified
  runs (`out/cost_ptct_n*_sameN_d*.summary.json`, verdict `CERTIFIED`, `log2Q = 300`) are not
  recorded in the tree (no case file is kept for them, and `fhe_check recommend` has no BFV
  support: the README of `harness/eval/cks26`). The fifth prime here is the first entry of the
  case file's `bfv.multiplication.auxBasis` (the next prime `≡ 1 (mod 2N)` below the last
  ciphertext prime). Fingerprint, not proof of identity: with it, `Q mod t` gives exactly the
  input noise those certified runs record (`fheCheck.inputNoise` = `39·(2N + 1) + Q mod t`:
  1097592, 2792468, 17446959, 31996980, 5588864). The theorems are about the sets as written,
  whatever the library generates.
* The storage-level fields `store.W` and the roots `ψ` are read by no statement here
  (`Spec.FullParams`); the fifth prime's `ψ` is not recorded and is `0`. Primality of every
  ciphertext prime IS checked (by the kernel): the class runs `Spec.schemeParamsOK?`.
* In the plaintext–ciphertext rows, `keyNoise` is read only by key switching, which that circuit
  does not use, and the layout is one limb per digit with no special prime
  (`Spec.Budget.uniformLayout 1`). The squaring rows (last section) relinearize; there `keyNoise`
  is an assumed bound and the special primes and digit sizes are those of their case files.
-/

namespace Challenge.IndCpaDAttack
open Spec NPoly Scheme Source Spec.IndCpaD Spec.IndCpaDProfile Spec.IndCpaDLM Spec.Encrypt
  Spec.EncryptBFV Challenge.IndCpaDProfile Challenge.IndCpaDLM Challenge.BFV MeasureTheory

/-! ## The circuit -/

/-- The variable names of the case files: `ct_1` (the fresh encryption), `ct_2`, …, `ct_9`. -/
def ctVars : List Var := ["ct_1", "ct_2", "ct_3", "ct_4", "ct_5", "ct_6", "ct_7", "ct_8", "ct_9"]

/-- **The plaintext–ciphertext attack circuit** at level `L`, depth `K ≤ 8`, plaintext bound `b`:
the fresh ciphertext `ct_1` and the plaintext `pt_2` (one component,
declared bound `b`), then `ct_{d+1} = mulPlain ct_d pt_2` for `d = 1, …, K`, output `ct_{K+1}`.
For `L = 4` and the case's `K` and `b` this is the `program` of `cases/ptct_n*_coef.fhecheck.json.gz`
(`inputs`, `body`, `outputs`; the `level` 4 of both inputs; the declared `bound` of `pt_2`). The
plaintext's value is the circuit's constant (`QCirc`'s third component), arbitrary in every
statement below. -/
def ptctProg (L K b : ℕ) : Program where
  inputs := [{ name := "ct_1", parts := 2, level := L, scale := 0, key := 1 },
             { name := "pt_2", parts := 1, level := L, scale := 0, key := 1 }]
  body := (List.range K).map fun d => .mulPlain (ctVars.getD (d + 1) "") (ctVars.getD d "") "pt_2"
  outputs := [ctVars.getD K ""]
  bounds := [("pt_2", b)]

/-- The noise bound of `ct_{k+1}` by the plaintext-product rule of `Challenge.BFV.refBoundBFV`
(`N·b·(B + r)`, `r = Q mod t`), from the fresh-noise bound `B₀`. -/
def ptctNoise (N t Q b B₀ : ℕ) : ℕ → ℕ
  | 0 => B₀
  | k + 1 => N * b * (ptctNoise N t Q b B₀ k + Q % t)

/-! ## The scheme, the class, the evaluator -/

/-- One limb per digit, no special prime. -/
def cksLayout : Budget.KSLayout := Budget.uniformLayout 1

/-- BFV public-key encryption with evaluation keys at `P` (`bfvKSData`), every error coefficient
within `[−39, 39]`, ternary `u`, no rotation keys. -/
def cksData (P : FullParams) : AbsScheme := bfvKSData P cksLayout [] 39 1 39 39

/-- The certified budget at `P` (`Spec.BudgetBFV.certified`). -/
def cksBudget (P : FullParams) : TraceBFV.Budget := BudgetBFV.certified P cksLayout

/-- The circuit builder. -/
def mkCks (P : FullParams) (p : Program) (f : List Var) (c : Var → M (cksData P)) :
    (cksData P).Circ := (p, f, c)

/-- **The class**: the class `bfvClass` of the BFV evaluator at the certified budget. -/
def admCks (P : FullParams) : (cksData P).Circ → Bool :=
  bfvClass (cksData P) cksLayout [] (cksBudget P)

/-- **The evaluator**: the BFV step interpreter `bfvStep` with the keys of the public key. -/
def evCks (P : FullParams) : (cksData P).PK → (cksData P).Circ → List (CT (cksData P)) →
    List (CT (cksData P)) :=
  interpEval (cksData P) (bfvStepFn (cksData P) cksLayout (fun pk => pk.2.2.1)
    (fun pk => pk.2.2.2))

/-- The attack query on the fresh entry `ct_1`, with the plaintext `c`. -/
def ptctQ (P : FullParams) (K b : ℕ) (c : Var → M (cksData P)) : QCirc (cksData P) :=
  (ptctProg P.src.qs.length K b, ["ct_1"], c)

/-- Key errors: the all-ones polynomial for each of `n` digits at every level `ℓ ≥ 1` (none at
the non-level `0`). -/
def onesErrL (N n : ℕ) : ℕ → List (IntPoly N) :=
  fun ℓ => if ℓ = 0 then [] else List.replicate n ⟨fun _ => 1⟩

/-! ## What is claimed -/

/-- **Refusal at `P`, depth `K`, plaintext bound `b`, last accepted depth `K′`** (module
docstring): the profile certificate rejects the attack circuit at the certified budget; the
class rejects it for every plaintext; the oracle refuses the
attack query on a fresh entry in every reachable state; the reference analysis accepts `K′`
products with the bound `ptctNoise … K′` and refuses `K′ + 1`, whose bound fails `decOK`. -/
def AttackRefused (P : FullParams) (K K' b : ℕ) : Prop :=
  Challenge.Profile.certifyBFVProfile? (cksData P).Pe (fun _ => cksBudget P)
      (ptctProg P.src.qs.length K b) = none ∧
  (∀ c, admCks P (mkCks P (ptctProg P.src.qs.length K b) ["ct_1"] c) = false) ∧
  (∀ G, Reach (mkCks P) (admCks P) G → "ct_1" ∈ G.fresh → ∀ c,
    (∀ x ∈ constNames (ptctQ P K b c) ++ (ptctQ P K b c).1.body.map Trace.dst, x ∉ G.names) →
    admLM (mkCks P) (admCks P) G (ptctQ P K b c) [("ct_1", true)] = false) ∧
  (∀ c, admCks P (mkCks P (ptctProg P.src.qs.length K' b) ["ct_1"] c) = true) ∧
  (∀ c, admCks P (mkCks P (ptctProg P.src.qs.length (K' + 1) b) ["ct_1"] c) = false) ∧
  refAnalyzeBFVAt (cksData P).Pe (fun _ => cksBudget P) (ptctProg P.src.qs.length K' b) =
    some (ptctNoise P.src.N P.src.t (P.src.modulus P.src.qs.length) b (cksData P).eps K') ∧
  refAnalyzeBFVAt (cksData P).Pe (fun _ => cksBudget P) (ptctProg P.src.qs.length (K' + 1) b) =
    none ∧
  decOK P.src.t (P.src.modulus P.src.qs.length)
    (ptctNoise P.src.N P.src.t (P.src.modulus P.src.qs.length) b (cksData P).eps K') = true ∧
  decOK P.src.t (P.src.modulus P.src.qs.length)
    (ptctNoise P.src.N P.src.t (P.src.modulus P.src.qs.length) b (cksData P).eps (K' + 1)) = false

/-- **The attack circuit at depth `K` is in a class on which IND-CPA-D reduces to IND-CPA, at `P`**
(module docstring): class membership for every plaintext; acceptance by the oracle on a fresh
entry in every reachable state; the encryption hypothesis; perfect correctness on the class;
noisy key generation gives good keys; the advantage bound of the reduction. -/
def AttackReduces (P : FullParams) (K b : ℕ) : Prop :=
  (∀ c, admCks P (mkCks P (ptctProg P.src.qs.length K b) ["ct_1"] c) = true) ∧
  (∀ G, Reach (mkCks P) (admCks P) G → "ct_1" ∈ G.fresh → ∀ c,
    (∀ x ∈ constNames (ptctQ P K b c) ++ (ptctQ P K b c).1.body.map Trace.dst, x ∉ G.names) →
    admLM (mkCks P) (admCks P) G (ptctQ P K b c) [("ct_1", true)] = true) ∧
  (cksData P).EncOKBFV ∧
  Correct (freshScheme (cksData P) (admCks P) (evCks P) (cksData P).decBFV) ∧
  (∀ (s e a : IntPoly P.src.N), SecretOK P.secretBound s → normInf e ≤ 39 →
    ∀ (ra : ℕ → List (IntPoly P.src.N)) (ga : ℕ → ℕ → List (IntPoly P.src.N)),
      (cksData P).KeysOK (bfvKeyGen P cksLayout s e a ra (onesErrL P.src.N P.src.qs.length) ga
        (fun _ => onesErrL P.src.N P.src.qs.length)) (s, e)) ∧
  ∀ [DecidableEq (M (cksData P))] {Ω Coins : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsFiniteMeasure μ] (pk : Ω → (cksData P).PK) (sk : Ω → (cksData P).SK)
    (tape : Ω → ℕ → (cksData P).ER) (coins : Ω → Coins)
    (A : Coins → (cksData P).PK → LAdv (cksData P) Bool) (q : ℕ),
    (∀ r p, BoundedLM (A r p) q) →
    |(μ {ω | gameLM (mkCks P) (admCks P) (evCks P) (cksData P).decBFV true (pk ω) (sk ω)
          (tape ω) (A (coins ω) (pk ω)) 0 [] (Global.empty (cksData P)) = true}).toReal -
        (μ {ω | gameLM (mkCks P) (admCks P) (evCks P) (cksData P).decBFV false (pk ω) (sk ω)
          (tape ω) (A (coins ω) (pk ω)) 0 [] (Global.empty (cksData P)) = true}).toReal| ≤
      |(μ {ω | gameCPA (S := freshScheme (cksData P) (admCks P) (evCks P) (cksData P).decBFV)
          true (pk ω) (tape ω) (reductionLM (mkCks P) (admCks P) (evCks P) (cksData P).decBFV A
            (coins ω) (pk ω)) 0 = true}).toReal -
        (μ {ω | gameCPA (S := freshScheme (cksData P) (admCks P) (evCks P) (cksData P).decBFV)
          false (pk ω) (tape ω) (reductionLM (mkCks P) (admCks P) (evCks P) (cksData P).decBFV A
            (coins ω) (pk ω)) 0 = true}).toReal| +
      2 * (μ {ω | ¬ ((cksData P).KeysOK (pk ω) (sk ω) ∧
        ∀ i < q, (cksData P).GoodE (pk ω) (sk ω) (tape ω i))}).toReal

/-- **The reduction for every BFV parameter set without special primes** at which a fresh
encryption decrypts at the top level and the attack circuit is in the class (two closed checks),
besides the shape of the parameters (BFV, `t ≥ 2`, a nonempty chain of moduli `≥ 3`, `N ≥ 1`,
a key-error bound `≥ 1`, no special prime). The instances below discharge every hypothesis. -/
theorem attackReduces_of (P : FullParams) (K b : ℕ) (hk : P.src.kind = .bfv) (ht : 2 ≤ P.src.t)
    (hL : P.src.qs ≠ []) (hN : 1 ≤ P.src.N) (hkn : 1 ≤ P.keyNoise)
    (hsp : P.store.special = []) (hq : ∀ q ∈ P.src.qs, 3 ≤ q)
    (hdec : decOK P.src.t (P.src.modulus P.src.qs.length) (cksData P).eps = true)
    (hmem : admCks P (mkCks P (ptctProg P.src.qs.length K b) ["ct_1"] (fun _ => 0)) = true) :
    AttackReduces P K b := sorry

/-! ## The five parameter sets of the paper's Table 3 -/

/-- `cases/ptct_n12_coef.fhecheck.json.gz`: `N = 2¹²`, `t = 786433`, four 60-bit primes
(`log2 Q = 240`). Attack depth `K = 8`, plaintext bound `786432`. -/
def cksN12 : FullParams where
  src := { kind := .bfv, N := 4096, t := 786433,
           qs := [1152921504606830593, 1152921504606748673, 1152921504606683137,
                  1152921504606601217] }
  store := { W := 4096, special := [],
             limbs := [⟨1152921504606830593, 116777451583545⟩, ⟨1152921504606748673, 271802498405390⟩,
                       ⟨1152921504606683137, 134367042585739⟩, ⟨1152921504606601217, 276147373136904⟩] }
  secretBound := 1
  inputNoise := 0
  keyNoise := 39
  outputNoise := 0

/-- `cksN12` with the fifth prime `1152921504606584833` (`auxBasis[0]` of the same case file;
`log2 Q = 300`). -/
def cksN12Plus : FullParams where
  src := { kind := .bfv, N := 4096, t := 786433,
           qs := [1152921504606830593, 1152921504606748673, 1152921504606683137,
                  1152921504606601217, 1152921504606584833] }
  store := { W := 4096, special := [],
             limbs := [⟨1152921504606830593, 116777451583545⟩, ⟨1152921504606748673, 271802498405390⟩,
                       ⟨1152921504606683137, 134367042585739⟩, ⟨1152921504606601217, 276147373136904⟩,
                       ⟨1152921504606584833, 0⟩] }
  secretBound := 1
  inputNoise := 0
  keyNoise := 39
  outputNoise := 0

/-- `cases/ptct_n13_coef.fhecheck.json.gz`: `N = 2¹³`, `t = 4194305`, four 60-bit primes.
Attack depth `K = 7`, plaintext bound `4194304`. -/
def cksN13 : FullParams where
  src := { kind := .bfv, N := 8192, t := 4194305,
           qs := [1152921504606830593, 1152921504606748673, 1152921504606683137,
                  1152921504606601217] }
  store := { W := 8192, special := [],
             limbs := [⟨1152921504606830593, 25959043411404⟩, ⟨1152921504606748673, 100406242475323⟩,
                       ⟨1152921504606683137, 45474351589225⟩, ⟨1152921504606601217, 92707844590835⟩] }
  secretBound := 1
  inputNoise := 0
  keyNoise := 39
  outputNoise := 0

/-- `cksN13` with the fifth prime `1152921504606584833` (`auxBasis[0]` of the same case file). -/
def cksN13Plus : FullParams where
  src := { kind := .bfv, N := 8192, t := 4194305,
           qs := [1152921504606830593, 1152921504606748673, 1152921504606683137,
                  1152921504606601217, 1152921504606584833] }
  store := { W := 8192, special := [],
             limbs := [⟨1152921504606830593, 25959043411404⟩, ⟨1152921504606748673, 100406242475323⟩,
                       ⟨1152921504606683137, 45474351589225⟩, ⟨1152921504606601217, 92707844590835⟩,
                       ⟨1152921504606584833, 0⟩] }
  secretBound := 1
  inputNoise := 0
  keyNoise := 39
  outputNoise := 0

/-- `cases/ptct_n14_coef.fhecheck.json.gz`: `N = 2¹⁴`, `t = 67108865`, four 60-bit primes.
Attack depth `K = 6`, plaintext bound `67108864`. -/
def cksN14 : FullParams where
  src := { kind := .bfv, N := 16384, t := 67108865,
           qs := [1152921504606748673, 1152921504606683137, 1152921504606584833,
                  1152921504605962241] }
  store := { W := 16384, special := [],
             limbs := [⟨1152921504606748673, 62213374832584⟩, ⟨1152921504606683137, 212089012217363⟩,
                       ⟨1152921504606584833, 92166579128688⟩, ⟨1152921504605962241, 74756755228070⟩] }
  secretBound := 1
  inputNoise := 0
  keyNoise := 39
  outputNoise := 0

/-- `cksN14` with the fifth prime `1152921504604979201` (`auxBasis[0]` of the same case file). -/
def cksN14Plus : FullParams where
  src := { kind := .bfv, N := 16384, t := 67108865,
           qs := [1152921504606748673, 1152921504606683137, 1152921504606584833,
                  1152921504605962241, 1152921504604979201] }
  store := { W := 16384, special := [],
             limbs := [⟨1152921504606748673, 62213374832584⟩, ⟨1152921504606683137, 212089012217363⟩,
                       ⟨1152921504606584833, 92166579128688⟩, ⟨1152921504605962241, 74756755228070⟩,
                       ⟨1152921504604979201, 0⟩] }
  secretBound := 1
  inputNoise := 0
  keyNoise := 39
  outputNoise := 0

/-- `cases/ptct_n15_coef.fhecheck.json.gz`: `N = 2¹⁵`, `t = 33423361`, four 60-bit primes.
Attack depth `K = 6`, plaintext bound `33423360`. -/
def cksN15 : FullParams where
  src := { kind := .bfv, N := 32768, t := 33423361,
           qs := [1152921504606584833, 1152921504598720513, 1152921504597016577,
                  1152921504595968001] }
  store := { W := 32768, special := [],
             limbs := [⟨1152921504606584833, 4443670208963⟩, ⟨1152921504598720513, 100545759574150⟩,
                       ⟨1152921504597016577, 31693996050849⟩, ⟨1152921504595968001, 88651361085495⟩] }
  secretBound := 1
  inputNoise := 0
  keyNoise := 39
  outputNoise := 0

/-- `cksN15` with the fifth prime `1152921504595640321` (`auxBasis[0]` of the same case file). -/
def cksN15Plus : FullParams where
  src := { kind := .bfv, N := 32768, t := 33423361,
           qs := [1152921504606584833, 1152921504598720513, 1152921504597016577,
                  1152921504595968001, 1152921504595640321] }
  store := { W := 32768, special := [],
             limbs := [⟨1152921504606584833, 4443670208963⟩, ⟨1152921504598720513, 100545759574150⟩,
                       ⟨1152921504597016577, 31693996050849⟩, ⟨1152921504595968001, 88651361085495⟩,
                       ⟨1152921504595640321, 0⟩] }
  secretBound := 1
  inputNoise := 0
  keyNoise := 39
  outputNoise := 0

/-- `cases/ptct_n16_coef.fhecheck.json.gz`: `N = 2¹⁶`, `t = 1048577`, four 60-bit primes.
Attack depth `K = 7`, plaintext bound `1048576`. -/
def cksN16 : FullParams where
  src := { kind := .bfv, N := 65536, t := 1048577,
           qs := [1152921504606584833, 1152921504598720513, 1152921504597016577,
                  1152921504595968001] }
  store := { W := 65536, special := [],
             limbs := [⟨1152921504606584833, 18043022392882⟩, ⟨1152921504598720513, 800790938143⟩,
                       ⟨1152921504597016577, 17749908910371⟩, ⟨1152921504595968001, 11469071954203⟩] }
  secretBound := 1
  inputNoise := 0
  keyNoise := 39
  outputNoise := 0

/-- `cksN16` with the fifth prime `1152921504592822273` (`auxBasis[0]` of the same case file). -/
def cksN16Plus : FullParams where
  src := { kind := .bfv, N := 65536, t := 1048577,
           qs := [1152921504606584833, 1152921504598720513, 1152921504597016577,
                  1152921504595968001, 1152921504592822273] }
  store := { W := 65536, special := [],
             limbs := [⟨1152921504606584833, 18043022392882⟩, ⟨1152921504598720513, 800790938143⟩,
                       ⟨1152921504597016577, 17749908910371⟩, ⟨1152921504595968001, 11469071954203⟩,
                       ⟨1152921504592822273, 0⟩] }
  secretBound := 1
  inputNoise := 0
  keyNoise := 39
  outputNoise := 0

/-! ## The headlines -/

/-- **`N = 2¹²`, `t = 786433`: the published attack circuit (our re-implementation) is refused at
the attack's parameter set and is in a class on which IND-CPA-D reduces to IND-CPA with one more
60-bit prime.** At `cksN12` (`cases/ptct_n12_coef.fhecheck.json.gz`) the 8-product chain is
refused, 6 products are accepted and the 7th fails the decryption condition (`fhe_check`:
"overflows at body[6]", `out/ptct_n12_coef.summary.json`); at `cksN12Plus` the 8-product chain is
in the class of the BFV evaluator `bfvStep` at the certified budget, the scheme is correct on the
class, and every adversary of the game with evaluation on earlier results whose queries are
checked against that class has `Adv^{IND-CPA-D} ≤ Adv^{IND-CPA} + 2·Pr[bad]`. Model (module
docstring): textbook decryption, public evaluation keys, our transcription of the circuit, our
evaluator, assumed error bounds `[−39, 39]`, IND-CPA of the abstract scheme assumed. -/
theorem cks_ptct_n12 :
    AttackRefused cksN12 8 6 786432 ∧ AttackReduces cksN12Plus 8 786432 := sorry

/-- **`N = 2¹³`, `t = 4194305`** (`cases/ptct_n13_coef.fhecheck.json.gz`): as `cks_ptct_n12`,
depth 7, 5 accepted ("overflows at body[5]"). -/
theorem cks_ptct_n13 :
    AttackRefused cksN13 7 5 4194304 ∧ AttackReduces cksN13Plus 7 4194304 := sorry

/-- **`N = 2¹⁴`, `t = 67108865`** (`cases/ptct_n14_coef.fhecheck.json.gz`): depth 6, 4 accepted
("overflows at body[4]"). -/
theorem cks_ptct_n14 :
    AttackRefused cksN14 6 4 67108864 ∧ AttackReduces cksN14Plus 6 67108864 := sorry

/-- **`N = 2¹⁵`, `t = 33423361`** (`cases/ptct_n15_coef.fhecheck.json.gz`): depth 6, 4 accepted
("overflows at body[4]"). -/
theorem cks_ptct_n15 :
    AttackRefused cksN15 6 4 33423360 ∧ AttackReduces cksN15Plus 6 33423360 := sorry

/-- **`N = 2¹⁶`, `t = 1048577`** (`cases/ptct_n16_coef.fhecheck.json.gz`): depth 7, 5 accepted
("overflows at body[5]"). -/
theorem cks_ptct_n16 :
    AttackRefused cksN16 7 5 1048576 ∧ AttackReduces cksN16Plus 7 1048576 := sorry

/-- **The refused bounds are the ones `fhe_check` reports** (`fheCheck.failure.bound` of
`out/ptct_n1{2,3,4,5,6}_coef.summary.json`): the bound of the first refused product, at the
fresh-noise bound of the data, is the recorded number in each of the five rows. -/
theorem cks_ptct_refused_bounds :
    ptctNoise 4096 786433 (cksN12.src.modulus 4) 786432 (cksData cksN12).eps 7 =
      5251037663091305562219578713906387505284935393317623225167875033404538880 ∧
    ptctNoise 8192 4194305 (cksN13.src.modulus 4) 4194304 (cksData cksN13).eps 6 =
      8645295002261143479853705142650371180946969650113112424994994217025536 ∧
    ptctNoise 16384 67108865 (cksN14.src.modulus 4) 67108864 (cksData cksN14).eps 5 =
      95263556898098926628455582455600851287684774034139372458602464804864 ∧
    ptctNoise 32768 33423361 (cksN15.src.modulus 4) 33423360 (cksData cksN15).eps 5 =
      44020180844967149018074699655908855737692558292007728570408621834240 ∧
    ptctNoise 65536 1048577 (cksN16.src.modulus 4) 1048576 (cksData cksN16).eps 6 =
      659376370918342488325287573605949135222680560990456753709864386295758848 := sorry

/-! ## The ciphertext–ciphertext (squaring) attack circuit at `t = 257`

Our re-implementation of the evaluation circuit of the squaring attack's phase 1, as
`harness/eval/cks26/README.md` ("Attack 3") describes it: a fresh input, then `K` times an addition
of a new fresh input followed by a squaring, relinearized. At `t = 257` the case
file `cases/ctct_e3_t257_p1.fhecheck.json.gz` has `K = 48` squarings: 49 fresh inputs and 144
instructions (`add`, `mul`, `relin` per squaring). Its parameters (`N = 2¹⁶`, 26 ciphertext primes
of 52 bits, 6 special primes, digits of 6 limbs: `keySwitching.digits.towersPerDigit`) are
`cksSq257`. `fhe_check` refuses the circuit there, with first failing instruction `body[97]`
(`out/ctct_e3_t257_p1.summary.json`: the 33rd product, i.e. 32 squarings certified). The
cost search (`out/cost_ctct_e3_t257.result.json`) found the full depth certified at OpenFHE's
128-bit-security choice for multiplicative depth 72: `N = 2¹⁷`, 40 ciphertext primes of 52 bits
(`log2 Q = 2080`), 7 special primes, digits of 8 limbs, recorded in full in
`cases/cost_ctct_e3_t257_full_d72.fhecheck.json.gz` (`cksSq257Cert`); this is NOT one more prime
at the same ring dimension. The program is the same in both case files.

The statements below are those of the plaintext–ciphertext rows for this circuit: refusal at
`cksSq257` (the first 97 instructions are accepted; the 98th, the product `ct_132 = ct_131·ct_131`,
is refused because the product rule's bound `mulBound` from the bound of `ct_131` fails `decOK`),
and the reduction at `cksSq257Cert`. The evaluator, the error bounds and the model are those of
the module docstring; the relinearization is `Challenge.Realize.OpenFHEBFV.relinBFV`
(hybrid key switching on the digits of `sqLayout`, canonical digit representatives), at the
certified key-switching budget `Spec.Budget.ksBoundAt` for the assumed key-error bound `keyNoise`.
-/

/-- The 49 fresh inputs of `cases/ctct_e3_t257_p1.fhecheck.json.gz` (`program.inputs[].name`). -/
def sqIns : List Var := [
  "ct_1", "ct_2", "ct_6", "ct_10", "ct_14", "ct_18", "ct_22", "ct_26", "ct_30", "ct_34",
  "ct_38", "ct_42", "ct_46", "ct_50", "ct_54", "ct_58", "ct_62", "ct_66", "ct_70",
  "ct_74", "ct_78", "ct_82", "ct_86", "ct_90", "ct_94", "ct_98", "ct_102", "ct_106",
  "ct_110", "ct_114", "ct_118", "ct_122", "ct_126", "ct_130", "ct_134", "ct_138",
  "ct_142", "ct_146", "ct_150", "ct_154", "ct_158", "ct_162", "ct_166", "ct_170",
  "ct_174", "ct_178", "ct_182", "ct_186", "ct_190"]

/-- The 144 instructions of `cases/ctct_e3_t257_p1.fhecheck.json.gz` (`program.body`, verbatim;
the same in `cases/cost_ctct_e3_t257_full_d72.fhecheck.json.gz`). -/
def sqBody : List Instr := [
  .add "ct_3" "ct_1" "ct_2", .mul "ct_4" "ct_3" "ct_3", .relin "ct_5" "ct_4",
  .add "ct_7" "ct_5" "ct_6", .mul "ct_8" "ct_7" "ct_7", .relin "ct_9" "ct_8",
  .add "ct_11" "ct_9" "ct_10", .mul "ct_12" "ct_11" "ct_11", .relin "ct_13" "ct_12",
  .add "ct_15" "ct_13" "ct_14", .mul "ct_16" "ct_15" "ct_15", .relin "ct_17" "ct_16",
  .add "ct_19" "ct_17" "ct_18", .mul "ct_20" "ct_19" "ct_19", .relin "ct_21" "ct_20",
  .add "ct_23" "ct_21" "ct_22", .mul "ct_24" "ct_23" "ct_23", .relin "ct_25" "ct_24",
  .add "ct_27" "ct_25" "ct_26", .mul "ct_28" "ct_27" "ct_27", .relin "ct_29" "ct_28",
  .add "ct_31" "ct_29" "ct_30", .mul "ct_32" "ct_31" "ct_31", .relin "ct_33" "ct_32",
  .add "ct_35" "ct_33" "ct_34", .mul "ct_36" "ct_35" "ct_35", .relin "ct_37" "ct_36",
  .add "ct_39" "ct_37" "ct_38", .mul "ct_40" "ct_39" "ct_39", .relin "ct_41" "ct_40",
  .add "ct_43" "ct_41" "ct_42", .mul "ct_44" "ct_43" "ct_43", .relin "ct_45" "ct_44",
  .add "ct_47" "ct_45" "ct_46", .mul "ct_48" "ct_47" "ct_47", .relin "ct_49" "ct_48",
  .add "ct_51" "ct_49" "ct_50", .mul "ct_52" "ct_51" "ct_51", .relin "ct_53" "ct_52",
  .add "ct_55" "ct_53" "ct_54", .mul "ct_56" "ct_55" "ct_55", .relin "ct_57" "ct_56",
  .add "ct_59" "ct_57" "ct_58", .mul "ct_60" "ct_59" "ct_59", .relin "ct_61" "ct_60",
  .add "ct_63" "ct_61" "ct_62", .mul "ct_64" "ct_63" "ct_63", .relin "ct_65" "ct_64",
  .add "ct_67" "ct_65" "ct_66", .mul "ct_68" "ct_67" "ct_67", .relin "ct_69" "ct_68",
  .add "ct_71" "ct_69" "ct_70", .mul "ct_72" "ct_71" "ct_71", .relin "ct_73" "ct_72",
  .add "ct_75" "ct_73" "ct_74", .mul "ct_76" "ct_75" "ct_75", .relin "ct_77" "ct_76",
  .add "ct_79" "ct_77" "ct_78", .mul "ct_80" "ct_79" "ct_79", .relin "ct_81" "ct_80",
  .add "ct_83" "ct_81" "ct_82", .mul "ct_84" "ct_83" "ct_83", .relin "ct_85" "ct_84",
  .add "ct_87" "ct_85" "ct_86", .mul "ct_88" "ct_87" "ct_87", .relin "ct_89" "ct_88",
  .add "ct_91" "ct_89" "ct_90", .mul "ct_92" "ct_91" "ct_91", .relin "ct_93" "ct_92",
  .add "ct_95" "ct_93" "ct_94", .mul "ct_96" "ct_95" "ct_95", .relin "ct_97" "ct_96",
  .add "ct_99" "ct_97" "ct_98", .mul "ct_100" "ct_99" "ct_99", .relin "ct_101" "ct_100",
  .add "ct_103" "ct_101" "ct_102", .mul "ct_104" "ct_103" "ct_103", .relin "ct_105" "ct_104",
  .add "ct_107" "ct_105" "ct_106", .mul "ct_108" "ct_107" "ct_107", .relin "ct_109" "ct_108",
  .add "ct_111" "ct_109" "ct_110", .mul "ct_112" "ct_111" "ct_111", .relin "ct_113" "ct_112",
  .add "ct_115" "ct_113" "ct_114", .mul "ct_116" "ct_115" "ct_115", .relin "ct_117" "ct_116",
  .add "ct_119" "ct_117" "ct_118", .mul "ct_120" "ct_119" "ct_119", .relin "ct_121" "ct_120",
  .add "ct_123" "ct_121" "ct_122", .mul "ct_124" "ct_123" "ct_123", .relin "ct_125" "ct_124",
  .add "ct_127" "ct_125" "ct_126", .mul "ct_128" "ct_127" "ct_127", .relin "ct_129" "ct_128",
  .add "ct_131" "ct_129" "ct_130", .mul "ct_132" "ct_131" "ct_131", .relin "ct_133" "ct_132",
  .add "ct_135" "ct_133" "ct_134", .mul "ct_136" "ct_135" "ct_135", .relin "ct_137" "ct_136",
  .add "ct_139" "ct_137" "ct_138", .mul "ct_140" "ct_139" "ct_139", .relin "ct_141" "ct_140",
  .add "ct_143" "ct_141" "ct_142", .mul "ct_144" "ct_143" "ct_143", .relin "ct_145" "ct_144",
  .add "ct_147" "ct_145" "ct_146", .mul "ct_148" "ct_147" "ct_147", .relin "ct_149" "ct_148",
  .add "ct_151" "ct_149" "ct_150", .mul "ct_152" "ct_151" "ct_151", .relin "ct_153" "ct_152",
  .add "ct_155" "ct_153" "ct_154", .mul "ct_156" "ct_155" "ct_155", .relin "ct_157" "ct_156",
  .add "ct_159" "ct_157" "ct_158", .mul "ct_160" "ct_159" "ct_159", .relin "ct_161" "ct_160",
  .add "ct_163" "ct_161" "ct_162", .mul "ct_164" "ct_163" "ct_163", .relin "ct_165" "ct_164",
  .add "ct_167" "ct_165" "ct_166", .mul "ct_168" "ct_167" "ct_167", .relin "ct_169" "ct_168",
  .add "ct_171" "ct_169" "ct_170", .mul "ct_172" "ct_171" "ct_171", .relin "ct_173" "ct_172",
  .add "ct_175" "ct_173" "ct_174", .mul "ct_176" "ct_175" "ct_175", .relin "ct_177" "ct_176",
  .add "ct_179" "ct_177" "ct_178", .mul "ct_180" "ct_179" "ct_179", .relin "ct_181" "ct_180",
  .add "ct_183" "ct_181" "ct_182", .mul "ct_184" "ct_183" "ct_183", .relin "ct_185" "ct_184",
  .add "ct_187" "ct_185" "ct_186", .mul "ct_188" "ct_187" "ct_187", .relin "ct_189" "ct_188",
  .add "ct_191" "ct_189" "ct_190", .mul "ct_192" "ct_191" "ct_191", .relin "ct_193" "ct_192"]

/-- **The squaring attack circuit**, its first `k` instructions, at level `L`: every input a fresh
two-component ciphertext at level `L`, the output the last destination (`ct_193` for `k = 144`,
the case file's `program.outputs`). -/
def sqProg (L k : ℕ) : Program where
  inputs := sqIns.map fun x => { name := x, parts := 2, level := L, scale := 0, key := 1 }
  body := sqBody.take k
  outputs := [((sqBody.take k).getLast?.map Trace.dst).getD ""]

/-- `cases/ctct_e3_t257_p1.fhecheck.json.gz`: `N = 2¹⁶`, `t = 257`, 26 ciphertext primes of 52 bits (`log2 Q = 1352`), 6 special primes (`params.limbs`, `params.special`). -/
def cksSq257 : FullParams where
  src := { kind := .bfv, N := 65536, t := 257,
           qs := [4503599626321921, 4503599625535489, 4503599625404417, 4503599623045121,
                  4503599621472257, 4503599619112961, 4503599615311873, 4503599613214721,
                  4503599607840769, 4503599606661121, 4503599605350401, 4503599604170753,
                  4503599603908609, 4503599603515393, 4503599600762881, 4503599600238593,
                  4503599599190017, 4503599598665729, 4503599597879297, 4503599595651073,
                  4503599595257857, 4503599592767489, 4503599589359617, 4503599587000321,
                  4503599583068161, 4503599579922433] }
  store := { W := 65536,
             limbs := [⟨4503599626321921, 94510489515⟩, ⟨4503599625535489, 141990425884⟩,
                       ⟨4503599625404417, 62879452361⟩, ⟨4503599623045121, 5106237945⟩,
                       ⟨4503599621472257, 3594277316⟩, ⟨4503599619112961, 37489847598⟩,
                       ⟨4503599615311873, 93167482113⟩, ⟨4503599613214721, 2024475945⟩,
                       ⟨4503599607840769, 10590638434⟩, ⟨4503599606661121, 35159463898⟩,
                       ⟨4503599605350401, 4163713097⟩, ⟨4503599604170753, 5211942980⟩,
                       ⟨4503599603908609, 61374650766⟩, ⟨4503599603515393, 30530876951⟩,
                       ⟨4503599600762881, 5753606077⟩, ⟨4503599600238593, 17333478820⟩,
                       ⟨4503599599190017, 36955179526⟩, ⟨4503599598665729, 180363715236⟩,
                       ⟨4503599597879297, 124304049415⟩, ⟨4503599595651073, 76491633208⟩,
                       ⟨4503599595257857, 7663033071⟩, ⟨4503599592767489, 4458766076⟩,
                       ⟨4503599589359617, 150710588309⟩, ⟨4503599587000321, 253654800607⟩,
                       ⟨4503599583068161, 44403339493⟩, ⟨4503599579922433, 34871110258⟩],
             special := [⟨1152921504606584833, 18043022392882⟩, ⟨1152921504598720513, 800790938143⟩,
                         ⟨1152921504597016577, 17749908910371⟩, ⟨1152921504595968001, 11469071954203⟩,
                         ⟨1152921504592822273, 21482204621753⟩, ⟨1152921504592429057, 6744827058362⟩] }
  secretBound := 1
  inputNoise := 0
  keyNoise := 39
  outputNoise := 0

/-- `cases/cost_ctct_e3_t257_full_d72.fhecheck.json.gz`: `N = 2¹⁷`, `t = 257`, 40 ciphertext primes of 52 bits (`log2 Q = 2080`), 7 special primes. -/
def cksSq257Cert : FullParams where
  src := { kind := .bfv, N := 131072, t := 257,
           qs := [4503599626321921, 4503599625535489, 4503599615311873, 4503599613214721,
                  4503599606661121, 4503599605350401, 4503599603515393, 4503599595651073,
                  4503599592767489, 4503599589359617, 4503599587000321, 4503599583068161,
                  4503599579922433, 4503599572320257, 4503599571271681, 4503599568125953,
                  4503599565766657, 4503599563407361, 4503599561310209, 4503599554756609,
                  4503599550824449, 4503599548465153, 4503599542960129, 4503599536930817,
                  4503599535882241, 4503599527231489, 4503599526445057, 4503599525920769,
                  4503599518842881, 4503599517270017, 4503599515697153, 4503599513075713,
                  4503599511764993, 4503599510192129, 4503599505211393, 4503599503114241,
                  4503599499706369, 4503599485812737, 4503599479521281, 4503599477686273] }
  store := { W := 131072,
             limbs := [⟨4503599626321921, 14522987458⟩, ⟨4503599625535489, 23376380174⟩,
                       ⟨4503599615311873, 30869578310⟩, ⟨4503599613214721, 10594833821⟩,
                       ⟨4503599606661121, 35821017720⟩, ⟨4503599605350401, 17001390416⟩,
                       ⟨4503599603515393, 3357762395⟩, ⟨4503599595651073, 16055616878⟩,
                       ⟨4503599592767489, 23964790414⟩, ⟨4503599589359617, 78132946201⟩,
                       ⟨4503599587000321, 35250931579⟩, ⟨4503599583068161, 42860389924⟩,
                       ⟨4503599579922433, 17607186431⟩, ⟨4503599572320257, 11146952415⟩,
                       ⟨4503599571271681, 1887111220⟩, ⟨4503599568125953, 34893721905⟩,
                       ⟨4503599565766657, 5446291128⟩, ⟨4503599563407361, 21315199621⟩,
                       ⟨4503599561310209, 100548879671⟩, ⟨4503599554756609, 474581545⟩,
                       ⟨4503599550824449, 10941589514⟩, ⟨4503599548465153, 49958148334⟩,
                       ⟨4503599542960129, 10930625412⟩, ⟨4503599536930817, 70994235620⟩,
                       ⟨4503599535882241, 157497102556⟩, ⟨4503599527231489, 18137677029⟩,
                       ⟨4503599526445057, 49900808066⟩, ⟨4503599525920769, 5555890213⟩,
                       ⟨4503599518842881, 107764157013⟩, ⟨4503599517270017, 124750852949⟩,
                       ⟨4503599515697153, 16451565173⟩, ⟨4503599513075713, 6466506836⟩,
                       ⟨4503599511764993, 4615242106⟩, ⟨4503599510192129, 51970838166⟩,
                       ⟨4503599505211393, 9582193436⟩, ⟨4503599503114241, 4970041798⟩,
                       ⟨4503599499706369, 3672661460⟩, ⟨4503599485812737, 23074571961⟩,
                       ⟨4503599479521281, 22881294420⟩, ⟨4503599477686273, 184894722489⟩],
             special := [⟨1152921504606584833, 30403152079314⟩, ⟨1152921504598720513, 11565110459493⟩,
                         ⟨1152921504592429057, 37675653583⟩, ⟨1152921504581419009, 2965188311474⟩,
                         ⟨1152921504580894721, 1491348944157⟩, ⟨1152921504578273281, 33773555664922⟩,
                         ⟨1152921504577748993, 2134070710646⟩] }
  secretBound := 1
  inputNoise := 0
  keyNoise := 39
  outputNoise := 0

/-- Digits of `α` limbs, canonical representatives. -/
def sqLayout (α : ℕ) : Budget.KSLayout := Budget.uniformLayout α true

/-- The data at `P` with the layout `lay` (errors in `[−39, 39]`, ternary `u`, no rotations). -/
def sqData (P : FullParams) (lay : Budget.KSLayout) : AbsScheme := bfvKSData P lay [] 39 1 39 39

/-- The circuit builder. -/
def mkSq (P : FullParams) (lay : Budget.KSLayout) (p : Program) (f : List Var)
    (c : Var → M (sqData P lay)) : (sqData P lay).Circ := (p, f, c)

/-- The class: `bfvClass` at the certified budget. -/
def admSq (P : FullParams) (lay : Budget.KSLayout) : (sqData P lay).Circ → Bool :=
  bfvClass (sqData P lay) lay [] (BudgetBFV.certified P lay)

/-- The evaluator: `bfvStep` with the keys of the public key. -/
def evSq (P : FullParams) (lay : Budget.KSLayout) : (sqData P lay).PK → (sqData P lay).Circ →
    List (CT (sqData P lay)) → List (CT (sqData P lay)) :=
  interpEval (sqData P lay) (bfvStepFn (sqData P lay) lay (fun pk => pk.2.2.1)
    (fun pk => pk.2.2.2))

/-- The squaring query on the fresh entries `sqIns`. -/
def sqQ (P : FullParams) (lay : Budget.KSLayout) (c : Var → M (sqData P lay)) :
    QCirc (sqData P lay) :=
  (sqProg P.src.qs.length 144, sqIns, c)

/-- **Refusal of the squaring circuit at `P`** with last accepted prefix `k` (module section
docstring). -/
def SqRefused (P : FullParams) (lay : Budget.KSLayout) (k : ℕ) : Prop :=
  Challenge.Profile.certifyBFVProfile? (sqData P lay).Pe (fun _ => BudgetBFV.certified P lay)
      (sqProg P.src.qs.length 144) = none ∧
  (∀ c, admSq P lay (mkSq P lay (sqProg P.src.qs.length 144) sqIns c) = false) ∧
  (∀ G, Reach (mkSq P lay) (admSq P lay) G → (∀ x ∈ sqIns, x ∈ G.fresh) → ∀ c,
    (∀ x ∈ constNames (sqQ P lay c) ++ (sqQ P lay c).1.body.map Trace.dst, x ∉ G.names) →
    admLM (mkSq P lay) (admSq P lay) G (sqQ P lay c) (sqIns.map fun x => (x, true)) = false) ∧
  (∀ c, admSq P lay (mkSq P lay (sqProg P.src.qs.length k) sqIns c) = true) ∧
  (∀ c, admSq P lay (mkSq P lay (sqProg P.src.qs.length (k + 1)) sqIns c) = false) ∧
  ∃ B, refAnalyzeBFVAt (sqData P lay).Pe (fun _ => BudgetBFV.certified P lay)
      (sqProg P.src.qs.length k) = some B ∧
    decOK P.src.t (P.src.modulus P.src.qs.length) (mulBound P.src.N P.src.t
      (P.src.modulus P.src.qs.length) (BudgetBFV.certified P lay).mulLift
      (BudgetBFV.certified P lay).mulRound B B) = false

/-- **The squaring circuit is in a class on which IND-CPA-D reduces to IND-CPA, at `P`.** -/
def SqReduces (P : FullParams) (lay : Budget.KSLayout) : Prop :=
  (∀ c, admSq P lay (mkSq P lay (sqProg P.src.qs.length 144) sqIns c) = true) ∧
  (∀ G, Reach (mkSq P lay) (admSq P lay) G → (∀ x ∈ sqIns, x ∈ G.fresh) → ∀ c,
    (∀ x ∈ constNames (sqQ P lay c) ++ (sqQ P lay c).1.body.map Trace.dst, x ∉ G.names) →
    admLM (mkSq P lay) (admSq P lay) G (sqQ P lay c) (sqIns.map fun x => (x, true)) = true) ∧
  (sqData P lay).EncOKBFV ∧
  Correct (freshScheme (sqData P lay) (admSq P lay) (evSq P lay) (sqData P lay).decBFV) ∧
  (∀ (s e a : IntPoly P.src.N), SecretOK P.secretBound s → normInf e ≤ 39 →
    ∀ (ra : ℕ → List (IntPoly P.src.N)) (ga : ℕ → ℕ → List (IntPoly P.src.N)),
      (sqData P lay).KeysOK (bfvKeyGen P lay s e a ra (onesErrL P.src.N P.src.qs.length) ga
        (fun _ => onesErrL P.src.N P.src.qs.length)) (s, e)) ∧
  ∀ [DecidableEq (M (sqData P lay))] {Ω Coins : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsFiniteMeasure μ] (pk : Ω → (sqData P lay).PK) (sk : Ω → (sqData P lay).SK)
    (tape : Ω → ℕ → (sqData P lay).ER) (coins : Ω → Coins)
    (A : Coins → (sqData P lay).PK → LAdv (sqData P lay) Bool) (q : ℕ),
    (∀ r p, BoundedLM (A r p) q) →
    |(μ {ω | gameLM (mkSq P lay) (admSq P lay) (evSq P lay) (sqData P lay).decBFV true (pk ω)
          (sk ω) (tape ω) (A (coins ω) (pk ω)) 0 [] (Global.empty (sqData P lay)) = true}).toReal -
        (μ {ω | gameLM (mkSq P lay) (admSq P lay) (evSq P lay) (sqData P lay).decBFV false (pk ω)
          (sk ω) (tape ω) (A (coins ω) (pk ω)) 0 [] (Global.empty (sqData P lay)) = true}).toReal| ≤
      |(μ {ω | gameCPA (S := freshScheme (sqData P lay) (admSq P lay) (evSq P lay)
            (sqData P lay).decBFV) true (pk ω) (tape ω) (reductionLM (mkSq P lay) (admSq P lay)
            (evSq P lay) (sqData P lay).decBFV A (coins ω) (pk ω)) 0 = true}).toReal -
        (μ {ω | gameCPA (S := freshScheme (sqData P lay) (admSq P lay) (evSq P lay)
            (sqData P lay).decBFV) false (pk ω) (tape ω) (reductionLM (mkSq P lay) (admSq P lay)
            (evSq P lay) (sqData P lay).decBFV A (coins ω) (pk ω)) 0 = true}).toReal| +
      2 * (μ {ω | ¬ ((sqData P lay).KeysOK (pk ω) (sk ω) ∧
        ∀ i < q, (sqData P lay).GoodE (pk ω) (sk ω) (tape ω i))}).toReal

/-- **The reduction for the squaring circuit at every BFV parameter set with special primes** at
which a fresh encryption decrypts and the circuit is in the class (closed checks), besides the
shape of the parameters. -/
theorem sqReduces_of (P : FullParams) (lay : Budget.KSLayout) (hk : P.src.kind = .bfv)
    (ht : 2 ≤ P.src.t) (hL : P.src.qs ≠ []) (hN : 1 ≤ P.src.N) (hkn : 1 ≤ P.keyNoise)
    (hsp : 3 ≤ Budget.specialProd P) (hq : ∀ q ∈ P.src.qs, 3 ≤ q)
    (hdec : decOK P.src.t (P.src.modulus P.src.qs.length) (sqData P lay).eps = true)
    (hmem : admSq P lay (mkSq P lay (sqProg P.src.qs.length 144) sqIns (fun _ => 0)) = true) :
    SqReduces P lay := sorry

/-- **`t = 257`, squaring attack (phase 1, 48 squarings): refused at the attack's parameter set,
in a class on which IND-CPA-D reduces to IND-CPA at the certified set the cost search recorded**
(`N = 2¹⁷`, 40 primes; not one more prime). At `cksSq257` the first 97 instructions (32
squarings and an addition) are accepted and the 33rd product is refused (`fhe_check`: "overflows
at body[97]"); at `cksSq257Cert` the whole circuit is in the class of the BFV evaluator `bfvStep`
(textbook product, our transcription of hybrid relinearization) and the reduction applies. Model
as in the module docstring. -/
theorem cks_ctct_t257 :
    SqRefused cksSq257 (sqLayout 6) 97 ∧ SqReduces cksSq257Cert (sqLayout 8) := sorry

/-- **The fresh-noise bounds are the input noises of the recorded runs** (`fheCheck.inputNoise`):
`out/ptct_n1{2,3,4,5,6}_coef.summary.json` for the attack sets,
`out/cost_ptct_n12_sameN_d6.summary.json` and `out/cost_ptct_n1{3,4,5,6}_sameN_d5.summary.json`
(the certified 5-limb runs) for the sets with the fifth prime, `out/ctct_e3_t257_p1.summary.json`
and `out/cost_ctct_e3_t257_full_d72.summary.json` for the squaring sets. For the sets with the
fifth prime this is the `Q mod t` fingerprint of the module docstring. -/
theorem cks_eps :
    (cksData cksN12).eps = 889334 ∧ (cksData cksN12Plus).eps = 1097592 ∧
    (cksData cksN13).eps = 2946451 ∧ (cksData cksN13Plus).eps = 2792468 ∧
    (cksData cksN14).eps = 30280324 ∧ (cksData cksN14Plus).eps = 17446959 ∧
    (cksData cksN15).eps = 15245566 ∧ (cksData cksN15Plus).eps = 31996980 ∧
    (cksData cksN16).eps = 5686500 ∧ (cksData cksN16Plus).eps = 5588864 ∧
    (sqData cksSq257 (sqLayout 6)).eps = 5112099 ∧
    (sqData cksSq257Cert (sqLayout 8)).eps = 10223899 := sorry

end Challenge.IndCpaDAttack
