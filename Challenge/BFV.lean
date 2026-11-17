import Challenge.BFV.Defs

/-!
# Challenge.BFV — the BFV noise headline   (LOCKED statements; proofs in `Validation/BFV/`)

What the statements mean is defined in `Spec/TraceBFV.lean` (phase contracts of the BFV
operations), `Spec/BudgetBFV.lean` (the budget of the textbook algorithms) and
`Challenge/BFV/Defs.lean` (the headline predicate and the reference analyzer `refAnalyzeBFV`).

* **Decryption.** `bfv_decrypt_of_noise`: the acceptance condition `2·(t·B + (Q mod t)·(t−1)) < Q`
  makes the noise clause of `BFVEncrypts` imply exact decryption. `encrypts_bfv_iff_phase`,
  `encrypts_bfv_decrypts`: the phase used by `Spec.TraceBFV` is the one `Encrypts` decrypts.
* **Headline.** `refAnalyzeBFV_sound`: the reference analyzer is sound for every run meeting the
  contracts. `refAnalyzeBFV_rejects_nonBFV`, `refAnalyzeBFV_badDecl`: scope.
* **Non-vacuity.** `sealBFV_ok`, `bfv_inputs_exist`: the hypotheses can be met;
  `refAnalyzeBFV_accepts_seal`: a depth-2 program with a rotation is accepted at a parameter set
  of the shape commonly used with BFV (N = 8192, 174-bit modulus) with the certified budget; the `stepOK_*` and `*_realizable` pins (here and in
  `Challenge/BFV/Domain.lean`): every contract is met by the textbook algorithm within
  `Spec.BudgetBFV.certified`, on the domain where the analyzer accepts the operation (products
  and modulus switching: two-component operands; the analyzer rejects them otherwise).
  `Challenge.BFV.certified_run_exists` (`Challenge/BFV/Domain.lean`): every program accepted at
  the certified budget has a ciphertext-level run from every valid input.

The statement is about the locked analyzer itself, not about a definition hole: a faster or
tighter analyzer can later be required to satisfy `NoiseSoundBFV` and to be never worse than
`refAnalyzeBFV`.
-/

namespace Challenge.BFV
open Spec NPoly Scheme Source Correct

/-! ## Decryption -/

/-- **The decryption condition.** If the phase is `⌊Q/t⌋·m + e (mod Q)` with `‖e‖∞ ≤ B` and
`2·(t·B + (Q mod t)·(t − 1)) < Q`, the ciphertext decrypts to `m`: the noise clause of
`BFVEncrypts` gives the whole of it. -/
theorem bfv_decrypt_of_noise {N : ℕ} (t Q B : ℕ) (ht : 0 < t) (s : IntPoly N)
    (ct : List (Poly Q N)) (m : Poly t N)
    (hnoise : normInf (centered (phase (ofInt Q s) ct -
      ofInt Q ⟨fun i => ((Q / t * (m.coeff i).val : ℕ) : ℤ)⟩)) ≤ B)
    (hB : decOK t Q B = true) : BFVEncrypts t B s ct m := sorry

-- The condition is the exact threshold at small parameters (all messages, all `|e| ≤ B`, by
-- enumeration): `t = 7`, `Q = 1000` (`r = 6`): `B = 66` decrypts, `B = 67` does not.
#guard decOK 7 1000 66 && !decOK 7 1000 67
#guard (List.range 7).all fun m => (List.range 133).all fun j =>
  let Φ : ℤ := (((1000 / 7 * m : ℕ) : ℤ) + ((j : ℤ) - 66) : ZMod 1000).valMinAbs
  ((roundDiv (7 * Φ) 1000 : ℤ) : ZMod 7) == (m : ZMod 7)
#guard
  let Φ : ℤ := (((1000 / 7 * 6 : ℕ) : ℤ) + (-67 : ℤ) : ZMod 1000).valMinAbs
  ((roundDiv (7 * Φ) 1000 : ℤ) : ZMod 7) != (6 : ZMod 7)

variable (P : FullParams)

/-- `Encrypts`, for BFV, in terms of `Trace.phaseAt`. -/
theorem encrypts_bfv_iff_phase (hk : P.src.kind = .bfv) (s : IntPoly P.src.N) (B : ℕ)
    (v : Val P.src) (m : Poly P.src.t P.src.N) (hm : v.msg = .exact m)
    (ct : List (IntPoly P.src.N)) :
    Encrypts P s B v ct ↔
      ct.length = v.parts ∧
      (⟨fun i => (roundDiv (P.src.t *
          (centered (Trace.phaseAt P (P.src.modulus v.level) v.key s ct)).coeff i)
          (P.src.modulus v.level) : ZMod P.src.t)⟩ : Poly P.src.t P.src.N) = m ∧
      normInf (centered (Trace.phaseAt P (P.src.modulus v.level) v.key s ct -
        ofInt (P.src.modulus v.level)
          ⟨fun i => ((P.src.modulus v.level / P.src.t * (m.coeff i).val : ℕ) : ℤ)⟩)) ≤ B := sorry

/-- For BFV, a ciphertext that `Encrypts` a value decrypts to its message exactly, by the
decryption function pinned in `Challenge.Scheme`, under the key the value is recorded under. -/
theorem encrypts_bfv_decrypts (hk : P.src.kind = .bfv) (s : IntPoly P.src.N) (B : ℕ)
    (v : Val P.src) (ct : List (IntPoly P.src.N)) (h : Encrypts P s B v ct) :
    ∃ m, v.msg = .exact m ∧
      bfvDecrypt P.src.t (automorph v.key s) (ct.map (ofInt (P.src.modulus v.level))) = m := sorry

/-! ## The headline -/

/-- **BFV noise headline: the reference analyzer is sound.** -/
theorem refAnalyzeBFV_sound : NoiseSoundBFV refAnalyzeBFV := sorry

/-- **Scope.** Nothing outside BFV is accepted. -/
theorem refAnalyzeBFV_rejects_nonBFV : NoiseRejectsNonBFV refAnalyzeBFV := sorry

/-- The reference analyzer rejects every program with an ill-formed input declaration. -/
theorem refAnalyzeBFV_badDecl (E : TraceBFV.Budget) (prog : Source.Program) (d : Decl)
    (hd : d ∈ prog.inputs)
    (h : d.parts = 0 ∨ d.level = 0 ∨ P.src.qs.length < d.level ∨ d.key % 2 = 0 ∨
      2 * P.src.N ≤ d.key) :
    refAnalyzeBFV P E prog = none := sorry

/-! ## Non-vacuity: parameters, inputs, acceptance -/

/-- A BFV parameter set of the shape commonly used with BFV (N = 8192, 174-bit modulus):
`N = 2¹³`, `t = 65537`, a 174-bit ciphertext modulus of two 43-bit and two 44-bit primes and one
44-bit special prime (the largest NTT-friendly primes of those sizes), ternary secret. Nothing
here is a claim about any library's defaults or samplers; the names `sealBFV`, `sealProg` are
historical.

Errors: every error coefficient is assumed to lie in `[−21, 21]` (for example a centred binomial
distribution with 42 coin flips, which has that support), so `21` bounds every error coefficient
with certainty (no tail cut). `keyNoise = 21` is that bound for the error of a
key-switching key. `inputNoise = 2¹⁹` covers the worst case of a fresh public-key encryption:
the phase is `⌊Q·m/t⌉ + e·u + e₁ + e₂·s` with ternary `u`, `s` and errors `e`, `e₁`, `e₂` in
`[−21, 21]`, so the noise relative to `⌊Q/t⌋·m` (what `BFVEncrypts` bounds) is at most
`21·(2N + 1) + (Q mod t) ≤ 344085 + 65536 = 409621 < 2¹⁹ = 524288` (the term `Q mod t` is the
difference between `⌊Q·m/t⌉` and `⌊Q/t⌋·m`). These are worst-case bounds of the assumed
distributions, not a model of any library's code. -/
def sealBFV : FullParams where
  src := { kind := .bfv, N := 8192,
           qs := [8796092858369, 8796092792833, 17592186028033, 17592185438209], t := 65537 }
  store := {
    W := 8192
    limbs := [⟨8796092858369, 4732080483711⟩, ⟨8796092792833, 3833382005217⟩,
              ⟨17592186028033, 13285651579259⟩, ⟨17592185438209, 4944083735799⟩]
    special := [⟨17592184717313, 14804678051466⟩] }
  secretBound := 1
  inputNoise := 2 ^ 19
  keyNoise := 21
  outputNoise := 0

/-- The instance is valid at the scheme level. -/
theorem sealBFV_ok : SchemeParamsOK sealBFV := sorry

#guard schemeParamsOK? sealBFV
#guard Budget.specialOK? sealBFV

/-- Every message has a BFV encryption with noise `0` under every secret, with any number of
components, at every level whose modulus satisfies the decryption condition for `B = 0`: the
input hypothesis of the headline is satisfiable. -/
theorem bfv_inputs_exist (hk : P.src.kind = .bfv) (ht : 0 < P.src.t) (s : IntPoly P.src.N)
    (v : Val P.src) (m : Poly P.src.t P.src.N) (hm : v.msg = .exact m) (hp : 1 ≤ v.parts)
    (hQ : decOK P.src.t (P.src.modulus v.level) 0 = true) :
    ∃ ct, Encrypts P s 0 v ct := sorry

/-- A tiny BFV instance for the checks below: `N = 4`, `Q = 65537 · 786433`, `t = 17`. -/
def tinyBFV : FullParams where
  src := { kind := .bfv, N := 4, qs := [65537, 786433], t := 17 }
  store := { W := 2, limbs := [⟨65537, 16⟩, ⟨786433, 241748⟩], special := [] }
  secretBound := 1
  inputNoise := 64
  keyNoise := 64
  outputNoise := 0

/-- A budget for programs that only add (no key switch, modulus switch, product, or inexact
plaintext addition). -/
def noBudget : TraceBFV.Budget := ⟨0, 0, 0, 0, 0⟩

/-- A depth-2 program with a rotation and plaintext operations, on fresh two-component
ciphertexts at the top level: `y = relin(σ₃(relin(a·b)) · c)·p + q`, with centred plaintexts
(`‖p‖∞, ‖q‖∞ ≤ 32768`). -/
def sealProg : Source.Program :=
  { inputs := [⟨"a", 2, 4, 1, 1⟩, ⟨"b", 2, 4, 1, 1⟩, ⟨"c", 2, 4, 1, 1⟩,
               ⟨"p", 1, 4, 1, 1⟩, ⟨"q", 1, 4, 1, 1⟩],
    bounds := [("p", 32768), ("q", 32768)],
    body := [.mul "ab" "a" "b", .relin "ab" "ab", .automorph "r" "ab" 3, .keySwitch "r" "r",
             .mul "y" "r" "c", .relin "y" "y", .mulPlain "y" "y" "p", .addPlain "y" "y" "q"],
    outputs := ["y"] }

/-- The reference analyzer accepts `sealProg` at `sealBFV` with the certified budget of the
textbook algorithms (one limb per key-switching digit), with a bound below `2¹³¹`; decryption
needs a bound below about `Q/(2t) ≈ 2¹⁵⁶`. -/
theorem refAnalyzeBFV_accepts_seal :
    ∃ B, refAnalyzeBFV sealBFV (BudgetBFV.certified sealBFV (Budget.uniformLayout 1)) sealProg
      = some B ∧ B ≤ 2 ^ 131 := sorry

-- The certified budget at `sealBFV`, and the bounds along `sealProg` (compiled evaluation).
#guard BudgetBFV.ksBudget sealBFV (Budget.uniformLayout 1) == 262144
#guard BudgetBFV.msBudget sealBFV == 4097
#guard BudgetBFV.mulLift sealBFV == 4097
#guard BudgetBFV.mulRound sealBFV == 67117057
#guard refAnalyzeBFV sealBFV (BudgetBFV.certified sealBFV (Budget.uniformLayout 1)) sealProg
  == some 1487107268480789873794743232688495311414
#guard refAnalyzeBFV sealBFV (BudgetBFV.certified sealBFV (Budget.uniformLayout 1))
  { sealProg with body := sealProg.body.take 2, outputs := ["ab"] } == some 2517375493271807815
-- Worst-case depth at `sealBFV`: three squarings of a fresh ciphertext (each relinearized) are
-- accepted (bounds about `2⁶¹`, `2¹⁰³`, `2¹⁴⁵`), a fourth is rejected.
#guard (List.range 5).map (fun n => (refAnalyzeBFV sealBFV
    (BudgetBFV.certified sealBFV (Budget.uniformLayout 1))
    { inputs := [⟨"a", 2, 4, 1, 1⟩],
      body := (List.replicate n [Instr.square "a" "a", .relin "a" "a"]).flatten,
      outputs := ["a"] }).map Nat.log2) == [some 19, some 61, some 103, some 145, none]

/-! Discrimination, at `tinyBFV` (`Q = 51540459521`, `Q mod t = 9`, `inputNoise = 64`). -/

-- A sum: `64 + 64 + 9`. The carry `Q mod t` is part of the bound.
#guard refAnalyzeBFV tinyBFV noBudget
  { inputs := [⟨"a", 2, 2, 1, 1⟩, ⟨"b", 2, 2, 1, 1⟩], body := [.add "c" "a" "b"],
    outputs := ["c"] } == some 137
-- The decryption condition is the acceptance threshold: `2·(17·B + 9·16) < Q` holds for
-- `B = 2·757947925 + 9` and fails for `B = 2·757947926 + 9`.
#guard refAnalyzeBFV { tinyBFV with inputNoise := 757947925 } noBudget
  { inputs := [⟨"a", 2, 2, 1, 1⟩, ⟨"b", 2, 2, 1, 1⟩], body := [.add "c" "a" "b"],
    outputs := ["c"] } == some 1515895859
#guard refAnalyzeBFV { tinyBFV with inputNoise := 757947926 } noBudget
  { inputs := [⟨"a", 2, 2, 1, 1⟩, ⟨"b", 2, 2, 1, 1⟩], body := [.add "c" "a" "b"],
    outputs := ["c"] } == none
-- A product with the textbook budget (`mulLift = 3`, `mulRound = 21`), and a second one (after
-- relinearization, here with key-switching budget `0`: a product of a three-component value is
-- outside the domain of the rules, `Challenge/BFV/Domain.lean`).
#guard refAnalyzeBFV tinyBFV ⟨0, 0, 3, 21, 0⟩
  { inputs := [⟨"a", 2, 2, 1, 1⟩, ⟨"b", 2, 2, 1, 1⟩], body := [.mul "c" "a" "b"],
    outputs := ["c"] } == some 48744
#guard refAnalyzeBFV tinyBFV ⟨0, 0, 3, 21, 0⟩
  { inputs := [⟨"a", 2, 2, 1, 1⟩, ⟨"b", 2, 2, 1, 1⟩],
    body := [.mul "c" "a" "b", .relin "c" "c", .square "c" "c"], outputs := ["c"] }
  == some 32761707
-- A larger lift or rounding budget (an RNS multiplication) costs noise.
#guard refAnalyzeBFV tinyBFV ⟨0, 0, 4, 21, 0⟩
  { inputs := [⟨"a", 2, 2, 1, 1⟩, ⟨"b", 2, 2, 1, 1⟩], body := [.mul "c" "a" "b"],
    outputs := ["c"] } == some 58600
#guard refAnalyzeBFV tinyBFV ⟨0, 0, 3, 121, 0⟩
  { inputs := [⟨"a", 2, 2, 1, 1⟩, ⟨"b", 2, 2, 1, 1⟩], body := [.mul "c" "a" "b"],
    outputs := ["c"] } == some 48794
-- Modulus switching: `⌊64 / 786433⌋ + 3 + (65537 mod 17)`; key switching of an input under
-- `σ₃(s)`; rotation and a constant multiple: `|−5|·((64 + 9) + 9)`.
#guard refAnalyzeBFV tinyBFV ⟨0, 3, 0, 0, 0⟩
  { inputs := [⟨"a", 2, 2, 1, 1⟩], body := [.modSwitch "c" "a"], outputs := ["c"] } == some 5
#guard refAnalyzeBFV tinyBFV ⟨5, 0, 0, 0, 0⟩
  { inputs := [⟨"a", 2, 2, 1, 3⟩], body := [.keySwitch "c" "a"], outputs := ["c"] } == some 69
#guard refAnalyzeBFV tinyBFV noBudget
  { inputs := [⟨"a", 2, 2, 1, 1⟩], body := [.automorph "c" "a" 3, .mulConst "c" "c" (-5)],
    outputs := ["c"] } == some 410
-- Plaintexts: an undeclared one counts `t − 1 = 16` (`64 + 9·1`); a declared bound of `8` in a
-- product gives `4·8·(64 + 9)`; an inexact plaintext addition (`plainAdd = 9`) is charged.
#guard refAnalyzeBFV tinyBFV noBudget
  { inputs := [⟨"a", 2, 2, 1, 1⟩, ⟨"p", 1, 2, 1, 1⟩], body := [.addPlain "c" "a" "p"],
    outputs := ["c"] } == some 73
#guard refAnalyzeBFV tinyBFV ⟨0, 0, 0, 0, 9⟩
  { inputs := [⟨"a", 2, 2, 1, 1⟩, ⟨"p", 1, 2, 1, 1⟩], body := [.subPlain "c" "a" "p"],
    outputs := ["c"] } == some 82
#guard refAnalyzeBFV tinyBFV noBudget
  { inputs := [⟨"a", 2, 2, 1, 1⟩, ⟨"p", 1, 2, 1, 1⟩], bounds := [("p", 8)],
    body := [.mulPlain "c" "a" "p"], outputs := ["c"] } == some 2336
-- Rejections: a plaintext used as a ciphertext operand; a plaintext output; a ciphertext used
-- as a plaintext; `dropLimbs` (not a BFV operation); another scheme; an undefined operand.
#guard refAnalyzeBFV tinyBFV noBudget
  { inputs := [⟨"a", 2, 2, 1, 1⟩, ⟨"p", 1, 2, 1, 1⟩], body := [.add "c" "a" "p"],
    outputs := ["c"] } == none
#guard refAnalyzeBFV tinyBFV noBudget
  { inputs := [⟨"a", 2, 2, 1, 1⟩, ⟨"p", 1, 2, 1, 1⟩], body := [.copy "c" "p"],
    outputs := ["c"] } == none
#guard refAnalyzeBFV tinyBFV noBudget
  { inputs := [⟨"a", 2, 2, 1, 1⟩, ⟨"b", 2, 2, 1, 1⟩], body := [.mulPlain "c" "a" "b"],
    outputs := ["c"] } == none
#guard refAnalyzeBFV tinyBFV noBudget
  { inputs := [⟨"a", 2, 2, 1, 1⟩], body := [.dropLimbs "c" "a" 1], outputs := ["c"] } == none
#guard refAnalyzeBFV { tinyBFV with src := { tinyBFV.src with kind := .bgv } } noBudget
  { inputs := [⟨"a", 2, 2, 1, 1⟩], body := [], outputs := ["a"] } == none
#guard refAnalyzeBFV tinyBFV noBudget
  { inputs := [⟨"a", 2, 2, 1, 1⟩], body := [.add "c" "a" "nope"], outputs := ["c"] } == none

/-! ## Realizability: the textbook algorithms meet the contracts -/

/-- Componentwise addition (the shorter ciphertext padded with zero components) meets the `add`
contract. -/
theorem stepOK_add_padded (E : TraceBFV.Budget) (s : IntPoly P.src.N) (ρ ρ' : Env P.src)
    (σ : Trace.CtEnv P) (d a b : Var) (x y : Val P.src) (ca cb : List (IntPoly P.src.N))
    (hstep : step P.src ρ (.add d a b) = some ρ') (hx : ρ a = some x) (hy : ρ b = some y)
    (ha : σ a = some ca) (hb : σ b = some cb)
    (hla : ca.length = x.parts) (hlb : cb.length = y.parts) :
    TraceBFV.StepOK P E s ρ ρ' σ (σ.set d (Challenge.Source.padZip (· + ·) ca cb))
      (.add d a b) := sorry

/-- Adding `⌊Q/t⌋·p` to the first component meets the `addPlain` contract, with no deviation
(every budget). -/
theorem stepOK_addPlain_textbook (E : TraceBFV.Budget) (s : IntPoly P.src.N) (ρ ρ' : Env P.src)
    (σ : Trace.CtEnv P) (d a p : Var) (x y : Val P.src) (ca : List (IntPoly P.src.N))
    (c : IntPoly P.src.N)
    (hstep : step P.src ρ (.addPlain d a p) = some ρ') (hx : ρ a = some x) (hy : ρ p = some y)
    (ha : σ a = some ca) (hp : σ p = some [c]) (hla : ca.length = x.parts) :
    TraceBFV.StepOK P E s ρ ρ' σ
      (σ.set d (bfvAddPlain P.src.t (P.src.modulus x.level) ca c)) (.addPlain d a p) := sorry

/-- Multiplying every component by the plaintext polynomial meets the `mulPlain` contract. -/
theorem stepOK_mulPlain_textbook (E : TraceBFV.Budget) (s : IntPoly P.src.N) (ρ ρ' : Env P.src)
    (σ : Trace.CtEnv P) (d a p : Var) (x y : Val P.src) (ca : List (IntPoly P.src.N))
    (c : IntPoly P.src.N)
    (hstep : step P.src ρ (.mulPlain d a p) = some ρ') (hx : ρ a = some x) (hy : ρ p = some y)
    (ha : σ a = some ca) (hp : σ p = some [c]) (hla : ca.length = x.parts) :
    TraceBFV.StepOK P E s ρ ρ' σ (σ.set d (ca.map (c * ·))) (.mulPlain d a p) := sorry

/-- **Textbook multiplication meets the `mul` contract** with `mulLift = ⌊(2 + N·B_s)/2⌋` and
`mulRound = 1 + N·B_s + (N·B_s)²` (`Spec.BudgetBFV`), for two-component operands under any
secret within the bound. -/
theorem stepOK_mul_textbook (hP : SchemeParamsOK P) (E : TraceBFV.Budget)
    (hL : BudgetBFV.mulLift P ≤ E.mulLift) (hR : BudgetBFV.mulRound P ≤ E.mulRound)
    (s : IntPoly P.src.N) (hs : SecretOK P.secretBound s) (ρ ρ' : Env P.src)
    (σ : Trace.CtEnv P) (d a b : Var) (x y : Val P.src) (ca cb : List (IntPoly P.src.N))
    (hstep : step P.src ρ (.mul d a b) = some ρ') (hx : ρ a = some x) (hy : ρ b = some y)
    (ha : σ a = some ca) (hb : σ b = some cb)
    (hla : ca.length = 2) (hlb : cb.length = 2) (h2x : x.parts = 2) (h2y : y.parts = 2) :
    TraceBFV.StepOK P E s ρ ρ' σ
      (σ.set d (bfvMul P.src.t (P.src.modulus x.level) ca cb)) (.mul d a b) := sorry

/-- **Rounding every component meets the `modSwitch` contract** with
`modSwitch = ⌈(1 + N·B_s)/2⌉`, for two-component ciphertexts. -/
theorem stepOK_modSwitch_textbook (hP : SchemeParamsOK P) (E : TraceBFV.Budget)
    (hE : BudgetBFV.msBudget P ≤ E.modSwitch)
    (s : IntPoly P.src.N) (hs : SecretOK P.secretBound s) (ρ ρ' : Env P.src)
    (σ : Trace.CtEnv P) (d a : Var) (x : Val P.src) (ca : List (IntPoly P.src.N))
    (hstep : step P.src ρ (.modSwitch d a) = some ρ') (hx : ρ a = some x)
    (ha : σ a = some ca) (hℓL : x.level ≤ P.src.qs.length) (h2 : x.parts = 2)
    (hla : ca.length = 2) :
    TraceBFV.StepOK P E s ρ ρ' σ
      (σ.set d (ca.map (bfvModSwitchComp P.src.qs[x.level - 1]!))) (.modSwitch d a) := sorry

/-- **Relinearization within `BudgetBFV.ksBoundAt`**: at every level there is a function of the
operand ciphertext and the key-switching keys alone whose output meets the `relin` contract, for
every secret within the bound and every list of gadget keys valid for it with noise at most
`P.keyNoise` (`Spec.Budget.GadgetKeysOK`; for BFV the key errors need not be multiples of `t`). -/
theorem relin_realizable (lay : Budget.KSLayout)
    (hP : SchemeParamsOK P) (hS : Budget.SpecialOK P) (ℓ : ℕ)
    (hℓ : ℓ ≤ P.src.qs.length) (hlay : lay.okAt ℓ = true) :
    ∃ f : List (IntPoly P.src.N) → List (IntPoly P.src.N × IntPoly P.src.N) →
        List (IntPoly P.src.N),
      ∀ (E : TraceBFV.Budget), BudgetBFV.ksBoundAt P lay ℓ ≤ E.keySwitch →
      ∀ (s : IntPoly P.src.N), SecretOK P.secretBound s →
      ∀ (keys : List (IntPoly P.src.N × IntPoly P.src.N)),
        Budget.GadgetKeysOK P lay ℓ .square s keys →
      ∀ (ρ ρ' : Env P.src) (σ : Trace.CtEnv P) (d a : Var) (x : Val P.src)
        (ca : List (IntPoly P.src.N)),
        step P.src ρ (.relin d a) = some ρ' → ρ a = some x → σ a = some ca → x.level = ℓ →
        ca.length = x.parts →
        TraceBFV.StepOK P E s ρ ρ' σ (σ.set d (f ca keys)) (.relin d a) := sorry

/-- **Key switching within `BudgetBFV.ksBoundAt`.** The operand is under `σ_g(s)`, `g` its
recorded key; the keys are valid for the target `σ_g(s)`. -/
theorem keySwitch_realizable (lay : Budget.KSLayout)
    (hP : SchemeParamsOK P) (hS : Budget.SpecialOK P) (ℓ : ℕ)
    (hℓ : ℓ ≤ P.src.qs.length) (hlay : lay.okAt ℓ = true) :
    ∃ f : List (IntPoly P.src.N) → List (IntPoly P.src.N × IntPoly P.src.N) →
        List (IntPoly P.src.N),
      ∀ (E : TraceBFV.Budget), BudgetBFV.ksBoundAt P lay ℓ ≤ E.keySwitch →
      ∀ (s : IntPoly P.src.N), SecretOK P.secretBound s →
      ∀ (ρ ρ' : Env P.src) (σ : Trace.CtEnv P) (d a : Var) (x : Val P.src)
        (ca : List (IntPoly P.src.N)),
        step P.src ρ (.keySwitch d a) = some ρ' → ρ a = some x → σ a = some ca → x.level = ℓ →
        ca.length = x.parts →
      ∀ (keys : List (IntPoly P.src.N × IntPoly P.src.N)),
        Budget.GadgetKeysOK P lay ℓ (.galois x.key) s keys →
        TraceBFV.StepOK P E s ρ ρ' σ (σ.set d (f ca keys)) (.keySwitch d a) := sorry

/-- `ksBudget` is at least `ksBoundAt` at every level of the chain, so the realizability pins
hold with `E = Spec.BudgetBFV.certified P lay`. -/
theorem ksBoundAt_le_ksBudget (lay : Budget.KSLayout) (ℓ : ℕ) (h1 : 1 ≤ ℓ)
    (hℓ : ℓ ≤ P.src.qs.length) : BudgetBFV.ksBoundAt P lay ℓ ≤ BudgetBFV.ksBudget P lay := sorry

end Challenge.BFV
