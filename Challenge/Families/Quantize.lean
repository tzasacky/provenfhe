import Challenge.BFVMul

/-!
# Challenge.Families.Quantize — scale-invariant tensoring that rounds before it scales (Lattigo)   (LOCKED statements; proofs in `Validation/Families/Quantize.lean`)

The RNS multiplications of `Challenge.BFVMul` (HPS, P-over-Q, BEHZ) all compute an approximation
of `⌊t·T/Q⌉`: they scale by `t` and then divide. Lattigo's BFV multiplication (the scale-invariant
tensoring of its unified BGV/BFV evaluator) divides first and multiplies by `t` afterwards. That
is a different algorithm, not an HPS instance; this file states the family it belongs to and
proves the contract for it.

**Lattigo's algorithm, read from the source.** Lattigo v6.2.0 (commit
`c1fd095f08602e2d4ef571db015fc553fdd2d845`). `Evaluator.MulScaleInvariant` /
`MulRelinScaleInvariant` (`schemes/bgv/evaluator.go:705`, `:806`) call `tensorScaleInvariant`
(`:898-962`):

1. *Lift* (`modUpAndNTT`, `:991-1001`; `ring.BasisExtender.ModUpQtoP`,
   `ring/basis_extension.go:177-190`): each component is shifted by `⌊Q/2⌋` (`:185-187`),
   extended from `Q` to the auxiliary basis `QMul` by `ModUpExact` (`:282-308`), whose overflow
   count is the TRUNCATION of the binary64 sum `Σᵢ float64(yᵢ)/float64(qᵢ)` (`reconstructRNS`,
   `:550-595`; `vi += float64(y)/qif`, `v = uint64(vi)`), and shifted back (`:189`). In exact
   arithmetic this is the centred representative `[c]_Q` (for odd `Q`): `approxLift Q c 0`. With
   the binary64 error the overflow count can be off by one when the sum is within the error of an
   integer, i.e. when the shifted value is within that error of `0` or `Q`: the lift is then
   `[c]_Q ± Q`, `approxLift Q c u` with `‖u‖∞ ≤ 1`.
2. *Tensor* (`tensorLowDeg`, `:1003-1048`) limb-wise in `Q` and `QMul`.
3. *Quantize* (`quantize`, `:1050-1070`): `ModDownQPtoP` (`ring/basis_extension.go:262-278`)
   computes in `QMul` the integer `D = (T − L)/Q`, `L` the lift (step 1, same routine) of
   `[T]_Q`; `ModUpPtoQ` (`:195-209`) brings `D` back to `Q` as its centred representative modulo
   `QMul`; then `MulScalar(…, t)` (`evaluator.go:1067`) multiplies by `t`. The comment at
   `:1066` says it: "(ct(x)/Q)*T, doing so only requires that Q*P > Q*Q, faster but adds error
   ~|T|".

So the output is `t·D` with `D` within `(1 + 2v)·Q/2` of `T/Q` (`v = 0` exact, `v = 1` with the
binary64 overflow error), not `⌊t·T/Q⌉`: the rounding slack is `ρ = t·(1 + 2v)` instead of `1`.
`QMul` has `⌈(bitlen Q_ℓ + log₂N)/61⌉` primes at level `ℓ` (`evaluator.go:43-48`; the primes:
`params.go:98-104`, 61-bit NTT primes downward from `2⁶¹`): it budgets for `N·Q`, not for `t`, so
OpenFHE's HPS side condition `hpsAuxOK?` (`t·N·(Q−1)² + Q < P·Q`) FAILS at some levels of
Lattigo's own example parameters (checked below); what the algorithm needs instead is that `D`
is recovered from its residues modulo `QMul`, `quantizeAuxOK?`.

**What is proved here** (integer level, any library). `stepOK_mul_quantize`,
`stepOK_square_quantize`: every multiplication that multiplies lifts `approxLift Q c u` with
`‖u‖∞ ≤ U` and outputs `t·D` (modulo `Q`) with `2·|Q·Dⱼ − Tⱼ| ≤ Q·ρ₀` meets the contract at
`(mulLiftApprox P U, mulRoundApprox P (t·ρ₀))`. `quantize_round_ok`: the exact centred quotient
`D = ⌊T/Q⌉` has `ρ₀ = 1`. `stepOK_mul_quantize_lifted`, `stepOK_square_quantize_lifted`: the
same by the size of the
representatives (lift excess `e`). So Lattigo's tensoring, as read from the source, is covered at
`(U, ρ) = (0, t)` in exact arithmetic, and with the binary64 overflow error either at `(1, 3t)`
(whole multiples of `Q`; costs a level at Lattigo's example set, `Challenge.Families.Coverage`) or,
by size, at `e = 1 + ⌈2δQ⌉`, `ρ = 2t` for an overflow-sum error `δ` (no level lost), PROVIDED
its limb-level steps compute these integers: that is ARGUED above, not proved (no Lean
transcription of Lattigo's routines exists; `quantizeAuxOK?` is the side condition such a proof
would need, derived here, not used by a theorem).

**Cost.** `mulRoundApprox P t = t · mulRound P`: the rounding term of the noise of a product is
`t` times the textbook one. That term is small next to the `t·‖v‖·N·B_s` terms: on `sealProg`
at `sealBFV` the analyzer's bound moves by less than one part in a million (guards below). The
lift error of the binary64 overflow count (`U = 1`) is what costs: three bits there.
-/

namespace Challenge.Families
open Spec NPoly Scheme Source Challenge.BFV Challenge.BFVMul

variable (P : FullParams)

/-- **Rounding before scaling meets the `mul` contract.** As `Challenge.BFVMul.stepOK_mul_approx`,
with the output congruent modulo `Q` to `t·D` for integer polynomials `D₀, D₁, D₂` with
`2·|Q·Dⱼ − Tⱼ| ≤ Q·ρ₀` coefficientwise, `T` the tensor product of the lifts: the rounding slack is
`t·ρ₀`. -/
theorem stepOK_mul_quantize (hP : SchemeParamsOK P) (U ρ₀ : ℕ) (E : TraceBFV.Budget)
    (hL : BudgetBFV.mulLiftApprox P U ≤ E.mulLift)
    (hR : BudgetBFV.mulRoundApprox P (P.src.t * ρ₀) ≤ E.mulRound)
    (s : IntPoly P.src.N) (hs : SecretOK P.secretBound s) (ρ ρ' : Env P.src)
    (σ : Trace.CtEnv P) (d a b : Var) (x y : Val P.src) (ca cb : List (IntPoly P.src.N))
    (hstep : step P.src ρ (.mul d a b) = some ρ') (hx : ρ a = some x) (hy : ρ b = some y)
    (ha : σ a = some ca) (hb : σ b = some cb)
    (hla : ca.length = 2) (hlb : cb.length = 2) (h2x : x.parts = 2) (h2y : y.parts = 2)
    (hℓ : 1 ≤ x.level) (hℓL : x.level ≤ P.src.qs.length)
    (ua ub D out : List (IntPoly P.src.N))
    (hua : ua.length = 2) (hub : ub.length = 2) (hD : D.length = 3)
    (hUa : ∀ u ∈ ua, normInf u ≤ U) (hUb : ∀ u ∈ ub, normInf u ≤ U)
    (hquant : ∀ (j : ℕ) (i : Fin P.src.N),
      2 * |(P.src.modulus x.level : ℤ) * (D.getD j 0).coeff i -
          ((Challenge.Source.tensor (approxLift (P.src.modulus x.level) ca ua)
            (approxLift (P.src.modulus x.level) cb ub)).getD j 0).coeff i|
        ≤ (P.src.modulus x.level : ℤ) * ρ₀)
    (hout : out.map (ofInt (P.src.modulus x.level)) =
      (D.map fun p => (⟨fun i => (P.src.t : ℤ) * p.coeff i⟩ : IntPoly P.src.N)).map
        (ofInt (P.src.modulus x.level))) :
    TraceBFV.StepOK P E s ρ ρ' σ (σ.set d out) (.mul d a b) := sorry

/-- **Rounding before scaling meets the `square` contract** (the same lift on both sides). -/
theorem stepOK_square_quantize (hP : SchemeParamsOK P) (U ρ₀ : ℕ) (E : TraceBFV.Budget)
    (hL : BudgetBFV.mulLiftApprox P U ≤ E.mulLift)
    (hR : BudgetBFV.mulRoundApprox P (P.src.t * ρ₀) ≤ E.mulRound)
    (s : IntPoly P.src.N) (hs : SecretOK P.secretBound s) (ρ ρ' : Env P.src)
    (σ : Trace.CtEnv P) (d a : Var) (x : Val P.src) (ca : List (IntPoly P.src.N))
    (hstep : step P.src ρ (.square d a) = some ρ') (hx : ρ a = some x)
    (ha : σ a = some ca) (hla : ca.length = 2) (h2x : x.parts = 2)
    (hℓ : 1 ≤ x.level) (hℓL : x.level ≤ P.src.qs.length)
    (ua D out : List (IntPoly P.src.N))
    (hua : ua.length = 2) (hD : D.length = 3) (hUa : ∀ u ∈ ua, normInf u ≤ U)
    (hquant : ∀ (j : ℕ) (i : Fin P.src.N),
      2 * |(P.src.modulus x.level : ℤ) * (D.getD j 0).coeff i -
          ((Challenge.Source.tensor (approxLift (P.src.modulus x.level) ca ua)
            (approxLift (P.src.modulus x.level) ca ua)).getD j 0).coeff i|
        ≤ (P.src.modulus x.level : ℤ) * ρ₀)
    (hout : out.map (ofInt (P.src.modulus x.level)) =
      (D.map fun p => (⟨fun i => (P.src.t : ℤ) * p.coeff i⟩ : IntPoly P.src.N)).map
        (ofInt (P.src.modulus x.level))) :
    TraceBFV.StepOK P E s ρ ρ' σ (σ.set d out) (.square d a) := sorry

/-- **Rounding before scaling, by the size of the representatives** (the form of
`Challenge.BFVMul.stepOK_mul_lifted`): any integer representatives `A`, `B` of the operands
modulo `Q` with `2·‖·‖∞ ≤ Q + e`, output congruent to `t·D` with `2·|Q·Dⱼ − (A ⊗ B)ⱼ| ≤ Q·ρ₀`:
the contract holds at `(mulLiftNormAt P ℓ e, mulRoundApprox P (t·ρ₀))`. This is the form for a
lift that is off by `±Q` only next to `±Q/2` (Lattigo's binary64 overflow count, step 1 of the
module docstring): `e = 1 + ⌈2δQ⌉` and `ρ₀ = 2` for an overflow-sum error `δ ≤ 1/2`, instead of
`U = 1`, `ρ₀ = 3`. -/
theorem stepOK_mul_quantize_lifted (hP : SchemeParamsOK P) (e ρ₀ : ℕ) (E : TraceBFV.Budget)
    (s : IntPoly P.src.N) (hs : SecretOK P.secretBound s) (ρ ρ' : Env P.src)
    (σ : Trace.CtEnv P) (d a b : Var) (x y : Val P.src) (ca cb : List (IntPoly P.src.N))
    (hL : BudgetBFV.mulLiftNormAt P x.level e ≤ E.mulLift)
    (hR : BudgetBFV.mulRoundApprox P (P.src.t * ρ₀) ≤ E.mulRound)
    (hstep : step P.src ρ (.mul d a b) = some ρ') (hx : ρ a = some x) (hy : ρ b = some y)
    (ha : σ a = some ca) (hb : σ b = some cb)
    (hla : ca.length = 2) (hlb : cb.length = 2) (h2x : x.parts = 2) (h2y : y.parts = 2)
    (hℓ : 1 ≤ x.level) (hℓL : x.level ≤ P.src.qs.length)
    (A B D out : List (IntPoly P.src.N))
    (hA : A.map (ofInt (P.src.modulus x.level)) = ca.map (ofInt (P.src.modulus x.level)))
    (hB : B.map (ofInt (P.src.modulus x.level)) = cb.map (ofInt (P.src.modulus x.level)))
    (hD : D.length = 3)
    (hAn : ∀ p ∈ A, 2 * normInf p ≤ P.src.modulus x.level + e)
    (hBn : ∀ p ∈ B, 2 * normInf p ≤ P.src.modulus x.level + e)
    (hquant : ∀ (j : ℕ) (i : Fin P.src.N),
      2 * |(P.src.modulus x.level : ℤ) * (D.getD j 0).coeff i -
          ((Challenge.Source.tensor A B).getD j 0).coeff i|
        ≤ (P.src.modulus x.level : ℤ) * ρ₀)
    (hout : out.map (ofInt (P.src.modulus x.level)) =
      (D.map fun p => (⟨fun i => (P.src.t : ℤ) * p.coeff i⟩ : IntPoly P.src.N)).map
        (ofInt (P.src.modulus x.level))) :
    TraceBFV.StepOK P E s ρ ρ' σ (σ.set d out) (.mul d a b) := sorry

/-- **Rounding before scaling, by size: the `square` contract** (the same representatives on
both sides). -/
theorem stepOK_square_quantize_lifted (hP : SchemeParamsOK P) (e ρ₀ : ℕ) (E : TraceBFV.Budget)
    (s : IntPoly P.src.N) (hs : SecretOK P.secretBound s) (ρ ρ' : Env P.src)
    (σ : Trace.CtEnv P) (d a : Var) (x : Val P.src) (ca : List (IntPoly P.src.N))
    (hL : BudgetBFV.mulLiftNormAt P x.level e ≤ E.mulLift)
    (hR : BudgetBFV.mulRoundApprox P (P.src.t * ρ₀) ≤ E.mulRound)
    (hstep : step P.src ρ (.square d a) = some ρ') (hx : ρ a = some x)
    (ha : σ a = some ca) (hla : ca.length = 2) (h2x : x.parts = 2)
    (A D out : List (IntPoly P.src.N))
    (hA : A.map (ofInt (P.src.modulus x.level)) = ca.map (ofInt (P.src.modulus x.level)))
    (hD : D.length = 3)
    (hAn : ∀ p ∈ A, 2 * normInf p ≤ P.src.modulus x.level + e)
    (hquant : ∀ (j : ℕ) (i : Fin P.src.N),
      2 * |(P.src.modulus x.level : ℤ) * (D.getD j 0).coeff i -
          ((Challenge.Source.tensor A A).getD j 0).coeff i|
        ≤ (P.src.modulus x.level : ℤ) * ρ₀)
    (hout : out.map (ofInt (P.src.modulus x.level)) =
      (D.map fun p => (⟨fun i => (P.src.t : ℤ) * p.coeff i⟩ : IntPoly P.src.N)).map
        (ofInt (P.src.modulus x.level))) :
    TraceBFV.StepOK P E s ρ ρ' σ (σ.set d out) (.square d a) := sorry

/-- **The exact quotient has `ρ₀ = 1`**: `2·|Q·⌊T/Q⌉ − T| ≤ Q` for every integer `T` and every
`Q > 0` (`Spec.Scheme.roundDiv`). -/
theorem quantize_round_ok (T : ℤ) (Q : ℕ) (hQ : 0 < Q) :
    2 * |(Q : ℤ) * roundDiv T Q - T| ≤ (Q : ℤ) * 1 := sorry

/-! ## The side condition of the limb-level algorithm (derived, not used by a theorem) -/

/-- **Recovery of the quotient from `QMul`** (module docstring, step 3): with lifts within
`(1 + 2U)·Q/2` the tensor has `|T| ≤ N·Q²·(1 + 2U)²/2`, so `|D| ≤ N·Q·(1 + 2U)²/2 + ρ₀/2`, and
the centred lift of `D` from `QMul` (product `P`) is `D` itself when `2|D| ≤ P − 1`. Sufficient:
`N·Q·(1 + 2U)² + ρ₀ + 1 ≤ P`. (The float error of the centred lift from `QMul` itself is not
budgeted here.) -/
def quantizeAuxOK? (N : ℕ) (qs ps : List ℕ) (U ρ₀ : ℕ) : Bool :=
  decide (N * qs.prod * (1 + 2 * U) ^ 2 + ρ₀ + 1 ≤ ps.prod)

/-! ## Lattigo's example parameters

`ExampleParameters128BitLogN14LogQP438` (`schemes/bgv/examples_parameters.go:6-14`): `N = 2¹⁴`,
twelve ciphertext primes, `t = 65537`. `lattigoQMul` are the seven primes of `QMul`
(`NTTFriendlyPrimesGenerator(61, 2N).NextDownstreamPrimes(7)`, computed by
a script outside the repository); level `ℓ` uses the first
`⌈(bitlen Q_ℓ + 14)/61⌉` of them. -/

/-- The ciphertext primes of Lattigo's example set. -/
def lattigoQs : List ℕ :=
  [0x10000048001, 0x20008001, 0x1ffc8001, 0x20040001, 0x1ffc0001, 0x1ffb0001,
   0x20068001, 0x1ff60001, 0x200b0001, 0x200d0001, 0x1ff18001, 0x200f8001]

/-- The `QMul` primes of Lattigo's example set (section docstring). -/
def lattigoQMul : List ℕ :=
  [0x1fffffffffe10001, 0x1fffffffffe00001, 0x1fffffffffdd0001, 0x1fffffffffd08001,
   0x1fffffffffcf8001, 0x1fffffffffc80001, 0x1fffffffffb40001]

/-- The `QMul` primes Lattigo uses at level `ℓ` (`evaluator.go:43-48`). -/
def lattigoQMulAt (N : ℕ) (qs ps : List ℕ) (ℓ : ℕ) : List ℕ :=
  ps.take ((Nat.size (qs.take ℓ).prod + Nat.log2 N + 60) / 61)

/-- **At every level of Lattigo's example set the quotient is recovered**, in exact arithmetic
(`U = 0`, `ρ₀ = 1`) and with the binary64 overflow error (`U = 1`, `ρ₀ = 3`). -/
theorem lattigo_quantizeAuxOK : ∀ ℓ ∈ List.range' 1 12,
    quantizeAuxOK? 16384 (lattigoQs.take ℓ) (lattigoQMulAt 16384 lattigoQs lattigoQMul ℓ) 0 1 &&
      quantizeAuxOK? 16384 (lattigoQs.take ℓ) (lattigoQMulAt 16384 lattigoQs lattigoQMul ℓ) 1 3
    = true := sorry

-- OpenFHE's HPS side condition (which budgets for `t`) fails at levels 1, 3 and 5 of Lattigo's
-- example set: Lattigo's algorithm is not HPS.
#guard (List.range' 1 12).map (fun ℓ =>
    hpsAuxOK? 65537 16384 (lattigoQs.take ℓ) (lattigoQMulAt 16384 lattigoQs lattigoQMul ℓ))
  == [false, true, false, true, false, true, true, true, true, true, true, true]
#guard (List.range' 1 12).map (fun ℓ => (lattigoQMulAt 16384 lattigoQs lattigoQMul ℓ).length)
  == [1, 2, 2, 3, 3, 4, 4, 5, 5, 6, 6, 7]
-- The cost against the textbook rounding, at `sealBFV` (`t = 65537`), on `sealProg`: the
-- rounding slack `t` (exact quantization, `U = 0`) moves the analyzer's bound by less than one
-- part in a million (the rounding term is dominated by the `t·‖v‖·N·B_s` terms); the
-- float-tolerant form (`U = 1`, `ρ = 3t`) costs three bits, all of them from `U = 1`.
#guard refAnalyzeBFV sealBFV (sealBudget ⟨0, 1, true⟩) sealProg
  == some 1487107268480789873794743232688495335249
#guard refAnalyzeBFV sealBFV (sealBudget ⟨0, 65537, true⟩) sealProg
  == some 1487108567684153328513261127222505314129
#guard (refAnalyzeBFV sealBFV (sealBudget ⟨2 * sealBFV.src.modulus 4, 3 * 65537, true⟩)
    sealProg).map Nat.log2 == some 133

-- Rejections: the binary64 whole-multiple form `(U, ρ₀) = (1, 3)` fails at a single 50-bit
-- prime with `N = 2¹¹` (`QMul` one prime, `⌈(50 + 11)/61⌉ = 1`), where the exact form holds
-- with almost no margin (`lattigo_edge.py`); too small a `QMul` fails both.
#guard quantizeAuxOK? 2048 [1125899906826241] [2305843009213616129] 0 1
#guard !quantizeAuxOK? 2048 [1125899906826241] [2305843009213616129] 1 3
#guard !quantizeAuxOK? 16384 lattigoQs (lattigoQMul.take 6) 0 1

end Challenge.Families
