import Challenge.BFV
import Challenge.BFVMul.HPS
import Challenge.BFVMul.BEHZ
import Challenge.BFVMul.POverQ
import Spec.BudgetBFVRns
import Spec.Encrypt

/-!
# Challenge.BFVMul — BFV as libraries run it: approximate (RNS) multiplication   (LOCKED statements; proofs in `Validation/BFVMul/`)

`Challenge.BFV` proves the `mul` contract of `Spec.TraceBFV` for the textbook algorithm only. OpenFHE
does not run it: it multiplies in RNS (BEHZ, HPS, and its P-over-Q variants). This file closes that gap in two layers.

1. **Every approximate multiplication meets the contract** (`stepOK_mul_approx`,
   `stepOK_square_approx`). The hypothesis is about integers only, component by component, with no
   secret key and no algorithm in it: the algorithm multiplies representatives
   `Aᵢ = [cᵢ]_Q + Q·uᵢ`, `‖uᵢ‖∞ ≤ U` (`approxLift`), and each component `Xⱼ` of its result is
   within `ρ/2` of `t·(A ⊗ B)ⱼ/Q` (`2·|Q·Xⱼ − t·Tⱼ| ≤ Q·ρ`). Then for every secret within the
   bound the contract holds with `Spec.BudgetBFV.mulLiftApprox P U`,
   `Spec.BudgetBFV.mulRoundApprox P ρ`. An RNS variant is covered once its `U` and `ρ` are known;
   `U = 0`, `ρ = 1` is the textbook algorithm.
2. **The remaining textbook operations** (`stepOK_sub_padded`, `stepOK_subPlain_textbook`,
   `stepOK_mulConst_textbook`, `stepOK_automorph_textbook`, `stepOK_square_textbook`) and
   **plaintext addition by rounding** (`stepOK_addPlain_rounded`: adding `⌊Q·p/t⌉`, within
   `Spec.BudgetBFV.plainAddRoundedAt`; `stepOK_addPlain_scaled`: adding any polynomial within one
   unit of `Q·p/t`, within `Spec.BudgetBFV.plainAddScaledAt`. OpenFHE adds `⌈Q·p/t⌉`
   (`Spec/EncryptBFV.lean`), which the second covers: the method `scaled`).
3. **The certificate** `certified_decrypts`: acceptance by the reference analyzer, with every
   output under the secret key itself, gives exact decryption *with `s`* of every output of every
   run within the budget. `certifiedApprox_sound`: the headline at the budget of an approximate
   multiplication.

The idealised RNS algorithms themselves (limb by limb), and the pins that they have the slacks
claimed, are in `Challenge/BFVMul/`.
-/

namespace Challenge.BFVMul
open Spec NPoly Scheme Source Correct Challenge.BFV

variable (P : FullParams)

/-! ## Approximate multiplication -/

/-- The representatives an approximate multiplication multiplies: `[cᵢ]_Q + Q·uᵢ`, the centred
representative of each component modulo `Q` plus a multiple of `Q`. -/
def approxLift {N : ℕ} (Q : ℕ) (c u : List (IntPoly N)) : List (IntPoly N) :=
  List.zipWith (fun x w => centered (ofInt Q x) + (Q : ℤ) • w) c u

/-- **Every approximate multiplication meets the `mul` contract.** Two-component operands at
modulus `Q` (the modulus of their level). If the stored result `out` is congruent modulo `Q`,
component by component, to integer polynomials `X₀, X₁, X₂` with
`2·|Q·Xⱼ − t·Tⱼ| ≤ Q·r` coefficientwise, where `T` is the integer tensor product of the lifts
`[caᵢ]_Q + Q·uaᵢ` and `[cbᵢ]_Q + Q·ubᵢ`, `‖uaᵢ‖∞, ‖ubᵢ‖∞ ≤ U`, then the step meets the contract
for every budget with `mulLift ≥ ⌊(2 + N·B_s)/2⌋ + U·(1 + N·B_s)` and
`mulRound ≥ r·(1 + N·B_s + (N·B_s)²)`, under every secret within the bound. -/
theorem stepOK_mul_approx (hP : SchemeParamsOK P) (U r : ℕ) (E : TraceBFV.Budget)
    (hL : BudgetBFV.mulLiftApprox P U ≤ E.mulLift)
    (hR : BudgetBFV.mulRoundApprox P r ≤ E.mulRound)
    (s : IntPoly P.src.N) (hs : SecretOK P.secretBound s) (ρ ρ' : Env P.src)
    (σ : Trace.CtEnv P) (d a b : Var) (x y : Val P.src) (ca cb : List (IntPoly P.src.N))
    (hstep : step P.src ρ (.mul d a b) = some ρ') (hx : ρ a = some x) (hy : ρ b = some y)
    (ha : σ a = some ca) (hb : σ b = some cb)
    (hla : ca.length = 2) (hlb : cb.length = 2) (h2x : x.parts = 2) (h2y : y.parts = 2)
    (hℓ : 1 ≤ x.level) (hℓL : x.level ≤ P.src.qs.length)
    (ua ub X out : List (IntPoly P.src.N))
    (hua : ua.length = 2) (hub : ub.length = 2) (hX : X.length = 3)
    (hUa : ∀ u ∈ ua, normInf u ≤ U) (hUb : ∀ u ∈ ub, normInf u ≤ U)
    (hround : ∀ (j : ℕ) (i : Fin P.src.N),
      2 * |(P.src.modulus x.level : ℤ) * (X.getD j 0).coeff i -
          (P.src.t : ℤ) * ((Challenge.Source.tensor (approxLift (P.src.modulus x.level) ca ua)
            (approxLift (P.src.modulus x.level) cb ub)).getD j 0).coeff i|
        ≤ (P.src.modulus x.level : ℤ) * r)
    (hout : out.map (ofInt (P.src.modulus x.level)) = X.map (ofInt (P.src.modulus x.level))) :
    TraceBFV.StepOK P E s ρ ρ' σ (σ.set d out) (.mul d a b) := sorry

/-- **Every approximate squaring meets the `square` contract**: as `stepOK_mul_approx`, with the
same lift of the operand on both sides of the tensor product. -/
theorem stepOK_square_approx (hP : SchemeParamsOK P) (U r : ℕ) (E : TraceBFV.Budget)
    (hL : BudgetBFV.mulLiftApprox P U ≤ E.mulLift)
    (hR : BudgetBFV.mulRoundApprox P r ≤ E.mulRound)
    (s : IntPoly P.src.N) (hs : SecretOK P.secretBound s) (ρ ρ' : Env P.src)
    (σ : Trace.CtEnv P) (d a : Var) (x : Val P.src) (ca : List (IntPoly P.src.N))
    (hstep : step P.src ρ (.square d a) = some ρ') (hx : ρ a = some x)
    (ha : σ a = some ca) (hla : ca.length = 2) (h2x : x.parts = 2)
    (hℓ : 1 ≤ x.level) (hℓL : x.level ≤ P.src.qs.length)
    (ua X out : List (IntPoly P.src.N))
    (hua : ua.length = 2) (hX : X.length = 3) (hUa : ∀ u ∈ ua, normInf u ≤ U)
    (hround : ∀ (j : ℕ) (i : Fin P.src.N),
      2 * |(P.src.modulus x.level : ℤ) * (X.getD j 0).coeff i -
          (P.src.t : ℤ) * ((Challenge.Source.tensor (approxLift (P.src.modulus x.level) ca ua)
            (approxLift (P.src.modulus x.level) ca ua)).getD j 0).coeff i|
        ≤ (P.src.modulus x.level : ℤ) * r)
    (hout : out.map (ofInt (P.src.modulus x.level)) = X.map (ofInt (P.src.modulus x.level))) :
    TraceBFV.StepOK P E s ρ ρ' σ (σ.set d out) (.square d a) := sorry

-- The budgets: slack `(0, 1)` is the textbook budget; each unit of lift slack costs `1 + N·B_s`,
-- the rounding budget is linear in the rounding slack.
#guard BudgetBFV.mulLiftApprox sealBFV 0 == BudgetBFV.mulLift sealBFV
#guard BudgetBFV.mulRoundApprox sealBFV 1 == BudgetBFV.mulRound sealBFV
#guard BudgetBFV.mulLiftApprox sealBFV 1 == 4097 + 8193
#guard BudgetBFV.mulRoundApprox sealBFV 3 == 3 * 67117057
#guard BudgetBFV.mulLiftApprox tinyBFV 2 == 3 + 2 * 5
-- `approxLift` at `Q = 7`: `[5]₇ + 7·1 = −2 + 7`, `[3]₇ − 7·2 = 3 − 14`.
#guard (approxLift (N := 1) 7 [⟨fun _ => 5⟩, ⟨fun _ => 3⟩] [⟨fun _ => 1⟩, ⟨fun _ => -2⟩]).map
  (·.coeff 0) == [5, -11]

/-! ## Approximate multiplication, by the size of the representatives

The form libraries need. A base extension does not return the centred representative plus a
whole multiple of `Q` so much as a representative slightly outside the centred range:
`2·‖Aᵢ‖∞ ≤ Q + e`. The lift budget is then `Spec.BudgetBFV.mulLiftNormAt`, which for `e ≪ Q/N` is
the textbook one. `Spec.BudgetBFV.hpsSlack`, `poverqSlack`, `leveledSlack`, `behzSlack` compute
`e` and the rounding slack of the RNS variants. -/

/-- **Every multiplication of representatives of bounded size meets the `mul` contract.** As
`stepOK_mul_approx`, with any integer representatives `A`, `B` of the operands' components modulo
`Q` such that `2·‖Aᵢ‖∞, 2·‖Bᵢ‖∞ ≤ Q + e`: the contract holds for every budget with
`mulLift ≥ ⌊((Q + e)·(1 + N·B_s) + Q)/(2Q)⌋` and `mulRound ≥ r·(1 + N·B_s + (N·B_s)²)`. The two
operands may be the same variable (a library squaring that lifts its operand in two ways is a
`mul` of the operand with itself). -/
theorem stepOK_mul_lifted (hP : SchemeParamsOK P) (e r : ℕ) (E : TraceBFV.Budget)
    (s : IntPoly P.src.N) (hs : SecretOK P.secretBound s) (ρ ρ' : Env P.src)
    (σ : Trace.CtEnv P) (d a b : Var) (x y : Val P.src) (ca cb : List (IntPoly P.src.N))
    (hL : BudgetBFV.mulLiftNormAt P x.level e ≤ E.mulLift)
    (hR : BudgetBFV.mulRoundApprox P r ≤ E.mulRound)
    (hstep : step P.src ρ (.mul d a b) = some ρ') (hx : ρ a = some x) (hy : ρ b = some y)
    (ha : σ a = some ca) (hb : σ b = some cb)
    (hla : ca.length = 2) (hlb : cb.length = 2) (h2x : x.parts = 2) (h2y : y.parts = 2)
    (hℓ : 1 ≤ x.level) (hℓL : x.level ≤ P.src.qs.length)
    (A B X out : List (IntPoly P.src.N))
    (hA : A.map (ofInt (P.src.modulus x.level)) = ca.map (ofInt (P.src.modulus x.level)))
    (hB : B.map (ofInt (P.src.modulus x.level)) = cb.map (ofInt (P.src.modulus x.level)))
    (hX : X.length = 3)
    (hAn : ∀ p ∈ A, 2 * normInf p ≤ P.src.modulus x.level + e)
    (hBn : ∀ p ∈ B, 2 * normInf p ≤ P.src.modulus x.level + e)
    (hround : ∀ (j : ℕ) (i : Fin P.src.N),
      2 * |(P.src.modulus x.level : ℤ) * (X.getD j 0).coeff i -
          (P.src.t : ℤ) * ((Challenge.Source.tensor A B).getD j 0).coeff i|
        ≤ (P.src.modulus x.level : ℤ) * r)
    (hout : out.map (ofInt (P.src.modulus x.level)) = X.map (ofInt (P.src.modulus x.level))) :
    TraceBFV.StepOK P E s ρ ρ' σ (σ.set d out) (.mul d a b) := sorry

/-- **Every squaring of representatives of bounded size meets the `square` contract.** As
`stepOK_mul_lifted`, with the same integer representatives `A` of the operand's components
(`2·‖Aᵢ‖∞ ≤ Q + e`) on both sides of the tensor product. -/
theorem stepOK_square_lifted (hP : SchemeParamsOK P) (e r : ℕ) (E : TraceBFV.Budget)
    (s : IntPoly P.src.N) (hs : SecretOK P.secretBound s) (ρ ρ' : Env P.src)
    (σ : Trace.CtEnv P) (d a : Var) (x : Val P.src) (ca : List (IntPoly P.src.N))
    (hL : BudgetBFV.mulLiftNormAt P x.level e ≤ E.mulLift)
    (hR : BudgetBFV.mulRoundApprox P r ≤ E.mulRound)
    (hstep : step P.src ρ (.square d a) = some ρ') (hx : ρ a = some x)
    (ha : σ a = some ca) (hla : ca.length = 2) (h2x : x.parts = 2)
    (A X out : List (IntPoly P.src.N))
    (hA : A.map (ofInt (P.src.modulus x.level)) = ca.map (ofInt (P.src.modulus x.level)))
    (hX : X.length = 3)
    (hAn : ∀ p ∈ A, 2 * normInf p ≤ P.src.modulus x.level + e)
    (hround : ∀ (j : ℕ) (i : Fin P.src.N),
      2 * |(P.src.modulus x.level : ℤ) * (X.getD j 0).coeff i -
          (P.src.t : ℤ) * ((Challenge.Source.tensor A A).getD j 0).coeff i|
        ≤ (P.src.modulus x.level : ℤ) * r)
    (hout : out.map (ofInt (P.src.modulus x.level)) = X.map (ofInt (P.src.modulus x.level))) :
    TraceBFV.StepOK P E s ρ ρ' σ (σ.set d out) (.square d a) := sorry

-- The lift budget by size: `e = 0` is the textbook budget, `e = 2·U·Q` is `mulLiftApprox P U`,
-- and an excess of `Q/2¹⁴` (BEHZ with `m̃ = 2¹⁶`, three limbs) costs nothing at `N = 8192`.
#guard BudgetBFV.mulLiftNormAt sealBFV 4 0 == BudgetBFV.mulLift sealBFV
#guard BudgetBFV.mulLiftNormAt sealBFV 4 (2 * sealBFV.src.modulus 4)
  == BudgetBFV.mulLiftApprox sealBFV 1
#guard BudgetBFV.mulLiftNormAt sealBFV 4 (sealBFV.src.modulus 4 / 2 ^ 14) == 4097
#guard BudgetBFV.mulLiftNormAt sealBFV 4 (sealBFV.src.modulus 4 / 2 ^ 12) == 4098
#guard BudgetBFV.mulLiftNormAt tinyBFV 2 0 == 3

-- The slack formulas against the reference implementation `harness/bfv-rns/bounds.py` (exact
-- rational arithmetic there), at `N = 16384`, `t = 65537`, three 60-bit ciphertext moduli and
-- four auxiliary ones (products below), idealised and with the binary64 tolerances.
section SlackGuards
open BudgetBFV
private def gQ : ℕ := 1532495540865888362556304599376739954304657377252981581
private def gR : ℕ := 1766847064778383152626722115740568872570572093495188336151656873765650113
private def gP : ℕ := 1532495540865888115319897383382456169967638180362298639
private def gQ2 : ℕ := 1329227995784915642319506138910959327
private def gP2 : ℕ := 1329227995784915457852065401815465607
private def gq0 : ℕ := 1152921504606846883
private def gp0 : ℕ := 1152921504606846799
private def gqs : List ℕ := [1152921504606846883, 1152921504606846869, 1152921504606846803]
private def gps : List ℕ := [1152921504606846799, 1152921504606846793, 1152921504606846777]
#guard hpsSlack 65537 16384 gQ gR 0 0 0 == ⟨0, 1, true⟩
#guard hpsSlack 65537 16384 gQ gR (doubleSw 3) (doubleSw 4) (doubleSr gqs)
  == ⟨8166776806102520480956943412796213733376, 6913, true⟩
#guard poverqSlack 65537 16384 gQ gP 3 0 0 == ⟨7, 6442549250, true⟩
#guard poverqSlack 65537 16384 gQ gP 3 (doubleSw 3) (doubleSr gps)
  == ⟨8166776806102520480956943412796213733382, 6442556162, true⟩
#guard leveledSlack 65537 16384 gQ gQ2 gP2 3 0 0 0
  == ⟨6917529027641081779, 8665712502412103509453389652, true⟩
#guard leveledSlack 65537 16384 gQ gQ2 gP2 3 (doubleSw 3) 8070450532247927628
    18446744073709548744
  == ⟨8166776806102520483024131670556289742931, 2227088117547140453084548511568, true⟩
#guard leveledSlack 65537 16384 gQ gq0 gp0 3 0 0 0
  == ⟨7975367974709493881587152944030082835, 9990886296771325948584102238654421341080258640,
      true⟩
#guard leveledSlack 65537 16384 gQ gq0 gp0 3 (doubleSw 3) 18446744073709549384
    8070450532247927600
  == ⟨13612623904833318830888283353658936991823,
      5856086640983182800475029879503348958953501079180, true⟩
#guard behzSlack 65537 16384 gQ gP 1152921504606846767 3 3 (2 ^ 16)
  == ⟨93536104789177756503680700645552975726602623123351, 6, true⟩
#guard ksLeveled 16384 1152921504606846803 (10 ^ 20) 1 0
  == 115292150460684689744732965739289010176
#guard ksLeveled 16384 1152921504606846803 (10 ^ 20) 16384 (7 * (1 + 1152921504606846803))
  == 115292150738137991604835771109778391040
-- Side conditions fail when the auxiliary modulus is too small.
#guard (hpsSlack 65537 16384 gQ gQ 0 0 0).ok == false
#guard (behzSlack 65537 16384 gQ gq0 1152921504606846767 3 1 (2 ^ 16)).ok == false
#guard (poverqSlack 65537 16384 gQ 5 3 0 0).ok == false
end SlackGuards

/-! ## HPS multiplication, limb by limb

`hpsMul` (`Challenge/BFVMul/HPS.lean`) is the RNS multiplication of Halevi–Polyakov–Shoup as
OpenFHE runs it for `MultiplicationTechnique == HPS`, with the two floating-point rounded sums
replaced by exact rational rounding. Under the side condition `hpsAuxOK?` on the auxiliary basis
it meets the contract within the *textbook* budget (lift slack `0`, rounding slack `1`): the
idealised algorithm computes the textbook result modulo `Q`. Nothing is claimed about the
floating-point code; an implementation whose float error moves a rounding by one unit is covered
by `stepOK_mul_approx` with the corresponding slack instead. -/

/-- **Idealised HPS multiplication meets the `mul` contract** within the textbook budget, at
every level whose limbs with the auxiliary basis `ps` pass `hpsAuxOK?`. -/
theorem stepOK_mul_hps (hP : SchemeParamsOK P) (E : TraceBFV.Budget)
    (hL : BudgetBFV.mulLift P ≤ E.mulLift) (hR : BudgetBFV.mulRound P ≤ E.mulRound)
    (s : IntPoly P.src.N) (hs : SecretOK P.secretBound s) (ρ ρ' : Env P.src)
    (σ : Trace.CtEnv P) (d a b : Var) (x y : Val P.src) (ca cb : List (IntPoly P.src.N))
    (ps : List ℕ)
    (hstep : step P.src ρ (.mul d a b) = some ρ') (hx : ρ a = some x) (hy : ρ b = some y)
    (ha : σ a = some ca) (hb : σ b = some cb)
    (hla : ca.length = 2) (hlb : cb.length = 2) (h2x : x.parts = 2) (h2y : y.parts = 2)
    (hℓ : 1 ≤ x.level) (hℓL : x.level ≤ P.src.qs.length)
    (haux : hpsAuxOK? P.src.t P.src.N (P.src.qs.take x.level) ps = true) :
    TraceBFV.StepOK P E s ρ ρ' σ
      (σ.set d (hpsMul P.src.t (P.src.qs.take x.level) ps ca cb)) (.mul d a b) := sorry

/-- **Idealised HPS squaring meets the `square` contract** within the textbook budget. -/
theorem stepOK_square_hps (hP : SchemeParamsOK P) (E : TraceBFV.Budget)
    (hL : BudgetBFV.mulLift P ≤ E.mulLift) (hR : BudgetBFV.mulRound P ≤ E.mulRound)
    (s : IntPoly P.src.N) (hs : SecretOK P.secretBound s) (ρ ρ' : Env P.src)
    (σ : Trace.CtEnv P) (d a : Var) (x : Val P.src) (ca : List (IntPoly P.src.N)) (ps : List ℕ)
    (hstep : step P.src ρ (.square d a) = some ρ') (hx : ρ a = some x)
    (ha : σ a = some ca) (hla : ca.length = 2) (h2x : x.parts = 2)
    (hℓ : 1 ≤ x.level) (hℓL : x.level ≤ P.src.qs.length)
    (haux : hpsAuxOK? P.src.t P.src.N (P.src.qs.take x.level) ps = true) :
    TraceBFV.StepOK P E s ρ ρ' σ
      (σ.set d (hpsMul P.src.t (P.src.qs.take x.level) ps ca ca)) (.square d a) := sorry

/-- The idealised HPS product is the textbook product, modulo `Q`, component by component. -/
theorem hpsMul_congr_bfvMul {N : ℕ} (t : ℕ) (qs ps : List ℕ)
    (haux : hpsAuxOK? t N qs ps = true) (c d : List (IntPoly N))
    (hc : c.length = 2) (hd : d.length = 2) :
    (hpsMul t qs ps c d).map (ofInt qs.prod) = (bfvMul t qs.prod c d).map (ofInt qs.prod) := sorry


/-! ## BEHZ multiplication, limb by limb

`behzMul` (`Challenge/BFVMul/BEHZ.lean`) is the RNS multiplication of
Bajard–Eynard–Hasan–Zucca as OpenFHE runs it for `MultiplicationTechnique == BEHZ`
(`m̃` is an argument of `behzMul`: OpenFHE uses `2¹⁶`; the instances at `sealBFV` below use `2³²`):
integers only, nothing idealised but machine words and the NTT. Under the side
condition `behzAuxOK?` it meets the contract with the slacks of `Spec.BudgetBFV.behzSlack`: lift
excess `⌈2(k − 1)·Q/m̃⌉`, rounding slack `2k`, `k` the number of limbs. -/

/-- **BEHZ multiplication meets the `mul` contract** with the slacks of `behzSlack`. -/
theorem stepOK_mul_behz (hP : SchemeParamsOK P) (E : TraceBFV.Budget)
    (s : IntPoly P.src.N) (hs : SecretOK P.secretBound s) (ρ ρ' : Env P.src)
    (σ : Trace.CtEnv P) (d a b : Var) (x y : Val P.src) (ca cb : List (IntPoly P.src.N))
    (bs : List ℕ) (msk mt : ℕ)
    (hL : BudgetBFV.mulLiftNormAt P x.level
            (BudgetBFV.behzSlack P.src.t P.src.N (P.src.modulus x.level) bs.prod msk x.level
              bs.length mt).e ≤ E.mulLift)
    (hR : BudgetBFV.mulRoundApprox P (2 * x.level) ≤ E.mulRound)
    (hstep : step P.src ρ (.mul d a b) = some ρ') (hx : ρ a = some x) (hy : ρ b = some y)
    (ha : σ a = some ca) (hb : σ b = some cb)
    (hla : ca.length = 2) (hlb : cb.length = 2) (h2x : x.parts = 2) (h2y : y.parts = 2)
    (hℓ : 1 ≤ x.level) (hℓL : x.level ≤ P.src.qs.length)
    (haux : behzAuxOK? P.src.t P.src.N (P.src.qs.take x.level) bs msk mt = true) :
    TraceBFV.StepOK P E s ρ ρ' σ
      (σ.set d (behzMul P.src.t (P.src.qs.take x.level) bs msk mt ca cb)) (.mul d a b) := sorry

/-- **BEHZ squaring meets the `square` contract** with the same slacks. -/
theorem stepOK_square_behz (hP : SchemeParamsOK P) (E : TraceBFV.Budget)
    (s : IntPoly P.src.N) (hs : SecretOK P.secretBound s) (ρ ρ' : Env P.src)
    (σ : Trace.CtEnv P) (d a : Var) (x : Val P.src) (ca : List (IntPoly P.src.N))
    (bs : List ℕ) (msk mt : ℕ)
    (hL : BudgetBFV.mulLiftNormAt P x.level
            (BudgetBFV.behzSlack P.src.t P.src.N (P.src.modulus x.level) bs.prod msk x.level
              bs.length mt).e ≤ E.mulLift)
    (hR : BudgetBFV.mulRoundApprox P (2 * x.level) ≤ E.mulRound)
    (hstep : step P.src ρ (.square d a) = some ρ') (hx : ρ a = some x)
    (ha : σ a = some ca) (hla : ca.length = 2) (h2x : x.parts = 2)
    (hℓ : 1 ≤ x.level) (hℓL : x.level ≤ P.src.qs.length)
    (haux : behzAuxOK? P.src.t P.src.N (P.src.qs.take x.level) bs msk mt = true) :
    TraceBFV.StepOK P E s ρ ρ' σ
      (σ.set d (behzMul P.src.t (P.src.qs.take x.level) bs msk mt ca ca)) (.square d a) := sorry

-- An odd `m̃` fails the side condition of `behzSlack`.
#guard (BudgetBFV.behzSlack 5 4 97 221 19 1 2 3).ok == false
#guard (BudgetBFV.behzSlack 5 4 97 221 19 1 2 4).ok == true

/-! ## P-over-Q multiplication, limb by limb

`poverqMul` and `leveledMul` (`Challenge/BFVMul/POverQ.lean`) are the multiplications of
Kim–Polyakov–Zucca that OpenFHE runs by default (`HPSPOVERQ`; `HPSPOVERQLEVELED`, which drops
`drop` limbs internally, multiplies at the smaller modulus and scales back), with the binary64
rounded sums replaced by exact rational rounding. They meet the contract with the idealised
slacks of `Spec.BudgetBFV.poverqSlack` and `leveledSlack` (tolerances `0`); the only side
condition is that the moduli are positive and pairwise coprime (a small auxiliary modulus makes
the slack large, not the statement false). Nothing is claimed about the floating-point code.
The library's squaring under these techniques lifts its operand in two ways and is a `mul` of
the operand with itself, which these statements cover. -/

/-- **Idealised P-over-Q multiplication meets the `mul` contract** with the slacks of
`poverqSlack`. -/
theorem stepOK_mul_poverq (hP : SchemeParamsOK P) (E : TraceBFV.Budget)
    (s : IntPoly P.src.N) (hs : SecretOK P.secretBound s) (ρ ρ' : Env P.src)
    (σ : Trace.CtEnv P) (d a b : Var) (x y : Val P.src) (ca cb : List (IntPoly P.src.N))
    (ps : List ℕ)
    (hL : BudgetBFV.mulLiftNormAt P x.level
            (BudgetBFV.poverqSlack P.src.t P.src.N (P.src.modulus x.level) ps.prod x.level 0 0).e
          ≤ E.mulLift)
    (hR : BudgetBFV.mulRoundApprox P
            (BudgetBFV.poverqSlack P.src.t P.src.N (P.src.modulus x.level) ps.prod x.level 0 0).rho
          ≤ E.mulRound)
    (hstep : step P.src ρ (.mul d a b) = some ρ') (hx : ρ a = some x) (hy : ρ b = some y)
    (ha : σ a = some ca) (hb : σ b = some cb)
    (hla : ca.length = 2) (hlb : cb.length = 2) (h2x : x.parts = 2) (h2y : y.parts = 2)
    (hℓ : 1 ≤ x.level) (hℓL : x.level ≤ P.src.qs.length)
    (haux : poverqAuxOK? P.src.t P.src.N (P.src.qs.take x.level) ps = true) :
    TraceBFV.StepOK P E s ρ ρ' σ
      (σ.set d (poverqMul P.src.t (P.src.qs.take x.level) ps ca cb)) (.mul d a b) := sorry

/-- **Idealised leveled P-over-Q multiplication meets the `mul` contract** with the slacks of
`leveledSlack`, for every number `drop` of limbs dropped internally. -/
theorem stepOK_mul_leveled (hP : SchemeParamsOK P) (E : TraceBFV.Budget)
    (s : IntPoly P.src.N) (hs : SecretOK P.secretBound s) (ρ ρ' : Env P.src)
    (σ : Trace.CtEnv P) (d a b : Var) (x y : Val P.src) (ca cb : List (IntPoly P.src.N))
    (ps : List ℕ) (drop : ℕ)
    (hL : BudgetBFV.mulLiftNormAt P x.level
            (BudgetBFV.leveledSlack P.src.t P.src.N (P.src.modulus x.level)
              (P.src.modulus (x.level - drop)) (ps.take (x.level - drop)).prod x.level 0 0 0).e
          ≤ E.mulLift)
    (hR : BudgetBFV.mulRoundApprox P
            (BudgetBFV.leveledSlack P.src.t P.src.N (P.src.modulus x.level)
              (P.src.modulus (x.level - drop)) (ps.take (x.level - drop)).prod x.level 0 0 0).rho
          ≤ E.mulRound)
    (hstep : step P.src ρ (.mul d a b) = some ρ') (hx : ρ a = some x) (hy : ρ b = some y)
    (ha : σ a = some ca) (hb : σ b = some cb)
    (hla : ca.length = 2) (hlb : cb.length = 2) (h2x : x.parts = 2) (h2y : y.parts = 2)
    (hℓ : 1 ≤ x.level) (hℓL : x.level ≤ P.src.qs.length)
    (haux : leveledAuxOK? P.src.t P.src.N (P.src.qs.take x.level) ps drop = true) :
    TraceBFV.StepOK P E s ρ ρ' σ
      (σ.set d (leveledMul P.src.t (P.src.qs.take x.level) ps drop ca cb)) (.mul d a b) := sorry

/-! ## Acceptance with the budget of an RNS multiplication

`Challenge.BFV.refAnalyzeBFV_accepts_seal` accepts the depth-2 program `sealProg` at the
parameters `sealBFV` (a parameter set of the shape commonly used with BFV: N = 8192, 174-bit modulus) with the *textbook* budget. Here: the same program with the
budgets of the multiplications OpenFHE runs, and plaintext addition by rounding (plaintexts
within `32768`). The auxiliary moduli enter the slacks only through their product, and the
slacks only improve as it grows, so lower bounds are used: BEHZ with `m̃ = 2³²`, a base of
four primes above `2⁶⁰` and `m_sk > 2⁶⁰`; P-over-Q with four auxiliary primes above `2⁴²`.

The cost against the textbook budget is below a thousandth of a bit for BEHZ and HPS (bound
`1487107268…` in both), and two bits for P-over-Q with this (small) auxiliary modulus,
`Q/P ≈ 2⁶`: its rounding slack `ρ ≈ 2·t·N·k·Q/P` is paid once per multiplication. -/

/-- The key-switching, modulus-switching and plaintext-addition numbers at `sealBFV`, with the
multiplication numbers of the slack `sl` at the top level. -/
def sealBudget (sl : BudgetBFV.Slack) : TraceBFV.Budget :=
  BudgetBFV.budgetOf (BudgetBFV.ksBudget sealBFV (Budget.uniformLayout 1))
    (BudgetBFV.msBudget sealBFV) (BudgetBFV.mulLiftNormAt sealBFV 4 sl.e)
    (BudgetBFV.mulRoundApprox sealBFV sl.rho) (BudgetBFV.plainAddRounded sealBFV 32768)

/-- BEHZ at `sealBFV`: `k = 4`, `m̃ = 2³²`, base product at least `2²⁴⁰`, `m_sk ≥ 2⁶⁰`. -/
def sealBEHZ : BudgetBFV.Slack :=
  BudgetBFV.behzSlack 65537 8192 (sealBFV.src.modulus 4) (2 ^ 240) (2 ^ 60) 4 4 (2 ^ 32)

/-- P-over-Q at `sealBFV` (idealised): `k = 4`, auxiliary product at least `2¹⁶⁸`. -/
def sealPOverQ : BudgetBFV.Slack :=
  BudgetBFV.poverqSlack 65537 8192 (sealBFV.src.modulus 4) (2 ^ 168) 4 0 0

/-- HPS at `sealBFV` with the binary64 tolerances: auxiliary product at least `2²¹⁰`. -/
def sealHPS : BudgetBFV.Slack :=
  BudgetBFV.hpsSlack 65537 8192 (sealBFV.src.modulus 4) (2 ^ 210) (BudgetBFV.doubleSw 4)
    (BudgetBFV.doubleSw 5) (BudgetBFV.doubleSr sealBFV.src.qs)

/-- **The reference analyzer accepts `sealProg` at `sealBFV` with the BEHZ budget**,
with a bound below `2¹³¹`, as with the textbook budget. -/
theorem refAnalyzeBFV_accepts_seal_behz :
    sealBEHZ.ok = true ∧
    ∃ B, refAnalyzeBFV sealBFV (sealBudget sealBEHZ) sealProg = some B ∧ B ≤ 2 ^ 131 := sorry

/-- **The reference analyzer accepts `sealProg` at `sealBFV` with the P-over-Q budget** (the
family OpenFHE runs by default), with a bound below `2¹³³`. -/
theorem refAnalyzeBFV_accepts_seal_poverq :
    sealPOverQ.ok = true ∧
    ∃ B, refAnalyzeBFV sealBFV (sealBudget sealPOverQ) sealProg = some B ∧ B ≤ 2 ^ 133 := sorry

#guard sealBEHZ == ⟨33451115118582234806483297447873958169485721, 8, true⟩
#guard sealPOverQ == ⟨512, 274882079233, true⟩
#guard sealHPS == ⟨191408816062444123114490303694957493799, 2, true⟩
#guard (sealBudget sealBEHZ).mulLift == 4097 && (sealBudget sealPOverQ).mulLift == 4097
#guard (sealBudget sealBEHZ).plainAdd == 23835
-- Bounds on `sealProg`: textbook multiplication (with rounded plaintext addition), BEHZ, HPS
-- with float tolerances, P-over-Q.
#guard refAnalyzeBFV sealBFV (sealBudget ⟨0, 1, true⟩) sealProg
  == some 1487107268480789873794743232688495335249
#guard refAnalyzeBFV sealBFV (sealBudget sealBEHZ) sealProg
  == some 1487107268619559764005097146872301164369
#guard refAnalyzeBFV sealBFV (sealBudget sealHPS) sealProg
  == some 1487107268500614143571620720063109207889
#guard refAnalyzeBFV sealBFV (sealBudget sealPOverQ) sealProg
  == some 6936443845196500763689501953860571305809
-- Worst-case depth is unchanged: three relinearized squarings are accepted, a fourth is not
-- (bit lengths of the bounds; P-over-Q pays two bits at the first product).
#guard [sealBEHZ, sealHPS, sealPOverQ].map (fun sl => (List.range 5).map fun n =>
    (refAnalyzeBFV sealBFV (sealBudget sl)
      { inputs := [⟨"a", 2, 4, 1, 1⟩],
        body := (List.replicate n [Instr.square "a" "a", .relin "a" "a"]).flatten,
        outputs := ["a"] }).map Nat.log2)
  == [[some 19, some 61, some 103, some 145, none], [some 19, some 61, some 103, some 145, none],
      [some 19, some 63, some 105, some 147, none]]
-- Discrimination: a rounding slack of `2¹⁰⁰` is rejected; so is a lift excess of `2¹⁰⁰·Q`.
#guard refAnalyzeBFV sealBFV (sealBudget ⟨0, 2 ^ 100, true⟩) sealProg == none
#guard refAnalyzeBFV sealBFV (sealBudget ⟨2 ^ 100 * sealBFV.src.modulus 4, 1, true⟩) sealProg
  == none

/-! ## The remaining textbook operations -/

/-- Componentwise subtraction (the shorter ciphertext padded with zero components) meets the
`sub` contract. -/
theorem stepOK_sub_padded (E : TraceBFV.Budget) (s : IntPoly P.src.N) (ρ ρ' : Env P.src)
    (σ : Trace.CtEnv P) (d a b : Var) (x y : Val P.src) (ca cb : List (IntPoly P.src.N))
    (hstep : step P.src ρ (.sub d a b) = some ρ') (hx : ρ a = some x) (hy : ρ b = some y)
    (ha : σ a = some ca) (hb : σ b = some cb)
    (hla : ca.length = x.parts) (hlb : cb.length = y.parts) :
    TraceBFV.StepOK P E s ρ ρ' σ (σ.set d (Challenge.Source.padZip (· - ·) ca cb))
      (.sub d a b) := sorry

/-- Textbook plaintext subtraction: `c₀ − Δ·p`. -/
def bfvSubPlain {N : ℕ} (t Q : ℕ) (c : List (IntPoly N)) (p : IntPoly N) : List (IntPoly N) :=
  Challenge.Source.padZip (· - ·) c [((Q / t : ℕ) : ℤ) • p]

/-- Subtracting `⌊Q/t⌋·p` from the first component meets the `subPlain` contract, with no
deviation (every budget). -/
theorem stepOK_subPlain_textbook (E : TraceBFV.Budget) (s : IntPoly P.src.N) (ρ ρ' : Env P.src)
    (σ : Trace.CtEnv P) (d a p : Var) (x y : Val P.src) (ca : List (IntPoly P.src.N))
    (c : IntPoly P.src.N)
    (hstep : step P.src ρ (.subPlain d a p) = some ρ') (hx : ρ a = some x) (hy : ρ p = some y)
    (ha : σ a = some ca) (hp : σ p = some [c]) (hla : ca.length = x.parts) (h1 : 1 ≤ x.parts) :
    TraceBFV.StepOK P E s ρ ρ' σ
      (σ.set d (bfvSubPlain P.src.t (P.src.modulus x.level) ca c)) (.subPlain d a p) := sorry

/-- Multiplying every component by the integer constant meets the `mulConst` contract. -/
theorem stepOK_mulConst_textbook (E : TraceBFV.Budget) (s : IntPoly P.src.N) (ρ ρ' : Env P.src)
    (σ : Trace.CtEnv P) (d a : Var) (c : ℤ) (x : Val P.src) (ca : List (IntPoly P.src.N))
    (hstep : step P.src ρ (.mulConst d a c) = some ρ') (hx : ρ a = some x)
    (ha : σ a = some ca) (hla : ca.length = x.parts) :
    TraceBFV.StepOK P E s ρ ρ' σ (σ.set d (ca.map (c • ·))) (.mulConst d a c) := sorry

/-- **Rotation.** Applying `X ↦ X^g` to every component meets the `automorph` contract: the
result is read under `σ_g` of the operand's key. -/
theorem stepOK_automorph_textbook (hP : SchemeParamsOK P) (E : TraceBFV.Budget)
    (s : IntPoly P.src.N) (ρ ρ' : Env P.src) (σ : Trace.CtEnv P) (d a : Var) (g : ℕ)
    (x : Val P.src) (ca : List (IntPoly P.src.N))
    (hstep : step P.src ρ (.automorph d a g) = some ρ') (hx : ρ a = some x)
    (ha : σ a = some ca) (hla : ca.length = x.parts) :
    TraceBFV.StepOK P E s ρ ρ' σ (σ.set d (ca.map (automorph g))) (.automorph d a g) := sorry

/-- **Textbook squaring meets the `square` contract** within the textbook budget: `bfvMul` of the
operand with itself. -/
theorem stepOK_square_textbook (hP : SchemeParamsOK P) (E : TraceBFV.Budget)
    (hL : BudgetBFV.mulLift P ≤ E.mulLift) (hR : BudgetBFV.mulRound P ≤ E.mulRound)
    (s : IntPoly P.src.N) (hs : SecretOK P.secretBound s) (ρ ρ' : Env P.src)
    (σ : Trace.CtEnv P) (d a : Var) (x : Val P.src) (ca : List (IntPoly P.src.N))
    (hstep : step P.src ρ (.square d a) = some ρ') (hx : ρ a = some x)
    (ha : σ a = some ca) (hla : ca.length = 2) (h2x : x.parts = 2)
    (hℓ : 1 ≤ x.level) (hℓL : x.level ≤ P.src.qs.length) :
    TraceBFV.StepOK P E s ρ ρ' σ
      (σ.set d (bfvMul P.src.t (P.src.modulus x.level) ca ca)) (.square d a) := sorry

/-! ## Plaintext addition by rounding -/

/-- `⌊Q·p/t⌉`, coefficient by coefficient: the scaled plaintext a library adds (OpenFHE
`TimesQovert`). -/
def scaleUp {N : ℕ} (t Q : ℕ) (p : IntPoly N) : IntPoly N :=
  ⟨fun i => roundDiv (Q * p.coeff i) t⟩

/-- Plaintext addition by rounding: `c₀ + ⌊Q·p/t⌉`. -/
def bfvAddPlainRounded {N : ℕ} (t Q : ℕ) (c : List (IntPoly N)) (p : IntPoly N) :
    List (IntPoly N) :=
  Challenge.Source.padZip (· + ·) c [scaleUp t Q p]

/-- Plaintext subtraction by rounding: `c₀ − ⌊Q·p/t⌉`. -/
def bfvSubPlainRounded {N : ℕ} (t Q : ℕ) (c : List (IntPoly N)) (p : IntPoly N) :
    List (IntPoly N) :=
  Challenge.Source.padZip (· - ·) c [scaleUp t Q p]

/-- **Adding `⌊Q·p/t⌉` meets the `addPlain` contract** with deviation at most
`⌊(2·(Q mod t)·b + t)/(2t)⌋` for a stored plaintext polynomial with `‖p‖∞ ≤ b`. -/
theorem stepOK_addPlain_rounded (hP : SchemeParamsOK P) (E : TraceBFV.Budget)
    (s : IntPoly P.src.N) (ρ ρ' : Env P.src)
    (σ : Trace.CtEnv P) (d a p : Var) (x y : Val P.src) (ca : List (IntPoly P.src.N))
    (c : IntPoly P.src.N) (b : ℕ) (hc : normInf c ≤ b)
    (hE : BudgetBFV.plainAddRoundedAt P x.level b ≤ E.plainAdd)
    (hstep : step P.src ρ (.addPlain d a p) = some ρ') (hx : ρ a = some x) (hy : ρ p = some y)
    (ha : σ a = some ca) (hp : σ p = some [c]) (hla : ca.length = x.parts) (h1 : 1 ≤ x.parts) :
    TraceBFV.StepOK P E s ρ ρ' σ
      (σ.set d (bfvAddPlainRounded P.src.t (P.src.modulus x.level) ca c)) (.addPlain d a p) :=
  sorry

/-- **Subtracting `⌊Q·p/t⌉` meets the `subPlain` contract** with the same deviation. -/
theorem stepOK_subPlain_rounded (hP : SchemeParamsOK P) (E : TraceBFV.Budget)
    (s : IntPoly P.src.N) (ρ ρ' : Env P.src)
    (σ : Trace.CtEnv P) (d a p : Var) (x y : Val P.src) (ca : List (IntPoly P.src.N))
    (c : IntPoly P.src.N) (b : ℕ) (hc : normInf c ≤ b)
    (hE : BudgetBFV.plainAddRoundedAt P x.level b ≤ E.plainAdd)
    (hstep : step P.src ρ (.subPlain d a p) = some ρ') (hx : ρ a = some x) (hy : ρ p = some y)
    (ha : σ a = some ca) (hp : σ p = some [c]) (hla : ca.length = x.parts) (h1 : 1 ≤ x.parts) :
    TraceBFV.StepOK P E s ρ ρ' σ
      (σ.set d (bfvSubPlainRounded P.src.t (P.src.modulus x.level) ca c)) (.subPlain d a p) :=
  sorry

/-- **Adding any polynomial within one unit of `Q·p/t` meets the `addPlain` contract** with
deviation at most `⌊(Q mod t)·b/t⌋ + 1` for `‖p‖∞ ≤ b`: whatever rounding the library's scaling
of the plaintext uses (OpenFHE's `TimesQovert` rounds up). (`0 < t` is needed: at `t = 0` the
hypothesis on `w` says nothing.) -/
theorem stepOK_addPlain_scaled (hP : SchemeParamsOK P) (ht : 0 < P.src.t)
    (E : TraceBFV.Budget)
    (s : IntPoly P.src.N) (ρ ρ' : Env P.src)
    (σ : Trace.CtEnv P) (d a p : Var) (x y : Val P.src) (ca : List (IntPoly P.src.N))
    (c w : IntPoly P.src.N) (b : ℕ) (hc : normInf c ≤ b)
    (hw : ∀ i, |(P.src.t : ℤ) * w.coeff i - (P.src.modulus x.level : ℤ) * c.coeff i| ≤ P.src.t)
    (hE : BudgetBFV.plainAddScaledAt P x.level b ≤ E.plainAdd)
    (hstep : step P.src ρ (.addPlain d a p) = some ρ') (hx : ρ a = some x) (hy : ρ p = some y)
    (ha : σ a = some ca) (hp : σ p = some [c]) (hla : ca.length = x.parts) (h1 : 1 ≤ x.parts) :
    TraceBFV.StepOK P E s ρ ρ' σ
      (σ.set d (Challenge.Source.padZip (· + ·) ca [w])) (.addPlain d a p) := sorry

/-- **Subtracting any polynomial within one unit of `Q·p/t` meets the `subPlain` contract** with
the same deviation. -/
theorem stepOK_subPlain_scaled (hP : SchemeParamsOK P) (ht : 0 < P.src.t)
    (E : TraceBFV.Budget)
    (s : IntPoly P.src.N) (ρ ρ' : Env P.src)
    (σ : Trace.CtEnv P) (d a p : Var) (x y : Val P.src) (ca : List (IntPoly P.src.N))
    (c w : IntPoly P.src.N) (b : ℕ) (hc : normInf c ≤ b)
    (hw : ∀ i, |(P.src.t : ℤ) * w.coeff i - (P.src.modulus x.level : ℤ) * c.coeff i| ≤ P.src.t)
    (hE : BudgetBFV.plainAddScaledAt P x.level b ≤ E.plainAdd)
    (hstep : step P.src ρ (.subPlain d a p) = some ρ') (hx : ρ a = some x) (hy : ρ p = some y)
    (ha : σ a = some ca) (hp : σ p = some [c]) (hla : ca.length = x.parts) (h1 : 1 ≤ x.parts) :
    TraceBFV.StepOK P E s ρ ρ' σ
      (σ.set d (Challenge.Source.padZip (· - ·) ca [w])) (.subPlain d a p) := sorry

/-- `plainAddScaled` covers every level of the chain. -/
theorem plainAddScaledAt_le (b ℓ : ℕ) (h1 : 1 ≤ ℓ) (hℓ : ℓ ≤ P.src.qs.length) :
    BudgetBFV.plainAddScaledAt P ℓ b ≤ BudgetBFV.plainAddScaled P b := sorry

-- Rounding up at `tinyBFV`: `⌈Q·16/17⌉ − ⌊Q/17⌋·16 = 9 = ⌊9·16/17⌋ + 1`.
#guard BudgetBFV.plainAddScaledAt tinyBFV 2 16 == 9
#guard BudgetBFV.plainAddScaled tinyBFV 16 == 9
#guard (51540459521 * 16 + 16) / 17 - (51540459521 / 17) * 16 == 9

/-- `plainAddRounded` covers every level of the chain. -/
theorem plainAddRoundedAt_le (b ℓ : ℕ) (h1 : 1 ≤ ℓ) (hℓ : ℓ ≤ P.src.qs.length) :
    BudgetBFV.plainAddRoundedAt P ℓ b ≤ BudgetBFV.plainAddRounded P b := sorry

-- At `tinyBFV` (`Q mod t = 9` at level 2, `65537 mod 17 = 2` at level 1, `t = 17`): a plaintext
-- with coefficients up to 16 deviates by at most `⌊(2·9·16 + 17)/34⌋ = 8`; a centred one (up
-- to 8) by at most `4`; never more than `t`.
#guard BudgetBFV.plainAddRoundedAt tinyBFV 2 16 == 8
#guard BudgetBFV.plainAddRoundedAt tinyBFV 1 16 == 2
#guard BudgetBFV.plainAddRounded tinyBFV 16 == 8
#guard BudgetBFV.plainAddRounded tinyBFV 8 == 4
#guard BudgetBFV.plainAddRounded sealBFV 65536 ≤ 65537
-- The deviation is attained: `Q = 51540459521`, `p = 16`: `⌊Q·16/17⌉ − ⌊Q/17⌋·16 = 8`.
#guard roundDiv (51540459521 * 16) 17 - (51540459521 / 17 : ℕ) * 16 == 8

/-! ## The certificate -/

/-- What a BFV certificate says: `Source.eval` computes every output, and at the end of every
ciphertext-level run within the budget each output variable holds a ciphertext, under the secret
key itself (Galois element 1), whose BFV decryption *with `s`* at its own level is the message
`Source.eval` computes. -/
def OutputsDecrypt (E : TraceBFV.Budget) (prog : Program)
    (s : IntPoly P.src.N) (msgs : Var → Msg P.src.t P.src.N)
    (cts : Var → List (IntPoly P.src.N)) : Prop :=
  ∃ ρ, Source.eval P.src prog msgs = some ρ ∧
    ∀ σ, TraceBFV.Run P E s prog.body (initEnv P.src prog msgs) (Trace.initCt P prog cts) σ →
      ∀ o ∈ prog.outputs, ∃ v ct m, ρ o = some v ∧ σ o = some ct ∧ v.msg = .exact m ∧
        v.key = 1 ∧ bfvDecrypt P.src.t s (ct.map (ofInt (P.src.modulus v.level))) = m

/-- **The worst-case BFV certificate** (`fhe_check` on a BFV program). If the reference analysis
accepts and every output is under the secret key itself (`Spec.Encrypt.outputsUnderS?`), then
for every secret, all messages and all inputs within their bounds, every output of every run
within the budget decrypts with `s` to the message the program computes. -/
theorem certified_decrypts (E : TraceBFV.Budget) (prog : Program) (B : ℕ)
    (hP : SchemeParamsOK P) (hk : P.src.kind = .bfv)
    (h : refAnalyzeBFV P E prog = some B)
    (hc : Encrypt.outputsUnderS? P.src prog = true)
    (s : IntPoly P.src.N) (msgs : Var → Msg P.src.t P.src.N)
    (cts : Var → List (IntPoly P.src.N)) (hin : TraceBFV.InputsOK P s prog msgs cts) :
    OutputsDecrypt P E prog s msgs cts := sorry

/-- **The BFV headline at the budget of an approximate multiplication**: for a library whose
multiplication has lift slack `U` and rounding slack `r` (`stepOK_mul_approx`), whose key
switching is hybrid with layout `lay` (`Challenge.BFV.relin_realizable`), whose modulus switching
rounds (`stepOK_modSwitch_textbook`) and whose plaintext addition deviates by at most `pa`. -/
theorem certifiedApprox_sound (lay : Budget.KSLayout) (U r pa : ℕ) (prog : Program) (B : ℕ)
    (hP : SchemeParamsOK P) (hk : P.src.kind = .bfv)
    (h : refAnalyzeBFV P (BudgetBFV.certifiedApprox P lay U r pa) prog = some B)
    (s : IntPoly P.src.N) (msgs : Var → Msg P.src.t P.src.N)
    (cts : Var → List (IntPoly P.src.N)) (hin : TraceBFV.InputsOK P s prog msgs cts) :
    ∃ ρ, Source.eval P.src prog msgs = some ρ ∧
      ∀ σ, TraceBFV.Run P (BudgetBFV.certifiedApprox P lay U r pa) s prog.body
          (initEnv P.src prog msgs) (Trace.initCt P prog cts) σ →
        ∀ o ∈ prog.outputs, ∃ v ct, ρ o = some v ∧ σ o = some ct ∧ Encrypts P s B v ct := sorry

-- `certifiedApprox` at slack `(0, 1)` and exact plaintext addition is the textbook budget.
#guard (BudgetBFV.certifiedApprox sealBFV (Budget.uniformLayout 1) 0 1 0).mulLift
  == (BudgetBFV.certified sealBFV (Budget.uniformLayout 1)).mulLift
#guard (BudgetBFV.certifiedApprox sealBFV (Budget.uniformLayout 1) 0 1 0).mulRound
  == (BudgetBFV.certified sealBFV (Budget.uniformLayout 1)).mulRound
-- An output left under a rotated key is not certified as decrypting with `s`.
#guard Encrypt.outputsUnderS? tinyBFV.src
  { inputs := [⟨"a", 2, 2, 1, 1⟩], body := [.automorph "c" "a" 3], outputs := ["c"] } == false
#guard Encrypt.outputsUnderS? tinyBFV.src
  { inputs := [⟨"a", 2, 2, 1, 1⟩], body := [.automorph "c" "a" 3, .keySwitch "c" "c"],
    outputs := ["c"] } == true

end Challenge.BFVMul
