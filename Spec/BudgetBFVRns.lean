import Spec.BudgetBFV

/-!
# Spec.BudgetBFVRns — the BFV budget of approximate (RNS) multiplication   (TRUSTED)

`Spec.BudgetBFV` gives the two multiplication numbers of `Spec.TraceBFV.Budget` for the textbook
algorithm (centred lift, integer tensor product, exact rounding of `t·T/Q`). A library runs an RNS
variant: it multiplies some other representatives of the operands, and its scaling is not the
exact rounding. Both deviations are measured component by component, on integers, with no secret
in sight:

* **lift slack `U`.** The algorithm multiplies integer polynomials `Aᵢ = [cᵢ]_Q + Q·uᵢ` with
  `‖uᵢ‖∞ ≤ U`, where `[cᵢ]_Q` is the centred representative of component `i` (`U = 0`: the centred
  lift itself).
* **rounding slack `ρ`.** Every component `Xⱼ` of the result (as an integer polynomial, before
  reduction modulo `Q`) satisfies `2·|Q·Xⱼ − t·Tⱼ| ≤ Q·ρ` coefficientwise, `T = A ⊗ B` the integer
  tensor product (`ρ = 1`: exact rounding to nearest).

`Challenge.BFVMul.stepOK_mul_approx` proves that every such algorithm, on two-component operands
under a secret of norm at most `B_s`, meets the `mul` contract with

  `mulLift = ⌊(2 + N·B_s)/2⌋ + U·(1 + N·B_s)`,   `mulRound = ρ·(1 + N·B_s + (N·B_s)²)`.

The slacks of a particular algorithm (HPS, P-over-Q, BEHZ) are computed further down from its
auxiliary basis; that an algorithm has them is a statement about integers and is what
`Challenge.BFVMul` pins for the idealised algorithms.

**Plaintext addition by rounding.** A library that adds `⌊Q·p/t⌉` instead of `⌊Q/t⌋·p` deviates
from the `addPlain` contract by `⌊(Q mod t)·p/t⌉`, at most `⌊(2·(Q mod t)·b + t)/(2t)⌋` for
`‖p‖∞ ≤ b`: `plainAddRoundedAt`.
-/

namespace Spec.BudgetBFV
open NPoly Scheme Source

/-- The lift budget of a multiplication with lift slack `U` (module docstring). -/
def mulLiftApprox (P : FullParams) (U : ℕ) : ℕ :=
  mulLift P + U * (1 + P.src.N * P.secretBound)

/-- The rounding budget of a multiplication with rounding slack `ρ` (module docstring). -/
def mulRoundApprox (P : FullParams) (ρ : ℕ) : ℕ := ρ * mulRound P

/-- The deviation of adding `⌊Q·p/t⌉` from adding `⌊Q/t⌋·p` at level `ℓ`, for `‖p‖∞ ≤ b`. -/
def plainAddRoundedAt (P : FullParams) (ℓ b : ℕ) : ℕ :=
  (2 * (P.src.modulus ℓ % P.src.t) * b + P.src.t) / (2 * P.src.t)

/-- `plainAddRoundedAt`, maximised over the levels `1, …, L` of the chain. -/
def plainAddRounded (P : FullParams) (b : ℕ) : ℕ :=
  ((List.range P.src.qs.length).map fun i => plainAddRoundedAt P (i + 1) b).foldl max 0

/-- The deviation of adding any integer polynomial within one unit of `Q·p/t` (rounding up, down
or to nearest: `|t·w − Q·p| ≤ t` coefficientwise) from adding `⌊Q/t⌋·p`, at level `ℓ`, for
`‖p‖∞ ≤ b`: `⌊(Q mod t)·b/t⌋ + 1`. -/
def plainAddScaledAt (P : FullParams) (ℓ b : ℕ) : ℕ :=
  P.src.modulus ℓ % P.src.t * b / P.src.t + 1

/-- `plainAddScaledAt`, maximised over the levels `1, …, L` of the chain. -/
def plainAddScaled (P : FullParams) (b : ℕ) : ℕ :=
  ((List.range P.src.qs.length).map fun i => plainAddScaledAt P (i + 1) b).foldl max 0

/-- The certified budget of a BFV parameter set whose multiplication has lift slack `U` and
rounding slack `ρ`, whose key switching is hybrid with layout `lay`, whose modulus switching
rounds every component, and whose plaintext addition deviates by at most `pa`. -/
def certifiedApprox (P : FullParams) (lay : Budget.KSLayout) (U ρ pa : ℕ) : TraceBFV.Budget :=
  { keySwitch := ksBudget P lay, modSwitch := msBudget P, mulLift := mulLiftApprox P U,
    mulRound := mulRoundApprox P ρ, plainAdd := pa }

/-! ## A finer lift budget, from the size of the representatives

`mulLiftApprox` measures the lift in whole multiples of `Q`. An RNS base extension overshoots the
centred range by a small fraction of `Q` only: the representatives satisfy `2·‖Aᵢ‖∞ ≤ Q + e` with
`e ≪ Q`. Then the integer phase `A₀ + A₁·s = Φ + Q·k` has
`‖k‖∞ ≤ ⌊((Q + e)·(1 + N·B_s) + Q) / (2Q)⌋` (`Challenge.BFVMul.stepOK_mul_lifted`); `e = 0` gives
the textbook value, `e = 2·U·Q` gives `mulLiftApprox P U`. -/

/-- The lift budget at level `ℓ` of a multiplication whose representatives satisfy
`2·‖Aᵢ‖∞ ≤ Q_ℓ + e`. -/
def mulLiftNormAt (P : FullParams) (ℓ e : ℕ) : ℕ :=
  ((P.src.modulus ℓ + e) * (1 + P.src.N * P.secretBound) + P.src.modulus ℓ) /
    (2 * P.src.modulus ℓ)

/-! ## Slacks of the RNS multiplications libraries run

Plain arithmetic on the numbers involved: `t`, `N`, the ciphertext modulus `Q` (with `k` limbs),
the auxiliary modulus, and the floating-point tolerances. Each function returns a `Slack`: the
lift excess `e` (`2·‖Aᵢ‖∞ ≤ Q + e`), the rounding slack `rho` (`2·|Q·Xⱼ − t·Tⱼ| ≤ Q·rho`), and
whether the side condition on the auxiliary basis holds. All moduli are assumed odd and pairwise
coprime. The derivations and a numeric validation against limb-level models of the library code
are in `harness/bfv-rns/` (`bounds.py`, `validate.py`); `Challenge.BFVMul` pins what is proved.

**Floating point.** OpenFHE's HPS-family code computes two rounded sums in binary64: the
overflow count of an exact base switch (`SwitchCRTBasis`) and the fractional part of a scaling
(`ScaleAndRound`). A tolerance is a numerator over `2⁵³` (`floatDen`): the computed sum is within
`w/2⁵³` (base switch), `r/2⁵³` (scaling) of the exact one. `0` is the idealised exact algorithm.
`doubleSw`, `doubleSr` bound the error of the sums as the library computes them, in every
arithmetic conforming to the standard model of binary64 (`Spec.Float.Conforms`): proved in
`Challenge.BFVMul.Float` (`nuSw_tol`, `nuSr_tol`; at most 128 moduli below `2⁶⁰`), as is that the
multiplications with such sums have the slacks below (`stepOK_mul_hps_float`,
`stepOK_mul_poverq_float`, `stepOK_mul_leveled_float`). The slacks at these tolerances CHARGE
the floating-point error to the budget; they do not say the library computes the idealised
algorithm. For 60-bit limbs the scaling tolerance is far above one unit (`doubleSr` of two 60-bit
limbs is about `2¹¹`, i.e. the rounding slack `rho` is about `2¹²`). -/

/-- The denominator of the floating-point tolerances. -/
def floatDen : ℕ := 2 ^ 53

/-- `⌈a / b⌉`. -/
def ceilDiv (a b : ℕ) : ℕ := (a + b - 1) / b

/-- Tolerance numerator of a binary64 `SwitchCRTBasis` overflow sum over `k` source limbs. -/
def doubleSw (k : ℕ) : ℕ := k * (k + 5)

/-- Tolerance numerator of a binary64 `ScaleAndRound` fractional sum over the input limbs `ms`. -/
def doubleSr (ms : List ℕ) : ℕ := (ms.length + 6) * (1 + ms.sum)

/-- The slacks of one multiplication algorithm at one level (section docstring). -/
structure Slack where
  /-- lift excess: `2·‖Aᵢ‖∞ ≤ Q + e` -/
  e : ℕ
  /-- rounding slack: `2·|Q·Xⱼ − t·Tⱼ| ≤ Q·rho` -/
  rho : ℕ
  /-- the side condition on the auxiliary basis holds -/
  ok : Bool
  deriving Repr, DecidableEq

/-- **HPS** (Halevi–Polyakov–Shoup; OpenFHE `HPS`): exact extension to `Q·R`, tensor, scaling by
`t/Q` into `R`, exact switch back. `w`, `wr`: base-switch tolerances from `Q` and from `R`; `r`:
scaling tolerance. Lift within `Q/2 + Q·w/2⁵³`; result within `1/2 + r/2⁵³` of `t·T/Q`; needs
`t·N·Q·(1 + 2w/2⁵³)² + 2 + 2r/2⁵³ ≤ R·(1 − 2wr/2⁵³)`. -/
def hpsSlack (t N Q R w wr r : ℕ) : Slack :=
  let F := floatDen
  { e := ceilDiv (2 * Q * w) F
    rho := 1 + ceilDiv (2 * r) F
    ok := decide (t * N * Q * (F + 2 * w) ^ 2 + 2 * F ^ 2 + 2 * r * F ≤ R * (F - 2 * wr) * F) &&
          decide (2 * w < F) }

/-- **P-over-Q** (Kim–Polyakov–Zucca; OpenFHE `HPSPOVERQ`, and `HPSPOVERQLEVELED` with no
internal drop): one operand extended exactly, the other scaled by `P/Q` with a fast (approximate)
conversion from the `k` limbs of `Q`, tensor modulo `Q·P`, scaling by `t/P` into `Q`. Second
operand's lift within `Q/2 + Q·w/2⁵³ + k·Q/P`; result within
`1/2 + r/2⁵³ + t·N·k·Q·(1 + 2w/2⁵³)/P` of `t·T/Q`; needs `k/P + w/2⁵³ < 1/2`. -/
def poverqSlack (t N Q Pm k w r : ℕ) : Slack :=
  let F := floatDen
  { e := ceilDiv (2 * Q * w * Pm + 2 * k * Q * F) (F * Pm)
    rho := 1 + ceilDiv (2 * r * Pm + 2 * t * N * k * Q * (F + 2 * w)) (Pm * F)
    ok := decide (2 * (k * F + w * Pm) < Pm * F) }

/-- **Leveled P-over-Q** (OpenFHE `HPSPOVERQLEVELED` at the top level with an internal drop):
the first operand is scaled down from `Q` (`k` limbs) to `Ql` by rounding (tolerance `r1`), the
second converted from `Q` to `Pl` as in `poverqSlack`, the product is computed at `Ql`, `Pl` and
multiplied by `D = Q/Ql`. Result within
`D·(1/2 + r/2⁵³) + t·N·D·[(1 + 2r1/2⁵³)·(1 + 2w/2⁵³ + 2k/Pl) + 2k·Ql·(1 + 2w/2⁵³)/Pl]/2`
of `t·T/Q`. -/
def leveledSlack (t N Q Ql Pl k w r1 r : ℕ) : Slack :=
  let F := floatDen
  let D := Q / Ql
  { e := max (ceilDiv (D * (F + 2 * r1) + 2 * Q * w) F)
             (ceilDiv (2 * Q * w * Pl + 2 * k * Q * F) (F * Pl))
    rho := ceilDiv (D * (F + 2 * r) * F * Pl +
                    t * N * D * ((F + 2 * r1) * (Pl * (F + 2 * w) + 2 * k * F) +
                                 2 * k * Ql * (F + 2 * w) * F)) (F * F * Pl)
    ok := decide (2 * (k * F + w * Pl) < Pl * F) &&
          decide (D * (F + 2 * r1) + 2 * Q * w < Q * F) && decide (Ql ∣ Q) }

/-- **BEHZ** (Bajard–Eynard–Hasan–Zucca; OpenFHE `BEHZ`; integers only): fast conversion
to `B ∪ {m_sk} ∪ {m̃}` with a small Montgomery reduction modulo `m̃`, tensor, fast floor,
Shenoy–Kumaresan conversion back. `k`, `kB`: limbs of `Q` and of `B`. Lift within
`Q/2 + (k − 1)·Q/m̃`; `t·T/Q − X ∈ [0, k)`; needs
`t·N·Q·(m̃ + 2(k−1))² + 2k·m̃² ≤ m̃²·B·(m_sk − 1 − 2kB)`, `gcd(m̃, Q) = 1`, and `m̃` even (the
Montgomery remainder is read in `[−m̃/2, m̃/2)`; for odd `m̃` the lift bound fails: `Q = 97`,
`m̃ = 3`, the value `33` is lifted to `−64`). -/
def behzSlack (t N Q Bm msk k kB mt : ℕ) : Slack :=
  { e := ceilDiv (2 * (k - 1) * Q) mt
    rho := 2 * k
    ok := decide (t * N * Q * (mt + 2 * (k - 1)) ^ 2 + 2 * k * mt ^ 2 ≤
                    mt ^ 2 * Bm * (msk - 1 - 2 * kB)) &&
          decide (2 * (k - 1) ≤ mt) && Nat.gcd mt Q == 1 && decide (0 < mt) &&
          decide (mt % 2 = 0) }

/-- **Key switching with an internal drop** (OpenFHE `HPSPOVERQLEVELED`): the switched component
is scaled down by `D = Q/Ql` with rounding (tolerance `r1`), key-switched at the lower level with
error at most `ksl`, and multiplied back by `D`. `btgt` bounds the key it multiplies (`N·B_s²`
for relinearization, `B_s` for a rotation):
`‖e‖∞ ≤ ⌊D·((1 + 2r1/2⁵³)·N·btgt + 2·ksl)/2⌋`. -/
def ksLeveled (N D ksl btgt r1 : ℕ) : ℕ :=
  D * ((floatDen + 2 * r1) * N * btgt + 2 * ksl * floatDen) / (2 * floatDen)

/-- The budget assembled from its five numbers. -/
def budgetOf (ks ms lift round pa : ℕ) : TraceBFV.Budget :=
  { keySwitch := ks, modSwitch := ms, mulLift := lift, mulRound := round, plainAdd := pa }

end Spec.BudgetBFV
