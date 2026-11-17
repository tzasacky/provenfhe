import Challenge.BFVMul.HPS
import Spec.BudgetBFVRns

/-!
# Challenge.BFVMul.POverQ — BFV multiplication in RNS, Kim–Polyakov–Zucca "P over Q"   (LOCKED definitions)

OpenFHE's default BFV multiplication (`MultiplicationTechnique == HPSPOVERQ`, and
`HPSPOVERQLEVELED`): the variant of Kim, Polyakov and Zucca ("Revisiting homomorphic encryption
schemes for finite fields", ePrint 2021/204) of the HPS multiplication of
`Challenge.BFVMul.HPS`. It is defined here limb by limb, in the form
`LeveledSHEBFVRNS::EvalMult` runs it (`src/pke/lib/scheme/bfvrns/bfvrns-leveledshe.cpp:200`; line
numbers are those of upstream OpenFHE v1.6.1, commit b59e1f29). Definitions only: that
`poverqMul` meets the `mul` contract of `Spec.TraceBFV` with the slack
`Spec.BudgetBFV.poverqSlack`, under `poverqAuxOK?`, is proved in `Validation/BFVMul/POverQ.lean`.

**The algorithm** (`poverqMul`). `qs = [q₁, …, q_k]` is the ciphertext basis, `Q = ∏ qᵢ`;
`ps = [p₁, …, p_m]` the auxiliary basis (OpenFHE: `R_l`, with `m = k`), `P = ∏ pⱼ`. An RNS
polynomial is the list of its limbs; in the extended basis the `qs`-limbs come first, then the
`ps`-limbs (both `ExpandCRTBasis`, `dcrtpoly-impl.h:1112-1143`, and `FastExpandCRTBasisPloverQ`,
`:1181-1194`, lay the limbs out so).

1. *Operand 1 is expanded exactly* (`HPS.expand`; `ExpandCRTBasis`, called at
   `bfvrns-leveledshe.cpp:241-246`): its `ps`-limbs are the residues of the representative of
   the value in `[-Q/2, Q/2)`.
2. *Operand 2 is scaled by `P/Q`, approximately* (`POverQ.fastExpand`;
   `FastExpandCRTBasisPloverQ`, called at `bfvrns-leveledshe.cpp:256-261`):
   * `POverQ.negPDigits`: `yᵢ = [xᵢ·(−P)·(Q/qᵢ)⁻¹]_{qᵢ} ∈ [0, qᵢ)` (table `mNegRlQlHatInvModq`,
     `bfvrns-cryptoparameters.cpp:505-520`);
   * `POverQ.approx1`: `wⱼ = Σᵢ yᵢ·[qᵢ⁻¹]_{pⱼ} mod pⱼ` (`ApproxSwitchCRTBasis`,
     `dcrtpoly-impl.h:938-984`, with the table `qInvModr`, `bfvrns-cryptoparameters.cpp:522-528`,
     in the place of `QHatModp`). These are the residues modulo `P` of `(P·x + Σᵢ yᵢ·Q/qᵢ)/Q`,
     an integer `P·B/Q + δ` with `B ≡ x (mod Q)` and `δ = Σᵢ yᵢ/qᵢ ∈ [0, k)`;
   * the `qs`-limbs are then obtained from the `ps`-limbs by the exact base switch
     `HPS.switchBasis ps qs` (`SwitchCRTBasis`, `dcrtpoly-impl.h:1058`): the residues of the
     representative `W ∈ [-P/2, P/2)`.
3. *Tensor* (`HPS.tensor`; `bfvrns-leveledshe.cpp:351-361`): limb-wise in the basis `qs ++ ps`.
4. *Scale and round by `t/P` into `qs`* (`POverQ.scaleRoundOut t ps qs`; `ScaleAndRound`,
   `dcrtpoly-impl.h:1536`, called at `bfvrns-leveledshe.cpp:380-390` with the tables
   `tQlSlHatInvModsDivsModq`, `tQlSlHatInvModsDivsFrac`, `bfvrns-cryptoparameters.cpp:562-591`):
   `⌊t·x/P⌉ mod qᵢ` from the residues of `x`. It is `HPS.scale1` with the roles of the two bases
   exchanged (the tables are those of HPS with `Q` and `R` exchanged: `θⱼ = t·Q·[(QP/pⱼ)⁻¹]_{pⱼ}`
   per input limb, `t·Q·[(QP/qᵢ)⁻¹]_{qᵢ}/qᵢ` per output limb); the input limbs are the *last*
   `m` ones, the output limbs the first `k` (`inputIndex = sizeO`, `dcrtpoly-impl.h:1551-1554`).

No base switch follows: the result is already in the basis `qs`.

**What the result is.** With `A` the representative of operand 1 in `[-Q/2, Q/2)` and
`W = (P·B + S)/Q`, `S = Σᵢ yᵢ·Q/qᵢ ∈ [0, k·Q)`, component `j` of the result is
`⌊t·(A ⊗ W)ⱼ/P⌉ mod Q`: the textbook `t·(A ⊗ B)ⱼ/Q` plus `t·(A ⊗ S)ⱼ/(P·Q)` plus a rounding, so
`2·|Q·Xⱼ − t·(A ⊗ B)ⱼ| ≤ Q·(1 + 2·t·N·k·Q/P)`, and `2·‖B‖∞ ≤ Q + 2·k·Q/P`. This is
`Spec.BudgetBFV.poverqSlack t N Q P k 0 0`. The tensor product may wrap around modulo `Q·P`;
that is harmless, since `⌊t·(x + Q·P·u)/P⌉ = ⌊t·x/P⌉ + t·Q·u`.

**What is idealised.** OpenFHE computes two rounded sums in binary64: the overflow count of
each exact base switch (`nu`, `dcrtpoly-impl.h:1080-1089`: here `HPS.overflow`, exact) and the
fractional part of the scaling (`nu`, `dcrtpoly-impl.h:1566-1571`: here the `roundDiv` inside
`HPS.scale1`, exact). The library's result equals this model's whenever the floating-point error
does not move a sum across a half-integer; nothing is claimed here about the floating-point
code beyond that (`Spec.BudgetBFV.poverqSlack` with nonzero tolerances is the paper analysis of
it). Also not modelled: machine-word arithmetic (Barrett reduction, 128-bit accumulation; the
table entry `qᵢ − [P·(Q/qᵢ)⁻¹]_{qᵢ}` is `[−P·(Q/qᵢ)⁻¹]_{qᵢ}` here, the same number for
`qᵢ > 1` coprime to `P`), the NTT (the model multiplies coefficient vectors), and the generic
component count (two-component operands, as `bfvMul`).

**The side condition** (`poverqAuxOK?`): the moduli of `qs ++ ps` are positive and pairwise
coprime. Nothing else is needed for the bound above: no oddness (any representative in
`[-Q/2, Q/2]` will do for `A`), no lower bound on `P` (a small `P` makes the slack large, not
the statement false; `Spec.BudgetBFV.poverqSlack`'s own flag `2·k < P` is not used).

**The leveled variant** (`leveledMul`; `HPSPOVERQLEVELED` on top-level operands,
`bfvrns-leveledshe.cpp:263-301`, `:391-405`) with `drop ≥ 1` limbs dropped internally:
`Q_l`, `P_l` are the first `k − drop` limbs of `qs`, `ps`, and `D = Q/Q_l`.
Operand 1 is scaled from `Q` to `Q_l` by rounding (`POverQ.scaleRoundOut 1 (qs.drop l) Q_l`;
`ScaleAndRound` with the tables `QlQHatInvModqDivqModq`, `…Frac`,
`bfvrns-cryptoparameters.cpp:597-618`) and expanded exactly to `P_l`; operand 2 is converted
from the full `Q` to `P_l` (table `mNegRlQHatInvModq`, `bfvrns-cryptoparameters.cpp:491-503`)
and exactly to `Q_l`; the product is scaled by `t/P_l` into `Q_l` and multiplied by `D` back
into `Q` (`POverQ.expandQlHat`; `ExpandCRTBasisQlHat`, `dcrtpoly-impl.h:1196-1216`). `drop = 0`
is `poverqMul` with `ps.take k`. How many limbs the library drops (`FindLevelsToDrop`) is not
modelled: `drop` is a parameter. With `A' = ⌊a/D⌉` centred modulo `Q_l` and `A = D·A' − (D·⌊a/D⌉ − a)`
(`A ≡ a (mod Q)`, `2·‖A‖∞ ≤ Q + D`), `B` as above with `P_l` for `P`, the result is
`D·⌊t·(A' ⊗ W)/P_l⌉ mod Q`, within `Spec.BudgetBFV.leveledSlack t N Q Q_l P_l k 0 0 0` of
`t·(A ⊗ B)/Q`; side condition `leveledAuxOK?`.
-/

namespace Challenge.BFVMul
open Spec NPoly Scheme

variable {N : ℕ}

namespace POverQ

/-- `yᵢ = [xᵢ·(−P)·(Q/qᵢ)⁻¹]_{qᵢ} ∈ [0, qᵢ)`, from the residues `x` modulo `qs`
(`dcrtpoly-impl.h:957-959` with the table `mNegRlQlHatInvModq`,
`bfvrns-cryptoparameters.cpp:505-520`). -/
def negPDigits (qs : List ℕ) (P : ℕ) (x : List ℤ) : List ℤ :=
  List.zipWith (fun q xi => xi * (-((P : ℤ) * HPS.invMod (qs.prod / q) q) % q) % q) qs x

/-- `Σᵢ yᵢ·[qᵢ⁻¹]_p mod p` (`dcrtpoly-impl.h:960-965` with the table `qInvModr`,
`bfvrns-cryptoparameters.cpp:522-528`). -/
def approx1 (qs : List ℕ) (y : List ℤ) (p : ℕ) : ℤ :=
  (List.zipWith (fun q yi => yi * HPS.invMod q p) qs y).sum % p

/-- Fast scaling by `P/Q` of an RNS polynomial in the basis `qs`; the result is in the basis
`ps` (`ApproxSwitchCRTBasis` as called by `FastExpandCRTBasisPloverQ`,
`dcrtpoly-impl.h:1182-1185`). -/
def fastScale (qs ps : List ℕ) (x : List (IntPoly N)) : List (IntPoly N) :=
  ps.map fun p => ⟨fun i => approx1 qs (negPDigits qs ps.prod (HPS.residues x i)) p⟩

/-- `FastExpandCRTBasisPloverQ` (`dcrtpoly-impl.h:1181-1194`): from the basis `qs` to
`ql ++ ps`: the fast scaling into `ps`, preceded by its exact base switch to `ql` (`ql = qs` for
`HPSPOVERQ`). -/
def fastExpand (qs ps ql : List ℕ) (x : List (IntPoly N)) : List (IntPoly N) :=
  let w := fastScale qs ps x
  HPS.switchBasis ps ql w ++ w

/-- `ScaleAndRound` (`dcrtpoly-impl.h:1536`) with input basis `ins` and output basis `outs`:
`⌊t·x/I⌉ mod o` for every `o ∈ outs`, `I = ∏ ins`, from the limbs `xin` of `x` modulo `ins` and
`xout` modulo `outs` (`HPS.scale1`; the rounded sum is exact here). -/
def scaleRoundOut (t : ℕ) (ins outs : List ℕ) (xin xout : List (IntPoly N)) :
    List (IntPoly N) :=
  List.zipWith (fun o xo => ⟨fun i => HPS.scale1 t ins outs (HPS.residues xin i) o (xo.coeff i)⟩)
    outs xout

/-- `ExpandCRTBasisQlHat` (`dcrtpoly-impl.h:1196-1216`): from the limbs of `x` modulo `ql` (the
first limbs of `qs`), the limbs modulo `qs` of `(Q/Q_l)·x`: multiplied by `[Q/Q_l]_{qᵢ}` in the
limbs of `ql`, zero in the others. -/
def expandQlHat (qs ql : List ℕ) (x : List (IntPoly N)) : List (IntPoly N) :=
  List.zipWith (fun (q : ℕ) (xi : IntPoly N) =>
      (⟨fun i => xi.coeff i * ((qs.prod / ql.prod % q : ℕ) : ℤ) % q⟩ : IntPoly N)) ql x ++
    (qs.drop ql.length).map fun _ => ⟨fun _ => 0⟩

end POverQ

/-- **P-over-Q multiplication** (OpenFHE `HPSPOVERQ`, idealised: module docstring) of two
2-component BFV ciphertexts at ciphertext basis `qs`, with auxiliary basis `ps`. The operands are
integer representatives, read modulo each `q ∈ qs`; the result is the three components,
reconstructed from their final `qs`-limbs with coefficients in `[0, Q)`. Everything in between is
on limbs. -/
def poverqMul (t : ℕ) (qs ps : List ℕ) (c d : List (IntPoly N)) : List (IntPoly N) :=
  let a := c.map fun x => HPS.expand qs ps (HPS.toLimbs qs x)
  let b := d.map fun x => POverQ.fastExpand qs ps qs (HPS.toLimbs qs x)
  (HPS.tensor (qs ++ ps) a b).map fun x =>
    HPS.reconstruct qs (POverQ.scaleRoundOut t ps qs (x.drop qs.length) (x.take qs.length))

/-- The side condition on the bases under which `poverqMul` has the slack
`Spec.BudgetBFV.poverqSlack t N Q P k 0 0` (module docstring): all moduli positive and pairwise
coprime. (`t` and `N` are not constrained; they are arguments for uniformity with
`hpsAuxOK?`.) -/
def poverqAuxOK? (_t _N : ℕ) (qs ps : List ℕ) : Bool :=
  (qs ++ ps).all (fun m => decide (0 < m)) && decide ((qs ++ ps).Pairwise Nat.Coprime)

/-- **Leveled P-over-Q multiplication** (OpenFHE `HPSPOVERQLEVELED` on top-level operands,
idealised: module docstring) with `drop` limbs dropped internally: computed at the first
`k − drop` limbs `Q_l` of `qs` and `P_l` of `ps`, and multiplied by `Q/Q_l`. The result is
reconstructed from its `qs`-limbs with coefficients in `[0, Q)`. -/
def leveledMul (t : ℕ) (qs ps : List ℕ) (drop : ℕ) (c d : List (IntPoly N)) : List (IntPoly N) :=
  let l := qs.length - drop
  let ql := qs.take l
  let pl := ps.take l
  let a := c.map fun x =>
    let xl := HPS.toLimbs qs x
    HPS.expand ql pl (POverQ.scaleRoundOut 1 (qs.drop l) ql (xl.drop l) (xl.take l))
  let b := d.map fun x => POverQ.fastExpand qs pl ql (HPS.toLimbs qs x)
  (HPS.tensor (ql ++ pl) a b).map fun x =>
    HPS.reconstruct qs
      (POverQ.expandQlHat qs ql (POverQ.scaleRoundOut t pl ql (x.drop ql.length) (x.take ql.length)))

/-- The side condition of `leveledMul`, under which it has the slack
`Spec.BudgetBFV.leveledSlack t N Q Q_l P_l k 0 0 0`: all moduli of `qs ++ ps.take (k − drop)`
positive and pairwise coprime. -/
def leveledAuxOK? (_t _N : ℕ) (qs ps : List ℕ) (drop : ℕ) : Bool :=
  (qs ++ ps.take (qs.length - drop)).all (fun m => decide (0 < m)) &&
  decide ((qs ++ ps.take (qs.length - drop)).Pairwise Nat.Coprime)

/-! ## A direct integer computation, for the checks below

The same quantities on integers, with no limbs: the representatives the algorithm multiplies and
the result before reduction modulo `Q`. Used by the `#guard`s only. -/

namespace POverQ

/-- The representative of `x` modulo `m` in `[-m/2, m/2)`. -/
def cen (m : ℕ) (x : ℤ) : ℤ := x - (m : ℤ) * roundDiv x m

/-- `S = Σᵢ [x·(−P)·(Q/qᵢ)⁻¹]_{qᵢ}·(Q/qᵢ) ∈ [0, k·Q)`, congruent to `−P·x` modulo `Q`. -/
def refS (qs : List ℕ) (P : ℕ) (x : ℤ) : ℤ :=
  (qs.map fun q : ℕ => (-(P : ℤ) * x * HPS.invMod (qs.prod / q) q % q) * ((qs.prod / q : ℕ) : ℤ)).sum

/-- `W`: the representative in `[-P/2, P/2)` of `S/Q` modulo `P`. -/
def refW (qs : List ℕ) (P : ℕ) (x : ℤ) : ℤ := cen P (refS qs P x * HPS.invMod qs.prod P)

/-- `B = (Q·W − S)/P`: the representative of operand 2 the algorithm multiplies. -/
def refB (qs : List ℕ) (P : ℕ) (x : ℤ) : ℤ := (qs.prod * refW qs P x - refS qs P x) / P

/-- The claims about `poverqMul t qs ps c d` checked numerically (two-component `c`, `d`; slack
`e`, `rho`): `B` is an integer, congruent to `d` modulo `Q`, with `2·|B| ≤ Q + e`; the result is
`⌊t·(A ⊗ W)/P⌉` modulo `Q`, and `2·|Q·X − t·(A ⊗ B)| ≤ Q·rho`. -/
def refCheck (t : ℕ) (qs ps : List ℕ) (e rho : ℕ) (c d : List (IntPoly N)) : Bool :=
  let Q := qs.prod
  let P := ps.prod
  let A : List (IntPoly N) := c.map fun x => ⟨fun i => cen Q (x.coeff i)⟩
  let W : List (IntPoly N) := d.map fun x => ⟨fun i => refW qs P (x.coeff i)⟩
  let B : List (IntPoly N) := d.map fun x => ⟨fun i => refB qs P (x.coeff i)⟩
  let X : List (IntPoly N) := (Challenge.Source.tensor A W).map (Challenge.BFV.scaleRound t P)
  let T := Challenge.Source.tensor A B
  let out := poverqMul t qs ps c d
  let idx := List.finRange N
  (d.all fun x => idx.all fun i =>
    (Q * refW qs P (x.coeff i) - refS qs P (x.coeff i)) % P == 0 &&
    (refB qs P (x.coeff i) - x.coeff i) % Q == 0 &&
    decide (2 * |refB qs P (x.coeff i)| ≤ Q + e)) &&
  out.length == 3 &&
  ((List.range 3).all fun j => idx.all fun i =>
    ((out.getD j 0).coeff i - (X.getD j 0).coeff i) % Q == 0 &&
    decide (2 * |(Q : ℤ) * (X.getD j 0).coeff i - t * (T.getD j 0).coeff i| ≤ Q * rho))

/-- The claims about `leveledMul t qs ps drop c d` checked numerically (two-component `c`, `d`;
slack `e`, `rho`), with `Q_l`, `P_l` the first `k − drop` limbs and `D = Q/Q_l`:
`A' = ⌊a/D⌉` centred modulo `Q_l`, `A = D·A' − α` with `α` the centred residue of `D·A' − a`
modulo `Q` (so `A ≡ a`), `W`, `B` as in `refCheck` with `P_l` for `P` (and all the limbs of `Q`),
`X = D·⌊t·(A' ⊗ W)/P_l⌉`. Checked: `B` is an integer congruent to `d` modulo `Q`,
`2·|A|, 2·|B| ≤ Q + e`, the result is `X` modulo `Q`, and `2·|Q·X − t·(A ⊗ B)| ≤ Q·rho`. -/
def refCheckLeveled (t : ℕ) (qs ps : List ℕ) (drop e rho : ℕ) (c d : List (IntPoly N)) : Bool :=
  let l := qs.length - drop
  let Q := qs.prod
  let Ql := (qs.take l).prod
  let Pl := (ps.take l).prod
  let D := Q / Ql
  let A' : List (IntPoly N) := c.map fun x => ⟨fun i => cen Ql (roundDiv (x.coeff i) D)⟩
  let A : List (IntPoly N) := c.map fun x =>
    ⟨fun i => let a' := cen Ql (roundDiv (x.coeff i) D); D * a' - cen Q (D * a' - x.coeff i)⟩
  let W : List (IntPoly N) := d.map fun x => ⟨fun i => refW qs Pl (x.coeff i)⟩
  let B : List (IntPoly N) := d.map fun x => ⟨fun i => refB qs Pl (x.coeff i)⟩
  let X : List (IntPoly N) := (Challenge.Source.tensor A' W).map fun T =>
    ⟨fun i => D * roundDiv (t * T.coeff i) Pl⟩
  let T := Challenge.Source.tensor A B
  let out := leveledMul t qs ps drop c d
  let idx := List.finRange N
  (d.all fun x => idx.all fun i =>
    (Q * refW qs Pl (x.coeff i) - refS qs Pl (x.coeff i)) % Pl == 0 &&
    (refB qs Pl (x.coeff i) - x.coeff i) % Q == 0 &&
    decide (2 * |refB qs Pl (x.coeff i)| ≤ Q + e)) &&
  (A.all fun x => idx.all fun i => decide (2 * |x.coeff i| ≤ Q + e)) &&
  out.length == 3 &&
  ((List.range 3).all fun j => idx.all fun i =>
    ((out.getD j 0).coeff i - (X.getD j 0).coeff i) % Q == 0 &&
    decide (2 * |(Q : ℤ) * (X.getD j 0).coeff i - t * (T.getD j 0).coeff i| ≤ Q * rho))

/-- The largest distance modulo `Q` between two lists of polynomials, coefficient by
coefficient. -/
def maxDist (Q : ℕ) (x y : List (IntPoly N)) : ℤ :=
  ((List.zipWith (fun (a b : IntPoly N) =>
      (List.finRange N).map fun i => |cen Q (a.coeff i - b.coeff i)|) x y).flatten).foldl max 0

end POverQ

/-! ## Checks at tiny parameters

`N = 4`, `t = 5`, `qs = [7, 11]` (`Q = 77`), `ps = [13, 17]` (`P = 221`): the slack is
`e = ⌈2·2·77/221⌉ = 2`, `rho = 1 + ⌈2·5·4·2·77/221⌉ = 29`. On random and on extreme operands
(coefficients `(Q ± 1)/2`, `Q − 1`) the limb-level result is the direct integer computation, the
representatives and the result are within the slack, and the result is *not* the textbook one:
it differs from `bfvMul` modulo `Q` by up to 4 (exact rounding of `t·(A ⊗ B)/Q` gives `bfvMul`
modulo `Q` for all representatives `A`, `B`). The bound needs its `rho`: it fails with
`rho = 1`, the textbook value. -/

open Spec.BudgetBFV in
#guard poverqSlack 5 4 77 221 2 0 0 == ⟨2, 29, true⟩

#guard poverqAuxOK? 5 4 [7, 11] [13, 17]

#guard
  let c : List (IntPoly 4) := [⟨![3, 76, 41, 20]⟩, ⟨![55, 9, 0, 68]⟩]
  let d : List (IntPoly 4) := [⟨![38, 39, 1, 70]⟩, ⟨![12, 33, 64, 5]⟩]
  let x : List (IntPoly 4) := [⟨![38, 38, 38, 38]⟩, ⟨![39, 39, 39, 39]⟩]
  let y : List (IntPoly 4) := [⟨![38, 39, 38, 39]⟩, ⟨![76, 1, 38, 5]⟩]
  POverQ.refCheck 5 [7, 11] [13, 17] 2 29 c d && POverQ.refCheck 5 [7, 11] [13, 17] 2 29 c c &&
  POverQ.refCheck 5 [7, 11] [13, 17] 2 29 x y && POverQ.refCheck 5 [7, 11] [13, 17] 2 29 x x &&
  POverQ.refCheck 5 [7, 11] [13, 17] 2 29 x c

#guard
  let x : List (IntPoly 4) := [⟨![38, 38, 38, 38]⟩, ⟨![39, 39, 39, 39]⟩]
  let y : List (IntPoly 4) := [⟨![38, 39, 38, 39]⟩, ⟨![76, 1, 38, 5]⟩]
  POverQ.maxDist 77 (poverqMul 5 [7, 11] [13, 17] x y) (Challenge.BFV.bfvMul 5 77 x y) == 3 &&
  POverQ.maxDist 77 (poverqMul 5 [7, 11] [13, 17] x x) (Challenge.BFV.bfvMul 5 77 x x) == 4 &&
  !POverQ.refCheck 5 [7, 11] [13, 17] 2 1 x y

-- Moduli with a common factor are rejected, and the result is then not the integer computation.
#guard !poverqAuxOK? 5 4 [7, 11] [13, 21]

#guard
  let c : List (IntPoly 4) := [⟨![3, 76, 41, 20]⟩, ⟨![55, 9, 0, 68]⟩]
  let d : List (IntPoly 4) := [⟨![38, 39, 1, 70]⟩, ⟨![12, 33, 64, 5]⟩]
  !POverQ.refCheck 5 [7, 11] [13, 21] 2 29 c d

-- An even ciphertext modulus and a tiny auxiliary modulus are accepted: the bound holds with
-- the (then large) slack.
open Spec.BudgetBFV in
#guard
  let c : List (IntPoly 4) := [⟨![3, 87, 44, 20]⟩, ⟨![55, 9, 0, 43]⟩]
  let d : List (IntPoly 4) := [⟨![44, 45, 1, 70]⟩, ⟨![12, 33, 64, 5]⟩]
  let s := poverqSlack 5 4 88 3 2 0 0
  poverqAuxOK? 5 4 [8, 11] [3] && s == ⟨118, 2348, false⟩ &&
  POverQ.refCheck 5 [8, 11] [3] s.e s.rho c d

/-! `N = 2`, `t = 2`, `qs = [11, 13]` (`Q = 143`), `ps = [15, 16]`, secret `1 − X`: the product of
an encryption of `1 + X` (noise `1`) and one of `X` (noise `−X`) decrypts to `X·(1 + X) = 1 + X`;
with the auxiliary basis `[3]` it does not. (The same example, evaluated by the kernel, is in
`FHE/BFV/MulPOverQExample.lean`.) -/

#guard
  let s : IntPoly 2 := ⟨![1, -1]⟩
  let c : List (IntPoly 2) := [⟨![-69, 10]⟩, ⟨![40, 101]⟩]
  let d : List (IntPoly 2) := [⟨![-90, 6]⟩, ⟨![13, 77]⟩]
  let dec := fun (x : List (IntPoly 2)) =>
    let m := bfvDecrypt 2 s (x.map (ofInt 143))
    [(m.coeff 0).val, (m.coeff 1).val]
  dec c == [1, 1] && dec d == [0, 1] &&
  dec (poverqMul 2 [11, 13] [15, 16] c d) == [1, 1] &&
  dec (poverqMul 2 [11, 13] [15, 16] c c) == [0, 0] &&
  POverQ.refCheck 2 [11, 13] [15, 16] 3 11 c d &&
  dec (poverqMul 2 [11, 13] [3] c d) != [1, 1]

/-! The leveled variant. `N = 2`, `t = 2`, `qs = [11, 13, 17]` (`Q = 2431`), `ps = [15, 16, 19]`,
one limb dropped (`Q_l = 143`, `P_l = 240`, `D = 17`): the slack is
`Spec.BudgetBFV.leveledSlack 2 2 2431 143 240 3 0 0 0 = ⟨61, 330, true⟩`; the result is the direct
integer computation, within the slack, decrypts, and is far from the textbook one (distance 37
modulo `Q`). With `drop = 0` it is `poverqMul`. -/

open Spec.BudgetBFV in
#guard leveledSlack 2 2 2431 143 240 3 0 0 0 == ⟨61, 330, true⟩

#guard leveledAuxOK? 2 2 [11, 13, 17] [15, 16, 19] 1
#guard !leveledAuxOK? 2 2 [11, 13, 17] [15, 22, 19] 1

#guard
  let s : IntPoly 2 := ⟨![1, -1]⟩
  let c : List (IntPoly 2) := [⟨![-1485, -86]⟩, ⟨![700, 2001]⟩]
  let d : List (IntPoly 2) := [⟨![-2290, -450]⟩, ⟨![313, 1977]⟩]
  let dec := fun (x : List (IntPoly 2)) =>
    let m := bfvDecrypt 2 s (x.map (ofInt 2431))
    [(m.coeff 0).val, (m.coeff 1).val]
  let coeffs := fun (x : List (IntPoly 2)) => x.map fun a => [a.coeff 0, a.coeff 1]
  dec c == [1, 1] && dec d == [0, 1] &&
  dec (leveledMul 2 [11, 13, 17] [15, 16, 19] 1 c d) == [1, 1] &&
  dec (leveledMul 2 [11, 13, 17] [15, 16, 19] 1 c c) == [0, 0] &&
  POverQ.refCheckLeveled 2 [11, 13, 17] [15, 16, 19] 1 61 330 c d &&
  POverQ.refCheckLeveled 2 [11, 13, 17] [15, 16, 19] 1 61 330 c c &&
  !POverQ.refCheckLeveled 2 [11, 13, 17] [15, 16, 19] 1 61 17 c d &&
  POverQ.maxDist 2431 (leveledMul 2 [11, 13, 17] [15, 16, 19] 1 c d)
    (Challenge.BFV.bfvMul 2 2431 c d) == 37 &&
  coeffs (leveledMul 2 [11, 13, 17] [15, 16, 19] 0 c d) == [[78, 2071], [135, 1747], [21, 2059]] &&
  coeffs (poverqMul 2 [11, 13, 17] [15, 16, 19] c d) == [[78, 2071], [135, 1747], [21, 2059]]

-- Extreme and random operands at `N = 2`, `t = 5`, `qs = [7, 11, 13]`, one and two limbs dropped.
open Spec.BudgetBFV in
#guard
  let c : List (IntPoly 2) := [⟨![500, 1000]⟩, ⟨![501, 0]⟩]
  let d : List (IntPoly 2) := [⟨![1000, 500]⟩, ⟨![977, 501]⟩]
  let s1 := leveledSlack 5 2 1001 77 323 3 0 0 0
  let s2 := leveledSlack 5 2 1001 7 17 3 0 0 0
  POverQ.refCheckLeveled 5 [7, 11, 13] [17, 19, 23] 1 s1.e s1.rho c d &&
  POverQ.refCheckLeveled 5 [7, 11, 13] [17, 19, 23] 1 s1.e s1.rho d c &&
  POverQ.refCheckLeveled 5 [7, 11, 13] [17, 19, 23] 2 s2.e s2.rho c d &&
  POverQ.refCheckLeveled 5 [7, 11, 13] [17, 19, 23] 2 s2.e s2.rho d d

end Challenge.BFVMul
