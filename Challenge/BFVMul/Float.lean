import Challenge.BFVMul
import Spec.Float

/-!
# Challenge.BFVMul.Float — the HPS-family multiplications with their binary64 sums   (LOCKED definitions and statements; proofs in `Validation/BFVMul/Float*.lean`)

`Challenge.BFVMul.HPS` and `Challenge.BFVMul.POverQ` define OpenFHE's `HPS`, `HPSPOVERQ` and
`HPSPOVERQLEVELED` multiplications with the two sums the library computes in `double` replaced by
exact rational rounding. This file defines them **as the library computes them**: the two sums
are evaluated in an arithmetic `A : Spec.Float.Arith`, operation by operation, and truncated.
The statements say that for *every* arithmetic conforming to the standard model
(`Spec.Float.Conforms`) the sums are within the tolerances `Spec.BudgetBFV.doubleSw`, `doubleSr`
of their exact values, and that the multiplications then meet the `mul` contract of
`Spec.TraceBFV` with the slacks `Spec.BudgetBFV.hpsSlack`, `poverqSlack`, `leveledSlack` *at those
tolerances* (the numbers `fhe_check` budgets for with `floatTolerant = true`).

**What these statements do and do not say.** The contract is met at slacks *evaluated at the
tolerances* `doubleSw`, `doubleSr`: the floating-point error is not shown to vanish, it is
CHARGED to the noise budget. The library does not compute the idealised algorithms of
`Challenge.BFVMul.HPS`/`POverQ`: with two 60-bit limbs its scaling sum is off by up to about
`2¹¹` units per coefficient (`doubleSr`), and the
rounding slack `rho` of the budget grows accordingly.

* *Covered under the model* (`Spec.Float.Conforms`): every binary64 operation of the two sums
  and of the tables they read.
* *Modelled as exact modular arithmetic, NOT verified*: the machine-word integer steps
  (`ModMulFastConst`, `Mul128` accumulation, `BarrettUint128ModUint64`, `ModAddFast`/`ModSubFast`,
  the table look-up `alphaQModp[⌊nu⌋]` read as multiplication by `⌊nu⌋`) and the NTT, as in
  `Challenge.BFVMul.HPS`.
* *Checked by the side condition*: the precondition under which the unreduced 128-bit
  accumulation `curValue += Mul128(…)` (`dcrtpoly-impl.h:1095-1097`, `:1577-1583`,
  `:1597-1603`) cannot wrap: `floatBasisOK` bounds every modulus by `2⁶⁰` (OpenFHE's own
  `MAX_MODULUS_SIZE64 = 60`, `basicint.h:40`, which is also what its Barrett and
  `ModMulFastConst` routines assume) and the number of limbs by 128, so at most 129 products of
  two residues below `2⁶⁰` are added: `acc_no_overflow` (proved). That the library's reduction
  routines are correct under that bound is argued, not proved. The other compile-time branch of
  these accumulations (the `#else` taken without `HAVE_INT128`) reduces
  every product modulo the modulus and adds modularly instead; the binary64 sums are computed
  before the branch, outside it, so the branch gives the same residues and the same sums, given
  correct modular reduction, and the transcription covers both.
* *Build option.* The transcriptions are for OpenFHE built with its default
  `WITH_REDUCED_NOISE=OFF` (`CMakeLists.txt:95`). With the option on, `ApproxSwitchCRTBasis`
  (`dcrtpoly-impl.h:938-985`) takes centred digits instead of digits in `[0, q_i)`. That routine
  is called by `FastExpandCRTBasisPloverQ` (`:1182`), which the P-over-Q multiplications use, and
  by `ApproxModUp` and `ApproxModDown` (`:1002`, `:1040`) of hybrid key switching, so their
  outputs differ; parameter generation changes as well. A build with the option on is not
  covered.
* Two facts about the casts are proved: the table index `⌊nuSw⌋` is in `[0, k]`
  (`nuSw_index`; the table `alphaQModp` has `k + 1` rows), and `nu_range`: both sums are
  nonnegative, `nuSw < 2¹⁷`, `nuSr < 2⁸¹`, so each cast truncates exactly whichever branch of
  `isConvertableToNativeInt` is taken.
* *Squaring* is covered for `HPS` only (`stepOK_square_hps_float`); under the P-over-Q
  techniques the library's squaring is a `mul` of the operand with itself, with two different
  lifts, and is covered as such only where the caller presents it as a `mul`.
* *Determinism.* `Arith.mulAdd` and `Fl.Sums` are functions: the same arguments give the same
  result. A build in which the same loop is compiled in several copies with different
  contraction choices is still covered, because the proofs use `Fl.SumsOK` only call by call
  (each truncated sum is within tolerance; no proof compares two calls), and every per-call
  result of such a build is the result of *some* conforming `mulAdd`. The statements are
  nevertheless stated for one function `S`; a per-call restatement was not made.

Source: upstream OpenFHE v1.6.1, tag `v1.6.1`, commit
`b59e1f291965f14fbee5172cd83a20f5b856204f` (the commit `harness/frontend/openfhe/build_openfhe.sh`
pins). File and line numbers are that commit's. `NATIVEINT == 64` with `HAVE_INT128` only.

## The floating-point code, exactly

All of it is `double`; there is no `long double` in these paths, nor anywhere in v1.6.1's
lattice, BFV or decryption code (the only occurrence in `src/core`, `src/pke/lib` is the discrete
Gaussian sampler). The *decryption* `ScaleAndRound` overload (`dcrtpoly-impl.h:1220-1490`, also
`double` only) is not part of multiplication; it is modelled separately in `Spec/DecryptBFV.lean`.

*Tables* (`src/pke/lib/scheme/bfvrns/bfvrns-cryptoparameters.cpp`, computed once at set-up):

* `m_qInv[i] = 1. / static_cast<double>(q_i)` (`:263-266`), `m_rInv[j]` likewise for the
  auxiliary moduli (`:427-430`): `Fl.qInv`: one conversion, one division.
* `m_tRSHatInvModsDivsFrac[i]` (`:283-289`), `m_tQlSlHatInvModsDivsFrac[l][j]` (`:537-546`,
  `:566-575`), `m_QlQHatInvModqDivqFrac[l][j]` (`:598-606`): each is
  `static_cast<double>(n) / static_cast<double>(m)` with `m` a modulus and `n` an exact
  big-integer residue in `[0, m)`: `Fl.frac`: two conversions, one division.

*Loops* (`src/core/include/lattice/hal/default/dcrtpoly-impl.h`, once per coefficient):

* `SwitchCRTBasis` (`:1080-1089`): `double nu{0.5}; for i: nu += y_i.ConvertToDouble() * qInv[i];`
  then `static_cast<size_t>(nu)`: `Fl.nuSw` and its floor. `ConvertToDouble` is
  `static_cast<double>` of the 64-bit word (`ubintnat.h:1431-1433`).
* `ScaleAndRound` (`:1566-1574`): `double nu = 0.5; for i: nu += Frac[i] * x_i.ConvertToDouble();`
  then `static_cast<BasicInteger>(nu)` if `isConvertableToNativeInt(nu)` (`|nu|` at most
  `Max64BitValue() = 2⁶³ − 2⁹ − 1`, `utilities.h:106-108`), else
  `static_cast<DoubleNativeInt>(nu)` (128-bit; `:1573-1611`): `Fl.nuSr` and its floor. Both casts
  truncate, exactly, a value that is nonnegative and below `2⁸¹` (`nu_range`), so the integer the
  limb arithmetic then uses is `⌊nu⌋` in both branches.

`s += a * b` is `Spec.Float.Arith.mulAdd` (a product and a sum, or one fused multiply-add). The
constants `0.5` and `1.` are exact.

Everything else in the three multiplications is integer arithmetic and is as in
`Challenge.BFVMul.HPS`/`POverQ` (same definitions, reused); `Fl.switch1`, `Fl.scale1` and what is
built from them differ from `HPS.switch1`, `HPS.scale1` only in taking the two truncated sums
from a `Fl.Sums`, which is `Fl.floatSums A` for the library and `Fl.floatSums Spec.Float.exact`
for the idealised algorithm.

## Side conditions (all decidable)

* `floatBasisOK ms`: at most 128 moduli, each in `[1, 2⁶⁰)`. The tolerance statements hold more
  generally (the proofs use only: at most `2¹⁶` moduli below `2⁶⁴`); the stricter bound is what
  makes the library's integer steps compute the transcription (above). The values the
  floating-point code computes stay inside the window of `Spec.Float.InRange` (proved, not
  assumed).
* `floatAuxOK? qs ps`: `floatBasisOK` of both bases, all moduli odd, at least 3 and pairwise
  coprime (what `Challenge.CertifyBFV.basisOK` checks).
* for `HPS` only, the flag `ok` of the slack `Spec.BudgetBFV.hpsSlack` (the scaled product must
  fit the auxiliary modulus). The P-over-Q statements need no such flag.

## What is not covered

The generic component count; `FindLevelsToDrop` (the number of dropped limbs is a parameter);
the non-`HAVE_INT128` and `NATIVEINT != 64` branches; and any platform outside `Spec.Float`'s
docstring. (Key switching after an internal drop, `Spec.BudgetBFV.ksLeveled`, is proved in
`Challenge/BFVMul/KSLeveled.lean`: `stepOK_relin_leveled_tol`, `stepOK_keySwitch_leveled_tol`.)
-/

namespace Challenge.BFVMul
open Spec NPoly Scheme Source Correct Challenge.BFV Spec.Float

namespace Fl

/-! ## The two sums -/

/-- `1. / static_cast<double>(q)`: an entry of `m_qInv` / `m_rInv`
(`bfvrns-cryptoparameters.cpp:263-266`, `:427-430`). -/
def qInv (A : Arith) (q : ℕ) : ℚ := A.div 1 (A.ofNat q)

/-- `static_cast<double>(n) / static_cast<double>(m)`: an entry of a `…Frac` table
(`bfvrns-cryptoparameters.cpp:283-289`, `:537-546`, `:566-575`, `:598-606`). -/
def frac (A : Arith) (n m : ℕ) : ℚ := A.div (A.ofNat n) (A.ofNat m)

/-- `nu` of `SwitchCRTBasis` after its loop (`dcrtpoly-impl.h:1080-1087`): from `0.5`, for each
source modulus `q` and digit `y`, `nu += y.ConvertToDouble() * qInv`. -/
def nuSw (A : Arith) (qs : List ℕ) (y : List ℤ) : ℚ :=
  (qs.zip y).foldl (fun s p => A.mulAdd s (A.ofNat p.2.toNat) (qInv A p.1)) (1 / 2)

/-- `nu` of `ScaleAndRound` after its loop (`dcrtpoly-impl.h:1566-1571`): from `0.5`, for each
input modulus `m`, table numerator `n` and residue `x`, `nu += Frac * x.ConvertToDouble()`. -/
def nuSr (A : Arith) (ms : List ℕ) (ns x : List ℤ) : ℚ :=
  ((ms.zip ns).zip x).foldl
    (fun s p => A.mulAdd s (frac A p.1.2.toNat p.1.1) (A.ofNat p.2.toNat)) (1 / 2)

/-- The exact value `nuSw` approximates: `1/2 + Σᵢ yᵢ/qᵢ`. -/
def exactSw (qs : List ℕ) (y : List ℤ) : ℚ :=
  1 / 2 + ((qs.zip y).map fun p => (p.2 : ℚ) / (p.1 : ℚ)).sum

/-- The exact value `nuSr` approximates: `1/2 + Σᵢ xᵢ·nᵢ/mᵢ`. -/
def exactSr (ms : List ℕ) (ns x : List ℤ) : ℚ :=
  1 / 2 + (((ms.zip ns).zip x).map fun p => (p.2 : ℚ) * (p.1.2 : ℚ) / (p.1.1 : ℚ)).sum

/-- The two truncated sums a multiplication uses (`Spec.Float.Sums`: `sw qs y` is the overflow
count of a base switch from the moduli `qs` with digits `y`; `sr ms ns x` is the truncated
fractional sum of a scaling with input moduli `ms`, table numerators `ns` and residues `x`). -/
abbrev Sums := Spec.Float.Sums

/-- The sums as the library computes them in the arithmetic `A`: the floors of `nuSw`, `nuSr`
(`static_cast<size_t>(nu)`, `dcrtpoly-impl.h:1089`; `static_cast<BasicInteger>(nu)` /
`static_cast<DoubleNativeInt>(nu)`, `:1574`, `:1594`). -/
def floatSums (A : Arith) : Sums :=
  { sw := fun qs y => ⌊nuSw A qs y⌋, sr := fun ms ns x => ⌊nuSr A ms ns x⌋ }

end Fl

/-- The sizes for which the floating-point multiplications are covered: at most 128 moduli,
each in `[1, 2⁶⁰)` (OpenFHE's `MAX_MODULUS_SIZE64`; with these the unreduced 128-bit
accumulations of the library cannot wrap: `acc_no_overflow`). -/
def floatBasisOK (ms : List ℕ) : Bool :=
  decide (ms.length ≤ 128) && ms.all fun m => decide (1 ≤ m) && decide (m < 2 ^ 60)

namespace Fl

/-- The digits of a base switch or the residues of a scaling are reduced: `0 ≤ v < m` for each
modulus `m` and its value `v`. -/
def Reduced (ms : List ℕ) (v : List ℤ) : Prop := ∀ p ∈ ms.zip v, 0 ≤ p.2 ∧ p.2 < (p.1 : ℤ)

/-- **The tolerances.** On reduced arguments over a basis passing `floatBasisOK`, each truncated
sum is the floor of a number within `doubleSw k / 2⁵³` (base switch, `k` moduli), resp.
`doubleSr ms / 2⁵³` (scaling), of the exact sum. -/
def SumsOK (S : Sums) : Prop :=
  (∀ (qs : List ℕ) (y : List ℤ), floatBasisOK qs = true → Reduced qs y →
    ∃ s : ℚ, S.sw qs y = ⌊s⌋ ∧
      |s - exactSw qs y| ≤ (BudgetBFV.doubleSw qs.length : ℚ) / BudgetBFV.floatDen) ∧
  (∀ (ms : List ℕ) (ns x : List ℤ), floatBasisOK ms = true → Reduced ms ns → Reduced ms x →
    ∃ s : ℚ, S.sr ms ns x = ⌊s⌋ ∧
      |s - exactSr ms ns x| ≤ (BudgetBFV.doubleSr ms : ℚ) / BudgetBFV.floatDen)

/-! ## The multiplications, with the sums of `S`

Word for word `HPS.switch1`, `HPS.scale1` and the definitions built from them, with `S.sw` in
the place of `HPS.overflow` and `S.sr` in the place of the exact rounded fractional sum. -/

variable {N : ℕ}

/-- `HPS.switch1` with the overflow count `S.sw qs y` (`dcrtpoly-impl.h:1080-1103`). -/
def switch1 (S : Sums) (qs : List ℕ) (x : List ℤ) (p : ℕ) : ℤ :=
  let y := HPS.digits qs x
  ((List.zipWith (fun q yi => yi * ((qs.prod / q % p : ℕ) : ℤ)) qs y).sum -
    S.sw qs y * ((qs.prod % p : ℕ) : ℤ)) % p

/-- `SwitchCRTBasis` (`dcrtpoly-impl.h:1058-1109`). -/
def switchBasis (S : Sums) (qs ps : List ℕ) (x : List (IntPoly N)) : List (IntPoly N) :=
  ps.map fun p => ⟨fun i => switch1 S qs (HPS.residues x i) p⟩

/-- `ExpandCRTBasis` (`dcrtpoly-impl.h:1112-1143`). -/
def expand (S : Sums) (qs ps : List ℕ) (x : List (IntPoly N)) : List (IntPoly N) :=
  x ++ switchBasis S qs ps x

/-- The numerators of the `…Frac` table of a scaling by `t/Q` into `ps`: `θᵢ mod qᵢ`. -/
def fracNums (t : ℕ) (qs ps : List ℕ) : List ℤ :=
  ((HPS.theta t qs ps).zip qs).map fun θ => θ.1 % (θ.2 : ℤ)

/-- `HPS.scale1` with the truncated fractional sum `S.sr` (`dcrtpoly-impl.h:1566-1611`). -/
def scale1 (S : Sums) (t : ℕ) (qs ps : List ℕ) (xq : List ℤ) (p : ℕ) (xp : ℤ) : ℤ :=
  let θq := (HPS.theta t qs ps).zip qs
  let int := (List.zipWith (fun (θ : ℤ × ℕ) xi => xi * (θ.1 / θ.2 % p)) θq xq).sum
  let ω := (t : ℤ) * ps.prod * HPS.invMod (qs.prod * ps.prod / p) p / p % p
  (int + xp * ω + S.sr qs (fracNums t qs ps) xq) % p

/-- `ScaleAndRound` from `qs ++ ps` into `ps` (`dcrtpoly-impl.h:1536-1649`; `HPS.scaleRound`). -/
def scaleRound (S : Sums) (t : ℕ) (qs ps : List ℕ) (x : List (IntPoly N)) : List (IntPoly N) :=
  List.zipWith
    (fun p xp =>
      ⟨fun i => scale1 S t qs ps (HPS.residues (x.take qs.length) i) p (xp.coeff i)⟩)
    ps (x.drop qs.length)

/-- `ScaleAndRound` with input basis `ins` and output basis `outs` (`POverQ.scaleRoundOut`). -/
def scaleRoundOut (S : Sums) (t : ℕ) (ins outs : List ℕ) (xin xout : List (IntPoly N)) :
    List (IntPoly N) :=
  List.zipWith
    (fun o xo => ⟨fun i => scale1 S t ins outs (HPS.residues xin i) o (xo.coeff i)⟩) outs xout

/-- `FastExpandCRTBasisPloverQ` (`dcrtpoly-impl.h:1181-1194`; `POverQ.fastExpand`): the fast
scaling is integer arithmetic, the switch from `ps` to `ql` uses `S.sw`. -/
def fastExpand (S : Sums) (qs ps ql : List ℕ) (x : List (IntPoly N)) : List (IntPoly N) :=
  let w := POverQ.fastScale qs ps x
  switchBasis S ps ql w ++ w

/-- **HPS multiplication with the sums of `S`** (`hpsMul`; OpenFHE `HPS`). -/
def hpsMul (S : Sums) (t : ℕ) (qs ps : List ℕ) (c d : List (IntPoly N)) : List (IntPoly N) :=
  let ext := fun a : IntPoly N => expand S qs ps (HPS.toLimbs qs a)
  (HPS.tensor (qs ++ ps) (c.map ext) (d.map ext)).map fun x =>
    HPS.reconstruct qs (switchBasis S ps qs (scaleRound S t qs ps x))

/-- **P-over-Q multiplication with the sums of `S`** (`poverqMul`; OpenFHE `HPSPOVERQ`, and
`HPSPOVERQLEVELED` with no internal drop). -/
def poverqMul (S : Sums) (t : ℕ) (qs ps : List ℕ) (c d : List (IntPoly N)) : List (IntPoly N) :=
  let a := c.map fun x => expand S qs ps (HPS.toLimbs qs x)
  let b := d.map fun x => fastExpand S qs ps qs (HPS.toLimbs qs x)
  (HPS.tensor (qs ++ ps) a b).map fun x =>
    HPS.reconstruct qs (scaleRoundOut S t ps qs (x.drop qs.length) (x.take qs.length))

/-- **Leveled P-over-Q multiplication with the sums of `S`** (`leveledMul`; OpenFHE
`HPSPOVERQLEVELED` at the top level with `drop` limbs dropped internally). -/
def leveledMul (S : Sums) (t : ℕ) (qs ps : List ℕ) (drop : ℕ) (c d : List (IntPoly N)) :
    List (IntPoly N) :=
  let l := qs.length - drop
  let ql := qs.take l
  let pl := ps.take l
  let a := c.map fun x =>
    let xl := HPS.toLimbs qs x
    expand S ql pl (scaleRoundOut S 1 (qs.drop l) ql (xl.drop l) (xl.take l))
  let b := d.map fun x => fastExpand S qs pl ql (HPS.toLimbs qs x)
  (HPS.tensor (ql ++ pl) a b).map fun x =>
    HPS.reconstruct qs
      (POverQ.expandQlHat qs ql
        (scaleRoundOut S t pl ql (x.drop ql.length) (x.take ql.length)))

end Fl

/-- The side condition on the two bases of a floating-point multiplication: both pass
`floatBasisOK`, and all moduli are odd, at least 3 and pairwise coprime. -/
def floatAuxOK? (qs ps : List ℕ) : Bool :=
  floatBasisOK qs && floatBasisOK ps &&
  (qs ++ ps).all (fun m => decide (3 ≤ m) && decide (m % 2 = 1)) &&
  decide ((qs ++ ps).Pairwise Nat.Coprime)

/-! ## The model is satisfiable, and the exact arithmetic gives the idealised algorithms -/

/-- The exact arithmetic conforms to the standard model. -/
theorem exact_conforms : Conforms Spec.Float.exact := sorry

/-- The coefficients of a list of polynomials (for the checks below). -/
def Fl.coeffs {N : ℕ} (x : List (IntPoly N)) : List (List ℤ) :=
  x.map fun a => (List.finRange N).map fun i => a.coeff i

/-- The sums in the exact arithmetic: the idealised algorithm. -/
def Fl.exactSums : Fl.Sums := Fl.floatSums Spec.Float.exact

-- With the exact arithmetic the transcription is the idealised algorithm (tiny parameters of
-- `Challenge.BFVMul.HPS`, `POverQ`).
#guard Fl.coeffs (Fl.hpsMul (N := 4) Fl.exactSums 5 [7, 11] [13, 17, 19]
      [⟨![3, 76, 41, 20]⟩, ⟨![55, 9, 0, 68]⟩] [⟨![38, 39, 1, 70]⟩, ⟨![12, 33, 64, 5]⟩])
  == Fl.coeffs (hpsMul (N := 4) 5 [7, 11] [13, 17, 19]
      [⟨![3, 76, 41, 20]⟩, ⟨![55, 9, 0, 68]⟩] [⟨![38, 39, 1, 70]⟩, ⟨![12, 33, 64, 5]⟩])
#guard Fl.coeffs (Fl.poverqMul (N := 4) Fl.exactSums 5 [7, 11] [13, 17]
      [⟨![3, 76, 41, 20]⟩, ⟨![55, 9, 0, 68]⟩] [⟨![38, 39, 1, 70]⟩, ⟨![12, 33, 64, 5]⟩])
  == Fl.coeffs (poverqMul (N := 4) 5 [7, 11] [13, 17]
      [⟨![3, 76, 41, 20]⟩, ⟨![55, 9, 0, 68]⟩] [⟨![38, 39, 1, 70]⟩, ⟨![12, 33, 64, 5]⟩])
#guard Fl.coeffs (Fl.leveledMul (N := 2) Fl.exactSums 2 [11, 13, 17] [15, 16, 19] 1
      [⟨![-1485, -86]⟩, ⟨![700, 2001]⟩] [⟨![-2290, -450]⟩, ⟨![313, 1977]⟩])
  == Fl.coeffs (leveledMul (N := 2) 2 [11, 13, 17] [15, 16, 19] 1
      [⟨![-1485, -86]⟩, ⟨![700, 2001]⟩] [⟨![-2290, -450]⟩, ⟨![313, 1977]⟩])

-- The exact sums: `1/2 + 3/7 + 10/11` truncates to `1`; `1/2 + 6·3/7 + 10·5/11` to `7`.
#guard Fl.nuSw Spec.Float.exact [7, 11] [3, 10] == 1 / 2 + 3 / 7 + 10 / 11
#guard (Fl.floatSums Spec.Float.exact).sw [7, 11] [3, 10] == 1
#guard (Fl.floatSums Spec.Float.exact).sr [7, 11] [3, 5] [6, 10] == 7
#guard Fl.exactSr [7, 11] [3, 5] [6, 10] == 1 / 2 + 18 / 7 + 50 / 11
#guard floatBasisOK [1152921504606846883, 3] && !floatBasisOK [0, 5] && !floatBasisOK [2 ^ 60]
#guard floatBasisOK (List.replicate 128 7) && !floatBasisOK (List.replicate 129 7)
#guard floatAuxOK? [7, 11] [13, 17] && !floatAuxOK? [7, 11] [13, 21] && !floatAuxOK? [8, 11] [13]

/-! ## The binary64 sums are within the tolerances -/

/-- **The overflow sum of `SwitchCRTBasis`, in any conforming arithmetic, is within
`doubleSw k / 2⁵³` of `1/2 + Σ yᵢ/qᵢ`**, on a basis passing `floatBasisOK` and reduced
digits. -/
theorem nuSw_tol (A : Arith) (hA : Conforms A) (qs : List ℕ) (y : List ℤ)
    (hqs : floatBasisOK qs = true) (hy : Fl.Reduced qs y) :
    |Fl.nuSw A qs y - Fl.exactSw qs y| ≤
      (BudgetBFV.doubleSw qs.length : ℚ) / BudgetBFV.floatDen := sorry

/-- **The fractional sum of `ScaleAndRound`, in any conforming arithmetic, is within
`doubleSr ms / 2⁵³` of `1/2 + Σ xᵢ·nᵢ/mᵢ`**, on a basis passing `floatBasisOK`, reduced table
numerators and reduced residues. -/
theorem nuSr_tol (A : Arith) (hA : Conforms A) (ms : List ℕ) (ns x : List ℤ)
    (hms : floatBasisOK ms = true) (hn : Fl.Reduced ms ns) (hx : Fl.Reduced ms x) :
    |Fl.nuSr A ms ns x - Fl.exactSr ms ns x| ≤
      (BudgetBFV.doubleSr ms : ℚ) / BudgetBFV.floatDen := sorry

/-- The values the casts truncate are nonnegative and far below the range of the integer types
(`size_t` for the overflow count, 128 bits for the scaling sum). -/
theorem nu_range (A : Arith) (hA : Conforms A) (ms : List ℕ) (ns x : List ℤ)
    (hms : floatBasisOK ms = true) (hn : Fl.Reduced ms ns) (hx : Fl.Reduced ms x) :
    (0 ≤ Fl.nuSw A ms x ∧ Fl.nuSw A ms x < 2 ^ 17) ∧
    (0 ≤ Fl.nuSr A ms ns x ∧ Fl.nuSr A ms ns x < 2 ^ 81) := sorry

/-- **The table index of `SwitchCRTBasis` is in range**: `alphaQModp[static_cast<size_t>(nu)]`
(`dcrtpoly-impl.h:1089`) reads one of the `k + 1` rows of the table. -/
theorem nuSw_index (A : Arith) (hA : Conforms A) (qs : List ℕ) (y : List ℤ)
    (hqs : floatBasisOK qs = true) (hy : Fl.Reduced qs y) :
    0 ≤ ⌊Fl.nuSw A qs y⌋ ∧ ⌊Fl.nuSw A qs y⌋ ≤ (qs.length : ℤ) := sorry

/-- **The unreduced 128-bit accumulations cannot wrap**: `curValue += Mul128(x_i, c_i)` over the
input limbs, plus one more product (`dcrtpoly-impl.h:1095-1097`, `:1577-1583`), of residues and
table entries below `2⁶⁰`, over a basis passing `floatBasisOK`, stays below `2¹²⁸`. -/
theorem acc_no_overflow (ms : List ℕ) (hms : floatBasisOK ms = true) (x c : List ℕ)
    (hlen : x.length ≤ ms.length) (hx : ∀ v ∈ x, v < 2 ^ 60) (hc : ∀ v ∈ c, v < 2 ^ 60)
    (xo co : ℕ) (hxo : xo < 2 ^ 60) (hco : co < 2 ^ 60) :
    (List.zipWith (· * ·) x c).sum + xo * co < 2 ^ 128 := sorry

/-- **The library's sums are within the tolerances**, for every conforming arithmetic. -/
theorem floatSums_ok (A : Arith) (hA : Conforms A) : Fl.SumsOK (Fl.floatSums A) := sorry

/-! ## The multiplications meet the contract at the slacks with tolerances

For every `S` within the tolerances (`Fl.SumsOK`; in particular `Fl.floatSums A` for every
conforming `A`). The slack numbers are those `Challenge.CertifyBFV.slacksAt` computes with
`floatTol = true`. -/

variable (P : FullParams)

/-- **HPS multiplication with sums within the tolerances meets the `mul` contract** at the slack
`hpsSlack t N Q R (doubleSw k) (doubleSw |R|) (doubleSr qs)`. -/
theorem stepOK_mul_hps_tol (S : Fl.Sums) (hS : Fl.SumsOK S)
    (hP : SchemeParamsOK P) (E : TraceBFV.Budget)
    (s : IntPoly P.src.N) (hs : SecretOK P.secretBound s) (ρ ρ' : Env P.src)
    (σ : Trace.CtEnv P) (d a b : Var) (x y : Val P.src) (ca cb : List (IntPoly P.src.N))
    (ps : List ℕ)
    (hL : BudgetBFV.mulLiftNormAt P x.level
            (BudgetBFV.hpsSlack P.src.t P.src.N (P.src.modulus x.level) ps.prod
              (BudgetBFV.doubleSw x.level) (BudgetBFV.doubleSw ps.length)
              (BudgetBFV.doubleSr (P.src.qs.take x.level))).e ≤ E.mulLift)
    (hR : BudgetBFV.mulRoundApprox P
            (BudgetBFV.hpsSlack P.src.t P.src.N (P.src.modulus x.level) ps.prod
              (BudgetBFV.doubleSw x.level) (BudgetBFV.doubleSw ps.length)
              (BudgetBFV.doubleSr (P.src.qs.take x.level))).rho ≤ E.mulRound)
    (hok : (BudgetBFV.hpsSlack P.src.t P.src.N (P.src.modulus x.level) ps.prod
              (BudgetBFV.doubleSw x.level) (BudgetBFV.doubleSw ps.length)
              (BudgetBFV.doubleSr (P.src.qs.take x.level))).ok = true)
    (hstep : step P.src ρ (.mul d a b) = some ρ') (hx : ρ a = some x) (hy : ρ b = some y)
    (ha : σ a = some ca) (hb : σ b = some cb)
    (hla : ca.length = 2) (hlb : cb.length = 2) (h2x : x.parts = 2) (h2y : y.parts = 2)
    (hℓ : 1 ≤ x.level) (hℓL : x.level ≤ P.src.qs.length)
    (haux : floatAuxOK? (P.src.qs.take x.level) ps = true) :
    TraceBFV.StepOK P E s ρ ρ' σ
      (σ.set d (Fl.hpsMul S P.src.t (P.src.qs.take x.level) ps ca cb)) (.mul d a b) := sorry

/-- **HPS squaring with sums within the tolerances meets the `square` contract** at the same
slack. -/
theorem stepOK_square_hps_tol (S : Fl.Sums) (hS : Fl.SumsOK S)
    (hP : SchemeParamsOK P) (E : TraceBFV.Budget)
    (s : IntPoly P.src.N) (hs : SecretOK P.secretBound s) (ρ ρ' : Env P.src)
    (σ : Trace.CtEnv P) (d a : Var) (x : Val P.src) (ca : List (IntPoly P.src.N))
    (ps : List ℕ)
    (hL : BudgetBFV.mulLiftNormAt P x.level
            (BudgetBFV.hpsSlack P.src.t P.src.N (P.src.modulus x.level) ps.prod
              (BudgetBFV.doubleSw x.level) (BudgetBFV.doubleSw ps.length)
              (BudgetBFV.doubleSr (P.src.qs.take x.level))).e ≤ E.mulLift)
    (hR : BudgetBFV.mulRoundApprox P
            (BudgetBFV.hpsSlack P.src.t P.src.N (P.src.modulus x.level) ps.prod
              (BudgetBFV.doubleSw x.level) (BudgetBFV.doubleSw ps.length)
              (BudgetBFV.doubleSr (P.src.qs.take x.level))).rho ≤ E.mulRound)
    (hok : (BudgetBFV.hpsSlack P.src.t P.src.N (P.src.modulus x.level) ps.prod
              (BudgetBFV.doubleSw x.level) (BudgetBFV.doubleSw ps.length)
              (BudgetBFV.doubleSr (P.src.qs.take x.level))).ok = true)
    (hstep : step P.src ρ (.square d a) = some ρ') (hx : ρ a = some x)
    (ha : σ a = some ca) (hla : ca.length = 2) (h2x : x.parts = 2)
    (hℓ : 1 ≤ x.level) (hℓL : x.level ≤ P.src.qs.length)
    (haux : floatAuxOK? (P.src.qs.take x.level) ps = true) :
    TraceBFV.StepOK P E s ρ ρ' σ
      (σ.set d (Fl.hpsMul S P.src.t (P.src.qs.take x.level) ps ca ca)) (.square d a) := sorry

/-- **P-over-Q multiplication with sums within the tolerances meets the `mul` contract** at the
slack `poverqSlack t N Q P k (doubleSw k) (doubleSr ps)`, for an auxiliary basis of at most `k`
moduli (OpenFHE: exactly `k`). -/
theorem stepOK_mul_poverq_tol (S : Fl.Sums) (hS : Fl.SumsOK S)
    (hP : SchemeParamsOK P) (E : TraceBFV.Budget)
    (s : IntPoly P.src.N) (hs : SecretOK P.secretBound s) (ρ ρ' : Env P.src)
    (σ : Trace.CtEnv P) (d a b : Var) (x y : Val P.src) (ca cb : List (IntPoly P.src.N))
    (ps : List ℕ)
    (hL : BudgetBFV.mulLiftNormAt P x.level
            (BudgetBFV.poverqSlack P.src.t P.src.N (P.src.modulus x.level) ps.prod x.level
              (BudgetBFV.doubleSw x.level) (BudgetBFV.doubleSr ps)).e ≤ E.mulLift)
    (hR : BudgetBFV.mulRoundApprox P
            (BudgetBFV.poverqSlack P.src.t P.src.N (P.src.modulus x.level) ps.prod x.level
              (BudgetBFV.doubleSw x.level) (BudgetBFV.doubleSr ps)).rho ≤ E.mulRound)
    (hstep : step P.src ρ (.mul d a b) = some ρ') (hx : ρ a = some x) (hy : ρ b = some y)
    (ha : σ a = some ca) (hb : σ b = some cb)
    (hla : ca.length = 2) (hlb : cb.length = 2) (h2x : x.parts = 2) (h2y : y.parts = 2)
    (hℓ : 1 ≤ x.level) (hℓL : x.level ≤ P.src.qs.length) (hps : ps.length ≤ x.level)
    (haux : floatAuxOK? (P.src.qs.take x.level) ps = true) :
    TraceBFV.StepOK P E s ρ ρ' σ
      (σ.set d (Fl.poverqMul S P.src.t (P.src.qs.take x.level) ps ca cb)) (.mul d a b) := sorry

/-- **Leveled P-over-Q multiplication with sums within the tolerances meets the `mul` contract**
at the slack `leveledSlack t N Q Q_l P_l k (doubleSw k) (doubleSr (dropped limbs)) (doubleSr P_l)`,
for every number `drop` of limbs dropped internally. The flag `ok` of the slack is not needed
(nor is it for `stepOK_mul_poverq_tol`): a small auxiliary modulus makes the slack large, not the
statement false. -/
theorem stepOK_mul_leveled_tol (S : Fl.Sums) (hS : Fl.SumsOK S)
    (hP : SchemeParamsOK P) (E : TraceBFV.Budget)
    (s : IntPoly P.src.N) (hs : SecretOK P.secretBound s) (ρ ρ' : Env P.src)
    (σ : Trace.CtEnv P) (d a b : Var) (x y : Val P.src) (ca cb : List (IntPoly P.src.N))
    (ps : List ℕ) (drop : ℕ)
    (hL : BudgetBFV.mulLiftNormAt P x.level
            (BudgetBFV.leveledSlack P.src.t P.src.N (P.src.modulus x.level)
              (P.src.modulus (x.level - drop)) (ps.take (x.level - drop)).prod x.level
              (BudgetBFV.doubleSw x.level)
              (BudgetBFV.doubleSr ((P.src.qs.take x.level).drop (x.level - drop)))
              (BudgetBFV.doubleSr (ps.take (x.level - drop)))).e ≤ E.mulLift)
    (hR : BudgetBFV.mulRoundApprox P
            (BudgetBFV.leveledSlack P.src.t P.src.N (P.src.modulus x.level)
              (P.src.modulus (x.level - drop)) (ps.take (x.level - drop)).prod x.level
              (BudgetBFV.doubleSw x.level)
              (BudgetBFV.doubleSr ((P.src.qs.take x.level).drop (x.level - drop)))
              (BudgetBFV.doubleSr (ps.take (x.level - drop)))).rho ≤ E.mulRound)
    (hstep : step P.src ρ (.mul d a b) = some ρ') (hx : ρ a = some x) (hy : ρ b = some y)
    (ha : σ a = some ca) (hb : σ b = some cb)
    (hla : ca.length = 2) (hlb : cb.length = 2) (h2x : x.parts = 2) (h2y : y.parts = 2)
    (hℓ : 1 ≤ x.level) (hℓL : x.level ≤ P.src.qs.length)
    (haux : floatAuxOK? (P.src.qs.take x.level) (ps.take (x.level - drop)) = true) :
    TraceBFV.StepOK P E s ρ ρ' σ
      (σ.set d (Fl.leveledMul S P.src.t (P.src.qs.take x.level) ps drop ca cb)) (.mul d a b) :=
  sorry

/-! ## The library's multiplications, for every conforming arithmetic

The statements above at `S = Fl.floatSums A`: what `fhe_check` needs in order to certify a BFV
program under `HPS`, `HPSPOVERQ` or `HPSPOVERQLEVELED` with no assumption about the binary64
steps beyond `Spec.Float.Conforms`. -/

/-- **OpenFHE's `HPS` multiplication, computed in any conforming binary64 arithmetic, meets the
`mul` contract** at the slack with the tolerances `doubleSw`, `doubleSr`. -/
theorem stepOK_mul_hps_float (A : Arith) (hA : Conforms A)
    (hP : SchemeParamsOK P) (E : TraceBFV.Budget)
    (s : IntPoly P.src.N) (hs : SecretOK P.secretBound s) (ρ ρ' : Env P.src)
    (σ : Trace.CtEnv P) (d a b : Var) (x y : Val P.src) (ca cb : List (IntPoly P.src.N))
    (ps : List ℕ)
    (hL : BudgetBFV.mulLiftNormAt P x.level
            (BudgetBFV.hpsSlack P.src.t P.src.N (P.src.modulus x.level) ps.prod
              (BudgetBFV.doubleSw x.level) (BudgetBFV.doubleSw ps.length)
              (BudgetBFV.doubleSr (P.src.qs.take x.level))).e ≤ E.mulLift)
    (hR : BudgetBFV.mulRoundApprox P
            (BudgetBFV.hpsSlack P.src.t P.src.N (P.src.modulus x.level) ps.prod
              (BudgetBFV.doubleSw x.level) (BudgetBFV.doubleSw ps.length)
              (BudgetBFV.doubleSr (P.src.qs.take x.level))).rho ≤ E.mulRound)
    (hok : (BudgetBFV.hpsSlack P.src.t P.src.N (P.src.modulus x.level) ps.prod
              (BudgetBFV.doubleSw x.level) (BudgetBFV.doubleSw ps.length)
              (BudgetBFV.doubleSr (P.src.qs.take x.level))).ok = true)
    (hstep : step P.src ρ (.mul d a b) = some ρ') (hx : ρ a = some x) (hy : ρ b = some y)
    (ha : σ a = some ca) (hb : σ b = some cb)
    (hla : ca.length = 2) (hlb : cb.length = 2) (h2x : x.parts = 2) (h2y : y.parts = 2)
    (hℓ : 1 ≤ x.level) (hℓL : x.level ≤ P.src.qs.length)
    (haux : floatAuxOK? (P.src.qs.take x.level) ps = true) :
    TraceBFV.StepOK P E s ρ ρ' σ
      (σ.set d (Fl.hpsMul (Fl.floatSums A) P.src.t (P.src.qs.take x.level) ps ca cb))
      (.mul d a b) := sorry

/-- **OpenFHE's `HPS` squaring, computed in any conforming binary64 arithmetic, meets the
`square` contract** at the same slack. -/
theorem stepOK_square_hps_float (A : Arith) (hA : Conforms A)
    (hP : SchemeParamsOK P) (E : TraceBFV.Budget)
    (s : IntPoly P.src.N) (hs : SecretOK P.secretBound s) (ρ ρ' : Env P.src)
    (σ : Trace.CtEnv P) (d a : Var) (x : Val P.src) (ca : List (IntPoly P.src.N))
    (ps : List ℕ)
    (hL : BudgetBFV.mulLiftNormAt P x.level
            (BudgetBFV.hpsSlack P.src.t P.src.N (P.src.modulus x.level) ps.prod
              (BudgetBFV.doubleSw x.level) (BudgetBFV.doubleSw ps.length)
              (BudgetBFV.doubleSr (P.src.qs.take x.level))).e ≤ E.mulLift)
    (hR : BudgetBFV.mulRoundApprox P
            (BudgetBFV.hpsSlack P.src.t P.src.N (P.src.modulus x.level) ps.prod
              (BudgetBFV.doubleSw x.level) (BudgetBFV.doubleSw ps.length)
              (BudgetBFV.doubleSr (P.src.qs.take x.level))).rho ≤ E.mulRound)
    (hok : (BudgetBFV.hpsSlack P.src.t P.src.N (P.src.modulus x.level) ps.prod
              (BudgetBFV.doubleSw x.level) (BudgetBFV.doubleSw ps.length)
              (BudgetBFV.doubleSr (P.src.qs.take x.level))).ok = true)
    (hstep : step P.src ρ (.square d a) = some ρ') (hx : ρ a = some x)
    (ha : σ a = some ca) (hla : ca.length = 2) (h2x : x.parts = 2)
    (hℓ : 1 ≤ x.level) (hℓL : x.level ≤ P.src.qs.length)
    (haux : floatAuxOK? (P.src.qs.take x.level) ps = true) :
    TraceBFV.StepOK P E s ρ ρ' σ
      (σ.set d (Fl.hpsMul (Fl.floatSums A) P.src.t (P.src.qs.take x.level) ps ca ca))
      (.square d a) := sorry

/-- **OpenFHE's `HPSPOVERQ` multiplication (and `HPSPOVERQLEVELED` with no internal drop),
computed in any conforming binary64 arithmetic, meets the `mul` contract** at the slack with the
tolerances. -/
theorem stepOK_mul_poverq_float (A : Arith) (hA : Conforms A)
    (hP : SchemeParamsOK P) (E : TraceBFV.Budget)
    (s : IntPoly P.src.N) (hs : SecretOK P.secretBound s) (ρ ρ' : Env P.src)
    (σ : Trace.CtEnv P) (d a b : Var) (x y : Val P.src) (ca cb : List (IntPoly P.src.N))
    (ps : List ℕ)
    (hL : BudgetBFV.mulLiftNormAt P x.level
            (BudgetBFV.poverqSlack P.src.t P.src.N (P.src.modulus x.level) ps.prod x.level
              (BudgetBFV.doubleSw x.level) (BudgetBFV.doubleSr ps)).e ≤ E.mulLift)
    (hR : BudgetBFV.mulRoundApprox P
            (BudgetBFV.poverqSlack P.src.t P.src.N (P.src.modulus x.level) ps.prod x.level
              (BudgetBFV.doubleSw x.level) (BudgetBFV.doubleSr ps)).rho ≤ E.mulRound)
    (hstep : step P.src ρ (.mul d a b) = some ρ') (hx : ρ a = some x) (hy : ρ b = some y)
    (ha : σ a = some ca) (hb : σ b = some cb)
    (hla : ca.length = 2) (hlb : cb.length = 2) (h2x : x.parts = 2) (h2y : y.parts = 2)
    (hℓ : 1 ≤ x.level) (hℓL : x.level ≤ P.src.qs.length) (hps : ps.length ≤ x.level)
    (haux : floatAuxOK? (P.src.qs.take x.level) ps = true) :
    TraceBFV.StepOK P E s ρ ρ' σ
      (σ.set d (Fl.poverqMul (Fl.floatSums A) P.src.t (P.src.qs.take x.level) ps ca cb))
      (.mul d a b) := sorry

/-- **OpenFHE's `HPSPOVERQLEVELED` multiplication with an internal drop, computed in any
conforming binary64 arithmetic, meets the `mul` contract** at the slack with the tolerances. -/
theorem stepOK_mul_leveled_float (A : Arith) (hA : Conforms A)
    (hP : SchemeParamsOK P) (E : TraceBFV.Budget)
    (s : IntPoly P.src.N) (hs : SecretOK P.secretBound s) (ρ ρ' : Env P.src)
    (σ : Trace.CtEnv P) (d a b : Var) (x y : Val P.src) (ca cb : List (IntPoly P.src.N))
    (ps : List ℕ) (drop : ℕ)
    (hL : BudgetBFV.mulLiftNormAt P x.level
            (BudgetBFV.leveledSlack P.src.t P.src.N (P.src.modulus x.level)
              (P.src.modulus (x.level - drop)) (ps.take (x.level - drop)).prod x.level
              (BudgetBFV.doubleSw x.level)
              (BudgetBFV.doubleSr ((P.src.qs.take x.level).drop (x.level - drop)))
              (BudgetBFV.doubleSr (ps.take (x.level - drop)))).e ≤ E.mulLift)
    (hR : BudgetBFV.mulRoundApprox P
            (BudgetBFV.leveledSlack P.src.t P.src.N (P.src.modulus x.level)
              (P.src.modulus (x.level - drop)) (ps.take (x.level - drop)).prod x.level
              (BudgetBFV.doubleSw x.level)
              (BudgetBFV.doubleSr ((P.src.qs.take x.level).drop (x.level - drop)))
              (BudgetBFV.doubleSr (ps.take (x.level - drop)))).rho ≤ E.mulRound)
    (hstep : step P.src ρ (.mul d a b) = some ρ') (hx : ρ a = some x) (hy : ρ b = some y)
    (ha : σ a = some ca) (hb : σ b = some cb)
    (hla : ca.length = 2) (hlb : cb.length = 2) (h2x : x.parts = 2) (h2y : y.parts = 2)
    (hℓ : 1 ≤ x.level) (hℓL : x.level ≤ P.src.qs.length)
    (haux : floatAuxOK? (P.src.qs.take x.level) (ps.take (x.level - drop)) = true) :
    TraceBFV.StepOK P E s ρ ρ' σ
      (σ.set d (Fl.leveledMul (Fl.floatSums A) P.src.t (P.src.qs.take x.level) ps drop ca cb))
      (.mul d a b) := sorry

end Challenge.BFVMul
