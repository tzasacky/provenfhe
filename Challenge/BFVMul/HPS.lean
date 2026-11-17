import Challenge.BFV.Defs

/-!
# Challenge.BFVMul.HPS — BFV multiplication in RNS, Halevi–Polyakov–Shoup   (LOCKED definitions)

`Challenge.BFV.bfvMul` is the textbook multiplication: centred lift to `ℤ`, tensor product over
`ℤ[X]/(X^N+1)`, exact rounding of `t·c/Q`. No library runs it. This file defines, limb by limb,
the RNS variant of Halevi, Polyakov and Shoup ("An improved RNS variant of the BFV homomorphic
encryption scheme", ePrint 2018/117) in the form OpenFHE runs for
`MultiplicationTechnique == HPS` (`LeveledSHEBFVRNS::EvalMult`,
`src/pke/lib/scheme/bfvrns/bfvrns-leveledshe.cpp:200`; line numbers are those of upstream
OpenFHE v1.6.1, commit b59e1f29). It contains definitions only; `Challenge.BFVMul` states
that `hpsMul` meets the `mul` contract of `Spec.TraceBFV`, under `hpsAuxOK?`.

**The algorithm.** `qs = [q₁, …, q_k]` is the ciphertext basis, `Q = ∏ qᵢ`; `ps = [p₁, …, p_m]`
is the auxiliary basis (OpenFHE: `R`), `P = ∏ pⱼ`. An RNS polynomial is the list of its limbs,
one polynomial with coefficients in `[0, m)` per modulus `m`.

1. *Expand* (`HPS.expand`; `ExpandCRTBasis`, `dcrtpoly-impl.h:1112`, called at
   `bfvrns-leveledshe.cpp:226` and `:233`): every component of both operands is extended from
   `qs` to `qs ++ ps` by `HPS.switchBasis`, which computes the residues modulo each `pⱼ` of the
   centred representative of the value modulo `Q`.
2. *Tensor* (`HPS.tensor`; `bfvrns-leveledshe.cpp:351-361`): limb-wise negacyclic products in the
   basis `qs ++ ps` (OpenFHE multiplies in the evaluation representation; the model multiplies
   coefficient vectors, which is the same map on limbs).
3. *Scale and round* (`HPS.scaleRound`; `ScaleAndRound`, `dcrtpoly-impl.h:1536`, called at
   `bfvrns-leveledshe.cpp:371`): `⌊t·x/Q⌉ mod pⱼ` from the residues of `x` modulo `qs ++ ps`.
4. *Switch back* (`HPS.switchBasis`; `SwitchCRTBasis`, `dcrtpoly-impl.h:1058`, called at
   `bfvrns-leveledshe.cpp:375`): from `ps` to `qs`.

**Base switching** (`HPS.switch1`). With `yᵢ = [xᵢ·(Q/qᵢ)⁻¹]_{qᵢ} ∈ [0, qᵢ)`, the
integer `Σᵢ yᵢ·(Q/qᵢ)` is congruent to `x` modulo `Q`, and `v = ⌊1/2 + Σᵢ yᵢ/qᵢ⌋` is the number
of multiples of `Q` by which it exceeds the representative of `x` in `[-Q/2, Q/2)`. The residue
modulo `p` is `Σᵢ yᵢ·[Q/qᵢ]_p − v·[Q]_p mod p` (tables `QHatInvModq`, `QHatModp`, `alphaQModp`:
`bfvrns-cryptoparameters.cpp:189-203`, `:336-344`).

**Scaling** (`HPS.scale1`), as OpenFHE implements it. With
`θᵢ = t·P·[(QP/qᵢ)⁻¹]_{qᵢ}` and `ωⱼ = t·P·[(QP/pⱼ)⁻¹]_{pⱼ} / pⱼ` (an integer),

  `⌊t·x/Q⌉ ≡ Σᵢ xᵢ·⌊θᵢ/qᵢ⌋ + x'ⱼ·ωⱼ + ⌊1/2 + Σᵢ xᵢ·(θᵢ mod qᵢ)/qᵢ⌋   (mod pⱼ)`,

where `xᵢ` are the residues modulo `qs` and `x'ⱼ` the residue modulo `pⱼ`. The tables are
`tRSHatInvModsDivsModr` (`⌊θᵢ/qᵢ⌋ mod pⱼ` and `ωⱼ mod pⱼ`) and `tRSHatInvModsDivsFrac`
(`(θᵢ mod qᵢ)/qᵢ`): `bfvrns-cryptoparameters.cpp:282-305`.

**What is idealised.** OpenFHE computes the two rounded sums in floating point: `v` as
`static_cast<size_t>(0.5 + Σ double(yᵢ)·(1/qᵢ))` (`dcrtpoly-impl.h:1080-1089`) and the fractional
part of the scaling as `0.5 + Σ tRSHatInvModsDivsFrac[i]·double(xᵢ)` truncated
(`dcrtpoly-impl.h:1566-1574`). Here both are exact: `v = ⌊1/2 + Σ yᵢ/qᵢ⌋` and
`⌊1/2 + Σ xᵢ·(θᵢ mod qᵢ)/qᵢ⌋` over the rationals, written with the common denominator `Q` as
`Spec.Scheme.roundDiv (Σ …·(Q/qᵢ)) Q` (halves round up, as `0.5 + …` truncated does). The
library's result equals this model's whenever the floating-point error does not move a sum
across a half-integer; HPS18 analyse when that holds and what it costs when it does
not. Nothing is claimed here about the floating-
point code beyond that. Also not modelled: machine-word arithmetic (Barrett reduction, 128-bit
accumulation), the NTT, and the generic component count (the model, like `bfvMul`, multiplies
two-component ciphertexts).

**The side condition** (`hpsAuxOK?`): the moduli of `qs ++ ps` are positive and pairwise
coprime, those of `qs` are odd, and `t·N·(Q−1)² + Q < P·Q`. Oddness of `Q` makes the centred
representative unique (for even `Q` the residue `Q/2` is lifted to `−Q/2` by step 1 and to
`+Q/2` by `ZMod.valMinAbs`, and the products differ). The inequality says the scaled tensor
product fits in the centred range of `P`: the tensor of centred lifts (coefficients at most
`(Q−1)/2`) has coefficients at most `2N·((Q−1)/2)²`, so `|⌊t·T/Q⌉| ≤ t·N·(Q−1)²/(2Q) + 1/2 < P/2`.
It implies that the tensor product does not wrap modulo `Q·P` (which step 3 does not even need:
it computes `⌊t·x/Q⌉ mod P` for every representative `x` of the residues).
-/

namespace Challenge.BFVMul
open Spec NPoly Scheme

variable {N : ℕ}

namespace HPS

/-- `a⁻¹ mod m` as an integer in `[0, m)` (`0` if `a` is not invertible). -/
def invMod (a m : ℕ) : ℤ := ((a : ZMod m)⁻¹).val

/-- The limbs of an integer polynomial in the basis `ms`: coefficients reduced into `[0, m)`. -/
def toLimbs (ms : List ℕ) (a : IntPoly N) : List (IntPoly N) :=
  ms.map fun m : ℕ => ⟨fun i => a.coeff i % (m : ℤ)⟩

/-- The residues of coefficient `i`, one per limb. -/
def residues (x : List (IntPoly N)) (i : Fin N) : List ℤ := x.map (·.coeff i)

/-- `yᵢ = [xᵢ·(Q/qᵢ)⁻¹]_{qᵢ}` (`xQHatInvModq`, `dcrtpoly-impl.h:1084`). -/
def digits (qs : List ℕ) (x : List ℤ) : List ℤ :=
  List.zipWith (fun q xi => xi * invMod (qs.prod / q) q % q) qs x

/-- The overflow count `v = ⌊1/2 + Σᵢ yᵢ/qᵢ⌋`, exactly (`nu`, `dcrtpoly-impl.h:1080-1089`,
computed there in `double`). -/
def overflow (qs : List ℕ) (y : List ℤ) : ℤ :=
  roundDiv (List.zipWith (fun q yi => yi * ((qs.prod / q : ℕ) : ℤ)) qs y).sum qs.prod

/-- Exact base switch of one value: from its residues `x` modulo `qs`, the residue modulo `p` of
its representative in `[-Q/2, Q/2)`: `Σᵢ yᵢ·[Q/qᵢ]_p − v·[Q]_p mod p`
(`dcrtpoly-impl.h:1091-1105`). -/
def switch1 (qs : List ℕ) (x : List ℤ) (p : ℕ) : ℤ :=
  let y := digits qs x
  ((List.zipWith (fun q yi => yi * ((qs.prod / q % p : ℕ) : ℤ)) qs y).sum -
    overflow qs y * ((qs.prod % p : ℕ) : ℤ)) % p

/-- Exact base switch of an RNS polynomial from the basis `qs` to the basis `ps`
(`SwitchCRTBasis`, `dcrtpoly-impl.h:1058`). -/
def switchBasis (qs ps : List ℕ) (x : List (IntPoly N)) : List (IntPoly N) :=
  ps.map fun p => ⟨fun i => switch1 qs (residues x i) p⟩

/-- Base extension from `qs` to `qs ++ ps` (`ExpandCRTBasis`, `dcrtpoly-impl.h:1112`): the
limbs modulo `qs` are kept, those modulo `ps` come from `switchBasis`. -/
def expand (qs ps : List ℕ) (x : List (IntPoly N)) : List (IntPoly N) :=
  x ++ switchBasis qs ps x

/-- Limb-wise negacyclic product in the basis `ms`. -/
def mulLimbs (ms : List ℕ) (a b : List (IntPoly N)) : List (IntPoly N) :=
  List.zipWith (fun (m : ℕ) ab => ⟨fun i => (ab.1 * ab.2).coeff i % (m : ℤ)⟩) ms (a.zip b)

/-- Limb-wise sum in the basis `ms`. -/
def addLimbs (ms : List ℕ) (a b : List (IntPoly N)) : List (IntPoly N) :=
  List.zipWith (fun (m : ℕ) ab => ⟨fun i => (ab.1 + ab.2).coeff i % (m : ℤ)⟩) ms (a.zip b)

/-- Tensor product of two 2-component ciphertexts held as RNS polynomials in the basis `ms`
(`bfvrns-leveledshe.cpp:351-361`). -/
def tensor (ms : List ℕ) (c d : List (List (IntPoly N))) : List (List (IntPoly N)) :=
  match c, d with
  | [c₀, c₁], [d₀, d₁] =>
    [mulLimbs ms c₀ d₀, addLimbs ms (mulLimbs ms c₀ d₁) (mulLimbs ms c₁ d₀), mulLimbs ms c₁ d₁]
  | _, _ => []

/-- `θᵢ = t·P·[(QP/qᵢ)⁻¹]_{qᵢ}`, one per modulus of `qs`
(`tRSHatInvMods`, `bfvrns-cryptoparameters.cpp:297`). -/
def theta (t : ℕ) (qs ps : List ℕ) : List ℤ :=
  qs.map fun q => (t : ℤ) * ps.prod * invMod (qs.prod * ps.prod / q) q

/-- Scale and round one value: from its residues `xq` modulo `qs` and its residue `xp` modulo
the modulus `p` of `ps`, `⌊t·x/Q⌉ mod p` (module docstring; `dcrtpoly-impl.h:1566-1591`). The
rounded sum of fractional parts (`nu`, in `double` there) is exact here. -/
def scale1 (t : ℕ) (qs ps : List ℕ) (xq : List ℤ) (p : ℕ) (xp : ℤ) : ℤ :=
  let θq := (theta t qs ps).zip qs
  let int := (List.zipWith (fun (θ : ℤ × ℕ) xi => xi * (θ.1 / θ.2 % p)) θq xq).sum
  let frac := roundDiv
    (List.zipWith (fun (θ : ℤ × ℕ) xi => xi * (θ.1 % θ.2) * ((qs.prod / θ.2 : ℕ) : ℤ)) θq xq).sum
    qs.prod
  let ω := (t : ℤ) * ps.prod * invMod (qs.prod * ps.prod / p) p / p % p
  (int + xp * ω + frac) % p

/-- Scale and round an RNS polynomial in the basis `qs ++ ps` by `t/Q`; the result is in the
basis `ps` (`ScaleAndRound`, `dcrtpoly-impl.h:1536`). -/
def scaleRound (t : ℕ) (qs ps : List ℕ) (x : List (IntPoly N)) : List (IntPoly N) :=
  List.zipWith
    (fun p xp => ⟨fun i => scale1 t qs ps (residues (x.take qs.length) i) p (xp.coeff i)⟩)
    ps (x.drop qs.length)

/-- The integer polynomial with coefficients in `[0, Q)` whose limbs in the basis `qs` are `x`:
`Σᵢ [xᵢ·(Q/qᵢ)⁻¹]_{qᵢ}·(Q/qᵢ) mod Q`. -/
def reconstruct (qs : List ℕ) (x : List (IntPoly N)) : IntPoly N :=
  ⟨fun i => (List.zipWith (fun q yi => yi * ((qs.prod / q : ℕ) : ℤ)) qs
    (digits qs (residues x i))).sum % qs.prod⟩

end HPS

/-- **HPS multiplication** of two 2-component BFV ciphertexts at ciphertext basis `qs`, with
auxiliary basis `ps` (module docstring). The operands are integer representatives, read modulo
each `q ∈ qs`; the result is the three components, reconstructed from their final `qs`-limbs with
coefficients in `[0, Q)`. Everything in between is on limbs. -/
def hpsMul (t : ℕ) (qs ps : List ℕ) (c d : List (IntPoly N)) : List (IntPoly N) :=
  let ext := fun a : IntPoly N => HPS.expand qs ps (HPS.toLimbs qs a)
  (HPS.tensor (qs ++ ps) (c.map ext) (d.map ext)).map fun x =>
    HPS.reconstruct qs (HPS.switchBasis ps qs (HPS.scaleRound t qs ps x))

/-- The side condition on the auxiliary basis under which `hpsMul` is exact (module docstring):
all moduli positive and pairwise coprime, the ciphertext moduli odd, and
`t·N·(Q−1)² + Q < P·Q`. -/
def hpsAuxOK? (t N : ℕ) (qs ps : List ℕ) : Bool :=
  (qs ++ ps).all (fun m => decide (0 < m)) &&
  decide ((qs ++ ps).Pairwise Nat.Coprime) &&
  qs.all (fun q => decide (q % 2 = 1)) &&
  decide (t * N * (qs.prod - 1) * (qs.prod - 1) + qs.prod < ps.prod * qs.prod)

/-! ## Checks at tiny parameters

`N = 4`, `t = 5`, `qs = [7, 11]` (`Q = 77`). With `ps = [13, 17, 19]` the side condition holds
and `hpsMul` agrees with the textbook `bfvMul` modulo `Q`; with `ps = [13, 17]` (too small) or
with an even ciphertext modulus it is rejected, and the result is wrong on the same inputs. -/

#guard hpsAuxOK? 5 4 [7, 11] [13, 17, 19]

#guard
  let c : List (IntPoly 4) := [⟨![3, 76, 41, 20]⟩, ⟨![55, 9, 0, 68]⟩]
  let d : List (IntPoly 4) := [⟨![38, 39, 1, 70]⟩, ⟨![12, 33, 64, 5]⟩]
  let coeffs := fun (x : List (IntPoly 4)) =>
    x.map fun a => (List.finRange 4).map fun i => a.coeff i % 77
  coeffs (hpsMul 5 [7, 11] [13, 17, 19] c d) = coeffs (Challenge.BFV.bfvMul 5 77 c d) &&
  coeffs (hpsMul 5 [7, 11] [13, 17, 19] c c) = coeffs (Challenge.BFV.bfvMul 5 77 c c)

#guard !hpsAuxOK? 5 4 [7, 11] [13, 17]

#guard
  let c : List (IntPoly 4) := [⟨![3, 76, 41, 20]⟩, ⟨![55, 9, 0, 68]⟩]
  let d : List (IntPoly 4) := [⟨![38, 39, 1, 70]⟩, ⟨![12, 33, 64, 5]⟩]
  let coeffs := fun (x : List (IntPoly 4)) =>
    x.map fun a => (List.finRange 4).map fun i => a.coeff i % 77
  coeffs (hpsMul 5 [7, 11] [13, 17] c d) != coeffs (Challenge.BFV.bfvMul 5 77 c d)

#guard !hpsAuxOK? 5 4 [8, 11] [13, 17, 19, 23]

#guard
  let c : List (IntPoly 4) := [⟨![44, 0, 0, 0]⟩, ⟨![0, 0, 0, 0]⟩]
  let d : List (IntPoly 4) := [⟨![1, 0, 0, 0]⟩, ⟨![0, 0, 0, 0]⟩]
  let coeffs := fun (x : List (IntPoly 4)) =>
    x.map fun a => (List.finRange 4).map fun i => a.coeff i % 88
  coeffs (hpsMul 5 [8, 11] [13, 17, 19, 23] c d) != coeffs (Challenge.BFV.bfvMul 5 88 c d)

end Challenge.BFVMul
