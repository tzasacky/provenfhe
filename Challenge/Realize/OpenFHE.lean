import Spec.Budget

/-!
# Challenge.Realize.OpenFHE — OpenFHE's BGV key switching, relinearization and v1.6.1 rotation   (LOCKED definitions)

A transcription, on integer representatives and using only trusted primitives (`Spec.Ring`,
`Spec.Budget`), of the BGV operations of upstream OpenFHE v1.6.1 (commit b59e1f29; line numbers
below are of that commit) that involve key switching, for a build with the default CMake options
(no `WITH_REDUCED_NOISE`: canonical representatives, `Spec.Budget.KSLayout.canonical = true`).
`Challenge.Realize` states that they meet the contracts of `Spec.Trace` at the budget
`Spec.Budget.ksBoundAt` (canonical) and at the certified budget of a certificate. These are
definitions only.

**How this is tied to OpenFHE.** Not by a theorem about OpenFHE's code. The conformance harness
(`harness/openfhe-pin/algo/`) runs the untrusted Lean functions `FHE.Pin.Algo.relinOpenFHE`
(`c + FHE.KeySwitch.keySwitchBGVOpenFHE`) and `FHE.Pin.Algo.rotateOpenFHE161` on the exact inputs
of every relinearization and rotation of recorded OpenFHE v1.6.1 runs and finds their RNS limbs
equal to OpenFHE's, bit for bit (`algo.relin`, `algo.rotate`). The functions below are proved
equal to those, limb for limb (the RNS limbs of the output here are the limbs those functions
return on the RNS limbs of the input; keys read as their residues modulo `Q_ℓ·P`):
`FHE.Realize.ksOpenFHE_toRNS` (the core, = `keySwitchBGVOpenFHE`), `FHE.Realize.relinOpenFHE_toRNS`,
`FHE.Realize.rotateOpenFHE161_toRNS` (kernel-checked, axiom-scanned and kernel-replayed by the
gate with the rest of `FHE`, not locked). The parameters of that equality are the bases built
from `P` (`SchemeParamsOK`, `SpecialOK`) and the digits `lay.sizes ℓ`. `keySwitchOpenFHE` (a key
switch of a two-component ciphertext on its own) has no separate harness check; its core is the
one `algo.relin` compares.

**The algorithm** (`KeySwitchHYBRID`, `keyswitch/keyswitch-hybrid.cpp`; `ApproxSwitchCRTBasis`,
`dcrtpoly-impl.h:938-977`; `ApproxModDown`). At level `ℓ` the limbs `q₀ … q_{ℓ−1}` of the chain
are split into consecutive digits (`lay.sizes ℓ`); `ps` are the special moduli, `P` their product.

1. *ModUp* of digit `j` (`modUpDigit`): the integer `Dⱼ = Σᵣ [d·(Qⱼ/qᵣ)⁻¹]_{qᵣ} · (Qⱼ/qᵣ)` over
   the limbs `qᵣ` of the digit (`Qⱼ` their product), with `[·]` the representative in `[0, qᵣ)`
   (`fbc`). Its residues modulo the digit's own limbs are those of `d` (OpenFHE copies them); its
   residues modulo the other limbs and the special moduli are OpenFHE's fast base conversion.
   `Dⱼ ≡ d (mod Qⱼ)` and `0 ≤ Dⱼ ≤ ℓⱼ·(Qⱼ − 1)`: not centred, which is what costs the factor two
   in the canonical bound.
2. *Inner products* over `Q_ℓ·P` (`innerKey`): `Σⱼ Dⱼ·bⱼ` and `Σⱼ Dⱼ·aⱼ`, `(bⱼ, aⱼ)` the stored
   key of digit `j` (any integer representatives: only their residues modulo `Q_ℓ·P` matter).
3. *ModDown* by `P`, BGV form (`modDownBGV`): `(X − t·F) / P` with
   `F = fbc ps ([X·t⁻¹]_{p})`, an exact division (`X − t·F ≡ 0 (mod p)` for every special
   modulus `p`). OpenFHE computes it limb by limb as `(X − t·F)·P⁻¹ mod qᵢ`.

**Relinearization** (`relinOpenFHE`; `LeveledSHEBase::RelinearizeInPlace`,
`base-leveledshe.cpp:362-380`, and `EvalMult(ct, ct, key)`, `:232-247`, on a three-component
product): `[c₀ + KS(c₂)₀, c₁ + KS(c₂)₁]`. **Key switching** (`keySwitchOpenFHE`;
`KeySwitchInPlace` on two components): `[c₀ + KS(c₁)₀, KS(c₁)₁]`. **Rotation, v1.6.1**
(`rotateOpenFHE161`; `EvalAutomorphism` → `EvalAutomorphismCore`, `base-leveledshe.cpp:455-506`,
HYBRID branch with `EvalFastKeySwitchCoreExt`, `keyswitch-hybrid.cpp:389-421`): ModUp of `c₁`, the
inner products with the key stored for `g` over `Q_ℓ·P`, `P·c₀` added to the first, **the
automorphism `σ_g` applied over `Q_ℓ·P`**, then ModDown. This is not the key switch followed by
`σ_g` (OpenFHE v1.3.1's order): with canonical representatives ModDown does not commute with `σ_g`
and the two differ by multiples of `t` (`harness/openfhe-pin/algo/README.md`).

Inputs of other shapes (a relinearization operand without exactly three components, a key switch
or rotation operand without exactly two) give the empty list: the statements are about the shapes
`Spec.Source.step` accepts.
-/

namespace Challenge.Realize
open Spec NPoly Spec.Budget

/-- **Canonical fast base conversion** from the moduli `ms`, as an integer:
`Σᵢ [xᵢ · (M/mᵢ)⁻¹]_{mᵢ} · (M/mᵢ)` with `M = ∏ ms`, `M/mᵢ` the product of the other moduli and
`[·]_{mᵢ}` the representative in `[0, mᵢ)`. `x m` is the residue modulo `m` of the value being
converted. The result is congruent to that value modulo `M` and lies in `[0, |ms|·(M − 1)]`. -/
def fbc (ms : List ℕ) (x : (m : ℕ) → ZMod m) : ℤ :=
  ∑ i : Fin ms.length,
    ((x ms[i] * (((ms.eraseIdx i).prod : ℕ) : ZMod ms[i])⁻¹).val : ℤ) * ((ms.eraseIdx i).prod : ℕ)

/-- The limbs of digit `j` at level `ℓ`: `(lay.sizes ℓ)[j]` consecutive limbs of the chain,
starting after those of the digits before it (their product is `Spec.Budget.digitModulus`). -/
def digitMods (P : FullParams) (lay : KSLayout) (ℓ j : ℕ) : List ℕ :=
  ((P.src.qs.take ℓ).drop ((lay.sizes ℓ).take j).sum).take ((lay.sizes ℓ).getD j 0)

/-- The special moduli (their product is `Spec.Budget.specialProd P`). -/
def specialMods (P : FullParams) : List ℕ := P.store.special.map (·.q)

/-- **ModUp** of digit `j` of `d`, canonical: `Dⱼ` coefficient by coefficient. -/
def modUpDigit (P : FullParams) (lay : KSLayout) (ℓ : ℕ) (d : IntPoly P.src.N) (j : ℕ) :
    IntPoly P.src.N :=
  ⟨fun c => fbc (digitMods P lay ℓ j) (fun m => (d.coeff c : ZMod m))⟩

/-- **The inner product** `Σⱼ Dⱼ · kⱼ` of the ModUp digits of `d` with the key components `kⱼ`,
over the digits of level `ℓ`. -/
def innerKey (P : FullParams) (lay : KSLayout) (ℓ : ℕ) (d : IntPoly P.src.N)
    (k : ℕ → IntPoly P.src.N) : IntPoly P.src.N :=
  (List.ofFn fun j : Fin (lay.sizes ℓ).length => modUpDigit P lay ℓ d j * k j).sum

/-- **BGV ModDown** by the special modulus `P`, OpenFHE's form: `(X − t·F) / P` with
`F = fbc ps ([X·t⁻¹]_p)`, coefficient by coefficient. -/
def modDownBGV (P : FullParams) (X : IntPoly P.src.N) : IntPoly P.src.N :=
  ⟨fun c => (X.coeff c - (P.src.t : ℤ) *
      fbc (specialMods P) (fun p => (X.coeff c : ZMod p) * (P.src.t : ZMod p)⁻¹)) /
    (specialProd P : ℤ)⟩

/-- **Hybrid key switching of one component**, OpenFHE's canonical form: `(KS(d)₀, KS(d)₁)`, with
the stored keys `(bⱼ, aⱼ)` (missing ones read as zero). -/
def ksOpenFHE (P : FullParams) (lay : KSLayout) (ℓ : ℕ) (d : IntPoly P.src.N)
    (keys : List (IntPoly P.src.N × IntPoly P.src.N)) : IntPoly P.src.N × IntPoly P.src.N :=
  (modDownBGV P (innerKey P lay ℓ d fun j => (keys.getD j (0, 0)).1),
   modDownBGV P (innerKey P lay ℓ d fun j => (keys.getD j (0, 0)).2))

/-- **OpenFHE's relinearization** of a three-component ciphertext at level `ℓ`:
`[c₀ + KS(c₂)₀, c₁ + KS(c₂)₁]`. -/
def relinOpenFHE (P : FullParams) (lay : KSLayout) (ℓ : ℕ) (ca : List (IntPoly P.src.N))
    (keys : List (IntPoly P.src.N × IntPoly P.src.N)) : List (IntPoly P.src.N) :=
  match ca with
  | [c0, c1, c2] => [c0 + (ksOpenFHE P lay ℓ c2 keys).1, c1 + (ksOpenFHE P lay ℓ c2 keys).2]
  | _ => []

/-- **OpenFHE's key switch** of a two-component ciphertext at level `ℓ`:
`[c₀ + KS(c₁)₀, KS(c₁)₁]`. -/
def keySwitchOpenFHE (P : FullParams) (lay : KSLayout) (ℓ : ℕ) (ca : List (IntPoly P.src.N))
    (keys : List (IntPoly P.src.N × IntPoly P.src.N)) : List (IntPoly P.src.N) :=
  match ca with
  | [c0, c1] => [c0 + (ksOpenFHE P lay ℓ c1 keys).1, (ksOpenFHE P lay ℓ c1 keys).2]
  | _ => []

/-- **OpenFHE v1.6.1's rotation** by `g` of a two-component ciphertext at level `ℓ`, with the
keys stored for `g`: `[ModDown(σ_g(P·c₀ + Σⱼ Dⱼ(c₁)·bⱼ)), ModDown(σ_g(Σⱼ Dⱼ(c₁)·aⱼ))]`. -/
def rotateOpenFHE161 (P : FullParams) (lay : KSLayout) (ℓ g : ℕ) (ca : List (IntPoly P.src.N))
    (keys : List (IntPoly P.src.N × IntPoly P.src.N)) : List (IntPoly P.src.N) :=
  match ca with
  | [c0, c1] =>
    [modDownBGV P (automorph g (((specialProd P : ℕ) : ℤ) • c0 +
        innerKey P lay ℓ c1 fun j => (keys.getD j (0, 0)).1)),
     modDownBGV P (automorph g (innerKey P lay ℓ c1 fun j => (keys.getD j (0, 0)).2))]
  | _ => []

-- `fbc` is a lift of the residues, with the canonical overflow: `1 ≡ 36 (mod 35)`.
#guard fbc [5, 7] (fun m => (12 : ZMod m)) == 12
#guard fbc [5, 7] (fun m => (1 : ZMod m)) == 36
#guard digitMods .exampleBGV31 (uniformLayout 1) 2 1 == [1074266113]
#guard (digitMods .exampleBGV31 (uniformLayout 2) 2 0).prod ==
  digitModulus .exampleBGV31 (uniformLayout 2) 2 0

end Challenge.Realize
