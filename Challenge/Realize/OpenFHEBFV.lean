import Challenge.Realize.OpenFHE
import Spec.BudgetBFV

/-!
# Challenge.Realize.OpenFHEBFV — OpenFHE's BFV key switching, relinearization and rotation   (LOCKED definitions)

A transcription, on integer representatives, of the BFV key switching of upstream OpenFHE v1.6.1
(commit b59e1f29; line numbers below are of that commit), default CMake options (no
`WITH_REDUCED_NOISE`). `Challenge.RealizeBFV` states that it meets the contracts of
`Spec.TraceBFV` at `Spec.BudgetBFV.ksBoundAt` and at the budget of a certificate. These are
definitions only.

**BFV runs the same key-switching code as BGV.** `LeveledSHEBFVRNS::RelinearizeCore`
(`pke/lib/scheme/bfvrns/bfvrns-leveledshe.cpp:856-900`) and `EvalAutomorphism` (`:744-757`) call
`algo->KeySwitchCore`, i.e. `KeySwitchHYBRID::KeySwitchCore` or `KeySwitchBV::KeySwitchCore`
(`pke/lib/keyswitch/keyswitch-hybrid.cpp:295-298`, `keyswitch-bv.cpp:236-240`), the functions BGV
uses. The only BFV-specific point is the plaintext modulus handed to `ApproxModDown`:
`t = (GetNoiseScale() == 1) ? 0 : GetPlaintextModulus()` (`keyswitch-hybrid.cpp:373`), and BFV's
noise scale is `1`, so `t = 0`: `ApproxModDown` (`core/include/lattice/hal/default/dcrtpoly-impl.h:1020-1055`)
skips both multiplications by `t⁻¹` and `t` (`if (t > 0)`, `:1036`, `:1049`) and returns
`(X − FastBConv([X]_P)) · P⁻¹`. That is exactly the BGV ModDown of `Challenge.Realize.OpenFHE`
(`modDownBGV`: `(X − t·fbc([X·t⁻¹]_p))/P`) at plaintext modulus `1`. So:

* **HYBRID** (`ksHybrid`): `Challenge.Realize.ksOpenFHE` at `Spec.BudgetBFV.unitPlain P` (the
  parameters with `t := 1`), literally the BGV transcription: canonical ModUp (`ApproxSwitchCRTBasis`,
  representatives in `[0, qᵢ)`), inner products with the stored keys over `Q_ℓ·P`, ModDown. Nothing
  is duplicated.
* **BV with digit size 0** (`ksBV`, `KeySwitchBV`, `keyswitch-bv.cpp:236-330`): the digits are
  `CRTDecompose(0)` (`dcrtpoly-impl.h:249-273`): digit `i` is the residue `[c]_{qᵢ}`, extended to
  the other limbs by `NativeVectorT(v, modulus)` (`core/lib/math/hal/intnat/mubintvecnat.cpp:192-215`),
  which maps a value `v > ⌊qᵢ/2⌋` to `v − qᵢ`: the **centred** representative (`crtDigit`). The
  result is `Σᵢ digitᵢ·(bᵢ, aᵢ)` over the ciphertext's limbs (`EvalFastKeySwitchCore`,
  `:257-330`, which reads the first `ℓ` keys and their first `ℓ` limbs); there is no special modulus
  and no ModDown. Key `i` holds `sOld` on limb `i` and `0` elsewhere (`:93-103`): the gadget entry
  `(Q/qᵢ)·[(Q/qᵢ)⁻¹]_{qᵢ}` of `Spec.Budget.gadgetFactor` with `P = 1` and one limb per digit.
  Digit size `> 0` (base-`2^w` digits) is not transcribed (the frontend refuses it).
* `ksBFV` chooses between them as the library's parameters do: HYBRID needs special primes (the
  OpenFHE frontend refuses HYBRID without them), BV has none. `ksDeclOK?` is the condition under
  which the declared layout is the one the library uses: canonical representatives for HYBRID
  (`lay.canonical = true`, the default build), one limb per digit for BV.

**Relinearization** (`relinBFV`; `RelinearizeCore` on three components, `:891-899`):
`[c₀ + KS(c₂)₀, c₁ + KS(c₂)₁]`. **Key switch of a two-component ciphertext** (`keySwitchBFV`;
`RelinearizeCore` on two components): `[c₀ + KS(c₁)₀, KS(c₁)₁]`. **Rotation** (`EvalAutomorphism`,
`:744-757`): `RelinearizeCore` with the key stored for the automorphism index `g`, *then* the
automorphism `σ_g` of both components: `(keySwitchBFV …).map (automorph g)`. This is the order of
OpenFHE v1.3.1's BGV rotation (`FHE.KeySwitch.Order`), not of v1.6.1's BGV rotation
(`Challenge.Realize.rotateOpenFHE161`, which applies `σ_g` before ModDown): BFV kept it.

Under `HPSPOVERQLEVELED` at the top level the library scales the switched component down first
and back up after; that is `Challenge.BFVMul.Fl.leveledKS` with `ksBFV` at the reduced level as
its `core` (`Challenge.RealizeBFV`, `Challenge.CertifyBFV.Library`).

Inputs of other shapes give the empty list.
-/

namespace Challenge.RealizeBFV
open Spec NPoly Spec.Budget Challenge.Realize

/-- **HYBRID key switching of one component, BFV** (`KeySwitchHYBRID` with `t = 0` in
`ApproxModDown`): the BGV transcription `Challenge.Realize.ksOpenFHE` at plaintext modulus `1`. -/
def ksHybrid (P : FullParams) (lay : KSLayout) (ℓ : ℕ) (d : IntPoly P.src.N)
    (keys : List (IntPoly P.src.N × IntPoly P.src.N)) : IntPoly P.src.N × IntPoly P.src.N :=
  ksOpenFHE (BudgetBFV.unitPlain P) lay ℓ d keys

/-- The centred residue of every coefficient modulo `q`: digit `i` of `CRTDecompose(0)`. -/
def crtDigit {N : ℕ} (q : ℕ) (d : IntPoly N) : IntPoly N :=
  ⟨fun c => ((d.coeff c : ZMod q)).valMinAbs⟩

/-- **BV key switching of one component, digit size 0** (`KeySwitchBV`): at level `ℓ`,
`(Σᵢ crtDigit qᵢ d · bᵢ, Σᵢ crtDigit qᵢ d · aᵢ)` over the first `ℓ` limbs and keys (missing keys
read as zero). -/
def ksBV (P : FullParams) (ℓ : ℕ) (d : IntPoly P.src.N)
    (keys : List (IntPoly P.src.N × IntPoly P.src.N)) : IntPoly P.src.N × IntPoly P.src.N :=
  ((List.ofFn fun i : Fin ℓ => crtDigit (P.src.qs.getD i 0) d * (keys.getD i (0, 0)).1).sum,
   (List.ofFn fun i : Fin ℓ => crtDigit (P.src.qs.getD i 0) d * (keys.getD i (0, 0)).2).sum)

/-- **OpenFHE's BFV key switching of one component** at level `ℓ`: BV without special primes,
HYBRID with them. -/
def ksBFV (P : FullParams) (lay : KSLayout) (ℓ : ℕ) (d : IntPoly P.src.N)
    (keys : List (IntPoly P.src.N × IntPoly P.src.N)) : IntPoly P.src.N × IntPoly P.src.N :=
  if P.store.special = [] then ksBV P ℓ d keys else ksHybrid P lay ℓ d keys

/-- **The declared layout is the library's**: with special primes (HYBRID), canonical
representatives (the default build); without (BV, digit size 0), one limb per digit at every level
of the chain. -/
def ksDeclOK? (P : FullParams) (lay : KSLayout) : Bool :=
  if P.store.special = [] then
    (List.range P.src.qs.length).all fun i => lay.sizes (i + 1) == List.replicate (i + 1) 1
  else lay.canonical

/-- **OpenFHE's BFV relinearization** at level `ℓ`: `[c₀ + KS(c₂)₀, c₁ + KS(c₂)₁]`. -/
def relinBFV (P : FullParams) (lay : KSLayout) (ℓ : ℕ) (ca : List (IntPoly P.src.N))
    (keys : List (IntPoly P.src.N × IntPoly P.src.N)) : List (IntPoly P.src.N) :=
  match ca with
  | [c0, c1, c2] => [c0 + (ksBFV P lay ℓ c2 keys).1, c1 + (ksBFV P lay ℓ c2 keys).2]
  | _ => []

/-- **OpenFHE's BFV key switch of a two-component ciphertext** at level `ℓ`:
`[c₀ + KS(c₁)₀, KS(c₁)₁]`. -/
def keySwitchBFV (P : FullParams) (lay : KSLayout) (ℓ : ℕ) (ca : List (IntPoly P.src.N))
    (keys : List (IntPoly P.src.N × IntPoly P.src.N)) : List (IntPoly P.src.N) :=
  match ca with
  | [c0, c1] => [c0 + (ksBFV P lay ℓ c1 keys).1, (ksBFV P lay ℓ c1 keys).2]
  | _ => []

/-- **OpenFHE's BFV rotation** by `g` at level `ℓ`, with the keys stored for `g`: the key switch,
then `σ_g` of both components (`EvalAutomorphism`). -/
def rotateBFV (P : FullParams) (lay : KSLayout) (ℓ g : ℕ) (ca : List (IntPoly P.src.N))
    (keys : List (IntPoly P.src.N × IntPoly P.src.N)) : List (IntPoly P.src.N) :=
  (keySwitchBFV P lay ℓ ca keys).map (automorph g)

-- The centred digit: `9 ≡ −2 (mod 11)`, `5` stays.
#guard (crtDigit (N := 2) 11 ⟨![9, 5]⟩).coeff 0 == -2 &&
  (crtDigit (N := 2) 11 ⟨![9, 5]⟩).coeff 1 == 5

end Challenge.RealizeBFV
