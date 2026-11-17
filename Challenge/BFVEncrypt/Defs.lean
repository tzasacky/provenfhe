import Spec.EncryptBFV
import Challenge.CertifyBFV.Defs

/-!
# Challenge.BFVEncrypt.Defs — a BFV certificate whose input noise is computed   (LOCKED definitions)

`Challenge.CertifyBFV.certifyBFV?` analyses a program at the input noise `x.P.inputNoise`, a number
it is given. `certifyBFVFresh?` computes that number from the bounds of the key and of the
encryption randomness, for inputs that are fresh OpenFHE encryptions
(`Spec.EncryptBFV.encryptBFV`), and then runs `certifyBFV?` at the parameters with the input noise
**replaced** (the declared `x.P.inputNoise` is not used):

1. the mode gives the error bound `ε` of every fresh encryption: `worstError` (mode `worst`);
   `Spec.Certify.freshEps` (mode `kappa`: `epsFor (varProxy …) (n·2N) κ + meanDrift …`, or the
   worst case if that is not larger), after checking that the variance proxy and the denominator of
   the mean bound are positive; `epsFor (varProxyL2 …) (n·2N) κ + meanDrift (E2 + 1 + S2) …` (mode
   `kappaL2`), after the same checks. `n` is the number of fresh inputs (`fresh.length`);
2. the analysed parameters are `x.P` with `inputNoise := freshInputNoise x.P x.prog fresh ε`
   (`ε` plus the largest encoding deviation `encodeDev` over the levels of the fresh inputs);
3. `Spec.EncryptBFV.freshOKBFV?` holds of the inputs;
4. `certifyBFV?` accepts at the analysed parameters (every check of `Challenge.CertifyBFV.Defs`,
   including that the analysed input noise decrypts at every input's level, `decOK`).

The statements are in `Challenge.BFVEncrypt`. `certifyBFV?` itself is unchanged: this function
checks more (it replaces a declared number by a computed one and adds `freshOKBFV?`), and every
statement about `certifyBFV?` applies to its certificate at the analysed parameters.
-/

namespace Challenge.BFVEncrypt
open Spec Spec.Source Spec.Encrypt Spec.EncryptBFV Spec.CertifyBFV Challenge.CertifyBFV

/-- The last three steps (module docstring), at the error bound `ε`. -/
def certifyAt? (x : InputBFV) (fresh : List Var) (ε : ℕ) (used : Certify.NoiseUsed) (drift : ℕ) :
    Option FreshCertBFV := do
  let P' : FullParams := { x.P with inputNoise := freshInputNoise x.P x.prog fresh ε }
  guard (freshOKBFV? x.prog fresh)
  let c ← certifyBFV? { x with P := P' }
  pure ⟨P', c, used, ε, drift⟩

/-- **The decision** (module docstring). -/
def certifyBFVFresh? (x : InputBFV) : FreshModeBFV → Option FreshCertBFV
  | .worst fresh Bk Bu B1 B2 =>
    certifyAt? x fresh (worstError x.P.src.N x.P.secretBound Bk Bu B1 B2) .freshWorst 0
  | .kappa fresh Bk Bu B1 B2 mn md κ => do
    guard (0 < varProxy x.P.src.N x.P.secretBound Bk Bu B1 B2)
    guard (0 < md)
    let (ε, used, drift) := Certify.freshEps x.P fresh.length Bk Bu B1 B2 mn md κ
    certifyAt? x fresh ε used drift
  | .kappaL2 fresh E2 S2 Vu V1 V2 mn md κ => do
    guard (0 < varProxyL2 E2 S2 Vu V1 V2)
    guard (0 < md)
    let drift := meanDrift (E2 + 1 + S2) mn md
    let ε := epsFor (varProxyL2 E2 S2 Vu V1 V2) (fresh.length * (2 * x.P.src.N)) κ + drift
    certifyAt? x fresh ε .freshKappaL2 drift

end Challenge.BFVEncrypt
