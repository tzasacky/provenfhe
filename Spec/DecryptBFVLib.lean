import Spec.DecryptBFV
import Spec.DecryptBFVLow
import Spec.DecryptBFVBEHZ

/-!
# Spec.DecryptBFVLib — which decryption routine OpenFHE runs   (TRUSTED)

`PKEBFVRNS::Decrypt` (OpenFHE v1.6.1, `src/pke/lib/scheme/bfvrns/bfvrns-pke.cpp:225-278`) chooses
its routine from the number of limbs of the ciphertext and the multiplication technique:

* all `sizeQ` limbs (`:238`), technique `HPS`, `HPSPOVERQ` or `HPSPOVERQLEVELED` (`:240-248`): the
  binary64 `ScaleAndRound(t, …)` (`Spec.DecryptBFV.bfvDecryptLib`);
* all limbs, any other technique, i.e. `BEHZ` (`:249-252`): the integer
  `ScaleAndRound(moduliQ, t, tgamma, …)` (`Spec.DecryptBFVBEHZ.bfvDecryptBEHZ`);
* fewer limbs (`:254-275`), every technique: the limb drops and the binary64 rounding
  (`Spec.DecryptBFVLow.bfvDecryptLow`; under `BEHZ` it is meant for ciphertexts of one limb only:
  `Spec.DecryptBFVLow` docstring).

`bfvDecryptOpenFHE` is that dispatch, on a ciphertext given by integer representatives `ct` at
level `ℓ` (limbs `qs.take ℓ`); `behz` says whether the technique is `BEHZ`.
-/

namespace Spec.DecryptBFVLib
open Spec.Float Spec.DecryptBFV Spec.DecryptBFVLow Spec.DecryptBFVBEHZ Spec.Scheme NPoly

/-- **The library's BFV decryption** (`bfvrns-pke.cpp:225-278`) of the integer ciphertext `ct` at
level `ℓ` under `s`: the native coefficients of the returned `NativePoly`. -/
def bfvDecryptOpenFHE (A : ArithD) (behz : Bool) (t : ℕ) (qs : List ℕ) (ℓ : ℕ) {N : ℕ}
    (s : IntPoly N) (ct : List (IntPoly N)) : NPoly ℕ N :=
  if ℓ = qs.length then
    if behz then bfvDecryptBEHZ t qs s (ct.map (ofInt qs.prod))
    else bfvDecryptLib A t qs s (ct.map (ofInt qs.prod))
  else bfvDecryptLow A t qs ℓ s (ct.map (ofInt (qs.take ℓ).prod))

end Spec.DecryptBFVLib
