import Challenge.BFVMul.BEHZWord
import FHE.BFV.MulBEHZWord

/-!
# Validation.BFVMul.BEHZWord — the Shenoy–Kumaresan correction of BEHZ is at least `−q`

Proofs of the statements of `Challenge.BFVMul.BEHZWord`: `sk1_alpha` by unfolding, and
`behz_sk_alpha_ge` from `FHE.BFV.MulBEHZ.behz_sk_alpha_ge'` (the fast floor of the tensor product
of the lifts has `|F| ≤ q·B` under `behzWordOK?`, Shenoy–Kumaresan is exact under `behzAuxOK?`,
and `B·α = Σⱼ zⱼ·B̂ⱼ − F ≥ −F`).
-/

namespace Validation.BFVMul
open Spec NPoly Scheme Challenge.BFVMul

variable {N : ℕ}

theorem sk1_alpha (bs : List ℕ) (msk : ℕ) (xb : List ℤ) (xsk : ℤ) (q : ℕ) :
    BEHZ.sk1 bs msk xb xsk q =
      (BEHZ.convSum bs (HPS.digits bs xb) q - BEHZ.skAlpha1 bs msk xb xsk * ((bs.prod % q : ℕ) : ℤ))
        % q := rfl

theorem behz_sk_alpha_ge (t : ℕ) (qs bs : List ℕ) (msk mt : ℕ)
    (haux : behzAuxOK? t N qs bs msk mt = true) (hword : behzWordOK? t N qs bs msk mt = true)
    (c d : List (IntPoly N)) (hc : c.length = 2) (hd : d.length = 2) :
    ∀ x ∈ HPS.tensor (qs ++ (bs ++ [msk]))
        (c.map fun a => BEHZ.extend qs (bs ++ [msk]) mt (HPS.toLimbs qs a))
        (d.map fun a => BEHZ.extend qs (bs ++ [msk]) mt (HPS.toLimbs qs a)),
      ∀ (i : Fin N), ∀ q ∈ qs,
        -(q : ℤ) ≤ BEHZ.skAlpha1 bs msk
          (HPS.residues ((BEHZ.floorq t qs (bs ++ [msk]) x).take bs.length) i)
          (((BEHZ.floorq t qs (bs ++ [msk]) x).getD bs.length 0).coeff i) :=
  FHE.BFV.MulBEHZ.behz_sk_alpha_ge' t qs bs msk mt haux hword c d hc hd

end Validation.BFVMul
