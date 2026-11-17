import Validation.BFVDecryptBEHZ.Main

/-!
# Validation.BFVDecryptBEHZ — proofs of the statements of `Challenge.BFVDecryptBEHZ`

* `Validation/BFVDecryptBEHZ/Shoup.lean`: `ModMulFastConst` with the signed fix-up
  (`modMulFastConst_spec`).
* `Main.lean`: the accumulation, the CRT, the rounding by `γ` (`behz1_exact`), the margin, the
  polynomial, the pins.
-/

namespace Validation.BFVDecryptBEHZ

example := (@modMulFastConst_spec : type_of% @Challenge.BFVDecryptBEHZ.modMulFastConst_spec)
example := (@behz1_exact : type_of% @Challenge.BFVDecryptBEHZ.behz1_exact)
example := (@behz1_correct : type_of% @Challenge.BFVDecryptBEHZ.behz1_correct)
example := (@bfvDecryptBEHZ_correct : type_of% @Challenge.BFVDecryptBEHZ.bfvDecryptBEHZ_correct)
example := (@behzParamsOK?_t_lt : type_of% @Challenge.BFVDecryptBEHZ.behzParamsOK?_t_lt)
example := (@behzMargin_needed : type_of% @Challenge.BFVDecryptBEHZ.behzMargin_needed)

end Validation.BFVDecryptBEHZ
