import Validation.BFVDecryptLow.Main

/-!
# Validation.BFVDecryptLow — proofs of the statements of `Challenge.BFVDecryptLow`

* `Validation/BFVDecryptLow/Words.lean`: the lanes, the Barrett loop, the modulus switch
  (`switchModulus_spec`).
* `Drop.lean`: the drops (`dropAll_spec`, `dropAll_noise`).
* `Float.lean`: the binary64 step (`multiplyAndRound_err`).
* `Main.lean`: the rounding step, one coefficient, the polynomial, the pins.
-/

namespace Validation.BFVDecryptLow

example := (@switchModulus_spec : type_of% @Challenge.BFVDecryptLow.switchModulus_spec)
example := (@dropAll_spec : type_of% @Challenge.BFVDecryptLow.dropAll_spec)
example := (@roundStep_exact : type_of% @Challenge.BFVDecryptLow.roundStep_exact)
example := (@multiplyAndRound_err : type_of% @Challenge.BFVDecryptLow.multiplyAndRound_err)
example := (@dropAll_noise : type_of% @Challenge.BFVDecryptLow.dropAll_noise)
example := (@decLow1_correct : type_of% @Challenge.BFVDecryptLow.decLow1_correct)
example := (@bfvDecryptLow_correct : type_of% @Challenge.BFVDecryptLow.bfvDecryptLow_correct)
example := (@decLowOK?_t_lt : type_of% @Challenge.BFVDecryptLow.decLowOK?_t_lt)
example := (@lowMargin_needed : type_of% @Challenge.BFVDecryptLow.lowMargin_needed)

end Validation.BFVDecryptLow
