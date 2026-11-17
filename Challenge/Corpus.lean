import Spec.Params
import Spec.Source

/-!
# Challenge.Corpus — test articles shared by the locked statements   (LOCKED statements; proofs in `Validation/`)

The two one-instruction source programs that the noise headline's guards and pins
(`Challenge.Headline.Defs`), the decryption pins (`Challenge.Decrypt`) and the fast analyzer's
guards use, and the two pins saying that the tiny parameter set `Spec.FullParams.tinyBGV`
(`N = 4`, `t = 17`, two primes `≡ 1 (mod 2¹⁶)`) is valid: `tinyBGV_ok` (`ParamsOK`) and
`paramsOK?_tinyBGV` (the decision procedure accepts it; compare `Challenge.Params.paramsOK?_sound`).

The corpus constants are defined here, not in `Spec/`: they are test articles, and they are part
of the locked statements.
-/

namespace Challenge.Corpus
open Spec Source

/-- The source program `c = a + b` on two fresh 2-component ciphertexts at level 2, under `s`
(a declaration is `⟨name, parts, level, scale, key⟩`). -/
def addProg : Source.Program :=
  { inputs := [⟨"a", 2, 2, 1, 1⟩, ⟨"b", 2, 2, 1, 1⟩], body := [.add "c" "a" "b"], outputs := ["c"] }

/-- The source program `c = a · b` (tensor product, 3 components, no relinearization). -/
def mulProg : Source.Program :=
  { inputs := [⟨"a", 2, 2, 1, 1⟩, ⟨"b", 2, 2, 1, 1⟩], body := [.mul "c" "a" "b"], outputs := ["c"] }

theorem tinyBGV_ok : ParamsOK FullParams.tinyBGV := sorry

/-- The decision procedure accepts `tinyBGV` (compare `Challenge.Params.paramsOK?_sound`). -/
theorem paramsOK?_tinyBGV : paramsOK? FullParams.tinyBGV = true := sorry

end Challenge.Corpus
