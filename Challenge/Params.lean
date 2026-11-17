import Spec.Correct

/-!
# Challenge.Params — `ParamsOK`: non-vacuity, decidability, message range   (LOCKED statements; proofs in `Validation/`)

* `exampleBGV31_ok`: `ParamsOK` is satisfiable at a realistic size (`N = 2¹⁴`, 31-bit primes).
* `schemeParamsOK?_sound`, `schemeParamsOK?_wideBGV`: the compiled check of the scheme-level core
  implies `SchemeParamsOK` (all the noise headline assumes) and accepts a 60-bit modulus.
* `paramsOK?_sound`, `paramsOK?_exampleBGV31`: the compiled check `Spec.paramsOK?` implies
  `ParamsOK` and accepts the shipped instance (`Challenge.Corpus.paramsOK?_tinyBGV` for the tiny
  one), so the `ParamsOK` hypothesis of a statement can be discharged on user parameters by
  running a program. `paramsOK?_rejects_*` show that it tells right from wrong.
* `bgv_inputs_exist`, `bgv_small_noise_excludes`: why `SchemeParamsOK.msgRange` is `t / 2 ≤ inputNoise`.
  With it every message has a two-component encryption within `inputNoise` at every level whose
  modulus exceeds `t` (so `InputsOK` restricts no message of a two-component input); below it
  some message has none.

Proofs must not use compiled-evaluation tactics (they add axioms): acceptance is by kernel
evaluation (`decide +kernel`; kernel `Nat` arithmetic is GMP-accelerated).
-/

namespace Challenge.Params
open Spec NPoly Scheme Source Correct

theorem exampleBGV31_ok : ParamsOK FullParams.exampleBGV31 := sorry

/-- **Soundness of the scheme-level check**: whatever `schemeParamsOK?` accepts is valid at the
scheme level, whatever the size of its primes. -/
theorem schemeParamsOK?_sound (P : FullParams) (h : schemeParamsOK? P = true) :
    SchemeParamsOK P := sorry

/-- A BGV parameter set outside 32-bit storage: `N = 2¹³`, one 60-bit prime
`2⁶⁰ - 2¹⁸ + 1` (not a 32-bit word), `t = 65537`. `store` is a placeholder (no limb table):
the scheme-level predicate does not read it. -/
def wideBGV : FullParams where
  src := { kind := .bgv, N := 8192, qs := [1152921504606584833], t := 65537 }
  store := { W := 1, limbs := [], special := [] }
  secretBound := 1
  inputNoise := 2 ^ 21
  keyNoise := 2 ^ 21
  outputNoise := 0

/-- The scheme-level check accepts a 60-bit prime (so the noise headline applies there), and the
full check rejects the same parameters (they do not fit 32-bit words). -/
theorem schemeParamsOK?_wideBGV :
    schemeParamsOK? wideBGV = true ∧ paramsOK? wideBGV = false := sorry

/-- **Soundness of the parameter check**: whatever `paramsOK?` accepts is valid. -/
theorem paramsOK?_sound (P : FullParams) (h : paramsOK? P = true) : ParamsOK P := sorry

/-- The check accepts the 31-bit example instance. -/
theorem paramsOK?_exampleBGV31 : paramsOK? FullParams.exampleBGV31 = true := sorry

/-- A composite modulus is rejected even when it has a `ψ` with `ψ^N = -1`: `697 = 17 · 41`,
`N = 4`, `ψ = 495` (`≡ 2 (mod 17)`, `≡ 3 (mod 41)`). Every other clause of `ParamsOK` holds for
these parameters, so it is the primality test that rejects, at both levels. -/
def compositeParams : FullParams where
  src := { kind := .bgv, N := 4, qs := [697], t := 5 }
  store := { W := 2, limbs := [⟨697, 495⟩], special := [] }
  secretBound := 1
  inputNoise := 64
  keyNoise := 64
  outputNoise := 128

theorem paramsOK?_rejects_composite :
    ((495 : ℕ) : ZMod 697) ^ 4 = -1 ∧ primeOK? 697 = false ∧ limbOK? 4 ⟨697, 495⟩ = false ∧
      schemeParamsOK? compositeParams = false ∧ paramsOK? compositeParams = false := sorry

/-- A `ψ` that is not a primitive `2N`-th root of unity is rejected (`ψ = 1`). -/
theorem paramsOK?_rejects_root :
    paramsOK? { FullParams.exampleBGV31 with
      store := { FullParams.exampleBGV31.store with
        limbs := [⟨1073872897, 1⟩, ⟨1074266113, 639594595⟩] } } = false := sorry

/-- An input noise bound below `t / 2` is rejected (`SchemeParamsOK.msgRange`), by both checks. -/
theorem paramsOK?_rejects_msgRange :
    schemeParamsOK? { FullParams.exampleBGV31 with inputNoise := 32767 } = false ∧
      paramsOK? { FullParams.exampleBGV31 with inputNoise := 32767 } = false := sorry

/-- **`SchemeParamsOK.msgRange` suffices.** Under scheme-level valid BGV parameters, every message
has a two-component encryption (`v.parts = 2`) with noise at most `P.inputNoise` under every
secret, at every level whose modulus exceeds `t`: for two-component inputs at such levels, the
input hypothesis of the headline theorems (`InputsOK`) excludes no message. (Inputs declared with
another number of components are not covered by this statement.) -/
theorem bgv_inputs_exist (P : FullParams) (hP : SchemeParamsOK P) (hk : P.src.kind = .bgv)
    (s : IntPoly P.src.N) (v : Val P.src) (m : Poly P.src.t P.src.N) (hm : v.msg = .exact m)
    (h2 : v.parts = 2) (hQ : P.src.t < P.src.modulus v.level) :
    ∃ ct, Encrypts P s P.inputNoise v ct := sorry

/-- **`SchemeParamsOK.msgRange` is necessary.** With a bound below `t / 2`, the constant message `⌊t/2⌋`
has no encryption at all within the bound: the centered phase is congruent to the message modulo
`t`, and the least absolute value in the class of `⌊t/2⌋` is `⌊t/2⌋`. -/
theorem bgv_small_noise_excludes (P : FullParams) (hk : P.src.kind = .bgv) (hN : 0 < P.src.N)
    (ht : 2 ≤ P.src.t) (s : IntPoly P.src.N) (B : ℕ) (hB : B < P.src.t / 2) (v : Val P.src)
    (hm : v.msg = .exact (NPoly.const ((P.src.t / 2 : ℕ) : ZMod P.src.t)))
    (ct : List (IntPoly P.src.N)) : ¬ Encrypts P s B v ct := sorry

end Challenge.Params
