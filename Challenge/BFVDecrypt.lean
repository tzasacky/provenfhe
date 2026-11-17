import Spec.DecryptBFV
import Spec.Decrypt
import Challenge.CertifyBFV

/-!
# Challenge.BFVDecrypt — OpenFHE's floating-point BFV decryption is textbook decryption under a computed margin   (LOCKED definitions and statements; proofs in `Validation/BFVDecrypt*.lean`)

`Spec.DecryptBFV` transcribes OpenFHE v1.6.1's BFV decryption for the HPS family at full level
(`DCRTPolyImpl::ScaleAndRound`, the overload with the `…Frac` tables; eight code paths), with its
`double` operations in an arithmetic `A : ArithD` and its machine-word operations with their
wrap-around written out. The statements:

* **Exactness** (`decrypt1_exact`): with the exact arithmetic, for every phase `x ∈ [0, Q)` the
  transcription returns a value `c ≤ t` with `c ≡ ⌊t·x/Q⌉ (mod t)`, `c < t` for power-of-two
  `t`. Pins the tables, the path selection and the integer part. No noise condition.
* **The floating-point error** (`floatSum_err_pow2`, `reduced_err_odd`): for every conforming
  arithmetic, the value that decides the rounding is within `delta t qs` of its exact value
  (for non-power-of-two `t`: the reduced value, before the final `+ 0.5`, within `delta` less the
  error of that addition); for non-power-of-two `t` also the exact reduced value is within
  `overshoot t qs` of `[0, t]`.
* **No wrap** (`words_split`, `intSum_no_wrap`): under `decParamsOK?`, the 64-bit integer
  operations (`MulEqFast`, `AddEqFast`, `SubEqFast`, `LShift`, `operator+=`) never wrap; the
  casts' arguments are in range (`casts_pow2`, and in the main theorem).
* **The main theorem** (`decrypt1_correct`, `bfvDecryptLib_correct`): for every conforming
  arithmetic, if the noise `[phase − ⌊Q/t⌋·m]_Q` is at most `B` and `decLibOK? t qs B`, every
  native coefficient `c` the library returns satisfies `c ≡ m_i (mod t)` and `c ≤ t`.
* **The certificate** (`decryptLibOK?`, `output_decryptLib`, `certifyBFV?_decryptsLib`): what
  `fhe_check` can add to a BFV certificate of `Challenge.CertifyBFV`.
* **Pins**: the margin cannot be dropped (`margin_needed`: a conforming arithmetic, parameters
  and a ciphertext whose noise `decOK` accepts, on which the transcription returns a wrong
  value), `#guard`s of `delta` and `decLibOK?` at OpenFHE-like parameters.

**What the library is NOT shown to do.** `decLibOK?` is strictly stronger than the textbook
condition `Challenge.BFV.decOK`: the proof needs a margin `δ` on top of the noise, to absorb the binary64
rounding of the library's computation. The statements say nothing about noise between the two
thresholds. `DecryptCore`, the NTT, the word-level modular arithmetic and `ModMulFastConst` are not
verified (`Spec.DecryptBFV` docstring), and neither is the decoding. The other two decryption
paths are not in this module: BEHZ in `Challenge.BFVDecryptBEHZ`, fewer limbs in
`Challenge.BFVDecryptLow`, combined per output by `Challenge.BFVDecryptLib.decryptLibExtOK?`.
-/

namespace Challenge.BFVDecrypt
open Spec Spec.Float Spec.DecryptBFV Spec.Scheme NPoly Source Correct Spec.CertifyBFV
  Challenge.CertifyBFV

/-! ## Exact quantities -/

/-- The residues are canonical: `xᵢ < qᵢ`, one per limb. -/
def Reduced (qs xs : List ℕ) : Prop := List.Forall₂ (fun x q => x < q) xs qs

/-- The exact fractional part of the decision sum: `Σ word · (θ mod q)/q` over the words of
`allWords` (the exact table entries). -/
def exactFrac (t : ℕ) (qs xs : List ℕ) : ℚ :=
  ((allWords qs (tables Spec.Float.exact t qs) xs).map fun w => (w.1 : ℚ) * w.2.2).sum

/-- The 64-bit integer operations do not wrap: every word split satisfies
`tmpLo + tmpHi·2^qMSBHf = x` with `tmpHi·2^qMSBHf < 2⁶⁴` (`words_split`); on the unreduced
paths every 64-bit product `MulEqFast` forms is below `2⁶⁴`; and `intSum` is the exact
(unwrapped) sum, below `2⁶³`. -/
def NoWrap (t : ℕ) (qs xs : List ℕ) : Prop :=
  let ws := allWords qs (tables Spec.Float.exact t qs) xs
  (pathReduce t qs = false → ∀ w ∈ ws, w.1 * w.2.1 < 2 ^ 64) ∧
  (intSum t qs ws : ℤ) =
      (ws.map fun w => if pathReduce t qs then w.1 * w.2.1 % t else w.1 * w.2.1).sum ∧
  intSum t qs ws < 2 ^ 63

/-! ## The model is satisfiable; exactness -/

/-- The exact arithmetic conforms. -/
theorem exactD_conforms : ConformsD exactD := sorry

/-- **With exact arithmetic the transcription rounds `t·x/Q` correctly**, for every phase
`x ∈ [0, Q)`: `c ≡ ⌊t·x/Q⌉ (mod t)` and `c ≤ t` (`c < t` for power-of-two `t`). -/
theorem decrypt1_exact (t : ℕ) (qs : List ℕ) (hp : decParamsOK? t qs = true) (x : ℕ)
    (hx : x < qs.prod) :
    ((decrypt1 exactD t qs (tables Spec.Float.exact t qs) (residues qs x) : ℕ) : ZMod t) =
        ((roundDiv (t * x) qs.prod : ℤ) : ZMod t) ∧
      decrypt1 exactD t qs (tables Spec.Float.exact t qs) (residues qs x) ≤ t ∧
      (isPow2 t = true → decrypt1 exactD t qs (tables Spec.Float.exact t qs) (residues qs x) < t) :=
  sorry

/-! ## No wrap -/

/-- **The word split is exact**: for a residue `x < 2⁶⁰`, `tmpHi = x >> qMSBHf` and
`tmpLo = x − (tmpHi << qMSBHf)` (wrapping operations) satisfy `tmpLo + tmpHi·2^qMSBHf = x`,
with no wrap of the shift or the subtraction. -/
theorem words_split (qs : List ℕ) (hq : qMSBHf qs ≤ 60) (x : ℕ) (hx : x < 2 ^ 60) :
    rshift x (qMSBHf qs) * 2 ^ qMSBHf qs < 2 ^ 64 ∧
    lshift (rshift x (qMSBHf qs)) (qMSBHf qs) = rshift x (qMSBHf qs) * 2 ^ qMSBHf qs ∧
    subFast x (lshift (rshift x (qMSBHf qs)) (qMSBHf qs)) + rshift x (qMSBHf qs) * 2 ^ qMSBHf qs
      = x := sorry

/-- **`intSum` never wraps** (`MulEqFast`, `AddEqFast` are wrapping operations): under
`decParamsOK?`, on canonical residues. -/
theorem intSum_no_wrap (t : ℕ) (qs xs : List ℕ) (hp : decParamsOK? t qs = true)
    (hx : Reduced qs xs) : NoWrap t qs xs := sorry

/-- The tables' integer parts do not depend on the arithmetic (and so neither do the words and
`intSum`). -/
theorem allWords_fst (A : Arith) (t : ℕ) (qs xs : List ℕ) :
    (allWords qs (tables A t qs) xs).map (fun w => (w.1, w.2.1)) =
      (allWords qs (tables Spec.Float.exact t qs) xs).map (fun w => (w.1, w.2.1)) := sorry

/-! ## The floating-point error -/

/-- **Power-of-two `t`: the sum is within `delta`** of `1/2 + exactFrac`, for every conforming
arithmetic, whenever `delta ≤ 1/2`; and the cast `static_cast<uint64_t>(floatSum)` (`D:1269`
etc.) has its argument in `[0, 2⁶⁴)`. -/
theorem floatSum_err_pow2 (A : ArithD) (hA : ConformsD A) (t : ℕ) (qs xs : List ℕ)
    (hp : decParamsOK? t qs = true) (hx : Reduced qs xs) (h2 : isPow2 t = true)
    (hδ : delta t qs ≤ 1 / 2) :
    |floatSum A.base (1 / 2) (allWords qs (tables A.base t qs) xs) - (1 / 2 + exactFrac t qs xs)|
        ≤ delta t qs ∧
      0 ≤ floatSum A.base (1 / 2) (allWords qs (tables A.base t qs) xs) ∧
      floatSum A.base (1 / 2) (allWords qs (tables A.base t qs) xs) < 2 ^ 64 := sorry

/-- **Non-power-of-two `t`: the reduced value is close to an exact one.** With `q` the computed
quotient and `e = exactFrac + intSum − t·q`: the reduced value `floatSum − td·q` is within
`sumErr 0 caps + u·(floatMax + t + 2) + 2⁻¹²⁷` of `e`; `e` lies in `[−overshoot, t + overshoot]`;
and the quotient's cast has its argument in `[0, 2⁶⁴)`. For every conforming arithmetic, whenever
`delta ≤ 1/2` and `floatMax ≤ 2⁵²`. (The final `+ 0.5` is analysed in `decrypt1_correct`,
where the margin keeps its result away from zero.) -/
theorem reduced_err_odd (A : ArithD) (hA : ConformsD A) (t : ℕ) (qs xs : List ℕ)
    (hp : decParamsOK? t qs = true) (hx : Reduced qs xs) (h2 : isPow2 t = false)
    (hδ : delta t qs ≤ 1 / 2) (hF : floatMax t qs ≤ 2 ^ 52) :
    let ws := allWords qs (tables A.base t qs) xs
    let f := floatSumInt A t qs ws
    let e : ℚ := exactFrac t qs xs + intSum t qs ws - t * quot A t f
    |reduced A t f - e| ≤ sumErr 0 (caps qs) + u * ((floatMax t qs : ℚ) + t + 2) + 1 / 2 ^ 127 ∧
      -overshoot t qs ≤ e ∧ e ≤ t + overshoot t qs ∧
      0 ≤ A.base.mul f (A.base.div 1 (A.base.ofNat t)) ∧
      A.base.mul f (A.base.div 1 (A.base.ofNat t)) < 2 ^ 64 := sorry

/-! ## The main theorem -/

/-- **One coefficient.** For every conforming arithmetic: if the phase `x ∈ [0, Q)` is within
`B` (centred) of `⌊Q/t⌋·m` modulo `Q`, and `decLibOK? t qs B`, the library returns `c ≤ t` with
`c ≡ m (mod t)`, and the argument of the final cast is in `[0, 2⁶⁴)`. -/
theorem decrypt1_correct (A : ArithD) (hA : ConformsD A) (t : ℕ) (qs : List ℕ)
    (hp : decParamsOK? t qs = true) (B : ℕ) (hB : decLibOK? t qs B = true) (x m : ℕ) (hm : m < t)
    (hx : x < qs.prod)
    (hnoise : (((x : ℤ) - (qs.prod / t * m : ℕ) : ℤ) : ZMod qs.prod).valMinAbs.natAbs ≤ B) :
    let c := decrypt1 A t qs (tables A.base t qs) (residues qs x)
    (c : ZMod t) = (m : ZMod t) ∧ c ≤ t ∧ (isPow2 t = true → c < t) ∧
      (isPow2 t = false →
        0 ≤ A.base.add (reduced A t (floatSumInt A t qs (allWords qs (tables A.base t qs)
              (residues qs x)))) (1 / 2) ∧
        A.base.add (reduced A t (floatSumInt A t qs (allWords qs (tables A.base t qs)
              (residues qs x)))) (1 / 2) < 2 ^ 64) := sorry

/-- **OpenFHE's BFV decryption (HPS family, full level) returns the encrypted message**, for
every conforming arithmetic, when the noise clause of `BFVEncrypts` holds at `B` and
`decLibOK? t qs B`: every native coefficient `c` satisfies `c ≡ mᵢ (mod t)` and `c ≤ t`. -/
theorem bfvDecryptLib_correct (A : ArithD) (hA : ConformsD A) (t : ℕ) (qs : List ℕ)
    (hp : decParamsOK? t qs = true) {N : ℕ} (s : IntPoly N) (ct : List (Poly qs.prod N))
    (m : Poly t N) (B : ℕ)
    (hnoise : normInf (centered (phase (ofInt qs.prod s) ct -
      ofInt qs.prod ⟨fun i => ((qs.prod / t * (m.coeff i).val : ℕ) : ℤ)⟩)) ≤ B)
    (hB : decLibOK? t qs B = true) (i : Fin N) :
    (((bfvDecryptLib A t qs s ct).coeff i : ℕ) : ZMod t) = m.coeff i ∧
      (bfvDecryptLib A t qs s ct).coeff i ≤ t := sorry

/-- **The same against textbook decryption**: under `BFVEncrypts` (which includes the noise
clause), the library's coefficients are those of `Spec.Scheme.bfvDecrypt` modulo `t`. -/
theorem bfvDecryptLib_eq (A : ArithD) (hA : ConformsD A) (t : ℕ) (qs : List ℕ)
    (hp : decParamsOK? t qs = true) {N : ℕ} (s : IntPoly N) (ct : List (Poly qs.prod N))
    (m : Poly t N) (B : ℕ) (he : BFVEncrypts t B s ct m) (hB : decLibOK? t qs B = true)
    (i : Fin N) :
    (((bfvDecryptLib A t qs s ct).coeff i : ℕ) : ZMod t) = (bfvDecrypt t s ct).coeff i ∧
      (bfvDecryptLib A t qs s ct).coeff i ≤ t := sorry

/-! ## The certificate -/

/-- **The library's decryption can be certified** for the outputs of a BFV program: the
technique is in the HPS family (only these use this overload), the parameters pass
`decParamsOK?`, every output is at the top level (`Spec.Decrypt.outputLevel?`: fewer limbs take
another path), and every output's own bound in `c.outputs` passes `decLibOK?`. Depends only on
`x.P`, `x.prog`, `x.mul` and `c.outputs`. -/
def decryptLibOK? (x : InputBFV) (c : CertificateBFV) : Bool :=
  (match x.mul with
    | some (.hps _) => true
    | some (.poverq _) => true
    | some (.leveled ..) => true
    | _ => false) &&
  decParamsOK? x.P.src.t x.P.src.qs &&
  x.prog.outputs.all (fun o => Decrypt.outputLevel? x.P.src x.prog o == some x.P.src.qs.length) &&
  c.outputs.all (fun ob => decLibOK? x.P.src.t x.P.src.qs ob.2)

/-- **One output.** A BFV value at the top level, under `s`, with exact message `m`, that
`Encrypts` with noise at most `B`, is decrypted by the library (every conforming arithmetic) to
native coefficients `c ≤ t` with `c ≡ mᵢ (mod t)`, if `decParamsOK?` and `decLibOK?` at `B`. -/
theorem output_decryptLib (P : FullParams) (hk : P.src.kind = .bfv) (A : ArithD)
    (hA : ConformsD A) (hp : decParamsOK? P.src.t P.src.qs = true)
    (s : IntPoly P.src.N) (B : ℕ) (v : Val P.src) (ct : List (IntPoly P.src.N))
    (m : Poly P.src.t P.src.N) (hmsg : v.msg = .exact m) (hkey : v.key = 1)
    (hlev : v.level = P.src.qs.length) (he : Encrypts P s B v ct)
    (hB : decLibOK? P.src.t P.src.qs B = true) (i : Fin P.src.N) :
    (((bfvDecryptLib A P.src.t P.src.qs s (ct.map (ofInt P.src.qs.prod))).coeff i : ℕ) :
        ZMod P.src.t) = m.coeff i ∧
      (bfvDecryptLib A P.src.t P.src.qs s (ct.map (ofInt P.src.qs.prod))).coeff i ≤ P.src.t :=
  sorry

/-- **The BFV certificate, with the library's decryption.** If `certifyBFV? x = some c` and
`decryptLibOK? x c`, then for every conforming arithmetic, secret, messages and inputs within
their bounds, at the end of every run within the budgets `c.budget`, every output's LIBRARY decryption with `s`
has native coefficients `c ≤ t` congruent to the message `Source.eval` computes. -/
theorem certifyBFV?_decryptsLib (x : InputBFV) (c : CertificateBFV) (h : certifyBFV? x = some c)
    (hd : decryptLibOK? x c = true) (A : ArithD) (hA : ConformsD A)
    (s : IntPoly x.P.src.N) (msgs : Var → Msg x.P.src.t x.P.src.N)
    (cts : Var → List (IntPoly x.P.src.N)) (hin : TraceBFV.InputsOK x.P s x.prog msgs cts) :
    ∃ ρ, Source.eval x.P.src x.prog msgs = some ρ ∧
      ∀ σ, TraceBFV.RunAt x.P c.budget s 0 x.prog.body (initEnv x.P.src x.prog msgs)
          (Trace.initCt x.P x.prog cts) σ →
        ∀ o ∈ x.prog.outputs, ∃ v ct m, ρ o = some v ∧ σ o = some ct ∧ v.msg = .exact m ∧
          ∀ i, (((bfvDecryptLib A x.P.src.t x.P.src.qs s
                  (ct.map (ofInt x.P.src.qs.prod))).coeff i : ℕ) : ZMod x.P.src.t) = m.coeff i ∧
            (bfvDecryptLib A x.P.src.t x.P.src.qs s (ct.map (ofInt x.P.src.qs.prod))).coeff i
              ≤ x.P.src.t := sorry

/-! ## Pins -/

/-- A conforming arithmetic that rounds every `s += a*b` up by the factor `1 + u` (contracted
form) and is otherwise exact (`advD_conforms`). -/
def advD : ArithD :=
  { exactD with
    base := { ofNat := fun n => n, mul := (· * ·), div := (· / ·), add := (· + ·),
              fma := fun a b c => (a * b + c) * (1 + Spec.Float.u),
              mulAdd := fun s a b => (s + a * b) * (1 + Spec.Float.u) } }

/-- `advD` conforms. -/
theorem advD_conforms : ConformsD advD := sorry

/-- The limb of `margin_needed`: `2⁵⁹ − 55` (odd; the split path, one limb). -/
def q0 : ℕ := 2 ^ 59 - 55

/-- **The margin cannot be dropped.** `t = 2`, one limb `q0`, message `0`, phase
`x = (q0 − 3)/4` (its noise is `x` itself): the textbook condition `decOK` accepts the noise,
textbook rounding gives `0`, the transcription with exact arithmetic gives `0`, and with the
conforming arithmetic `advD` it gives `1`. `decLibOK?` refuses this noise bound. -/
theorem margin_needed :
    decParamsOK? 2 [q0] = true ∧ Challenge.BFV.decOK 2 q0 ((q0 - 3) / 4) = true ∧
      roundDiv (2 * ((q0 - 3) / 4 : ℕ)) q0 = 0 ∧
      decrypt1 exactD 2 [q0] (tables Spec.Float.exact 2 [q0]) (residues [q0] ((q0 - 3) / 4)) = 0 ∧
      decrypt1 advD 2 [q0] (tables advD.base 2 [q0]) (residues [q0] ((q0 - 3) / 4)) = 1 ∧
      decLibOK? 2 [q0] ((q0 - 3) / 4) = false := sorry

-- OpenFHE-like parameters: three 60-bit limbs (the split path, every default parameter set).
-- With `t = 65536` and with `t = 786433` (reduced) the margin loss is below `2⁻¹⁶`; with
-- `t = 65537` (unreduced: `intSum` goes into the `double`) it is about `0.047`.
#guard decParamsOK? 65537 [1152921504606584833, 1152921504598720513, 1152921504597016577]
#guard pathSplit [1152921504606584833, 1152921504598720513, 1152921504597016577]
#guard delta 65536 [1152921504606584833, 1152921504598720513, 1152921504597016577] < 1 / 2 ^ 16
#guard delta 786433 [1152921504606584833, 1152921504598720513, 1152921504597016577] < 1 / 2 ^ 16
#guard delta 65537 [1152921504606584833, 1152921504598720513, 1152921504597016577] < 1 / 20 &&
  1 / 25 < delta 65537 [1152921504606584833, 1152921504598720513, 1152921504597016577]
-- A noise bound of 90% of the textbook threshold `Q/(2t)` is accepted at `t = 65536`, refused at
-- `t = 65537` only above 90%·(1 − 2·0.047).
#guard decLibOK? 65536 [1152921504606584833, 1152921504598720513, 1152921504597016577]
  ((1152921504606584833 * 1152921504598720513 * 1152921504597016577) / (2 * 65536) * 9 / 10)
#guard decLibOK? 65537 [1152921504606584833, 1152921504598720513, 1152921504597016577]
  ((1152921504606584833 * 1152921504598720513 * 1152921504597016577) / (2 * 65537) * 8 / 10)
#guard !decLibOK? 65537 [1152921504606584833, 1152921504598720513, 1152921504597016577]
  ((1152921504606584833 * 1152921504598720513 * 1152921504597016577) / (2 * 65537) * 95 / 100)
-- The top of the non-split path (three 49-bit limbs, `qMSB + sizeQMSB = 51`): the proved bound
-- exceeds `1/2`, so the check refuses even noise `0`.
#guard decParamsOK? 65537 [562949953421231, 562949953420961, 562949953420313]
#guard !pathSplit [562949953421231, 562949953420961, 562949953420313]
#guard 1 / 2 < delta 65537 [562949953421231, 562949953420961, 562949953420313]
#guard !decLibOK? 65537 [562949953421231, 562949953420961, 562949953420313] 0
-- Large `t` (`≥ 2⁵⁰`) is outside `decParamsOK?`.
#guard !decParamsOK? (2 ^ 50 + 1) [1152921504606584833, 1152921504598720513]
-- Path selection: the eight paths are all reachable.
#guard [(2, [97, 101]), (2 ^ 40, [2 ^ 47 - 115, 2 ^ 47 - 87]), (2, [1152921504606584833]),
    (2 ^ 40, (List.replicate 8 1152921504606584833)), (3, [97, 101]),
    (2 ^ 30 + 3, [2 ^ 40 - 87]), (3, [1152921504606584833]),
    (2 ^ 25 + 1, [1152921504606584833])].map
      (fun p => (isPow2 p.1, pathSplit p.2, pathReduce p.1 p.2))
  == [(true, false, false), (true, false, true), (true, true, false), (true, true, true),
      (false, false, false), (false, false, true), (false, true, false), (false, true, true)]

end Challenge.BFVDecrypt
