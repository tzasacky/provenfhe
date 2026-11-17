import Challenge.BFVMul
import Challenge.BFVMul.BEHZWord

/-!
# Challenge.Families.BEHZ — the BEHZ family, and SEAL's parameterisation of it   (LOCKED statements; proofs in `Validation/Families/BEHZ.lean`)

**The family theorem already exists.** `Challenge.BFVMul.behzMul t qs bs msk mt` is the
multiplication of Bajard, Eynard, Hasan and Zucca (ePrint 2016/510): fast conversion of `m̃·c`
from `qs` to `bs ++ [msk]` with the small Montgomery reduction modulo `m̃`, limb-wise tensor, fast
floor of `t·T/Q`, Shenoy–Kumaresan conversion back. Its auxiliary base `bs` (any number of
moduli, any sizes), the extra modulus `msk` and the Montgomery modulus `mt` are free arguments;
`Challenge.BFVMul.stepOK_mul_behz`, `stepOK_square_behz` hold for every choice accepted by
`behzAuxOK?` (positive pairwise coprime moduli, `mt` coprime to all of them and to `Q`, `mt` even,
`2(k−1) ≤ mt`, `msk > 2·|bs|`, and the size condition
`t·N·Q·(m̃ + 2(k−1))² + 2k·m̃² ≤ m̃²·B·(msk − 1 − 2·|bs|)`), at the slacks of
`Spec.BudgetBFV.behzSlack` (lift excess `⌈2(k−1)·Q/m̃⌉`, rounding slack `2k`). The two centring
conventions it fixes (`r` read in `[−m̃/2, m̃/2)`, `α` read as `α − msk` when `α > ⌊msk/2⌋`) are
those of both OpenFHE and SEAL (below). OpenFHE's choice (`m̃ = 2¹⁶`, `|bs| = k`, `msk` enlarged
until the condition holds) is one instance, checked at run time by `certifyBFV?`.

**What is library-specific is around it, not in it.** `Challenge.BFVMul.behzWordOK?` (the
`ModSubFast` precondition `α − msk ≥ −q`, `m̃ < b`, moduli below `2⁶⁰`) is OpenFHE's machine-word
condition; it is false at SEAL's bases (61-bit primes; checked below) and is not a side condition
of SEAL's algorithm, whose Shenoy–Kumaresan finish multiplies `|α|` by `B` and selects an addition
or a subtraction (`rns.cpp:1359-1373`), so no such precondition arises.

**SEAL's BEHZ multiplication, read from the source.** Microsoft SEAL v4.7.2 (commit
`ce53aa40969364f79599009bc8882f71fce0c13d`), `native/src/seal/`. Per data level the context
builds one `RNSTool` for that level's coefficient moduli (`context.cpp:420-427`), so at level `ℓ`
the ciphertext basis is `qs.take ℓ`. Its set-up (`util/rns.cpp:819-936`):

* `m_sk` and `γ` are the first two, and `B` the next primes, of `get_primes(2N, 61, |B| + 2)`
  (`util/numth.cpp:278-311`: the largest 61-bit primes `≡ 1 (mod 2N)`, descending)
  (`rns.cpp:863-868`, `:902-903`);
* `|B|` is the SHORTEST prefix such that
  `bitcount(B·m_sk) − 1 ≥ 5 + bitcount(t) + log₂N + bitcount(Q)` (`rns.cpp:870-900`, new in
  4.7.0; it can be fewer than `k` primes: three at the top level of `sealBFV`, below);
* `m̃ = 2³²` (`rns.cpp:906`).

`bfv_multiply` (`evaluator.cpp:499-631`) runs: `fastbconv_m_tilde_sm_mrq` (`rns.cpp:1521-1611`):
`yᵢ = [xᵢ·m̃·Q̂ᵢ⁻¹]_{qᵢ}` (input scale `m̃`, `rns.cpp:982-983`, `BaseConverter` set-up
`:709-748`), the limb modulo `b` is `Σᵢ yᵢ·[Q̂ᵢ·m̃⁻¹]_b + r·[Q·m̃⁻¹]_b` with
`r = Σᵢ yᵢ·[Q̂ᵢ·(−Q⁻¹)]_{m̃} mod m̃` (`:1568-1586`) read as `r − m̃` when `r ≥ m̃/2`
(`:1600-1601`): the residue of `(Σᵢ yᵢ·Q̂ᵢ + r·Q)·m̃⁻¹`, `BEHZ.smmrq1`. Then the tensor product
(`evaluator.cpp:612-617`) and `inverse_ntt_multiply_t_fast_floor_fastbconv_sk`
(`rns.cpp:1613-1705`): the inverse NTT scaled by `t·Q̂ᵢ⁻¹` gives `yᵢ = [t·xᵢ·Q̂ᵢ⁻¹]_{qᵢ}`
(`:1053-1056`), the fast conversion with output scales `Q⁻¹·B̂ⱼ⁻¹` (`:1061-1081`) subtracted
from the `Bsk` limbs scaled by `t·Q⁻¹·B̂ⱼ⁻¹` gives `zⱼ = [F·B̂ⱼ⁻¹]_{bⱼ}` and `[F]_{m_sk}` for the
fast floor `F = (t·T − Σᵢ yᵢ·Q̂ᵢ)/Q` (`:1680-1695`), and `fastbconv_sk_finish` (`:1336-1374`)
computes `α = [(Σⱼ zⱼ·B̂ⱼ − F)·B⁻¹]_{m_sk}`, negative when `α > ⌊m_sk/2⌋` (`:1354`), and
`Σⱼ zⱼ·B̂ⱼ − α·B mod qᵢ`. These are the integers of `BEHZ.floor1`, `BEHZ.sk1`. So SEAL's
multiplication is `behzMul t (qs.take ℓ) B m_sk (2³²)`, on residues: an instance of the family by
the choice of parameters. That equality is ARGUED from the source, as the OpenFHE transcription
is; not proved, and not checked against recorded SEAL runs. Not modelled: SEAL's lazy reductions
(`[0, 3m)` and `[0, 4m)` intermediate ranges, moduli below `2⁶¹`), Montgomery form, the NTT,
operands with more than two components.

**What is proved here.**

* `sealRule_of_bits`: SEAL's bit-count test implies `32·t·N·Q ≤ B·m_sk`.
* `behzAuxOK_sealRule`: for EVERY parameter set satisfying the size rule `32·t·N·Q ≤ B·m_sk`
  (whatever the primes, their number, their sizes), with all moduli distinct odd primes,
  `k ≤ 2³¹` and `4·|B| + 2 ≤ m_sk`, the side condition `behzAuxOK?` holds at `m̃ = 2³²`. So every
  parameter set SEAL accepts is in the family, not just the one checked below.
* `stepOK_mul_behz_sealRule`, `stepOK_square_behz_sealRule`: hence SEAL's parameterisation meets
  the `mul`/`square` contracts at the `behzSlack` slacks with `m̃ = 2³²`.
* `sealBFV_behzAuxOK`, `sealBFV_sealRule`: at `Challenge.BFV.sealBFV` (SEAL's
  `CoeffModulus::BFVDefault(8192)` data primes, `util/globals.cpp:50`, `t = 65537`) and SEAL's
  bases `sealAuxB ℓ`, `sealMsk` at each level `ℓ = 1…4` (computed by a script outside the repository, a transcription of the set-up above), the
  side condition and the size rule hold (kernel-checked); `stepOK_mul_behz_sealBFV` is the
  resulting statement about SEAL's algorithm at that parameter set.
* `openfhe_behzOK`: OpenFHE's parameterisation (`m̃ = 2¹⁶`, its base rule applied to the
  moduli of two recorded OpenFHE runs) passes `behzAuxOK?` and `behzWordOK?` (kernel-checked).

That SEAL's fast conversions read canonical residues (which the integer `Σᵢ yᵢ·Q̂ᵢ`, and hence the
equality with `behzMul`, depends on) was checked in the source: the first step of every
conversion reduces fully (`util/rns.cpp:425-442`, `multiply_uint_mod`), and the scaled inverse
NTT feeding the fast floor stores fully reduced values (`util/ntt.cpp:1146`, `FullReduce = true`;
`:303-306`; HEXL build: `:1141`, `multiply_poly_scalar_coeffmod`). The lazy ranges are only
those of the tensor-product inputs, which are residues either way. "Every parameter set SEAL
accepts" in `behzAuxOK_sealRule`'s reading rests on SEAL's own validity checks (coefficient
moduli at most 60 bits, hence distinct from the 61-bit `B`, `m_sk`; NTT-friendly primes are odd):
argued.
-/

namespace Challenge.Families
open Spec NPoly Scheme Source Challenge.BFV Challenge.BFVMul

/-! ## SEAL's size rule -/

/-- **SEAL's bit-count test implies the size rule.** If
`bitcount(t) + log₂N + bitcount(Q) + 5 ≤ bitcount(B·m_sk) − 1` (`rns.cpp:875-880`, with
`N = 2ⁿ`), then `32·t·N·Q ≤ B·m_sk`. -/
theorem sealRule_of_bits (t n Q Bm : ℕ) (h : 5 + Nat.size t + n + Nat.size Q ≤ Nat.size Bm - 1) :
    32 * t * 2 ^ n * Q ≤ Bm := sorry

/-- **Every parameter set meeting SEAL's size rule is in the BEHZ family.** All moduli of
`qs ++ bs ++ [msk]` distinct odd primes, at most `2³¹` ciphertext moduli, `4·|bs| + 2 ≤ msk`,
and `32·t·N·Q ≤ B·msk`: then `behzAuxOK?` holds with `m̃ = 2³²`. -/
theorem behzAuxOK_sealRule (t N : ℕ) (qs bs : List ℕ) (msk : ℕ) (ht : 1 ≤ t) (hN : 1 ≤ N)
    (hprime : ∀ m ∈ qs ++ bs ++ [msk], Nat.Prime m)
    (hodd : ∀ m ∈ qs ++ bs ++ [msk], m % 2 = 1)
    (hnd : (qs ++ bs ++ [msk]).Nodup)
    (hk : qs.length ≤ 2 ^ 31) (hmsk : 4 * bs.length + 2 ≤ msk)
    (hsize : 32 * t * N * qs.prod ≤ bs.prod * msk) :
    behzAuxOK? t N qs bs msk (2 ^ 32) = true := sorry

variable (P : FullParams)

/-- **BEHZ multiplication with SEAL's parameterisation meets the `mul` contract** at the slacks of
`behzSlack` with `m̃ = 2³²`, for every auxiliary base `bs` and `msk` meeting SEAL's size rule
at the operand's level (`behzAuxOK_sealRule`). About the algorithm `behzMul`, which SEAL's
`bfv_multiply` computes on residues as read from its source (module docstring); not about SEAL's
code. -/
theorem stepOK_mul_behz_sealRule (hP : SchemeParamsOK P) (E : TraceBFV.Budget)
    (s : IntPoly P.src.N) (hs : SecretOK P.secretBound s) (ρ ρ' : Env P.src)
    (σ : Trace.CtEnv P) (d a b : Var) (x y : Val P.src) (ca cb : List (IntPoly P.src.N))
    (bs : List ℕ) (msk : ℕ)
    (hL : BudgetBFV.mulLiftNormAt P x.level
            (BudgetBFV.behzSlack P.src.t P.src.N (P.src.modulus x.level) bs.prod msk x.level
              bs.length (2 ^ 32)).e ≤ E.mulLift)
    (hR : BudgetBFV.mulRoundApprox P (2 * x.level) ≤ E.mulRound)
    (hstep : step P.src ρ (.mul d a b) = some ρ') (hx : ρ a = some x) (hy : ρ b = some y)
    (ha : σ a = some ca) (hb : σ b = some cb)
    (hla : ca.length = 2) (hlb : cb.length = 2) (h2x : x.parts = 2) (h2y : y.parts = 2)
    (hℓ : 1 ≤ x.level) (hℓL : x.level ≤ P.src.qs.length)
    (ht : 1 ≤ P.src.t) (hN : 1 ≤ P.src.N)
    (hprime : ∀ m ∈ P.src.qs.take x.level ++ bs ++ [msk], Nat.Prime m)
    (hodd : ∀ m ∈ P.src.qs.take x.level ++ bs ++ [msk], m % 2 = 1)
    (hnd : (P.src.qs.take x.level ++ bs ++ [msk]).Nodup)
    (hk : x.level ≤ 2 ^ 31) (hmsk : 4 * bs.length + 2 ≤ msk)
    (hsize : 32 * P.src.t * P.src.N * (P.src.qs.take x.level).prod ≤ bs.prod * msk) :
    TraceBFV.StepOK P E s ρ ρ' σ
      (σ.set d (behzMul P.src.t (P.src.qs.take x.level) bs msk (2 ^ 32) ca cb)) (.mul d a b) :=
  sorry

/-- **BEHZ squaring with SEAL's parameterisation meets the `square` contract** with the same
slacks (`stepOK_mul_behz_sealRule`). -/
theorem stepOK_square_behz_sealRule (hP : SchemeParamsOK P) (E : TraceBFV.Budget)
    (s : IntPoly P.src.N) (hs : SecretOK P.secretBound s) (ρ ρ' : Env P.src)
    (σ : Trace.CtEnv P) (d a : Var) (x : Val P.src) (ca : List (IntPoly P.src.N))
    (bs : List ℕ) (msk : ℕ)
    (hL : BudgetBFV.mulLiftNormAt P x.level
            (BudgetBFV.behzSlack P.src.t P.src.N (P.src.modulus x.level) bs.prod msk x.level
              bs.length (2 ^ 32)).e ≤ E.mulLift)
    (hR : BudgetBFV.mulRoundApprox P (2 * x.level) ≤ E.mulRound)
    (hstep : step P.src ρ (.square d a) = some ρ') (hx : ρ a = some x)
    (ha : σ a = some ca) (hla : ca.length = 2) (h2x : x.parts = 2)
    (hℓ : 1 ≤ x.level) (hℓL : x.level ≤ P.src.qs.length)
    (ht : 1 ≤ P.src.t) (hN : 1 ≤ P.src.N)
    (hprime : ∀ m ∈ P.src.qs.take x.level ++ bs ++ [msk], Nat.Prime m)
    (hodd : ∀ m ∈ P.src.qs.take x.level ++ bs ++ [msk], m % 2 = 1)
    (hnd : (P.src.qs.take x.level ++ bs ++ [msk]).Nodup)
    (hk : x.level ≤ 2 ^ 31) (hmsk : 4 * bs.length + 2 ≤ msk)
    (hsize : 32 * P.src.t * P.src.N * (P.src.qs.take x.level).prod ≤ bs.prod * msk) :
    TraceBFV.StepOK P E s ρ ρ' σ
      (σ.set d (behzMul P.src.t (P.src.qs.take x.level) bs msk (2 ^ 32) ca ca)) (.square d a) :=
  sorry

/-! ## SEAL's bases at `sealBFV`

SEAL v4.7.2's auxiliary base `B` and `m_sk` for the data levels of `Challenge.BFV.sealBFV`
(`BFVDefault(8192)`, `t = 65537`), as the set-up at `rns.cpp:839-903` chooses them: the 61-bit
primes `≡ 1 (mod 16384)` below `2⁶¹` in descending order are `m_sk`, `γ`, `b₁`, `b₂`, `b₃`, …;
the size test needs three of the `b`s at level 4, two at level 3 and one at levels 2 and 1
(at levels 1 and 2 the base is capped at `|B| = k` primes, `rns.cpp:848-853`, `:892`). The
primes themselves are data copied from the script output: `behzAuxOK?` checks coprimality, not
primality. -/

/-- SEAL's auxiliary base `B` at level `ℓ` of `sealBFV` (section docstring). -/
def sealAuxB (ℓ : ℕ) : List ℕ :=
  if ℓ = 4 then [2305843009212694529, 2305843009212399617, 2305843009211662337]
  else if ℓ = 3 then [2305843009212694529, 2305843009212399617]
  else [2305843009212694529]

/-- SEAL's `m_sk` for `N = 8192` (the largest 61-bit prime `≡ 1 (mod 16384)`). -/
def sealMsk : ℕ := 2305843009213317121

/-- **SEAL's bases at `sealBFV` pass the BEHZ side condition** at every data level, with
`m̃ = 2³²`. -/
theorem sealBFV_behzAuxOK : ∀ ℓ ∈ [1, 2, 3, 4],
    behzAuxOK? sealBFV.src.t sealBFV.src.N (sealBFV.src.qs.take ℓ) (sealAuxB ℓ) sealMsk (2 ^ 32)
      = true := sorry

/-- **SEAL's bases at `sealBFV` meet SEAL's own size rule** (with the bit-count test as SEAL
evaluates it) at every data level. -/
theorem sealBFV_sealRule : ∀ ℓ ∈ [1, 2, 3, 4],
    5 + Nat.size sealBFV.src.t + 13 + Nat.size (sealBFV.src.qs.take ℓ).prod ≤
        Nat.size ((sealAuxB ℓ).prod * sealMsk) - 1 ∧
      32 * sealBFV.src.t * sealBFV.src.N * (sealBFV.src.qs.take ℓ).prod ≤
        (sealAuxB ℓ).prod * sealMsk := sorry

/-- **SEAL's BEHZ multiplication at `sealBFV` meets the `mul` contract** at every data level,
with its own bases, at the slacks of `behzSlack` with `m̃ = 2³²`. About the algorithm read from
SEAL's source (module docstring), not about SEAL's code. -/
theorem stepOK_mul_behz_sealBFV (E : TraceBFV.Budget)
    (s : IntPoly sealBFV.src.N) (hs : SecretOK sealBFV.secretBound s) (ρ ρ' : Env sealBFV.src)
    (σ : Trace.CtEnv sealBFV) (d a b : Var) (x y : Val sealBFV.src)
    (ca cb : List (IntPoly sealBFV.src.N))
    (hL : BudgetBFV.mulLiftNormAt sealBFV x.level
            (BudgetBFV.behzSlack sealBFV.src.t sealBFV.src.N (sealBFV.src.modulus x.level)
              (sealAuxB x.level).prod sealMsk x.level (sealAuxB x.level).length (2 ^ 32)).e
          ≤ E.mulLift)
    (hR : BudgetBFV.mulRoundApprox sealBFV (2 * x.level) ≤ E.mulRound)
    (hstep : step sealBFV.src ρ (.mul d a b) = some ρ') (hx : ρ a = some x) (hy : ρ b = some y)
    (ha : σ a = some ca) (hb : σ b = some cb)
    (hla : ca.length = 2) (hlb : cb.length = 2) (h2x : x.parts = 2) (h2y : y.parts = 2)
    (hℓ : 1 ≤ x.level) (hℓL : x.level ≤ sealBFV.src.qs.length) :
    TraceBFV.StepOK sealBFV E s ρ ρ' σ
      (σ.set d (behzMul sealBFV.src.t (sealBFV.src.qs.take x.level) (sealAuxB x.level) sealMsk
        (2 ^ 32) ca cb)) (.mul d a b) := sorry

-- OpenFHE's machine-word condition is not SEAL's: it fails at SEAL's 61-bit bases (whose
-- algorithm does not need it, module docstring).
#guard !behzWordOK? 65537 8192 (sealBFV.src.qs.take 4) (sealAuxB 4) sealMsk (2 ^ 32)
-- The slacks at SEAL's real top-level base (three primes, about `2¹⁸³`, not the `2²⁴⁰` lower
-- bound `Challenge.BFVMul.sealBEHZ` assumes): the flag holds, `e` and `ρ` are those of
-- `sealBEHZ` (they do not depend on `B`), and the analyzer's bound on `sealProg` is unchanged.
#guard BudgetBFV.behzSlack 65537 8192 (sealBFV.src.modulus 4) (sealAuxB 4).prod sealMsk 4 3 (2 ^ 32)
  == ⟨33451115118582234806483297447873958169485721, 8, true⟩
#guard Nat.log2 ((sealAuxB 4).prod) == 182
#guard refAnalyzeBFV sealBFV (sealBudget (BudgetBFV.behzSlack 65537 8192 (sealBFV.src.modulus 4)
    (sealAuxB 4).prod sealMsk 4 3 (2 ^ 32))) sealProg
  == some 1487107268619559764005097146872301164369
-- SEAL's rule is a real constraint: one prime fewer at level 4 fails it, and so does the
-- side condition.
#guard !decide (32 * 65537 * 8192 * (sealBFV.src.qs.take 4).prod ≤
    [2305843009212694529, 2305843009212399617].prod * sealMsk)
#guard !behzAuxOK? 65537 8192 (sealBFV.src.qs.take 4) [2305843009212694529] sealMsk (2 ^ 32)

/-! ## OpenFHE's bases at recorded parameter sets

OpenFHE v1.6.1 chooses its BEHZ bases (`bfvrns-cryptoparameters.cpp:672-695`): `B` is the `k`
primes `≡ 1 (mod 2N)` below the last ciphertext modulus (`PreviousPrime`), `msk` the next one
below, enlarged (`FirstPrime`/`NextPrime` of one more bit) while `B·msk < 2N·t·Q`; `m̃ = 2¹⁶`. The
ciphertext moduli below are the moduli of two RECORDED OpenFHE runs with `BEHZ`; the bases are
the RULE APPLIED to them by a script outside the repository (OpenFHE does not export them), not
recorded values. -/

/-- Recorded OpenFHE BEHZ run: `N = 8192`, `t = 65537`, three 60-bit moduli. -/
def openfheQs8 : List ℕ := [1152921504606830593, 1152921504606748673, 1152921504606683137]
/-- OpenFHE's rule applied to `openfheQs8`: `B`. -/
def openfheAuxB8 : List ℕ := [1152921504606601217, 1152921504606584833, 1152921504606109697]
/-- OpenFHE's rule applied to `openfheQs8`: `msk`. -/
def openfheMsk8 : ℕ := 1152921504605962241
/-- Recorded OpenFHE BEHZ run: `N = 16384`, `t = 68718428161`, four 60-bit moduli. -/
def openfheQs16 : List ℕ :=
  [1152921504606748673, 1152921504606683137, 1152921504606584833, 1152921504605962241]
/-- OpenFHE's rule applied to `openfheQs16`: `B`. -/
def openfheAuxB16 : List ℕ :=
  [1152921504604979201, 1152921504600260609, 1152921504599080961, 1152921504598720513]
/-- OpenFHE's rule applied to `openfheQs16`: `msk`. -/
def openfheMsk16 : ℕ := 1152921504597114881

/-- **OpenFHE's parameterisation at two recorded parameter sets** passes both the side condition
of the family (`behzAuxOK?`) and OpenFHE's own machine-word condition (`behzWordOK?`), with
`m̃ = 2¹⁶`; `Challenge.BFVMul.stepOK_mul_behz` then applies at these bases. -/
theorem openfhe_behzOK :
    (behzAuxOK? 65537 8192 openfheQs8 openfheAuxB8 openfheMsk8 (2 ^ 16) &&
      behzWordOK? 65537 8192 openfheQs8 openfheAuxB8 openfheMsk8 (2 ^ 16)) = true ∧
    (behzAuxOK? 68718428161 16384 openfheQs16 openfheAuxB16 openfheMsk16 (2 ^ 16) &&
      behzWordOK? 68718428161 16384 openfheQs16 openfheAuxB16 openfheMsk16 (2 ^ 16)) = true :=
  sorry

-- OpenFHE's own sizing test (`B·msk ≥ 2N·t·Q`) holds without enlarging `msk`, and the slacks.
#guard decide (2 * 8192 * 65537 * openfheQs8.prod ≤ openfheAuxB8.prod * openfheMsk8)
#guard BudgetBFV.behzSlack 65537 8192 openfheQs8.prod openfheAuxB8.prod openfheMsk8 3 3 (2 ^ 16)
  == ⟨93536104789155190132496402403383005297627572142064, 6, true⟩
-- One auxiliary prime fewer is rejected.
#guard !behzAuxOK? 65537 8192 openfheQs8 (openfheAuxB8.take 2) openfheMsk8 (2 ^ 16)

end Challenge.Families
