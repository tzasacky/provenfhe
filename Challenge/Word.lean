import Challenge.BFVMul.Float

/-!
# Challenge.Word — the machine-word side condition of OpenFHE's key switching   (LOCKED definitions and statements; proofs in `Validation/Word.lean`)

The key-switching statements (`Challenge/Realize/OpenFHE.lean`, `Challenge/Realize/OpenFHEBFV.lean`)
transcribe OpenFHE v1.6.1's hybrid key switching with exact integers. The library computes the
transcription only if its 64-bit word arithmetic does. This file states the one precondition of
hybrid key switching on the machine-word level that the other checks of the certificate do not
cover, and proves that it suffices.

Source: upstream OpenFHE v1.6.1, commit `b59e1f291965f14fbee5172cd83a20f5b856204f`;
`dcrtpoly-impl.h` is `src/core/include/lattice/hal/default/dcrtpoly-impl.h`. `NATIVEINT == 64`
with `HAVE_INT128` and OpenMP (the default build, `harness/frontend/openfhe/build_openfhe.sh`).

**The word step.** `DCRTPolyImpl::ApproxSwitchCRTBasis` (`dcrtpoly-impl.h:938-985`, the branch of
`:946-947`) is the base conversion of hybrid key switching: `ApproxModUp` of every digit from its
moduli to the other ciphertext moduli and the special moduli (`:987-1017`, from
`keyswitch-hybrid.cpp`), and `ApproxModDown` from the special moduli to the ciphertext moduli
(`:1019-1054`). For each coefficient and each target modulus `p` it adds, WITHOUT reduction, one
product `xᵢ · [Q̂ᵢ]_p` per source modulus `qᵢ` into an `unsigned __int128` (`sum[j] += Mul128(…)`,
`:957-962`), with `xᵢ < qᵢ` (the output of the Shoup multiplication, `:959`) and `[Q̂ᵢ]_p < p`,
and reduces only at the end (`BarrettUint128ModUint64`, `:965`). The sum is exact iff it stays
below `2¹²⁸` (at 60-bit moduli, more than 256 source moduli can exceed it); `ksWordOK?` below
excludes that.

**The condition** (`ksWordOK? qs ps`, `qs` the ciphertext moduli, `ps` the special moduli):
every modulus is in `[2, 2⁶⁰)` (OpenFHE's `MAX_MODULUS_SIZE64`, `basicint.h:40`, which its
Barrett (`ModMul` with `mu`) and Shoup (`ModMulFastConst`, signed result) routines assume), and
for every target modulus `p` of a conversion, `Σ_{q ∈ src} (q − 1) · (p − 1) < 2¹²⁸`, with
`src = qs` for `ApproxModUp` (every digit is a sublist of `qs`; its targets are in `qs ++ ps`)
and `src = ps` for `ApproxModDown` (targets in `qs`).

**What is proved and what is argued.** Proved (`modUp_acc_no_overflow`,
`modDown_acc_no_overflow`): under `ksWordOK?` the unreduced sum of every conversion is below
`2¹²⁸`, for every digit and every reduced input. Argued, not proved: that the Shoup and Barrett
steps around it compute residues given the moduli below `2⁶⁰`.
-/

namespace Challenge.Word

/-- One unreduced accumulation of `ApproxSwitchCRTBasis` from the source moduli `src` into the
target modulus `p` stays below `2¹²⁸` in the worst case: `Σ_{q ∈ src} (q − 1)·(p − 1) < 2¹²⁸`. -/
def accOK? (src : List ℕ) (p : ℕ) : Bool :=
  decide ((src.map (· - 1)).sum * (p - 1) < 2 ^ 128)

/-- **The machine-word side condition of OpenFHE's hybrid key switching** (module docstring):
every modulus in `[2, 2⁶⁰)`, every `ApproxModUp` accumulation (source `qs`, targets `qs ++ ps`)
and every `ApproxModDown` accumulation (source `ps`, targets `qs`) below `2¹²⁸`. -/
def ksWordOK? (qs ps : List ℕ) : Bool :=
  (qs ++ ps).all (fun m => decide (2 ≤ m) && decide (m < 2 ^ 60)) &&
  (qs ++ ps).all (fun p => accOK? qs p) && qs.all (fun q => accOK? ps q)

/-- **`ApproxModUp` cannot wrap** under `ksWordOK?`: for every digit `d` (a sublist of the
ciphertext moduli), every target modulus `p` (a ciphertext or special modulus), reduced digit
residues `x` and table entries `c` below `p`, the unreduced sum `Σ xᵢ·cᵢ` is below `2¹²⁸`. -/
theorem modUp_acc_no_overflow (qs ps : List ℕ) (h : ksWordOK? qs ps = true)
    (d : List ℕ) (hd : d.Sublist qs) (p : ℕ) (hp : p ∈ qs ++ ps)
    (x c : List ℕ) (hx : List.Forall₂ (· < ·) x d) (hc : ∀ v ∈ c, v < p) :
    (List.zipWith (· * ·) x c).sum < 2 ^ 128 := sorry

/-- **`ApproxModDown` cannot wrap** under `ksWordOK?`: from the special moduli into every
ciphertext modulus `q`. -/
theorem modDown_acc_no_overflow (qs ps : List ℕ) (h : ksWordOK? qs ps = true)
    (q : ℕ) (hq : q ∈ qs) (x c : List ℕ) (hx : List.Forall₂ (· < ·) x ps) (hc : ∀ v ∈ c, v < q) :
    (List.zipWith (· * ·) x c).sum < 2 ^ 128 := sorry

/-- **The condition is needed**: 257 source moduli `2⁶⁰ − 1` fail it, and reduced residues and
table entries `2⁶⁰ − 2` over them make the unreduced sum reach `2¹²⁸`. -/
theorem acc_wraps_without :
    ksWordOK? (List.replicate 257 (2 ^ 60 - 1)) [] = false ∧
      2 ^ 128 ≤ (List.zipWith (· * ·) (List.replicate 257 (2 ^ 60 - 2))
        (List.replicate 257 (2 ^ 60 - 2))).sum := sorry

/-! ## Checks -/

-- OpenFHE-sized: 30 ciphertext moduli and 10 special moduli just below 2^60 pass.
#guard ksWordOK? (List.replicate 30 (2 ^ 60 - 93)) (List.replicate 10 (2 ^ 60 - 173))
-- a modulus at 2^60, and 1001 moduli of 60 bits (depth 1000, OpenFHE's limit), fail.
#guard !ksWordOK? [2 ^ 60 + 1] []
#guard !ksWordOK? (List.replicate 1001 (2 ^ 60 - 93)) [2 ^ 60 - 173]
-- the special side alone: 300 special moduli of 60 bits fail on the ModDown sum.
#guard !ksWordOK? [2 ^ 60 - 93] (List.replicate 300 (2 ^ 60 - 173))

end Challenge.Word
