import Spec.BudgetBFV

/-!
# Spec.CertifyBFV — what a BFV certificate is decided from, and what it contains   (TRUSTED)

The data of the decision `Challenge.CertifyBFV.certifyBFV?` (a locked definition: it runs the
locked reference analyzer `Challenge.BFV.refAnalyzeBFVAt`, so it cannot live here): its input
(`InputBFV`: parameters, key-switching layout, program, the declared multiplication technique with
its auxiliary data, the plaintext-addition and modulus-switching methods, the internal drops) and its result
(`CertificateBFV`), with the hypotheses a certificate can record (`AssumptionBFV`). Nothing here
is a claim; the statements are in `Challenge.CertifyBFV`. This mirrors `Spec.Certify` for BGV.
-/

namespace Spec.CertifyBFV
open Spec Spec.Source


/-- The multiplication technique the library runs, with its auxiliary data. -/
inductive Technique
  /-- Fan–Vercauteren: centred lift, integer tensor product, exact rounding of `t·c/Q`. -/
  | textbook
  /-- Halevi–Polyakov–Shoup (OpenFHE `HPS`), with the auxiliary basis `R`. -/
  | hps (R : List ℕ)
  /-- OpenFHE `HPSPOVERQ`: the auxiliary primes `P_ℓ` are the first `ℓ` entries of `Ps`. -/
  | poverq (Ps : List ℕ)
  /-- OpenFHE `HPSPOVERQLEVELED`: as `poverq`, and inside a multiplication or a key switch of a
  ciphertext at the top level the library may drop limbs internally; how many, at each
  instruction, is `InputBFV.drops`. -/
  | leveled (Ps : List ℕ)
  /-- Bajard–Eynard–Hasan–Zucca (OpenFHE `BEHZ`): base `B`, extra modulus `msk`, Montgomery
  modulus `mt`. -/
  | behz (B : List ℕ) (msk mt : ℕ)
  deriving DecidableEq, Repr

/-- How the library adds a plaintext `p`: exactly `⌊Q/t⌋·p`, `⌊Q·p/t⌉`, or any polynomial within
one unit of `Q·p/t`. -/
inductive PlainAddMethod
  | delta
  | rounded
  | scaled
  deriving DecidableEq, Repr

/-- What `certifyBFV?` decides about: the decoded data, nothing else. -/
structure InputBFV where
  P : FullParams
  lay : Budget.KSLayout
  prog : Program
  /-- The declared multiplication technique (`none`: nothing declared). -/
  mul : Option Technique
  /-- The slacks of the HPS family include the binary64 tolerances (`Spec.BudgetBFV.doubleSw`,
  `doubleSr`): the budget is that of the library's floating-point code. `false`: the budget of
  the idealised exact algorithms, which the library does not run. -/
  floatTol : Bool
  /-- The declared plaintext-addition method (`none`: nothing declared). -/
  plainAdd : Option PlainAddMethod
  /-- Modulus switching rounds every component (`c ↦ ⌊c/q_last⌉`). -/
  msRound : Bool
  /-- `HPSPOVERQLEVELED` only: for each instruction of the body, in order, the number of limbs the
  library drops internally at it (the value its `FindLevelsToDrop` returns inside `EvalMult`,
  `EvalSquare` and `RelinearizeCore`: the calls at `bfvrns-leveledshe.cpp:271`, `:491`, `:874`, in
  the branches that start at `:263`, `:485`, `:869`, in OpenFHE
  v1.6.1; `0` at every other instruction). `certifyBFV?` requires one entry per instruction
  under `HPSPOVERQLEVELED` and ignores the list otherwise. -/
  drops : List ℕ := []

/-- A hypothesis a certificate's realizability rests on beyond the locked pins: a condition on
the platform under which realizability is PROVED. (Until the key switch after an internal drop
was proved, `Challenge.BFVMul.KSLeveled`, a second constructor `ksLeveled` recorded it as an
unproved claim.) -/
inductive AssumptionBFV
  /-- The binary64 steps of the multiplication, and of the scaling inside a key switch of
  `HPSPOVERQLEVELED`, are computed by an arithmetic conforming to the standard model
  `Spec.Float.Conforms` (IEEE binary64, round to nearest, no value-changing optimisation:
  `Spec/Float.lean`). Under it the library's HPS-family multiplication and its key switch with
  an internal drop are proved to meet their contracts at the budget (`Challenge.CertifyBFV`, the
  `…_float` statements and `certifyBFV?_leveled_relin`, `_leveled_keySwitch`); that a given
  build conforms is not something a proof can establish. -/
  | binary64
  /-- The budget is that of the IDEALISED exact algorithms (`floatTol = false`): the HPS-family
  multiplication, or the scaling inside a key switch of `HPSPOVERQLEVELED` with an internal drop,
  computed without the library's binary64 rounding. The realizability statements then hold for
  those idealised algorithms, which OpenFHE does not run; a certificate recording this is NOT
  about the library's code. Recorded exactly where `binary64` would be recorded with
  `floatTol = true`. -/
  | idealised
  /-- `HPSPOVERQLEVELED` with a multiplication or key switch of a top-level operand: the budget
  of each such instruction is computed for the internal drop the frontend declared there
  (`InputBFV.drops`), which is not checked (OpenFHE's `FindLevelsToDrop` is not modelled); the
  certificate is about runs in which the library drops exactly those limbs. -/
  | declaredDrops
  /-- The library's own decryption of the outputs (`PKEBFVRNS::Decrypt`, the routines transcribed
  in `Spec.DecryptBFVLib`) computes its binary64 steps by an arithmetic conforming to the standard
  model `Spec.DecryptBFV.ConformsD` (IEEE binary64, round to nearest, one rounding per operation,
  no value-changing optimisation: `Spec/DecryptBFV.lean`). The statement about the library's
  decryption (`Challenge.BFVDecryptLib.certifyBFV?_decryptsLibExt`) holds for every conforming
  arithmetic; that a given build conforms is not something a proof can establish. Recorded
  exactly when the declared technique is one of OpenFHE's four (HPS, HPSPOVERQ,
  HPSPOVERQLEVELED, BEHZ), i.e. exactly when that statement applies to the certificate, whatever
  `floatTol` says (the hypothesis is about decryption, not about the budget). -/
  | binary64Dec
  deriving DecidableEq, Repr

/-- What `certifyBFV?` returns. -/
structure CertificateBFV where
  /-- The budget the analysis was run at, one per instruction: `budgetBFV x`; `budget k` is
  the budget of instruction `k` of the body. -/
  budget : ℕ → TraceBFV.Budget
  /-- What `refAnalyzeBFVAt` returns on the whole program. -/
  bound : ℕ
  /-- Each output, in order, with what `refAnalyzeBFVAt` returns on the program with that output
  alone. -/
  outputs : List (Var × ℕ)
  /-- The levels at which the program multiplies (`mulLevels`). -/
  mulLevels : List ℕ
  /-- What realizability rests on beyond the locked pins (`assumptionsOf x`): `binary64` (a
  hypothesis on the platform) or `idealised` (the budget is the idealised exact algorithm's, not
  the library's), `declaredDrops`, and `binary64Dec` (the library's decryption conforms to
  `Spec.DecryptBFV.ConformsD`; recorded for every technique of OpenFHE's). With neither
  `binary64` nor `idealised`: the multiplication and key switching of the declared technique are
  proved at the budget with no hypothesis on the platform (textbook, BEHZ, or the HPS family on a
  program where no binary64 step is involved); the declared inputs themselves (technique,
  methods, bounds, drops, layout) are still assumptions: `Challenge.CertifyBFV`, module
  docstring. -/
  assumed : List AssumptionBFV

end Spec.CertifyBFV
