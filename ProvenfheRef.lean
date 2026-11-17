import FHE.Ref.BFV
import Challenge.IndCpaD.LM

/-!
# provenfhe_ref — run the proved reference BGV and BFV end to end
(UNTRUSTED glue around functions proved equal to the locked definitions)

    provenfhe_ref [bgv|bfv|all|profile] [SEEDS] [FIRST_SEED] [LOGN]

`LOGN` (default 13) selects the ring dimension. At `LOGN = 13` the parameters are exactly those
of the locked concrete theorems: `bgvKSSeal` (`correct_ksEval_bgvKSSeal`) and `sealBFV`
(`correct_lm_bfvSeal`): N = 8192, four 43–44-bit primes, one special prime, t = 65537. At any other
`LOGN` they are the same moduli with `N := 2^LOGN`; then only the generic theorems apply
(`correct_ksEval`, `correct_bfvEval`), and their side conditions (encryption hypothesis, class
membership) are decided here by compiled code, not by the kernel.

For each scheme and seed: sample a secret, the public-key error, the uniform parts, the key errors
and the encryption randomness from a seeded splitmix64 generator; check that they satisfy the
hypotheses of `keyGen_keysOK` / `bfvKeyGen_keysOK` and `GoodE`; generate the keys (public key,
relinearization keys, rotation keys for g = 5) with `FHE.Ref.keyGenA` / `bfvKeyGenA`; encrypt
random messages; check that each circuit is in the locked class (`ksClass`, `bfvClass`, `admLM`)
and refuse it otherwise; evaluate it with `FHE.Ref.ksEvalA` / `bfvEvalA`; decrypt (textbook);
compare with what the circuit computes (`sem`, through `FHE.Ref.semA`). Every function on that path
except the driver's sampling, timing and array comparison is proved equal to the locked definition
it implements (`FHE/Ref/*.lean`). Exit code 1 on any mismatch, any violated bound, or any class
verdict other than the expected one. The generator is a test harness: the theorems hold for every
key and randomness within the bounds, which are checked before use.
-/

open Spec Spec.NPoly Spec.Source Spec.IndCpaDProfile Spec.IndCpaDLM FHE.Pin FHE.Ref
  Challenge.IndCpaDProfile Challenge.IndCpaDLM

/-! ## Seeded generator (splitmix64) -/

def mix64 (z : UInt64) : UInt64 :=
  let z := (z ^^^ (z >>> 30)) * 0xbf58476d1ce4e5b9
  let z := (z ^^^ (z >>> 27)) * 0x94d049bb133111eb
  z ^^^ (z >>> 31)

def next64 (r : IO.Ref UInt64) : IO UInt64 := do
  let s := (← r.get) + 0x9e3779b97f4a7c15
  r.set s
  return mix64 s

/-- `N` coefficients in `[-B, B]`. -/
def sampleSmall (r : IO.Ref UInt64) (N B : ℕ) : IO (Array ℤ) := do
  let mut a := Array.mkEmpty N
  for _ in [0:N] do
    let x := (← next64 r).toNat % (2 * B + 1)
    a := a.push ((x : ℤ) - B)
  return a

/-- `N` coefficients in `[0, M)` (reduced from `⌊log₂ M / 64⌋ + 2` words). -/
def sampleUniform (r : IO.Ref UInt64) (N M : ℕ) : IO (Array ℤ) := do
  let words := M.log2 / 64 + 2
  let mut a := Array.mkEmpty N
  for _ in [0:N] do
    let mut x : ℕ := 0
    for _ in [0:words] do
      x := x * 2 ^ 64 + (← next64 r).toNat
    a := a.push ((x % M : ℕ) : ℤ)
  return a

def sampleMsg (r : IO.Ref UInt64) (N t : ℕ) : IO (Array (ZMod t)) := do
  let mut a := Array.mkEmpty N
  for _ in [0:N] do
    a := a.push (((← next64 r).toNat % t : ℕ) : ZMod t)
  return a

def sampleList (k : ℕ) (f : IO (Array ℤ)) : IO (List (Array ℤ)) := do
  let mut l := []
  for _ in [0:k] do
    l := l ++ [← f]
  return l

/-! ## Timing -/

/-- Evaluate `f ()` when the action runs (`@[noinline]`: not moved across the clock reads). -/
@[noinline] def runPure {α : Type} (f : Unit → α) : IO α := pure (f ())

def nowMs : IO Float := do return (← IO.monoNanosNow).toFloat / 1.0e6

def timed {α : Type} (f : Unit → α) : IO (α × Float) := do
  let t0 ← nowMs
  let r ← runPure f
  let t1 ← nowMs
  return (r, t1 - t0)

def fmt (x : Float) : String := toString ((x * 10).round / 10)

/-! ## Checks -/

/-- `normInf` (trusted) of the polynomial an array stands for. -/
def nrm (N : ℕ) (a : Array ℤ) : ℕ := normInf (ofArr a : IntPoly N)

/-- `∀ j, ok (normInf ((l.map ofArr).getD j 0))`: indices past the end read `0`, so checking
`j ≤ l.length` decides the universal statement. -/
def allKeyErr (N : ℕ) (l : List (Array ℤ)) (ok : ℕ → Bool) : Bool :=
  (List.range (l.length + 1)).all fun j => ok (normInf ((l.map (ofArr (N := N))).getD j 0))

def eqArr {t : ℕ} (N : ℕ) (a b : Array (ZMod t)) : Bool :=
  a.size == N && b.size == N && (List.range N).all fun i => a[i]! == b[i]!

/-- Per-phase timings collected over the run (for the summary). -/
abbrev Stats := IO.Ref (List (String × Float))

def record (st : Stats) (k : String) (v : Float) : IO Unit := st.modify ((k, v) :: ·)

/-! ## A circuit run, either scheme -/

/-- Everything one circuit run needs from a scheme instance. -/
structure Inst (t N : ℕ) where
  tag : String
  eval : (Program × List Var × (Var → Poly t N)) → List (ℕ × List (Array ℤ)) →
    List (ℕ × List (Array ℤ))
  dec : ℕ × List (Array ℤ) → Array (ZMod t)
  sem : (Program × List Var × (Var → Poly t N)) → List (Poly t N) → List (Poly t N)

/-- Class verdict, then (if accepted) evaluation, decryption, `sem`, comparison. -/
def runCircuit {t N : ℕ} (I : Inst t N) (st : Stats) (fail : IO.Ref Bool) (seed : ℕ) (name : String)
    (adm : Bool) (C : Program × List Var × (Var → Poly t N)) (inputs : List (Array (ZMod t)))
    (cts : List (ℕ × List (Array ℤ))) (expectAccept : Bool) (control : Bool := false) :
    IO (List (ℕ × List (Array ℤ))) := do
  let pre := s!"  {I.tag} seed={seed} {name}:"
  if !adm then
    if expectAccept then
      fail.set true; IO.println s!"{pre} class REJECTS (expected accept): FAIL"
    else IO.println s!"{pre} refused by the class, not evaluated: PASS"
    return []
  if !expectAccept then
    fail.set true; IO.println s!"{pre} class ACCEPTS (expected reject): FAIL"
    return []
  let (outs, tEv) ← timed fun _ => I.eval C cts
  let (ds, tDec) ← timed fun _ => outs.map I.dec
  let (es, tSem) ← timed fun _ => (I.sem C (inputs.map fun m => ofArr m)).map (force N)
  let ok := ds.length == es.length && ds.length > 0 && (ds.zip es).all fun (d, e) => eqArr N d e
  unless ok do fail.set true
  record st s!"{I.tag} eval: {name}" tEv
  record st s!"{I.tag} decrypt (one output)" tDec
  record st s!"{I.tag} sem" tSem
  IO.println s!"{pre} eval={fmt tEv}ms decrypt={fmt tDec}ms sem={fmt tSem}ms {if ok then "PASS" else "FAIL"}"
  if control then
    -- the comparison discriminates: `sem` of a perturbed first input differs from the decryption
    let pert := inputs.mapIdx fun k m => if k = 0 then m.modify 0 (· + 1) else m
    let es' := (I.sem C (pert.map fun m => ofArr m)).map (force N)
    let differs := !((ds.zip es').all fun (d, e) => eqArr N d e)
    unless differs do fail.set true
    IO.println s!"{pre} control: decryption vs sem of a perturbed input differ: {if differs then "PASS" else "FAIL"}"
  return outs

/-! ## Parameters -/

def bgvAt (logN : ℕ) : FullParams :=
  if logN = 13 then bgvKSSeal
  else { bgvKSSeal with src := { bgvKSSeal.src with N := 2 ^ logN },
                        store := { bgvKSSeal.store with W := 2 ^ logN } }

def bfvAt (logN : ℕ) : FullParams :=
  if logN = 13 then Challenge.BFV.sealBFV
  else
    let P := Challenge.BFV.sealBFV
    { P with src := { P.src with N := 2 ^ logN }, store := { P.store with W := 2 ^ logN } }

/-- At `LOGN = 13` the driver's instances ARE the locked ones (kernel-checked): the data, the class
predicate and the parameters of `correct_ksEval_bgvKSSeal`, `correct_lm_bfvSeal` and the oracle's
class `admSeal` / `admBFVSeal`. -/
example : bgvAt 13 = bgvKSSeal := rfl
example : bfvAt 13 = Challenge.BFV.sealBFV := rfl
example : bgvKSData (bgvAt 13) bgvKSLayout [5] 21 1 21 21 = bgvKSSealData := rfl
example : bfvKSData (bfvAt 13) bfvSealLayout [5] 21 1 21 21 = bfvSealData := rfl
example : ksClass (bgvKSData (bgvAt 13) bgvKSLayout [5] 21 1 21 21) bgvKSLayout [5]
    (fun _ => Spec.Budget.certified (bgvAt 13) bgvKSLayout) = admSeal := rfl
example : bfvClass (bfvKSData (bfvAt 13) bfvSealLayout [5] 21 1 21 21) bfvSealLayout [5]
    (Spec.BudgetBFV.certified (bfvAt 13) bfvSealLayout) = admBFVSeal := rfl

/-! ## BGV -/

def bgvSeed (P : FullParams) (st : Stats) (seed : ℕ) (fail : IO.Ref Bool) : IO Unit := do
  let lay := bgvKSLayout
  -- at `bgvKSSeal` this is `bgvKSSealData` and the profile `bgvKSSealProfile` (definitionally)
  let D : AbsScheme := bgvKSData P lay [5] 21 1 21 21
  let prof : D.Circ → Trace.Budget := fun _ => Spec.Budget.certified P lay
  let adm : D.Circ → Bool := ksClass D lay [5] prof
  let N := P.src.N
  let t := P.src.t
  let L := P.src.qs.length
  let Q := P.src.modulus L
  let QP := Q * Spec.Budget.specialProd P
  let nd := (lay.sizes L).length
  let tag := s!"BGV N={N}"
  -- the hypotheses of `encOK_bgvKSData` (closed; decided in the kernel only at `bgvKSSeal`)
  unless decide (2 ≤ t) && decide (2 * D.eps < Q) do
    fail.set true; IO.println s!"{tag}: encOK_bgvKSData hypotheses fail: FAIL"; return
  let r ← IO.mkRef (UInt64.ofNat (seed * 1000003 + 17))
  let t0 ← nowMs
  let s ← sampleSmall r N 1
  let e ← sampleSmall r N 21
  let a ← sampleUniform r N Q
  let ra ← sampleList nd (sampleUniform r N QP)
  let re ← sampleList nd (sampleSmall r N 21)
  let ga5 ← sampleList nd (sampleUniform r N QP)
  let ge5 ← sampleList nd (sampleSmall r N 21)
  let t1 ← nowMs
  -- the hypotheses of `keyGen_keysOK`: `hs`, `he`, `hre`, `hge` (rots = [5])
  let (hyp, tHyp) ← timed fun _ =>
    decide (nrm N s ≤ P.secretBound) && decide (nrm N e ≤ 21) &&
    allKeyErr N re (fun n => decide (t * n ≤ P.keyNoise) && decide (2 * (t * n) < QP)) &&
    allKeyErr N ge5 (fun n => decide (t * n ≤ P.keyNoise) && decide (2 * (t * n) < QP))
  unless hyp do
    fail.set true; IO.println s!"{tag} seed={seed}: sampled keys violate keyGen_keysOK's bounds: FAIL"; return
  let ga : ℕ → List (Array ℤ) := fun g => if g = 5 then ga5 else []
  let ge : ℕ → List (Array ℤ) := fun g => if g = 5 then ge5 else []
  let (pk0, tKg) ← timed fun _ => keyGenA P lay s e a ra re ga ge
  -- the rotation keys for g = 5, computed now; `memoAt_eq`: the same function
  let (tbl, tRot) ← timed fun _ => [5].map pk0.2.2.2
  let pk : KSPKA := (pk0.1, pk0.2.1, pk0.2.2.1, memoAt [5] tbl pk0.2.2.2)
  record st "BGV keygen (pk + relin keys)" tKg; record st "BGV keygen (rotation keys g=5)" tRot
  IO.println s!"{tag} seed={seed} sample={fmt (t1 - t0)}ms bounds-check={fmt tHyp}ms keygen(pk+relin)={fmt tKg}ms keygen(rot g=5)={fmt tRot}ms"
  -- encryption (`encBGVA_eq`), randomness checked against `GoodE`
  let enc : Array (ZMod t) → IO (ℕ × List (Array ℤ)) := fun m => do
    let u ← sampleSmall r N 1
    let e1 ← sampleSmall r N 21
    let e2 ← sampleSmall r N 21
    unless nrm N u ≤ 1 && nrm N e1 ≤ 21 && nrm N e2 ≤ 21 do
      fail.set true; throw (IO.userError "encryption randomness violates GoodE")
    runPure fun _ => (L, encA N t pk.1 pk.2.1 (force N (Spec.Encrypt.liftMsg (ofArr m : Poly t N))) u e1 e2)
  let ma ← sampleMsg r N t
  let mb ← sampleMsg r N t
  let t2 ← nowMs
  let ca ← enc ma
  let cb ← enc mb
  let t3 ← nowMs
  record st "BGV encrypt (one)" ((t3 - t2) / 2)
  IO.println s!"  {tag} seed={seed} encrypt x2={fmt (t3 - t2)}ms"
  let I : Inst t N :=
    { tag, eval := fun C cs => ksEvalA D lay pk.2.2.1 pk.2.2.2 C cs, dec := decBGVA D s, sem := semA D }
  -- 1. `bgvKSSealCirc` (`ksClass_bgvKSSeal`, kernel-checked at N = 2^13)
  let C1 : D.Circ := (bgvKSSealCirc.1, bgvKSSealCirc.2.1, fun _ => 0)
  let (a1, tC) ← timed fun _ => adm C1
  record st "BGV class check" tC
  let _ ← runCircuit I st fail seed "bgvKSSealCirc [mul,relin,automorph 5,keySwitch,modSwitch,addPlain]"
    a1 C1 [ma, mb] [ca, cb] true (control := true)
  -- 2. the same program with a random plaintext constant (class: compiled check)
  let mp ← sampleMsg r N t
  let C2 : D.Circ := (bgvKSSealCirc.1, bgvKSSealCirc.2.1, fun _ => ofArr mp)
  let _ ← runCircuit I st fail seed "same, random plaintext constant" (adm C2) C2 [ma, mb] [ca, cb] true
  -- 3. the two-stage example (`lm_two_stage_kernel` at N = 2^13): stage 2 on stage 1's OUTPUT
  let mk : Program → List Var → (Var → M D) → D.Circ := fun p f c => (p, f, c)
  let G0 : Global D := ((Global.empty D).link "a").link "b"
  let S1 : D.Circ := (lmStage1.1, lmStage1.2.1, fun _ => 0)
  let S2 : D.Circ := (lmStage2.1, lmStage2.2.1, fun _ => 0)
  let o1 ← runCircuit I st fail seed "two-stage, stage 1 [mul,relin]"
    (admLM mk adm G0 S1 [("a", true), ("b", true)]) S1 [ma, mb] [ca, cb] true
  let mc := force N ((semA D S1 [ofArr ma, ofArr mb]).headD 0)
  let _ ← runCircuit I st fail seed "two-stage, stage 2 on stage 1's output [automorph 5,keySwitch,modSwitch]"
    (admLM mk adm (G0.extend S1) S2 [("c", true)]) S2 [mc] o1 true
  -- negative controls: refused, never evaluated
  let _ ← runCircuit I st fail seed "NEG rotation keys for g=3 only (the #guard of ProfileBGVKS)"
    (ksClass D lay [3] prof C1) C1 [ma, mb] [ca, cb] false
  let _ ← runCircuit I st fail seed "NEG stage 2 declares its entry at level 3 (lm_reject_kernel.1)"
    (admLM mk adm (G0.extend S1) ({ S2.1 with inputs := [{ sealDecl "c" with level := 3 }] }, ["c"], fun _ => 0)
      [("c", true)]) S2 [mc] o1 false
  let _ ← runCircuit I st fail seed "NEG stage 2 overwrites a global name (lm_reject_kernel.2)"
    (admLM mk adm (G0.extend S1) ({ S2.1 with body := S2.1.body ++ [.copy "a" "m"] }, ["c"], fun _ => 0)
      [("c", true)]) S2 [mc] o1 false
  let _ ← runCircuit I st fail seed "NEG unlinked entry (lm_reject_kernel.3)"
    (admLM mk adm (G0.extend S1) S2 [("c", false)]) S2 [mc] o1 false

/-! ## BFV -/

/-- The two BFV stages inlined into one program over the fresh entries. -/
def bfvInlineProg : Program :=
  { inputs := [bfvSealDecl "a", bfvSealDecl "b"], body := bfvStage1.1.body ++ bfvStage2.1.body,
    outputs := ["m"] }

/-- The inlined program followed by a plaintext addition and a plaintext product at level 3. -/
def bfvPlainProg : Program :=
  { inputs := [bfvSealDecl "a", bfvSealDecl "b", ⟨"p", 1, 3, 0, 1⟩, ⟨"q", 1, 3, 0, 1⟩],
    body := bfvStage1.1.body ++ bfvStage2.1.body ++ [.addPlain "o" "m" "p", .mulPlain "o2" "o" "q"],
    outputs := ["o2"] }

def bfvSeed (P : FullParams) (st : Stats) (seed : ℕ) (fail : IO.Ref Bool) : IO Unit := do
  let lay := bfvSealLayout
  -- at `sealBFV` this is `bfvSealData`, `bfvSealBudget` and `admBFVSeal` (definitionally)
  let D : AbsScheme := bfvKSData P lay [5] 21 1 21 21
  let E := Spec.BudgetBFV.certified P lay
  let adm : D.Circ → Bool := bfvClass D lay [5] E
  let N := P.src.N
  let t := P.src.t
  let L := P.src.qs.length
  let Q := P.src.modulus L
  let Sp := Spec.Budget.specialProd P
  let levels := (List.range L).map (· + 1)
  let nd : ℕ → ℕ := fun ℓ => (lay.sizes ℓ).length
  let tag := s!"BFV N={N}"
  -- the hypotheses of `encOK_bfvKSData` (closed; decided in the kernel only at `sealBFV`)
  unless decide (2 ≤ t) && Challenge.BFV.decOK t Q D.eps do
    fail.set true; IO.println s!"{tag}: encOK_bfvKSData hypotheses fail: FAIL"; return
  let r ← IO.mkRef (UInt64.ofNat (seed * 1000033 + 29))
  let t0 ← nowMs
  let s ← sampleSmall r N 1
  let e ← sampleSmall r N 21
  let a ← sampleUniform r N Q
  let mut raT : List (List (Array ℤ)) := []
  let mut reT : List (List (Array ℤ)) := []
  let mut gaT : List (List (Array ℤ)) := []
  let mut geT : List (List (Array ℤ)) := []
  for ℓ in levels do
    raT := raT ++ [← sampleList (nd ℓ) (sampleUniform r N (P.src.modulus ℓ * Sp))]
    reT := reT ++ [← sampleList (nd ℓ) (sampleSmall r N 21)]
    gaT := gaT ++ [← sampleList (nd ℓ) (sampleUniform r N (P.src.modulus ℓ * Sp))]
    geT := geT ++ [← sampleList (nd ℓ) (sampleSmall r N 21)]
  let t1 ← nowMs
  let lv : List (List (Array ℤ)) → ℕ → List (Array ℤ) := fun T ℓ => if 1 ≤ ℓ then T.getD (ℓ - 1) [] else []
  let ra := lv raT
  let re := lv reT
  let ga : ℕ → ℕ → List (Array ℤ) := fun g ℓ => if g = 5 then lv gaT ℓ else []
  let ge : ℕ → ℕ → List (Array ℤ) := fun g ℓ => if g = 5 then lv geT ℓ else []
  -- the hypotheses of `bfvKeyGen_keysOK`: `hk`, `hs`, `he`, `hre`, `hge` (levels past the chain
  -- and `ℓ = 0` read `[]`, i.e. zero errors, so `ℓ ≤ L + 1` decides `∀ ℓ`)
  let (hyp, tHyp) ← timed fun _ =>
    decide (P.src.kind = .bfv) && decide (nrm N s ≤ P.secretBound) && decide (nrm N e ≤ 21) &&
    (List.range (L + 2)).all (fun ℓ =>
      allKeyErr N (re ℓ) (fun n => decide (n ≤ P.keyNoise) && decide (2 * n < P.src.modulus ℓ * Sp)) &&
      allKeyErr N (ge 5 ℓ) (fun n => decide (n ≤ P.keyNoise) && decide (2 * n < P.src.modulus ℓ * Sp)))
  unless hyp do
    fail.set true; IO.println s!"{tag} seed={seed}: sampled keys violate bfvKeyGen_keysOK's bounds: FAIL"; return
  let (pk0, tKg) ← timed fun _ => bfvKeyGenA P lay s e a ra re ga ge
  -- relinearization keys at every level and rotation keys for g = 5 at every level, computed
  -- now; `memoAt_eq`: the same functions
  let (rkT, tRk) ← timed fun _ => levels.map pk0.2.2.1
  let (gkT, tGk) ← timed fun _ => levels.map (pk0.2.2.2 5)
  let pk : BFVPKA := (pk0.1, pk0.2.1, memoAt levels rkT pk0.2.2.1,
    memoAt [5] [memoAt levels gkT (pk0.2.2.2 5)] pk0.2.2.2)
  record st "BFV keygen (pk)" tKg; record st "BFV keygen (relin keys, 4 levels)" tRk
  record st "BFV keygen (rotation keys g=5, 4 levels)" tGk
  IO.println s!"{tag} seed={seed} sample={fmt (t1 - t0)}ms bounds-check={fmt tHyp}ms keygen(pk)={fmt tKg}ms keygen(relin x4 levels)={fmt tRk}ms keygen(rot g=5 x4 levels)={fmt tGk}ms"
  let enc : Array (ZMod t) → IO (ℕ × List (Array ℤ)) := fun m => do
    let u ← sampleSmall r N 1
    let e1 ← sampleSmall r N 21
    let e2 ← sampleSmall r N 21
    unless nrm N u ≤ 1 && nrm N e1 ≤ 21 && nrm N e2 ≤ 21 do
      fail.set true; throw (IO.userError "encryption randomness violates GoodE")
    runPure fun _ => (L, encBFVA N t Q pk.1 pk.2.1 (force N (Spec.Encrypt.liftMsg (ofArr m : Poly t N))) u e1 e2)
  let ma ← sampleMsg r N t
  let mb ← sampleMsg r N t
  let t2 ← nowMs
  let ca ← enc ma
  let cb ← enc mb
  let t3 ← nowMs
  record st "BFV encrypt (one)" ((t3 - t2) / 2)
  IO.println s!"  {tag} seed={seed} encrypt x2={fmt (t3 - t2)}ms"
  let I : Inst t N :=
    { tag, eval := fun C cs => bfvEvalA D lay pk.2.2.1 pk.2.2.2 C cs, dec := decBFVA D s, sem := semA D }
  -- 1. the two stages inlined (class: compiled check)
  let C1 : D.Circ := (bfvInlineProg, ["a", "b"], fun _ => 0)
  let (a1, tC) ← timed fun _ => adm C1
  record st "BFV class check" tC
  let _ ← runCircuit I st fail seed "stages inlined [mul,relin,automorph 5,keySwitch,modSwitch]" a1 C1
    [ma, mb] [ca, cb] true (control := true)
  -- 2. with a plaintext addition and a plaintext product (random constants; compiled check)
  let mp ← sampleMsg r N t
  let mq ← sampleMsg r N t
  let C2 : D.Circ := (bfvPlainProg, ["a", "b"], fun x => if x = "p" then ofArr mp else ofArr mq)
  let _ ← runCircuit I st fail seed "inlined + addPlain + mulPlain" (adm C2) C2 [ma, mb] [ca, cb] true
  -- 3. the two-stage example (`lm_two_stage_bfv_kernel` at N = 2^13)
  let mk : Program → List Var → (Var → M D) → D.Circ := fun p f c => (p, f, c)
  let G0 : Global D := ((Global.empty D).link "a").link "b"
  let S1 : D.Circ := (bfvStage1.1, bfvStage1.2.1, fun _ => 0)
  let S2 : D.Circ := (bfvStage2.1, bfvStage2.2.1, fun _ => 0)
  let o1 ← runCircuit I st fail seed "two-stage, stage 1 [mul,relin]"
    (admLM mk adm G0 S1 [("a", true), ("b", true)]) S1 [ma, mb] [ca, cb] true
  let mc := force N ((semA D S1 [ofArr ma, ofArr mb]).headD 0)
  let _ ← runCircuit I st fail seed "two-stage, stage 2 on stage 1's output [automorph 5,keySwitch,modSwitch]"
    (admLM mk adm (G0.extend S1) S2 [("c", true)]) S2 [mc] o1 true
  -- negative controls (BFV analogues of the BGV kernel-checked rejections; compiled checks)
  let _ ← runCircuit I st fail seed "NEG rotation keys for g=3 only"
    (bfvClass D lay [3] E C1) C1 [ma, mb] [ca, cb] false
  let _ ← runCircuit I st fail seed "NEG stage 2 declares its entry at level 3"
    (admLM mk adm (G0.extend S1) ({ S2.1 with inputs := [{ bfvSealDecl "c" with level := 3 }] }, ["c"], fun _ => 0)
      [("c", true)]) S2 [mc] o1 false
  let _ ← runCircuit I st fail seed "NEG stage 2 overwrites a global name"
    (admLM mk adm (G0.extend S1) ({ S2.1 with body := S2.1.body ++ [.copy "a" "m"] }, ["c"], fun _ => 0)
      [("c", true)]) S2 [mc] o1 false
  let _ ← runCircuit I st fail seed "NEG unlinked entry"
    (admLM mk adm (G0.extend S1) S2 [("c", false)]) S2 [mc] o1 false

/-! ## Per-instruction profile (one key set, BFV inlined program; timing only) -/

def profileBFV (P : FullParams) : IO Unit := do
  let lay := bfvSealLayout
  let D : AbsScheme := bfvKSData P lay [5] 21 1 21 21
  let N := P.src.N
  let L := P.src.qs.length
  let Sp := Spec.Budget.specialProd P
  let r ← IO.mkRef (7 : UInt64)
  let s ← sampleSmall r N 1
  let e ← sampleSmall r N 21
  let a ← sampleUniform r N (P.src.modulus L)
  let ra4 ← sampleList (lay.sizes L).length (sampleUniform r N (P.src.modulus L * Sp))
  let re4 ← sampleList (lay.sizes L).length (sampleSmall r N 21)
  let pk := bfvKeyGenA P lay s e a (fun _ => ra4) (fun _ => re4) (fun _ _ => ra4) (fun _ _ => re4)
  let rk4 := pk.2.2.1 L
  let gk4 := pk.2.2.2 5 L
  let rk : ℕ → List (Array ℤ × Array ℤ) := fun _ => rk4
  let gk : ℕ → ℕ → List (Array ℤ × Array ℤ) := fun _ _ => gk4
  let u ← sampleSmall r N 1
  let c ← runPure fun _ => (L, encBFVA N P.src.t (P.src.modulus L) pk.1 pk.2.1 (zeroA N) u e e)
  let C : D.Circ := (bfvInlineProg, ["a", "b"], fun _ => 0)
  let mut ρ : Env D.P.src := initEnv D.P.src (D.prog C) fun _ => .exact 0
  let mut σ : CtEnvA := initCtA (D.prog C) (ctsA D C [c, c])
  IO.println s!"BFV N={N} time per instruction of the inlined program (one key set reused at every level; timing only)"
  for i in (D.prog C).body do
    let some ρ' := step D.P.src ρ i | IO.println "  replay fails"; return
    let (σ'?, dt) ← timed fun _ => bfvStepA D.Pe lay rk gk ρ σ i
    let some σ' := σ'? | IO.println "  step fails"; return
    IO.println s!"  {repr i}: {fmt dt}ms"
    ρ := ρ'; σ := σ'

def main (args : List String) : IO UInt32 := do
  let which := args.headD "all"
  let seeds := (args.getD 1 "20").toNat?.getD 20
  let first := (args.getD 2 "1").toNat?.getD 1
  let logN := (args.getD 3 "13").toNat?.getD 13
  unless which == "bgv" || which == "bfv" || which == "all" || which == "profile" do
    IO.eprintln "usage: provenfhe_ref [bgv|bfv|all|profile] [SEEDS] [FIRST_SEED] [LOGN]"
    return 2
  if which == "profile" then
    profileBFV (bfvAt logN)
    return 0
  if logN ≠ 13 then
    IO.println s!"N = 2^{logN}: NOT the parameters of the locked concrete theorems; the generic theorems apply, with their side conditions (encryption hypothesis, class membership) decided by compiled code."
  let fail ← IO.mkRef false
  let st : Stats ← IO.mkRef []
  let tStart ← nowMs
  for k in [0:seeds] do
    let seed := first + k
    if which == "bgv" || which == "all" then bgvSeed (bgvAt logN) st seed fail
    if which == "bfv" || which == "all" then bfvSeed (bfvAt logN) st seed fail
  let tEnd ← nowMs
  let rows := (← st.get).reverse
  let keys := rows.foldl (fun acc (k, _) => if acc.contains k then acc else acc ++ [k]) []
  IO.println "summary (ms over all runs):"
  for k in keys do
    let vs := (rows.filter (·.1 == k)).map (·.2)
    let mean := vs.foldl (· + ·) 0 / vs.length.toFloat
    let mx := vs.foldl max 0
    IO.println s!"  {k}: mean={fmt mean} max={fmt mx} n={vs.length}"
  let bad ← fail.get
  IO.println s!"total {fmt ((tEnd - tStart) / 1000)}s: {if bad then "FAIL" else "ALL PASS"}"
  return (if bad then 1 else 0)
