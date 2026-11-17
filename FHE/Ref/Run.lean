import FHE.Ref.Arr
import Spec.IndCpaDProfile

/-!
# FHE.Ref.Run — ciphertext environments of arrays, the interpreter loop, the circuit inputs and
outputs, the message-level evaluation and textbook decryption, PROVED equal   (UNTRUSTED glue)

* `CtEnvA`: a ciphertext environment holding arrays; `wE σ` reads it as a trusted
  `Spec.Trace.CtEnv` (`wE_setA`).
* `runA`: the loop of `Challenge.IndCpaDProfile.ksRun` / `Challenge.IndCpaDLM.irun` (the body
  executed alongside the zero-message replay `Spec.Source.step`); `runA_spec`: if one step
  commutes with `wE`, the run does.
* `ctsA`, `initCtA`: the circuit's input ciphertexts (`Spec.IndCpaDProfile.AbsScheme.cts`,
  `Spec.Trace.initCt`) as arrays; `outA`: the outputs as `ksEval`/`interpEval` read them.
* `semA`: `Spec.IndCpaDProfile.AbsScheme.sem` with the forced message-level step
  `FHE.Pin.stepA` (Kronecker product, linear automorphism): `semA_eq : semA D C ms = D.sem C ms`.
* `decBGVA`, `decBFVA`: textbook decryption (`AbsScheme.decBGV`, `AbsScheme.decBFV`) through the
  forced integer phase of `FHE.Pin` (`decryptA_spec`, `centredPhaseA_spec`).
-/

namespace FHE.Ref
open Spec Spec.NPoly FHE.Pin Spec.Source Spec.IndCpaDProfile

/-- A ciphertext environment of arrays: an association list, newest first. It is DATA, not a
function: an environment of closures would be eta-expanded by the compiler and every ciphertext
recomputed at every lookup. -/
abbrev CtEnvA : Type := List (Var × List (Array ℤ))

/-- Look a variable up (the newest binding). -/
def getA : CtEnvA → Var → Option (List (Array ℤ))
  | [], _ => none
  | (y, c) :: σ, x => if x = y then some c else getA σ x

/-- Assign one variable. -/
def setA (σ : CtEnvA) (x : Var) (c : List (Array ℤ)) : CtEnvA := (x, c) :: σ

/-- The trusted ciphertext environment an array environment stands for. -/
def wE {P : FullParams} (σ : CtEnvA) : Trace.CtEnv P := fun x => (getA σ x).map (wC P.src.N)

theorem wE_apply {P : FullParams} (σ : CtEnvA) (x : Var) :
    (wE (P := P) σ) x = (getA σ x).map (wC P.src.N) := rfl

theorem wE_setA {P : FullParams} (σ : CtEnvA) (x : Var) (c : List (Array ℤ)) :
    wE (P := P) (setA σ x c) = (wE σ).set x (wC P.src.N c) := by
  funext y
  simp only [wE, setA, getA, Trace.CtEnv.set]
  split <;> rfl

/-! ## Step shapes -/

section Shapes
variable {P : FullParams} (σ : CtEnvA) (d a b : Var)

theorem shapeM (FA : List (Array ℤ) → List (Array ℤ))
    (F : List (IntPoly P.src.N) → List (IntPoly P.src.N))
    (hF : ∀ ca, wC P.src.N (FA ca) = F (wC P.src.N ca)) :
    ((getA σ a).map fun ca => setA σ d (FA ca)).map (wE (P := P)) =
      ((wE (P := P) σ) a).map fun ca => (wE (P := P) σ).set d (F ca) := by
  rw [wE_apply]
  cases getA σ a <;> simp [wE_setA, hF]

theorem shapeB (FA : List (Array ℤ) → List (Array ℤ) → List (Array ℤ))
    (F : List (IntPoly P.src.N) → List (IntPoly P.src.N) → List (IntPoly P.src.N))
    (hF : ∀ ca cb, wC P.src.N (FA ca cb) = F (wC P.src.N ca) (wC P.src.N cb)) :
    ((getA σ a).bind fun ca => (getA σ b).map fun cb => setA σ d (FA ca cb)).map (wE (P := P)) =
      ((wE (P := P) σ) a).bind fun ca => ((wE (P := P) σ) b).map fun cb =>
        (wE (P := P) σ).set d (F ca cb) := by
  rw [wE_apply, wE_apply]
  cases getA σ a <;> cases getA σ b <;> simp [wE_setA, hF]

end Shapes

/-! ## The loop -/

/-- The body run alongside the zero-message replay (`ksRun`, `irun`), on arrays. -/
def runA (Ps : Params) (st : Env Ps → CtEnvA → Instr → Option CtEnvA) :
    List Instr → Env Ps → CtEnvA → Option CtEnvA
  | [], _, σ => some σ
  | i :: is, ρ, σ => (step Ps ρ i).bind fun ρ' => (st ρ σ i).bind fun σ' => runA Ps st is ρ' σ'

theorem runA_spec {P : FullParams} (st : Env P.src → CtEnvA → Instr → Option CtEnvA)
    (stT : Env P.src → Trace.CtEnv P → Instr → Option (Trace.CtEnv P))
    (hst : ∀ ρ σ i, (st ρ σ i).map (wE (P := P)) = stT ρ (wE σ) i)
    (run : List Instr → Env P.src → Trace.CtEnv P → Option (Trace.CtEnv P))
    (hnil : ∀ ρ σ, run [] ρ σ = some σ)
    (hcons : ∀ i is ρ σ, run (i :: is) ρ σ =
      (step P.src ρ i).bind fun ρ' => (stT ρ σ i).bind fun σ' => run is ρ' σ') :
    ∀ body ρ σ, (runA P.src st body ρ σ).map (wE (P := P)) = run body ρ (wE σ)
  | [], ρ, σ => by rw [hnil]; rfl
  | i :: is, ρ, σ => by
    rw [hcons, ← hst]
    show ((step P.src ρ i).bind fun ρ' => (st ρ σ i).bind fun σ' => runA P.src st is ρ' σ').map wE = _
    cases step P.src ρ i with
    | none => rfl
    | some ρ' =>
      simp only [Option.bind_some]
      cases st ρ σ i with
      | none => rfl
      | some σ' =>
        simp only [Option.bind_some, Option.map_some]
        exact runA_spec st stT hst run hnil hcons is ρ' σ'

/-! ## Inputs and outputs of a circuit -/

/-- Ciphertexts with array components, read as trusted ciphertexts. -/
def wIn (N : ℕ) (cs : List (ℕ × List (Array ℤ))) : List (ℕ × List (IntPoly N)) :=
  cs.map fun c => (c.1, wC N c.2)

/-- `Spec.IndCpaDProfile.AbsScheme.cts` on arrays (a constant is forced once per lookup). -/
def ctsA (D : AbsScheme) (C : D.Circ) (cs : List (ℕ × List (Array ℤ))) (x : Var) : List (Array ℤ) :=
  match (D.fresh C).idxOf? x with
  | some i => (cs[i]?.map (·.2)).getD []
  | none => [force D.P.src.N (Encrypt.liftMsg (D.pt C x))]

theorem cts_wIn (D : AbsScheme) (C : D.Circ) (cs : List (ℕ × List (Array ℤ))) (x : Var) :
    D.cts C (wIn D.P.src.N cs) x = wC D.P.src.N (ctsA D C cs x) := by
  simp only [AbsScheme.cts, ctsA]
  cases h : (D.fresh C).idxOf? x with
  | some i =>
    simp only [wIn, List.getElem?_map]
    cases cs[i]? <;> simp [wC]
  | none => simp [wC]

/-- `Spec.Trace.initCt` on arrays: every declared input with its ciphertext (computed once). -/
def initCtA (prog : Program) (cts : Var → List (Array ℤ)) : CtEnvA :=
  prog.inputs.map fun d => (d.name, cts d.name)

theorem getA_initCtA (cts : Var → List (Array ℤ)) (x : Var) :
    ∀ ins : List Decl, getA (ins.map fun d => (d.name, cts d.name)) x =
      (ins.find? (·.name = x)).map fun _ => cts x
  | [] => rfl
  | d :: ins => by
    simp only [List.map_cons, getA, List.find?_cons]
    by_cases h : x = d.name
    · subst h; simp
    · have h' : ¬ d.name = x := fun e => h e.symm
      simp only [h, h', if_false, decide_false]
      exact getA_initCtA cts x ins

theorem initCt_wIn (D : AbsScheme) (C : D.Circ) (cs : List (ℕ × List (Array ℤ))) :
    Trace.initCt D.Pe (D.prog C) (D.cts C (wIn D.P.src.N cs)) =
      wE (P := D.Pe) (initCtA (D.prog C) (ctsA D C cs)) := by
  funext x
  simp only [Trace.initCt, wE, initCtA, getA_initCtA, cts_wIn]
  cases (D.prog C).inputs.find? (·.name = x) <;> rfl

/-- The outputs of a run, as `ksEval` and `interpEval` return them. -/
def outA (D : AbsScheme) (C : D.Circ) (r : Option CtEnvA) : List (ℕ × List (Array ℤ)) :=
  (r.map fun σ => (D.prog C).outputs.map fun o => (D.outLevel C o, (getA σ o).getD [])).getD []

theorem outA_spec (D : AbsScheme) (C : D.Circ) (r : Option CtEnvA) :
    wIn D.P.src.N (outA D C r) =
      ((r.map (wE (P := D.Pe))).map fun σ =>
        (D.prog C).outputs.map fun o => (D.outLevel C o, (σ o).getD [])).getD [] := by
  cases r with
  | none => rfl
  | some σ =>
    simp only [outA, Option.map_some, Option.getD_some, wIn, List.map_map]
    refine List.map_congr_left fun o _ => ?_
    simp only [Function.comp, wE]
    cases getA σ o <;> rfl

/-- The evaluator built from a step function on arrays (`ksEval`, `interpEval` shape). -/
def evalA (D : AbsScheme) (st : Env D.P.src → CtEnvA → Instr → Option CtEnvA) (C : D.Circ)
    (cs : List (ℕ × List (Array ℤ))) : List (ℕ × List (Array ℤ)) :=
  outA D C (runA D.P.src st (D.prog C).body (initEnv D.P.src (D.prog C) fun _ => .exact 0)
    (initCtA (D.prog C) (ctsA D C cs)))

/-- **The array evaluator is the trusted one**, for every trusted step function it commutes with
and every run loop of the `ksRun`/`irun` shape. -/
theorem evalA_spec (D : AbsScheme) (st : Env D.P.src → CtEnvA → Instr → Option CtEnvA)
    (stT : Env D.P.src → Trace.CtEnv D.Pe → Instr → Option (Trace.CtEnv D.Pe))
    (hst : ∀ ρ σ i, (st ρ σ i).map (wE (P := D.Pe)) = stT ρ (wE σ) i)
    (run : List Instr → Env D.P.src → Trace.CtEnv D.Pe → Option (Trace.CtEnv D.Pe))
    (hnil : ∀ ρ σ, run [] ρ σ = some σ)
    (hcons : ∀ i is ρ σ, run (i :: is) ρ σ =
      (step D.P.src ρ i).bind fun ρ' => (stT ρ σ i).bind fun σ' => run is ρ' σ')
    (C : D.Circ) (cs : List (ℕ × List (Array ℤ))) :
    wIn D.P.src.N (evalA D st C cs) =
      ((run (D.prog C).body (initEnv D.P.src (D.prog C) fun _ => .exact 0)
          (Trace.initCt D.Pe (D.prog C) (D.cts C (wIn D.P.src.N cs)))).map
        fun σ => (D.prog C).outputs.map fun o => (D.outLevel C o, (σ o).getD [])).getD [] := by
  rw [evalA, outA_spec, initCt_wIn,
    runA_spec (P := D.Pe) st stT hst run hnil hcons]

/-! ## What a circuit computes, fast -/

/-- `Spec.Source.eval` with the forced step `FHE.Pin.stepA` (products by Kronecker substitution,
the automorphism by a linear scatter, every message forced once). -/
def evalMsgA (P : Params) (prog : Program) (msgs : Var → Msg P.t P.N) : Option (Env P) := do
  guard (prog.inputs.all fun dcl => dcl.ok P)
  guard (prog.inputs.all fun dcl => (msgs dcl.name).fits P.kind)
  let ρ ← prog.body.foldlM (stepA 1 .none P) (initEnv P prog msgs)
  guard (prog.outputs.all fun o => (ρ o).isSome)
  pure ρ

theorem evalMsgA_eq (P : Params) (prog : Program) (msgs : Var → Msg P.t P.N) :
    evalMsgA P prog msgs = Source.eval P prog msgs := by
  simp only [evalMsgA, Source.eval, foldlM_stepA]

/-- `Spec.IndCpaDProfile.AbsScheme.sem` with `evalMsgA`. -/
def semA (D : AbsScheme) (C : D.Circ) (ms : List (Poly D.P.src.t D.P.src.N)) :
    List (Poly D.P.src.t D.P.src.N) :=
  if ms.length = (D.fresh C).length then
    match evalMsgA D.P.src (D.prog C) (fun x => .exact (D.msg C ms x)) with
    | some ρ => (D.prog C).outputs.map fun o =>
        match ρ o with
        | some v => match v.msg with | .exact m => m
        | none => 0
    | none => []
  else []

/-- **The fast message-level evaluation is `sem`.** -/
theorem semA_eq (D : AbsScheme) (C : D.Circ) (ms : List (Poly D.P.src.t D.P.src.N)) :
    semA D C ms = D.sem C ms := by
  simp only [semA, evalMsgA_eq]
  rfl

/-! ## Textbook decryption -/

/-- BGV textbook decryption at the ciphertext's level (`AbsScheme.decBGV`), forced. -/
def decBGVA (D : AbsScheme) (s : Array ℤ) (c : ℕ × List (Array ℤ)) : Array (ZMod D.P.src.t) :=
  decryptA D.P.src.N 1 .none D.P.src.t (D.P.src.modulus c.1) s c.2

theorem decBGVA_eq (D : AbsScheme) (sk : D.SK) (s : Array ℤ) (hs : D.sec sk = ofArr s)
    (c : ℕ × List (Array ℤ)) :
    (ofArr (decBGVA D s c) : Poly D.P.src.t D.P.src.N) = D.decBGV sk (c.1, wC D.P.src.N c.2) := by
  rw [decBGVA, decryptA_spec]
  show _ = Scheme.bgvDecrypt D.P.src.t (D.sec sk) ((c.2.map ofArr).map (ofInt (D.P.src.modulus c.1)))
  rw [hs, List.map_map]
  rfl

/-- BFV textbook decryption at the ciphertext's level (`AbsScheme.decBFV`), forced. -/
def decBFVA (D : AbsScheme) (s : Array ℤ) (c : ℕ × List (Array ℤ)) : Array (ZMod D.P.src.t) :=
  mapA D.P.src.N (fun z : ℤ => ((Scheme.roundDiv (D.P.src.t * z) (D.P.src.modulus c.1) : ℤ) : ZMod D.P.src.t))
    (centredPhaseA D.P.src.N 1 .none (D.P.src.modulus c.1) s c.2)

theorem decBFVA_eq (D : AbsScheme) (sk : D.SK) (s : Array ℤ) (hs : D.sec sk = ofArr s)
    (c : ℕ × List (Array ℤ)) :
    (ofArr (decBFVA D s c) : Poly D.P.src.t D.P.src.N) = D.decBFV sk (c.1, wC D.P.src.N c.2) := by
  rw [decBFVA, ofArr_mapA, centredPhaseA_spec]
  show _ = Scheme.bfvDecrypt D.P.src.t (D.sec sk) ((c.2.map ofArr).map (ofInt (D.P.src.modulus c.1)))
  rw [hs, List.map_map]
  rfl

/-! ## Memoised key functions -/

/-- `f`, with its values on `gs` taken from the table `vals` (computed once by the caller). -/
def memoAt {β : Type} (gs : List ℕ) (vals : List β) (f : ℕ → β) : ℕ → β :=
  fun g => match (gs.zip vals).lookup g with
    | some v => v
    | none => f g

/-- A table of the values of `f` changes nothing. -/
theorem memoAt_eq {β : Type} (gs : List ℕ) (f : ℕ → β) : memoAt gs (gs.map f) f = f := by
  funext g
  simp only [memoAt]
  induction gs with
  | nil => rfl
  | cons a as ih =>
    simp only [List.map_cons, List.zip_cons_cons, List.lookup_cons]
    by_cases h : g = a
    · subst h; simp
    · have e : (g == a) = false := by simp [h]
      simp only [e]; exact ih

end FHE.Ref
