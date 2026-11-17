import Lean

/-!
# PinStatus — pin, headline and kernel audit of `scripts/check-spec.sh`   (TRUSTED; see trust/LOCK)

Run: `lake env lean --run scripts/PinStatus.lean [OUT_DIR [--replay-cache DIR | --replay-cache-write DIR] [--replay-jobs N]]`
(after `lake build Challenge Validation`; the cache flags are explained under "Replay cache",
`--replay-jobs` under "Parallel kernel replay").

This is a program, not a command elaborated after `import Validation`. It imports only `Lean`, and
loads the project's environment (`Challenge`, `Validation`) *as data* from the `.olean` files with
`importModules (loadExts := false)`, after every line of this file has been elaborated. So nothing
in `Validation` or `FHE` can redefine a command, macro, elaborator, instance or option this audit
uses, and no initializer or environment extension of theirs runs inside this process. (The earlier
version elaborated a `#pin_status` command after `import Validation`, in an environment the
audited code controls.)

Output lines (stdout):

* `PIN <Challenge.X> PROVEN | MISSING | MISMATCH | AXIOMS <list> | KERNEL-REJECTED <error>` for
  every theorem `Challenge.X` declared in a `Challenge` module, except the auto-generated field
  projections of a `Prop`-valued structure declared there (`PROJECTION <name> ...` lines: Lean
  makes them theorems, but nobody states or proves them, so they are not pins and are not
  counted). PROVEN means: `Validation.X` is a
  theorem, its type equals the locked one (syntactically after instantiating universe parameters,
  else by the *kernel's* definitional equality, never `Meta.isDefEq`), its closure uses only the
  three standard axioms, and **every constant in its closure was accepted by the Lean kernel in a
  fresh environment** (see below).
* `HEADLINE <pin> OK | BAD <reason>`: each locked headline statement is literally
  `<locked predicate> <hole>` (table hard-coded below), so no notation, macro, coercion or instance
  declared by the untrusted hole module can change what it claims.
* `HOLE <name> OK | BAD <reason>`: the holes (table `holes` below: the headline hole and the
  fast-path holes of `Challenge/Fast.lean`) are safe, computable definitions of the fixed
  types, with no `implemented_by`/`extern`/`opaque`/`unsafe`/`partial` constant in their closure
  outside Lean core, Std and Mathlib, no `sorryAx` and no non-standard axiom; and they too are
  kernel-replayed.
* `MODULES ...`: import-graph checks from the `.olean` headers (trusted modules import only trusted
  modules; the holes' closure contains nothing from `Validation`, `Challenge.Headline` or any
  library other than Lean/Mathlib, `Spec`, `Challenge`, `FHE`).
* `MODULES files ...`: every `.lean` file under `Challenge/` is in the import closure of
  `Challenge.lean`, and every file under `Spec/` is in the import closure of `Spec.lean` or under
  one of the allowlisted experimental prefixes (`unpinnedSpecPrefixes`, printed with the files
  they cover). A trusted or locked file that nothing imports is otherwise invisible to this audit.
* `FHE ...`: the whole untrusted `FHE` library (every `.lean` file under `FHE/`, loaded as data
  like everything else) and the equivalence proofs `Respec/Equiv/` (every `.lean` file there): no constant declared in an `FHE.*` module depends on `sorryAx` or on an
  axiom other than the three standard ones (`FHE axioms ...`), and the closure of all of them is
  kernel-replayed in the same fresh environment as the pins (`KERNEL FHE ...`).
* `CLASS <Challenge.X> <class> <why>` for every pin, and one `CLASSES ...` line with the counts:
  what kind of statement each locked statement is, so that "N statements proved" is never read as
  "N theorems of substance". See `Classification` below for the six classes, which of them are
  computed from the statement or the proof term and which come from the hand-written table
  `annotations` (whose rows are checked: the pin exists, and for an "instance of" row the proof
  really depends on the pin it names).
* `LOCKED ...`: no definition, structure or instance declared in a `Spec` or `Challenge` module,
  and no *statement* of a locked theorem, depends on `sorryAx` (the only `sorry` in locked code is
  the body of a pin).
* `KERNEL ...` and `SUMMARY ...`. One `KERNEL cache: off ...` line when every root was replayed
  from an empty environment (always without a cache flag; the strict gate requires it), or
  `KERNEL cache: on ...` with the number of roots and FHE constants whose replay was skipped
  (`--replay-cache`, development only; see "Replay cache" below).

Kernel replay. A declaration added with `set_option debug.skipKernelTC true`, or programmatically
with `addDeclWithoutChecking` / `withOptions … addDecl`, is stored in the `.olean` like any other;
`#print axioms` and `collectAxioms` cannot see the difference. So for each proved pin and each
hole, in turn, the constants of its closure that are not yet in the kernel environment are sent
to the kernel (`Lean.Kernel.Environment.replay`), starting from `mkEmptyEnvironment`: Lean core
and Mathlib constants used by a pin are re-checked too, not trusted from their `.olean`s. A pin
whose closure the kernel rejects is reported `KERNEL-REJECTED`, never PROVEN. With
`--replay-jobs N` (N > 1; `scripts/check-spec.sh` passes it by default) the same constants are
sent to the kernel, each once, by N parallel workers, with the same verdicts and output; see
"Parallel kernel replay" for how and why.

What remains trusted: this file, the Lean toolchain (kernel, `.olean` reader), and the fact that
the `.olean`s being read were produced by `lake build` from the sources (see check-spec.sh: build
first, then this; an attacker who can run code at build time is discussed there and in trust/).
Mathlib's `.olean`s are NOT rebuilt by the gate: they are whatever is in `.lake/packages` (on a
fresh clone, `./verify.sh` fetches Mathlib's prebuilt cache for the revision pinned in
`lake-manifest.json` rather than compiling it). That cache is not trusted for proofs: every Lean
core and Mathlib constant a pin or hole uses is re-checked by the kernel here, from an empty
environment. Only the *attributes* stored in those `.olean`s (e.g. `implemented_by` inside
Mathlib, which matter for compiled code, not for proofs) are taken on trust.

With `OUT_DIR`, writes `OUT_DIR/holes-modules.txt` (the `FHE` modules in the holes' import
closure) for the gate's textual cross-check, and `OUT_DIR/replay-roots.txt` (the replayed roots,
usable with `leanexport … -- $(cat …)` and `leanchecker --from-export` as an external re-check).

Exit code 0 iff nothing is MISMATCH / AXIOMS / KERNEL-REJECTED / BAD. MISSING pins are reported
only (the gate fails on them under `STRICT=1`).
-/

open Lean

namespace PinStatus

def allowedAxioms : List Name := [``propext, ``Quot.sound, ``Classical.choice]

/-- Library roots whose `.olean`s are built from source at pinned tags (toolchain, and
`lake-manifest.json` revisions). Only their attributes are taken on trust: their constants used by
a pin or hole are kernel-replayed like everything else. -/
def trustedRoots : List Name :=
  [`Init, `Std, `Lean, `Lake, `Mathlib, `Batteries, `Aesop, `Qq, `Plausible, `ProofWidgets,
   `ImportGraph, `LeanSearchClient]

/-- (locked theorem, locked predicate, hole). Hard-coded in trusted code, so the hole module cannot
change what is checked. Mirrors `Challenge/Headline.lean`; a change there needs a change here, by
the maintainers (both are under trust/LOCK). -/
def headlines : List (Name × Name × Name) :=
  [ (`Challenge.Headline.analyze_sound,               `Challenge.Headline.NoiseSoundBGV,       `FHE.Holes.analyze),
    (`Challenge.Headline.analyze_tight,               `Challenge.Headline.NoiseTightBGV,       `FHE.Holes.analyze),
    (`Challenge.Headline.analyze_accepts_addMul,      `Challenge.Headline.NoiseAcceptsAddMul,  `FHE.Holes.analyze),
    (`Challenge.Headline.analyze_rejects_nonBGV,      `Challenge.Headline.NoiseRejectsNonBGV,  `FHE.Holes.analyze) ]

/-- The fast path of `fhe_check` (`Challenge/Fast.lean`; predicates in `Challenge/Fast/Defs.lean`):
the functions the tool runs are equal to the locked analyzer and certificate decision. -/
def headlinesFast : List (Name × Name × Name) :=
  [ (`Challenge.Fast.analyzeFast_eq, `Challenge.Fast.AnalyzerEqRef,  `FHE.Holes.analyzeFast),
    (`Challenge.Fast.certifyFast_eq, `Challenge.Fast.CertifierEqRef, `FHE.Holes.certifyFast),
    (`Challenge.Fast.analyzeBFVFast_eq, `Challenge.Fast.AnalyzerBFVEqRef,  `FHE.Holes.analyzeBFVFast),
    (`Challenge.Fast.certifyBFVFast_eq, `Challenge.Fast.CertifierBFVEqRef, `FHE.Holes.certifyBFVFast),
    (`Challenge.Fast.certifyBFVFreshFast_eq, `Challenge.Fast.CertifierBFVFreshEqRef,
      `FHE.Holes.certifyBFVFreshFast),
    (`Challenge.Fast.decryptLibFast_eq, `Challenge.Fast.DecryptLibEqRef, `FHE.Holes.decryptLibFast),
    (`Challenge.Fast.decryptLibExtFast_eq, `Challenge.Fast.DecryptLibExtEqRef,
      `FHE.Holes.decryptLibExtFast),
    (`Challenge.Fast.scaleOKFast_eq, `Challenge.Fast.ScaleOKEqRef, `FHE.Holes.scaleOKFast) ]

/-- The profile mode of `fhe_check` (`Challenge/Fast/Profile.lean`; predicates in
`Challenge/Fast/ProfileDefs.lean`): the profile decisions and BFV coverage checks the tool runs are
equal to the locked ones of `Challenge.Profile`. -/
def headlinesFastProfile : List (Name × Name × Name) :=
  [ (`Challenge.Fast.certifyProfileFast_eq, `Challenge.Fast.ProfileEqRef, `FHE.Holes.certifyProfileFast),
    (`Challenge.Fast.certifyBFVProfileFast_eq, `Challenge.Fast.ProfileBFVEqRef,
      `FHE.Holes.certifyBFVProfileFast),
    (`Challenge.Fast.coversBFVFast_eq, `Challenge.Fast.CoversBFVEqRef, `FHE.Holes.coversBFVFast),
    (`Challenge.Fast.coversBFVAtFast_eq, `Challenge.Fast.CoversBFVAtEqRef, `FHE.Holes.coversBFVAtFast) ]

def headlineModule : Name := `Challenge.Headline
def headlineDefsModule : Name := `Challenge.Headline.Defs
def fastDefsModule : Name := `Challenge.Fast.Defs
def fastProfileDefsModule : Name := `Challenge.Fast.ProfileDefs

/-- The holes, their fixed types, and the locked module that declares each type. -/
def holes : List (Name × Name × Name) :=
  [ (`FHE.Holes.analyze,     `Challenge.Headline.NoiseAnalyzer, headlineDefsModule),
    (`FHE.Holes.analyzeFast, `Challenge.Headline.NoiseAnalyzer, headlineDefsModule),
    (`FHE.Holes.certifyFast, `Challenge.Fast.Certifier,         fastDefsModule),
    (`FHE.Holes.analyzeBFVFast, `Challenge.BFV.NoiseAnalyzerBFVAt, `Challenge.BFV.Defs),
    (`FHE.Holes.certifyBFVFast, `Challenge.Fast.CertifierBFV,    fastDefsModule),
    (`FHE.Holes.certifyBFVFreshFast, `Challenge.Fast.CertifierBFVFresh, fastDefsModule),
    (`FHE.Holes.decryptLibFast, `Challenge.Fast.DecryptLibCheck, fastDefsModule),
    (`FHE.Holes.decryptLibExtFast, `Challenge.Fast.DecryptLibCheck, fastDefsModule),
    (`FHE.Holes.scaleOKFast, `Challenge.Fast.ScaleCheck, fastDefsModule),
    (`FHE.Holes.certifyProfileFast, `Challenge.Fast.ProfileDecision, fastProfileDefsModule),
    (`FHE.Holes.certifyBFVProfileFast, `Challenge.Fast.ProfileDecisionBFV, fastProfileDefsModule),
    (`FHE.Holes.coversBFVFast, `Challenge.Fast.CoverageBFV, fastProfileDefsModule),
    (`FHE.Holes.coversBFVAtFast, `Challenge.Fast.CoverageBFVAt, fastProfileDefsModule) ]

/-- (module of the locked statements, module of their predicates, rows). Every row of a group is
checked against exactly that pair of modules. -/
def headlineGroups : List (Name × Name × List (Name × Name × Name)) :=
  [ (headlineModule, headlineDefsModule, headlines),
    (`Challenge.Fast, fastDefsModule, headlinesFast),
    (`Challenge.Fast.Profile, fastProfileDefsModule, headlinesFastProfile) ]

/-- The modules that import the hole: the statements modules of `headlineGroups`. -/
def headlineModules : List Name := headlineGroups.map (·.1)
def holesModule : Name := `FHE.Holes

def moduleOf? (env : Environment) (n : Name) : Option Name :=
  env.getModuleIdxFor? n |>.bind fun i => env.header.moduleNames[i.toNat]?

def isTrustedModule (m : Name) : Bool := trustedRoots.any (·.isPrefixOf m)

/-- Locked project code: `Spec` and `Challenge`, except the modules that import the hole (the
statements modules of `headlineGroups`, and the root `Challenge`, which imports them). -/
def isLockedModule (m : Name) : Bool :=
  m.getRoot == `Spec || (m.getRoot == `Challenge && !headlineModules.contains m && m != `Challenge)

/-- Constants directly referenced by a constant, as in `Lean.CollectAxioms`. -/
def directDeps (ci : ConstantInfo) : Array Name := Id.run do
  let add (acc : Array Name) (e : Expr) : Array Name := e.getUsedConstants.foldl (·.push ·) acc
  let mut out := add #[] ci.type
  match ci with
  | .defnInfo v => out := add out v.value
  | .thmInfo v => out := add out v.value
  | .opaqueInfo v => out := add out v.value
  | .inductInfo v => out := (v.ctors ++ v.all).foldl (·.push ·) out
  | .ctorInfo v => out := out.push v.induct
  | .recInfo v => out := v.rules.foldl (fun acc r => add acc r.rhs) (v.all.foldl (·.push ·) out)
  | _ => pure ()
  return out

/-- Dependency graph reachable from `roots`; `.error n` if a referenced constant does not exist. -/
def depGraph (env : Environment) (roots : Array Name) :
    Except Name (Std.HashMap Name (Array Name)) := Id.run do
  let mut g : Std.HashMap Name (Array Name) := {}
  let mut todo := roots
  while h : todo.size > 0 do
    let n := todo.back
    todo := todo.pop
    if g.contains n then continue
    let some ci := env.find? n | return .error n
    let ds := directDeps ci
    -- recursors of an inductive are needed to replay it
    let ds := match ci with
      | .inductInfo _ => if env.contains (mkRecName n) then ds.push (mkRecName n) else ds
      | _ => ds
    g := g.insert n ds
    for d in ds do
      unless g.contains d do todo := todo.push d
  return .ok g

/-- Nodes of `g` reachable from `root`, not entering `stop`. -/
def reach (g : Std.HashMap Name (Array Name)) (root : Name) (stop : Name → Bool := fun _ => false) :
    NameSet := Id.run do
  let mut seen : NameSet := {}
  let mut todo := #[root]
  while h : todo.size > 0 do
    let n := todo.back
    todo := todo.pop
    if seen.contains n || stop n then continue
    seen := seen.insert n
    for d in g.getD n #[] do
      unless seen.contains d do todo := todo.push d
  return seen

/-- Import closure of a module, from the `.olean` headers. -/
def importClosure (env : Environment) (m : Name) : NameSet := Id.run do
  let mut idx : Std.HashMap Name Nat := {}
  for h : i in [0:env.header.moduleNames.size] do
    idx := idx.insert env.header.moduleNames[i] i
  let mut seen : NameSet := {}
  let mut todo := #[m]
  while h : todo.size > 0 do
    let n := todo.back
    todo := todo.pop
    if seen.contains n then continue
    seen := seen.insert n
    if let some i := idx[n]? then
      if let some md := env.header.moduleData[i]? then
        for imp in md.imports do todo := todo.push imp.module
  return seen

def timeSince (t0 : Nat) : IO String := return s!"{((← IO.monoMsNow) - t0)} ms"

/-- Experimental trusted-tree modules that are deliberately outside the import closure of
`Spec.lean`: they have no pins and no headline depends on them. The gate prints the files this
covers on every run. Empty: every file under `Spec/` is imported by `Spec.lean`. -/
def unpinnedSpecPrefixes : List Name := []

/-- The modules of the `.lean` files under directory `dir` (relative to the working directory,
which is the repository root), e.g. `Spec/Trace.lean` ↦ `Spec.Trace`. -/
partial def leanFilesUnder (dir : System.FilePath) (pre : Name) : IO (Array Name) := do
  let mut out := #[]
  if !(← dir.pathExists) then return out
  for e in (← dir.readDir) do
    if ← e.path.isDir then
      out := out ++ (← leanFilesUnder e.path (pre.str e.fileName))
    else if e.fileName.endsWith ".lean" then
      out := out.push (pre.str (e.fileName.dropEnd 5).toString)
  return out.qsort (·.toString < ·.toString)

/-- The field names of the structure `S`, if `S` is a structure-like inductive (one constructor,
no indices, not recursive). -/
def structFields? (env : Environment) (S : Name) : Option (List Name) :=
  match env.find? S with
  | some (.inductInfo iv) =>
    if iv.numIndices != 0 || iv.isRec then none else
    match iv.ctors with
    | [c] =>
      match env.find? c with
      | some (.ctorInfo cv) =>
        let rec fields (e : Expr) (skip : Nat) (acc : List Name) : List Name :=
          match e with
          | .forallE n _ b _ => if skip > 0 then fields b (skip - 1) acc else fields b 0 (n :: acc)
          | _ => acc.reverse
        some (fields cv.type cv.numParams [])
      | _ => none
    | _ => none
  | _ => none

/-- `n` is `S.f` for a structure `S` declared in a `Challenge` module with a field `f`. Such a
name can only be the projection Lean generated with the structure (a second declaration of the
same name is an error), so it is not a statement anybody wrote. -/
def isStructProjection (env : Environment) (n : Name) : Bool :=
  match n with
  | .str S f =>
    (moduleOf? env S).any (·.getRoot == `Challenge) &&
      ((structFields? env S).any fun fs => fs.contains (Name.mkSimple f))
  | _ => false

/-! ## Classification of the locked statements

Every pin gets exactly one class, the first that applies:

1. `discrimination`: the statement says something is rejected or wrong. Computed from the
   statement: after stripping `∀`/`→` (and unfolding a locked `Spec`/`Challenge` predicate at the head),
   the conclusion is `¬ _`, `_ ≠ _`, `False`, `_ = none` or `_ = false`, or a closed conjunction
   one of whose conjuncts is.
2. `realizability`: the statement exhibits a ciphertext-level step or run meeting the contracts.
   Computed: the conclusion is `StepOK …` of one of the two `Spec.Trace*` files, or
   `∃ …, … StepOK …` / `∃ …, Run …`.
3. `instance`: an instance or immediate corollary of other pins. From `annotations`; the row names
   the pins it follows from, and the audit checks that the proof depends on each of them.
4. `unfolding`: true by unfolding definitions. Computed when the proof term is `rfl`; otherwise
   from `annotations` (a judgement: the proof is `simp`/`unfold`/`ring` on the definitions, with no
   mathematical content beyond them).
5. `closed`: a closed statement, with no universally quantified variable and no hypothesis (after
   unfolding a locked `Spec`/`Challenge` predicate at the head; so `NoiseSoundBGV analyze`
   for a named analyzer is NOT closed: it quantifies over parameters, programs and inputs): a fact
   about named parameters or programs, decided by evaluating a closed term in the kernel. Computed.
6. `substantive`: everything else: a universally quantified theorem that is none of the above.
-/

inductive PinClass
  | discrimination | realizability | inst | unfolding | closed | substantive
  deriving BEq, Repr

def PinClass.label : PinClass → String
  | .discrimination => "discrimination" | .realizability => "realizability"
  | .inst => "instance" | .unfolding => "unfolding" | .closed => "closed"
  | .substantive => "substantive"

/-- A hand-written annotation: `inst parents` (an instance or immediate corollary of the pins
`parents`) or `unfolding` (true by unfolding definitions). -/
inductive Ann
  | inst (parents : List Name)
  | unfolding
  /-- A closed fact whose statement the shape test does not recognise as closed (it unfolds to a
  bounded quantifier over a concrete list). -/
  | closed

/-- The annotation table (LOCKED with this file). Rows for pins that do not exist fail the gate;
`inst` rows are checked against the dependency graph of the proof. A pin without a row is
classified from its statement alone. -/
def annotations : List (Name × Ann) :=
  [ -- instances and immediate corollaries
    (`Challenge.BFVMul.stepOK_mul_hps_float,
      .inst [`Challenge.BFVMul.stepOK_mul_hps_tol, `Challenge.BFVMul.floatSums_ok]),
    (`Challenge.BFVMul.stepOK_square_hps_float,
      .inst [`Challenge.BFVMul.stepOK_square_hps_tol, `Challenge.BFVMul.floatSums_ok]),
    (`Challenge.BFVMul.stepOK_mul_poverq_float,
      .inst [`Challenge.BFVMul.stepOK_mul_poverq_tol, `Challenge.BFVMul.floatSums_ok]),
    (`Challenge.BFVMul.stepOK_mul_leveled_float,
      .inst [`Challenge.BFVMul.stepOK_mul_leveled_tol, `Challenge.BFVMul.floatSums_ok]),
    (`Challenge.Budget.certified_sound, .inst [`Challenge.Headline.analyze_sound]),
    (`Challenge.BFV.ksBoundAt_le_ksBudget, .inst [`Challenge.Budget.ksBoundAt_le_ksBudget]),
    (`Challenge.FreshNoise.fresh_certified,
      .inst [`Challenge.FreshNoise.fresh_sound, `Challenge.FreshNoise.freshError_tail]),
    (`Challenge.FreshNoise.fresh_certified_kappa,
      .inst [`Challenge.FreshNoise.fresh_certified, `Challenge.FreshNoise.epsFor_spec]),
    (`Challenge.FreshNoise.fresh_worst_decrypts,
      .inst [`Challenge.FreshNoise.fresh_sound, `Challenge.FreshNoise.freshError_worst]),
    (`Challenge.FreshNoise.fresh_kappa_decrypts,
      .inst [`Challenge.FreshNoise.fresh_sound, `Challenge.FreshNoise.freshError_tail,
             `Challenge.FreshNoise.epsFor_spec]),
    (`Challenge.FreshNoiseL2.fresh_certified_l2,
      .inst [`Challenge.FreshNoise.fresh_sound, `Challenge.FreshNoiseL2.freshError_tail_l2]),
    (`Challenge.FreshNoiseL2.fresh_certified_kappa_l2,
      .inst [`Challenge.FreshNoiseL2.fresh_certified_l2, `Challenge.FreshNoise.epsFor_spec]),
    (`Challenge.FreshNoiseL2.fresh_kappa_decrypts_l2,
      .inst [`Challenge.FreshNoise.fresh_sound, `Challenge.FreshNoiseL2.freshError_tail_l2,
             `Challenge.FreshNoise.epsFor_spec]),
    (`Challenge.FreshNoiseL2.subGaussSamplerOK_rademacher,
      .inst [`Challenge.FreshNoise.samplerOK_rademacher,
             `Challenge.FreshNoiseL2.subGaussSamplerOK_of_samplerOK]),
    (`Challenge.Budget.gadgetKeys_restrict_uniform,
      .inst [`Challenge.Budget.gadgetKeys_restrict, `Challenge.Budget.uniformLayout_restrictsTo]),
    (`Challenge.Certify.worst_certified,
      .inst [`Challenge.Certify.certified_sound, `Challenge.Certify.certify?_worstCase]),
    (`Challenge.Certify.certify?_sound, .inst [`Challenge.Certify.certified_sound]),
    (`Challenge.Realize.certify?_relinOpenFHE,
      .inst [`Challenge.Realize.relinOpenFHE_stepOK, `Challenge.Certify.certify?_paramsOK,
             `Challenge.Certify.certify?_keys_restrict]),
    (`Challenge.Realize.certify?_keySwitchOpenFHE,
      .inst [`Challenge.Realize.keySwitchOpenFHE_stepOK, `Challenge.Certify.certify?_paramsOK,
             `Challenge.Certify.certify?_keys_restrict]),
    (`Challenge.Realize.certify?_rotateOpenFHE161,
      .inst [`Challenge.Realize.rotateOpenFHE161_run, `Challenge.Certify.certify?_paramsOK,
             `Challenge.Certify.certify?_keys_restrict]),
    (`Challenge.Realize.certify?_modSwitch,
      .inst [`Challenge.Trace.stepOK_modSwitch_textbook_parts, `Challenge.Certify.certify?_spec]),
    (`Challenge.Certify.certify?_decrypts,
      .inst [`Challenge.Certify.certified_sound, `Challenge.Certify.outputsCertified_decrypts]),
    (`Challenge.Certify.fresh_kappa_decrypts,
      .inst [`Challenge.Certify.fresh_kappa_certified, `Challenge.Certify.outputsCertified_decrypts]),
    (`Challenge.Certify.fresh_l2_decrypts,
      .inst [`Challenge.Certify.fresh_l2_certified, `Challenge.Certify.outputsCertified_decrypts]),
    (`Challenge.Scaling.certify?_user,
      .inst [`Challenge.Certify.certify?_sound, `Challenge.Scaling.eval_scaled]),
    (`Challenge.Scaling.certify?_src,
      .inst [`Challenge.Certify.certify?_worstCase, `Challenge.Certify.certify?_fresh,
             `Challenge.Certify.certify?_freshL2]),
    (`Challenge.Scaling.adjProg_raw_ne_plain,
      .inst [`Challenge.Scaling.certify?_user, `Challenge.Scaling.adjProg_accepted]),
    (`Challenge.IndCpaD.prob_eq, .inst [`Challenge.IndCpaD.gameD_eq_gameCPA]),
    (`Challenge.IndCpaD.prob_le, .inst [`Challenge.IndCpaD.gameD_eq_gameCPA]),
    (`Challenge.IndCpaD.bfv_prob_eq, .inst [`Challenge.IndCpaD.prob_eq, `Challenge.IndCpaD.correct]),
    (`Challenge.IndCpaD.bfv_prob_le, .inst [`Challenge.IndCpaD.prob_le, `Challenge.IndCpaD.correct]),
    (`Challenge.IndCpaD.correct_libEval,
      .inst [`Challenge.IndCpaD.correct_of_meets, `Challenge.IndCpaD.libEval_meets]),
    (`Challenge.IndCpaD.meets_prob_eq,
      .inst [`Challenge.IndCpaD.prob_eq, `Challenge.IndCpaD.correct_of_meets]),
    (`Challenge.IndCpaD.meets_prob_le,
      .inst [`Challenge.IndCpaD.prob_le, `Challenge.IndCpaD.correct_of_meets]),
    (`Challenge.IndCpaD.correct_textEval,
      .inst [`Challenge.IndCpaD.correct_of_meets, `Challenge.IndCpaD.textEval_meets]),
    (`Challenge.IndCpaD.correct_textEval_tiny,
      .inst [`Challenge.IndCpaD.correct_textEval, `Challenge.IndCpaD.admissible_tiny]),
    (`Challenge.IndCpaD.correct_textEval_seal,
      .inst [`Challenge.IndCpaD.correct_textEval]),
    (`Challenge.Profile.run_mono,
      .inst [`Challenge.Profile.stepOK_mono]),
    (`Challenge.Profile.runAt_mono,
      .inst [`Challenge.Profile.stepOK_mono_bfv]),
    (`Challenge.Profile.outputsCertified_mono,
      .inst [`Challenge.Profile.run_mono]),
    (`Challenge.Profile.outputsCertifiedBFV_mono,
      .inst [`Challenge.Profile.runAt_mono]),
    (`Challenge.Instances.Lattigo.relin_meets,
      .inst [`Challenge.Budget.relin_realizable_top]),
    (`Challenge.Instances.Lattigo.keySwitch_meets,
      .inst [`Challenge.Budget.keySwitch_realizable_top]),
    (`Challenge.Instances.Lattigo.modSwitch_meets,
      .inst [`Challenge.Profile.coversBGV?_modSwitch]),
    (`Challenge.IndCpaDProfile.bfv_prob_eq,
      .inst [`Challenge.IndCpaD.prob_eq, `Challenge.IndCpaDProfile.correct_bfv]),
    (`Challenge.IndCpaDProfile.bfv_prob_le,
      .inst [`Challenge.IndCpaD.prob_le, `Challenge.IndCpaDProfile.correct_bfv]),
    (`Challenge.IndCpaDProfile.bgv_prob_eq,
      .inst [`Challenge.IndCpaD.prob_eq, `Challenge.IndCpaDProfile.correct_bgv]),
    (`Challenge.IndCpaDProfile.bgv_prob_le,
      .inst [`Challenge.IndCpaD.prob_le, `Challenge.IndCpaDProfile.correct_bgv]),
    (`Challenge.IndCpaDProfile.correct_via_profile,
      .inst [`Challenge.IndCpaDProfile.correct_bfv, `Challenge.IndCpaDProfile.admissible_profile, `Challenge.IndCpaDProfile.encOK_dataOf, `Challenge.IndCpaDProfile.evalMeets_dataOf, `Challenge.IndCpaD.libEval_meets]),
    (`Challenge.IndCpaDProfile.correct_textEval_via_profile,
      .inst [`Challenge.IndCpaDProfile.correct_bfv, `Challenge.IndCpaDProfile.admissible_profile, `Challenge.IndCpaDProfile.encOK_dataOf, `Challenge.IndCpaDProfile.evalMeets_dataOf, `Challenge.IndCpaD.textEval_meets]),
    (`Challenge.IndCpaDProfile.bfv_prob_eq_via_profile,
      .inst [`Challenge.IndCpaD.prob_eq, `Challenge.IndCpaDProfile.correct_via_profile]),
    (`Challenge.IndCpaDProfile.bfv_prob_le_via_profile,
      .inst [`Challenge.IndCpaD.prob_le, `Challenge.IndCpaDProfile.correct_via_profile]),
    (`Challenge.IndCpaDProfile.admBFV_tiny,
      .inst [`Challenge.IndCpaDProfile.admissible_profile, `Challenge.IndCpaDProfile.encOK_dataOf, `Challenge.IndCpaD.admissible_tiny]),
    (`Challenge.IndCpaDProfile.correct_exactEval,
      .inst [`Challenge.IndCpaDProfile.correct_bgv, `Challenge.IndCpaDProfile.exactEval_meets]),
    (`Challenge.IndCpaDProfile.correct_exactEval_bgvSeal,
      .inst [`Challenge.IndCpaDProfile.correct_exactEval, `Challenge.IndCpaDProfile.encOK_bgvData]),
    (`Challenge.MSB.msbDecrypt_iff,
      .inst [`Challenge.MSB.msbDecrypt_toLSB]),
    (`Challenge.MSB.run_toLSB,
      .inst [`Challenge.MSB.stepOK_toLSB]),
    (`Challenge.MSB.keySwitch_toLSB,
      .inst [`Challenge.MSB.stepOK_toLSB, `Challenge.MSB.keySwitch_stepOK]),
    (`Challenge.MSB.relin_toLSB,
      .inst [`Challenge.MSB.stepOK_toLSB, `Challenge.MSB.relin_stepOK]),
    (`Challenge.MSB.rescale_toLSB,
      .inst [`Challenge.MSB.stepOK_toLSB, `Challenge.MSB.rescale_stepOK]),
    (`Challenge.MSB.certifyProfile?_sound_msb,
      .inst [`Challenge.Profile.certifyProfile?_sound, `Challenge.MSB.run_toLSB, `Challenge.MSB.msbEncryptsRep_toLSB]),
    (`Challenge.MSBScale.certifyProfile?_user_msb,
      .inst [`Challenge.MSB.certifyProfile?_sound_msb, `Challenge.Scaling.eval_scaled]),
    (`Challenge.Instances.Lattigo.relin_meets_msb,
      .inst [`Challenge.MSB.relin_stepOK, `Challenge.MSB.gadgetKeys_restrict]),
    (`Challenge.Instances.Lattigo.keySwitch_meets_msb,
      .inst [`Challenge.MSB.keySwitch_stepOK, `Challenge.MSB.gadgetKeys_restrict]),
    (`Challenge.Instances.Lattigo.rescale_meets_msb,
      .inst [`Challenge.MSB.rescale_stepOK]),
    (`Challenge.Instances.Lattigo.relin_meets_lsb,
      .inst [`Challenge.Instances.Lattigo.relin_meets_msb, `Challenge.MSB.stepOK_toLSB]),
    (`Challenge.Instances.Lattigo.keySwitch_meets_lsb,
      .inst [`Challenge.Instances.Lattigo.keySwitch_meets_msb, `Challenge.MSB.stepOK_toLSB]),
    (`Challenge.Instances.Lattigo.rescale_meets_lsb,
      .inst [`Challenge.Instances.Lattigo.rescale_meets_msb, `Challenge.MSB.stepOK_toLSB]),
    (`Challenge.Instances.Lattigo.params_keyNoise, .unfolding),
    (`Challenge.Families.stepOK_mul_hps_tol_openfhe,
      .inst [`Challenge.Families.stepOK_mul_hps_anyTol]),
    (`Challenge.Families.stepOK_square_hps_tol_openfhe,
      .inst [`Challenge.Families.stepOK_square_hps_anyTol]),
    (`Challenge.Families.stepOK_mul_poverq_tol_openfhe,
      .inst [`Challenge.Families.stepOK_mul_poverq_anyTol]),
    (`Challenge.Families.stepOK_mul_leveled_tol_openfhe,
      .inst [`Challenge.Families.stepOK_mul_leveled_anyTol]),
    (`Challenge.Families.stepOK_mul_behz_sealBFV_covered,
      .inst [`Challenge.Families.stepOK_mul_behz_covered, `Challenge.Families.sealBFV_covers, `Challenge.Families.sealBFV_behzAuxOK]),
    (`Challenge.Families.sumsOK'_openfhe, .unfolding),
    (`Challenge.Families.sealBFV_behzAuxOK, .closed),
    (`Challenge.Families.sealBFV_sealRule, .closed),
    (`Challenge.Families.lattigo_quantizeAuxOK, .closed),
    (`Challenge.IndCpaDProfile.correct_ksEval,
      .inst [`Challenge.IndCpaDProfile.correct_bgv, `Challenge.IndCpaDProfile.ksEval_meets]),
    (`Challenge.IndCpaDProfile.correct_ksEval_bgvKSSeal,
      .inst [`Challenge.IndCpaDProfile.correct_ksEval, `Challenge.IndCpaDProfile.encOK_bgvKSData]),
    (`Challenge.IndCpaDProfile.keyGen_noisy_bgvKSSeal,
      .inst [`Challenge.IndCpaDProfile.keyGen_keysOK]),
    (`Challenge.IndCpaDProfile.adv_le,
      .inst [`Challenge.IndCpaD.prob_le]),
    (`Challenge.IndCpaDProfile.bfv_adv_le,
      .inst [`Challenge.IndCpaDProfile.adv_le, `Challenge.IndCpaDProfile.correct_bfv]),
    (`Challenge.IndCpaDProfile.bgv_adv_le,
      .inst [`Challenge.IndCpaDProfile.adv_le, `Challenge.IndCpaDProfile.correct_bgv]),
    (`Challenge.IndCpaDLM.probLM_eq,
      .inst [`Challenge.IndCpaDLM.gameLM_eq_gameCPA]),
    (`Challenge.IndCpaDLM.probLM_le,
      .inst [`Challenge.IndCpaDLM.gameLM_eq_gameCPA]),
    (`Challenge.IndCpaDLM.advLM_le,
      .inst [`Challenge.IndCpaDLM.probLM_le]),
    (`Challenge.IndCpaDLM.correct_lm_bgvKSSeal,
      .inst [`Challenge.IndCpaDLM.interpEval_ks, `Challenge.IndCpaDProfile.correct_ksEval_bgvKSSeal]),
    (`Challenge.IndCpaDLM.probLM_eq_bgvKSSeal,
      .inst [`Challenge.IndCpaDLM.probLM_eq, `Challenge.IndCpaDLM.ksStep_interpOK, `Challenge.IndCpaDLM.correct_lm_bgvKSSeal]),
    (`Challenge.IndCpaDLM.advLM_le_bgvKSSeal,
      .inst [`Challenge.IndCpaDLM.advLM_le, `Challenge.IndCpaDLM.ksStep_interpOK, `Challenge.IndCpaDLM.correct_lm_bgvKSSeal]),
    (`Challenge.IndCpaDLM.correct_bfvEval,
      .inst [`Challenge.IndCpaDProfile.correct_bfv, `Challenge.IndCpaDLM.bfvEval_meets]),
    (`Challenge.IndCpaDLM.correct_lm_bfvSeal,
      .inst [`Challenge.IndCpaDLM.correct_bfvEval, `Challenge.IndCpaDLM.encOK_bfvKSData, `Challenge.IndCpaDLM.lm_two_stage_bfv_kernel]),
    (`Challenge.IndCpaDLM.probLM_eq_bfvSeal,
      .inst [`Challenge.IndCpaDLM.probLM_eq, `Challenge.IndCpaDLM.bfvStep_interpOK, `Challenge.IndCpaDLM.correct_lm_bfvSeal]),
    (`Challenge.IndCpaDLM.advLM_le_bfvSeal,
      .inst [`Challenge.IndCpaDLM.advLM_le, `Challenge.IndCpaDLM.bfvStep_interpOK, `Challenge.IndCpaDLM.correct_lm_bfvSeal]),
    (`Challenge.IndCpaDLM.bfvKeyGen_noisy_bfvSeal,
      .inst [`Challenge.IndCpaDLM.bfvKeyGen_keysOK]),
    (`Challenge.IndCpaDLM.correct_lm_exact,
      .inst [`Challenge.IndCpaDProfile.correct_exactEval]),
    (`Challenge.IndCpaDLM.probLM_eq_bgvSealExact,
      .inst [`Challenge.IndCpaDLM.probLM_eq, `Challenge.IndCpaDLM.exactStep_interpOK, `Challenge.IndCpaDLM.correct_lm_exact, `Challenge.IndCpaDProfile.encOK_bgvData]),
    (`Challenge.IndCpaDLM.correct_interp_bfv,
      .inst [`Challenge.IndCpaDProfile.correct_bfv]),
    (`Challenge.IndCpaDLM.gameLM_eq_gameCPA_bfv,
      .inst [`Challenge.IndCpaDLM.gameLM_eq_gameCPA, `Challenge.IndCpaDLM.correct_interp_bfv]),
    (`Challenge.IndCpaDLM.probLM_eq_bfv,
      .inst [`Challenge.IndCpaDLM.probLM_eq, `Challenge.IndCpaDLM.correct_interp_bfv]),
    (`Challenge.IndCpaDLM.probLM_le_bfv,
      .inst [`Challenge.IndCpaDLM.probLM_le, `Challenge.IndCpaDLM.correct_interp_bfv]),
    (`Challenge.IndCpaDLM.advLM_le_bfv,
      .inst [`Challenge.IndCpaDLM.advLM_le, `Challenge.IndCpaDLM.correct_interp_bfv]),
    (`Challenge.IndCpaDLM.correct_interp_bgv,
      .inst [`Challenge.IndCpaDProfile.correct_bgv]),
    (`Challenge.IndCpaDLM.gameLM_eq_gameCPA_bgv,
      .inst [`Challenge.IndCpaDLM.gameLM_eq_gameCPA, `Challenge.IndCpaDLM.correct_interp_bgv]),
    (`Challenge.IndCpaDLM.probLM_eq_bgv,
      .inst [`Challenge.IndCpaDLM.probLM_eq, `Challenge.IndCpaDLM.correct_interp_bgv]),
    (`Challenge.IndCpaDLM.probLM_le_bgv,
      .inst [`Challenge.IndCpaDLM.probLM_le, `Challenge.IndCpaDLM.correct_interp_bgv]),
    (`Challenge.IndCpaDLM.advLM_le_bgv,
      .inst [`Challenge.IndCpaDLM.advLM_le, `Challenge.IndCpaDLM.correct_interp_bgv]),
    (`Challenge.IndCpaDBad.adv_le_sum,
      .inst [`Challenge.IndCpaDProfile.adv_le, `Challenge.IndCpaDBad.bad_le_sum]),
    (`Challenge.IndCpaDBad.adv_eq,
      .inst [`Challenge.IndCpaD.prob_eq]),
    (`Challenge.IndCpaDBad.advLM_le_sum,
      .inst [`Challenge.IndCpaDLM.advLM_le, `Challenge.IndCpaDBad.bad_le_sum]),
    (`Challenge.IndCpaDBad.advLM_eq,
      .inst [`Challenge.IndCpaDLM.probLM_eq]),
    (`Challenge.IndCpaDBad.advLM_le_sum_bfv,
      .inst [`Challenge.IndCpaDBad.advLM_le_sum, `Challenge.IndCpaDLM.correct_interp_bfv]),
    (`Challenge.IndCpaDBad.advLM_le_sum_bgv,
      .inst [`Challenge.IndCpaDBad.advLM_le_sum, `Challenge.IndCpaDLM.correct_interp_bgv]),
    (`Challenge.IndCpaDBad.goodE3_bad_le,
      .inst [`Challenge.IndCpaDBad.normInf_bad_le]),
    (`Challenge.IndCpaDBad.goodE_bad_le_bgvData,
      .inst [`Challenge.IndCpaDBad.goodE3_bad_le]),
    (`Challenge.IndCpaDBad.goodE_bad_le_bgvKSData,
      .inst [`Challenge.IndCpaDBad.goodE3_bad_le]),
    (`Challenge.IndCpaDBad.goodE_bad_le_bfvKSData,
      .inst [`Challenge.IndCpaDBad.goodE3_bad_le]),
    (`Challenge.IndCpaDBad.goodE_bad_le_dataOf,
      .inst [`Challenge.IndCpaDBad.goodE3_bad_le]),
    (`Challenge.IndCpaDLM.admLM_fresh_bgvKSSeal,
      .inst [`Challenge.IndCpaDLM.admLM_fresh_ks]),
    (`Challenge.IndCpaDLM.admLM_fresh_bgvSealExact,
      .inst [`Challenge.IndCpaDLM.admLM_fresh_exact]),
    (`Challenge.IndCpaDLM.admLM_fresh_bfvSeal,
      .inst [`Challenge.IndCpaDLM.admLM_fresh_bfvClass, `Challenge.IndCpaDLM.lm_two_stage_bfv_kernel]),
    (`Challenge.ProfileNamed.coversBFV?_relinBFV,
      .inst [`Challenge.RealizeBFV.relinBFV_stepOK, `Challenge.ProfileNamed.coversBFV?_side, `Challenge.ProfileNamed.coversBFV?_ksBound]),
    (`Challenge.ProfileNamed.coversBFV?_keySwitchBFV,
      .inst [`Challenge.RealizeBFV.keySwitchBFV_stepOK, `Challenge.ProfileNamed.coversBFV?_side, `Challenge.ProfileNamed.coversBFV?_ksBound]),
    (`Challenge.ProfileNamed.coversBFVAt?_relinBFV,
      .inst [`Challenge.RealizeBFV.relinBFV_stepOK, `Challenge.ProfileNamed.coversBFVAt?_side, `Challenge.ProfileNamed.coversBFVAt?_ksBound]),
    (`Challenge.ProfileNamed.coversBFVAt?_keySwitchBFV,
      .inst [`Challenge.RealizeBFV.keySwitchBFV_stepOK, `Challenge.ProfileNamed.coversBFVAt?_side, `Challenge.ProfileNamed.coversBFVAt?_ksBound]),
    (`Challenge.ProfileNamed.coversBGV?_relinOpenFHE,
      .inst [`Challenge.Realize.relinOpenFHE_stepOK, `Challenge.ProfileNamed.coversBGV?_side, `Challenge.ProfileNamed.coversBGV?_ksBound]),
    (`Challenge.ProfileNamed.coversBGV?_keySwitchOpenFHE,
      .inst [`Challenge.Realize.keySwitchOpenFHE_stepOK, `Challenge.ProfileNamed.coversBGV?_side, `Challenge.ProfileNamed.coversBGV?_ksBound]),
    (`Challenge.ProfileNamed.coversBGV?_modSwitchTextbook,
      .inst [`Challenge.Trace.stepOK_modSwitch_textbook_parts, `Challenge.ProfileNamed.coversBGV?_side, `Challenge.ProfileNamed.coversBGV?_msBudget]),
    (`Challenge.ProfileInputs.bgv_low_level_excludes,
      .inst [`Challenge.Params.bgv_small_noise_excludes]),
    (`Challenge.ProfileInputs.certify?_inputs_exist,
      .inst [`Challenge.ProfileInputs.certifyProfile?_inputs_exist_all, `Challenge.Profile.certify?_profile]),
    (`Challenge.ProfileInputs.certifyBFV?_inputs_exist,
      .inst [`Challenge.ProfileInputs.certifyBFVProfile?_inputs_exist_all, `Challenge.Profile.certifyBFV?_profile]),
    (`Challenge.ProfileNamed.coversBGV?_side, .unfolding),
    (`Challenge.ProfileNamed.coversBGV?_ksBound, .unfolding),
    (`Challenge.ProfileNamed.coversBGV?_msBudget, .unfolding),
    (`Challenge.ProfileNamed.coversBFV?_side, .unfolding),
    (`Challenge.ProfileNamed.coversBFV?_ksBound, .unfolding),
    (`Challenge.ProfileNamed.coversBFVAt?_side, .unfolding),
    (`Challenge.ProfileAchieve.bfvRun_eq_irun, .unfolding),
    (`Challenge.ProfileInputs.certifyProfile?_inputs_checked, .unfolding),
    (`Challenge.ProfileInputs.certifyBFVProfile?_plain_checked, .unfolding),
    (`Challenge.IndCpaDLM.embed_bgvSealExact,
      .inst [`Challenge.IndCpaDLM.embed_exact]),
    (`Challenge.IndCpaDLM.embed_bgvKSSeal,
      .inst [`Challenge.IndCpaDLM.embed_ks]),
    (`Challenge.IndCpaDLM.embed_bfvSeal,
      .inst [`Challenge.IndCpaDLM.embed_bfv, `Challenge.IndCpaDLM.lm_two_stage_bfv_kernel]),
    (`Challenge.IndCpaDLM.embedProb_bgvSealExact,
      .inst [`Challenge.IndCpaDLM.embed_bgvSealExact]),
    (`Challenge.IndCpaDLM.embedProb_bgvKSSeal,
      .inst [`Challenge.IndCpaDLM.embed_bgvKSSeal]),
    (`Challenge.IndCpaDLM.embedProb_bfvSeal,
      .inst [`Challenge.IndCpaDLM.embed_bfvSeal]),
    (`Challenge.IndCpaDAttack.attackReduces_of,
      .inst [`Challenge.IndCpaDLM.advLM_le, `Challenge.IndCpaDLM.correct_bfvEval, `Challenge.IndCpaDLM.encOK_bfvKSData, `Challenge.IndCpaDLM.bfvStep_interpOK, `Challenge.IndCpaDLM.bfvKeyGen_keysOK, `Challenge.IndCpaDLM.admLM_fresh_bfvClass]),
    (`Challenge.IndCpaDAttack.sqReduces_of,
      .inst [`Challenge.IndCpaDLM.advLM_le, `Challenge.IndCpaDLM.correct_bfvEval, `Challenge.IndCpaDLM.encOK_bfvKSData, `Challenge.IndCpaDLM.bfvStep_interpOK, `Challenge.IndCpaDLM.bfvKeyGen_keysOK, `Challenge.IndCpaDLM.admLM_fresh_bfvClass]),
    (`Challenge.IndCpaDAttack.cks_ptct_n12,
      .inst [`Challenge.IndCpaDAttack.attackReduces_of, `Challenge.IndCpaDLM.admLM_fresh_bfvClass]),
    (`Challenge.IndCpaDAttack.cks_ptct_n13,
      .inst [`Challenge.IndCpaDAttack.attackReduces_of, `Challenge.IndCpaDLM.admLM_fresh_bfvClass]),
    (`Challenge.IndCpaDAttack.cks_ptct_n14,
      .inst [`Challenge.IndCpaDAttack.attackReduces_of, `Challenge.IndCpaDLM.admLM_fresh_bfvClass]),
    (`Challenge.IndCpaDAttack.cks_ptct_n15,
      .inst [`Challenge.IndCpaDAttack.attackReduces_of, `Challenge.IndCpaDLM.admLM_fresh_bfvClass]),
    (`Challenge.IndCpaDAttack.cks_ptct_n16,
      .inst [`Challenge.IndCpaDAttack.attackReduces_of, `Challenge.IndCpaDLM.admLM_fresh_bfvClass]),
    (`Challenge.IndCpaDAttack.cks_ctct_t257,
      .inst [`Challenge.IndCpaDAttack.sqReduces_of, `Challenge.IndCpaDLM.admLM_fresh_bfvClass]),
    -- true by unfolding definitions
    (`Challenge.Certify.outputsCertified_decrypts, .unfolding),
    (`Challenge.Certify.certify?_worstCase, .unfolding),
    (`Challenge.Headline.analyze_tight, .unfolding),
    (`Challenge.Scheme.phase_two, .unfolding),
    (`Challenge.Scheme.phase_three, .unfolding),
    (`Challenge.FreshNoise.varProxy_ternary, .unfolding),
    (`Challenge.FreshNoiseL2.varProxyL2_support, .unfolding),
    (`Challenge.Budget.msBudgetAt_one, .unfolding),
    (`Challenge.Budget.msBudgetAt_two, .unfolding),
    (`Challenge.Budget.certified_modSwitchAt, .unfolding),
    (`Challenge.Source.tensorParts_two, .unfolding) ]

def stepOKNames : List Name := [`Spec.Trace.StepOK, `Spec.TraceBFV.StepOK]
def runNames : List Name := [`Spec.Trace.Run, `Spec.TraceBFV.Run]

/-- Unfold the head constant while it is a definition declared in a `Spec` or `Challenge` module
(a locked predicate such as `NoiseSoundBGV`, `NoiseTightBGV`; structures such
as `SchemeParamsOK` are not definitions and stay), at most `fuel` times. `StepOK` and `Run` are
kept folded: they are what `isRealizability` looks for. -/
def unfoldLocked (env : Environment) : Nat → Expr → Expr
  | 0, e => e
  | fuel + 1, e =>
    match e.getAppFn with
    | .const c ls =>
      match env.find? c with
      | some (.defnInfo d) =>
        if !stepOKNames.contains c && !runNames.contains c &&
            (moduleOf? env c).any (fun m => m.getRoot == `Challenge || m.getRoot == `Spec) then
          unfoldLocked env fuel
            ((d.value.instantiateLevelParams d.levelParams ls).beta e.getAppArgs)
        else e
      | _ => e
    | _ => e

/-- Strip leading `∀`/`→` binders and metadata (the body keeps its loose bound variables: only
its shape is inspected). Returns the body and whether any binder was stripped. -/
partial def stripForall (env : Environment) (e : Expr) (stripped : Bool := false) : Expr × Bool :=
  match unfoldLocked env 4 e.consumeMData with
  | .forallE _ _ b _ => stripForall env b true
  | e' => (e', stripped)

/-- No `∀`/`→` anywhere on the spine of conjunctions and existentials. -/
partial def isClosedShape (env : Environment) (e : Expr) : Bool :=
  let (b, stripped) := stripForall env e
  !stripped &&
    (if b.isAppOfArity ``And 2 then
      isClosedShape env (b.getArg! 0) && isClosedShape env (b.getArg! 1)
    else if b.isAppOfArity ``Exists 2 then
      match b.getArg! 1 with
      | .lam _ _ body _ => isClosedShape env body
      | _ => true
    else true)

partial def isRejection (env : Environment) (e : Expr) : Bool :=
  let (b, _) := stripForall env e
  let isNoneOrFalse (x : Expr) : Bool :=
    x.consumeMData.isAppOf ``Option.none || x.consumeMData.isConstOf ``Bool.false
  b.isAppOfArity ``Not 1 || b.isAppOfArity ``Ne 3 || b.isConstOf ``False ||
    (b.isAppOfArity ``Eq 3 && (isNoneOrFalse (b.getArg! 2) || isNoneOrFalse (b.getArg! 1))) ||
    (b.isAppOfArity ``And 2 && isClosedShape env b &&
      (isRejection env (b.getArg! 0) || isRejection env (b.getArg! 1)))

partial def isRealizability (env : Environment) (e : Expr) (underExists : Bool := false) : Bool :=
  let (b, _) := stripForall env e
  match b.getAppFn with
  | .const c _ =>
    if stepOKNames.contains c then true
    else if runNames.contains c then underExists
    else if b.isAppOfArity ``Exists 2 then
      match b.getArg! 1 with
      | .lam _ _ body _ => isRealizability env body true
      | _ => false
    else false
  | _ => false

/-- The proof term is `rfl` (after its `fun` binders). -/
partial def isRflProof (e : Expr) : Bool :=
  match e.consumeMData with
  | .lam _ _ b _ => isRflProof b
  | e' =>
    match e'.getAppFn with
    | .const c _ =>
      if c == ``rfl || c == ``Eq.refl || c == ``Iff.rfl || c == ``Iff.refl || c == ``HEq.refl then true
      else if c == ``id && e'.getAppNumArgs == 2 then isRflProof (e'.getArg! 1)
      else false
    | _ => false

/-! ## Replay cache (development runs only; never under `STRICT=1`)

`--replay-cache DIR` skips the kernel replay of a root (a proved pin or a hole) or of a constant of
the `FHE` library whose replay was accepted by an earlier run, when nothing in its closure changed;
`--replay-cache-write DIR` replays everything (as without the flag) and only records the result.
`scripts/check-spec.sh` passes `--replay-cache` only when not strict, and `--replay-cache-write`
under `STRICT=1`; without either flag this program behaves exactly as before the cache existed.

Why skipping is sound. The kernel's verdict on a root is a deterministic function of the toolchain
(kernel) and of the `ConstantInfo`s in the root's closure, which this program reads from the loaded
environment. Each of those `ConstantInfo`s is read from the `.olean` files of one module, its
*provider* (`moduleOf?`; when several modules declare the same auxiliary constant, such as an
equation lemma realized in each of them, the first one loaded provides it). A constant is
*unchanged* if its provider is the one recorded at the last write and that provider's
`.olean`/`.olean.server`/`.olean.private` files have the recorded SHA-256; then its `ConstantInfo`
is the recorded one. If every constant reachable from a root is unchanged, then by induction from
the root (same `ConstantInfo`, so the same names referenced, so the same constants reached) the
closure is exactly the one an earlier run handed to the kernel, which accepted it; so the kernel
would accept it again. The check is: no constant of the root's closure is reachable backwards
(along the reverse dependency edges) from a changed constant, and the root was recorded as
accepted. The same holds for the constants of the `FHE` library. `DIR` holds (written by
`scripts/olean_sha.py`) `env-id.txt`, a digest of the toolchain and this file (a cache written
under another one is ignored), and `olean-sha256.txt`, the SHA-256 of every `.olean` part on the
search path; and (written here, atomically, tab-separated) `replay-accepted.txt`: `ENV <env-id>`,
`M <module> <sha>` for every loaded module, `C <constant> <provider>` for every constant of the
dependency graph (both as 64-bit `Name.hash`es: two constant names of the graph with the same hash,
probability about n²/2⁶⁵ ≈ 10⁻⁹ for its n ≈ 10⁵ constants, could only hide a change of provider), `R <root>` for every accepted root and `F ok` if the `FHE` batch was accepted, all
valid for exactly those hashes and providers. Only acceptances are recorded, never rejections.
What is trusted in addition: the cache directory itself (anyone who can write it can make a
development run skip replay; the strict gate never reads it) and the stat-keyed memo of
`olean_sha.py`. Both may come from the machine's shared store (`GATE_SHARED_CACHE`, see
`scripts/olean_sha.py`): `replay-accepted.txt` is then a record this program wrote in another
checkout of the same machine, under the same env-id; the argument above does not depend on which
run wrote it, only on the hashes and providers it records, which are compared with this run's. -/

/-- The combined SHA-256 of a module's `.olean` parts, from `olean-sha256.txt`; `none` if its
`.olean` was not hashed. -/
def moduleSha (sha : Std.HashMap String String) (m : Name) : IO (Option String) := do
  let p ← try pure (some (← findOLean m)) catch _ => pure none
  let some p := p | return none
  let some h := sha[p.toString]? | return none
  let part (suf : String) := sha.getD (p.toString ++ suf) "-"
  return some s!"{h}:{part ".server"}:{part ".private"}"

/-- Lines of a text file, or `#[]` if it does not exist. -/
def readLines (p : System.FilePath) : IO (Array String) := do
  if !(← p.pathExists) then return #[]
  return ((← IO.FS.readFile p).splitOn "\n").toArray.filter (· != "")

/-! ## Parallel kernel replay

`--replay-jobs N` (default 1) with `N > 1` replaces the serial replay below (root by root, then
the `FHE` batch, each a call of `Lean.Kernel.Environment.replay`) by a parallel one over the same
set of constants. The serial one is kept, unchanged, for `N = 1`.

What is sent to the kernel. The constants to check are the union `U` of the closures (in the
dependency graph `g`) of every root and every `FHE` constant whose replay is not skipped by the
cache: exactly the constants the serial replay sends, each once. `U` is cut into *units*, the
pieces `Lean.Kernel.Environment.replay` sends to the kernel as one declaration: a definition,
theorem, axiom or opaque constant on its own; an inductive block (the types of its `all` list) together with
its constructors and recursors, which the kernel generates from the block and which are then
compared with the ones read from the `.olean`s (`==`, as `replay` does); and the quotient
constants. For each unit, `unitDecl?` builds the `Declaration` exactly as `replay` builds it (same
fields, same order of types and constructors; unsafe and partial constants are not sent, as in
`replay`). A unit depends on the units of the constants its members reference in `g` (a superset
of what `replay` follows: type, value, constructors, recursors, the block).

Unit membership is checked, not assumed (`checkUnit` and the main loop): a unit is accepted only if
none of its members is in the environment before, every member is a constant the kernel produced
from the unit's declaration (so a constant whose `all` list names another block, or a member the
declaration does not declare, is rejected instead of being counted as accepted unchecked), every
inductive member has the block's `all` list, and constructors and recursors are equal (`==`) to
the generated ones. A unit whose head is unsafe or partial is skipped, as `replay` skips such
constants, only if every member is unsafe or partial; otherwise it is rejected.

The schedule. The quotient (`Quot`, `Quot.mk`, `Quot.lift`, `Quot.ind`) and its closure, with the
closure of `Eq` (which `replay` adds before the quotient), are first replayed by `Lean.Kernel.Environment.replay` itself into the empty environment `E₀` (the kernel
records that the quotient was initialised, which `addDecl` of anything else does not). Then a unit
whose dependencies have all been accepted is handed to a worker task together with the current
environment `E`, which at that moment contains its dependencies, all of them already accepted by
the kernel, and otherwise only other accepted constants (`E` only grows). The worker calls
`Kernel.Environment.addDeclCore` (the kernel's type checker: the same call `replay` makes) on the
unit's declaration in `E`, and for an inductive block checks the generated constructors and
recursors against the `.olean`'s. Only when the kernel accepted it does the main loop add the same
`Declaration` value to its environment, with `addDeclWithoutChecking` (after checking again that
none of the unit's names is already there, since `addDeclWithoutChecking` would replace a
definition of the same name, and that every member is declared afterwards): it was checked, by the
kernel, in an environment that is a subset of the one it is added to, and the extra constants are
themselves kernel-checked, so the result is the environment the serial replay would build by
checking it there. A unit the kernel rejects is never added; the units that depend on it (directly
or not) are not sent at all and count as rejected, and so do units on a dependency cycle (which
constants the kernel accepted cannot form; only altered data can).

Why the verdicts are those of the serial replay. Whether the kernel accepts a declaration depends
only on the declaration and on the constants it references being present (and themselves
checked); other constants in the environment do not matter (names are unique, so there is no
clash). The serial replay rejects a root iff the closure of the root contains a constant the
kernel rejects or that depends on one (a rejected root does not extend the environment, so later
roots re-send what they share with it and are judged on their own); and it rejects the `FHE` batch
iff its closure does. Here a root (and the `FHE` batch) is rejected iff a constant of its closure
is in a rejected or skipped unit, which is the same condition. Nothing is admitted without having
been checked: the only constants in any environment handed to the kernel are the ones of `E₀`
(checked by `replay`) and of units the kernel accepted. The counts on the `KERNEL` lines are
computed from the verdicts as the serial replay counts them (the union of the closures of the
accepted roots; then the further constants of the `FHE` closure). The error text of a rejection
is the kernel's error on one rejected unit in the closure (for a root, the first rejected unit by
name that reaches it; for the `FHE` batch, the least error text), in the form
`replay` gives it: the same text as the serial replay when the closure contains one rejected
declaration; with several, the two may name different ones (the verdicts are the same).

A dependency the kernel needs but that `g` does not record could only make a unit fail with
"unknown constant" (a false rejection, which is visible as a difference from the serial
replay's verdicts), never make anything be accepted: the kernel never accepts a declaration that
mentions a constant absent from its environment. -/

/-- The unit of `U` a constant belongs to (see "Parallel kernel replay"): an inductive type, its
constructors and recursors belong to the first type of its block; quotient constants to `Quot`;
everything else is its own unit. -/
def unitKey (find? : Name → Option ConstantInfo) (n : Name) : Name :=
  match find? n with
  | some (.inductInfo v) => v.all.headD n
  | some (.ctorInfo v) =>
    match find? v.induct with
    | some (.inductInfo iv) => iv.all.headD v.induct
    | _ => v.induct
  | some (.recInfo v) => v.all.headD n
  | some (.quotInfo _) => ``Quot
  | _ => n

/-- The declaration `Lean.Kernel.Environment.replay` sends to the kernel for the unit `k`, built
the same way: `.ok none` if it sends nothing (unsafe or partial constants), `.error` if the unit is
malformed (a member of an inductive block that is not in the environment). -/
def unitDecl? (find? : Name → Option ConstantInfo) (k : Name) : Except String (Option Declaration) := do
  let some ci := find? k | throw s!"unknown constant {k}"
  if ci.isUnsafe || ci.isPartial then return none
  match ci with
  | .defnInfo i => return some (.defnDecl i)
  | .thmInfo i => return some (.thmDecl i)
  | .axiomInfo i => return some (.axiomDecl i)
  | .opaqueInfo i => return some (.opaqueDecl i)
  | .inductInfo i =>
    let types ← i.all.mapM fun t => do
      let some (.inductInfo ti) := find? t | throw s!"inductive block of {k}: no inductive {t}"
      let ctors ← ti.ctors.mapM fun c => do
        let some cc := find? c | throw s!"inductive {t}: no constructor {c}"
        pure ({ name := c, type := cc.type } : Constructor)
      pure ({ name := t, type := ti.type, ctors } : InductiveType)
    return some (.inductDecl i.levelParams i.numParams types false)
  | _ => throw s!"{k} is not the head of a unit"

/-- The kernel's check of one unit in `kenv`, as `Lean.Kernel.Environment.replay` does it: the
declaration through `addDeclCore`, then the generated constructors and recursors compared with the
ones read from the `.olean`s. -/
def checkUnit (find? : Name → Option ConstantInfo) (kenv : Kernel.Environment) (k : Name) (d : Declaration)
    (members : Array Name) : IO Unit := do
  for m in members do
    if (kenv.find? m).isSome then
      throw <| .userError s!"while replaying declaration '{k}': {m} is already declared"
  match kenv.addDeclCore 0 0 d (cancelTk? := none) with
  | .error ex =>
    throw <| .userError s!"while replaying declaration '{k}':\n{← (ex.toMessageData {}).toString}"
  | .ok kenv' =>
    for m in members do
      -- every member of the unit is a constant this declaration declares (a member that the
      -- declaration does not produce would otherwise count as accepted without a check)
      if (kenv'.find? m).isNone then
        throw <| .userError s!"while replaying declaration '{k}': {m} is in its unit but not declared by it"
      match find? m with
      | some (.inductInfo info') =>
        match kenv'.find? m with
        | some (.inductInfo info) =>
          unless info.all == info'.all do
            throw <| .userError s!"Invalid inductive {m} (block {info'.all}, generated {info.all})"
        | _ => throw <| .userError s!"No such inductive {m}"
      | some (.ctorInfo info') =>
        match kenv'.find? m with
        | some (.ctorInfo info) => unless info == info' do throw <| .userError s!"Invalid constructor {m}"
        | _ => throw <| .userError s!"No such constructor {m}"
      | some (.recInfo info') =>
        match kenv'.find? m with
        | some (.recInfo info) => unless info == info' do throw <| .userError s!"Invalid recursor {m}"
        | _ => throw <| .userError s!"No such recursor {m}"
      | _ => pure ()

/-- Parallel replay of the constants `todo` (closed under `g`) into an empty environment, with at
most `jobs` kernel checks at a time (see "Parallel kernel replay"). Returns the constants that
are rejected or depend on a rejected one, each with the error of a rejected unit (the first by
name) it depends on, and the number of units. -/
def parallelReplay (find? : Name → Option ConstantInfo) (g : Std.HashMap Name (Array Name))
    (rev : Std.HashMap Name (List Name)) (todo : Array Name) (jobs : Nat) :
    IO (Std.HashMap Name String × Nat) := do
  let t0 ← IO.monoMsNow
  -- 1. The quotient and its closure: `replay` itself, into the empty environment.
  let quot := todo.filter fun n => find? n matches some (.quotInfo _)
  let mut pre : NameSet := {}
  for q in quot do pre := pre.union (reach g q)
  -- `replay` adds the quotient after `Eq` (the types of `Quot.lift` and `Quot.ind` mention it)
  if !quot.isEmpty && g.contains ``Eq then pre := pre.union (reach g ``Eq)
  let mut kenv := (← mkEmptyEnvironment).toKernelEnv
  -- unit key ↦ error, for every rejected unit (and the prelude, as one unit `Quot`)
  let mut failedUnits : Array (Name × String) := #[]
  let mut badSeeds : Array (Name × Name) := #[]   -- (constant, the unit key whose error it gets)
  if !pre.isEmpty then
    let mut m : Std.HashMap Name ConstantInfo := {}
    for n in pre.toList do
      if let some ci := find? n then m := m.insert n ci
    try
      kenv ← kenv.replay m
    catch e =>
      failedUnits := failedUnits.push (``Quot, toString e)
      for n in pre.toList do badSeeds := badSeeds.push (n, ``Quot)
  -- 2. Units of the rest, and their dependencies.
  let mut keyIdx : Std.HashMap Name Nat := {}   -- unit key ↦ unit
  let mut unitOf : Std.HashMap Name Nat := {}   -- constant of `todo` outside the prelude ↦ unit
  let mut keys : Array Name := #[]
  let mut members : Array (Array Name) := #[]
  for n in todo do
    if pre.contains n then continue
    let k := unitKey find? n
    match keyIdx[k]? with
    | some i =>
      members := members.modify i (·.push n)
      unitOf := unitOf.insert n i
    | none =>
      unitOf := unitOf.insert n keys.size
      keyIdx := keyIdx.insert k keys.size
      keys := keys.push k
      members := members.push #[n]
  let nu := keys.size
  -- unit ↦ the units it depends on (constants outside `unitOf` are in the prelude: checked)
  let mut deps : Array (Array Nat) := Array.replicate nu #[]
  let mut dependents : Array (Array Nat) := Array.replicate nu #[]
  for i in [0:nu] do
    let mut ds : Array Nat := #[]
    for n in members[i]! do
      for d in g.getD n #[] do
        if let some j := unitOf[d]? then
          if j != i && !ds.contains j then ds := ds.push j
    deps := deps.set! i ds
    for j in ds do dependents := dependents.modify j (·.push i)
  let tSetup ← IO.monoMsNow
  let mut dur : Array Nat := Array.replicate nu 0
  let mut cp : Array Nat := Array.replicate nu 0
  let mut busy : Nat := 0
  -- 3. Schedule: a unit runs when every unit it depends on is accepted.
  let mut waiting : Array Nat := deps.map (·.size)
  let mut ready : Array Nat := #[]
  for i in [0:nu] do
    if waiting[i]! == 0 then ready := ready.push i
  -- `prelude failed`: nothing may run (every unit could depend on the quotient's closure only
  -- through `g`; to stay on the safe side, a failed prelude rejects every unit).
  if !failedUnits.isEmpty then ready := #[]
  let mut readyPos := 0
  let mut done : Array Bool := Array.replicate nu false
  let mut inflight : Array (Nat × Declaration × Task (Except IO.Error Nat)) := #[]
  let jobs := max jobs 1
  while readyPos < ready.size || !inflight.isEmpty do
    while readyPos < ready.size && inflight.size < jobs do
      let i := ready[readyPos]!
      readyPos := readyPos + 1
      match unitDecl? find? keys[i]! with
      | .error e => failedUnits := failedUnits.push (keys[i]!, e)
      | .ok none =>   -- nothing to send (unsafe or partial), as `replay`: never added
        -- only if every member is itself unsafe or partial (`replay` skips exactly those)
        if members[i]!.all (fun m => (find? m).any fun ci => ci.isUnsafe || ci.isPartial) then
          done := done.set! i true
        else
          failedUnits := failedUnits.push (keys[i]!,
            s!"while replaying declaration '{keys[i]!}': not sent (unsafe or partial), but its unit has safe members")
      | .ok (some d) =>
        let t ← IO.asTask (do
          let t0 ← IO.monoNanosNow
          checkUnit find? kenv keys[i]! d members[i]!
          return (← IO.monoNanosNow) - t0)
        inflight := inflight.push (i, d, t)
      -- (a unit with nothing to send releases nothing: its dependents wait forever and are
      -- reported below as depending on it, which the kernel would do with "unknown constant")
    let ts := inflight.toList.map (·.2.2)
    match ts with
    | [] => continue
    | t :: ts => let _ ← IO.waitAny (t :: ts)
    let mut still : Array (Nat × Declaration × Task (Except IO.Error Nat)) := #[]
    for (i, d, t) in inflight do
      if !(← IO.hasFinished t) then
        still := still.push (i, d, t)
        continue
      match t.get with
      | .error e => failedUnits := failedUnits.push (keys[i]!, toString e)
      | .ok ns =>
        dur := dur.set! i ns
        busy := busy + ns
        cp := cp.set! i (ns + (deps[i]!.foldl (fun a j => max a cp[j]!) 0))
        -- never replace a constant: every member must be new here, and declared afterwards
        let dup := members[i]!.filter fun m => (kenv.find? m).isSome
        let added : Except Kernel.Exception Kernel.Environment :=
          if !dup.isEmpty then .error (.other s!"already declared: {dup}") else
          match kenv.addDeclWithoutChecking d with
          | .ok e =>
            if members[i]!.all (fun m => (e.find? m).isSome) then .ok e
            else .error (.other "a member of the unit is not declared by its declaration")
          | .error ex => .error ex
        match added with
        | .error ex =>
          failedUnits := failedUnits.push (keys[i]!, s!"while adding the accepted declaration '{keys[i]!}':\n{← (ex.toMessageData {}).toString}")
        | .ok kenv' =>
          kenv := kenv'
          done := done.set! i true
          for j in dependents[i]! do
            waiting := waiting.modify j (· - 1)
            if waiting[j]! == 0 then ready := ready.push j
    inflight := still
  let tLoop ← IO.monoMsNow
  let maxCp := cp.foldl max 0
  let top := (Array.range nu).qsort (fun a b => dur[a]! > dur[b]!) |>.extract 0 3
  IO.eprintln s!"[PinStatus]   parallel replay: {nu} units; setup {tSetup - t0} ms, schedule {tLoop - tSetup} ms, kernel time {busy / 1000000} ms in all, longest chain {maxCp / 1000000} ms; slowest (ms): {top.toList.map fun i => (keys[i]!, dur[i]! / 1000000)}"
  -- 4. Every unit not accepted (rejected, or never sent because it depends on a rejected or
  -- unsent unit) is rejected, with the error of a rejected unit it depends on.
  failedUnits := failedUnits.qsort (fun a b => a.1.toString < b.1.toString)
  for (k, _) in failedUnits do
    if let some i := keyIdx[k]? then
      for n in members[i]! do badSeeds := badSeeds.push (n, k)
  for i in [0:nu] do
    unless done[i]! do
      for n in members[i]! do badSeeds := badSeeds.push (n, keys[i]!)
  let errOf : Std.HashMap Name String := failedUnits.foldl (fun m (k, e) => m.insert k e) {}
  let mut bad : Std.HashMap Name String := {}
  let mut todoB : Array (Name × Name) := badSeeds.reverse   -- first seeds popped first
  while h : todoB.size > 0 do
    let (n, k) := todoB.back
    todoB := todoB.pop
    if bad.contains n then continue
    let e := errOf.getD k s!"while replaying declaration '{k}': not sent to the kernel: it depends on a rejected declaration, on one that is not sent (unsafe or partial), or on itself (a dependency cycle)"
    bad := bad.insert n e
    for d in rev.getD n [] do
      unless bad.contains d do todoB := todoB.push (d, k)
  return (bad, nu)

end PinStatus

open PinStatus in
def main (args : List String) : IO UInt32 := do
  let outDir? := args.head?
  -- `--replay-jobs N` (last arguments): parallel kernel replay with N workers (see "Parallel
  -- kernel replay"); default 1, the serial replay.
  let (rest, jobsArg) : List String × Option Nat :=
    match (args.drop 1).reverse with
    | n :: "--replay-jobs" :: r => (r.reverse, some (n.toNat?.getD 0))
    | _ => (args.drop 1, none)
  let replayJobs := jobsArg.getD 1
  -- `--replay-cache DIR` (read and write) or `--replay-cache-write DIR` (write only); see above.
  let (cacheDir?, cacheRead) : Option System.FilePath × Bool :=
    match rest with
    | ["--replay-cache", d] => (some d, true)
    | ["--replay-cache-write", d] => (some d, false)
    | _ => (none, false)
  if (!rest.isEmpty && cacheDir?.isNone) || replayJobs == 0 || rest.contains "--replay-jobs" then
    IO.eprintln s!"usage: PinStatus [OUT_DIR [--replay-cache DIR | --replay-cache-write DIR] [--replay-jobs N]]"
    return 2
  let tStart ← IO.monoMsNow
  initSearchPath (← findSysroot)
  -- The project, as data. No initializer or environment extension of an imported module runs.
  -- Besides `Challenge` and `Validation`: the root `Spec` (for the file-coverage check) and every
  -- file under `FHE/` (for the axiom scan and replay of the whole untrusted library).
  let fheFiles ← leanFilesUnder "FHE" `FHE
  -- The proofs that `Spec/` agrees with the independent re-specification (`Respec/Equiv/`): under
  -- the same axiom scan and kernel replay as `FHE` (reported in the `FHE ...` lines).
  let respecFiles ← leanFilesUnder "Respec/Equiv" (`Respec ++ `Equiv)
  let env ← importModules
    (#[{ module := `Challenge }, { module := `Validation }, { module := `Spec }] ++
      (fheFiles ++ respecFiles).map fun m => { module := m }) {}
    (loadExts := false)
  IO.eprintln s!"[PinStatus] loaded {env.header.moduleNames.size} modules in {← timeSince tStart}"
  let mut failed : Nat := 0
  let mut out : Array String := #[]   -- report lines, printed at the end in a fixed order

  /- ## Module graph -/
  for m in env.header.moduleNames do
    if isLockedModule m then
      for d in (importClosure env m).toList do
        unless isTrustedModule d || isLockedModule d do
          failed := failed + 1
          out := out.push s!"MODULES BAD locked module {m} imports {d}"
  let mut holeFHE : Array Name := #[]
  for d in (importClosure env holesModule).toList do
    if d.getRoot == `FHE then holeFHE := holeFHE.push d
    else unless isTrustedModule d || isLockedModule d do
      failed := failed + 1
      out := out.push s!"MODULES BAD the holes' import closure contains {d}"
  holeFHE := holeFHE.qsort (·.toString < ·.toString)
  out := out.push s!"MODULES holes closure: {holeFHE.toList}"
  -- No constant in the `Challenge` namespace is declared outside a `Challenge` module.
  for (n, _) in env.constants.toList do
    if (`Challenge).isPrefixOf n then
      if let some m := moduleOf? env n then
        unless m.getRoot == `Challenge do
          failed := failed + 1
          out := out.push s!"MODULES BAD {n} is declared in {m}, outside Challenge"

  IO.eprintln s!"[PinStatus]   at {← timeSince tStart}: start of File coverage"
  /- ## File coverage: no trusted or locked file outside the audited import closures -/
  let challengeClosure := importClosure env `Challenge
  let specClosure := importClosure env `Spec
  let challengeFiles ← leanFilesUnder "Challenge" `Challenge
  let specFiles ← leanFilesUnder "Spec" `Spec
  let mut unpinned : Array Name := #[]
  for m in challengeFiles do
    unless challengeClosure.contains m do
      failed := failed + 1
      out := out.push s!"MODULES BAD file for {m} is under Challenge/ but not in the import closure of Challenge.lean"
  for m in specFiles do
    unless specClosure.contains m do
      if unpinnedSpecPrefixes.any (·.isPrefixOf m) then unpinned := unpinned.push m
      else
        failed := failed + 1
        out := out.push s!"MODULES BAD file for {m} is under Spec/ but neither in the import closure of Spec.lean nor on the allowlist {unpinnedSpecPrefixes}"
  out := out.push s!"MODULES files: {challengeFiles.size} under Challenge/ all imported by Challenge.lean; {specFiles.size} under Spec/, {specFiles.size - unpinned.size} imported by Spec.lean, {unpinned.size} experimental and UNPINNED (allowlist {unpinnedSpecPrefixes}): {unpinned.toList}"

  IO.eprintln s!"[PinStatus]   at {← timeSince tStart}: start of Pins: statement identity"
  /- ## Pins: statement identity -/
  let thms := env.constants.fold (init := #[]) fun acc n ci =>
    if (`Challenge).isPrefixOf n && !n.isInternal && ci matches .thmInfo _ &&
        (moduleOf? env n).any (·.getRoot == `Challenge) then acc.push n else acc
  let thms := thms.qsort (·.toString < ·.toString)
  -- Field projections of `Prop` structures declared in `Challenge` are not pins.
  let projections := thms.filter (isStructProjection env)
  let names := thms.filter (!isStructProjection env ·)
  for n in projections do
    out := out.push s!"PROJECTION {n} (generated field projection of the structure {n.getPrefix}; not a pin, not counted)"
  -- verdict per pin; `none` = candidate for PROVEN, decided after axioms and replay
  let mut verdict : Std.HashMap Name String := {}
  let mut candidates : Array (Name × Name) := #[]
  for n in names do
    let v := n.replacePrefix `Challenge `Validation
    let some ci := env.find? n | continue
    match env.find? v with
    | none => verdict := verdict.insert n "MISSING"
    | some (.thmInfo vi) =>
      let same : Bool :=
        ci.levelParams.length == vi.levelParams.length &&
          (let ty := vi.type.instantiateLevelParams vi.levelParams (ci.levelParams.map Level.param)
           ci.type == ty || Kernel.isDefEqGuarded env {} ci.type ty)
      if same then candidates := candidates.push (n, v)
      else verdict := verdict.insert n "MISMATCH"
    | some _ => verdict := verdict.insert n "MISMATCH (Validation constant is not a theorem)"

  IO.eprintln s!"[PinStatus]   at {← timeSince tStart}: start of Headlines: each locked"
  /- ## Headlines: each locked statement is literally `<locked predicate> <hole>` -/
  let mut badStatements : NameSet := {}
  for (pinModule, predModule, rows) in headlineGroups do
   for (pin, pred, hole) in rows do
    let why? : Option String :=
      match env.find? pin, env.find? pred with
      | some (.thmInfo t), some predCi =>
        if moduleOf? env pin != some pinModule then some s!"declared in {moduleOf? env pin}"
        else if moduleOf? env pred != some predModule then
          some s!"{pred} is declared in {moduleOf? env pred}, not {predModule}"
        else if !(predCi matches .defnInfo _) || !predCi.levelParams.isEmpty then
          some s!"{pred} is not a universe-monomorphic definition"
        else if !t.levelParams.isEmpty then some "has universe parameters"
        else if t.type != mkApp (mkConst pred) (mkConst hole) then
          some s!"statement is not literally `{pred} {hole}`: {t.type}"
        else none
      | _, _ => some "theorem or predicate not found"
    match why? with
    | none => out := out.push s!"HEADLINE {pin} OK"
    | some why =>
      failed := failed + 1
      badStatements := badStatements.insert pin
      out := out.push s!"HEADLINE {pin} BAD {why}"

  -- Every theorem declared in a module that imports the hole is a row of the table.
  let tabled : List Name := headlineGroups.flatMap fun g => g.2.2.map (·.1)
  for n in names do
    if (moduleOf? env n).any headlineModules.contains && !tabled.contains n then
      failed := failed + 1
      badStatements := badStatements.insert n
      out := out.push s!"HEADLINE {n} BAD declared in a headline module but not in the table"

  IO.eprintln s!"[PinStatus]   at {← timeSince tStart}: start of Dependency graph of everything"
  /- ## Dependency graph of everything to replay -/
  let roots := candidates.map (·.2) ++ (holes.map (·.1)).toArray.filter env.contains
  -- Every constant declared in a module of the untrusted `FHE` library.
  let mut fheConsts : Array Name := #[]
  for h : i in [0:env.header.moduleNames.size] do
    let m := env.header.moduleNames[i]
    if m.getRoot == `FHE || (`Respec ++ `Equiv).isPrefixOf m then
      if let some md := env.header.moduleData[i]? then
        fheConsts := fheConsts ++ md.constNames
  fheConsts := fheConsts.qsort (·.toString < ·.toString)
  -- Every constant declared in a `Spec` or `Challenge` module (for the `LOCKED` check below).
  let mut lockedConsts : Array Name := #[]
  for h : i in [0:env.header.moduleNames.size] do
    let m := env.header.moduleNames[i]
    if m.getRoot == `Spec || m.getRoot == `Challenge then
      if let some md := env.header.moduleData[i]? then
        lockedConsts := lockedConsts ++ md.constNames
  let t1 ← IO.monoMsNow
  let g ← match depGraph env (roots ++ fheConsts ++ lockedConsts) with
    | .ok g => pure g
    | .error u =>
      IO.println s!"KERNEL FAILED: unknown constant {u}"
      return 1
  -- axioms reachable from each root
  let axiomsOf (r : Name) : List Name :=
    (reach g r).toList.filter fun n => env.find? n matches some (.axiomInfo _)

  IO.eprintln s!"[PinStatus]   at {← timeSince tStart}: start of The whole FHE library"
  /- ## The whole `FHE` library: no `sorryAx`, no non-standard axiom -/
  -- Constants from which a bad axiom is reachable: reverse reachability from the bad axioms.
  let mut rev : Std.HashMap Name (List Name) := {}
  let mut badAxioms : Array Name := #[]
  for (n, ds) in g.toList do
    if env.find? n matches some (.axiomInfo _) then
      unless allowedAxioms.contains n do badAxioms := badAxioms.push n
    for d in ds do rev := rev.alter d fun l => some (n :: l.getD [])
  let mut tainted : Std.HashMap Name Name := {}   -- constant ↦ a bad axiom it depends on
  for a in badAxioms do
    let mut todo := #[a]
    while h : todo.size > 0 do
      let n := todo.back
      todo := todo.pop
      if tainted.contains n then continue
      tainted := tainted.insert n a
      for d in rev.getD n [] do
        unless tainted.contains d do todo := todo.push d
  let fheBad := fheConsts.filter tainted.contains
  for n in fheBad.toList.take 20 do
    out := out.push s!"FHE BAD {n} (in {moduleOf? env n}) depends on the axiom {tainted.getD n .anonymous}"
  if fheBad.size > 20 then out := out.push s!"FHE BAD ... and {fheBad.size - 20} more"
  failed := failed + fheBad.size
  out := out.push s!"FHE axioms: {fheConsts.size} constants in {fheFiles.size} modules under FHE/ and {respecFiles.size} under Respec/Equiv/ scanned, {fheBad.size} depend on sorryAx or a non-standard axiom"

  IO.eprintln s!"[PinStatus]   at {← timeSince tStart}: start of Locked code: sorry"
  /- ## Locked code: `sorry` only as the body of a pin -/
  -- A locked theorem's proof is `sorry` by design; its *statement*, and every locked constant that
  -- is not a theorem (definitions, structures, instances, their auxiliary constants), must not
  -- depend on `sorryAx`: reachability that does not pass through the body of a locked theorem.
  let isLockedThm (n : Name) : Bool :=
    (env.find? n matches some (.thmInfo _)) &&
      (moduleOf? env n).any fun m => m.getRoot == `Spec || m.getRoot == `Challenge
  -- Reverse reachability from `sorryAx` that stops at locked theorems (their bodies are `sorry`).
  let mut sorryTaint : NameSet := {}
  let mut todoS : Array Name := #[``sorryAx]
  while h : todoS.size > 0 do
    let n := todoS.back
    todoS := todoS.pop
    if sorryTaint.contains n then continue
    sorryTaint := sorryTaint.insert n
    unless isLockedThm n do
      for d in rev.getD n [] do
        unless sorryTaint.contains d do todoS := todoS.push d
  let mut lockedBad : Nat := 0
  let mut lockedChecked : Nat := 0
  for n in lockedConsts do
    let some ci := env.find? n | continue
    lockedChecked := lockedChecked + 1
    -- a statement that mentions a pin would put a proof inside a statement: also refused
    let hit : Bool :=
      if isLockedThm n then ci.type.getUsedConstants.any fun c => sorryTaint.contains c
      else sorryTaint.contains n
    if hit then
      lockedBad := lockedBad + 1
      if lockedBad ≤ 20 then
        out := out.push s!"LOCKED BAD {n} (in {moduleOf? env n}): a locked definition or the statement of a locked theorem depends on sorryAx or on a pin"
  failed := failed + lockedBad
  out := out.push s!"LOCKED sorry: {lockedChecked} constants of Spec and Challenge modules checked; {lockedBad} definitions or statements depend on sorryAx (the only sorry in locked code is the body of a pin)"

  IO.eprintln s!"[PinStatus]   at {← timeSince tStart}: start of Holes: honest"
  /- ## Holes: honest, computable definitions of the fixed types -/
  -- `moduleOf?` with the module array fetched once (`env.header` is not free per call).
  let modNames := env.header.moduleNames
  let provider (n : Name) : Option Name := (env.getModuleIdxFor? n).bind fun i => modNames[i.toNat]?
  let mut holeBad : Std.HashMap Name (Array String) := {}
  for (hole, ty, tyModule) in holes do
    let mut bad : Array String := #[]
    match env.find? hole with
    | some (.defnInfo d) =>
      if moduleOf? env hole != some holesModule then
        bad := bad.push s!"declared in {moduleOf? env hole}, not {holesModule}"
      if !d.levelParams.isEmpty then bad := bad.push "has universe parameters"
      if d.type != mkConst ty then bad := bad.push s!"type is {d.type}, not {ty}"
      if moduleOf? env ty != some tyModule then
        bad := bad.push s!"{ty} is declared in {moduleOf? env ty}, not {tyModule}"
      if d.safety != .safe then bad := bad.push "is unsafe or partial"
      if isNoncomputable env hole then bad := bad.push "is noncomputable"
      let closure := (reach g hole).toList   -- computed once (`axiomsOf hole` is its axioms)
      let axs := closure.filter fun n => env.find? n matches some (.axiomInfo _)
      if axs.contains ``sorryAx then bad := bad.push "closure contains sorryAx"
      let other := axs.filter fun a => !allowedAxioms.contains a && a != ``sorryAx
      unless other.isEmpty do bad := bad.push s!"closure uses axioms {other}"
      for c in closure do
        if (provider c).any isTrustedModule then continue
        if (Compiler.getImplementedBy? env c).isSome then
          bad := bad.push s!"closure contains {c}, which has @[implemented_by]"
        if isExtern env c then bad := bad.push s!"closure contains {c}, which has @[extern]"
        if let some ci := env.find? c then
          if ci matches .opaqueInfo _ then bad := bad.push s!"closure contains opaque {c}"
          if ci.isUnsafe then bad := bad.push s!"closure contains unsafe {c}"
          if ci.isPartial then bad := bad.push s!"closure contains partial {c}"
    | some _ => bad := bad.push "is not a definition (axiom, opaque, theorem, ...)"
    | none => bad := bad.push "not found"
    holeBad := holeBad.insert hole bad

  IO.eprintln s!"[PinStatus] statement, axiom, headline, hole and LOCKED checks done at {← timeSince tStart}"
  /- ## Replay cache: which constants are unchanged since the last recorded acceptance -/
  let tc ← IO.monoMsNow
  let mut curSha : Std.HashMap Name String := {}
  let mut envId : String := ""
  -- Constants of `g` that changed, or depend on one that changed (see "Replay cache" above).
  let mut dirtyC : NameSet := {}
  let mut oldRoots : Std.HashSet String := {}
  let mut oldFheOk := false
  if let some dir := cacheDir? then
    let mut sha : Std.HashMap String String := {}
    for l in ← readLines (dir / "olean-sha256.txt") do
      match l.splitOn " " with
      | [h, p] => sha := sha.insert p h
      | _ => pure ()
    envId := ((← readLines (dir / "env-id.txt")).getD 0 "").trimAscii.toString
    for m in env.header.moduleNames do
      if let some h ← moduleSha sha m then curSha := curSha.insert m h
    if cacheRead && envId != "" then
      let mut oldSha : Std.HashMap String String := {}
      let mut oldProv : Std.HashMap UInt64 UInt64 := {}
      let mut oldEnv := ""
      for l in ← readLines (dir / "replay-accepted.txt") do
        match l.splitOn "\t" with
        | ["ENV", e] => oldEnv := e
        | ["M", m, h] => oldSha := oldSha.insert m h
        | ["C", c, m] =>
          if let (some c, some m) := (c.toNat?, m.toNat?) then
            oldProv := oldProv.insert c.toUInt64 m.toUInt64
        | ["R", r] => oldRoots := oldRoots.insert r
        | ["F", "ok"] => oldFheOk := true
        | _ => pure ()   -- unreadable lines only make the cache miss
      if oldEnv == envId then
        let mut modClean : Std.HashMap Name Bool := {}
        for m in env.header.moduleNames do
          modClean := modClean.insert m ((curSha[m]?).isSome && curSha[m]? == oldSha[m.toString]?)
        -- A constant is changed if the module its `ConstantInfo` comes from has other `.olean`
        -- bytes, or another module provides it now (duplicated auxiliary declarations: the
        -- first module loaded wins), or it was not recorded.
        let mut todoD : Array Name := #[]
        for (n, _) in g.toList do
          let ok := match provider n with
            | some m => modClean.getD m false && oldProv[n.hash]? == some m.hash
            | none => false
          unless ok do todoD := todoD.push n
        -- ... and so is everything that depends on a changed constant.
        while h : todoD.size > 0 do
          let n := todoD.back
          todoD := todoD.pop
          if dirtyC.contains n then continue
          dirtyC := dirtyC.insert n
          for d in rev.getD n [] do
            unless dirtyC.contains d do todoD := todoD.push d
      else
        oldRoots := {}; oldFheOk := false
  let cachedRoot (r : Name) : Bool := cacheRead && oldRoots.contains r.toString && !dirtyC.contains r
  let cachedFhe (r : Name) : Bool := cacheRead && oldFheOk && !dirtyC.contains r
  if cacheDir?.isSome then
    IO.eprintln s!"[PinStatus] replay cache read in {← timeSince tc} ({dirtyC.size} changed constants)"

  /- ## Kernel replay, root by root, into one environment that starts empty -/
  -- Each root's not-yet-checked constants go to the kernel; a rejected root does not extend the
  -- environment, so later roots re-send what they share with it and are judged on their own.
  -- With `--replay-cache`, a root accepted earlier with an unchanged closure is skipped.
  -- With `--replay-jobs N`, N > 1: the same constants, each checked once, in parallel (see
  -- "Parallel kernel replay"), with the same verdicts and the same counts.
  let mut rejected : Std.HashMap Name String := {}
  let mut replayed : Nat := 0
  let mut skippedRoots : Nat := 0
  let mut fheSkipped : Nat := 0
  let mut fheAccepted := false
  if replayJobs > 1 then
    let roots' := roots.filter (!cachedRoot ·)
    skippedRoots := roots.size - roots'.size
    let fhe' := fheConsts.filter (!cachedFhe ·)
    fheSkipped := fheConsts.size - fhe'.size
    -- Union of the closures from `rs`, not entering `stop`.
    let closureOf (rs : Array Name) (stop : Name → Bool) : NameSet := Id.run do
      let mut seen : NameSet := {}
      let mut todo := rs
      while h : todo.size > 0 do
        let n := todo.back
        todo := todo.pop
        if seen.contains n || stop n then continue
        seen := seen.insert n
        for d in g.getD n #[] do
          unless seen.contains d do todo := todo.push d
      return seen
    -- exactly the constants the serial replay sends
    let all := closureOf (roots' ++ fhe') (fun _ => false)
    let tp ← IO.monoMsNow
    let (bad, nUnits) ← parallelReplay (env.find? ·) g rev all.toList.toArray replayJobs
    let tpMs := (← IO.monoMsNow) - tp
    IO.eprintln s!"[PinStatus] parallel kernel replay: {all.size} constants in {nUnits} units, {replayJobs} jobs, {tpMs} ms"
    for r in roots' do
      if let some e := bad[r]? then rejected := rejected.insert r (e.replace "\n" " ")
    -- the counts as the serial replay makes them: the closures of the accepted roots, then the
    -- further constants of the closure of the `FHE` library
    let accRoots := closureOf (roots'.filter (!rejected.contains ·)) (fun _ => false)
    replayed := accRoots.size
    out := out.push s!"KERNEL replayed {replayed} constants from {roots.size} roots in a fresh environment ({← timeSince t1}), rejected roots: {rejected.size}"
    let fheTodo := closureOf fhe' accRoots.contains
    let fheErr : Option String := fheTodo.toList.foldl (init := none) fun acc n =>
      match acc, bad[n]? with
      | none, e => e
      | some a, some e => some (if e < a then e else a)
      | a, none => a
    match fheErr with
    | none =>
      fheAccepted := true
      out := out.push s!"KERNEL FHE replayed {fheTodo.size} further constants (closure of all {fheConsts.size} constants of the FHE library{if fheSkipped == 0 then "" else s!", except {fheSkipped} unchanged since an accepted replay"}) ({tpMs} ms), rejected: 0"
    | some e =>
      failed := failed + 1
      out := out.push s!"KERNEL FHE BAD the kernel rejects the closure of the FHE library: {e.replace "\n" " "}"
  else
    let mut kenv := (← mkEmptyEnvironment).toKernelEnv
    for r in roots do
      if cachedRoot r then
        skippedRoots := skippedRoots + 1
        continue
      let todo := reach g r (stop := fun n => (kenv.find? n).isSome)
      let mut m : Std.HashMap Name ConstantInfo := {}
      for n in todo.toList do
        if let some ci := env.find? n then m := m.insert n ci
      try
        kenv ← kenv.replay m
        replayed := replayed + m.size
      catch e =>
        rejected := rejected.insert r (toString e |>.replace "\n" " ")
    out := out.push s!"KERNEL replayed {replayed} constants from {roots.size} roots in a fresh environment ({← timeSince t1}), rejected roots: {rejected.size}"
    -- The rest of the `FHE` library, in the same environment, in one batch.
    let t2 ← IO.monoMsNow
    let mut fheTodo : Std.HashMap Name ConstantInfo := {}
    let mut seen : NameSet := {}
    for r in fheConsts do
      if cachedFhe r then
        fheSkipped := fheSkipped + 1
        continue
      for n in (reach g r (stop := fun n => (kenv.find? n).isSome || seen.contains n)).toList do
        seen := seen.insert n
        if let some ci := env.find? n then fheTodo := fheTodo.insert n ci
    try
      kenv ← kenv.replay fheTodo
      fheAccepted := true
      out := out.push s!"KERNEL FHE replayed {fheTodo.size} further constants (closure of all {fheConsts.size} constants of the FHE library{if fheSkipped == 0 then "" else s!", except {fheSkipped} unchanged since an accepted replay"}) ({← timeSince t2}), rejected: 0"
    catch e =>
      failed := failed + 1
      out := out.push s!"KERNEL FHE BAD the kernel rejects the closure of the FHE library: {(toString e).replace "\n" " "}"
  if let some dir := cacheDir? then
    if cacheRead then
      out := out.push s!"KERNEL cache: on ({dir}; development only): replay skipped for {skippedRoots} of {roots.size} roots and {fheSkipped} of {fheConsts.size} FHE constants, accepted by an earlier run with the same toolchain and PinStatus.lean, and no constant of their closure changed (.olean SHA-256 of its module, same providing module)"
    else
      out := out.push s!"KERNEL cache: off (every root replayed from an empty environment; result recorded in {dir})"
    -- Record what is accepted now (replayed and accepted, or skipped as unchanged), atomically.
    if envId != "" then
      let mut lines : Array String := #[s!"ENV\t{envId}"]
      for m in env.header.moduleNames do
        if let some h := curSha[m]? then lines := lines.push s!"M\t{m}\t{h}"
      for (n, _) in g.toList do
        if let some m := provider n then lines := lines.push s!"C\t{n.hash}\t{m.hash}"
      for r in roots do
        unless rejected.contains r do lines := lines.push s!"R\t{r}"
      if fheAccepted then lines := lines.push "F\tok"
      let tmp := dir / s!"replay-accepted.txt.tmp"
      IO.FS.writeFile tmp (String.intercalate "\n" lines.toList ++ "\n")
      IO.FS.rename tmp (dir / "replay-accepted.txt")
  else
    out := out.push "KERNEL cache: off (every root replayed from an empty environment)"

  IO.eprintln s!"[PinStatus] kernel replay done at {← timeSince tStart}"
  /- ## Verdicts -/
  let mut proven : Nat := 0
  let mut missing : Nat := 0
  for (n, v) in candidates do
    if badStatements.contains n then
      verdict := verdict.insert n "BAD-STATEMENT (see HEADLINE)"
    else if let some e := rejected[v]? then
      verdict := verdict.insert n s!"KERNEL-REJECTED {e}"
    else
      -- `tainted` holds exactly the constants from which a non-standard axiom (or `sorryAx`) is
      -- reachable in `g`, so the closure is walked only for a pin that has one (to list them).
      let bad := if tainted.contains v then (axiomsOf v).filter (!allowedAxioms.contains ·) else []
      if bad.isEmpty then verdict := verdict.insert n "PROVEN"
      else verdict := verdict.insert n s!"AXIOMS {bad}"
  let mut pinLines : Array String := #[]
  for n in names do
    let s := verdict.getD n "MISSING"
    if s == "PROVEN" then proven := proven + 1
    else if s == "MISSING" then missing := missing + 1
    else failed := failed + 1
    pinLines := pinLines.push s!"PIN {n} {s}"
  for (hole, _, _) in holes do
    let mut bad := holeBad.getD hole #[]
    if let some e := rejected[hole]? then bad := bad.push s!"kernel rejects its closure: {e}"
    if bad.isEmpty then out := out.push s!"HOLE {hole} OK"
    else
      failed := failed + 1
      for b in bad do out := out.push s!"HOLE {hole} BAD {b}"

  /- ## Classification -/
  -- Reverse edges of `g`: `v` depends on `p` iff `v` is reachable from `p` along them.
  let revG : Std.HashMap Name (Array Name) := rev.fold (fun acc k l => acc.insert k l.toArray) {}
  let mut classLines : Array String := #[]
  let mut counts : Std.HashMap String Nat := {}
  for (a, _) in annotations do
    unless names.contains a do
      failed := failed + 1
      out := out.push s!"CLASS BAD the annotation table names {a}, which is not a pin"
  for n in names do
    let some ci := env.find? n | continue
    let v := n.replacePrefix `Challenge `Validation
    let ann? : Option Ann := (annotations.find? (·.1 == n)).map (·.2)
    let rflProof := match env.find? v with
      | some (.thmInfo vi) => isRflProof vi.value
      | _ => false
    let (cls, why) : PinClass × String :=
      if isRejection env ci.type then (.discrimination, "statement shape")
      else if isRealizability env ci.type then (.realizability, "statement shape")
      else match ann? with
        | some (.inst ps) => (.inst, s!"annotated: follows from {ps}")
        | some .unfolding => (.unfolding, "annotated")
        | some .closed => (.closed, "annotated")
        | none =>
          if rflProof then (.unfolding, "proof term is rfl")
          else if isClosedShape env ci.type then (.closed, "statement shape")
          else (.substantive, "default")
    -- An `inst` annotation is a claim about the proof: check the dependency.
    if let some (.inst ps) := ann? then
      if verdict.getD n "MISSING" == "PROVEN" then
        for p in ps do
          let pv := p.replacePrefix `Challenge `Validation
          unless names.contains p && (reach revG pv).contains v do
            failed := failed + 1
            out := out.push s!"CLASS BAD {n} is annotated as an instance of {p}, but its proof does not depend on {pv}"
    counts := counts.insert cls.label (counts.getD cls.label 0 + 1)
    classLines := classLines.push s!"CLASS {n} {cls.label} ({why})"
  let cnt (c : PinClass) : Nat := counts.getD c.label 0
  out := out.push s!"CLASSES total={names.size} substantive={cnt .substantive} realizability={cnt .realizability} discrimination={cnt .discrimination} closed={cnt .closed} unfolding={cnt .unfolding} instance={cnt .inst}"

  IO.eprintln s!"[PinStatus] verdicts and classification done at {← timeSince tStart}"
  for l in pinLines ++ classLines ++ out do IO.println l
  if let some dir := outDir? then
    IO.FS.writeFile (System.FilePath.mk dir / "holes-modules.txt")
      (String.join (holeFHE.toList.map (s!"{·}\n")))
    IO.FS.writeFile (System.FilePath.mk dir / "replay-roots.txt")
      (String.join (roots.toList.map (s!"{·}\n")))
  IO.println s!"SUMMARY proven={proven} missing={missing} failed={failed} total={names.size} projections_skipped={projections.size} ({← timeSince tStart})"
  return if failed == 0 then 0 else 1
