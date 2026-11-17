import Challenge
/-!
UNTRUSTED helper of `paper/gen/audit_generic.py` (where a library-specific line sits is not the
whole story): which `Spec` declarations the two main soundness statements read.

    lake env lean --run paper/gen/audit_closure.lean > out.tsv

For each of `Challenge.Certify.certify?_sound` and `Challenge.CertifyBFV.certifyBFV?_sound`, the
constants reachable from the statement's TYPE, unfolding the definitions (values) and inductive
types (constructors) of modules under `Spec` and `Challenge` (theorems are not unfolded: a proof is
not read by a statement). Two modes: `statement` stops at the decision functions `certify?` /
`certifyBFV?` (what the hypotheses and the conclusion mention apart from "the decision returned
c"), `full` unfolds them too. Prints one line per reachable `Spec` declaration:
`root, mode, module, name, first line, last line` (declaration range, 1-based).
-/
open Lean

partial def specClosure (env : Environment) (roots : List Name) (stop : Name → Bool) : NameSet := Id.run do
  let inScope := fun (n : Name) => match env.getModuleIdxFor? n with
    | some i =>
      let m := env.header.moduleNames[i.toNat]!
      (`Spec).isPrefixOf m || (`Challenge).isPrefixOf m
    | none => false
  let mut seen : NameSet := {}
  let mut todo := roots
  while !todo.isEmpty do
    let n := todo.head!
    todo := todo.tail!
    if seen.contains n then continue
    seen := seen.insert n
    let some ci := env.find? n | continue
    let mut cs := ci.type.getUsedConstants.toList
    if inScope n && !stop n then
      match ci with
      | .defnInfo d => cs := cs ++ d.value.getUsedConstants.toList
      | .inductInfo d => cs := cs ++ d.ctors
      | .opaqueInfo d => cs := cs ++ d.value.getUsedConstants.toList
      | _ => pure ()
    for c in cs do
      if !seen.contains c && inScope c then todo := c :: todo
  return seen

unsafe def main : IO Unit := do
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let env ← importModules #[{module := `Challenge}] {} (loadExts := true)
  let roots := [("bgv", `Challenge.Certify.certify?_sound), ("bfv", `Challenge.CertifyBFV.certifyBFV?_sound)]
  let deciders : List Name := [`Challenge.Certify.certify?, `Challenge.CertifyBFV.certifyBFV?]
  for (tag, r) in roots do
    if (env.find? r).isNone then throw (IO.userError s!"missing {r}")
    for (mode, stop) in [("statement", fun n => deciders.contains n), ("full", fun _ => false)] do
      let s := specClosure env [r] stop
      for n in s.toList.toArray.qsort (·.toString < ·.toString) do
        let some i := env.getModuleIdxFor? n | continue
        let m := env.header.moduleNames[i.toNat]!
        if !(`Spec).isPrefixOf m then continue
        let rng ← (findDeclarationRanges? n : CoreM _).toIO {fileName := "", fileMap := default} {env}
        let (line, endl) := match rng.1 with
          | some r => (r.range.pos.line, r.range.endPos.line)
          | none => (0, 0)
        IO.println s!"{tag}\t{mode}\t{m}\t{n}\t{line}\t{endl}"
