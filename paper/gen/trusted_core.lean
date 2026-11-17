import Challenge
/-!
UNTRUSTED helper of `paper/gen/trusted_core.py` (docs/TRUSTED-CORE.md): the declarations of `Spec`
and `Challenge` a reader must read to know what a given set of locked statements claims. A sibling
of `paper/gen/audit_closure.lean`, with the same unfolding rule, plus depth, declaration ranges and
the library notions relied on.

    lake env lean --run paper/gen/trusted_core.lean GROUP=Name1,Name2 GROUP2=Name3/Stop1,Stop2 ...

After a `/`, an optional list of constants whose definitions are NOT unfolded (their types are):
used to measure what a reader needs to know what a soundness statement claims, which does not
include the body of the decision function the statement is about.

For each group, breadth first from the given constants: the TYPE of every reached constant is
read; for a reached constant declared in a module under `Spec` or `Challenge` that is not a
theorem, its definition (value) or, for an inductive type, its constructors are read too. Theorems
other than the roots are not followed at all (a proof, and the statement of a lemma used inside a
proof term, are not read by a statement). Constants outside `Spec`/`Challenge` are not followed.

Output, tab-separated:
  `D  group  name  kind  module  depth  firstLine  selLine  lastLine  owner`  one per reached
      in-scope constant (ranges 1-based; `firstLine` includes the docstring, `selLine` is the line
      of the name; for an auxiliary constant without a range, e.g. `f.match_1`, the range and kind
      are those of `owner`, its nearest enclosing declaration with a range; else `owner` = name)
  `X  group  name  module  referrers`  one per out-of-scope constant read directly by a reached
      in-scope constant (`referrers` = how many reached constants read it)
-/
open Lean

def inScopeMod (m : Name) : Bool := (`Spec).isPrefixOf m || (`Challenge).isPrefixOf m

def kindOf : ConstantInfo → String
  | .defnInfo _ => "def" | .thmInfo _ => "theorem" | .axiomInfo _ => "axiom"
  | .opaqueInfo _ => "opaque" | .quotInfo _ => "quot" | .inductInfo _ => "inductive"
  | .ctorInfo _ => "ctor" | .recInfo _ => "rec"

unsafe def main (args : List String) : IO Unit := do
  initSearchPath (← findSysroot)
  enableInitializersExecution
  -- the modules `Challenge.lean` imports, read from its text, so that a stale `Challenge.olean`
  -- (built before a module was added to the root) does not hide a statement
  let src ← IO.FS.readFile "Challenge.lean"
  let mods := (src.splitOn "\n").filterMap fun l =>
    if l.startsWith "import " then some (l.drop 7).trim.toName else none
  let env ← importModules (mods.map ({module := ·})).toArray {} (loadExts := true)
  let modOf := fun (n : Name) => (env.getModuleIdxFor? n).map (fun i => env.header.moduleNames[i.toNat]!)
  let inScope := fun (n : Name) => match modOf n with | some m => inScopeMod m | none => false
  for arg in args do
    let some (grp, rest) := (match arg.splitOn "=" with | [g, r] => some (g, r) | _ => none)
      | throw (IO.userError s!"bad argument {arg} (want GROUP=Name1,Name2)")
    let (rootsS, stopsS) := match rest.splitOn "/" with
      | [r, st] => (r, st) | _ => (rest, "")
    let roots := (rootsS.splitOn ",").map String.toName
    let stops := if stopsS.isEmpty then [] else (stopsS.splitOn ",").map String.toName
    for r in stops do
      if (env.find? r).isNone then throw (IO.userError s!"missing {r}")
    for r in roots do
      if (env.find? r).isNone then throw (IO.userError s!"missing {r}")
    let mut depth : Std.HashMap Name Nat := {}
    let mut ext : Std.HashMap Name Nat := {}
    let mut frontier := roots.toArray
    for r in roots do depth := depth.insert r 0
    let mut d := 0
    while !frontier.isEmpty do
      let mut next : Array Name := #[]
      for n in frontier do
        let some ci := env.find? n | continue
        let mut cs := ci.type.getUsedConstants.toList
        if inScope n && !stops.contains n then
          match ci with
          | .defnInfo v => cs := cs ++ v.value.getUsedConstants.toList
          | .opaqueInfo v => cs := cs ++ v.value.getUsedConstants.toList
          | .inductInfo v => cs := cs ++ v.ctors
          | _ => pure ()
        let mut loc : NameSet := {}
        for c in cs do
          if loc.contains c then continue
          loc := loc.insert c
          if inScope c then
            let some cci := env.find? c | continue
            if cci matches .thmInfo _ then continue
            if !depth.contains c then
              depth := depth.insert c (d + 1)
              next := next.push c
          else
            ext := ext.insert c (ext.getD c 0 + 1)
      frontier := next
      d := d + 1
    let names := depth.toArray.qsort (fun a b => a.1.toString < b.1.toString)
    let rangeOf := fun (n : Name) => do
      let r ← (findDeclarationRanges? n : CoreM _).toIO {fileName := "", fileMap := default} {env}
      pure r.1
    for (n, dp) in names do
      let some ci := env.find? n | continue
      let m := (modOf n).getD .anonymous
      -- an auxiliary constant without a range (`f.match_1`, `f._f`, `T.ctorIdx`) is reported as
      -- its nearest enclosing declaration that has one (column `owner`)
      let mut owner := n
      let mut rng ← rangeOf n
      while rng.isNone && !owner.isAnonymous do
        owner := owner.getPrefix
        if !owner.isAnonymous && (env.find? owner).isSome then rng ← rangeOf owner
      let (l0, ls, l1) := match rng with
        | some r => (r.range.pos.line, r.selectionRange.pos.line, r.range.endPos.line)
        | none => (0, 0, 0)
      let ownerKind := ((env.find? owner).map kindOf).getD (kindOf ci)
      IO.println s!"D\t{grp}\t{n}\t{ownerKind}\t{m}\t{dp}\t{l0}\t{ls}\t{l1}\t{owner}"
    for (n, k) in ext.toArray.qsort (fun a b => a.1.toString < b.1.toString) do
      IO.println s!"X\t{grp}\t{n}\t{(modOf n).getD .anonymous}\t{k}"
