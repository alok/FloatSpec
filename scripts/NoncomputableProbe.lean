import Lean

/-!
Probe which `noncomputable` declarations the code generator actually needs.

For every constant tagged `noncomputable` in a module whose name starts with
one of `NoncomputableProbe.projects`, this asks the real code generator whether
the keyword is needed. Lean never warns about an unneeded `noncomputable`, so
this is how to find the removable ones. `scripts/noncomputable_probe.py` runs
it: like `scripts/AuditCompiledTrust.lean`, this file is a template, to which
the wrapper prepends an `import` for every FloatSpec module before running
`lake env lean` on the result.

For each candidate `c` the probe adds a copy `_ncprobe1.c` whose type and body
have every reference to another candidate redirected to that candidate's copy,
and runs `compileDecls` on it. Candidates go in dependency post-order, and
`compileDecls` tags a copy it cannot compile `noncomputable`
(`compileDecls.doCompile` in `CoreM.lean`), so a copy fails exactly when the
code generator rejects its own body or a dependency that could not be made
computable either. One pass reaches the fixpoint. An isolation pass
(`_ncprobe0`) runs the same test with the other candidates still tagged; a
candidate removable jointly but not in isolation needs another keyword deleted
in the same change. A tagged theorem is removable without a copy: the code
generator never compiles a theorem (`Compiler.getDeclNamesForCodeGen`).

Every copy goes through the kernel with `addDecl`, like any declaration, so
the probe needs no kernel bypass. A candidate whose copy the kernel rejects,
that the code generator rejects for another reason (a recursive definition's
kernel body, for one), or that is blocked only by such a candidate is
`inconclusive`, never `necessary`.

Computable project definitions that have generated code are copied and
compiled the same way, as controls; every copy must compile. A recursive
definition is compiled from its `_unsafe_rec` pre-definition, which its kernel
body does not carry, so it is listed and not copied.

Prints one JSON document on stdout. It relies on Lean 4.34 compiler internals
(`compileDecls` re-tagging, the `dependsOnNoncomputable` messages,
`_unsafe_rec`, IR lookup) and is pinned to that toolchain.
-/

open Lean Meta

namespace NoncomputableProbe

/-- Name of the probe copy of `n` in pass `pass`. -/
def copyName (pass : Nat) (n : Name) : Name := Name.mkSimple s!"_ncprobe{pass}" ++ n

/-- Module that defines `n`, for imported constants. -/
def moduleOf? (env : Environment) (n : Name) : Option Name :=
  (env.getModuleIdxFor? n).map fun idx => env.header.moduleNames[idx.toNat]!

/-- Constants of modules whose name starts with one of `projects`. -/
def inProject (env : Environment) (projects : Array Name) (n : Name) : Bool :=
  match moduleOf? env n with
  | some m => projects.any (·.isPrefixOf m)
  | none => false

/-- Declaration kind as the census names it. -/
def kindOf (env : Environment) (n : Name) (ci : ConstantInfo) : String :=
  if isInstanceCore env n then "instance"
  else match ci with
    | .defnInfo d => if d.hints matches .abbrev then "abbrev" else "def"
    | .opaqueInfo _ => "opaque"
    | .thmInfo _ => "theorem"
    | _ => "other"

/-- Replace each constant in `copies` by its copy. -/
def redirect (copies : NameMap Name) (e : Expr) : Expr :=
  e.replace fun
    | .const c ls => (copies.find? c).map (.const · ls)
    | _ => none

/-- The declaration that adds `ci`'s copy `name`, with references redirected. -/
def copyDecl (copies : NameMap Name) (name : Name) (ci : ConstantInfo) : Option Declaration :=
  match ci with
  | .defnInfo d => some <| .defnDecl { d with
      name, type := redirect copies d.type, value := redirect copies d.value, all := [name] }
  | .opaqueInfo d => some <| .opaqueDecl { d with
      name, type := redirect copies d.type, value := redirect copies d.value, all := [name] }
  | _ => none

/-- What happened to one copy. -/
inductive Outcome where
  /-- The copy compiled. -/
  | compiled
  /-- The code generator needs `blame` (as `Name.toString` renders it), which it
  cannot compile. -/
  | blocked (blame : String) (message : String)
  /-- The probe could not decide: no body, kernel rejection, or another compiler error. -/
  | failed (message : String)
  deriving Inhabited

/-- Drop the pretty-printing contexts, so a constant name in the message renders
as `Name.toString` (unabbreviated, private prefix kept) and can be looked up. -/
partial def withoutContext : MessageData → MessageData
  | .withContext _ m | .withNamingContext _ m => withoutContext m
  | .nest n m => .nest n (withoutContext m)
  | .group m => .group (withoutContext m)
  | .compose a b => .compose (withoutContext a) (withoutContext b)
  | .tagged t m => .tagged t (withoutContext m)
  | m => m

/-- The constant that the two `lean.dependsOnNoncomputable` errors of Lean 4.34
(`checkComputable` in `LCNF/ToLCNF.lean`) blame. -/
def blameOf? (message : String) : Option String :=
  match message.splitOn "because it depends on '" with
  | [_, rest] =>
    match rest.splitOn "', which is 'noncomputable'" with
    | [blame, _] => some blame
    | _ => none
  | _ =>
    match message.splitOn "` not supported by code generator" with
    | [head, _] => match head.splitOn "`" with
      | [_, blame] => some blame
      | _ => none
    | _ => none

/-- First line of an error, for the report. -/
def firstLine (message : String) : String := (message.splitOn "\n").head!

/-- Add `ci`'s copy under `copyName pass n` and compile it. A theorem needs no
copy: the code generator never compiles one (`Compiler.getDeclNamesForCodeGen`). -/
def probe (copies : NameMap Name) (pass : Nat) (n : Name) (ci : ConstantInfo) :
    CoreM Outcome := do
  if ci.isTheorem then return .compiled
  let name := copyName pass n
  let some decl := copyDecl copies name ci | return .failed "no definition body to compile"
  try
    addDecl decl
  catch e =>
    return .failed s!"kernel rejected the copy: {firstLine (← e.toMessageData.toString)}"
  try
    compileDecls #[name]
    return .compiled
  catch e =>
    let message ← (withoutContext e.toMessageData).toString
    return match blameOf? message with
      | some blame => .blocked blame (firstLine message)
      | none => .failed (firstLine message)

/-- Candidates in dependency post-order: every candidate after the candidates it uses. -/
def postOrder (deps : NameMap (Array Name)) (roots : Array Name) : Array Name := Id.run do
  let mut visited : NameSet := {}
  let mut out : Array Name := #[]
  for root in roots do
    let mut stack : Array (Name × Bool) := #[(root, false)]
    while !stack.isEmpty do
      let (n, done) := stack.back!
      stack := stack.pop
      if done then
        out := out.push n
      else if !visited.contains n then
        visited := visited.insert n
        stack := stack.push (n, true)
        for d in (deps.find? n).getD #[] do
          if !visited.contains d then stack := stack.push (d, false)
  return out

/-- Follow a blame through candidates (`candidateOf` maps the `Name.toString` of
a candidate and of its copy to the candidate) to the constant that is really
needed. `none` when the chain ends in a candidate the probe could not decide. -/
def rootCause (candidateOf : Std.HashMap String Name) (outcomes : NameMap Outcome) :
    String → Nat → Option String
  | _, 0 => none
  | blame, fuel + 1 =>
    match candidateOf[blame]? with
    | none => some blame
    | some orig =>
      match outcomes.find? orig with
      | some (.blocked next _) => rootCause candidateOf outcomes next fuel
      | _ => none

/-- `(line, column)` of a position. -/
def posJson (p : Position) : Json := Json.arr #[toJson p.line, toJson p.column]

/-- Pretty-printed result type (the type after all binders), shortened. -/
def resultType (ci : ConstantInfo) : MetaM String := do
  try
    forallTelescopeReducing ci.type fun _ body => do
      let s := toString (← ppExpr body)
      return (" ".intercalate (s.splitOn "\n" |>.map (·.trimAscii.toString))).take 120 |>.toString
  catch _ => return "?"

/-- The probe over the whole imported environment. -/
def run (projects : Array Name) : MetaM Json := do
  let env ← getEnv
  let mut candidates : Array Name := #[]
  let mut controls : Array Name := #[]
  let mut recursiveControls : Array Name := #[]
  for (n, ci) in env.constants.map₁.toList do
    if !inProject env projects n then continue
    if isNoncomputable env n then
      candidates := candidates.push n
    else if ci.isDefinition && !n.isInternal && (IR.findEnvDecl env n).isSome then
      if env.contains (Compiler.mkUnsafeRecName n) then
        recursiveControls := recursiveControls.push n
      else
        controls := controls.push n
  candidates := candidates.qsort (·.toString < ·.toString)
  controls := controls.qsort (·.toString < ·.toString)
  recursiveControls := recursiveControls.qsort (·.toString < ·.toString)
  let candidateSet : NameSet := candidates.foldl (·.insert ·) {}
  let mut deps : NameMap (Array Name) := {}
  for n in candidates do
    let used := ((env.find? n).bind (·.value? (allowOpaque := true))).map (·.getUsedConstants)
    deps := deps.insert n ((used.getD #[]).filter fun c => candidateSet.contains c && c != n)
  let order := postOrder deps candidates
  -- Pass 0: each candidate alone, the others still tagged.
  let mut isolated : NameMap Outcome := {}
  for n in order do
    isolated := isolated.insert n (← probe {} 0 n (env.find? n).get!)
  -- Pass 1: every candidate that has a copy is replaced by it. A copy that did
  -- not compile is tagged (or, if the kernel rejected it, an axiom), so its
  -- dependents blame it and the blame chain ends at its own outcome.
  let mut joint : NameMap Outcome := {}
  let mut copies : NameMap Name := {}
  for n in order do
    joint := joint.insert n (← probe copies 1 n (env.find? n).get!)
    if (← getEnv).contains (copyName 1 n) then
      copies := copies.insert n (copyName 1 n)
  let candidateOf : Std.HashMap String Name := candidates.foldl
    (fun m n => (m.insert n.toString n).insert (copyName 1 n).toString n) {}
  let mut rows : Array Json := #[]
  for n in candidates do
    let ci := (env.find? n).get!
    let ranges ← findDeclarationRanges? n
    let outcome := (joint.find? n).getD (.failed "not probed")
    let (status, blame, root, error) := match outcome with
      | .compiled => ("removable", "", "", "")
      | .blocked blame message =>
        let shown := (candidateOf[blame]?.map Name.toString).getD blame
        match rootCause candidateOf joint blame (candidates.size + 1) with
        | some root => ("necessary", shown, root, message)
        | none => ("inconclusive", shown, "", message)
      | .failed message => ("inconclusive", "", "", message)
    let alone := match isolated.find? n with
      | some .compiled => true
      | _ => false
    rows := rows.push <| Json.mkObj [
      ("name", toJson n.toString),
      ("module", toJson ((moduleOf? env n).getD .anonymous).toString),
      ("start", ranges.map (posJson ·.range.pos) |>.getD Json.null),
      ("selection", ranges.map (posJson ·.selectionRange.pos) |>.getD Json.null),
      ("kind", toJson (kindOf env n ci)),
      ("theorem", toJson ci.isTheorem),
      ("status", toJson status),
      ("removable_alone", toJson alone),
      ("blame", toJson blame),
      ("root_cause", toJson root),
      ("result_type", toJson (← resultType ci)),
      ("error", toJson error)]
  -- Controls: computable definitions copied without redirection must compile.
  let mut controlFailures : Array Json := #[]
  for n in controls do
    match ← probe {} 2 n (env.find? n).get! with
    | .compiled => pure ()
    | .blocked _ message | .failed message =>
      controlFailures := controlFailures.push <| Json.mkObj [
        ("name", toJson n.toString), ("error", toJson message)]
  return Json.mkObj [
    ("lean_version", toJson Lean.versionString),
    ("projects", toJson (projects.map Name.toString)),
    ("modules", toJson ((env.header.moduleNames.filter fun m => projects.any (·.isPrefixOf m)).map
      Name.toString)),
    ("candidates", Json.arr rows),
    ("controls", Json.mkObj [
      ("compiled", toJson (controls.size - controlFailures.size)),
      ("failed", Json.arr controlFailures),
      ("recursive_not_copied", toJson (recursiveControls.map Name.toString))])]

/-- Module-name prefixes whose declarations the probe examines.
`scripts/noncomputable_probe.py` replaces this line to probe other modules. -/
def projects : Array Name := #[`FloatSpec]

end NoncomputableProbe

open Lean Elab Command in
set_option Elab.async false in
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
run_cmd do
  let report ← liftTermElabM (NoncomputableProbe.run NoncomputableProbe.projects)
  liftIO (IO.println report.compress)
