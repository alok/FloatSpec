module

public meta import Lean.Elab.Command
public meta import Lean.Linter.Basic
public meta import Lean.DocString
public meta import Lean.Meta.Hint

/-! Pinned Flocq source references, an opt-in declaration coverage check, and a check that
Flocq citation syntax only appears in Verso docstrings, where `FloatSpecRoles` checks it. -/

open Lean Elab Command Linter

public meta section

set_option maxHeartbeats 1000000

namespace FloatSpec.Linter.CoqSource

/-- The Flocq commit recorded by the FloatSpec gitlink for this audit. -/
def flocqCommit : String := "7aab8f55bceec0cfafc3b3bc0e77e0dbb5a70c5f"

/-- Source-link metadata attached to a Lean declaration. -/
structure SourceRef where
  declName : Name
  path : String
  line : Nat
  coqName : String
  deriving Inhabited

/-- A public Lean helper that deliberately has no same-named Flocq declaration. -/
structure LocalRef where
  declName : Name
  reason : String
  deriving Inhabited

initialize sourceExt : SimplePersistentEnvExtension SourceRef (Array SourceRef) ←
  registerSimplePersistentEnvExtension {
    addImportedFn entries := entries.flatten
    addEntryFn entries entry := entries.push entry
  }

initialize localExt : SimplePersistentEnvExtension LocalRef (Array LocalRef) ←
  registerSimplePersistentEnvExtension {
    addImportedFn entries := entries.flatten
    addEntryFn entries entry := entries.push entry
  }

/-- Look up a declaration's pinned Flocq source reference. -/
def sourceRef? (env : Environment) (declName : Name) : Option SourceRef :=
  (sourceExt.getState env).find? (·.declName == declName)

/-- Look up the reason a public definition has no direct Flocq counterpart. -/
def localRef? (env : Environment) (declName : Name) : Option LocalRef :=
  (localExt.getState env).find? (·.declName == declName)

/-- Every Rocq source file under `src/` at `flocqCommit`, in the bytewise order of
`git ls-tree -r --name-only`. `scripts/validate_flocq_source_refs.py` checks this list against
that listing of the pinned commit. -/
def flocqSourceFiles : Array String := #[
  "src/Calc/Bracket.v", "src/Calc/Div.v", "src/Calc/Operations.v", "src/Calc/Plus.v",
  "src/Calc/Round.v", "src/Calc/Sqrt.v", "src/Core/Core.v", "src/Core/Defs.v",
  "src/Core/Digits.v", "src/Core/FIX.v", "src/Core/FLT.v", "src/Core/FLX.v", "src/Core/FTZ.v",
  "src/Core/Float_prop.v", "src/Core/Generic_fmt.v", "src/Core/Raux.v", "src/Core/Round_NE.v",
  "src/Core/Round_pred.v", "src/Core/Ulp.v", "src/Core/Zaux.v", "src/IEEE754/Binary.v",
  "src/IEEE754/BinarySingleNaN.v", "src/IEEE754/Bits.v", "src/IEEE754/PrimFloat.v",
  "src/Pff/Pff.v", "src/Pff/Pff2Flocq.v", "src/Pff/Pff2FlocqAux.v",
  "src/Prop/Div_sqrt_error.v", "src/Prop/Double_rounding.v", "src/Prop/Mult_error.v",
  "src/Prop/Plus_error.v", "src/Prop/Relative.v", "src/Prop/Round_odd.v", "src/Prop/Sterbenz.v"]

/-- A clickable link to a whole Flocq source file at the pinned commit. -/
def sourceFileUrl (path : String) : String :=
  s!"https://gitlab.inria.fr/flocq/flocq/-/blob/{flocqCommit}/{path}"

/-- A clickable link to the pinned source declaration. -/
def sourceUrl (ref : SourceRef) : String :=
  s!"{sourceFileUrl ref.path}#L{ref.line}"

/-- Does a declaration have a pinned Flocq source reference? -/
def hasSourceRef (env : Environment) (declName : Name) : Bool :=
  (sourceRef? env declName).isSome

end FloatSpec.Linter.CoqSource

syntax (name := flocqSourceAttr) "flocq_source " str num str : attr

initialize registerBuiltinAttribute {
  name := `flocqSourceAttr
  descr := "Attach a declaration to a named Flocq definition at the pinned source commit."
  applicationTime := .beforeElaboration
  add := fun decl stx _kind => do
    let `(attr| flocq_source $path:str $line:num $coqName:str) := stx
      | throwUnsupportedSyntax
    let path := path.getString
    let line := line.getNat
    let coqName := coqName.getString
    unless path.startsWith "src/" && path.endsWith ".v" &&
        (path.splitOn "..").length == 1 && line > 0 && !coqName.isEmpty do
      throwError "flocq_source requires a src/*.v path without '..', positive line, and Coq name"
    modifyEnv (FloatSpec.Linter.CoqSource.sourceExt.addEntry ·
      { declName := decl, path, line, coqName })
}

syntax (name := flocqLocalAttr) "flocq_local " str : attr

initialize registerBuiltinAttribute {
  name := `flocqLocalAttr
  descr := "Classify a public FloatSpec-only helper with no direct Flocq declaration."
  applicationTime := .beforeElaboration
  add := fun decl stx _kind => do
    let `(attr| flocq_local $reason:str) := stx
      | throwUnsupportedSyntax
    let reason := reason.getString.trimAscii.toString
    if reason.isEmpty then
      throwError "flocq_local requires a nonempty reason"
    modifyEnv (FloatSpec.Linter.CoqSource.localExt.addEntry ·
      { declName := decl, reason })
}

namespace FloatSpec.Linter.CoqSource

/-- Require a pinned Flocq source link on public definitions in an opted-in module. -/
-- Explicitly classified Lean-only helpers are exempt from the source-link requirement.
register_option linter.coqSource : Bool := {
  defValue := false
  descr := "warn when a public def/abbrev lacks @[flocq_source] or @[flocq_local]"
}

/-- Collect all written definitions, including each member of a mutual block.
Do not descend into declaration bodies: quoted commands are data, not declarations. -/
private partial def definitionIds (stx : Syntax) : Array Syntax := Id.run do
  if stx.isOfKind ``Lean.Parser.Command.declaration then
    if (stx[0].find? (·.isOfKind ``Lean.Parser.Command.private)).isSome then return #[]
    let body := stx[1]
    if body.isOfKind ``Lean.Parser.Command.definition ||
        body.isOfKind ``Lean.Parser.Command.abbrev then
      return #[body[1][0]]
    return #[]
  return stx.getArgs.foldl (fun ids child => ids ++ definitionIds child) #[]

/-- The source-link coverage linter. Enable it in a source-facing file once
that file's local helpers have been separated or explicitly classified. -/
def coqSourceLinter : Linter where run := withSetOptionIn fun stx => do
  unless linter.coqSource.get (← getOptions) && (← getInfoState).enabled do return
  if (← get).messages.hasErrors then return
  let env ← getEnv
  let currNamespace ← getCurrNamespace
  for id in definitionIds stx do
    if id.isMissing then continue
    let name := if (`_root_).isPrefixOf id.getId then
        id.getId.replacePrefix `_root_ .anonymous
      else currNamespace ++ id.getId
    if isPrivateName name then continue
    unless hasSourceRef env name || (localRef? env name).isSome do
      logLint linter.coqSource id
        s!"public definition {name} is unclassified; add \
          @[flocq_source \"src/Module.v\" LINE \"coq_name\"] \
          or @[flocq_local \"reason\"]"

initialize addLinter coqSourceLinter

/-- Flocq citation syntax is checked only in Verso docstrings. -/
register_option linter.flocqCitations : Bool := {
  defValue := true
  descr := "warn when a Markdown (non-Verso) docstring uses `{coq}`, `{coq_file}` or a `coq` \
    quote block, which it would show as unchecked literal text"
}

/-- The rest of `cs` after a run of exactly `n` backticks, if one occurs. -/
private partial def afterCodeSpan (n : Nat) : List Char → Option (List Char)
  | [] => none
  | cs@('`' :: _) =>
    let run := (cs.takeWhile (· == '`')).length
    if run == n then some (cs.drop run) else afterCodeSpan n (cs.drop run)
  | _ :: rest => afterCodeSpan n rest

/-- The Flocq roles applied to code on one Markdown line, skipping code spans, so a role
name that is itself written as code (such as `` `{coq}` ``) is not a use. -/
private partial def roleUses : List Char → Array String
  | [] => #[]
  | cs@('`' :: _) =>
    let run := (cs.takeWhile (· == '`')).length
    match afterCodeSpan run (cs.drop run) with
    | some rest => roleUses rest
    | none => roleUses (cs.drop run)
  | cs@('{' :: rest) =>
    let role := ["{coq}", "{coq_file}"].find? fun r => cs.take (r.length + 1) == (r ++ "`").toList
    match role with
    | some r => #["the `" ++ r ++ "` role"] ++ roleUses (cs.drop r.length)
    | none => roleUses rest
  | _ :: rest => roleUses rest

/-- Drops leading whitespace and Markdown container markers: `>`, and list bullets or numbers
followed by a space. -/
private partial def dropContainers (cs : List Char) : List Char :=
  let cs := cs.dropWhile Char.isWhitespace
  let digits := cs.takeWhile Char.isDigit
  match cs with
  | '>' :: rest => dropContainers rest
  | c :: s :: rest =>
    if (c == '*' || c == '-' || c == '+') && s.isWhitespace then dropContainers (s :: rest)
    else match cs.drop digits.length with
      | d :: s :: rest =>
        if !digits.isEmpty && (d == '.' || d == ')') && s.isWhitespace then
          dropContainers (s :: rest)
        else cs
      | _ => cs
  | _ => cs

/-- The Flocq citation syntax in Markdown docstring text: `{coq}` and `{coq_file}` applied to
code outside code spans, and fenced code blocks whose info string starts with the word `coq`.
The contents of other fenced blocks are skipped. -/
def markdownFlocqSyntax (text : String) : Array String := Id.run do
  let isIdentChar (c : Char) := c.isAlphanum || c == '_' || c == '\''
  let mut found : Array String := #[]
  let mut fence : Option (Char × Nat) := none
  for line in text.splitOn "\n" do
    let body := dropContainers line.toList
    let marker := body.headD ' '
    let run := (body.takeWhile (· == marker)).length
    let isFence := (marker == '`' || marker == '~') && run ≥ 3
    match fence with
    | some (c, n) =>
      if isFence && marker == c && run ≥ n && (body.drop run).all Char.isWhitespace then
        fence := none
    | none =>
      if isFence then
        fence := some (marker, run)
        let info := (body.drop run).dropWhile Char.isWhitespace
        if info.take 3 == "coq".toList && !((info.drop 3).headD ' ' |> isIdentChar) then
          found := found.push "a `coq` quote block"
      else
        found := found ++ roleUses line.toList
  return found

/-- The docstrings and module docs in a command, excluding those parsed as Verso. -/
private partial def markdownDocs (stx : Syntax) : Array Syntax :=
  if (stx.isOfKind ``Lean.Parser.Command.docComment ||
      stx.isOfKind ``Lean.Parser.Command.moduleDoc) then
    if stx[1].isOfKind `Lean.Parser.Command.versoCommentBody then #[] else #[stx]
  else stx.getArgs.foldl (fun docs child => docs ++ markdownDocs child) #[]

/-- Flocq citation syntax in a Markdown docstring renders as literal text, so a misspelled or
unanchored citation there goes unnoticed. This linter points at it and offers to turn on Verso
docstrings, where `FloatSpecRoles` resolves each citation or reports an error. -/
def flocqCitationLinter : Linter where run := withSetOptionIn fun stx => do
  unless linter.flocqCitations.get (← getOptions) do return
  if (← get).messages.hasErrors then return
  for doc in markdownDocs stx do
    let text := match doc[1] with
      | .atom _ val => val
      | _ => ""
    let uses := markdownFlocqSyntax text
    if uses.isEmpty then continue
    let uses := uses.foldl (fun acc u => if acc.contains u then acc else acc.push u) #[]
    let what := " and ".intercalate uses.toList
    let hint ← if doc.isOfKind ``Lean.Parser.Command.docComment && stx.getPos? == doc.getPos? then
        let suggestion : Meta.Hint.Suggestion :=
          { suggestion := .string "set_option doc.verso true in\n/--", span? := some doc[0],
            diffGranularity := .none }
        liftCoreM <| MessageData.hint m!"Check the citations in a Verso docstring:" #[suggestion]
          (ref? := some doc[0])
      else pure m!""
    logLint linter.flocqCitations doc m!"This Markdown docstring uses {what}, which only a \
      Verso docstring checks: here it is literal text, and a misspelled or unanchored citation \
      goes unnoticed. Turn on Verso docstrings for it with `set_option doc.verso true in` (then \
      each citation must name a pinned anchor), or write the name as plain code.{hint}"

initialize addLinter flocqCitationLinter

end FloatSpec.Linter.CoqSource

end
