module

public meta import Lean.Elab.Command
public meta import Lean.Linter.Basic
public meta import Lean.DocString

/-! Pinned Flocq source references and an opt-in declaration coverage check. -/

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

initialize sourceExt : SimplePersistentEnvExtension SourceRef (Array SourceRef) ←
  registerSimplePersistentEnvExtension {
    addImportedFn entries := entries.flatten
    addEntryFn entries entry := entries.push entry
  }

/-- Look up a declaration's pinned Flocq source reference. -/
def sourceRef? (env : Environment) (declName : Name) : Option SourceRef :=
  (sourceExt.getState env).find? (·.declName == declName)

/-- A clickable link to the pinned source declaration. -/
def sourceUrl (ref : SourceRef) : String :=
  s!"https://gitlab.inria.fr/flocq/flocq/-/blob/{flocqCommit}/{ref.path}#L{ref.line}"

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

namespace FloatSpec.Linter.CoqSource

/-- Require a pinned Flocq source link on public definitions in an opted-in module. -/
register_option linter.coqSource : Bool := {
  defValue := false
  descr := "warn when a public def/abbrev lacks @[flocq_source]"
}

private def definitionId? (stx : Syntax) : Option Syntax := do
  let declaration ← stx.find? (·.isOfKind ``Lean.Parser.Command.declaration)
  if (declaration.find? (·.isOfKind ``Lean.Parser.Command.private)).isSome then none
  let body := declaration[1]
  if body.isOfKind ``Lean.Parser.Command.definition ||
      body.isOfKind ``Lean.Parser.Command.abbrev then
    return body[1][0]
  none

/-- The source-link coverage linter. Enable it in a source-facing file once
that file's local helpers have been separated or explicitly classified. -/
def coqSourceLinter : Linter where run := withSetOptionIn fun stx => do
  unless linter.coqSource.get (← getOptions) && (← getInfoState).enabled do return
  if (← get).messages.hasErrors then return
  let env ← getEnv
  let some id := definitionId? stx | return
  if id.isMissing then return
  let name := (← getCurrNamespace) ++ id.getId
  if isPrivateName name then return
  unless hasSourceRef env name do
    logLint linter.coqSource id
      s!"public definition {name} has no pinned Flocq link; add \
        @[flocq_source \"src/Module.v\" LINE \"coq_name\"] \
        or keep a FloatSpec-only helper outside the source-facing surface"

initialize addLinter coqSourceLinter

end FloatSpec.Linter.CoqSource

end
