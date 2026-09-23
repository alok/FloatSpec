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

/-- Every Rocq source file under `src/` at `flocqCommit`, in `git ls-tree` order.
`scripts/validate_flocq_source_refs.py` checks this list against the pinned checkout. -/
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

end FloatSpec.Linter.CoqSource

end
