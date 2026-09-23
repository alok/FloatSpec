import FloatSpec

open Lean Elab Command

-- Export elaborated attributes, not text that merely resembles an attribute.
-- Combined attributes and `attribute [...] name` commands are included;
-- annotations inside comments or quoted strings are not.
run_cmd do
  let refs := FloatSpec.Linter.CoqSource.sourceExt.getState (← getEnv)
  let entries := refs.map fun ref => Json.mkObj [
    ("lean_name", toJson ref.declName.toString), ("path", toJson ref.path),
    ("line", toJson ref.line), ("name", toJson ref.coqName)]
  let result := Json.mkObj [
    ("flocq_commit", toJson FloatSpec.Linter.CoqSource.flocqCommit),
    ("source_files", toJson FloatSpec.Linter.CoqSource.flocqSourceFiles),
    ("references", Json.arr entries)]
  liftIO (IO.println result.compress)
