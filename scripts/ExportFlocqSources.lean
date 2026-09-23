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
  -- The `coq` docstring quotes of every FloatSpec module, as compiled: each with the anchor Lean
  -- resolved it to and the line of its fence.
  let env ← getEnv
  let modules := env.header.moduleNames.filter fun m => m.getRoot.toString.startsWith "FloatSpec"
  let quotes := modules.flatMap fun m =>
    (FloatSpec.Roles.moduleQuotes env m).map fun q =>
      q.json.setObjVal! "module" (toJson m.toString)
  let result := Json.mkObj [
    ("flocq_commit", toJson FloatSpec.Linter.CoqSource.flocqCommit),
    ("source_files", toJson FloatSpec.Linter.CoqSource.flocqSourceFiles),
    ("references", Json.arr entries),
    ("quote_modules", toJson (modules.map toString)),
    ("quotes", Json.arr quotes)]
  liftIO (IO.println result.compress)
