import FloatSpec
import FloatSpec.src.IEEE754.ComputableCompare

open Lean Elab Command

-- Compiler-backed candidates only. Matching a name or source anchor does not
-- establish that a type, body, hypotheses, or proof agrees with Rocq.
run_cmd do
  let env ← getEnv
  let mut declarations : Array Json := #[]
  for (name, info) in env.constants.toList do
    let origin := match env.getModuleIdxFor? name with
      | some idx => env.header.moduleNames[idx.toNat]!
      | none => env.mainModule
    if origin.toString.startsWith "FloatSpec.src." && !isPrivateName name && !name.isInternal then
      let kind := match info with
        | .defnInfo _ => "definition" | .thmInfo _ => "theorem" | .opaqueInfo _ => "opaque"
        | .axiomInfo _ => "axiom" | .inductInfo _ => "inductive" | .ctorInfo _ => "constructor"
        | .recInfo _ => "recursor" | .quotInfo _ => "quotient"
      declarations := declarations.push (Json.mkObj [
        ("name", toJson name.toString), ("module", toJson origin.toString),
        ("kind", toJson kind), ("noncomputable", toJson (isNoncomputable env name)),
        ("type_hash", toJson (toString info.type.hash)),
        ("value_hash", toJson ((info.value? true).map fun value => toString value.hash))])
  let refs := FloatSpec.Linter.CoqSource.sourceExt.getState env
  let references := refs.map fun ref => Json.mkObj [
    ("lean_name", toJson ref.declName.toString), ("path", toJson ref.path),
    ("line", toJson ref.line), ("name", toJson ref.coqName)]
  liftIO (IO.println (Json.mkObj [
    ("flocq_commit", toJson FloatSpec.Linter.CoqSource.flocqCommit),
    ("declarations", Json.arr declarations), ("references", Json.arr references)]).compress)
