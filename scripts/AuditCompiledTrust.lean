import FloatSpec
-- Audit opt-in helpers too; removing an aggregate import must not hide proof debt.
import FloatSpec.src.IEEE754.ComputableCompare
import Lean.Util.CollectAxioms
import Lean.Compiler.ImplementedByAttr
import Lean.Compiler.ExternAttr

open Lean Elab Command

-- Inspect elaborated declarations, including theorem and opaque bodies.
-- The environment's transitive axiom collector catches propagation through
-- wrapper theorems even when the wrapper contains no written `sorry`.
run_cmd do
  let env ← getEnv
  let mut count := 0
  let mut axioms : Array String := #[]
  let mut unsafeDecls : Array String := #[]
  let mut overrides : Array String := #[]
  let mut directSorry : Array String := #[]
  let mut transitiveSorry : Array String := #[]
  let mut unexpected : Array Json := #[]
  for (name, info) in env.constants.toList do
    let origin := match env.getModuleIdxFor? name with
      | some idx => env.header.moduleNames[idx.toNat]!
      | none => env.mainModule
    if origin.toString.startsWith "FloatSpec.src." then
      count := count + 1
      if let .axiomInfo _ := info then axioms := axioms.push name.toString
      if info.isUnsafe then unsafeDecls := unsafeDecls.push name.toString
      if (Compiler.getImplementedBy? env name).isSome || (getExternAttrData? env name).isSome then
        overrides := overrides.push name.toString
      if info.getUsedConstantsAsSet.contains ``sorryAx then
        directSorry := directSorry.push name.toString
      let dependencies ← collectAxioms name
      if dependencies.contains ``sorryAx then
        transitiveSorry := transitiveSorry.push name.toString
      let other := dependencies.filter fun ax =>
        !#[``propext, ``Classical.choice, ``Quot.sound, ``sorryAx].contains ax
      if !other.isEmpty then
        unexpected := unexpected.push (Json.mkObj [
          ("declaration", toJson name.toString),
          ("axioms", toJson (other.map Name.toString))])
  let result := Json.mkObj [
    ("project_declarations", toJson count),
    ("source_modules", toJson ((env.header.moduleNames.filter fun name =>
      name.toString.startsWith "FloatSpec.src.").map Name.toString)),
    ("project_axioms", toJson (axioms.qsort (· < ·))),
    ("unsafe_declarations", toJson (unsafeDecls.qsort (· < ·))),
    ("runtime_overrides", toJson (overrides.qsort (· < ·))),
    ("direct_sorry", toJson (directSorry.qsort (· < ·))),
    ("transitive_sorry", toJson (transitiveSorry.qsort (· < ·))),
    ("unexpected_axiom_dependencies", Json.arr unexpected)]
  liftIO (IO.println result.compress)
