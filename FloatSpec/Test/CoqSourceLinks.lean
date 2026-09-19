import FloatSpec.src.IEEE754.BitsSourceFacade
import FloatSpec.src.Core.FLX
import FloatSpec.Linter.CoqSourceLinter

/-! Check that source references survive module imports and expose pinned links. -/

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let expected := #[
    (`valid_binary, "src/IEEE754/Binary.v#L166"),
    (`FloatSpec.IEEE754.Bits.Source.join_bits, "src/IEEE754/Bits.v#L37"),
    (`FloatSpec.IEEE754.Bits.Source.binary_float_of_bits,
      "src/IEEE754/Bits.v#L491"),
    (`FloatSpec.Core.FLX.FLX_exp, "src/Core/FLX.v#L43"),
    (`FloatSpec.Core.FLX.FLX_format, "src/Core/FLX.v#L39"),
    (`FloatSpec.Core.FLX.FLXN_format, "src/Core/FLX.v#L136")
  ]
  for (decl, fragment) in expected do
    let some ref := FloatSpec.Linter.CoqSource.sourceRef? env decl
      | throwError "missing imported Flocq source reference for {decl}"
    unless ((FloatSpec.Linter.CoqSource.sourceUrl ref).splitOn fragment).length > 1 do
      throwError "wrong metadata source-link target for {decl}"
    let some _doc ← Lean.findDocString? env decl
      | throwError "missing declaration documentation for {decl}"
