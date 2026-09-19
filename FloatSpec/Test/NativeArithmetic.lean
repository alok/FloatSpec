import FloatSpec.src.IEEE754.PrimFloat

/-! Arithmetic adapters for native/model/Rocq differential execution. Values are
serialized through the single-NaN quotient; signed zeros remain distinct. -/

namespace FloatSpec.Test.NativeArithmetic

open FaithfulPrimFloat

/-- Native binary64 addition, subtraction, multiplication, division, and square
root, preceded by both canonicalized inputs. Native arithmetic uses RNE. -/
def nativeObservation (left right : UInt64) : List Int :=
  let x := Float.ofBits left
  let y := Float.ofBits right
  [x.toModel.toBits.toNat, y.toModel.toBits.toNat,
   (x + y).toModel.toBits.toNat, (x - y).toModel.toBits.toNat,
   (x * y).toModel.toBits.toNat, (x / y).toModel.toBits.toNat,
   x.sqrt.toModel.toBits.toNat]

/-- The same seven fields through the actual source-facing Lean operations. -/
noncomputable def modelObservation (left right : UInt64) : List Int :=
  let x := PrimitiveFloat.ofModel (Float.Model.ofBits left)
  let y := PrimitiveFloat.ofModel (Float.Model.ofBits right)
  [x.toModel.toBits.toNat, y.toModel.toBits.toNat,
   (add x y).toModel.toBits.toNat, (sub x y).toModel.toBits.toNat,
   (mul x y).toModel.toBits.toNat, (div x y).toModel.toBits.toNat,
   (sqrt x).toModel.toBits.toNat]

-- The old unary-counting positive conversion cannot reduce this 53-bit input
-- within the ordinary resource bounds. This exercises the actual converter.
theorem positive_conversion_binary64 :
    FloatSpec.Core.Zaux.positiveToNat
      (binaryPositiveOfNat 9007199254740992 (by decide)) = 9007199254740992 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem one_and_two : modelObservation 0x3ff0000000000000 0x4000000000000000 =
    [0x3ff0000000000000, 0x4000000000000000, 0x4008000000000000,
     0xbff0000000000000, 0x4000000000000000, 0x3fe0000000000000,
     0x3ff0000000000000] := by
  decide +kernel

end FloatSpec.Test.NativeArithmetic
