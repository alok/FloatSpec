import FloatSpec.src.IEEE754.PrimFloat

/-! Serialization adapters for four-path binary64 execution tests. These call the
actual implementations; they do not duplicate the arithmetic. NaNs are observed
through the single-NaN model, so payload preservation is not asserted. -/

namespace FloatSpec.Test.NativeIEEE

open FaithfulPrimFloat

/-- Native results: canonical input bits, successor bits, predecessor bits,
`frExp` significand bits, and its signed exponent. -/
def nativeObservation (word : UInt64) : List Int :=
  let x := Float.ofBits word
  let result := x.frExp
  [x.toModel.toBits.toNat,
   (PrimitiveFloat.nativeNextUp x).toModel.toBits.toNat,
   (PrimitiveFloat.nativeNextDown x).toModel.toBits.toNat,
   result.1.toModel.toBits.toNat, result.2]

/-- The same five observations through the Lean port's logical Flocq carrier.
Unlike native `frExp`, this total model has a specified exceptional exponent. -/
def modelObservation (word : UInt64) : List Int :=
  let x := PrimitiveFloat.ofModel (Float.Model.ofBits word)
  let result := FaithfulPrimFloat.Z.frexp x
  [x.toModel.toBits.toNat, (next_up x).toModel.toBits.toNat,
   (next_down x).toModel.toBits.toNat, result.1.toModel.toBits.toNat, result.2]

-- A permanent, closed regression at the smallest positive subnormal.
set_option maxRecDepth 100000 in
theorem minimum_subnormal : modelObservation 1 =
    [1, 2, 0, 4602678819172646912, -1073] := by
  decide +kernel

end FloatSpec.Test.NativeIEEE
