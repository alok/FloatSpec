import FloatSpec.src.IEEE754.BinarySingleNaNSourceFacade

/-! Executable SingleNaN arithmetic at one-bit precision. This format is legal
for SingleNaN, even though the full-payload bridge needs room for a NaN payload.
The expected answers are literal boundaries, not another rounding algorithm. -/

namespace SingleNaNArithmetic

private instance : Prec_gt_0 (1 : Int) := ⟨by decide⟩
private instance : Prec_lt_emax (1 : Int) (2 : Int) := ⟨by decide⟩

private def one : BinarySingleNaN.binary_float 1 2 :=
  BinarySingleNaN.SF2B' (.S754_finite false 1 0)
private def two : BinarySingleNaN.binary_float 1 2 :=
  BinarySingleNaN.SF2B' (.S754_finite false 1 1)
private def negTwo : BinarySingleNaN.binary_float 1 2 :=
  BinarySingleNaN.SF2B' (.S754_finite true 1 1)

private def directRow (mode : RoundingMode) : List StandardFloat :=
  [BinarySingleNaN.Bplus mode two one,
   BinarySingleNaN.Bminus mode one one,
   BinarySingleNaN.Bmult mode two two,
   BinarySingleNaN.Bdiv mode one two,
   BinarySingleNaN.Bsqrt mode two,
   BinarySingleNaN.Bfma mode two two negTwo].map binarySingleNaNFloatToStandardFloat

private def sourceRow (mode : FloatSpec.IEEE754.BinarySingleNaN.Source.mode) : List StandardFloat :=
  [FloatSpec.IEEE754.BinarySingleNaN.Source.Bplus mode two one,
   FloatSpec.IEEE754.BinarySingleNaN.Source.Bminus mode one one,
   FloatSpec.IEEE754.BinarySingleNaN.Source.Bmult mode two two,
   FloatSpec.IEEE754.BinarySingleNaN.Source.Bdiv mode one two,
   FloatSpec.IEEE754.BinarySingleNaN.Source.Bsqrt mode two,
   FloatSpec.IEEE754.BinarySingleNaN.Source.Bfma mode two two negTwo].map
    binarySingleNaNFloatToStandardFloat

private def expected : List (List StandardFloat) :=
  [[.S754_infinity false, .S754_zero false, .S754_infinity false,
    .S754_zero false, .S754_finite false 1 0, .S754_finite false 1 1],
   [.S754_finite false 1 1, .S754_zero false, .S754_finite false 1 1,
    .S754_zero false, .S754_finite false 1 0, .S754_finite false 1 1],
   [.S754_finite false 1 1, .S754_zero true, .S754_finite false 1 1,
    .S754_zero false, .S754_finite false 1 0, .S754_finite false 1 1],
   [.S754_infinity false, .S754_zero false, .S754_infinity false,
    .S754_finite false 1 0, .S754_finite false 1 1, .S754_finite false 1 1],
   [.S754_infinity false, .S754_zero false, .S754_infinity false,
    .S754_finite false 1 0, .S754_finite false 1 0, .S754_finite false 1 1]]

private def directRows := [.RNE, .RTZ, .RTN, .RTP, .RNA].map directRow
private def sourceRows := [.mode_NE, .mode_ZR, .mode_DN, .mode_UP, .mode_NA].map sourceRow

example : directRows = expected := by decide +kernel
example : sourceRows = expected := by decide +kernel

private def check : IO Unit := do
  unless decide (directRows = expected ∧ sourceRows = expected) do
    throw (IO.userError "SingleNaN arithmetic boundary mismatch")
  IO.println "PASS: 30 one-bit arithmetic boundaries through each of two SingleNaN APIs (compiled and kernel-checked)."

#eval check

end SingleNaNArithmetic
