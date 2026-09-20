import FloatSpec.src.IEEE754.BinarySingleNaNSourceFacade

/-! Raw overflow retains the source positive-mantissa fallback at all integer
precisions. Validity claims still require their separate format hypotheses. -/

namespace RawOverflow

private def rows : List StandardFloat :=
  [BinarySingleNaN.binary_overflow (prec := 0) (emax := 1) .RTZ false,
   BinarySingleNaN.binary_overflow (prec := -1) (emax := 1) .RTZ true,
   standard_binary_overflow 0 (-4) .RNE true,
   FF2SF (Binary.binary_overflow (prec := 3) (emax := 3) .RTZ false),
   full_float.toStandardFloat (Binary.binary_overflow_exact (prec := 0) (emax := 1) .RTZ false),
   FF2SF (_root_.binary_overflow (-3) (-4) .RTP true),
   BinarySingleNaN.binary_overflow (prec := 3) (emax := 4) .RTZ true]

private def expected : List StandardFloat :=
  [.S754_finite false 1 1, .S754_finite true 1 2, .S754_infinity true,
   .S754_finite false 7 0, .S754_finite false 1 1, .S754_finite true 1 (-1),
   .S754_finite true 7 1]

example : rows = expected := by decide +kernel
example : rawOverflowMantissa (-1) = 1 ∧ rawOverflowMantissa 0 = 1 ∧
    rawOverflowMantissa 3 = 7 := by decide +kernel
example (prec : Int) : 0 < rawOverflowMantissa prec := rawOverflowMantissa_pos prec

private def check : IO Unit := do
  unless decide (rows = expected) do throw (IO.userError "raw overflow fallback mismatch")
  IO.println "PASS: seven raw overflow boundaries (compiled and kernel-checked)."

#eval check

end RawOverflow
