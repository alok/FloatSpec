import FloatSpec.src.IEEE754.BinarySingleNaNSourceFacade

/-! The public raw rounding APIs execute without format-validity instances.
These finite assertions are separate from the conditional real-value theorems.
The full-payload and SingleNaN entry points share their integer algorithm. -/

namespace RawIEEERounding

private def nine : FloatSpec.Core.Zaux.Positive := binaryPositiveOfNat 9 (by decide)

private def rows : List StandardFloat :=
  [BinarySingleNaN.binary_round (prec := 3) (emax := 4) .RNE false nine (-3),
   BinarySingleNaN.binary_round (prec := 3) (emax := 4) .RNA false nine (-3),
   full_float.toStandardFloat
     (Binary.binary_round (prec := 3) (emax := 4) .RTN true nine (-3)),
   BinarySingleNaN.binary_round_aux (prec := 3) (emax := 4) .RNE true 0 (-4) .loc_Exact,
   full_float.toStandardFloat
     (Binary.binary_round_aux (prec := 3) (emax := 4) .RNE false (-1) (-4) .loc_Exact),
   full_float.toStandardFloat
     (Binary.binary_round (prec := 3) (emax := 3) .RNE false .xH 0),
   -- Regressions mined from differential seed 826411: signed shifting must
   -- truncate toward zero, even though these raw inputs have no value theorem.
   BinarySingleNaN.binary_round_aux (prec := -1) (emax := 1) .RTZ false (-2) 2 .loc_Exact,
   full_float.toStandardFloat
     (Binary.binary_round_aux (prec := 3) (emax := 4) .RNA true (-7) (-6) .loc_Exact),
   BinarySingleNaN.binary_round_aux (prec := 3) (emax := 3) .RTZ true (-2) (-5)
     (.loc_Inexact .lt)]

private def expected : List StandardFloat :=
  [.S754_finite false 4 (-2), .S754_finite false 5 (-2),
   .S754_finite true 5 (-2), .S754_zero true, .S754_nan, .S754_finite false 4 (-2),
   .S754_zero false, .S754_zero true, .S754_zero true]

example : rows = expected := by decide +kernel

private def check : IO Unit := do
  unless decide (rows = expected) do throw (IO.userError "raw IEEE rounding boundary mismatch")
  IO.println "PASS: nine raw IEEE rounding boundaries (compiled and kernel-checked)."

#eval check

end RawIEEERounding
