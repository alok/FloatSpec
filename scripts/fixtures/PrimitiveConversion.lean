import FloatSpec.src.IEEE754.PrimFloat

/-! Numeric primitive conversion is not the rejecting SF2B' validity adapter.
The expected constructor rows retain signs, uint63 wrapping, and two rounding
stages. No real-valued oracle or admitted refinement theorem is used. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

namespace PrimitiveConversion

private instance : Prec_gt_0 (53 : Int) := FaithfulPrimFloat.Hprec
private instance : Prec_lt_emax (53 : Int) (1024 : Int) := FaithfulPrimFloat.Hmax

private def inputs : List StandardFloat :=
  [.S754_finite false 3 (-1),
   .S754_finite false 9223372036854775808 (0),
   .S754_finite false 9223372036854775809 (0),
   .S754_finite false 9223372036854775807 (0),
   .S754_finite false 9007199254740997 (-1077),
   .S754_zero false,
   .S754_infinity false,
   .S754_finite false 4503599627370496 (-52),
   .S754_finite false 1 (-1074),
   .S754_finite false 9007199254740991 (971),
   .S754_finite false 1 (-1075),
   .S754_finite false 3 (-1075),
   .S754_finite false 1 (1024),
   .S754_finite false 1 (-1000000000000000000000000000000),
   .S754_finite false 1 (1000000000000000000000000000000),
   .S754_finite true 3 (-1),
   .S754_finite true 9223372036854775808 (0),
   .S754_finite true 9223372036854775809 (0),
   .S754_finite true 9223372036854775807 (0),
   .S754_finite true 9007199254740997 (-1077),
   .S754_zero true,
   .S754_infinity true,
   .S754_finite true 4503599627370496 (-52),
   .S754_finite true 1 (-1074),
   .S754_finite true 9007199254740991 (971),
   .S754_finite true 1 (-1075),
   .S754_finite true 3 (-1075),
   .S754_finite true 1 (1024),
   .S754_finite true 1 (-1000000000000000000000000000000),
   .S754_finite true 1 (1000000000000000000000000000000),
   .S754_nan]

private def expected : List StandardFloat :=
  [.S754_finite false 6755399441055744 (-52),
   .S754_zero false,
   .S754_finite false 4503599627370496 (-52),
   .S754_finite false 4503599627370496 (11),
   .S754_finite false 1125899906842624 (-1074),
   .S754_zero false,
   .S754_infinity false,
   .S754_finite false 4503599627370496 (-52),
   .S754_finite false 1 (-1074),
   .S754_finite false 9007199254740991 (971),
   .S754_zero false,
   .S754_finite false 2 (-1074),
   .S754_infinity false,
   .S754_zero false,
   .S754_infinity false,
   .S754_finite true 6755399441055744 (-52),
   .S754_zero true,
   .S754_finite true 4503599627370496 (-52),
   .S754_finite true 4503599627370496 (11),
   .S754_finite true 1125899906842624 (-1074),
   .S754_zero true,
   .S754_infinity true,
   .S754_finite true 4503599627370496 (-52),
   .S754_finite true 1 (-1074),
   .S754_finite true 9007199254740991 (971),
   .S754_zero true,
   .S754_finite true 2 (-1074),
   .S754_infinity true,
   .S754_zero true,
   .S754_infinity true,
   .S754_nan]

private def outputs : List StandardFloat :=
  inputs.map (fun x => FaithfulPrimFloat.Prim2SF (FaithfulPrimFloat.SF2Prim x))

theorem literal_conversions : outputs = expected := by decide +kernel

-- The validity adapter has a different total contract: reject instead of round.
theorem numeric_conversion_is_not_validation :
    FaithfulPrimFloat.Prim2SF (FaithfulPrimFloat.SF2Prim (.S754_finite false 3 (-1))) ≠
      binarySingleNaNFloatToStandardFloat
        (BinarySingleNaN.SF2B' (prec := 53) (emax := 1024) (.S754_finite false 3 (-1))) := by
  decide +kernel

private def doubleRoundInput : StandardFloat := .S754_finite false 9007199254740997 (-1077)
private def oneShot : StandardFloat :=
  binarySingleNaNFloatToStandardFloat (Binary.B2BSN
    (Binary.binary_normalize (prec := 53) (emax := 1024)
      .RNE 9007199254740997 (-1077) false))

theorem two_roundings_are_not_one :
    FaithfulPrimFloat.Prim2SF (FaithfulPrimFloat.SF2Prim doubleRoundInput) =
      .S754_finite false 1125899906842624 (-1074) ∧
    oneShot = .S754_finite false 1125899906842625 (-1074) := by
  decide +kernel

private def checks : Bool :=
  decide (outputs = expected) &&
    decide (FaithfulPrimFloat.Prim2SF (FaithfulPrimFloat.SF2Prim doubleRoundInput) ≠ oneShot)

#eval do
  unless checks do
    throw (IO.userError "primitive numeric conversion boundary mismatch")
  IO.println "PASS: 31 literal primitive conversions, uint63 wrapping, and a double-rounding counterexample."

#print axioms literal_conversions
#print axioms numeric_conversion_is_not_validation
#print axioms two_roundings_are_not_one

end PrimitiveConversion
