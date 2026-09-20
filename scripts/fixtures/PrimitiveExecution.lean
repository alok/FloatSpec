import FloatSpec.src.IEEE754.PrimFloat

/-! Compilation and literal smoke checks for each formerly noncomputable primitive
entry point. The broader domain is exercised by the prim_arithmetic, prim_helpers,
and prim_round differential families; these 37 examples alone are not coverage. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

namespace PrimitiveExecution

private def check_binary_round_aux : StandardFloat := FaithfulPrimFloat.binary_round_aux false 1 0 .loc_Exact
private def check_SFmul : StandardFloat := FaithfulPrimFloat.SFmul (FaithfulPrimFloat.Prim2SF FaithfulPrimFloat.one) (FaithfulPrimFloat.Prim2SF FaithfulPrimFloat.one)
private def check_SFdiv : StandardFloat := FaithfulPrimFloat.SFdiv (FaithfulPrimFloat.Prim2SF FaithfulPrimFloat.one) (FaithfulPrimFloat.Prim2SF FaithfulPrimFloat.one)
private def check_binary_round : StandardFloat := FaithfulPrimFloat.binary_round false .xH 0
private def check_binary_normalize : StandardFloat := FaithfulPrimFloat.binary_normalize 1 0 false
private def check_SFldexp : StandardFloat := FaithfulPrimFloat.SFldexp (FaithfulPrimFloat.Prim2SF FaithfulPrimFloat.one) 1
private def check_SFadd : StandardFloat := FaithfulPrimFloat.SFadd (FaithfulPrimFloat.Prim2SF FaithfulPrimFloat.one) (FaithfulPrimFloat.Prim2SF FaithfulPrimFloat.one)
private def check_mul : StandardFloat := FaithfulPrimFloat.Prim2SF (FaithfulPrimFloat.mul FaithfulPrimFloat.one FaithfulPrimFloat.one)
private def check_div : StandardFloat := FaithfulPrimFloat.Prim2SF (FaithfulPrimFloat.div FaithfulPrimFloat.one FaithfulPrimFloat.one)
private def check_sqrt : StandardFloat := FaithfulPrimFloat.Prim2SF (FaithfulPrimFloat.sqrt FaithfulPrimFloat.one)
private def check_of_uint63 : StandardFloat := FaithfulPrimFloat.Prim2SF (FaithfulPrimFloat.of_uint63 (FaithfulPrimFloat.Uint63.ofInt 1 (by decide) (by decide)))
private def check_ldexp : StandardFloat := FaithfulPrimFloat.Prim2SF (FaithfulPrimFloat.ldexp FaithfulPrimFloat.one 1)
private def check_Z_ldexp : StandardFloat := FaithfulPrimFloat.Prim2SF (FaithfulPrimFloat.Z.ldexp FaithfulPrimFloat.one 1)
private def check_Z_frexp : StandardFloat := FaithfulPrimFloat.Prim2SF ((FaithfulPrimFloat.Z.frexp FaithfulPrimFloat.one).1)
private def check_ldshiftexp : StandardFloat := FaithfulPrimFloat.Prim2SF (FaithfulPrimFloat.ldshiftexp FaithfulPrimFloat.one (FaithfulPrimFloat.Uint63.ofInt 2102 (by decide) (by decide)))
private def check_frshiftexp : StandardFloat := FaithfulPrimFloat.Prim2SF ((FaithfulPrimFloat.frshiftexp FaithfulPrimFloat.one).1)
private def check_ulp : StandardFloat := FaithfulPrimFloat.Prim2SF (FaithfulPrimFloat.ulp FaithfulPrimFloat.one)
private def check_next_up : StandardFloat := FaithfulPrimFloat.Prim2SF (FaithfulPrimFloat.next_up FaithfulPrimFloat.one)
private def check_next_down : StandardFloat := FaithfulPrimFloat.Prim2SF (FaithfulPrimFloat.next_down FaithfulPrimFloat.one)
private def check_add : StandardFloat := FaithfulPrimFloat.Prim2SF (FaithfulPrimFloat.add FaithfulPrimFloat.one FaithfulPrimFloat.one)
private def check_two : StandardFloat := FaithfulPrimFloat.Prim2SF (FaithfulPrimFloat.two)
private def check_sub : StandardFloat := FaithfulPrimFloat.Prim2SF (FaithfulPrimFloat.sub FaithfulPrimFloat.one FaithfulPrimFloat.one)
private def check_Mul_instance : StandardFloat := FaithfulPrimFloat.Prim2SF (FaithfulPrimFloat.one * FaithfulPrimFloat.one)
private def check_Div_instance : StandardFloat := FaithfulPrimFloat.Prim2SF (FaithfulPrimFloat.one / FaithfulPrimFloat.one)
private def check_Add_instance : StandardFloat := FaithfulPrimFloat.Prim2SF (FaithfulPrimFloat.one + FaithfulPrimFloat.one)
private def check_Sub_instance : StandardFloat := FaithfulPrimFloat.Prim2SF (FaithfulPrimFloat.one - FaithfulPrimFloat.one)
private def check_Bmult : StandardFloat := FaithfulPrimFloat.B2SF (FaithfulPrimFloat.Bmult .RNE FaithfulPrimFloat.Bone FaithfulPrimFloat.Bone)
private def check_Bdiv : StandardFloat := FaithfulPrimFloat.B2SF (FaithfulPrimFloat.Bdiv .RNE FaithfulPrimFloat.Bone FaithfulPrimFloat.Bone)
private def check_Bsqrt : StandardFloat := FaithfulPrimFloat.B2SF (FaithfulPrimFloat.Bsqrt .RNE FaithfulPrimFloat.Bone)
private def check_binary_normalize_bsn : StandardFloat := FaithfulPrimFloat.B2SF (FaithfulPrimFloat.binary_normalize_bsn .RNE 1 0 false)
private def check_Bldexp : StandardFloat := FaithfulPrimFloat.B2SF (FaithfulPrimFloat.Bldexp .RNE FaithfulPrimFloat.Bone 1)
private def check_Bfrexp : StandardFloat := FaithfulPrimFloat.B2SF ((FaithfulPrimFloat.Bfrexp FaithfulPrimFloat.Bone).1)
private def check_Bulp : StandardFloat := FaithfulPrimFloat.B2SF (FaithfulPrimFloat.Bulp' FaithfulPrimFloat.Bone)
private def check_Bsucc : StandardFloat := FaithfulPrimFloat.B2SF (FaithfulPrimFloat.Bsucc FaithfulPrimFloat.Bone)
private def check_Bpred : StandardFloat := FaithfulPrimFloat.B2SF (FaithfulPrimFloat.Bpred FaithfulPrimFloat.Bone)
private def check_Bplus : StandardFloat := FaithfulPrimFloat.B2SF (FaithfulPrimFloat.Bplus .RNE FaithfulPrimFloat.Bone FaithfulPrimFloat.Bone)
private def check_Bminus : StandardFloat := FaithfulPrimFloat.B2SF (FaithfulPrimFloat.Bminus .RNE FaithfulPrimFloat.Bone FaithfulPrimFloat.Bone)

private def outputs : List StandardFloat :=
  [check_binary_round_aux,
   check_SFmul,
   check_SFdiv,
   check_binary_round,
   check_binary_normalize,
   check_SFldexp,
   check_SFadd,
   check_mul,
   check_div,
   check_sqrt,
   check_of_uint63,
   check_ldexp,
   check_Z_ldexp,
   check_Z_frexp,
   check_ldshiftexp,
   check_frshiftexp,
   check_ulp,
   check_next_up,
   check_next_down,
   check_add,
   check_two,
   check_sub,
   check_Mul_instance,
   check_Div_instance,
   check_Add_instance,
   check_Sub_instance,
   check_Bmult,
   check_Bdiv,
   check_Bsqrt,
   check_binary_normalize_bsn,
   check_Bldexp,
   check_Bfrexp,
   check_Bulp,
   check_Bsucc,
   check_Bpred,
   check_Bplus,
   check_Bminus]

private def expected : List StandardFloat :=
  [.S754_finite false 1 (0),
   .S754_finite false 4503599627370496 (-52),
   .S754_finite false 4503599627370496 (-52),
   .S754_finite false 4503599627370496 (-52),
   .S754_finite false 4503599627370496 (-52),
   .S754_finite false 4503599627370496 (-51),
   .S754_finite false 4503599627370496 (-51),
   .S754_finite false 4503599627370496 (-52),
   .S754_finite false 4503599627370496 (-52),
   .S754_finite false 4503599627370496 (-52),
   .S754_finite false 4503599627370496 (-52),
   .S754_finite false 4503599627370496 (-51),
   .S754_finite false 4503599627370496 (-51),
   .S754_finite false 4503599627370496 (-53),
   .S754_finite false 4503599627370496 (-51),
   .S754_finite false 4503599627370496 (-53),
   .S754_finite false 4503599627370496 (-104),
   .S754_finite false 4503599627370497 (-52),
   .S754_finite false 9007199254740991 (-53),
   .S754_finite false 4503599627370496 (-51),
   .S754_finite false 4503599627370496 (-51),
   .S754_zero false,
   .S754_finite false 4503599627370496 (-52),
   .S754_finite false 4503599627370496 (-52),
   .S754_finite false 4503599627370496 (-51),
   .S754_zero false,
   .S754_finite false 4503599627370496 (-52),
   .S754_finite false 4503599627370496 (-52),
   .S754_finite false 4503599627370496 (-52),
   .S754_finite false 4503599627370496 (-52),
   .S754_finite false 4503599627370496 (-51),
   .S754_finite false 4503599627370496 (-53),
   .S754_finite false 4503599627370496 (-104),
   .S754_finite false 4503599627370497 (-52),
   .S754_finite false 9007199254740991 (-53),
   .S754_finite false 4503599627370496 (-51),
   .S754_zero false]

theorem each_entry_point_matches_literal : outputs = expected := by decide +kernel

theorem decomposition_exponents :
    (FaithfulPrimFloat.Z.frexp FaithfulPrimFloat.one).2 = 1 ∧
    FaithfulPrimFloat.Uint63.to_Z (FaithfulPrimFloat.frshiftexp FaithfulPrimFloat.one).2 = 2102 ∧
    (FaithfulPrimFloat.Bfrexp FaithfulPrimFloat.Bone).2 = 1 := by decide +kernel

private def rawProduct : StandardFloat :=
  FaithfulPrimFloat.SFmul (.S754_finite false 3 (-1)) (.S754_finite false 3 (-1))

private def primitiveProduct : StandardFloat :=
  let x := FaithfulPrimFloat.SF2Prim (.S754_finite false 3 (-1))
  FaithfulPrimFloat.Prim2SF (x * x)

-- Both encode 2.25, but the raw source helper does not promise a canonical
-- result when its inputs are noncanonical. Numeric conversion is a separate step.
theorem raw_and_converted_arithmetic_have_distinct_encodings :
    rawProduct = .S754_finite false 9 (-2) ∧
    primitiveProduct = .S754_finite false 5066549580791808 (-51) ∧
    validBinarySingleNaNStandardFloat (prec := 53) (emax := 1024) rawProduct = false := by
  decide +kernel

#eval do
  unless decide (outputs = expected) do
    throw (IO.userError "primitive executable entry point mismatch")
  unless (FaithfulPrimFloat.Z.frexp FaithfulPrimFloat.one).2 == 1 &&
      FaithfulPrimFloat.Uint63.to_Z (FaithfulPrimFloat.frshiftexp FaithfulPrimFloat.one).2 == 2102 &&
      (FaithfulPrimFloat.Bfrexp FaithfulPrimFloat.Bone).2 == 1 do
    throw (IO.userError "primitive executable decomposition exponent mismatch")
  IO.println "PASS: all 33 primitive definitions, four notation instances, and three decomposition exponents executed."
  unless decide (rawProduct = StandardFloat.S754_finite false 9 (-2)) &&
      decide (primitiveProduct = StandardFloat.S754_finite false 5066549580791808 (-51)) do
    throw (IO.userError "raw versus converted primitive multiplication mismatch")
  IO.println "PASS: raw 1.5 squared is (9,-2); converted primitive 1.5 squared is canonical 2.25."

#print axioms each_entry_point_matches_literal
#print axioms decomposition_exponents
#print axioms raw_and_converted_arithmetic_have_distinct_encodings

end PrimitiveExecution
