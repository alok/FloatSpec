import FloatSpec.src.IEEE754.Bits
import FloatSpec.src.IEEE754.PrimFloat

/-! Run with `lake env lean --run scripts/fixtures/GuidedDemo.lean`.
Each section is a computation using the port, followed by a kernel-checked
finite assertion. These examples do not establish universal conformance. -/

namespace GuidedDemo

private def observe : StandardFloat → List Int
  | .S754_finite sign mantissa exponent => [if sign then 1 else 0, mantissa, exponent]
  | _ => []

private def sumBits : Nat :=
  (bits_of_b32 (b32_plus .RNE (b32_of_bits 0x3fc00000) (b32_of_bits 0x40100000))).toNat

example : sumBits = 0x40700000 := by decide +kernel

private def modes (sign : Bool) : List (List Int) :=
  [.RNE, .RTZ, .RTN, .RTP, .RNA].map fun mode =>
    observe (binary_round (prec := 3) (emax := 4) mode sign 9 (-3))

example : modes false = [[0,4,-2], [0,4,-2], [0,4,-2], [0,5,-2], [0,5,-2]] ∧
    modes true = [[1,4,-2], [1,4,-2], [1,5,-2], [1,4,-2], [1,5,-2]] := by
  decide +kernel

private def direct : List Int :=
  observe (binary_round (prec := 3) (emax := 10) .RNE false 73 (-6))

private def viaFour : List Int :=
  match binary_round (prec := 4) (emax := 10) .RNE false 73 (-6) with
  | .S754_finite sign mantissa exponent =>
      observe (binary_round (prec := 3) (emax := 10) .RNE sign mantissa exponent)
  | _ => []

example : direct = [0,5,-2] ∧ viaFour = [0,4,-2] := by decide +kernel

private def zeroComparison : Option Ordering :=
  b64_compare (b64_of_bits 0) (b64_of_bits 0x8000000000000000)

private def nanComparison : Option Ordering :=
  b64_compare (b64_of_bits 0x7ff8000000000000) (b64_of_bits 0)

private def booleanComparison : List (List Bool) :=
  let positiveZero : BinarySingleNaN.binary_float 3 4 := .B754_zero false
  let negativeZero : BinarySingleNaN.binary_float 3 4 := .B754_zero true
  [negativeZero, .B754_nan].map fun y =>
    [BinarySingleNaN.Beqb positiveZero y,
     BinarySingleNaN.Bltb positiveZero y, BinarySingleNaN.Bleb positiveZero y]

private def negativeTinySuccessor : Nat :=
  (bits_of_b64 (b64_succ (b64_of_bits 0x8000000000000001))).toNat

example : zeroComparison = some .eq ∧ nanComparison = none ∧
    negativeTinySuccessor = 0x8000000000000000 ∧
    booleanComparison = [[true, false, true], [false, false, false]] := by decide +kernel

private def rawValidity : List Bool :=
  [valid_binary_SF (prec := 3) (emax := 4) (.S754_finite false 1 0),
   valid_binary_SF (prec := 3) (emax := 4) (.S754_finite false 4 (-2))]

example : rawValidity = [false, true] := by decide +kernel

private def signedShiftAndFloor : List Int :=
  [(shr_1 ⟨-1, false, false⟩).shr_m, (-1 : Int) / 2]

private def rawRoundIsNegativeZero : Bool :=
  match binary_round_aux (prec := 3) (emax := 4) .RNA true (-7) (-6) .loc_Exact with
  | .S754_zero true => true
  | _ => false

example : signedShiftAndFloor = [0, -1] ∧ rawRoundIsNegativeZero = true := by
  decide +kernel

private def numericConversion : List Int :=
  observe (FaithfulPrimFloat.Prim2SF
    (FaithfulPrimFloat.SF2Prim (.S754_finite false 3 (-1))))

private def conversionDouble : List Int :=
  observe (FaithfulPrimFloat.Prim2SF
    (FaithfulPrimFloat.SF2Prim (.S754_finite false 9007199254740997 (-1077))))

private def conversionSingle : List Int :=
  observe (binary_round (prec := 53) (emax := 1024) .RNE false 9007199254740997 (-1077))

example : numericConversion = [0,6755399441055744,-52] ∧
    conversionDouble = [0,1125899906842624,-1074] ∧
    conversionSingle = [0,1125899906842625,-1074] := by decide +kernel

/-- Print seven examples and fail if compiled execution disagrees with their assertions. -/
def run : IO Unit := do
  IO.println "1. Exact arithmetic: binary32 1.5 + 2.25 = 3.75."
  IO.println s!"   Result word: {sumBits} (expected 0x40700000 = 1081081856)."
  unless sumBits == 0x40700000 do throw (IO.userError "exact addition failed")
  IO.println "2. Rounding 1.125 with three bits: rows are [sign, mantissa, exponent]."
  IO.println "   Value = (-1)^sign * mantissa * 2^exponent. Modes: NE, ZR, DN, UP, NA."
  IO.println s!"   Positive: {modes false}; negative: {modes true}."
  unless modes false == [[0,4,-2], [0,4,-2], [0,4,-2], [0,5,-2], [0,5,-2]] &&
      modes true == [[1,4,-2], [1,4,-2], [1,5,-2], [1,4,-2], [1,5,-2]] do
    throw (IO.userError "rounding table failed")
  IO.println "3. Double rounding: 73/64 directly to three bits is 1.25; via four bits it is 1."
  IO.println s!"   Direct: {direct}; via four: {viaFour}."
  unless direct == [0,5,-2] && viaFour == [0,4,-2] do
    throw (IO.userError "double rounding witness failed")
  IO.println "4. +0 and -0 compare equal; NaN is unordered; successor of negative tiniest is -0."
  IO.println s!"   Zero comparison: {repr zeroComparison}; NaN: {repr nanComparison}."
  IO.println s!"   Boolean [=, <, <=] for +0 versus [-0, NaN]: {booleanComparison}."
  IO.println s!"   Successor word: {negativeTinySuccessor} (negative zero)."
  unless zeroComparison == some .eq && nanComparison == none &&
      negativeTinySuccessor == 0x8000000000000000 &&
      booleanComparison == [[true, false, true], [false, false, false]] do
    throw (IO.userError "special values failed")
  IO.println "5. Same real value does not mean canonical representation."
  IO.println s!"   (mantissa 1, exponent 0) versus (4, -2): validity = {rawValidity}."
  unless rawValidity == [false, true] do throw (IO.userError "raw validity failed")
  IO.println "6. Signed shifting is not floor division: shift(-1) = 0, but (-1)/2 = -1."
  IO.println s!"   [source shift, floor division] = {signedShiftAndFloor}."
  IO.println s!"   Saved raw-rounding counterexample now returns negative zero: {rawRoundIsNegativeZero}."
  IO.println "   Negative raw mantissas are outside the value theorem; the total API still follows Flocq."
  unless signedShiftAndFloor == [0, -1] && rawRoundIsNegativeZero do
    throw (IO.userError "signed raw rounding regression failed")
  IO.println "7. Numeric conversion is not validation: raw (3, -1) converts to canonical 1.5."
  IO.println s!"   Converted [sign, mantissa, exponent]: {numericConversion}."
  IO.println "   Conversion rounds the integer first, then scales; one-shot rounding can differ."
  IO.println s!"   (2^53+5)*2^-1077 converted: {conversionDouble}; one shot: {conversionSingle}."
  unless numericConversion == [0,6755399441055744,-52] &&
      conversionDouble == [0,1125899906842624,-1074] &&
      conversionSingle == [0,1125899906842625,-1074] do
    throw (IO.userError "numeric primitive conversion failed")
  IO.println "PASS: all seven compiled examples agree with their finite kernel assertions."

end GuidedDemo

def main : IO Unit := GuidedDemo.run
