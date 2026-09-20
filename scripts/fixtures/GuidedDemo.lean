import FloatSpec.src.IEEE754.Bits

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

private def negativeTinySuccessor : Nat :=
  (bits_of_b64 (b64_succ (b64_of_bits 0x8000000000000001))).toNat

example : zeroComparison = some .eq ∧ nanComparison = none ∧
    negativeTinySuccessor = 0x8000000000000000 := by decide +kernel

private def rawValidity : List Bool :=
  [valid_binary_SF (prec := 3) (emax := 4) (.S754_finite false 1 0),
   valid_binary_SF (prec := 3) (emax := 4) (.S754_finite false 4 (-2))]

example : rawValidity = [false, true] := by decide +kernel

/-- Print five examples and fail if compiled execution disagrees with their assertions. -/
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
  IO.println s!"   Successor word: {negativeTinySuccessor} (negative zero)."
  unless zeroComparison == some .eq && nanComparison == none &&
      negativeTinySuccessor == 0x8000000000000000 do
    throw (IO.userError "special values failed")
  IO.println "5. Same real value does not mean canonical representation."
  IO.println s!"   (mantissa 1, exponent 0) versus (4, -2): validity = {rawValidity}."
  unless rawValidity == [false, true] do throw (IO.userError "raw validity failed")
  IO.println "PASS: all five compiled examples agree with their finite kernel assertions."

end GuidedDemo

def main : IO Unit := GuidedDemo.run
