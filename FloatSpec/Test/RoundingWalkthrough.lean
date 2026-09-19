import FloatSpec.src.IEEE754.Bits

/-! The reading guide's executable three-bit rounding example. A row contains
sign (0 positive, 1 negative), mantissa, and exponent. The five rows are ordered
nearest-even, toward-zero, downward, upward, nearest-away. -/

namespace FloatSpec.Test.RoundingWalkthrough

/-- Round the exact magnitude 9 times 2 to the power -3, using three-bit precision. -/
def halfway (mode : RoundingMode) (sign : Bool) : List Int :=
  match binary_round (prec := 3) (emax := 4) mode sign 9 (-3) with
  | .S754_finite s mantissa exponent => [if s then 1 else 0, mantissa, exponent]
  | _ => []

/-- Observe the same input under every source rounding mode. -/
def table (sign : Bool) : List (List Int) :=
  [.RNE, .RTZ, .RTN, .RTP, .RNA].map (fun mode => halfway mode sign)

/-- At positive and negative halfway points, direction and tie policy matter. -/
theorem halfway_all_modes :
    table false = [[0,4,-2], [0,4,-2], [0,4,-2], [0,5,-2], [0,5,-2]] ∧
    table true = [[1,4,-2], [1,4,-2], [1,5,-2], [1,4,-2], [1,5,-2]] := by
  decide +kernel

#eval table false
#eval table true

end FloatSpec.Test.RoundingWalkthrough
