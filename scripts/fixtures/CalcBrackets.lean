import FloatSpec.src.Calc.Div
import FloatSpec.src.Calc.Sqrt

/-! Independent integer inequalities for the exact rational brackets returned
by Calc. No rounding theorem, real-valued oracle, or second divider/square-root
implementation supplies the expected answers. -/

namespace CalcBrackets

open FloatSpec.Calc.Bracket

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

private def matchesLocation (lowerEqual : Bool) (midpoint : Ordering) : Location → Bool
  | .loc_Exact => lowerEqual
  | .loc_Inexact position => !lowerEqual && position == midpoint

private def divisionLaw (beta m1 e1 m2 e2 target : Int) : Bool :=
  let (q, location) := FloatSpec.Calc.Div.Fdiv_core beta m1 e1 m2 e2 target
  let common := min e1 (e2 + target)
  let numerator := m1 * beta ^ (e1 - common).toNat
  let denominator := m2 * beta ^ (e2 + target - common).toNat
  decide (q * denominator ≤ numerator ∧ numerator < (q + 1) * denominator) &&
    matchesLocation (numerator == q * denominator)
      (Ord.compare (2 * numerator) ((2 * q + 1) * denominator)) location

private def sqrtLaw (beta mantissa exponent target : Int) : Bool :=
  let (q, location) := FloatSpec.Calc.Sqrt.Fsqrt_core beta mantissa exponent target
  let common := min exponent (2 * target)
  let numerator := mantissa * beta ^ (exponent - common).toNat
  let denominator := beta ^ (2 * target - common).toNat
  decide (0 ≤ q ∧ q * q * denominator ≤ numerator ∧
    numerator < (q + 1) * (q + 1) * denominator) &&
    matchesLocation (numerator == q * q * denominator)
      (Ord.compare (4 * numerator) ((2 * q + 1) * (2 * q + 1) * denominator)) location

private def divisionChecks : List Bool :=
  [2, 3, 10].flatMap fun beta =>
    (List.range 8).flatMap fun left => (List.range 8).flatMap fun right =>
      [-1, 0, 1].flatMap fun leftExponent => [-1, 0, 1].flatMap fun rightExponent =>
        [-2, -1, 0, 1, 2].map fun target =>
          divisionLaw beta (left + 1) leftExponent (right + 1) rightExponent target

private def sqrtChecks : List Bool :=
  [2, 3, 10].flatMap fun beta => (List.range 32).flatMap fun mantissa =>
    [-3, -2, -1, 0, 1, 2, 3].flatMap fun exponent =>
      ([-3, -2, -1, 0, 1, 2, 3].filter fun target => 2 * target ≤ exponent).map fun target =>
        sqrtLaw beta (mantissa + 1) exponent target

example : divisionLaw 2 1 0 3 0 0 = true := by decide +kernel
example : divisionChecks.length = 8640 ∧ divisionChecks.all id = true := by decide +kernel
example : sqrtLaw 2 2 0 0 = true := by decide +kernel
example : sqrtChecks.length = 2496 ∧ sqrtChecks.all id = true := by decide +kernel

-- The exponent precondition cannot be discarded. Scaling by a negative
-- integer power here zeroes the raw radicand; the returned zero is not sqrt(9).
example : FloatSpec.Calc.Sqrt.Fsqrt_core 2 9 0 1 = (0, .loc_Exact) ∧
    sqrtLaw 2 9 0 1 = false := by decide +kernel

-- The same quotient at two output scales illustrates both division branches.
example : FloatSpec.Calc.Div.Fdiv_core 2 7 0 3 0 (-1) = (4, .loc_Inexact .gt) ∧
    FloatSpec.Calc.Div.Fdiv_core 2 7 0 3 0 1 = (1, .loc_Inexact .lt) := by decide +kernel

#eval do
  unless divisionChecks.length == 8640 && divisionChecks.all id &&
      sqrtChecks.length == 2496 && sqrtChecks.all id &&
      !sqrtLaw 2 9 0 1 do
    throw (IO.userError "independent Calc bracket law failed")
  IO.println s!"PASS: {divisionChecks.length} division brackets, {sqrtChecks.length} square-root brackets, and a required-exponent-premise counterexample."

end CalcBrackets
