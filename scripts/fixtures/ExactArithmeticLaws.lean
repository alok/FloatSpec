import FloatSpec.src.IEEE754.Bits

/-! Finite arithmetic laws in a three-bit format, independently of Rocq.
Integer units are 2^-4. The positive finite values are the three subnormals
and the four normalized mantissas at each of six exponents. This enumeration
does not ask the rounding implementation which inputs should be valid. -/

namespace ExactArithmeticLaws

private def positiveUnits : List Int :=
  [1, 2, 3] ++ (List.range 6).flatMap fun shift =>
    [4, 5, 6, 7].map fun m => m * (2 : Int) ^ shift

private def finiteUnits : List Int :=
  positiveUnits.map (-·) ++ [0] ++ positiveUnits

private def units : StandardFloat → Option Int
  | .S754_zero _ => some 0
  | .S754_finite sign m e =>
      if -4 ≤ e then
        let magnitude : Int := m * (2 : Int) ^ (e + 4).toNat
        some (if sign then -magnitude else magnitude)
      else none
  | _ => none

private def rounded (mode : RoundingMode) (x : Int) : Option Int :=
  if x = 0 then some 0
  else units (binary_round (prec := 3) (emax := 4) mode (x < 0) x.natAbs (-4))

private def sterbenzPairs : List (Int × Int) :=
  (positiveUnits.product positiveUnits).filter fun (x, y) => x ≤ 2 * y && y ≤ 2 * x

private def additionPairs : List (Int × Int) :=
  (finiteUnits.product finiteUnits).filter fun (x, y) => (x + y).natAbs ≤ 224

private def additionError (mode : RoundingMode) (x y : Int) : Bool :=
  match rounded mode (x + y) with
  | none => false
  | some sum => rounded mode (sum - (x + y)) == some (sum - (x + y))

/-- Validate the independently enumerated input domain in all five modes. -/
theorem inputs_exact :
    ([RoundingMode.RNE, .RTZ, .RTN, .RTP, .RNA].all fun mode =>
      finiteUnits.all fun x => rounded mode x == some x) = true := by
  decide +kernel

/-- Sterbenz subtraction is exact for the finite pairs satisfying its ratio
premise, in every rounding mode; the range is small enough to avoid overflow. -/
theorem sterbenz_grid :
    ([RoundingMode.RNE, .RTZ, .RTN, .RTP, .RNA].all fun mode =>
      sterbenzPairs.all fun (x, y) => rounded mode (x - y) == some (x - y)) = true := by
  decide +kernel

/-- The nearest-rounded addition error is itself representable. Both tie
policies are checked, and exact sums outside the finite range are excluded. -/
theorem addition_error_grid :
    ([RoundingMode.RNE, .RNA].all fun mode =>
      additionPairs.all fun (x, y) => additionError mode x y) = true := by
  decide +kernel

/-- Without the factor-two premise, even positive representable operands
can have an inexact subtraction: 1 - 1/16 rounds from 15/16 to 1. -/
theorem sterbenz_premise_matters :
    rounded .RNE 16 = some 16 ∧ rounded .RNE 1 = some 1 ∧
    rounded .RNE (16 - 1) = some 16 ∧ ¬ (16 ≤ 2 * (1 : Int)) := by
  decide +kernel

#eval [finiteUnits.length, sterbenzPairs.length, additionPairs.length]

end ExactArithmeticLaws
