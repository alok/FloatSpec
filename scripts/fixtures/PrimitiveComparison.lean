import FloatSpec.src.IEEE754.PrimFloat

/-! Raw encoding order is not arbitrary dyadic value order. These literal
observations keep raw, primitive-model, and proof-carrying APIs distinct.
Rocq's raw carrier has positive mantissas; no zero-mantissa extension is tested. -/

namespace PrimitiveComparison
private def ordering : Option Ordering → Int
  | none => 2 | some .lt => -1 | some .eq => 0 | some .gt => 1
private def boolean (b : Bool) : Int := if b then 1 else 0
private def primitiveOrdering : FaithfulPrimFloat.float_comparison → Int
  | .FNotComparable => 2 | .FLt => -1 | .FEq => 0 | .FGt => 1

private def inputs : List (StandardFloat × StandardFloat) :=
  [(.S754_finite false 3 (-1), .S754_finite false 6 (-2)),
   (.S754_finite false 6 (-2), .S754_finite false 3 (-1)),
   (.S754_finite true 3 (-1), .S754_finite true 6 (-2)),
   (.S754_finite false 1 (1), .S754_finite false 16 (0)),
   (.S754_finite false 4503599627370496 (-52), .S754_finite false 4503599627370496 (-51)),
   (.S754_finite false 4503599627370496 (-51), .S754_finite false 4503599627370496 (-52)),
   (.S754_finite false 4503599627370496 (-52), .S754_finite false 4503599627370496 (-52)),
   (.S754_finite true 4503599627370496 (-52), .S754_finite false 4503599627370496 (-52)),
   (.S754_zero false, .S754_zero true),
   (.S754_zero true, .S754_zero false),
   (.S754_nan, .S754_zero false),
   (.S754_finite false 4503599627370496 (-52), .S754_nan),
   (.S754_nan, .S754_nan),
   (.S754_infinity true, .S754_infinity false),
   (.S754_infinity false, .S754_infinity true),
   (.S754_infinity false, .S754_infinity false),
   (.S754_infinity true, .S754_finite false 4503599627370496 (-52)),
   (.S754_finite false 4503599627370496 (-52), .S754_infinity false),
   (.S754_finite false 1 (-1074), .S754_zero false),
   (.S754_finite true 1 (-1074), .S754_zero true),
   (.S754_finite false 4503599627370495 (-1074), .S754_finite false 4503599627370496 (-1074)),
   (.S754_finite false 9007199254740991 (971), .S754_infinity false),
   (.S754_finite false 1 (-1000000), .S754_finite false 1 (1000000)),
   (.S754_finite false 1 (-1075), .S754_finite false 1 (-1074))]

private def observe (rawX rawY : StandardFloat) : List Int :=
  let x := BinarySingleNaN.SF2B' (prec := 53) (emax := 1024) rawX
  let y := BinarySingleNaN.SF2B' (prec := 53) (emax := 1024) rawY
  let px := FaithfulPrimFloat.B2Prim x
  let py := FaithfulPrimFloat.B2Prim y
  [ordering (FaithfulPrimFloat.SFcompare rawX rawY),
   boolean (FaithfulPrimFloat.SFeqb rawX rawY),
   boolean (FaithfulPrimFloat.SFltb rawX rawY),
   boolean (FaithfulPrimFloat.SFleb rawX rawY),
   boolean (validBinarySingleNaNStandardFloat (prec := 53) (emax := 1024) rawX),
   boolean (validBinarySingleNaNStandardFloat (prec := 53) (emax := 1024) rawY),
   primitiveOrdering (FaithfulPrimFloat.compare px py),
   boolean (FaithfulPrimFloat.eqb px py),
   boolean (FaithfulPrimFloat.ltb px py),
   boolean (FaithfulPrimFloat.leb px py),
   ordering (FaithfulPrimFloat.Bcompare x y),
   boolean (FaithfulPrimFloat.Beqb x y),
   boolean (FaithfulPrimFloat.Bltb x y),
   boolean (FaithfulPrimFloat.Bleb x y)]

private def expected : List (List Int) :=
  [[1, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0],
   [-1, 0, 1, 1, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0],
   [-1, 0, 1, 1, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0],
   [1, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0],
   [-1, 0, 1, 1, 1, 1, -1, 0, 1, 1, -1, 0, 1, 1],
   [1, 0, 0, 0, 1, 1, 1, 0, 0, 0, 1, 0, 0, 0],
   [0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1],
   [-1, 0, 1, 1, 1, 1, -1, 0, 1, 1, -1, 0, 1, 1],
   [0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1],
   [0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1],
   [2, 0, 0, 0, 1, 1, 2, 0, 0, 0, 2, 0, 0, 0],
   [2, 0, 0, 0, 1, 1, 2, 0, 0, 0, 2, 0, 0, 0],
   [2, 0, 0, 0, 1, 1, 2, 0, 0, 0, 2, 0, 0, 0],
   [-1, 0, 1, 1, 1, 1, -1, 0, 1, 1, -1, 0, 1, 1],
   [1, 0, 0, 0, 1, 1, 1, 0, 0, 0, 1, 0, 0, 0],
   [0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1],
   [-1, 0, 1, 1, 1, 1, -1, 0, 1, 1, -1, 0, 1, 1],
   [-1, 0, 1, 1, 1, 1, -1, 0, 1, 1, -1, 0, 1, 1],
   [1, 0, 0, 0, 1, 1, 1, 0, 0, 0, 1, 0, 0, 0],
   [-1, 0, 1, 1, 1, 1, -1, 0, 1, 1, -1, 0, 1, 1],
   [-1, 0, 1, 1, 1, 1, -1, 0, 1, 1, -1, 0, 1, 1],
   [-1, 0, 1, 1, 1, 1, -1, 0, 1, 1, -1, 0, 1, 1],
   [-1, 0, 1, 1, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0],
   [-1, 0, 1, 1, 0, 1, 2, 0, 0, 0, 2, 0, 0, 0]]

private theorem literalObservations :
    inputs.map (fun (x, y) => observe x y) = expected := by decide +kernel

-- Equal real values do not license replacing Rocq's total raw comparator.
private theorem equalValues :
    SF2R 2 (.S754_finite false 3 (-1)) =
      SF2R 2 (.S754_finite false 6 (-2)) := by
  norm_num [SF2R, F2R, FloatSpec.Core.Defs.F2R]

private theorem differentRawComparison :
    FaithfulPrimFloat.SFcompare (.S754_finite false 3 (-1))
      (.S754_finite false 6 (-2)) = some .gt := by decide +kernel

#eval do
  unless decide (inputs.map (fun (x, y) => observe x y) = expected) do
    throw (IO.userError "raw/primitive/validated comparison regression")
  IO.println "PASS: 24 literal comparison cases, 12 independently called APIs, and observed validity."

end PrimitiveComparison
