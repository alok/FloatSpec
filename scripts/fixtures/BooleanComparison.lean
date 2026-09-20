import FloatSpec.src.IEEE754.BinarySingleNaN

/-! Finite kernel and compiled checks of the actual public Boolean APIs.
The table has independent literal expectations, mirrored in the Rocq fixture.
Invalid raw finite encodings are deliberately converted to NaN by SF2B'. -/

namespace BooleanComparison

private def observe {prec emax : Int}
    (x y : BinarySingleNaN.binary_float prec emax) : List Bool :=
  [BinarySingleNaN.Beqb x y, BinarySingleNaN.Bltb x y, BinarySingleNaN.Bleb x y]

private def finite (sign : Bool) (mantissa : Nat) (exponent : Int) :
    BinarySingleNaN.binary_float 3 4 :=
  BinarySingleNaN.SF2B' (.S754_finite sign mantissa exponent)

private def table : List (List Bool) :=
  [observe (prec := 0) (emax := -1) (.B754_zero false) (.B754_zero true),
   observe (prec := 3) (emax := 4) .B754_nan .B754_nan,
   observe (prec := 3) (emax := 4) (.B754_infinity false) (.B754_infinity false),
   observe (prec := 1) (emax := 1) (.B754_infinity true) (.B754_infinity false),
   observe (finite true 4 (-1)) (finite true 4 (-2)),
   observe (finite false 3 (-4)) (finite false 4 (-4)),
   observe (finite true 3 (-4)) (finite true 4 (-4)),
   observe (finite false 1 0) (finite false 4 (-2))]

private def expected : List (List Bool) :=
  [[true, false, true], [false, false, false], [true, false, true],
   [false, true, true], [false, true, true], [false, true, true],
   [false, false, false], [false, false, false]]

example : table = expected := by decide +kernel

private def check : IO Unit := do
  unless table == expected do
    throw (IO.userError s!"Boolean comparison mismatch: {table}")
  IO.println "PASS: eight Boolean comparison boundaries (compiled and kernel-checked)."

#eval check

#print axioms Beqb_correct
#print axioms Bltb_correct
#print axioms Bleb_correct
#print axioms Beqb_refl

end BooleanComparison
