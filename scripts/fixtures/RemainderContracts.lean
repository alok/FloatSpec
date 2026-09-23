import FloatSpec.src.Prop.Div_sqrt_error

/-! Source contracts for exact remainders, including the small-quotient premise. -/

namespace FloatSpec.Test.RemainderContracts

open FloatSpec.Core

variable (beta : Int) [ValidRadix beta] (fexp : Int → Int)
variable [Generic_fmt.Valid_exp fexp] [Generic_fmt.Monotone_exp fexp]

#check (_root_.format_REM_aux (beta := beta) (fexp := fexp) :
  ∀ (rnd : Real → Int) [Generic_fmt.Valid_rnd rnd] (x y : Real), 1 < beta →
    Generic_fmt.generic_format beta fexp x → Generic_fmt.generic_format beta fexp y →
    0 ≤ x → 0 < y →
    ((0 < x / y ∧ x / y < (1 / 2 : Real)) → rnd (x / y) = 0) →
    Generic_fmt.generic_format beta fexp (x - (rnd (x / y) : Real) * y))

#check (_root_.format_REM (beta := beta) (fexp := fexp) :
  ∀ (rnd : Real → Int) [Generic_fmt.Valid_rnd rnd] (x y : Real), 1 < beta →
    (|x / y| < (1 / 2 : Real) → rnd (x / y) = 0) →
    Generic_fmt.generic_format beta fexp x → Generic_fmt.generic_format beta fexp y →
    Generic_fmt.generic_format beta fexp (x - (rnd (x / y) : Real) * y))

#check (_root_.format_REM_ZR (beta := beta) (fexp := fexp) :
  ∀ x y : Real, 1 < beta →
    Generic_fmt.generic_format beta fexp x → Generic_fmt.generic_format beta fexp y →
    Generic_fmt.generic_format beta fexp (x - (Raux.Ztrunc (x / y) : Real) * y))

#check (_root_.format_REM_N (beta := beta) (fexp := fexp) :
  ∀ (choice : Int → Bool) (x y : Real), 1 < beta →
    Generic_fmt.generic_format beta fexp x → Generic_fmt.generic_format beta fexp y →
    Generic_fmt.generic_format beta fexp (x - (Generic_fmt.Znearest choice (x / y) : Real) * y))

/-- Seven lies in the binade from four inclusive to eight exclusive. -/
theorem magnitude_minus_seven : Raux.mag 2 (-7 : Real) = 3 :=
  Raux.mag_unique 2 (-7) 3 (by decide) (by norm_num) (by norm_num)

#print axioms magnitude_minus_seven

/-- Two-bit precision cannot represent minus seven. -/
theorem minus_seven_not_format :
    ¬ Generic_fmt.generic_format 2 (FLX.FLX_exp 2) (-7 : Real) := by
  norm_num [Generic_fmt.generic_format, Generic_fmt.scaled_mantissa, Generic_fmt.cexp,
    FLX.FLX_exp, magnitude_minus_seven, Raux.Ztrunc, Raux.Zfloor, Raux.Zceil]

#print axioms minus_seven_not_format

/-- Every power of two is representable at two-bit precision. -/
theorem powers_are_representable (exponent : Int) :
    Generic_fmt.generic_format 2 (FLX.FLX_exp 2) ((2 : Real) ^ exponent) := by
  exact Generic_fmt.generic_format_bpow 2 (FLX.FLX_exp 2) exponent
    (by norm_num [FLX.FLX_exp])

#print axioms powers_are_representable

/-- Rounding upward is a valid integer mode but cannot replace the small-input premise.
The concrete witnesses are x = 1 and y = 8, whose upward-quotient remainder is -7. -/
theorem ceiling_does_not_preserve_remainder_format :
    ¬ ∀ x y : Real, Generic_fmt.generic_format 2 (FLX.FLX_exp 2) x →
      Generic_fmt.generic_format 2 (FLX.FLX_exp 2) y →
      Generic_fmt.generic_format 2 (FLX.FLX_exp 2)
        (x - (Raux.Zceil (x / y) : Real) * y) := by
  intro claimed
  have hx : Generic_fmt.generic_format 2 (FLX.FLX_exp 2) (1 : Real) := by
    simpa using powers_are_representable 0
  have hy : Generic_fmt.generic_format 2 (FLX.FLX_exp 2) (8 : Real) := by
    convert powers_are_representable 3 using 1
    norm_num
  have remainder := claimed 1 8 hx hy
  norm_num [Raux.Zceil] at remainder
  exact minus_seven_not_format remainder

#print axioms ceiling_does_not_preserve_remainder_format
#print axioms _root_.format_REM_aux
#print axioms _root_.format_REM
#print axioms _root_.format_REM_ZR
#print axioms _root_.format_REM_N

end FloatSpec.Test.RemainderContracts
