import FloatSpec.src.Core.Ulp

namespace FloatSpec.Test.ExponentValidityBoundary

open FloatSpec.Core.Generic_fmt FloatSpec.Core.Ulp
open Std.Do

/-- An exponent function whose available precision alternates with the binade. -/
def zigzag (exponent : Int) : Int :=
  if exponent % 2 = 0 then exponent - 1 else exponent - 3

/-- Validity constrains transitions, but does not require monotonicity. -/
instance zigzag_valid : Valid_exp zigzag where
  valid_exp exponent := by
    constructor
    · intro _
      unfold zigzag
      split_ifs <;> grind
    · intro impossible
      unfold zigzag at impossible
      split_ifs at impossible <;> grind

#print axioms zigzag_valid

/-- The first two binades already witness failure of exponent monotonicity. -/
theorem zigzag_not_monotone : ¬ FloatSpec.Core.Generic_fmt.Monotone_exp zigzag := by
  intro monotone
  have contradiction := monotone.mono (a := 0) (b := 1) (by decide)
  norm_num [zigzag] at contradiction

#print axioms zigzag_not_monotone

/-- Every power of two is representable, including both witness values below. -/
theorem zigzag_contains_powers (exponent : Int) :
    generic_format 2 zigzag ((2 : Real) ^ exponent) := by
  have bounds : (1 : Int) < 2 ∧ zigzag (exponent + 1) ≤ exponent := by
    constructor
    · decide
    · unfold zigzag
      split_ifs <;> grind
  simpa [wp, PostCond.noThrow, Id.run, bind, pure] using
    generic_format_bpow 2 zigzag exponent bounds

#print axioms zigzag_contains_powers

/-- The spacing below one is a half in this valid format. -/
theorem zigzag_ulp_half : ulp 2 zigzag (1 / 2 : Real) = (1 / 2 : Real) := by
  have power := ulp_bpow (beta := 2) (fexp := zigzag) (e := -1)
    (show (1 : Int) < 2 from by decide)
  simpa [wp, PostCond.noThrow, Id.run, bind, pure, zigzag] using power

#print axioms zigzag_ulp_half

/-- The next binade has finer spacing, despite format validity. -/
theorem zigzag_ulp_one : ulp 2 zigzag (1 : Real) = (1 / 4 : Real) := by
  have power := ulp_bpow (beta := 2) (fexp := zigzag) (e := 0)
    (show (1 : Int) < 2 from by decide)
  norm_num [wp, PostCond.noThrow, Id.run, bind, pure, zigzag] at power ⊢
  exact power

#print axioms zigzag_ulp_one

/-- Removing the monotone-exponent hypothesis would make the ULP law false. -/
theorem valid_format_can_have_decreasing_ulp :
    (0 : Real) ≤ 1 / 2 ∧ (1 / 2 : Real) ≤ 1 ∧
    ulp 2 zigzag (1 : Real) < ulp 2 zigzag (1 / 2 : Real) := by
  rw [zigzag_ulp_one, zigzag_ulp_half]
  norm_num

#print axioms valid_format_can_have_decreasing_ulp

end FloatSpec.Test.ExponentValidityBoundary
