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
  have bound : zigzag (exponent + 1) ≤ exponent := by
    unfold zigzag
    split_ifs <;> grind
  exact generic_format_bpow 2 zigzag exponent bound

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
    ¬ ∀ x y : Real, 0 ≤ x → x ≤ y → ulp 2 zigzag x ≤ ulp 2 zigzag y := by
  intro claimed
  have contradiction := claimed (1 / 2) 1 (by norm_num) (by norm_num)
  rw [zigzag_ulp_one, zigzag_ulp_half] at contradiction
  norm_num at contradiction

#print axioms valid_format_can_have_decreasing_ulp

/-- Seven quarters lies in the binade with finer spacing. -/
theorem zigzag_magnitude_seven_quarters :
    FloatSpec.Core.Raux.mag 2 (7 / 4 : Real) = 1 :=
  FloatSpec.Core.Raux.mag_unique 2 (7 / 4) 1
    (by decide) (by norm_num) (by norm_num)

#print axioms zigzag_magnitude_seven_quarters

/-- Three quarters falls back into the binade with coarser spacing. -/
theorem zigzag_magnitude_three_quarters :
    FloatSpec.Core.Raux.mag 2 (3 / 4 : Real) = 0 :=
  FloatSpec.Core.Raux.mag_unique 2 (3 / 4) 0
    (by decide) (by norm_num) (by norm_num)

#print axioms zigzag_magnitude_three_quarters

/-- Fine spacing above one admits seven quarters. -/
theorem zigzag_seven_quarters_representable :
    generic_format 2 zigzag (7 / 4 : Real) := by
  norm_num [generic_format, scaled_mantissa, cexp, zigzag,
    zigzag_magnitude_seven_quarters, FloatSpec.Core.Raux.Ztrunc,
    FloatSpec.Core.Raux.Zfloor, FloatSpec.Core.Raux.Zceil]

#print axioms zigzag_seven_quarters_representable

/-- Coarse spacing below one excludes three quarters. -/
theorem zigzag_three_quarters_not_representable :
    ¬ generic_format 2 zigzag (3 / 4 : Real) := by
  norm_num [generic_format, scaled_mantissa, cexp, zigzag,
    zigzag_magnitude_three_quarters, FloatSpec.Core.Raux.Ztrunc,
    FloatSpec.Core.Raux.Zfloor, FloatSpec.Core.Raux.Zceil]

#print axioms zigzag_three_quarters_not_representable

/-- Validity alone does not make even truncation remainders representable. -/
theorem truncation_remainder_needs_monotone_exponents :
    ¬ ∀ x y : Real, generic_format 2 zigzag x → generic_format 2 zigzag y →
      generic_format 2 zigzag (x - (FloatSpec.Core.Raux.Ztrunc (x / y) : Real) * y) := by
  intro claimed
  have hone : generic_format 2 zigzag (1 : Real) := by
    simpa using zigzag_contains_powers 0
  have remainder := claimed (7 / 4) 1 zigzag_seven_quarters_representable hone
  norm_num [FloatSpec.Core.Raux.Ztrunc, FloatSpec.Core.Raux.Zfloor,
    FloatSpec.Core.Raux.Zceil] at remainder
  exact zigzag_three_quarters_not_representable remainder

#print axioms truncation_remainder_needs_monotone_exponents

end FloatSpec.Test.ExponentValidityBoundary
