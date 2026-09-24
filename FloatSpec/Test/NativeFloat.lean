import FloatSpec.src.IEEE754.NativeFloat

/-! Regression checks for `FloatSpec.IEEE754.NativeFloat`: Flocq's correctness
theorems restated for Lean's native `Float` and `Float32` operators.

The `#check` commands record the exact statements and the `#print axioms`
commands record that each headline theorem depends only on `propext`,
`Classical.choice` and `Quot.sound`. The examples evaluate native floats in the
kernel (`decide +kernel`) and apply the theorems to concrete and symbolic
inputs. -/

namespace FloatSpec.Test.NativeFloat

open FloatSpec.IEEE754.BinarySingleNaN.Source (mode round_mode)

section Float64

open FloatSpec.IEEE754.NativeFloat

/-! ## binary64 statements -/

#check @add_correct
#check @sub_correct
#check @mul_correct
#check @div_correct
#check @sqrt_correct
#check @add_eq_round
#check @sub_eq_round
#check @mul_eq_round
#check @div_eq_round
#check @sqrt_eq_round
#check @add_standard_model
#check @sub_standard_model
#check @mul_standard_model
#check @div_standard_model
#check @sqrt_standard_model
#check @round_standard_model
#check @round_abs_lt_of_abs_le
#check @sqrt_isFinite_of_nonneg
#check @isFinite_eq
#check @isNaN_eq
#check @toBinary_eq_Prim2B

#print axioms add_correct
#print axioms sub_correct
#print axioms mul_correct
#print axioms div_correct
#print axioms sqrt_correct
#print axioms add_eq_round
#print axioms sub_eq_round
#print axioms mul_eq_round
#print axioms div_eq_round
#print axioms sqrt_eq_round
#print axioms add_standard_model
#print axioms sub_standard_model
#print axioms mul_standard_model
#print axioms div_standard_model
#print axioms sqrt_standard_model
#print axioms round_standard_model
#print axioms round_abs_lt_of_abs_le
#print axioms sqrt_isFinite_of_nonneg
#print axioms binaryEquiv
#print axioms toBinary_eq_Prim2B

/-! ## binary64 values, evaluated by the kernel -/

theorem toStandardFloat_one : toStandardFloat (1.0 : Float) =
    .S754_finite false 4503599627370496 (-52) := by
  decide +kernel

theorem toStandardFloat_tenth : toStandardFloat (0.1 : Float) =
    .S754_finite false 7205759403792794 (-56) := by
  decide +kernel

theorem toStandardFloat_fifth : toStandardFloat (0.2 : Float) =
    .S754_finite false 7205759403792794 (-55) := by
  decide +kernel

/-- `0.1 + 0.2` is `5404319552844596 * 2 ^ (-54)`, that is
`0.30000000000000004`, not the binary64 value of `0.3`. -/
theorem toStandardFloat_tenth_add_fifth : toStandardFloat ((0.1 : Float) + 0.2) =
    .S754_finite false 5404319552844596 (-54) := by
  decide +kernel

example : (0.1 : Float) + 0.2 ≠ 0.3 := by
  decide +kernel

example : toStandardFloat (Float.sqrt 2.0) =
    .S754_finite false 6369051672525773 (-52) := by
  decide +kernel

example : toReal (1.0 : Float) = 1 := by
  rw [toReal_eq_SF2R, toStandardFloat_one]
  norm_num [SF2R, FloatSpec.Core.Defs.F2R]

theorem toReal_tenth : toReal (0.1 : Float) = 7205759403792794 * 2 ^ (-56 : ℤ) := by
  rw [toReal_eq_SF2R, toStandardFloat_tenth]
  norm_num [SF2R, FloatSpec.Core.Defs.F2R]

theorem toReal_fifth : toReal (0.2 : Float) = 7205759403792794 * 2 ^ (-55 : ℤ) := by
  rw [toReal_eq_SF2R, toStandardFloat_fifth]
  norm_num [SF2R, FloatSpec.Core.Defs.F2R]

/-- The concrete sum `0.1 + 0.2` is the correctly rounded sum of the binary64
values of its operands. Finiteness comes from the kernel; the no-overflow
hypothesis from `round_abs_lt_of_abs_le`. -/
example : toReal ((0.1 : Float) + 0.2) =
    FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp (-1074) 53) (round_mode .mode_NE)
      (toReal 0.1 + toReal 0.2) := by
  refine (add_eq_round 0.1 0.2 (by decide +kernel) (by decide +kernel)
    (round_abs_lt_of_abs_le ?_)).1
  rw [toReal_tenth, toReal_fifth]
  calc |7205759403792794 * 2 ^ (-56 : ℤ) + 7205759403792794 * 2 ^ (-55 : ℤ)| ≤ (1 : ℝ) := by
        norm_num
    _ ≤ (2 ^ 53 - 1) * 2 ^ (971 : ℤ) :=
        one_le_mul_of_one_le_of_one_le (by norm_num) (one_le_zpow₀ (by norm_num) (by norm_num))

/-! ## binary64 theorems applied to symbolic inputs -/

/-- The absolute error of a native addition that does not overflow. -/
example (x y : Float) (hx : x.isFinite = true) (hy : y.isFinite = true)
    (h : |toReal x + toReal y| ≤ (2 ^ 53 - 1) * 2 ^ (971 : ℤ)) :
    |toReal (x + y) - (toReal x + toReal y)| ≤
      2 ^ (-53 : ℤ) * |toReal x + toReal y| + 2 ^ (-1075 : ℤ) := by
  obtain ⟨ε, η, hε, hη, -, heq⟩ := add_standard_model x y hx hy (round_abs_lt_of_abs_le h)
  rw [heq]
  calc |(toReal x + toReal y) * (1 + ε) + η - (toReal x + toReal y)|
      = |(toReal x + toReal y) * ε + η| := by ring_nf
    _ ≤ |(toReal x + toReal y) * ε| + |η| := abs_add_le _ _
    _ = |toReal x + toReal y| * |ε| + |η| := by rw [abs_mul]
    _ ≤ |toReal x + toReal y| * 2 ^ (-53 : ℤ) + 2 ^ (-1075 : ℤ) := by gcongr
    _ = 2 ^ (-53 : ℤ) * |toReal x + toReal y| + 2 ^ (-1075 : ℤ) := by ring

/-- A product of finite floats that does not overflow is finite. -/
example (x y : Float) (hx : x.isFinite = true) (hy : y.isFinite = true)
    (h : |toReal x * toReal y| ≤ (2 ^ 53 - 1) * 2 ^ (971 : ℤ)) :
    (x * y).isFinite = true := by
  rw [(mul_eq_round x y (round_abs_lt_of_abs_le h)).2, hx, hy]
  rfl

/-- Division by a nonzero float: the quotient is correctly rounded. -/
example (x y : Float) (hy : toReal y ≠ 0)
    (h : |toReal x / toReal y| ≤ (2 ^ 53 - 1) * 2 ^ (971 : ℤ)) :
    toReal (x / y) =
      FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp (-1074) 53) (round_mode .mode_NE)
        (toReal x / toReal y) :=
  (div_eq_round x y hy (round_abs_lt_of_abs_le h)).1

/-- The square root of a finite nonnegative float is finite and correctly
rounded. -/
example (x : Float) (hx : x.isFinite = true) (h0 : 0 ≤ toReal x) :
    x.sqrt.isFinite = true ∧
      toReal x.sqrt =
        FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp (-1074) 53) (round_mode .mode_NE)
          (Real.sqrt (toReal x)) :=
  ⟨sqrt_isFinite_of_nonneg x hx h0, sqrt_eq_round x⟩

/-- `toBinary` is a bijection onto Flocq's binary64 values. -/
example (x : Float) : ofBinary (toBinary x) = x := ofBinary_toBinary x

end Float64

section Float32

open FloatSpec.IEEE754.NativeFloat32

/-! ## binary32 statements -/

#check @add_correct
#check @sub_correct
#check @mul_correct
#check @div_correct
#check @sqrt_correct
#check @add_standard_model
#check @sub_standard_model
#check @mul_standard_model
#check @div_standard_model
#check @sqrt_standard_model
#check @round_abs_lt_of_abs_le

#print axioms add_correct
#print axioms sub_correct
#print axioms mul_correct
#print axioms div_correct
#print axioms sqrt_correct
#print axioms add_eq_round
#print axioms sub_eq_round
#print axioms mul_eq_round
#print axioms div_eq_round
#print axioms sqrt_eq_round
#print axioms add_standard_model
#print axioms sub_standard_model
#print axioms mul_standard_model
#print axioms div_standard_model
#print axioms sqrt_standard_model
#print axioms round_standard_model
#print axioms round_abs_lt_of_abs_le
#print axioms sqrt_isFinite_of_nonneg
#print axioms binaryEquiv

/-! ## binary32 values, evaluated by the kernel -/

theorem toStandardFloat32_one : toStandardFloat (1.0 : Float32) =
    .S754_finite false 8388608 (-23) := by
  decide +kernel

theorem toStandardFloat32_tenth : toStandardFloat (0.1 : Float32) =
    .S754_finite false 13421773 (-27) := by
  decide +kernel

example : toReal (1.0 : Float32) = 1 := by
  rw [toReal_eq_SF2R, toStandardFloat32_one]
  norm_num [SF2R, FloatSpec.Core.Defs.F2R]

/-- The standard model for a binary32 product that does not overflow. -/
example (x y : Float32) (h : |toReal x * toReal y| ≤ (2 ^ 24 - 1) * 2 ^ (104 : ℤ)) :
    ∃ ε η : ℝ, |ε| ≤ 2 ^ (-24 : ℤ) ∧ |η| ≤ 2 ^ (-150 : ℤ) ∧ ε * η = 0 ∧
      toReal (x * y) = (toReal x * toReal y) * (1 + ε) + η :=
  mul_standard_model x y (round_abs_lt_of_abs_le h)

end Float32

end FloatSpec.Test.NativeFloat
