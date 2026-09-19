import FloatSpec.src.Core.FIX

/-! Regression examples for the direct fixed-point format interface. -/

namespace FloatSpec.Test.FIXDirect

open FloatSpec.Core.FIX

example (emin exponent : Int) : FIX_exp emin exponent = emin :=
  FIX_exp_spec (emin := emin) exponent

example (emin beta : Int) [ValidRadix beta] : FIX_format emin beta 0 :=
  FIX_format_zero (emin := emin) beta

example (emin beta : Int) [ValidRadix beta] (x : ℝ)
    (hx : FIX_format emin beta x) : FIX_format emin beta (-x) :=
  FIX_format_neg (emin := emin) beta x hx

example (f : ℝ → Int) [FloatSpec.Core.Generic_fmt.Valid_rnd f] (x : ℝ) :
    FloatSpec.Core.Generic_fmt.round_to_generic (beta := 2)
      (fexp := FIX_exp (emin := (0 : Int))) (mode := f) x = (f x : ℝ) :=
  round_FIX_IZR f x

end FloatSpec.Test.FIXDirect
