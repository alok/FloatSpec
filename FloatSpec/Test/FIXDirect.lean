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

example (emin beta mantissa : Int) [ValidRadix beta] :
    FIX_format emin beta
      (FloatSpec.Core.Defs.F2R
        (FloatSpec.Core.Defs.FlocqFloat.mk mantissa emin :
          FloatSpec.Core.Defs.FlocqFloat beta)) :=
  ⟨⟨mantissa, emin⟩, rfl, rfl⟩

example (emin beta : Int) [ValidRadix beta] (x : ℝ)
    (hx : FIX_format emin beta x) :
    FloatSpec.Core.Generic_fmt.generic_format beta (FIX_exp emin) x :=
  generic_format_FIX (emin := emin) beta x hx

example (emin beta : Int) [ValidRadix beta] (x : ℝ)
    (hx : FloatSpec.Core.Generic_fmt.generic_format beta (FIX_exp emin) x) :
    FIX_format emin beta x :=
  FIX_format_generic (emin := emin) beta x hx

example (f : ℝ → Int) [FloatSpec.Core.Generic_fmt.Valid_rnd f] (x : ℝ) :
    FloatSpec.Core.Generic_fmt.round_to_generic (beta := 2)
      (fexp := FIX_exp (emin := (0 : Int))) (mode := f) x = (f x : ℝ) :=
  round_FIX_IZR f x

end FloatSpec.Test.FIXDirect
