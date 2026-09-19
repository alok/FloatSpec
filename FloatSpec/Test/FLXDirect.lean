import FloatSpec.src.Core.FLX

/-! Regression examples for the direct fixed-precision format interface. -/

namespace FloatSpec.Test.FLXDirect

open FloatSpec.Core.FLX

example (prec beta : Int) [ValidRadix beta] (x : ℝ)
    (hx : FLX_format prec beta x) :
    FloatSpec.Core.Generic_fmt.generic_format beta (FLX_exp prec) x :=
  generic_format_FLX (prec := prec) beta x hx

example (prec beta : Int) [ValidRadix beta] [Prec_gt_0 prec] (x : ℝ)
    (hx : FloatSpec.Core.Generic_fmt.generic_format beta (FLX_exp prec) x) :
    FLX_format prec beta x :=
  FLX_format_generic (prec := prec) beta x hx

end FloatSpec.Test.FLXDirect
