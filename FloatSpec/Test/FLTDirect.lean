import FloatSpec.src.Core.FLT

/-! Regression examples for the direct floating-point format interface. -/

namespace FloatSpec.Test.FLTDirect

open FloatSpec.Core.FLT FloatSpec.Core.Generic_fmt

example (prec emin beta : Int) [ValidRadix beta] (x : ℝ)
    (hx : FLT_format prec emin beta x) :
    generic_format beta (FLT_exp prec emin) x :=
  generic_format_FLT (prec := prec) (emin := emin) beta x hx

example (prec emin beta : Int) [Prec_gt_0 prec] [ValidRadix beta] (x : ℝ)
    (hx : generic_format beta (FLT_exp prec emin) x) :
    FLT_format prec emin beta x :=
  FLT_format_generic (prec := prec) (emin := emin) beta x hx

end FloatSpec.Test.FLTDirect
