import FloatSpec.src.Calc.Plus
import FloatSpec.src.Calc.Round
import FloatSpec.src.IEEE754.Binary
import FloatSpec.src.Pff.Pff2FlocqAux

namespace FloatSpec.Test.FlocqConformance

open FloatSpec.Calc.Bracket
open Std.Do

/-! These examples mirror executable evaluations against the Flocq gitlink
commit.  In particular, Flocq's integer `Zpower` is total and evaluates to zero
at a negative exponent; replacing it with a power at `Int.natAbs` changes the
result outside the proof theorem's positive-exponent preconditions. -/

example :
    FloatSpec.Calc.Plus.Fplus_core 2 1 0 0 1 1 =
      (0, Location.loc_Exact) := by
  rfl

example :
    FloatSpec.Calc.Plus.Fplus_core 2 1 0 0 1 0 =
      (1, Location.loc_Exact) := by
  rfl

example :
    FloatSpec.Calc.Round.truncate_aux 2
      (2, 0, Location.loc_Exact) (-1) =
      (0, -1, Location.loc_Inexact Ordering.gt) := by
  rfl

example :
    FloatSpec.Calc.Round.truncate_aux 2
      (2, 0, Location.loc_Exact) 1 =
      (1, 1, Location.loc_Exact) := by
  rfl

example :
    valid_binary_payload (prec := 3) (emax := 4)
      (.F754_nan false 0) = false := by
  rfl

example :
    valid_binary_payload (prec := 3) (emax := 4)
      (.F754_nan false 4) = false := by
  simp [valid_binary_payload, FloatSpec.Core.Digits.digits2_pos,
    FloatSpec.Core.Digits.digits2_Pnat,
    FloatSpec.Core.Digits.digits2_Pnat_bitlength_payload,
    FloatSpec.Core.Zaux.Zlt_bool]

example :
    valid_binary_payload (prec := 3) (emax := 4)
      (.F754_nan false 3) = true := by
  simp [valid_binary_payload, FloatSpec.Core.Digits.digits2_pos,
    FloatSpec.Core.Digits.digits2_Pnat,
    FloatSpec.Core.Digits.digits2_Pnat_bitlength_payload,
    FloatSpec.Core.Zaux.Zlt_bool]

example : (make_bound 2 0 (-1)).dExp = 1 := by
  have h := make_bound_Emin 2 0 (-1)
  have h' := h (by omega : (-1 : Int) ≤ 0)
  simpa [wp, PostCond.noThrow, make_bound_Emin_check, pure] using h'

end FloatSpec.Test.FlocqConformance
