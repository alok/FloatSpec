import FloatSpec.src.Calc.Plus
import FloatSpec.src.Calc.Div
import FloatSpec.src.Calc.Sqrt
import FloatSpec.src.Calc.Round
import FloatSpec.src.IEEE754.Binary
import FloatSpec.src.IEEE754.BinarySingleNaN
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
    FloatSpec.Calc.Operations.Falign 2 ⟨1, 0⟩ ⟨1, -1⟩ =
      (2, 1, -1) := by
  rfl

example (beta : Int) [ValidRadix beta]
    (x y : FloatSpec.Core.Defs.FlocqFloat beta) :
    FloatSpec.Calc.Operations.Falign_exp beta x y = min x.Fexp y.Fexp :=
  FloatSpec.Calc.Operations.Falign_spec_exp beta x y

example (beta : Int) [ValidRadix beta] (m1 m2 e : Int) :
    FloatSpec.Calc.Operations.Fplus_same_exp beta m1 m2 e =
      FloatSpec.Core.Defs.FlocqFloat.mk (m1 + m2) e :=
  FloatSpec.Calc.Operations.Fplus_same_exp_spec beta m1 m2 e

example (beta : Int) [ValidRadix beta] (m1 m2 e : Int) :
    FloatSpec.Calc.Operations.Fminus_same_exp beta m1 m2 e =
      FloatSpec.Core.Defs.FlocqFloat.mk (m1 - m2) e :=
  FloatSpec.Calc.Operations.Fminus_same_exp_spec beta m1 m2 e

example :
    FloatSpec.Calc.Plus.Fplus 2 (FloatSpec.Core.FIX.FIX_exp 0)
      ⟨1, 0⟩ ⟨1, 1⟩ =
      (3, 0, Location.loc_Exact) := by
  rfl

example :
    FloatSpec.Calc.Div.Fdiv_core 2 4 0 2 0 0 =
      (2, Location.loc_Exact) := by
  rfl

example :
    FloatSpec.Calc.Div.Fdiv_core 2 1 0 2 0 0 =
      (0, Location.loc_Inexact Ordering.eq) := by
  rfl

example :
    FloatSpec.Calc.Div.Fdiv 2 (FloatSpec.Core.FIX.FIX_exp 0)
      ⟨4, 0⟩ ⟨2, 0⟩ =
      (2, 0, Location.loc_Exact) := by
  rfl

example :
    FloatSpec.Calc.Sqrt.Fsqrt_core 2 4 0 0 =
      (2, Location.loc_Exact) := by
  norm_num [FloatSpec.Calc.Sqrt.Fsqrt_core, FloatSpec.Core.Zaux.Zpower]

example :
    FloatSpec.Calc.Sqrt.Fsqrt_core 2 2 0 0 =
      (1, Location.loc_Inexact Ordering.lt) := by
  norm_num [FloatSpec.Calc.Sqrt.Fsqrt_core, FloatSpec.Core.Zaux.Zpower]

example :
    FloatSpec.Calc.Sqrt.Fsqrt 2 (FloatSpec.Core.FIX.FIX_exp 0)
      ⟨4, 0⟩ = (2, 0, Location.loc_Exact) := by
  norm_num [FloatSpec.Calc.Sqrt.Fsqrt, FloatSpec.Calc.Sqrt.Fsqrt_core,
    FloatSpec.Core.Zaux.Zpower, FloatSpec.Core.FIX.FIX_exp]

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

-- Source `truncate` derives the target exponent from `fexp`, not from a
-- caller-supplied exponent.  The legacy `truncate_at_exp` would not shift here.
example :
    FloatSpec.Calc.Round.truncate 2 (FloatSpec.Core.FIX.FIX_exp 1)
      (4, 0, Location.loc_Exact) =
      (2, 1, Location.loc_Exact) := by
  rfl

example :
    Binary.shr_fexp (prec := 2) (emax := 4) 4 0 Location.loc_Exact =
      ({ shr_m := 2, shr_r := false, shr_s := false }, 1) := by
  rfl

example :
    FloatSpec.Calc.Round.round_sign_UP true
      (Location.loc_Inexact Ordering.gt) = false := by
  rfl

example :
    FloatSpec.Calc.Round.round_N true
      (Location.loc_Inexact Ordering.eq) = true := by
  rfl

example :
    FloatSpec.Calc.Round.truncate_FIX (beta := 2) 1
      (4, 0, Location.loc_Exact) = (2, 1, Location.loc_Exact) := by
  rfl

example :
    valid_binary_payload (prec := 3) (emax := 4)
      (.F754_nan false 0) = false := by
  rfl

example :
    valid_binary_payload (prec := 3) (emax := 4)
      (.F754_nan false 4) = false := by
  simp [valid_binary_payload, valid_binary, FloatSpec.Core.Digits.digits2_pos,
    FloatSpec.Core.Digits.digits2_Pnat,
    FloatSpec.Core.Digits.digits2_Pnat_bitlength_payload,
    FloatSpec.Core.Zaux.Zlt_bool]

example :
    valid_binary_payload (prec := 3) (emax := 4)
      (.F754_nan false 3) = true := by
  simp [valid_binary_payload, valid_binary, FloatSpec.Core.Digits.digits2_pos,
    FloatSpec.Core.Digits.digits2_Pnat,
    FloatSpec.Core.Digits.digits2_Pnat_bitlength_payload,
    FloatSpec.Core.Zaux.Zlt_bool]

example : (make_bound 2 0 (-1)).dExp = 1 := by
  have h := make_bound_Emin 2 0 (-1)
  have h' := h (by omega : (-1 : Int) ≤ 0)
  simpa [wp, PostCond.noThrow, make_bound_Emin_check, pure] using h'

end FloatSpec.Test.FlocqConformance
