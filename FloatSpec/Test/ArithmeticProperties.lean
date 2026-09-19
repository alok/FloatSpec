import FloatSpec.src.Calc.Bracket
import FloatSpec.src.Calc.Sqrt
import FloatSpec.src.Core.Zaux

/-! Independent finite arithmetic invariants. These are kernel-checked examples,
not universal specifications and not values copied from a second implementation. -/

namespace FloatSpec.Test.ArithmeticProperties

open FloatSpec.Calc.Bracket
open FloatSpec.Core.Zaux

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

private def locations : List Location :=
  [.loc_Exact, .loc_Inexact .lt, .loc_Inexact .eq, .loc_Inexact .gt]

/-- Four exact rational representatives, with a common denominator of four. -/
private def quarter : Location → Int
  | .loc_Exact => 0
  | .loc_Inexact .lt => 1
  | .loc_Inexact .eq => 2
  | .loc_Inexact .gt => 3

private def classifyQuarter (steps index : Int) (loc : Location) : Location :=
  let numerator := 4 * index + quarter loc
  if numerator = 0 then .loc_Exact
  else .loc_Inexact (if numerator < 2 * steps then .lt
    else if numerator = 2 * steps then .eq else .gt)

-- 8,316 rational representative cases: 2 ≤ steps ≤ 64, 0 ≤ index < steps.
theorem location_rational_grid : ((List.range 63).all fun n =>
    let steps := n + 2
    (List.range steps).all fun index => locations.all fun loc =>
      decide (new_location steps index loc = classifyQuarter steps index loc)) = true := by
  decide

-- Signed floor-division reconstruction and remainder sign/range, including
-- division by zero. Numerators -32..32; denominators -16..16: 2,145 cases.
theorem signed_division_grid : ((List.range 65).all fun n => (List.range 33).all fun d =>
    let a : Int := (n : Int) - 32
    let b : Int := (d : Int) - 16
    let (q, r) := Z_div_eucl a b
    decide (a = b * q + r ∧
      (if b = 0 then q = 0 ∧ r = a
       else if 0 < b then 0 ≤ r ∧ r < b else b < r ∧ r ≤ 0))) = true := by
  decide

-- Integer square-root brackets independently characterize the nonnegative
-- answer at exponent zero. Negative inputs check Flocq's totalized convention.
theorem sqrt_bracket_grid : ((List.range 273).all fun n =>
    let m : Int := (n : Int) - 16
    let (q, loc) := FloatSpec.Calc.Sqrt.Fsqrt_core 2 m 0 0
    decide (if m < 0 then q = 0 ∧ loc = .loc_Exact
      else 0 ≤ q ∧ q * q ≤ m ∧ m < (q + 1) * (q + 1) ∧
        (loc = .loc_Exact ↔ q * q = m))) = true := by
  decide +kernel

end FloatSpec.Test.ArithmeticProperties
