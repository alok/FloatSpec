import FloatSpec.src.IEEE754.Bits

/-! Independent finite error bounds for source-shaped nearest rounding.
Precision 3 and emax 4 give emin -4, u = 1/8, and half a minimum ulp = 1/32.
All values below are represented in units of 2^-8, so checking the bound needs
integer arithmetic only. Inputs stay below overflow; this is not an error
bound for IEEE infinities or a replacement for the real-valued theorem. -/

namespace RelativeErrorGrid

private def units : StandardFloat → Option Int
  | .S754_zero _ => some 0
  | .S754_finite sign m e =>
      if -8 ≤ e then
        let magnitude : Int := m * (2 : Int) ^ (e + 8).toNat
        some (if sign then -magnitude else magnitude)
      else none
  | _ => none

private def bound (mode : RoundingMode) (sign : Bool) (m : Nat) : Bool :=
  let x : Int := if sign then -(m : Int) else m
  match units (binary_round (prec := 3) (emax := 4) mode sign m (-8)) with
  | none => false
  | some y =>
      if 64 ≤ m then decide (8 * (y - x).natAbs ≤ m)
      else decide ((y - x).natAbs ≤ 8)

/-- The relative bound requires normal magnitude; below that, the absolute
subnormal bound is used. Both nearest tie policies and both signs are checked. -/
theorem finite_nearest_grid :
    ([RoundingMode.RNE, .RNA].all fun mode => [false, true].all fun sign =>
      (List.range 1023).all fun k => bound mode sign (k + 1)) = true := by
  decide +kernel

/-- Dropping the normal-magnitude premise really fails: 2^-8 rounds to zero,
so its relative error is 1 rather than at most 1/8. -/
theorem underflow_requires_absolute_term :
    units (binary_round (prec := 3) (emax := 4) .RNE false 1 (-8)) = some 0 ∧
    ¬ (8 * Int.natAbs (0 - 1) ≤ 1) := by
  decide +kernel

#eval [bound .RNE false 1, bound .RNA true 1,
  bound .RNE false 64, bound .RNA true 1023]

end RelativeErrorGrid
