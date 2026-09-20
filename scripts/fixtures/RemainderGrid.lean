import FloatSpec.src.IEEE754.Bits

/-! Finite remainder-format checks in a three-bit format with units of 2^-4.
Quotients are an independent integer model of truncation, nearest ties-down,
nearest ties-up and ceiling. The code under test is actual binary_round.
This does not make the real-valued Ztrunc/Znearest definitions executable. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

namespace RemainderGrid

private def positiveUnits : List Int :=
  [1, 2, 3] ++ (List.range 6).flatMap fun shift =>
    [4, 5, 6, 7].map fun mantissa => mantissa * (2 : Int) ^ shift

private def finiteUnits : List Int := positiveUnits.map (-·) ++ [0] ++ positiveUnits

private def quotient (mode : Nat) (x y : Int) : Int :=
  if y = 0 then 0
  else
    let numerator := if y < 0 then -x else x
    let denominator : Int := y.natAbs
    let lower := numerator / denominator
    let remainder := numerator % denominator
    match mode with
    | 0 => numerator.tdiv denominator
    | 1 => lower + if denominator < 2 * remainder then 1 else 0
    | 2 => lower + if denominator ≤ 2 * remainder then 1 else 0
    | _ => lower + if remainder = 0 then 0 else 1

private def roundedUnits (value : Int) : Option Int :=
  if value = 0 then some 0
  else match binary_round (prec := 3) (emax := 4) .RNE (value < 0) value.natAbs (-4) with
    | .S754_zero _ => some 0
    | .S754_finite sign mantissa exponent =>
        if -4 ≤ exponent then
          let magnitude : Int := mantissa * (2 : Int) ^ (exponent + 4).toNat
          some (if sign then -magnitude else magnitude)
        else none
    | _ => none

private def sourcePremise (x y q : Int) : Bool :=
  y == 0 || 2 * x.natAbs ≥ y.natAbs || q == 0

private def check (mode : Nat) (x y : Int) : Bool :=
  let q := quotient mode x y
  let remainder := x - q * y
  !sourcePremise x y q || roundedUnits remainder == some remainder

/-- Actual source rounding preserves all remainders whose local source premise holds. -/
theorem remainder_grid :
    ([0, 1, 2, 3].all fun mode => (finiteUnits.product finiteUnits).all fun (x, y) =>
      check mode x y) = true := by
  decide +kernel

#print axioms remainder_grid

/-- Ceiling at a tiny positive quotient gives a remainder outside the format. -/
theorem ceiling_is_not_unconditionally_exact :
    roundedUnits (1 - quotient 3 1 128 * 128) ≠ some (1 - quotient 3 1 128 * 128) := by
  decide +kernel

#print axioms ceiling_is_not_unconditionally_exact

#eval do
  let mut qualified := 0
  let mut outside := 0
  let mut inexactOutside := 0
  let mut zeroDenominators := 0
  for mode in [0, 1, 2, 3] do
    for (x, y) in finiteUnits.product finiteUnits do
      let q := quotient mode x y
      let remainder := x - q * y
      let exact := roundedUnits remainder == some remainder
      if y == 0 then zeroDenominators := zeroDenominators + 1
      if sourcePremise x y q then
        qualified := qualified + 1
        unless exact do
          throw <| IO.userError s!"remainder failure: mode={mode}, x={x}, y={y}, quotient={q}"
      else
        outside := outside + 1
        if !exact then inexactOutside := inexactOutside + 1
  IO.println <| s!"PASS: 12,100 remainder cases; qualified={qualified}; outside={outside}; " ++
    s!"inexactOutside={inexactOutside}; zeroDenominators={zeroDenominators}"

end RemainderGrid
