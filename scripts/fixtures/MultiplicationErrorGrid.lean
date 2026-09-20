import FloatSpec.src.IEEE754.BinarySingleNaNSourceFacade

/-! Independent finite FLT multiplication-error check. Input units are 2^-4,
product/error units are 2^-8. Candidate membership uses an enumerated format,
not the rounder being tested. This is not a universal proof of Mult_error.v. -/

namespace MultiplicationErrorGrid

private instance : Prec_gt_0 (3 : Int) := ⟨by decide⟩
private instance : Prec_lt_emax (3 : Int) (4 : Int) := ⟨by decide⟩

private def positive : List (Nat × Int) :=
  [(1, -4), (2, -4), (3, -4)] ++
  (List.range 6).flatMap fun shift => [4, 5, 6, 7].map fun m => (m, (shift : Int) - 4)

private def inputUnits (s : Bool) (m : Nat) (e : Int) : Int :=
  let u : Int := m * (2 : Int) ^ (e + 4).toNat
  if s then -u else u

private def inputs : List (Int × BinarySingleNaN.binary_float 3 4) :=
  [(0, .B754_zero false)] ++ [false, true].flatMap fun s =>
    positive.map fun (m, e) =>
      (inputUnits s m e, BinarySingleNaN.SF2B' (.S754_finite s m e))

private def finiteUnits := inputs.map Prod.fst

private def units : StandardFloat → Option Int
  | .S754_zero _ => some 0
  | .S754_finite s m e =>
      if -8 ≤ e then
        let u : Int := m * (2 : Int) ^ (e + 8).toNat
        some (if s then -u else u)
      else none
  | _ => none

private def pairs := (inputs.product inputs).filter fun (x, y) =>
  let product := x.1 * y.1
  (product == 0 || 512 ≤ product.natAbs) && product.natAbs ≤ 3584

private def checkPair (mode : RoundingMode)
    (x y : Int × BinarySingleNaN.binary_float 3 4) : Bool :=
  match units (binarySingleNaNFloatToStandardFloat (BinarySingleNaN.Bmult mode x.2 y.2)) with
  | none => false
  | some rounded =>
      let error := rounded - x.1 * y.1
      error % 16 == 0 && finiteUnits.contains (error / 16)

private def modes : List RoundingMode := [.RNE, .RTZ, .RTN, .RTP, .RNA]

example : inputs.length = 55 ∧ pairs.length = 1077 ∧ modes.length = 5 := by
  decide +kernel

example : (inputs.all fun (u, x) =>
    units (binarySingleNaNFloatToStandardFloat x) == some (16 * u)) = true := by
  decide +kernel

example : (modes.all fun mode => pairs.all fun (x, y) => checkPair mode x y) = true := by
  decide +kernel

private def tiny : BinarySingleNaN.binary_float 3 4 :=
  BinarySingleNaN.SF2B' (.S754_finite false 1 (-4))

example : units (binarySingleNaNFloatToStandardFloat tiny) = some 16 ∧
    units (binarySingleNaNFloatToStandardFloat (BinarySingleNaN.Bmult .RNE tiny tiny)) = some 0 ∧
    (-1 : Int) % 16 ≠ 0 ∧ checkPair .RNE (1, tiny) (1, tiny) = false := by decide +kernel

#eval do
  unless modes.all (fun mode => pairs.all fun (x, y) => checkPair mode x y) do
    throw (IO.userError "multiplication-error grid failed")
  IO.println s!"PASS: {inputs.length} exact inputs; {5 * pairs.length} conditional multiplication-error cases; underflow counterexample."

end MultiplicationErrorGrid
