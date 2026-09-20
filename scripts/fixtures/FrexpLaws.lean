import FloatSpec.src.IEEE754.BinarySingleNaNSourceFacade

/-! Independent integer checks of exact decomposition and its conditional
normalization law. No real-valued theorem is used as an execution oracle.
Formats include precision >= emax and empty finite-value ranges. -/

namespace FrexpLaws

private def finiteMember (precision : Nat) (emax : Int) (m : Nat) (e : Int) : Bool :=
  let emin := 3 - emax - (precision : Int)
  decide (0 < m ∧ m < 2 ^ precision ∧ emin ≤ e ∧ e ≤ emax - precision ∧
    (e = emin ∨ 2 ^ (precision - 1) ≤ m))

private def compareDyadic (m e n f : Int) : Ordering :=
  if e ≤ f then compare m (n * 2 ^ (f - e).toNat)
  else compare (m * 2 ^ (e - f).toNat) n

private def checkCase (precisionMinusOne : Nat) (emax : Int)
    (s : Bool) (m : Nat) (e : Int) : Bool :=
  let precision := precisionMinusOne + 1
  let prec : Int := precision
  letI : Prec_gt_0 prec := ⟨by dsimp [prec, precision]; grind⟩
  let raw := StandardFloat.S754_finite s m e
  let x := BinarySingleNaN.SF2B' (prec := prec) (emax := emax) raw
  let converted := binarySingleNaNFloatToStandardFloat x
  let f := BinarySingleNaN.Bfrexp x
  let fraction := binarySingleNaNFloatToStandardFloat f.1
  if finiteMember precision emax m e then
    decide (converted = raw) && match fraction with
    | .S754_finite fs fm fe =>
        (fs == s) && finiteMember precision emax fm fe &&
        (compareDyadic m e fm (fe + f.2) == .eq) &&
        (emax ≤ 2 || (compareDyadic fm fe 1 (-1) != .lt &&
                      compareDyadic fm fe 1 0 == .lt))
    | _ => false
  else
    decide (converted = .S754_nan ∧ fraction = .S754_nan) && f.2 == -2 * emax - prec

private def formats : List (Nat × Int) :=
  [(0, 2), (2, 3), (7, 2), (7, 3), (0, -3), (7, 0), (7, 1)]

private def checks : List (Bool × Bool) :=
  formats.flatMap fun (pm, emax) =>
    let emin := 3 - emax - ((pm + 1 : Nat) : Int)
    [false, true].flatMap fun s =>
      (List.range (2 ^ (pm + 1))).flatMap fun m =>
        (List.range (max 1 (2 * emax).toNat)).map fun offset =>
          let e := emin - 1 + (offset : Int)
          (finiteMember (pm + 1) emax (m + 1) e, checkCase pm emax s (m + 1) e)

example : checks.length = 6772 ∧ (checks.filter Prod.fst).length = 2086 ∧
    checks.all Prod.snd = true := by
  decide +kernel

#eval do
  unless checks.length == 6772 && (checks.filter Prod.fst).length == 2086 &&
      checks.all Prod.snd do
    throw (IO.userError "independent frexp domain law failed")
  IO.println "PASS: 6,772 independent frexp laws; 2,086 valid finite inputs and 4,686 rejected raw inputs."

end FrexpLaws
