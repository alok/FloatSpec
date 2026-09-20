import FloatSpec.src.IEEE754.BinarySingleNaNSourceFacade

/-! Literal source-helper boundaries. The one-bit format deliberately cannot
represent a normalized frexp fraction: Flocq's normalization conclusion needs
`2 < emax`, while the total decomposition still returns a result. -/

namespace SingleNaNHelpers

private instance : Prec_gt_0 (3 : Int) := ⟨by decide⟩
private instance : Prec_lt_emax (3 : Int) (4 : Int) := ⟨by decide⟩
private instance : Prec_gt_0 (1 : Int) := ⟨by decide⟩
private instance : Prec_lt_emax (1 : Int) (2 : Int) := ⟨by decide⟩
private instance : Prec_gt_0 (8 : Int) := ⟨by decide⟩

private def one : BinarySingleNaN.binary_float 3 4 := BinarySingleNaN.Bone
private def tiny : BinarySingleNaN.binary_float 3 4 :=
  BinarySingleNaN.SF2B' (.S754_finite false 1 (-4))
private def observe {p e : Int} := @binarySingleNaNFloatToStandardFloat p e

private def rows : List StandardFloat :=
  [observe one, observe (Binary.B2BSN (Binary.Bone (prec := 3) (emax := 4))),
   observe (BinarySingleNaN.binary_normalize (prec := 3) (emax := 4) .RNE 0 0 true),
   observe (BinarySingleNaN.binary_normalize (prec := 3) (emax := 4) .RNE (-9) (-3) false),
   observe (BinarySingleNaN.Bldexp .RNE tiny (-1)),
   observe (BinarySingleNaN.Bldexp .RTP tiny (-1)),
   observe (BinarySingleNaN.Bulp' one),
   observe (BinarySingleNaN.Bpred_pos' one),
   observe (BinarySingleNaN.Bsucc' one),
   observe (BinarySingleNaN.Bsucc' (BinarySingleNaN.Bopp tiny)),
   observe (BinarySingleNaN.Bsucc' (prec := 3) (emax := 4) (.B754_zero true)),
   observe (BinarySingleNaN.Bsucc' (prec := 3) (emax := 4) (.B754_infinity true)),
   observe (BinarySingleNaN.Bsucc' (prec := 3) (emax := 4) .B754_nan)]

private def expected : List StandardFloat :=
  [.S754_finite false 4 (-2), .S754_finite false 4 (-2),
   .S754_zero true, .S754_finite true 4 (-2),
   .S754_zero false, .S754_finite false 1 (-4),
   .S754_finite false 4 (-4), .S754_finite false 7 (-3),
   .S754_finite false 5 (-2), .S754_zero true,
   .S754_finite false 1 (-4), .S754_finite true 7 1, .S754_nan]

private def fractions : List (StandardFloat × Int) :=
  [let f := BinarySingleNaN.Bfrexp one; (observe f.1, f.2),
   let f := BinarySingleNaN.Bfrexp tiny; (observe f.1, f.2),
   let f := BinarySingleNaN.Bfrexp (prec := 3) (emax := 4) (.B754_zero true);
     (observe f.1, f.2),
   let f := BinarySingleNaN.Bfrexp (BinarySingleNaN.Bone (prec := 1) (emax := 2));
     (observe f.1, f.2),
   -- No Prec_lt_emax instance exists for these four source-legal calls.
   let f := BinarySingleNaN.Bfrexp
     (BinarySingleNaN.SF2B' (prec := 8) (emax := 2) (.S754_finite false 1 (-7)));
     (observe f.1, f.2),
   let f := BinarySingleNaN.Bfrexp
     (BinarySingleNaN.SF2B' (prec := 8) (emax := 3) (.S754_finite true 1 (-8)));
     (observe f.1, f.2),
   let f := BinarySingleNaN.Bfrexp
     (BinarySingleNaN.SF2B' (prec := 3) (emax := 3) (.S754_finite false 4 (-2)));
     (observe f.1, f.2),
   let f := BinarySingleNaN.Bfrexp (prec := 1) (emax := -3) (.B754_zero true);
     (observe f.1, f.2)]

private def expectedFractions : List (StandardFloat × Int) :=
  [(.S754_finite false 4 (-3), 1), (.S754_finite false 4 (-3), -3),
   (.S754_zero true, -11), (.S754_finite false 1 0, 0),
   (.S754_finite false 1 (-7), 0), (.S754_finite true 128 (-8), -7),
   (.S754_finite false 4 (-3), 1), (.S754_zero true, 5)]

private def shifts : List Int :=
  [(Binary.shr_fexp (prec := 3) (emax := 4) (-1) (-5) .loc_Exact).1.shr_m,
   (BinarySingleNaN.shr_fexp (prec := 3) (emax := 4) (-1) (-5) .loc_Exact).1.shr_m]

-- The source equality theorems really need these domain restrictions.
private def premiseWitnesses : Bool :=
  let inf : BinarySingleNaN.binary_float 3 4 := .B754_infinity false
  let negativeOne := BinarySingleNaN.Bopp one
  decide (observe (BinarySingleNaN.Bulp' inf) ≠ observe (BinarySingleNaN.Bulp inf)) &&
    decide (observe (BinarySingleNaN.Bpred_pos' negativeOne) ≠
      observe (BinarySingleNaN.Bpred negativeOne))

example : rows = expected ∧ fractions = expectedFractions ∧ shifts = [0, 0] := by
  decide +kernel

example : premiseWitnesses = true := by decide +kernel

#eval do
  unless decide (rows = expected ∧ fractions = expectedFractions ∧ shifts = [0, 0]) &&
      premiseWitnesses do
    throw (IO.userError "SingleNaN helper boundary mismatch")
  IO.println "PASS: 13 helper values, eight decompositions, two signed shifts, and two premise counterexamples."

end SingleNaNHelpers
