import FloatSpec.src.IEEE754.BinarySingleNaNSourceFacade

/-! Each normalization entry point must execute independently. Literal expected
values cover both zero signs, even/odd halfway cases, subnormal underflow and
overflow in all five modes. These are finite checks, not source equivalence. -/

namespace Normalization
private instance : Prec_gt_0 (3 : Int) := ⟨by decide⟩
private instance : Prec_lt_emax (3 : Int) (4 : Int) := ⟨by decide⟩

private def inputs : List (Int × Int × Bool) :=
  [(0, 20, true), (0, -20, false), (9, -3, false), (-9, -3, false),
   (1, -5, false), (-1, -5, false), (15, 0, false), (-15, 0, false),
   (11, -3, false), (-11, -3, false)]

private def observe (mode : RoundingMode) (m e : Int) (szero : Bool) : List StandardFloat :=
  [Binary.B2SF (Binary.binary_normalize (prec := 3) (emax := 4) mode m e szero),
   B2SF_BSN (_root_.binary_normalize (prec := 3) (emax := 4) mode m e szero),
   binarySingleNaNFloatToStandardFloat
     (BinarySingleNaN.binary_normalize (prec := 3) (emax := 4) mode m e szero)]

private def actual : List (List StandardFloat) :=
  [.RNE, .RTZ, .RTN, .RTP, .RNA].map fun mode =>
    inputs.flatMap fun (m, e, szero) => observe mode m e szero

private def expected : List (List StandardFloat) :=
  [[.S754_zero true,
     .S754_zero false,
     .S754_finite false 4 (-2),
     .S754_finite true 4 (-2),
     .S754_zero false,
     .S754_zero true,
     .S754_infinity false,
     .S754_infinity true,
     .S754_finite false 6 (-2),
     .S754_finite true 6 (-2)],
   [.S754_zero true,
     .S754_zero false,
     .S754_finite false 4 (-2),
     .S754_finite true 4 (-2),
     .S754_zero false,
     .S754_zero true,
     .S754_finite false 7 (1),
     .S754_finite true 7 (1),
     .S754_finite false 5 (-2),
     .S754_finite true 5 (-2)],
   [.S754_zero true,
     .S754_zero false,
     .S754_finite false 4 (-2),
     .S754_finite true 5 (-2),
     .S754_zero false,
     .S754_finite true 1 (-4),
     .S754_finite false 7 (1),
     .S754_infinity true,
     .S754_finite false 5 (-2),
     .S754_finite true 6 (-2)],
   [.S754_zero true,
     .S754_zero false,
     .S754_finite false 5 (-2),
     .S754_finite true 4 (-2),
     .S754_finite false 1 (-4),
     .S754_zero true,
     .S754_infinity false,
     .S754_finite true 7 (1),
     .S754_finite false 6 (-2),
     .S754_finite true 5 (-2)],
   [.S754_zero true,
     .S754_zero false,
     .S754_finite false 5 (-2),
     .S754_finite true 5 (-2),
     .S754_finite false 1 (-4),
     .S754_finite true 1 (-4),
     .S754_infinity false,
     .S754_infinity true,
     .S754_finite false 6 (-2),
     .S754_finite true 6 (-2)]]

-- This local adapter requires evidence about its raw result, not an assumed
-- theorem about every integer input. Preserve the rejection bit separately.
private def adapter (prec emax : Int) (mode : RoundingMode) (sx : Bool)
    (mx ex : Int) (lx : FloatSpec.Calc.Bracket.Location) : Bool × StandardFloat :=
  let raw := _root_.binary_round_aux (prec := prec) (emax := emax) mode sx mx ex lx
  let valid := validBinarySingleNaNStandardFloat (prec := prec) (emax := emax) raw
  (valid, if h : valid = true then
    binarySingleNaNFloatToStandardFloat
      (binaryRoundAuxToBinarySingleNaNFloat (prec := prec) (emax := emax)
        mode sx mx ex lx h)
    else .S754_nan)

private def adapterRows : List (Bool × StandardFloat) :=
  [adapter 3 4 .RNE false 9 (-3) .loc_Exact,
   adapter 3 4 .RNA true 9 (-3) .loc_Exact,
   adapter 3 4 .RNE true 0 (-4) .loc_Exact,
   adapter 3 4 .RNE false (-1) (-4) .loc_Exact,
   adapter 3 0 .RTZ false 1 0 .loc_Exact,
   -- A malformed format parameter alone need not make the raw result invalid:
   -- this one rounds to a valid zero, unlike the preceding finite overflow.
   adapter 0 1 .RTZ false 1 0 .loc_Exact]

private def expectedAdapters : List (Bool × StandardFloat) :=
  [(true, .S754_finite false 4 (-2)), (true, .S754_finite true 5 (-2)),
   (true, .S754_zero true), (true, .S754_nan), (false, .S754_nan),
   (true, .S754_zero false)]

private def expectedRows : List (List StandardFloat) :=
  expected.map (fun values => values.flatMap (List.replicate 3))

private theorem normalizersAgreeWithLiterals : actual = expectedRows := by
  decide +kernel

private theorem adapterPremiseIsObserved : adapterRows = expectedAdapters := by decide +kernel

#eval do
  unless decide (actual = expectedRows) &&
      decide (adapterRows = expectedAdapters) do
    throw (IO.userError "normalization or validity adapter boundary mismatch")
  IO.println "PASS: 150 normalization observations (three APIs, five modes) and six validity-adapter boundaries."

end Normalization
