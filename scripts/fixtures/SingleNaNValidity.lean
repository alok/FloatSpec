import FloatSpec.src.IEEE754.BinarySingleNaNSourceFacade

/-! A raw carrier can contain a finite representation that is not canonical.
The source predicate must reject it even though it denotes a harmless real.
These checks deliberately do not use the permissive legacy validity predicate. -/

namespace SingleNaNValidity

private def valid (m : Nat) (e : Int) : Bool :=
  validBinarySingleNaNStandardFloat (prec := 3) (emax := 4) (.S754_finite false m e)

/-- Only the normalized representation of one is valid in this three-bit format;
the exponent bound also excludes a normalized mantissa above the finite range. -/
theorem boundaries :
    valid 1 0 = false ∧ valid 4 (-2) = true ∧ valid 4 2 = false ∧
    valid 1 (-4) = true ∧ valid 1 (-5) = false ∧ valid 0 (-4) = false := by
  decide +kernel

/-- Cross-test counterexamples to the old range-only converter and the
off-by-one mantissa bound in the old raw-carrier validity predicate. -/
theorem raw_boundary_regressions :
    ¬ validB754 3 4 (.B754_finite false 1 0) ∧
    validB754 3 4 (.B754_finite false 4 (-2)) ∧
    _root_.SF2B' (prec := 3) (emax := 4) (.S754_finite false 1 0) = .B754_nan ∧
    _root_.SF2B' (prec := 3) (emax := 4) (.S754_finite false 4 (-2)) =
      .B754_finite false 4 (-2) ∧
    _root_.SF2B' (prec := 3) (emax := 4) (.S754_finite false 0 (-4)) = .B754_nan := by
  refine ⟨?_, ?_, rfl, rfl, rfl⟩ <;> unfold validB754 <;> decide +kernel

/-- The raw and proof-carrying total converters agree for every input,
including invalid finite representations and exceptional values. -/
example (prec emax : Int) (x : StandardFloat) :
    _root_.SF2B' (prec := prec) (emax := emax) x =
      SF2BSpec' (prec := prec) (emax := emax) x := by
  cases x with
  | S754_zero s => rfl
  | S754_infinity s => rfl
  | S754_nan => rfl
  | S754_finite s m e =>
      by_cases hm : 0 < m <;>
        cases hb : specFloat_bounded (prec := prec) (emax := emax) m e <;>
          simp [SF2B', SF2BSpec', standardFloatToBinarySingleNaNFloat',
            standardFloatToBinarySingleNaNFloat, binarySingleNaNFloatToB754,
            validBinarySingleNaNStandardFloat, hm, hb]

/-- Fitting only checks the upper exponent. Its validity theorem therefore
needs the canonical-mantissa premise; it is not unconditional validity. -/
theorem fit_requires_canonical_input :
    validBinarySingleNaNStandardFloat (prec := 3) (emax := 4)
      (binary_fit_aux (prec := 3) (emax := 4) .RNE false 1 0) = false ∧
    validBinarySingleNaNStandardFloat (prec := 3) (emax := 4)
      (binary_fit_aux (prec := 3) (emax := 4) .RNE false 4 (-2)) = true := by
  decide +kernel

/-- This is the proof-carrying source theorem, not the raw-carrier legacy claim. -/
example (x : BinarySingleNaN.binary_float 3 4) :
    validBinarySingleNaNStandardFloat (prec := 3) (emax := 4)
      (BinarySingleNaN.B2SF x) = true :=
  BinarySingleNaN.valid_binary_B2SF x

/-- The root source export must establish the same strong predicate. -/
example (x : BinarySingleNaNFloat prec emax) :
    validBinarySingleNaNStandardFloat (prec := prec) (emax := emax)
      (binarySingleNaNFloatToStandardFloat x) = true :=
  _root_.valid_binary_B2SF x

/-- Consuming the validity conjunct rules out a regression to the old
always-true compatibility predicate. -/
example (prec emax : Int) [Prec_gt_0 prec] [Prec_lt_emax prec emax]
    (mode : RoundingMode) (sign : Bool) (m : Nat) (e : Int) (hpos : 0 < m)
    (hcanon : canonical_mantissa (prec := prec) (emax := emax) m e = true) :
    validBinarySingleNaNStandardFloat (prec := prec) (emax := emax)
      (binary_fit_aux (prec := prec) (emax := emax) mode sign m e) = true :=
  (binary_fit_aux_correct (prec := prec) (emax := emax) mode sign m e hpos hcanon).1

#eval [valid 1 0, valid 4 (-2), valid 4 2, valid 1 (-4), valid 1 (-5), valid 0 (-4)]

end SingleNaNValidity
