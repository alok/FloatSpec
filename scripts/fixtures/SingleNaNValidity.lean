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

#eval [valid 1 0, valid 4 (-2), valid 4 2, valid 1 (-4), valid 1 (-5), valid 0 (-4)]

end SingleNaNValidity
