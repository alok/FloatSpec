import FloatSpec.src.IEEE754.PrimFloat
import FloatSpec.src.IEEE754.BinarySingleNaNSourceFacade

/-! Regression checks for the source-facing Coq primitive-float contract. -/

open FaithfulPrimFloat

example : FaithfulPrimFloat.flatten_cmp_opt none = FNotComparable := rfl

example :
    FaithfulPrimFloat.flatten_cmp_opt (some Ordering.eq) = FEq := rfl

example :
    FaithfulPrimFloat.flatten_cmp_opt (some Ordering.lt) = FLt := rfl

example :
    FaithfulPrimFloat.flatten_cmp_opt (some Ordering.gt) = FGt := rfl

/-- The former three-way model incorrectly returned ordinary equality here. -/
example :
    FaithfulPrimFloat.compare FaithfulPrimFloat.nan FaithfulPrimFloat.zero =
      FNotComparable := rfl

/-- Coq's standalone class contains only `prec < emax`; it does not impose an
independent lower bound on `emax`. -/
example : Prec_lt_emax (-5) 0 := ⟨by omega⟩

/-- Binary-format proofs still recover the useful lower bound from the two
actual source premises. -/
example : (2 : Int) ≤ FaithfulPrimFloat.primEmax := by
  have hprec := FaithfulPrimFloat.Hprec.pos
  have hlt := FaithfulPrimFloat.Hmax.prec_lt_emax
  omega

-- This consumer pins the real source validity contract. Replacing it with the
-- permissive compatibility predicate would make this example fail to typecheck.
example {prec emax : Int} [Prec_gt_0 prec] [Prec_lt_emax prec emax]
    (mode : RoundingMode) (sign : Bool) :
    validBinarySingleNaNStandardFloat (prec := prec) (emax := emax)
      (BinarySingleNaN.binary_overflow (prec := prec) (emax := emax) mode sign) = true :=
  BinarySingleNaN.binary_overflow_correct mode sign

-- Nat-based compatibility carriers can express malformed finite values that
-- Coq excludes through its positive mantissa type. Actual validity must reject them.
example : validBinarySingleNaNStandardFloat (prec := 53) (emax := 1024)
    (.S754_finite false 0 (-1074)) = false := by decide

example : validBinarySingleNaNStandardFloat (prec := 53) (emax := 1024)
    (.S754_finite false 1 1024) = false := by decide

-- The conversion theorem must relate independent validity predicates, with
-- no assumption that the input is already valid.
example {prec emax : Int} (x : StandardFloat) (hnotnan : is_nan_SF x = false) :
    valid_binary (prec := prec) (emax := emax) (SF2FF x) =
      validBinarySingleNaNStandardFloat (prec := prec) (emax := emax) x :=
  valid_binary_SF2FF x hnotnan

example : valid_binary (prec := 53) (emax := 1024)
    (SF2FF (.S754_finite false 0 (-1074))) = false := by decide
