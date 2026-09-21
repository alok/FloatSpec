import FloatSpec.src.Pff.SourceFacade

/-! Typed clients for the unindexed source operations. Radix one is deliberately
accepted by addition, subtraction and multiplication correctness, while
zero-observer laws have no radix premise. -/

namespace PffBasicSourceContracts

open FloatSpec.Pff

#check (Source.Fzero : Int → Source.float)
#check (Source.is_Fzero : Source.float → Prop)
#check (Source.Fmult : Source.float → Source.float → Source.float)
#check (Source.FzeroisReallyZero : ∀ radix exponent : Int,
  Source.FtoR radix (Source.Fzero exponent) = 0)
#check (Source.is_Fzero_rep1 : ∀ (radix : Int) (x : Source.float),
  Source.is_Fzero x → Source.FtoR radix x = 0)
#check (Source.is_Fzero_rep2 : ∀ (radix : Int), 1 < radix →
  ∀ x : Source.float, Source.FtoR radix x = 0 → Source.is_Fzero x)
#check (Source.Fmult_correct : ∀ (radix : Int), 0 < radix →
  ∀ x y : Source.float, Source.FtoR radix (Source.Fmult x y) =
    Source.FtoR radix x * Source.FtoR radix y)

#check Source.FzeroisReallyZero 0 (-7)
#check Source.is_Fzero_rep1 (-3)
#check Source.Fmult_correct 1 (by decide)

#check (Source.Fopp_correct : ∀ (radix : Int) (x : Source.float),
  Source.FtoR radix (Source.Fopp x) = -Source.FtoR radix x)
#check (Source.Fopp_Fopp : ∀ x : Source.float, Source.Fopp (Source.Fopp x) = x)
#check (Source.Fabs_correct : ∀ (radix : Int), 0 < radix → ∀ x : Source.float,
  Source.FtoR radix (Source.Fabs x) = |Source.FtoR radix x|)
#check (Source.Fabs_Fzero : ∀ x : Source.float,
  ¬ Source.is_Fzero x → ¬ Source.is_Fzero (Source.Fabs x))

#check Source.Fopp_correct (-2)
#check Source.Fabs_correct 1 (by decide)

#check (Source.Fplus_correct : ∀ (radix : Int), 0 < radix → ∀ x y : Source.float,
  Source.FtoR radix (Source.Fplus radix x y) = Source.FtoR radix x + Source.FtoR radix y)
#check (Source.Fminus_correct : ∀ (radix : Int), 0 < radix → ∀ x y : Source.float,
  Source.FtoR radix (Source.Fminus radix x y) = Source.FtoR radix x - Source.FtoR radix y)
#check Source.Fplus_correct 1 (by decide)
#check Source.Fminus_correct 1 (by decide)

#guard Source.Fzero (-7) == ⟨0, -7⟩
#guard Source.Fmult ⟨-3, -7⟩ ⟨5, 9⟩ == ⟨-15, 2⟩
#guard @decide (Source.is_Fzero (Source.Fzero (-7)))
  (by unfold Source.is_Fzero Source.Fzero; infer_instance)

/-- At radix zero, adding exponents does not preserve products across negative powers. -/
theorem zero_radix_is_not_a_multiplication_model :
    Source.FtoR 0 (Source.Fmult ⟨1, 1⟩ ⟨1, -1⟩) ≠
      Source.FtoR 0 ⟨1, 1⟩ * Source.FtoR 0 ⟨1, -1⟩ := by
  norm_num [Source.FtoR, Source.Fmult]

#print axioms zero_radix_is_not_a_multiplication_model
#print axioms Source.Fmult_correct
#print axioms Source.FzeroisReallyZero
#print axioms Source.is_Fzero_rep1
#print axioms Source.is_Fzero_rep2
#print axioms Source.Fmult
#print axioms Source.Fzero

/-- A negative radix invalidates the absolute-value observer law. -/
theorem negative_radix_is_not_an_absolute_value_model :
    Source.FtoR (-2) (Source.Fabs ⟨1, 1⟩) ≠ |Source.FtoR (-2) ⟨1, 1⟩| := by
  norm_num [Source.FtoR, Source.Fabs]

#print axioms negative_radix_is_not_an_absolute_value_model
#print axioms Source.Fopp_correct
#print axioms Source.Fopp_Fopp
#print axioms Source.Fabs_correct
#print axioms Source.Fabs_Fzero

/-- Alignment at radix zero loses a nonzero value when the common exponent is negative. -/
theorem zero_radix_is_not_an_addition_model :
    Source.FtoR 0 (Source.Fplus 0 ⟨1, 0⟩ ⟨0, -1⟩) ≠
      Source.FtoR 0 ⟨1, 0⟩ + Source.FtoR 0 ⟨0, -1⟩ := by
  norm_num [Source.FtoR, Source.Fplus]

theorem zero_radix_is_not_a_subtraction_model :
    Source.FtoR 0 (Source.Fminus 0 ⟨1, 0⟩ ⟨0, -1⟩) ≠
      Source.FtoR 0 ⟨1, 0⟩ - Source.FtoR 0 ⟨0, -1⟩ := by
  norm_num [Source.FtoR, Source.Fminus, Source.Fplus, Source.Fopp]

#print axioms zero_radix_is_not_an_addition_model
#print axioms zero_radix_is_not_a_subtraction_model
#print axioms Source.Fplus_correct
#print axioms Source.Fminus_correct

end PffBasicSourceContracts
