import FloatSpec.src.Pff.SourceFacade

/-! Typed clients for the unindexed source operations. Radix one is deliberately
accepted by multiplication correctness, while zero-observer laws have no radix premise. -/

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

end PffBasicSourceContracts
