import FloatSpec.src.Core.FTZ

/-! Regression checks for the source-shaped flush-to-zero format contract. -/

namespace FloatSpec.Test.FTZSourceShape

open FloatSpec.Core.Defs FloatSpec.Core.FTZ

example (prec emin beta : Int) [Fact (0 < prec)] [ValidRadix beta] (x : ℝ) :
    FTZ_format prec emin beta x ↔
      ∃ f : FlocqFloat beta,
        x = F2R f ∧
          (x ≠ 0 →
            FloatSpec.Core.Zaux.Zpower beta (prec - 1) ≤ |f.Fnum| ∧
            |f.Fnum| < FloatSpec.Core.Zaux.Zpower beta prec) ∧
          emin ≤ f.Fexp := Iff.rfl

example (prec emin beta : Int) [Fact (0 < prec)] [ValidRadix beta] :
    FTZ_format prec emin beta (0 : ℝ) := by
  refine ⟨⟨0, emin⟩, ?_, ?_, le_rfl⟩
  · simp [F2R]
  · intro h
    exact (h rfl).elim

example (prec emin beta : Int) [Fact (0 < prec)] [ValidRadix beta] (x : ℝ)
    (hx : FTZ_format prec emin beta x) : FloatSpec.Core.FLX.FLXN_format prec beta x :=
  FLXN_format_FTZ (prec := prec) (emin := emin) beta x hx

end FloatSpec.Test.FTZSourceShape
