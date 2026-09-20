import FloatSpec.src.Core.FTZ

/-! Regression checks for the source-shaped flush-to-zero format contract. -/

namespace FloatSpec.Test.FTZSourceShape

open FloatSpec.Core.Defs FloatSpec.Core.FTZ

example (prec emin beta : Int) [ValidRadix beta] (x : ℝ) :
    FTZ_format prec emin beta x ↔
      ∃ f : FlocqFloat beta,
        x = F2R f ∧
          (x ≠ 0 →
            FloatSpec.Core.Zaux.Zpower beta (prec - 1) ≤ |f.Fnum| ∧
            |f.Fnum| < FloatSpec.Core.Zaux.Zpower beta prec) ∧
          emin ≤ f.Fexp := Iff.rfl

/-- Zero has the source-shaped FTZ representation at every integer precision. -/
theorem zeroAtAnyPrecision (prec emin beta : Int) [ValidRadix beta] :
    FTZ_format prec emin beta (0 : ℝ) := by
  refine ⟨⟨0, emin⟩, ?_, ?_, le_rfl⟩
  · simp [F2R]
  · intro h
    exact (h rfl).elim

example (prec emin beta : Int) [ValidRadix beta] (x : ℝ)
    (hx : FTZ_format prec emin beta x) : FloatSpec.Core.FLX.FLXN_format prec beta x :=
  FLXN_format_FTZ (prec := prec) (emin := emin) beta x hx

example (prec emin beta : Int) [ValidRadix beta] :
    FloatSpec.Core.Generic_fmt.generic_format beta (FTZ_exp prec emin) 0 :=
  generic_format_FTZ prec emin beta 0 (zeroAtAnyPrecision prec emin beta)

end FloatSpec.Test.FTZSourceShape
