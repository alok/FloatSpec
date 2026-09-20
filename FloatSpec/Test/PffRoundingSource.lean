import FloatSpec.src.Pff.SourceFacade

/-! Closed source-facing real-rounding regressions. These are kernel-checked
mathematical statements, not native execution of real logarithms. -/

namespace FloatSpec.Test.PffRoundingSource

open FloatSpec.Pff

private def bound : Source.Fbound := ⟨9, 0, by decide⟩
private noncomputable def row (r : Real) : List Source.float :=
  [Source.RND_Min bound 3 2 r, Source.RND_Max bound 3 2 r,
    Source.RND_EvenClosest bound 3 2 r]

/-- The odd lower mantissa loses the positive halfway tie. -/
theorem positive_half : row (3 / 2) = [⟨1, 0⟩, ⟨2, 0⟩, ⟨2, 0⟩] := by
  norm_num [row, Source.RND_EvenClosest, Source.RND_Max, Source.RND_Min,
    Source.RND_Max_Pos, Source.RND_Min_Pos, Source.firstNormalPos, Source.nNormMin,
    Source.FtoR, Source.FSucc, Source.Fopp, Zpower_nat, IRNDD, bound]

/-- The even lower mantissa wins the negative halfway tie. -/
theorem negative_half : row (-3 / 2) = [⟨-2, 0⟩, ⟨-1, 0⟩, ⟨-2, 0⟩] := by
  norm_num [row, Source.RND_EvenClosest, Source.RND_Max, Source.RND_Min,
    Source.RND_Max_Pos, Source.RND_Min_Pos, Source.firstNormalPos, Source.nNormMin,
    Source.FtoR, Source.FSucc, Source.Fopp, Zpower_nat, IRNDD, bound]

/-- An even lower mantissa wins the positive halfway tie. -/
theorem even_lower_half : row (5 / 2) = [⟨2, 0⟩, ⟨3, 0⟩, ⟨2, 0⟩] := by
  norm_num [row, Source.RND_EvenClosest, Source.RND_Max, Source.RND_Min,
    Source.RND_Max_Pos, Source.RND_Min_Pos, Source.firstNormalPos, Source.nNormMin,
    Source.FtoR, Source.FSucc, Source.Fopp, Zpower_nat, IRNDD, bound]

/-- An odd lower mantissa loses the negative halfway tie. -/
theorem negative_odd_lower_half : row (-5 / 2) = [⟨-3, 0⟩, ⟨-2, 0⟩, ⟨-2, 0⟩] := by
  norm_num [row, Source.RND_EvenClosest, Source.RND_Max, Source.RND_Min,
    Source.RND_Max_Pos, Source.RND_Min_Pos, Source.firstNormalPos, Source.nNormMin,
    Source.FtoR, Source.FSucc, Source.Fopp, Zpower_nat, IRNDD, bound]

/-- Strictly closer to the lower result, without invoking parity. -/
theorem below_half : row (4 / 3) = [⟨1, 0⟩, ⟨2, 0⟩, ⟨1, 0⟩] := by
  norm_num [row, Source.RND_EvenClosest, Source.RND_Max, Source.RND_Min,
    Source.RND_Max_Pos, Source.RND_Min_Pos, Source.firstNormalPos, Source.nNormMin,
    Source.FtoR, Source.FSucc, Source.Fopp, Zpower_nat, IRNDD, bound]

/-- Strictly closer to the upper result, without invoking parity. -/
theorem above_half : row (5 / 3) = [⟨1, 0⟩, ⟨2, 0⟩, ⟨2, 0⟩] := by
  norm_num [row, Source.RND_EvenClosest, Source.RND_Max, Source.RND_Min,
    Source.RND_Max_Pos, Source.RND_Min_Pos, Source.firstNormalPos, Source.nNormMin,
    Source.FtoR, Source.FSucc, Source.Fopp, Zpower_nat, IRNDD, bound]

/-- An exact input keeps the same lower and upper record. -/
theorem exact_integer : row 2 = [⟨2, 0⟩, ⟨2, 0⟩, ⟨2, 0⟩] := by
  norm_num [row, Source.RND_EvenClosest, Source.RND_Max, Source.RND_Min,
    Source.RND_Max_Pos, Source.RND_Min_Pos, Source.firstNormalPos, Source.nNormMin,
    Source.FtoR, Source.FSucc, Source.Fopp, Zpower_nat, IRNDD, bound]

/-- Signed wrapper branching retains the source zero record. -/
theorem zero : row 0 = [⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩] := by
  norm_num [row, Source.RND_EvenClosest, Source.RND_Max, Source.RND_Min,
    Source.RND_Max_Pos, Source.RND_Min_Pos, Source.firstNormalPos, Source.nNormMin,
    Source.FtoR, Source.FSucc, Source.Fopp, Zpower_nat, IRNDD, bound]

/-- The total wrappers retain the corrected nonpositive-radix logarithm convention. -/
theorem negative_radix :
    let b : Source.Fbound := ⟨4, 0, by decide⟩
    [Source.RND_Min b (-2) 2 2, Source.RND_Max b (-2) 2 2,
      Source.RND_EvenClosest b (-2) 2 2] = [⟨-4, -1⟩, ⟨-4, -1⟩, ⟨-4, -1⟩] := by
  norm_num [Source.RND_EvenClosest, Source.RND_Max, Source.RND_Min,
    Source.RND_Max_Pos, Source.RND_Min_Pos, Source.firstNormalPos, Source.nNormMin,
    Source.FtoR, Source.FSucc, Source.Fopp, Source.rocqLn, Zpower_nat, IRNDD]

/-- Precision zero is outside rounding correctness premises, but the exported
definition still has these observable source results. -/
theorem zero_precision :
    let b : Source.Fbound := ⟨1, 0, by decide⟩
    [Source.RND_Min b 2 0 2, Source.RND_Max b 2 0 2,
      Source.RND_EvenClosest b 2 0 2] = [⟨0, 2⟩, ⟨1, 3⟩, ⟨0, 2⟩] := by
  have hlog : Real.log (2 : Real) ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  norm_num [Source.RND_EvenClosest, Source.RND_Max, Source.RND_Min,
    Source.RND_Max_Pos, Source.RND_Min_Pos, Source.firstNormalPos, Source.nNormMin,
    Source.FtoR, Source.FSucc, Source.Fopp, Source.rocqLn, Zpower_nat, IRNDD, hlog]

#print axioms positive_half
#print axioms negative_half
#print axioms even_lower_half
#print axioms negative_odd_lower_half
#print axioms below_half
#print axioms above_half
#print axioms exact_integer
#print axioms zero
#print axioms negative_radix
#print axioms zero_precision

end FloatSpec.Test.PffRoundingSource
