import FloatSpec.src.Pff.SourceFacade

/-!
The source-facing Pff rounding function is total at every integer radix.
Rocq Stdlib's logarithm is zero at nonpositive inputs, whereas Lean's logarithm
uses absolute value. These closed regressions separate that convention from
the positive-radix domain where ordinary rounding theorems apply.
-/

namespace FloatSpec.Test.PffLogTotality

open FloatSpec.Pff

private def bound : Source.Fbound := ⟨4, 0, by decide⟩

/-- The formula before the Rocq logarithm convention was restored. -/
private noncomputable def previousLogFormula (b : Source.Fbound) (radix : Int)
    (precision : Nat) (r : Real) : Source.float :=
  let firstNormPosValue := Source.FtoR radix (Source.firstNormalPos radix b precision)
  if firstNormPosValue ≤ r then
    let e : Int := IRNDD (Real.log r / Real.log (radix : Real) +
      (-(precision : Int) + 1 : Int))
    ⟨IRNDD (r * (radix : Real) ^ (-e)), e⟩
  else
    ⟨IRNDD (r * (radix : Real) ^ (b.dExp : Int)), -(b.dExp : Int)⟩

/-- Pinned Rocq produces this raw record at radix minus two. -/
theorem negative_radix : Source.RND_Min_Pos bound (-2) 2 (2 : Real) = ⟨-4, -1⟩ := by
  norm_num [Source.RND_Min_Pos, Source.rocqLn, Source.firstNormalPos, Source.nNormMin,
    Source.FtoR, Zpower_nat, IRNDD, bound]

/-- The former formula gives a different raw representation on the same input. -/
theorem previous_negative_radix : previousLogFormula bound (-2) 2 (2 : Real) = ⟨2, 0⟩ := by
  have hlog : Real.log (2 : Real) ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  norm_num [previousLogFormula, Source.firstNormalPos, Source.nNormMin,
    Source.FtoR, Zpower_nat, IRNDD, Real.log_neg_eq_log, hlog, bound]

/-- Every positive-radix result is preserved, even for inputs below the normal
threshold; this is a universal closed theorem, not a sampled grid. -/
theorem positive_radix_preserved (b : Source.Fbound) (radix : Int)
    (precision : Nat) (r : Real) (hradix : 0 < radix) :
    Source.RND_Min_Pos b radix precision r = previousLogFormula b radix precision r := by
  have hrbase : (0 : Real) < (radix : Real) := by exact_mod_cast hradix
  have hfirst : 0 < Source.FtoR radix (Source.firstNormalPos radix b precision) := by
    unfold Source.FtoR Source.firstNormalPos Source.nNormMin Zpower_nat
    positivity
  unfold Source.RND_Min_Pos previousLogFormula
  by_cases hnormal : Source.FtoR radix (Source.firstNormalPos radix b precision) ≤ r
  · have hr : 0 < r := hfirst.trans_le hnormal
    simp [hnormal, Source.rocqLn, hr, hrbase]
  · simp [hnormal]

/-- The numerator also follows Rocq's convention on a negative real input. -/
theorem negative_radix_negative_input :
    Source.RND_Min_Pos bound (-2) 2 (-2 : Real) = ⟨4, -1⟩ := by
  norm_num [Source.RND_Min_Pos, Source.rocqLn, Source.firstNormalPos, Source.nNormMin,
    Source.FtoR, Zpower_nat, IRNDD, bound]

#print axioms negative_radix
#print axioms previous_negative_radix
#print axioms positive_radix_preserved
#print axioms negative_radix_negative_input

end FloatSpec.Test.PffLogTotality
