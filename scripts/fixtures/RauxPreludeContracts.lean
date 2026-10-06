import FloatSpec.src.Core.Raux

namespace RauxPreludeContracts
open FloatSpec.Core.Raux

-- Raux.v:26-344, sections Rmissing and IZR. Rocq's `Rabs`, `Rmin`/`Rmax`, `x²`, `/x`,
-- `exp`, `sqrt` and `IZR` are Lean's `|·|`, `min`/`max`, `x * x`, `x⁻¹`, `Real.exp`,
-- `Real.sqrt` and the integer cast.
theorem le_0_minus : ∀ x y : ℝ, x ≤ y → 0 ≤ y - x := Rle_0_minus
theorem abs_eq_abs : ∀ x y : ℝ, |x| = |y| → x = y ∨ x = -y := Rabs_eq_Rabs
theorem abs_minus_le : ∀ x y : ℝ, 0 ≤ y → y ≤ 2 * x → |x - y| ≤ x := Rabs_minus_le
theorem abs_eq_0 : ∀ x : ℝ, |x| = 0 → x = 0 := Rabs_eq_R0
theorem mult_lt_compat : ∀ r1 r2 r3 r4 : ℝ, 0 ≤ r1 → 0 ≤ r3 → r1 < r2 → r3 < r4 →
    r1 * r3 < r2 * r4 := Rmult_lt_compat
theorem mult_neq_reg_r : ∀ r1 r2 r3 : ℝ, r2 * r1 ≠ r3 * r1 → r2 ≠ r3 := Rmult_neq_reg_r
theorem mult_neq_compat_r : ∀ r1 r2 r3 : ℝ, r1 ≠ 0 → r2 ≠ r3 → r2 * r1 ≠ r3 * r1 :=
  Rmult_neq_compat_r
theorem mult_min_distr_r : ∀ r r1 r2 : ℝ, 0 ≤ r → min r1 r2 * r = min (r1 * r) (r2 * r) :=
  Rmult_min_distr_r
theorem mult_min_distr_l : ∀ r r1 r2 : ℝ, 0 ≤ r → r * min r1 r2 = min (r * r1) (r * r2) :=
  Rmult_min_distr_l
theorem min_opp : ∀ x y : ℝ, min (-x) (-y) = -max x y := Rmin_opp
theorem max_opp : ∀ x y : ℝ, max (-x) (-y) = -min x y := Rmax_opp
theorem exp_mono : ∀ x y : ℝ, x ≤ y → Real.exp x ≤ Real.exp y := exp_le
theorem inv_lt : ∀ x y : ℝ, 0 < x → x < y → y⁻¹ < x⁻¹ := Rinv_lt
theorem inv_le : ∀ x y : ℝ, 0 < x → x ≤ y → y⁻¹ ≤ x⁻¹ := Rinv_le
theorem sqrt_nonneg : ∀ x : ℝ, 0 ≤ Real.sqrt x := sqrt_ge_0
theorem sqrt_nonpos : ∀ x : ℝ, x ≤ 0 → Real.sqrt x = 0 := sqrt_neg
theorem sqr_le_abs : ∀ x y : ℝ, x * x ≤ y * y → x ≤ |y| := Rsqr_le_abs_0_alt
theorem abs_le_inv : ∀ x y : ℝ, |x| ≤ y → -y ≤ x ∧ x ≤ y := Rabs_le_inv
theorem abs_ge : ∀ x y : ℝ, y ≤ -x ∨ x ≤ y → x ≤ |y| := Rabs_ge
theorem abs_ge_inv : ∀ x y : ℝ, x ≤ |y| → y ≤ -x ∨ x ≤ y := Rabs_ge_inv
theorem abs_lt : ∀ x y : ℝ, -y < x ∧ x < y → |x| < y := Rabs_lt
theorem abs_lt_inv : ∀ x y : ℝ, |x| < y → -y < x ∧ x < y := Rabs_lt_inv
theorem abs_gt : ∀ x y : ℝ, y < -x ∨ x < y → x < |y| := Rabs_gt
theorem abs_gt_inv : ∀ x y : ℝ, x < |y| → y < -x ∨ x < y := Rabs_gt_inv
theorem izr_le_lt : ∀ m n p : Int, m ≤ n ∧ n < p → (m : ℝ) ≤ n ∧ (n : ℝ) < p := IZR_le_lt
theorem le_lt_izr : ∀ m n p : Int, (m : ℝ) ≤ n ∧ (n : ℝ) < p → m ≤ n ∧ n < p := le_lt_IZR
theorem neq_izr : ∀ m n : Int, (m : ℝ) ≠ n → m ≠ n := neq_IZR

#print axioms mult_lt_compat
#print axioms inv_lt
#print axioms neq_izr

-- Each premise below is necessary.
private theorem abs_minus_le_needs_nonneg :
    ¬ ∀ x y : ℝ, y ≤ 2 * x → |x - y| ≤ x := by
  intro h
  have := h 0 (-1) (by norm_num)
  norm_num at this

private theorem abs_minus_le_needs_upper :
    ¬ ∀ x y : ℝ, 0 ≤ y → |x - y| ≤ x := by
  intro h
  have := h 0 1 (by norm_num)
  norm_num at this

private theorem mult_lt_compat_needs_nonneg :
    ¬ ∀ r1 r2 r3 r4 : ℝ, 0 ≤ r3 → r1 < r2 → r3 < r4 → r1 * r3 < r2 * r4 := by
  intro h
  have := h (-2) (-1) 1 2 (by norm_num) (by norm_num) (by norm_num)
  norm_num at this

private theorem mult_neq_compat_needs_nonzero :
    ¬ ∀ r1 r2 r3 : ℝ, r2 ≠ r3 → r2 * r1 ≠ r3 * r1 := by
  intro h
  exact h 0 0 1 (by norm_num) (by norm_num)

private theorem mult_min_distr_needs_nonneg :
    ¬ ∀ r r1 r2 : ℝ, min r1 r2 * r = min (r1 * r) (r2 * r) := by
  intro h
  have := h (-1) 0 1
  norm_num at this

private theorem inv_lt_needs_pos : ¬ ∀ x y : ℝ, x < y → y⁻¹ < x⁻¹ := by
  intro h
  have := h (-1) 1 (by norm_num)
  norm_num at this

#print axioms abs_minus_le_needs_nonneg
#print axioms inv_lt_needs_pos

end RauxPreludeContracts
