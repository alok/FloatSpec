import FloatSpec.src.Core.Raux

namespace RauxMagContracts
open FloatSpec.Core.Raux

-- Raux.v:1583-2153. Rocq's `mag x` is a dependent `mag_prop x` record coerced to `Z`; Lean's
-- `mag beta x` is that integer (cutover plan E7) and the record keeps the source fields. The
-- body is the source's witness. Rocq closes `mag` with `Qed`, so only Lean can evaluate it,
-- for instance at zero.
theorem raux_mag_contracts_check_1 (beta : Int) (x : ℝ) :
    mag beta x = Zfloor (Real.log |x| / Real.log (beta : ℝ)) + 1 := rfl
theorem raux_mag_contracts_check_2 (beta : Int) : mag beta 0 = 1 := by simp [mag, Zfloor]

-- The record: an exponent and, for nonzero inputs, its two-sided power bound.
def raux_mag_contracts_check_3 (beta : Int) (x : ℝ) (m : mag_prop beta x) : Int := m.mag_val
theorem raux_mag_contracts_check_4 (beta : Int) (x : ℝ) (m : mag_prop beta x) (hx : x ≠ 0) :
    bpow beta (m.mag_val - 1) ≤ |x| ∧ |x| < bpow beta m.mag_val := m.mag_spec hx

theorem lt_bpow_bpow : ∀ beta e1 e2 : Int, 1 < beta → bpow beta (e1 - 1) < bpow beta e2 → e1 ≤ e2 :=
  bpow_lt_bpow
theorem unique_exp : ∀ (beta : Int) (x : ℝ) (e1 e2 : Int), 1 < beta →
    bpow beta (e1 - 1) ≤ x ∧ x < bpow beta e1 → bpow beta (e2 - 1) ≤ x ∧ x < bpow beta e2 →
    e1 = e2 := bpow_unique
theorem unique : ∀ (beta : Int) (x : ℝ) (e : Int), 1 < beta →
    bpow beta (e - 1) ≤ |x| ∧ |x| < bpow beta e → mag beta x = e := mag_unique
theorem opp : ∀ (beta : Int) (x : ℝ), 1 < beta → mag beta (-x) = mag beta x := mag_opp
theorem abs' : ∀ (beta : Int) (x : ℝ), 1 < beta → mag beta |x| = mag beta x := mag_abs
theorem unique_pos : ∀ (beta : Int) (x : ℝ) (e : Int), 1 < beta →
    bpow beta (e - 1) ≤ x ∧ x < bpow beta e → mag beta x = e := mag_unique_pos
theorem le_abs : ∀ (beta : Int) (x y : ℝ), 1 < beta → x ≠ 0 → |x| ≤ |y| →
    mag beta x ≤ mag beta y := mag_le_abs
theorem le : ∀ (beta : Int) (x y : ℝ), 1 < beta → 0 < x → x ≤ y → mag beta x ≤ mag beta y := mag_le
theorem lt : ∀ (beta : Int) (x y : ℝ), 1 < beta → 0 < y → mag beta x < mag beta y → x < y := lt_mag
theorem of_bpow : ∀ beta e : Int, 1 < beta → mag beta (bpow beta e) = e + 1 := mag_bpow
theorem mult_bpow : ∀ (beta : Int) (x : ℝ) (e : Int), 1 < beta → x ≠ 0 →
    mag beta (x * bpow beta e) = mag beta x + e := mag_mult_bpow
theorem le_bpow : ∀ (beta : Int) (x : ℝ) (e : Int), 1 < beta → x ≠ 0 → |x| < bpow beta e →
    mag beta x ≤ e := mag_le_bpow
theorem gt_bpow : ∀ (beta : Int) (x : ℝ) (e : Int), 1 < beta → bpow beta e ≤ |x| →
    e < mag beta x := mag_gt_bpow
theorem ge_bpow : ∀ (beta : Int) (x : ℝ) (e : Int), 1 < beta → bpow beta (e - 1) ≤ |x| →
    e ≤ mag beta x := mag_ge_bpow
theorem upper : ∀ (beta : Int) (x : ℝ), 1 < beta → |x| < bpow beta (mag beta x) := bpow_mag_gt
theorem lower : ∀ (beta : Int) (x : ℝ), 1 < beta → x ≠ 0 → bpow beta (mag beta x - 1) ≤ |x| :=
  bpow_mag_le
theorem le_Zpower : ∀ beta m e : Int, 1 < beta → m ≠ 0 → |m| < FloatSpec.Core.Zaux.Zpower beta e →
    mag beta (m : ℝ) ≤ e := mag_le_Zpower
theorem gt_Zpower : ∀ beta m e : Int, 1 < beta → m ≠ 0 → FloatSpec.Core.Zaux.Zpower beta e ≤ |m| →
    e < mag beta (m : ℝ) := mag_gt_Zpower
theorem mult : ∀ (beta : Int) (x y : ℝ), 1 < beta → x ≠ 0 → y ≠ 0 →
    mag beta x + mag beta y - 1 ≤ mag beta (x * y) ∧ mag beta (x * y) ≤ mag beta x + mag beta y :=
  mag_mult
theorem plus : ∀ (beta : Int) (x y : ℝ), 1 < beta → 0 < y → y ≤ x →
    mag beta x ≤ mag beta (x + y) ∧ mag beta (x + y) ≤ mag beta x + 1 := mag_plus
theorem minus : ∀ (beta : Int) (x y : ℝ), 1 < beta → 0 < y → y < x →
    mag beta (x - y) ≤ mag beta x := mag_minus
theorem minus_lb : ∀ (beta : Int) (x y : ℝ), 1 < beta → 0 < x → 0 < y →
    mag beta y ≤ mag beta x - 2 → mag beta x - 1 ≤ mag beta (x - y) := mag_minus_lb
theorem plus_ge : ∀ (beta : Int) (x y : ℝ), 1 < beta → x ≠ 0 →
    mag beta y ≤ mag beta x - 2 → mag beta x - 1 ≤ mag beta (x + y) := mag_plus_ge
theorem div : ∀ (beta : Int) (x y : ℝ), 1 < beta → x ≠ 0 → y ≠ 0 →
    mag beta x - mag beta y ≤ mag beta (x / y) ∧ mag beta (x / y) ≤ mag beta x - mag beta y + 1 :=
  mag_div
-- Rocq's `Z.div2` rounds down, as Lean's `/ 2` does for this nonnegative divisor.
theorem sqrt : ∀ (beta : Int) (x : ℝ), 1 < beta → 0 < x →
    mag beta (Real.sqrt x) = (mag beta x + 1) / 2 := mag_sqrt
theorem one : ∀ beta : Int, 1 < beta → mag beta 1 = 1 := mag_1

#print axioms unique
#print axioms mult
#print axioms sqrt

-- Concrete magnitudes: 1000 has four decimal digits, 7/4 lies in [1, 2).
theorem raux_mag_contracts_check_5 : mag 10 1000 = 4 ∧ mag 2 (7/4) = 1 := by
  constructor
  · exact mag_unique 10 1000 4 (by norm_num) ⟨by norm_num [bpow], by norm_num [bpow]⟩
  · exact mag_unique 2 (7/4) 1 (by norm_num) ⟨by norm_num [bpow], by norm_num [bpow]⟩

-- Positivity premises are needed: magnitude ignores sign, order does not.
private theorem le_needs_pos : ¬ ∀ x y : ℝ, x ≤ y → mag 10 x ≤ mag 10 y := by
  intro h
  have := h (-10) 1 (by norm_num)
  rw [mag_unique 10 (-10) 2 (by norm_num) ⟨by norm_num [bpow], by norm_num [bpow]⟩,
    mag_unique 10 1 1 (by norm_num) ⟨by norm_num [bpow], by norm_num [bpow]⟩] at this
  exact absurd this (by decide)

private theorem lt_needs_pos : ¬ ∀ x y : ℝ, mag 10 x < mag 10 y → x < y := by
  intro h
  have := h 1 (-10) (by
    rw [mag_unique 10 (-10) 2 (by norm_num) ⟨by norm_num [bpow], by norm_num [bpow]⟩,
      mag_unique 10 1 1 (by norm_num) ⟨by norm_num [bpow], by norm_num [bpow]⟩]
    decide)
  norm_num at this

#print axioms le_needs_pos

end RauxMagContracts
