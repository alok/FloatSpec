import FloatSpec.Linter
/-
This file is part of the Flocq formalization of floating-point
arithmetic in Lean 4, ported from Coq: https://flocq.gitlabpages.inria.fr/

Original Copyright (C) 2011-2018 Sylvie Boldo
Original Copyright (C) 2011-2018 Guillaume Melquiond

This library is free software; you can redistribute it and/or
modify it under the terms of the GNU Lesser General Public
License as published by the Free Software Foundation; either
version 3 of the License, or (at your option) any later version.

This library is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
COPYING file for more details.
-/

import FloatSpec.src.Core.Zaux
import FloatSpecRoles  -- Register {coq} doc role
-- import Mathlib.Data.Real.Basic
-- import Mathlib.Data.Real.Sqrt
-- import Mathlib.Analysis.SpecialFunctions.Log.Basic
-- import Mathlib.Data.Nat.Find
-- import Mathlib.Tactic

open Real

namespace FloatSpec.Core.Raux

section Rmissing

/-- Coq {lit}`Rle_0_minus`: if {lit}`x ≤ y`, then {lit}`0 ≤ y - x`. -/
theorem Rle_0_minus (x y : ℝ) (hxy : x ≤ y) : 0 ≤ y - x :=
  sub_nonneg_of_le hxy

/-- Coq {lit}`Rabs_eq_Rabs`: equal absolute values give equality up to sign. -/
@[flocq_source "src/Core/Raux.v" 38 "Rabs_eq_Rabs"]
theorem Rabs_eq_Rabs (x y : ℝ) (hxy : |x| = |y|) : x = y ∨ x = -y :=
  abs_eq_abs.mp hxy

/-- Coq {lit}`Rabs_minus_le`: if {lit}`0 ≤ y` and {lit}`y ≤ 2 * x`, then
    {lit}`|x - y| ≤ x`. -/
@[flocq_source "src/Core/Raux.v" 56 "Rabs_minus_le"]
theorem Rabs_minus_le (x y : ℝ) (hy : 0 ≤ y) (hyx : y ≤ 2 * x) : |x - y| ≤ x := by
  have hx_upper : x - y ≤ x := sub_le_self x hy
  have hx_lower : -x ≤ x - y := by linarith
  exact abs_le.mpr ⟨hx_lower, hx_upper⟩

/-- Coq {lit}`Rabs_ge`: if {lit}`y ≤ -x ∨ x ≤ y`, then {lit}`x ≤ |y|`. -/
@[flocq_source "src/Core/Raux.v" 244 "Rabs_ge"]
theorem Rabs_ge (x y : ℝ) (h : y ≤ -x ∨ x ≤ y) : x ≤ |y| := by
  rcases h with h1 | h2
  · -- Case y ≤ -x ⇒ x ≤ |y|
    have hxle : x ≤ -y := by
      have := neg_le_neg h1
      simpa using this
    have h_abs : -y ≤ |y| := by
      simpa using (neg_le_abs y)
    exact hxle.trans h_abs
  · -- Case x ≤ y ⇒ x ≤ |y|
    exact h2.trans (le_abs_self y)

/-- Coq {lit}`Rabs_ge_inv`: if {lit}`x ≤ |y|`, then {lit}`y ≤ -x ∨ x ≤ y`. -/
@[flocq_source "src/Core/Raux.v" 258 "Rabs_ge_inv"]
theorem Rabs_ge_inv (x y : ℝ) (hx : x ≤ |y|) : y ≤ -x ∨ x ≤ y := by
  by_cases hy : 0 ≤ y
  · -- If y ≥ 0, then |y| = y and the goal reduces to x ≤ y
    have habs : |y| = y := abs_of_nonneg hy
    have hx' : x ≤ y := by simpa [habs] using hx
    exact Or.inr hx'
  · -- If y ≤ 0, then |y| = -y and from x ≤ -y we get y ≤ -x
    have hy' : y ≤ 0 := le_of_not_ge hy
    have habs : |y| = -y := abs_of_nonpos hy'
    have hx' : x ≤ -y := by simpa [habs] using hx
    have : y ≤ -x := by
      have := neg_le_neg hx'
      simpa using this
    exact Or.inl this

/-- Coq {lit}`Rabs_le_inv`: if {lit}`|x| ≤ y`, then {lit}`-y ≤ x ≤ y`. -/
@[flocq_source "src/Core/Raux.v" 229 "Rabs_le_inv"]
theorem Rabs_le_inv (x y : ℝ) (h : |x| ≤ y) : -y ≤ x ∧ x ≤ y :=
  abs_le.mp h

/-- Coq {lit}`Rmult_lt_compat`: multiplying nonnegative values preserves strict
    inequalities. -/
theorem Rmult_lt_compat (r1 r2 r3 r4 : ℝ) (h1 : 0 ≤ r1) (h3 : 0 ≤ r3)
    (h12 : r1 < r2) (h34 : r3 < r4) : r1 * r3 < r2 * r4 := by
  by_cases hr3 : r3 = 0
  · subst hr3
    simp
    exact mul_pos (h1.trans_lt h12) h34
  · have h3_pos : 0 < r3 := lt_of_le_of_ne h3 (Ne.symm hr3)
    exact mul_lt_mul h12 (le_of_lt h34) h3_pos (le_of_lt (h1.trans_lt h12))

/-- Coq {lit}`Rmult_neq_reg_r`: if {lit}`r2 * r1 ≠ r3 * r1`, then {lit}`r2 ≠ r3`. -/
theorem Rmult_neq_reg_r (r1 r2 r3 : ℝ) (h : r2 * r1 ≠ r3 * r1) : r2 ≠ r3 := by
  intro h_eq
  exact h (by rw [h_eq])

/-- Coq {lit}`Rmult_neq_compat_r`: if {lit}`r1 ≠ 0` and {lit}`r2 ≠ r3`, then
    {lit}`r2 * r1 ≠ r3 * r1`. -/
theorem Rmult_neq_compat_r (r1 r2 r3 : ℝ) (h1 : r1 ≠ 0) (h23 : r2 ≠ r3) :
    r2 * r1 ≠ r3 * r1 :=
  fun h => h23 (mul_right_cancel₀ h1 h)

/-- Coq {lit}`Rmult_min_distr_r`: if {lit}`0 ≤ r`, then
    {lit}`min r1 r2 * r = min (r1 * r) (r2 * r)`. -/
theorem Rmult_min_distr_r (r r1 r2 : ℝ) (h : 0 ≤ r) :
    min r1 r2 * r = min (r1 * r) (r2 * r) :=
  min_mul_of_nonneg r1 r2 h

/-- Coq {lit}`Rmult_min_distr_l`: if {lit}`0 ≤ r`, then
    {lit}`r * min r1 r2 = min (r * r1) (r * r2)`. -/
theorem Rmult_min_distr_l (r r1 r2 : ℝ) (h : 0 ≤ r) :
    r * min r1 r2 = min (r * r1) (r * r2) :=
  mul_min_of_nonneg r1 r2 h

/-- Coq {lit}`Rmin_opp`: {lit}`min (-x) (-y) = -(max x y)`. -/
theorem Rmin_opp (x y : ℝ) : min (-x) (-y) = -(max x y) :=
  min_neg_neg x y

/-- Coq {lit}`Rmax_opp`: {lit}`max (-x) (-y) = -(min x y)`. -/
theorem Rmax_opp (x y : ℝ) : max (-x) (-y) = -(min x y) :=
  max_neg_neg x y

/-- Coq {lit}`exp_le`: the real exponential is monotone. -/
theorem exp_le (x y : ℝ) (hxy : x ≤ y) : Real.exp x ≤ Real.exp y :=
  Real.exp_le_exp.mpr hxy

end Rmissing

section IZR

/-- Coq {lit}`IZR_le_lt`: integer bounds {lit}`m ≤ n < p` transfer to the real casts. -/
@[flocq_source "src/Core/Raux.v" 318 "IZR_le_lt"]
theorem IZR_le_lt (m n p : Int) (h : m ≤ n ∧ n < p) :
    (m : ℝ) ≤ (n : ℝ) ∧ (n : ℝ) < (p : ℝ) :=
  ⟨Int.cast_mono h.1, Int.cast_strictMono h.2⟩

/-- Coq {lit}`le_lt_IZR`: real-cast bounds {lit}`m ≤ n < p` reflect to the integers. -/
@[flocq_source "src/Core/Raux.v" 327 "le_lt_IZR"]
theorem le_lt_IZR (m n p : Int) (h : (m : ℝ) ≤ (n : ℝ) ∧ (n : ℝ) < (p : ℝ)) :
    m ≤ n ∧ n < p :=
  ⟨Int.cast_le.1 h.1, Int.cast_lt.1 h.2⟩

/-- Coq {lit}`neq_IZR`: unequal real casts come from unequal integers. -/
theorem neq_IZR (m n : Int) (hmnR : (m : ℝ) ≠ (n : ℝ)) : m ≠ n :=
  fun hmn => hmnR (by simp [hmn])

end IZR

section Rrecip

/-- Coq {lit}`Rinv_lt`: the reciprocal reverses strict order on positive reals. -/
@[flocq_source "src/Core/Raux.v" 172 "Rinv_lt"]
theorem Rinv_lt (x y : ℝ) (hx : 0 < x) (hxy : x < y) : y⁻¹ < x⁻¹ :=
  inv_strictAnti₀ hx hxy

/-- Coq {lit}`Rinv_le`: the reciprocal is antitone on positive reals. -/
@[flocq_source "src/Core/Raux.v" 184 "Rinv_le"]
theorem Rinv_le (x y : ℝ) (hx : 0 < x) (hxy : x ≤ y) : y⁻¹ ≤ x⁻¹ :=
  inv_anti₀ hx hxy

end Rrecip

section Sqrt

/-- Coq {lit}`sqrt_ge_0`: the real square root is nonnegative. -/
theorem sqrt_ge_0 (x : ℝ) : 0 ≤ Real.sqrt x :=
  Real.sqrt_nonneg x

/-- Coq {lit}`sqrt_neg`: the square root of a nonpositive real is zero. -/
@[flocq_source "src/Core/Raux.v" 206 "sqrt_neg"]
theorem sqrt_neg (x : ℝ) (hx : x ≤ 0) : Real.sqrt x = 0 :=
  Real.sqrt_eq_zero_of_nonpos hx

end Sqrt

section Abs

/-- Coq {lit}`Rabs_eq_R0`: a real with zero absolute value is zero. -/
@[flocq_source "src/Core/Raux.v" 66 "Rabs_eq_R0"]
theorem Rabs_eq_R0 (x : ℝ) : |x| = 0 → x = 0 :=
  abs_eq_zero.mp

end Abs

section Squares

/-- Coq {lit}`Rsqr_le_abs_0_alt`: from {lit}`x² ≤ y²`, deduce {lit}`x ≤ |y|`.
    Coq's {lit}`x²` is {lit}`Rsqr x`, defined as {lit}`x * x`; Lean has no
    {lit}`Rsqr`, so the statement uses that body, as {name}`Rcompare_sqr` does. -/
@[flocq_source "src/Core/Raux.v" 221 "Rsqr_le_abs_0_alt"]
theorem Rsqr_le_abs_0_alt (x y : ℝ) (hxy : x * x ≤ y * y) : x ≤ |y| :=
  le_trans (le_abs_self x) (abs_le_iff_mul_self_le.mpr hxy)

end Squares

section AbsMore

/-- Coq {lit}`Rabs_lt`: if {lit}`-y < x < y`, then {lit}`|x| < y`. -/
theorem Rabs_lt (x y : ℝ) (h : -y < x ∧ x < y) : |x| < y := by
  exact abs_lt.mpr h

end AbsMore

section AbsGt

/-- Coq `Rabs_gt`: the disjunctive characterization implies the strict
absolute-value bound. -/
theorem Rabs_gt (x y : ℝ) (h : y < -x ∨ x < y) : x < |y| := by
  rcases h with h | h
  · have hxy : x < -y := by simpa using neg_lt_neg h
    exact hxy.trans_le (by simpa using neg_le_abs y)
  · exact h.trans_le (le_abs_self y)

end AbsGt

section AbsGtInv

/-- Coq `Rabs_gt_inv`: if `x < |y|`, then `y < -x` or `x < y`. -/
theorem Rabs_gt_inv (x y : ℝ) (h : x < |y|) : y < -x ∨ x < y := by
  by_cases hy : 0 ≤ y
  · right
    simpa [abs_of_nonneg hy] using h
  · left
    have hy_nonpos : y ≤ 0 := le_of_not_ge hy
    have hx_neg : x < -y := by
      simpa [abs_of_nonpos hy_nonpos] using h
    simpa using (neg_lt_neg hx_neg)

/-- Converse direction of {lean}`Rabs_gt_inv`: if {lit}`y < x ∨ y < -x`, then
    {lit}`y < |x|`. -/
theorem Rabs_gt_inv_spec (x y : ℝ) (h : y < x ∨ y < -x) : y < |x| := by
  rcases h with hxy | hxny
  · exact lt_of_lt_of_le hxy (le_abs_self x)
  · exact lt_of_lt_of_le hxny (by simpa using (neg_le_abs x))

end AbsGtInv

section Rcompare

/-- Three-way comparison for real numbers

    Returns -1 if x < y, 0 if x = y, and 1 if x > y.
    This provides a complete ordering comparison in one operation.
-/
noncomputable def Rcompare (x y : ℝ) : Int :=
  (if x < y then -1
        else if x = y then 0
        else 1)

/-- Coq {lit}`Rcompare_prop`: inductive characterization of {lean}`Rcompare` codes. -/
inductive Rcompare_prop (x y : ℝ) : Int → Prop where
  | Rcompare_Lt_ : x < y → Rcompare_prop x y (-1)
  | Rcompare_Eq_ : x = y → Rcompare_prop x y 0
  | Rcompare_Gt_ : y < x → Rcompare_prop x y 1

export Rcompare_prop (Rcompare_Lt_ Rcompare_Eq_ Rcompare_Gt_)

/-- Coq-style spec: {lit}`Rcompare_prop` holds for {lean}`Rcompare`. -/
theorem Rcompare_prop_spec (x y : ℝ) : Rcompare_prop x y (Rcompare x y) := by
  by_cases hxy : x < y
  · simpa [Rcompare, hxy] using (Rcompare_Lt_ (x := x) (y := y) hxy)
  · by_cases hxeq : x = y
    · subst hxeq
      simpa [Rcompare, hxy] using (Rcompare_Eq_ (x := x) (y := x) rfl)
    · have hyx : y < x := lt_of_le_of_ne (le_of_not_gt hxy) (Ne.symm hxeq)
      simpa [Rcompare, hxy, hxeq, hyx] using (Rcompare_Gt_ (x := x) (y := y) hyx)

/-- Three-way comparison correctness: the code is {lit}`-1`, {lit}`0`, or {lit}`1`
    exactly when {lit}`x < y`, {lit}`x = y`, or {lit}`y < x`. -/
theorem Rcompare_spec (x y : ℝ) :
    (Rcompare x y = -1 ↔ x < y) ∧
      (Rcompare x y = 0 ↔ x = y) ∧
      (Rcompare x y = 1 ↔ y < x) := by
  unfold Rcompare
  by_cases hxy : x < y
  · have hne : x ≠ y := ne_of_lt hxy
    have hnotyx : ¬ y < x := not_lt_of_ge (le_of_lt hxy)
    simp [hxy, hne, hnotyx]
  · by_cases hxeq : x = y
    · subst hxeq
      simp
    · have hyx : y < x := lt_of_le_of_ne (le_of_not_gt hxy) (Ne.symm hxeq)
      simp [hxy, hxeq, hyx]

/-- Coq `Rcompare_sym`: swapping the operands reverses the comparison. -/
theorem Rcompare_sym (x y : ℝ) : Rcompare x y = -(Rcompare y x) := by
  rcases lt_trichotomy x y with hxy | hxy | hyx
  · have hnxy : ¬ y < x := not_lt_of_ge hxy.le
    have hne : x ≠ y := ne_of_lt hxy
    simp [Rcompare, hxy, hnxy, hne, hne.symm]
  · subst y
    simp [Rcompare]
  · have hnyx : ¬ x < y := not_lt_of_ge hyx.le
    have hne : x ≠ y := ne_of_gt hyx
    simp [Rcompare, hyx, hnyx, hne, hne.symm]

/-- Coq `Rcompare_opp`: negating both operands reverses the comparison. -/
theorem Rcompare_opp (x y : ℝ) : Rcompare (-x) (-y) = Rcompare y x := by
  rcases lt_trichotomy x y with hxy | hxy | hyx
  · have hnxy : ¬ y < x := not_lt_of_ge hxy.le
    have hne : x ≠ y := ne_of_lt hxy
    simp [Rcompare, hxy, hnxy, hne, hne.symm]
  · subst y
    simp [Rcompare]
  · have hnyx : ¬ x < y := not_lt_of_ge hyx.le
    have hne : x ≠ y := ne_of_gt hyx
    simp [Rcompare, hyx, hnyx, hne, hne.symm]

/-- Coq `Rcompare_plus_r`: right translation preserves comparison. -/
theorem Rcompare_plus_r (z x y : ℝ) :
    Rcompare (x + z) (y + z) = Rcompare x y := by
  simp [Rcompare]

/-- Coq `Rcompare_plus_l`: left translation preserves comparison. -/
theorem Rcompare_plus_l (z x y : ℝ) :
    Rcompare (z + x) (z + y) = Rcompare x y := by
  simp [Rcompare]

/-- Coq `Rcompare_mult_r`: right multiplication by a positive value preserves comparison. -/
theorem Rcompare_mult_r (z x y : ℝ) (hz : 0 < z) :
    Rcompare (x * z) (y * z) = Rcompare x y := by
  have hz0 : z ≠ 0 := ne_of_gt hz
  have hlt : x * z < y * z ↔ x < y := by
    constructor
    · intro h
      exact lt_of_mul_lt_mul_right h (le_of_lt hz)
    · intro h
      exact mul_lt_mul_of_pos_right h hz
  have heq : x * z = y * z ↔ x = y := by
    constructor
    · intro h
      exact mul_right_cancel₀ hz0 h
    · intro h
      rw [h]
  simp only [Rcompare, hlt, heq]

/-- Coq `Rcompare_mult_l`: left multiplication by a positive value preserves comparison. -/
theorem Rcompare_mult_l (z x y : ℝ) (hz : 0 < z) :
    Rcompare (z * x) (z * y) = Rcompare x y := by
  have hz0 : z ≠ 0 := ne_of_gt hz
  have hlt : z * x < z * y ↔ x < y := by
    constructor
    · intro h
      exact lt_of_mul_lt_mul_right (by simpa [mul_comm] using h) (le_of_lt hz)
    · intro h
      simpa [mul_comm] using mul_lt_mul_of_pos_right h hz
  have heq : z * x = z * y ↔ x = y := by
    constructor
    · intro h
      exact mul_left_cancel₀ hz0 h
    · intro h
      rw [h]
  simp only [Rcompare, hlt, heq]

end Rcompare

section RcompareMore

/-- Source strict-order proposition, expressed in the legacy integer encoding
of comparison: Lt is -1, Eq is 0, and Gt is 1. -/
@[flocq_source "src/Core/Raux.v" 371 "Rcompare_Lt"]
theorem Rcompare_Lt (x y : ℝ) (hxy : x < y) : Rcompare x y = -1 := by
  simp [Rcompare, hxy]

/-- Source equality proposition in the legacy comparison encoding. -/
@[flocq_source "src/Core/Raux.v" 411 "Rcompare_Eq"]
theorem Rcompare_Eq (x y : ℝ) (hxy : x = y) : Rcompare x y = 0 := by
  subst y
  simp [Rcompare]

/-- Source reverse strict-order proposition in the legacy comparison encoding. -/
@[flocq_source "src/Core/Raux.v" 428 "Rcompare_Gt"]
theorem Rcompare_Gt (x y : ℝ) (hyx : y < x) : Rcompare x y = 1 := by
  simp [Rcompare, not_lt_of_ge hyx.le, ne_of_gt hyx]

/-- Source non-Lt proposition in the legacy comparison encoding. -/
@[flocq_source "src/Core/Raux.v" 392 "Rcompare_not_Lt"]
theorem Rcompare_not_Lt (x y : ℝ) (hyx : y ≤ x) : Rcompare x y ≠ -1 := by
  simp [Rcompare, not_lt_of_ge hyx]
  split_ifs <;> norm_num

/-- Source non-Gt proposition in the legacy comparison encoding. -/
@[flocq_source "src/Core/Raux.v" 449 "Rcompare_not_Gt"]
theorem Rcompare_not_Gt (x y : ℝ) (hxy : x ≤ y) : Rcompare x y ≠ 1 := by
  rcases lt_or_eq_of_le hxy with h | h
  · simp [Rcompare, h]
  · subst y; simp [Rcompare]

/-- Coq {lit}`Rcompare_Lt_inv`: the Lt code {lit}`-1` implies {lit}`x < y`. -/
theorem Rcompare_Lt_inv (x y : ℝ) (h : Rcompare x y = -1) : x < y :=
  (Rcompare_spec x y).1.mp h

/-- Coq {lit}`Rcompare_not_Lt_inv`: a code other than {lit}`-1` implies {lit}`y ≤ x`. -/
theorem Rcompare_not_Lt_inv (x y : ℝ) (h : Rcompare x y ≠ -1) : y ≤ x :=
  not_lt.mp fun hxy => h ((Rcompare_spec x y).1.mpr hxy)

/-- Coq {lit}`Rcompare_Eq_inv`: the Eq code {lit}`0` implies {lit}`x = y`. -/
theorem Rcompare_Eq_inv (x y : ℝ) (h : Rcompare x y = 0) : x = y :=
  (Rcompare_spec x y).2.1.mp h

/-- Coq {lit}`Rcompare_Gt_inv`: the Gt code {lit}`1` implies {lit}`y < x`. -/
theorem Rcompare_Gt_inv (x y : ℝ) (h : Rcompare x y = 1) : y < x :=
  (Rcompare_spec x y).2.2.mp h

/-- Coq {lit}`Rcompare_not_Gt_inv`: a code other than {lit}`1` implies {lit}`x ≤ y`. -/
theorem Rcompare_not_Gt_inv (x y : ℝ) (h : Rcompare x y ≠ 1) : x ≤ y :=
  not_lt.mp fun hyx => h ((Rcompare_spec x y).2.2.mpr hyx)

/-- Integer comparison as an Int code (-1/0/1), mirroring Coq's Z.compare -/
def Zcompare_int (m n : Int) : Int :=
  (if m < n then -1 else if m = n then 0 else 1)

/-- Comparing real casts of integers agrees with the integer comparison code. -/
@[flocq_source "src/Core/Raux.v" 468 "Rcompare_IZR"]
theorem Rcompare_IZR (m n : Int) :
    Rcompare (m : ℝ) (n : ℝ) = Zcompare_int m n := by
  simp [Rcompare, Zcompare_int]

/-- Coq theorem `Rcompare_middle`: midpoint comparison identity. -/
theorem Rcompare_middle (x d u : ℝ) :
    Rcompare (x - d) (u - x) = Rcompare x ((d + u) / 2) := by
  unfold Rcompare
  have hlt : (x - d < u - x) ↔ x < (d + u) / 2 := by
    constructor <;> intro h <;> linarith
  have heq : (x - d = u - x) ↔ x = (d + u) / 2 := by
    constructor <;> intro h <;> linarith
  by_cases hleft_lt : x - d < u - x
  · have hxlt : x < (d + u) / 2 := hlt.mp hleft_lt
    simp [hleft_lt, hxlt]
  · by_cases hleft_eq : x - d = u - x
    · have hxeq : x = (d + u) / 2 := heq.mp hleft_eq
      have hmid_eq : (d + u) / 2 - d = u - (d + u) / 2 := by
        linarith
      simp [hxeq, hmid_eq]
    · have hxnotlt : ¬ x < (d + u) / 2 := by
        intro hxlt
        exact hleft_lt (hlt.mpr hxlt)
      have hxneq : x ≠ (d + u) / 2 := by
        intro hxeq
        exact hleft_eq (heq.mpr hxeq)
      simp [hleft_lt, hleft_eq, hxnotlt, hxneq]

/-- Coq {lit}`Rcompare_half_l`: comparing {lit}`x / 2` with {lit}`y` is comparing
    {lit}`x` with {lit}`2 * y`. -/
theorem Rcompare_half_l (x y : ℝ) : Rcompare (x / 2) y = Rcompare x (2 * y) := by
  have hlt : x / 2 < y ↔ x < 2 * y := by
    constructor <;> intro h <;> linarith
  have heq : x / 2 = y ↔ x = 2 * y := by
    constructor <;> intro h <;> linarith
  simp only [Rcompare, hlt, heq]

/-- Coq {lit}`Rcompare_half_r`: comparing {lit}`x` with {lit}`y / 2` is comparing
    {lit}`2 * x` with {lit}`y`. -/
theorem Rcompare_half_r (x y : ℝ) : Rcompare x (y / 2) = Rcompare (2 * x) y := by
  have hlt : x < y / 2 ↔ 2 * x < y := by
    constructor <;> intro h <;> linarith
  have heq : x = y / 2 ↔ 2 * x = y := by
    constructor <;> intro h <;> linarith
  simp only [Rcompare, hlt, heq]

/-- Coq {lit}`Rcompare_sqr`: comparing squares is comparing absolute values. -/
theorem Rcompare_sqr (x y : ℝ) :
    Rcompare (x * x) (y * y) = Rcompare |x| |y| := by
  -- Compare using the three cases on |x| and |y|
  rcases lt_trichotomy (|x|) (|y|) with hlt | heq | hgt
  · -- Lt case
    have hx2 : x ^ 2 < y ^ 2 := (sq_lt_sq).2 hlt
    -- Left code is -1, right code is -1
    have hx2' : x * x < y * y := by simpa [pow_two] using hx2
    simp [Rcompare, hx2', hlt]
  · -- Eq case
    have hx2eq : x ^ 2 = y ^ 2 := by
      simpa [sq_abs] using congrArg (fun t => t ^ (2 : Nat)) heq
    have hxeq' : x * x = y * y := by simpa [pow_two] using hx2eq
    -- Show the left code is 0 (second branch), and the right code is 0 (equality)
    by_cases hxlt : x * x < y * y
    · -- Contradiction: rewriting by equality gives x*x < x*x
      have hxlt' : x * x < x * x := by simpa [hxeq'] using hxlt
      exact (False.elim ((lt_irrefl _) hxlt'))
    · simp [Rcompare, hxeq', heq]
  · -- Gt case
    have hy2 : y ^ 2 < x ^ 2 := (sq_lt_sq).2 hgt
    have hnotlt : ¬ x * x < y * y := by
      have : ¬ x ^ 2 < y ^ 2 := not_lt.mpr (le_of_lt hy2)
      simpa [pow_two] using this
    have hneq : x * x ≠ y * y := by
      have : x ^ 2 ≠ y ^ 2 := by simpa [eq_comm] using (ne_of_gt hy2)
      simpa [pow_two] using this
    -- With ¬(x^2 < y^2) and x^2 ≠ y^2, left code is 1; on the right we are in the Gt branch
    -- Also reduce the right side using ¬(|x| < |y|) and |x| ≠ |y|
    have hnotlt_abs : ¬ |x| < |y| := not_lt_of_ge (le_of_lt hgt)
    have hneq_abs : |x| ≠ |y| := by
      intro hEq
      -- From |y| < |x| and |x| = |y|, derive the contradiction |y| < |y|
      have : |y| < |y| := by simpa [hEq] using hgt
      exact (lt_irrefl _ this)
    simp [Rcompare, hnotlt, hneq, hnotlt_abs, hneq_abs]

/-- Coq {lit}`Rmin_compare`: the minimum is selected by the comparison code. -/
theorem Rmin_compare (x y : ℝ) :
    min x y = (if Rcompare x y = -1 then x else if Rcompare x y = 0 then x else y) := by
  by_cases hlt : x < y
  · simp [Rcompare, hlt, le_of_lt hlt]
  · by_cases heq : x = y
    · subst heq
      simp [Rcompare]
    · have hgt : y < x := lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm heq)
      simp [Rcompare, hlt, heq, le_of_lt hgt]

end RcompareMore

section BooleanComparisons

/-- Boolean less-or-equal test for real numbers

    Tests whether x ≤ y, returning a boolean result.
    This provides a decidable ordering test.
-/
noncomputable def Rle_bool (x y : ℝ) : Bool :=
  (decide (x ≤ y))

/-- Coq {lit}`Rle_bool_prop`: inductive characterization of {lean}`Rle_bool`. -/
inductive Rle_bool_prop (x y : ℝ) : Bool → Prop where
  | Rle_bool_true_ : x ≤ y → Rle_bool_prop x y true
  | Rle_bool_false_ : y < x → Rle_bool_prop x y false

export Rle_bool_prop (Rle_bool_true_ Rle_bool_false_)

/-- Coq-style spec: {lit}`Rle_bool_prop` holds for {lean}`Rle_bool`. -/
theorem Rle_bool_prop_spec (x y : ℝ) : Rle_bool_prop x y (Rle_bool x y) := by
  by_cases hxy : x ≤ y
  · have h : Rle_bool_prop x y true := Rle_bool_true_ hxy
    simpa [Rle_bool, hxy] using h
  · have hyx : y < x := lt_of_not_ge hxy
    have h : Rle_bool_prop x y false := Rle_bool_false_ hyx
    simpa [Rle_bool, hxy] using h

/-- The boolean less-or-equal test returns {lean}`true` exactly when {lit}`x ≤ y`. -/
theorem Rle_bool_spec (x y : ℝ) : Rle_bool x y = true ↔ x ≤ y := by
  simp [Rle_bool]

/-- Coq {lit}`Rle_bool_true`: if {lit}`x ≤ y`, then {lean}`Rle_bool x y = true`. -/
theorem Rle_bool_true (x y : ℝ) (hxy : x ≤ y) : Rle_bool x y = true := by
  simpa [Rle_bool] using hxy

/-- Coq {lit}`Rle_bool_false`: if {lit}`y < x`, then {lean}`Rle_bool x y = false`. -/
theorem Rle_bool_false (x y : ℝ) (hyx : y < x) : Rle_bool x y = false := by
  simpa [Rle_bool] using hyx

/-- Boolean strict less-than test for real numbers

    Tests whether x < y, returning a boolean result.
    This provides a decidable strict ordering test.
-/
noncomputable def Rlt_bool (x y : ℝ) : Bool :=
  (x < y)

/-- Coq {lit}`Rlt_bool_prop`: inductive characterization of {lean}`Rlt_bool`. -/
inductive Rlt_bool_prop (x y : ℝ) : Bool → Prop where
  | Rlt_bool_true_ : x < y → Rlt_bool_prop x y true
  | Rlt_bool_false_ : y ≤ x → Rlt_bool_prop x y false

export Rlt_bool_prop (Rlt_bool_true_ Rlt_bool_false_)

/-- Coq-style spec: {lit}`Rlt_bool_prop` holds for {lean}`Rlt_bool`. -/
theorem Rlt_bool_prop_spec (x y : ℝ) : Rlt_bool_prop x y (Rlt_bool x y) := by
  by_cases hxy : x < y
  · have h : Rlt_bool_prop x y true := Rlt_bool_true_ hxy
    simpa [Rlt_bool, hxy] using h
  · have hyx : y ≤ x := le_of_not_gt hxy
    have h : Rlt_bool_prop x y false := Rlt_bool_false_ hyx
    simpa [Rlt_bool, hxy] using h

/-- The boolean strict test returns {lean}`true` exactly when {lit}`x < y`. -/
theorem Rlt_bool_spec (x y : ℝ) : Rlt_bool x y = true ↔ x < y := by
  simp [Rlt_bool]

/-- Coq {lit}`Rlt_bool_true`: if {lit}`x < y`, then {lean}`Rlt_bool x y = true`. -/
theorem Rlt_bool_true (x y : ℝ) (hlt : x < y) : Rlt_bool x y = true := by
  simpa [Rlt_bool] using hlt

/-- Coq {lit}`Rlt_bool_false`: if {lit}`y ≤ x`, then {lean}`Rlt_bool x y = false`. -/
theorem Rlt_bool_false (x y : ℝ) (hyx : y ≤ x) : Rlt_bool x y = false := by
  simpa [Rlt_bool] using hyx

/-- Coq {lit}`Rlt_bool_opp`: negating both operands swaps the strict test. -/
theorem Rlt_bool_opp (x y : ℝ) : Rlt_bool (-x) (-y) = Rlt_bool y x := by
  simp [Rlt_bool]

/-- Coq `negb_Rlt_bool`: negating `x ≤ y` is the test for `y < x`. -/
theorem negb_Rlt_bool (x y : ℝ) :
    Bool.not (Rle_bool x y) = Rlt_bool y x := by
  by_cases hxy : x ≤ y
  · have hyx : ¬ y < x := not_lt_of_ge hxy
    simp [Rle_bool, Rlt_bool, hxy, hyx]
  · have hyx : y < x := lt_of_not_ge hxy
    simp [Rle_bool, Rlt_bool, hxy, hyx]

/-- Coq `negb_Rle_bool`: negating `x < y` is the test for `y ≤ x`. -/
theorem negb_Rle_bool (x y : ℝ) :
    Bool.not (Rlt_bool x y) = Rle_bool y x := by
  by_cases hxy : x < y
  · have hyx : ¬ y ≤ x := not_le_of_gt hxy
    simp [Rle_bool, Rlt_bool, hxy, hyx]
  · have hyx : y ≤ x := le_of_not_gt hxy
    simp [Rle_bool, Rlt_bool, hxy, hyx]

/-- Boolean equality test for real numbers

    Tests whether two real numbers are equal, returning a boolean.
    This provides a decidable equality test.
-/
noncomputable def Req_bool (x y : ℝ) : Bool :=
  (x = y)

/-- Coq {lit}`Req_bool_prop`: inductive characterization of {lean}`Req_bool`. -/
inductive Req_bool_prop (x y : ℝ) : Bool → Prop where
  | Req_bool_true_ : x = y → Req_bool_prop x y true
  | Req_bool_false_ : x ≠ y → Req_bool_prop x y false

export Req_bool_prop (Req_bool_true_ Req_bool_false_)

/-- Coq-style spec: {lit}`Req_bool_prop` holds for {lean}`Req_bool`. -/
theorem Req_bool_prop_spec (x y : ℝ) : Req_bool_prop x y (Req_bool x y) := by
  by_cases hxy : x = y
  · have h : Req_bool_prop x y true := Req_bool_true_ hxy
    simpa [Req_bool, hxy] using h
  · have h : Req_bool_prop x y false := Req_bool_false_ hxy
    simpa [Req_bool, hxy] using h

/-- The boolean equality test returns {lean}`true` exactly when {lit}`x = y`. -/
theorem Req_bool_spec (x y : ℝ) : Req_bool x y = true ↔ x = y := by
  simp [Req_bool]

/-- Coq {lit}`Req_bool_true`: if {lit}`x = y`, then {lean}`Req_bool x y = true`. -/
theorem Req_bool_true (x y : ℝ) (hxy : x = y) : Req_bool x y = true := by
  simpa [Req_bool] using hxy

/-- Coq {lit}`Req_bool_false`: if {lit}`x ≠ y`, then {lean}`Req_bool x y = false`. -/
theorem Req_bool_false (x y : ℝ) (hxy : x ≠ y) : Req_bool x y = false := by
  simpa [Req_bool] using hxy

end BooleanComparisons

section BooleanOperations

/-- Coq {lit}`eqb_sym`: boolean equality is symmetric. -/
theorem eqb_sym (a b : Bool) : (a == b) = (b == a) :=
  Bool.beq_comm

/-- Coq {lit}`eqb_true`: if {lit}`a = b`, then {lit}`(a == b) = true`. -/
@[flocq_source "src/Core/Raux.v" 2169 "eqb_true"]
theorem eqb_true (a b : Bool) (hEq : a = b) : (a == b) = true := by
  cases hEq
  cases a <;> rfl

/-- Coq {lit}`eqb_false`: if {lit}`a = !b`, then {lit}`(a == b) = false`. -/
@[flocq_source "src/Core/Raux.v" 2163 "eqb_false"]
theorem eqb_false (a b : Bool) (h : a = !b) : (a == b) = false := by
  cases h
  cases b <;> rfl

end BooleanOperations

section ConditionalOpposite

/-- Conditional opposite based on sign

    Returns -m if the condition is true, m otherwise.
    This is used for conditional negation in floating-point
    sign handling.
-/
def cond_Ropp (b : Bool) (m : ℝ) : ℝ :=
  if b then -m else m

/-- Defining equation of {lean}`cond_Ropp`: negate exactly when the flag is set. -/
theorem cond_Ropp_spec (b : Bool) (m : ℝ) :
    cond_Ropp b m = if b then -m else m :=
  rfl

/-- Coq {lit}`cond_Ropp_involutive`: conditional negation is involutive. -/
theorem cond_Ropp_involutive (b : Bool) (m : ℝ) : cond_Ropp b (cond_Ropp b m) = m := by
  cases b <;> simp [cond_Ropp]

/-- Coq {lit}`cond_Ropp_inj`: conditional negation by a fixed flag is injective. -/
theorem cond_Ropp_inj (b : Bool) (m1 m2 : ℝ)
    (h : cond_Ropp b m1 = cond_Ropp b m2) : m1 = m2 := by
  cases b <;> simpa [cond_Ropp] using h

end ConditionalOpposite

section CondAbsMulAdd

/-- Coq {lit}`abs_cond_Ropp`: absolute value ignores conditional negation. -/
@[flocq_source "src/Core/Raux.v" 2190 "abs_cond_Ropp"]
theorem abs_cond_Ropp (b : Bool) (x : ℝ) : |cond_Ropp b x| = |x| := by
  cases b <;> simp [cond_Ropp]

/-- Coq {lit}`cond_Ropp_mult_l`: conditional negation of a product, left factor. -/
@[flocq_source "src/Core/Raux.v" 2237 "cond_Ropp_mult_l"]
theorem cond_Ropp_mult_l (b : Bool) (x y : ℝ) :
    cond_Ropp b (x * y) = cond_Ropp b x * y := by
  cases b <;> simp [cond_Ropp]

/-- Coq {lit}`cond_Ropp_mult_r`: conditional negation of a product, right factor. -/
@[flocq_source "src/Core/Raux.v" 2247 "cond_Ropp_mult_r"]
theorem cond_Ropp_mult_r (b : Bool) (x y : ℝ) :
    cond_Ropp b (x * y) = x * cond_Ropp b y := by
  cases b <;> simp [cond_Ropp]

/-- Coq {lit}`cond_Ropp_plus`: conditional negation distributes over addition. -/
@[flocq_source "src/Core/Raux.v" 2257 "cond_Ropp_plus"]
theorem cond_Ropp_plus (b : Bool) (x y : ℝ) :
    cond_Ropp b (x + y) = cond_Ropp b x + cond_Ropp b y := by
  cases b <;> simp [cond_Ropp, add_comm]

end CondAbsMulAdd

section CondRltBool

/-- Coq {lit}`cond_Ropp_Rlt_bool`: applying the sign from {lean}`Rlt_bool m 0`
    turns {lean}`m` into its absolute value. -/
theorem cond_Ropp_Rlt_bool (m : ℝ) :
    cond_Ropp (Rlt_bool m 0) m = |m| := by
  by_cases hm : m < 0
  · simp [cond_Ropp, Rlt_bool, hm, abs_of_neg hm]
  · have hm_nonneg : 0 ≤ m := le_of_not_gt hm
    simp [cond_Ropp, Rlt_bool, hm, abs_of_nonneg hm_nonneg]

/-- Strict comparison after conditionally negating both operands. -/
theorem cond_Ropp_Rlt_bool_spec (b : Bool) (x y : ℝ) :
    Rlt_bool (cond_Ropp b x) (cond_Ropp b y) = true ↔ (if b then y < x else x < y) := by
  cases b <;> simp [Rlt_bool, cond_Ropp]

/-- Coq {lit}`Rlt_bool_cond_Ropp`: a positive magnitude has sign flag {lean}`sx`
    after conditional negation by {lean}`sx`. -/
theorem Rlt_bool_cond_Ropp (x : ℝ) (sx : Bool) (hx : 0 < x) :
    Rlt_bool (cond_Ropp sx x) 0 = sx := by
  cases sx
  · have hnot : ¬ x < 0 := by linarith
    simp [Rlt_bool, cond_Ropp, hnot]
  · have hneg : -x < 0 := by linarith
    simp [Rlt_bool, cond_Ropp, hneg]

/-- Strict comparison against a conditionally negated right operand. -/
theorem Rlt_bool_cond_Ropp_spec (b : Bool) (x y : ℝ) :
    Rlt_bool x (cond_Ropp b y) = true ↔ (if b then x < -y else x < y) := by
  cases b <;> simp [Rlt_bool, cond_Ropp]

end CondRltBool

section IZRCond

/-- Coq `IZR_cond_Zopp`: conditional integer negation commutes with casting. -/
theorem IZR_cond_Zopp (b : Bool) (m : Int) :
    ((FloatSpec.Core.Zaux.cond_Zopp b m : Int) : ℝ) = cond_Ropp b (m : ℝ) := by
  cases b <;> simp [FloatSpec.Core.Zaux.cond_Zopp, cond_Ropp]

end IZRCond

-- Inverse bounds for strict absolute inequalities
section AbsLtInv

/-- Coq {lit}`Rabs_lt_inv`: if {lit}`|x| < y`, then {lit}`-y < x < y`. -/
@[flocq_source "src/Core/Raux.v" 279 "Rabs_lt_inv"]
theorem Rabs_lt_inv (x y : ℝ) (h : |x| < y) : -y < x ∧ x < y :=
  abs_lt.mp h

end AbsLtInv

-- Integer rounding helpers (floor/ceil/trunc/away) and their properties
section IntRound

/-- Coq {lit}`Zfloor`: the integer floor of a real. -/
noncomputable def Zfloor (x : ℝ) : Int :=
  ⌊x⌋

/-- Coq {lit}`Zceil`: the integer ceiling of a real. -/
noncomputable def Zceil (x : ℝ) : Int :=
  ⌈x⌉

/-- Truncation toward zero: ceil for negatives, floor otherwise -/
noncomputable def Ztrunc (x : ℝ) : Int :=
  (if x < 0 then ⌈x⌉ else ⌊x⌋)

/-- Truncation commutes with absolute value, as reals. -/
theorem Ztrunc_abs_real (y : ℝ) :
    (((Ztrunc |y|) : Int) : ℝ) = |(((Ztrunc y) : Int) : ℝ)| := by
  -- Work by cases on the sign of y and unfold Ztrunc.
  by_cases hy : y < 0
  · -- Negative case: compute both sides explicitly and compare
    have hceil_nonpos : Int.ceil y ≤ 0 := (Int.ceil_le).mpr (by simpa using (le_of_lt hy))
    have hceil_nonposR : ((Int.ceil y : Int) : ℝ) ≤ 0 := by exact_mod_cast hceil_nonpos
    -- Left-hand side: Ztrunc (|y|) = ⌊-y⌋ = -⌈y⌉
    have hL : (((Ztrunc (abs y)) : Int) : ℝ) = -(((Int.ceil y : Int) : ℝ)) := by
      have : (Ztrunc (abs y)) = Int.floor (-y) := by
        -- since y < 0, we have |y| = -y and Ztrunc uses floor on nonnegatives
        have : (abs y) = -y := by simpa [abs_of_neg hy]
        -- Ztrunc on nonnegative arguments reduces to floor
        -- because -y > 0 given y < 0
        have hypos : 0 < -y := by exact neg_pos.mpr hy
        -- Now simplify Ztrunc (abs y)
        simp [Ztrunc, this, not_lt.mpr (le_of_lt hypos)]
      -- Cast both sides to ℝ and rewrite floor(-y)
      simpa [Int.floor_neg, Int.cast_neg] using congrArg (fun i : Int => (i : ℝ)) this
    -- Right-hand side: abs (⌈y⌉) = -⌈y⌉ because ⌈y⌉ ≤ 0
    have hR : abs ((((Ztrunc y) : Int) : ℝ)) = -(((Int.ceil y : Int) : ℝ)) := by
      -- Ztrunc y uses ceil when y < 0
      have : (((Ztrunc y) : Int) : ℝ) = ((Int.ceil y : Int) : ℝ) := by
        simp [Ztrunc, hy]
      -- simplify absolute value using nonpositivity of ⌈y⌉
      rw [this, abs_of_nonpos hceil_nonposR]
    -- Conclude by comparing both canonical forms
    exact hL.trans hR.symm
  · -- Nonnegative case: |y| = y and both truncations use floor
    have hy0 : 0 ≤ y := le_of_not_gt hy
    have hfloor_nonneg : 0 ≤ (Int.floor y : Int) := (Int.le_floor).mpr (by simpa using hy0)
    have hL : ((((Ztrunc (abs y)) : Int) : ℝ)) = ((Int.floor y : Int) : ℝ) := by
      simp [Ztrunc, abs_of_nonneg hy0, hy]
    have hR : abs ((((Ztrunc y) : Int) : ℝ)) = ((Int.floor y : Int) : ℝ) := by
      have : (((Ztrunc y) : Int) : ℝ) = ((Int.floor y : Int) : ℝ) := by
        simp [Ztrunc, hy]
      rw [this, abs_of_nonneg (by exact_mod_cast hfloor_nonneg)]
    exact hL.trans hR.symm

/-- Away-from-zero rounding: floor for negatives, ceil otherwise -/
noncomputable def Zaway (x : ℝ) : Int :=
  (if x < 0 then ⌊x⌋ else ⌈x⌉)

/-- Floor lower bound: ⌊x⌋ ≤ x -/
theorem Zfloor_lb (x : ℝ) :
    ((Zfloor x : Int) : ℝ) ≤ x := by
  unfold Zfloor
  -- Standard floor property: (⌊x⌋ : ℝ) ≤ x
  simpa using (Int.floor_le x)

/-- Floor upper bound: x < ⌊x⌋ + 1 -/
theorem Zfloor_ub (x : ℝ) :
    x < ((Zfloor x : Int) : ℝ) + 1 := by
  unfold Zfloor
  -- Standard floor upper bound: x < (⌊x⌋ : ℝ) + 1
  simpa using (Int.lt_floor_add_one x)

/-- Floor greatest-lower-bound: if m ≤ x then m ≤ ⌊x⌋ -/
theorem Zfloor_lub (m : Int) (x : ℝ) (hm : (m : ℝ) ≤ x) :
    m ≤ Zfloor x := by
  unfold Zfloor
  -- Greatest lower bound property for floor: m ≤ ⌊x⌋ ↔ (m : ℝ) ≤ x
  exact (Int.le_floor).mpr hm

/-- Characterization: if m ≤ x < m+1 then ⌊x⌋ = m -/
theorem Zfloor_imp (m : Int) (x : ℝ) (h : (m : ℝ) ≤ x ∧ x < (m : ℝ) + 1) :
    Zfloor x = m := by
  unfold Zfloor
  -- Characterization of floor by the half-open interval [m, m+1)
  simpa using ((Int.floor_eq_iff).2 h)

/-- Floor of an integer equals itself -/
theorem Zfloor_IZR (m : Int) :
    Zfloor (m : ℝ) = m := by
  unfold Zfloor
  -- Floor of an integer casts back to the same integer
  simpa using (Int.floor_intCast m)

/-- Monotonicity of floor: x ≤ y ⇒ ⌊x⌋ ≤ ⌊y⌋ -/
theorem Zfloor_le (x y : ℝ) (hxy : x ≤ y) :
    Zfloor x ≤ Zfloor y := by
  -- Expose the floors
  simp [Zfloor]  -- goal becomes: ⌊x⌋ ≤ ⌊y⌋
  -- Use the GLB property of floor with m := ⌊x⌋ and r := y
  -- It suffices to show (⌊x⌋ : ℝ) ≤ y
  refine (Int.le_floor).mpr ?_
  exact (Int.floor_le x).trans hxy

end IntRound

section IntCeil

/-- Ceiling upper bound: x ≤ ⌈x⌉ -/
theorem Zceil_ub (x : ℝ) :
    x ≤ ((Zceil x : Int) : ℝ) := by
  unfold Zceil
  -- Standard ceiling property: x ≤ (⌈x⌉ : ℝ)
  have hx : x ≤ (Int.ceil x : ℝ) := by
    -- Cast the integer inequality to ℝ
    exact_mod_cast Int.le_ceil x
  simpa using hx

/-- Ceiling lower-neighborhood: ⌈x⌉ - 1 < x -/
theorem Zceil_lb (x : ℝ) :
    ((Zceil x : Int) : ℝ) - 1 < x := by
  unfold Zceil
  -- Using the standard ceiling bound: (⌈x⌉ : ℝ) < x + 1
  -- and rewriting a - 1 < b ↔ a < b + 1
  simpa [sub_lt_iff_lt_add, add_comm] using (Int.ceil_lt_add_one x)

/-- Ceiling least-upper-bound: if x ≤ m then ⌈x⌉ ≤ m -/
theorem Zceil_glb (m : Int) (x : ℝ) (hx : x ≤ (m : ℝ)) :
    Zceil x ≤ m := by
  unfold Zceil
  -- Least upper bound property for ceiling: ⌈x⌉ ≤ m ↔ x ≤ m
  exact (Int.ceil_le).mpr hx

/-- Characterization: if m - 1 < x ≤ m then ⌈x⌉ = m -/
theorem Zceil_imp (m : Int) (x : ℝ) (h : (m : ℝ) - 1 < x ∧ x ≤ (m : ℝ)) :
    Zceil x = m := by
  unfold Zceil
  -- Characterization of ceiling by the half-open interval (m-1, m]
  simpa using ((Int.ceil_eq_iff).2 h)

/-- Ceiling of an integer equals itself -/
theorem Zceil_IZR (m : Int) :
    Zceil (m : ℝ) = m := by
  unfold Zceil
  -- Ceiling of an integer casts back to the same integer
  simpa using (Int.ceil_intCast m)

/-- Monotonicity of ceiling: x ≤ y ⇒ ⌈x⌉ ≤ ⌈y⌉ -/
theorem Zceil_le (x y : ℝ) (hxy : x ≤ y) :
    Zceil x ≤ Zceil y := by
  -- Expose the ceilings
  simp [Zceil]
  -- Use the characterization of ceiling via upper bounds:
  -- ⌈x⌉ ≤ m ↔ x ≤ m. Take m := ⌈y⌉ and show x ≤ ⌈y⌉ using x ≤ y ≤ ⌈y⌉.
  refine (Int.ceil_le).mpr ?_
  exact hxy.trans (Int.le_ceil y)

/-- Non-integral case: if ⌊x⌋ ≠ x then ⌈x⌉ = ⌊x⌋ + 1 -/
theorem Zceil_floor_neq (x : ℝ) (hne : ((Zfloor x : Int) : ℝ) ≠ x) :
    Zceil x = Zfloor x + 1 := by
  -- Expose the pure ceilings/floors
  simp [Zceil, Zfloor] at *
  -- Let f := ⌊x⌋ and c := ⌈x⌉
  set f := Int.floor x
  set c := Int.ceil x
  -- From floor inequality and the hypothesis (⌊x⌋ : ℝ) ≠ x, get strict inequality
  have hfl : (f : ℝ) ≤ x := by simpa [f] using (Int.floor_le x)
  have hflt : (f : ℝ) < x := lt_of_le_of_ne hfl (by simpa [f] using hne)
  -- And x ≤ c by definition of ceiling
  have hxc : x ≤ (c : ℝ) := by simpa [c] using (Int.le_ceil x)
  -- Hence (f : ℝ) < (c : ℝ), so f < c as integers
  have hfcR : (f : ℝ) < (c : ℝ) := lt_of_lt_of_le hflt hxc
  have hfc : f < c := (Int.cast_lt).mp hfcR
  -- Also, from x < (⌊x⌋ : ℝ) + 1, we get ⌈x⌉ ≤ ⌊x⌋ + 1
  have hceil_le : c ≤ f + 1 := by
    refine (Int.ceil_le).mpr ?_
    have hxlt : x < (f : ℝ) + 1 := by
      -- x < (⌊x⌋ : ℝ) + 1
      simpa [f] using (Int.lt_floor_add_one x)
    -- Strengthen to ≤ and rewrite the cast of (f+1 : ℤ)
    have : x ≤ (f : ℝ) + 1 := le_of_lt hxlt
    simpa [Int.cast_add, Int.cast_one] using this
  -- Combine c ≤ f+1 with f < c ↔ f+1 ≤ c
  have hle' : f + 1 ≤ c := (Int.add_one_le_iff.mpr hfc)
  exact le_antisymm hceil_le hle'

end IntCeil

section IntTrunc

/-- Truncation at integers: Ztrunc (m) = m -/
theorem Ztrunc_IZR (m : Int) :
    Ztrunc (m : ℝ) = m := by
  unfold Ztrunc; by_cases h : (m : ℝ) < 0 <;> simp [h]

/-- For nonnegatives: Ztrunc x = ⌊x⌋ -/
theorem Ztrunc_floor (x : ℝ) (hx : 0 ≤ x) :
    Ztrunc x = Zfloor x := by
  unfold Ztrunc
  -- Under 0 ≤ x, the truncation takes the floor branch
  have hx_nlt : ¬ x < 0 := not_lt.mpr hx
  simp [Zfloor, hx_nlt]

/-- For nonpositives: Ztrunc x = ⌈x⌉ -/
theorem Ztrunc_ceil (x : ℝ) (hxle : x ≤ 0) :
    Ztrunc x = Zceil x := by
  unfold Ztrunc
  by_cases hlt : x < 0
  · -- Negative case: Ztrunc takes the ceiling branch
    simp [Zceil, hlt]
  · -- Nonnegative case with x ≤ 0 ⇒ x = 0, so floor = ceil = 0
    have hx0 : 0 ≤ x := not_lt.mp hlt
    have hxeq : x = 0 := le_antisymm hxle hx0
    simp [Zceil, hxeq]

/-- Monotonicity of truncation: x ≤ y ⇒ Ztrunc x ≤ Ztrunc y -/
theorem Ztrunc_le (x y : ℝ) (hxy : x ≤ y) :
    Ztrunc x ≤ Ztrunc y := by
  -- Expose the definitions of Ztrunc and split on the signs of x and y
  by_cases hx : x < 0
  · by_cases hy : y < 0
    · -- Both negative: trunc = ceil; use monotonicity of ceiling
      simp [Ztrunc, hx, hy]
      -- Show: ⌈x⌉ ≤ ⌈y⌉ using x ≤ y ≤ ⌈y⌉
      refine (Int.ceil_le).mpr ?_
      exact hxy.trans (Int.le_ceil y)
    · -- x < 0, 0 ≤ y: need ⌈x⌉ ≤ ⌊y⌋ via  ⌈x⌉ ≤ 0 ≤ ⌊y⌋
      have hy0 : 0 ≤ y := le_of_not_gt hy
      have hxle0 : x ≤ (0 : ℝ) := le_of_lt hx
      -- Coerce 0 to an Int-cast real to match lemmas' expected types
      have hxle0' : x ≤ ((0 : Int) : ℝ) := by simpa using hxle0
      have hceil_le0 : Int.ceil x ≤ 0 := (Int.ceil_le).mpr hxle0'
      have hy0' : ((0 : Int) : ℝ) ≤ y := by simpa using hy0
      have h0_le_floor : (0 : Int) ≤ Int.floor y := (Int.le_floor).mpr hy0'
      -- Combine the bounds and rewrite the goal
      have : Int.ceil x ≤ Int.floor y := le_trans hceil_le0 h0_le_floor
      simpa [Ztrunc, hx, hy] using this
  · by_cases hy : y < 0
    · -- 0 ≤ x and y < 0 contradict x ≤ y; derive False and conclude
      have hx0 : 0 ≤ x := le_of_not_gt hx
      have hy0 : 0 ≤ y := hx0.trans hxy
      have : False := (not_lt.mpr hy0) hy
      cases this
    · -- Both nonnegative: trunc = floor; use monotonicity of floor
      simp [Ztrunc, hx, hy]
      -- Show: ⌊x⌋ ≤ ⌊y⌋ via (⌊x⌋ : ℝ) ≤ y
      refine (Int.le_floor).mpr ?_
      exact (Int.floor_le x).trans hxy

/-- Opposite: Ztrunc (-x) = - Ztrunc x -/
theorem Ztrunc_opp (x : ℝ) :
    Ztrunc (-x) = -Ztrunc x := by
  -- Expose the definitions: Ztrunc t = if t < 0 then ⌈t⌉ else ⌊t⌋
  simp [Ztrunc]
  -- Goal now: (if 0 < x then ⌈-x⌉ else ⌊-x⌋) = -(if x < 0 then ⌈x⌉ else ⌊x⌋)
  by_cases hxpos : 0 < x
  · -- Left takes the ceil branch; right takes the floor branch
    have hnotlt : ¬ x < 0 := not_lt.mpr (le_of_lt hxpos)
    simp [hxpos, hnotlt, Int.ceil_neg]
  · -- Left takes the floor branch; split on whether x < 0 or x = 0
    have hxle : x ≤ 0 := le_of_not_gt hxpos
    by_cases hxlt : x < 0
    · -- Right takes the ceil branch; use floor_neg
      simp [hxpos, hxlt, Int.floor_neg]
    · -- Then x = 0, so both sides are 0
      have : x = 0 := le_antisymm hxle (le_of_not_gt hxlt)
      subst this
      simp

/-- Absolute value: Ztrunc |x| = |Ztrunc x| -/
theorem Ztrunc_abs (x : ℝ) :
    Ztrunc |x| = ((Ztrunc x).natAbs : Int) := by
  -- Expose both truncations; for |x| we can simplify the sign test
  -- since |x| ≥ 0 always.
  simp [Ztrunc, not_lt.mpr (abs_nonneg x)]
  -- Goal is now: ⌊|x|⌋ = Int.natAbs (if x < 0 then ⌈x⌉ else ⌊x⌋)
  by_cases hxlt : x < 0
  · -- Negative case: |x| = -x and ⌊-x⌋ = -⌈x⌉.
    have hxle : x ≤ 0 := le_of_lt hxlt
    have habs : |x| = -x := by simpa using (abs_of_neg hxlt)
    have hceil_nonpos : Int.ceil x ≤ 0 := (Int.ceil_le).mpr (by simpa using hxle)
    have hnabs : ((Int.natAbs (Int.ceil x) : Int)) = - (Int.ceil x) :=
      Int.ofNat_natAbs_of_nonpos hceil_nonpos
    have habs_cast : |Int.ceil x| = ((Int.natAbs (Int.ceil x) : Int)) := by
      simpa using (Int.natCast_natAbs (Int.ceil x))
    -- Rewrite both sides accordingly
    simpa [habs, Int.floor_neg, hxlt, hnabs, habs_cast]
  · -- Nonnegative case: x ≥ 0, so ⌊|x|⌋ = ⌊x⌋ and natAbs ⌊x⌋ = ⌊x⌋.
    have hxge : 0 ≤ x := le_of_not_gt hxlt
    have hxabs : |x| = x := by simpa using (abs_of_nonneg hxge)
    -- Floor is nonnegative when x is nonnegative, via the GLB property of floor.
    have hfloor_nonneg : 0 ≤ (Int.floor x : Int) := by
      -- Using: m ≤ ⌊x⌋ ↔ (m : ℝ) ≤ x, with m := 0
      have : (0 : Int) ≤ Int.floor x := (Int.le_floor).mpr (by simpa using hxge)
      simpa using this
    -- Show ⌊|x|⌋ = ⌊x⌋ and |if x<0 then ⌈x⌉ else ⌊x⌋| = |⌊x⌋|
    have hL : ⌊|x|⌋ = ⌊x⌋ := by simpa [hxabs]
    have hR : |if x < 0 then ⌈x⌉ else ⌊x⌋| = |⌊x⌋| := by simpa [hxlt]
    -- Since ⌊x⌋ ≥ 0, we have |⌊x⌋| = ⌊x⌋.
    have hAbsFloor : |Int.floor x| = Int.floor x := abs_of_nonneg hfloor_nonneg
    -- Conclude by rewriting both sides.
    simpa [hL, hR, hAbsFloor]

/-- Lower bound via absolute: if n ≤ |x| then n ≤ |Ztrunc x| -/
theorem Ztrunc_lub (n : Int) (x : ℝ) (h : (n : ℝ) ≤ |x|) :
    n ≤ ((Ztrunc x).natAbs : Int) := by
  unfold Ztrunc
  by_cases hxlt : x < 0
  · -- Negative case: z = ⌈x⌉ and |x| = -x
    -- Reduce to an inequality on ⌈x⌉
    simp [hxlt]
    have hxle : x ≤ 0 := le_of_lt hxlt
    have habs : |x| = -x := by simpa using (abs_of_nonpos hxle)
    -- From (n : ℝ) ≤ |x| = -x, deduce x ≤ -n
    have hx_le_negn : x ≤ (-n : ℝ) := by
      have : (n : ℝ) ≤ -x := by simpa [habs] using h
      have := neg_le_neg this
      simpa using this
    -- Hence ⌈x⌉ ≤ -n by the ceil characterization
    have hceil_le : Int.ceil x ≤ -n := (Int.ceil_le).mpr (by simpa using hx_le_negn)
    -- And ⌈x⌉ ≤ 0, since x ≤ 0
    have hceil_nonpos : Int.ceil x ≤ 0 := (Int.ceil_le).mpr (by simpa using hxle)
    -- From ⌈x⌉ ≤ -n, obtain n ≤ -⌈x⌉
    have hn_le : n ≤ - Int.ceil x := by
      have := neg_le_neg hceil_le
      simpa using this
    -- Conclude: n ≤ |⌈x⌉|
    have : n ≤ |Int.ceil x| := by
      simpa [abs_of_nonpos hceil_nonpos] using hn_le
    exact this
  · -- Nonnegative case: z = ⌊x⌋ and |x| = x
    -- Reduce to an inequality on ⌊x⌋
    simp [hxlt]
    have hxge : 0 ≤ x := le_of_not_gt hxlt
    have habs : |x| = x := by simpa using (abs_of_nonneg hxge)
    -- From (n : ℝ) ≤ x derive n ≤ ⌊x⌋, then compare to natAbs ⌊x⌋
    have h_le_floor : n ≤ Int.floor x := by
      have : (n : ℝ) ≤ x := by simpa [habs] using h
      exact (Int.le_floor).mpr this
    -- ⌊x⌋ ≥ 0
    have hfloor_nonneg : 0 ≤ (Int.floor x : Int) := by
      have : (0 : Int) ≤ Int.floor x := (Int.le_floor).mpr (by simpa using hxge)
      simpa using this
    -- Move to |⌊x⌋| using abs_of_nonneg
    have : n ≤ |Int.floor x| := by
      simpa [abs_of_nonneg hfloor_nonneg] using h_le_floor
    exact this

/-- Basic truncation error bound: |Ztrunc x - x| < 1 -/
theorem abs_Ztrunc_sub_lt_one (x : ℝ) : abs (((Ztrunc x) : ℝ) - x) < 1 := by
  unfold Ztrunc
  by_cases h : x < 0
  · -- Negative case: Ztrunc x = ⌈x⌉
    simp [h]
    -- We have x ≤ ⌈x⌉ < x + 1, so 0 ≤ ⌈x⌉ - x < 1
    have h1 : x ≤ (⌈x⌉ : ℝ) := Int.le_ceil x
    have h2 : (⌈x⌉ : ℝ) < x + 1 := Int.ceil_lt_add_one x
    have pos : 0 ≤ ⌈x⌉ - x := by linarith [h1]
    have lt : ⌈x⌉ - x < 1 := by linarith [h2]
    rw [abs_of_nonneg pos]
    exact lt
  · -- Non-negative case: Ztrunc x = ⌊x⌋
    simp [h]
    -- We have ⌊x⌋ ≤ x < ⌊x⌋ + 1, so 0 ≤ x - ⌊x⌋ < 1
    have h1 : (⌊x⌋ : ℝ) ≤ x := Int.floor_le x
    have h2 : x < ⌊x⌋ + 1 := Int.lt_floor_add_one x
    have pos : 0 ≤ x - ⌊x⌋ := by linarith [h1]
    have lt : x - ⌊x⌋ < 1 := by linarith [h2]
    rw [abs_sub_comm, abs_of_nonneg pos]
    exact lt

end IntTrunc

section IntAway

/-- Away-from-zero at integers: Zaway (m) = m -/
theorem Zaway_IZR (m : Int) :
    Zaway (m : ℝ) = m := by
  unfold Zaway; by_cases h : (m : ℝ) < 0 <;> simp [h]

/-- For nonnegatives: Zaway x = ⌈x⌉ -/
theorem Zaway_ceil (x : ℝ) (hx : 0 ≤ x) :
    Zaway x = Zceil x := by
  unfold Zaway
  -- Under 0 ≤ x, we have ¬ x < 0, so Zaway takes the ceil branch
  have hx_nlt : ¬ x < 0 := not_lt.mpr hx
  simp [Zceil, hx_nlt]

/-- For nonpositives: Zaway x = ⌊x⌋ -/
theorem Zaway_floor (x : ℝ) (hxle : x ≤ 0) :
    Zaway x = Zfloor x := by
  unfold Zaway
  by_cases hlt : x < 0
  · -- Negative case: Zaway takes the floor branch
    simp [Zfloor, hlt]
  · -- Nonnegative case with x ≤ 0 ⇒ x = 0, so ceil = floor
    have hx0 : 0 ≤ x := not_lt.mp hlt
    have hxeq : x = 0 := le_antisymm hxle hx0
    simp [Zfloor, hxeq]

/-- Monotonicity of away rounding: x ≤ y ⇒ Zaway x ≤ Zaway y -/
theorem Zaway_le (x y : ℝ) (hxy : x ≤ y) :
    Zaway x ≤ Zaway y := by
  -- Expose the definitions of Zaway and split on the signs of x and y
  by_cases hx : x < 0
  · by_cases hy : y < 0
    · -- Both negative: away = floor; use monotonicity of floor
      simp [Zaway, hx, hy]
      refine (Int.le_floor).mpr ?_
      exact (Int.floor_le x).trans hxy
    · -- x < 0, 0 ≤ y: need ⌊x⌋ ≤ ⌈y⌉
      have hy0 : 0 ≤ y := le_of_not_gt hy
      simp [Zaway, hx, hy]
      -- Show: (⌊x⌋ : ℝ) ≤ (⌈y⌉ : ℝ), then cast back to Int inequality
      have hR : ((Int.floor x : ℝ) ≤ (Int.ceil y : ℝ)) := by
        exact (Int.floor_le x) |>.trans (hxy.trans (Int.le_ceil y))
      exact (Int.cast_le).1 hR
  · by_cases hy : y < 0
    · -- 0 ≤ x and y < 0 contradict x ≤ y; derive False
      have hx0 : 0 ≤ x := le_of_not_gt hx
      have hy0 : 0 ≤ y := hx0.trans hxy
      have : False := (not_lt.mpr hy0) hy
      cases this
    · -- Both nonnegative: away = ceil; use monotonicity of ceiling
      simp [Zaway, hx, hy]
      refine (Int.ceil_le).mpr ?_
      exact hxy.trans (Int.le_ceil y)

/-- Opposite: Zaway (-x) = - Zaway x -/
theorem Zaway_opp (x : ℝ) :
    Zaway (-x) = -Zaway x := by
  -- Expose the definitions: Zaway t = if t < 0 then ⌊t⌋ else ⌈t⌉
  -- Target becomes a pure equality of integers
  simp [Zaway]
  -- Goal: (if 0 < x then ⌊-x⌋ else ⌈-x⌉) = - (if x < 0 then ⌊x⌋ else ⌈x⌉)
  by_cases hxpos : 0 < x
  · -- Then (-x) < 0 and x < 0 is false
    have hL : (if 0 < x then ⌊-x⌋ else ⌈-x⌉) = ⌊-x⌋ := by simp [hxpos]
    have hnlt : ¬ x < 0 := not_lt.mpr (le_of_lt hxpos)
    have hR : (if x < 0 then ⌊x⌋ else ⌈x⌉) = ⌈x⌉ := by simp [hnlt]
    have hfloor_neg : ⌊-x⌋ = -⌈x⌉ := by simpa using (Int.floor_neg (a := x))
    calc
      (if 0 < x then ⌊-x⌋ else ⌈-x⌉)
          = ⌊-x⌋ := hL
      _   = -⌈x⌉ := hfloor_neg
      _   = -(if x < 0 then ⌊x⌋ else ⌈x⌉) := by simpa [hR]
  · -- Not (0 < x): hence x ≤ 0; split further on x < 0
    have hxle : x ≤ 0 := le_of_not_gt hxpos
    by_cases hxlt : x < 0
    · -- Negative x: (-x) ≥ 0, so take ceil on the left; right takes floor
      have hL : (if 0 < x then ⌊-x⌋ else ⌈-x⌉) = ⌈-x⌉ := by simp [hxpos]
      have hR : (if x < 0 then ⌊x⌋ else ⌈x⌉) = ⌊x⌋ := by simp [hxlt]
      have hceil_neg : ⌈-x⌉ = -⌊x⌋ := by simpa using (Int.ceil_neg (a := x))
      calc
        (if 0 < x then ⌊-x⌋ else ⌈-x⌉)
            = ⌈-x⌉ := hL
        _   = -⌊x⌋ := hceil_neg
        _   = -(if x < 0 then ⌊x⌋ else ⌈x⌉) := by simpa [hR]
    · -- x = 0: both sides reduce to 0
      have hx0 : x = 0 := le_antisymm hxle (not_lt.mp hxlt)
      subst hx0
      simp

/-- Absolute value: Zaway |x| = |Zaway x| -/
theorem Zaway_abs (x : ℝ) :
    Zaway |x| = ((Zaway x).natAbs : Int) := by
  -- Expose both roundings; for |x| we can simplify the sign test
  -- since |x| ≥ 0 always.
  simp [Zaway, not_lt.mpr (abs_nonneg x)]
  -- Goal is now: ⌈|x|⌉ = Int.natAbs (if x < 0 then ⌊x⌋ else ⌈x⌉)
  by_cases hxlt : x < 0
  · -- Negative case: |x| = -x and ⌈-x⌉ = -⌊x⌋.
    have hxle : x ≤ 0 := le_of_lt hxlt
    have habs : |x| = -x := by simpa using (abs_of_nonpos hxle)
    -- Show ⌊x⌋ ≤ 0 via monotonicity of floor (x ≤ 0 ⇒ ⌊x⌋ ≤ ⌊0⌋ = 0)
    have hfloor_nonpos : Int.floor x ≤ 0 := by
      simpa using (Int.floor_le_floor (a := x) (b := 0) hxle)
    -- Conclude by rewriting both sides to -⌊x⌋ and |⌊x⌋|
    have hL : ⌈|x|⌉ = -⌊x⌋ := by simpa [habs] using (Int.ceil_neg (a := x))
    have hR : |if x < 0 then ⌊x⌋ else ⌈x⌉| = |⌊x⌋| := by simpa [hxlt]
    have hAbsFloor : |Int.floor x| = -Int.floor x := abs_of_nonpos hfloor_nonpos
    -- Chain the equalities
    calc
      ⌈|x|⌉ = -⌊x⌋ := hL
      _     = |⌊x⌋| := by simpa [hAbsFloor]
      _     = |if x < 0 then ⌊x⌋ else ⌈x⌉| := hR.symm
  · -- Nonnegative case: x ≥ 0, so ⌈|x|⌉ = ⌈x⌉ and |⌈x⌉| = ⌈x⌉.
    have hxge : 0 ≤ x := le_of_not_gt hxlt
    have hxabs : |x| = x := by simpa using (abs_of_nonneg hxge)
    -- ⌈x⌉ is nonnegative when x ≥ 0
    have hceil_nonneg : 0 ≤ (Int.ceil x : Int) := Int.ceil_nonneg (by simpa using hxge)
    -- Conclude by rewriting both sides.
    simpa [hxabs, hxlt, abs_of_nonneg hceil_nonneg]

end IntAway

section IntDiv

/-- Positive-denominator payload retained for callers that use Lean's Euclidean `/`. -/
theorem Zfloor_div_pos_payload (x y : Int) (hypos : 0 < y) :
    Zfloor ((x : ℝ) / (y : ℝ)) = x / y := by
  unfold Zfloor
  -- We prove ⌊(x : ℝ) / (y : ℝ)⌋ = x / y by the floor characterization
  -- using the Euclidean division x = y * (x / y) + x % y and
  -- bounds 0 ≤ x % y < y when 0 < y.
  have hy_pos : 0 < y := hypos
  -- Remainder bounds in ℤ
  have hr_nonnegZ : (0 : Int) ≤ x % y := Int.emod_nonneg _ (ne_of_gt hy_pos)
  have hr_ltZ : x % y < y := Int.emod_lt_of_pos _ hy_pos
  -- Cast to ℝ
  have hr_nonneg : (0 : ℝ) ≤ ((x % y : Int) : ℝ) := by
    exact_mod_cast hr_nonnegZ
  have hr_lt : ((x % y : Int) : ℝ) < (y : ℝ) := by
    exact_mod_cast hr_ltZ
  -- Real identity: (x : ℝ) = (y : ℝ) * (x / y) + (x % y)
  have hx_decomp : (y : ℝ) * ((x / y : Int) : ℝ) + ((x % y : Int) : ℝ) = (x : ℝ) := by
    simpa [Int.cast_add, Int.cast_mul] using
      congrArg (fun t : Int => (t : ℝ)) (Int.mul_ediv_add_emod x y)
  -- Lower bound: (x / y : ℝ) ≤ (x : ℝ) / (y : ℝ)
  have h_lower : ((x / y : Int) : ℝ) ≤ (x : ℝ) / (y : ℝ) := by
    -- Multiply both sides by y > 0 and use the decomposition
    have hyR_pos : 0 < (y : ℝ) := by exact_mod_cast hy_pos
    have hmul_le : ((x / y : Int) : ℝ) * (y : ℝ) ≤ (x : ℝ) := by
      -- (q*y) ≤ (q*y + r) when r ≥ 0
      have : ((x / y : Int) : ℝ) * (y : ℝ) ≤ ((x / y : Int) : ℝ) * (y : ℝ) + ((x % y : Int) : ℝ) :=
        by exact le_add_of_nonneg_right hr_nonneg
      simpa [mul_comm, hx_decomp] using this
    -- Using the equivalence a ≤ b / y ↔ a*y ≤ b for y > 0
    exact (le_div_iff₀ hyR_pos).mpr hmul_le
  -- Upper bound: (x : ℝ) / (y : ℝ) < (x / y : ℝ) + 1
  have h_upper : (x : ℝ) / (y : ℝ) < ((x / y : Int) : ℝ) + 1 := by
    -- Equivalent to x < ((x / y) + 1) * y since y > 0
    have hyR_pos : 0 < (y : ℝ) := by exact_mod_cast hy_pos
    -- From the decomposition x = y*q + r and r < y
    have hx_lt : (x : ℝ) < (((x / y : Int) : ℝ) + 1) * (y : ℝ) := by
      -- rewrite x in terms of q and r, then compare r < y
      have h := add_lt_add_left hr_lt ((y : ℝ) * ((x / y : Int) : ℝ))
      -- rearrange (y*q + y) = ((q + 1) * y)
      linarith [h]
    -- Transport the inequality through division by positive y
    exact (div_lt_iff₀ hyR_pos).mpr hx_lt
  -- Conclude by the floor characterization
  have hfloor : ⌊(x : ℝ) / (y : ℝ)⌋ = x / y := Int.floor_eq_iff.mpr ⟨h_lower, h_upper⟩
  exact hfloor

/-- Coq `Zfloor_div`: real floor agrees with Coq's floor division on the full
nonzero-divisor domain. Lean's corresponding integer operation is `Int.fdiv`. -/
theorem Zfloor_div (x y : Int) (hy : y ≠ 0) :
    Zfloor ((x : ℝ) / (y : ℝ)) = Int.fdiv x y := by
  by_cases hypos : 0 < y
  · have h := Zfloor_div_pos_payload x y hypos
    have hf : Int.fdiv x y = x / y :=
      Int.fdiv_eq_ediv_of_nonneg x (le_of_lt hypos)
    exact h.trans hf.symm
  · have hyneg : y < 0 := lt_of_le_of_ne (le_of_not_gt hypos) hy
    have h := Zfloor_div_pos_payload (-x) (-y) (by omega)
    have hf : Int.fdiv (-x) (-y) = (-x) / (-y) :=
      Int.fdiv_eq_ediv_of_nonneg (-x) (by omega)
    have hq : (-x) / (-y) = Int.fdiv x y := by
      rw [← hf, Int.neg_fdiv_neg]
    simpa using h.trans hq

/-- Coq lemma {lit}`Ztrunc_div`: for integers x and y with y ≠ 0, {lit}`Ztrunc` ({lit}`IZR` x / {lit}`IZR` y) equals the integer quotient; in Lean we state it as {lean}`Ztrunc ((x : ℝ) / (y : ℝ)) = Int.tdiv x y`. -/
theorem Ztrunc_div_nonneg_pos_payload (x y : Int) (hxy : 0 ≤ x ∧ 0 < y) :
    Ztrunc ((x : ℝ) / (y : ℝ)) = Int.tdiv x y := by
  have hx_nonneg : 0 ≤ x := hxy.left
  have hy_pos : 0 < y := hxy.right
  unfold Ztrunc
  -- x ≥ 0: Ztrunc takes the floor branch; use floor characterization and tdiv=ediv
  have hxR_nonneg : (0 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx_nonneg
  have hyR_pos : (0 : ℝ) < (y : ℝ) := by exact_mod_cast hy_pos
  have hx_nlt : ¬ ((x : ℝ) / (y : ℝ) < 0) := by
    exact not_lt.mpr (div_nonneg hxR_nonneg (le_of_lt hyR_pos))
  -- Show: ⌊(x:ℝ)/(y:ℝ)⌋ = x / y using the floor characterization at positive y
  have hr_nonnegZ : (0 : Int) ≤ x % y := Int.emod_nonneg _ (ne_of_gt hy_pos)
  have hr_ltZ : x % y < y := Int.emod_lt_of_pos _ hy_pos
  have hr_nonneg : (0 : ℝ) ≤ ((x % y : Int) : ℝ) := by exact_mod_cast hr_nonnegZ
  have hr_lt : ((x % y : Int) : ℝ) < (y : ℝ) := by exact_mod_cast hr_ltZ
  have hx_decomp : (y : ℝ) * ((x / y : Int) : ℝ) + ((x % y : Int) : ℝ) = (x : ℝ) := by
    simpa [Int.cast_add, Int.cast_mul] using congrArg (fun t : Int => (t : ℝ)) (Int.mul_ediv_add_emod x y)
  have h_lower : ((x / y : Int) : ℝ) ≤ (x : ℝ) / (y : ℝ) := by
    have hmul_le : ((x / y : Int) : ℝ) * (y : ℝ) ≤ (x : ℝ) := by
      have : ((x / y : Int) : ℝ) * (y : ℝ)
                ≤ ((x / y : Int) : ℝ) * (y : ℝ) + ((x % y : Int) : ℝ) :=
        le_add_of_nonneg_right hr_nonneg
      simpa [mul_comm, hx_decomp] using this
    exact (le_div_iff₀ hyR_pos).mpr hmul_le
  have h_upper : (x : ℝ) / (y : ℝ) < ((x / y : Int) : ℝ) + 1 := by
    have hx_lt : (x : ℝ) < (((x / y : Int) : ℝ) + 1) * (y : ℝ) := by
      have h := add_lt_add_left hr_lt ((y : ℝ) * ((x / y : Int) : ℝ))
      linarith [h]
    exact (div_lt_iff₀ hyR_pos).mpr hx_lt
  have hf : ⌊(x : ℝ) / (y : ℝ)⌋ = x / y := by
    simp only [Int.floor_eq_iff, h_lower, h_upper, and_self]
  have htdiv : Int.tdiv x y = x / y := by
    simpa using (Int.tdiv_eq_ediv_of_nonneg hx_nonneg : Int.tdiv x y = x / y)
  -- Rewrite with the floor and division facts to close the goal
  simpa [hx_nlt, hf, htdiv]

/-- Coq `Ztrunc_div`: real truncation agrees with integer truncating division
for every nonzero divisor, including negative dividends and divisors. -/
theorem Ztrunc_div (x y : Int) (hy : y ≠ 0) :
    Ztrunc ((x : ℝ) / (y : ℝ)) = Int.tdiv x y := by
  have positive_case (a b : Int) (ha : 0 ≤ a) (hb : 0 < b) :
      Ztrunc ((a : ℝ) / (b : ℝ)) = Int.tdiv a b :=
    Ztrunc_div_nonneg_pos_payload a b ⟨ha, hb⟩
  by_cases hx : 0 ≤ x
  · by_cases hypos : 0 < y
    · exact positive_case x y hx hypos
    · have hyneg : y < 0 := lt_of_le_of_ne (le_of_not_gt hypos) hy
      have hcanon := positive_case x (-y) hx (by omega)
      have hopp := Ztrunc_opp ((x : ℝ) / ((-y : Int) : ℝ))
      calc
        Ztrunc ((x : ℝ) / (y : ℝ))
            = Ztrunc (-((x : ℝ) / ((-y : Int) : ℝ))) := by
                congr 1
                simp only [Int.cast_neg, div_neg, neg_neg]
        _ = -Ztrunc ((x : ℝ) / ((-y : Int) : ℝ)) := hopp
        _ = -Int.tdiv x (-y) := congrArg Neg.neg hcanon
        _ = Int.tdiv x y := by
          simpa only [neg_neg] using (Int.tdiv_neg x (-y)).symm
  · have hxneg : x < 0 := lt_of_not_ge hx
    by_cases hypos : 0 < y
    · have hcanon := positive_case (-x) y (by omega) hypos
      have hopp := Ztrunc_opp (((-x : Int) : ℝ) / (y : ℝ))
      calc
        Ztrunc ((x : ℝ) / (y : ℝ))
            = Ztrunc (-(((-x : Int) : ℝ) / (y : ℝ))) := by
                congr 1
                simp only [Int.cast_neg, neg_div, neg_neg]
        _ = -Ztrunc (((-x : Int) : ℝ) / (y : ℝ)) := hopp
        _ = -Int.tdiv (-x) y := congrArg Neg.neg hcanon
        _ = Int.tdiv x y := by
          simpa only [neg_neg] using (Int.neg_tdiv (-x) y).symm
    · have hyneg : y < 0 := lt_of_le_of_ne (le_of_not_gt hypos) hy
      have hcanon := positive_case (-x) (-y) (by omega) (by omega)
      calc
        Ztrunc ((x : ℝ) / (y : ℝ))
            = Ztrunc (((-x : Int) : ℝ) / ((-y : Int) : ℝ)) := by
                congr 1
                rw [Int.cast_neg, Int.cast_neg, neg_div_neg_eq]
        _ = Int.tdiv (-x) (-y) := hcanon
        _ = Int.tdiv x y := Int.neg_tdiv_neg x y

end IntDiv

-- Comparisons against floor/ceil bounds
section CompareIntBounds

/-- Coq theorem {lit}`Rcompare_floor_ceil_middle`: in the non-integral case,
    comparing the fractional part of {lean}`x` with {lean}`1 / 2` is the same
    as comparing it with the distance from {lean}`x` to its ceiling. -/
theorem Rcompare_floor_ceil_middle (x : ℝ)
    (hne : ((Zfloor x) : ℝ) ≠ x) :
    Rcompare (x - (Zfloor x : ℝ)) (1 / 2) =
      Rcompare (x - (Zfloor x : ℝ)) ((Zceil x : ℝ) - x) := by
  have hceil : Zceil x = Zfloor x + 1 := by
    unfold Zceil Zfloor
    set f := Int.floor x
    set c := Int.ceil x
    have hne_f : (f : ℝ) ≠ x := by simpa [Zfloor, f] using hne
    have hfl : (f : ℝ) ≤ x := by simpa [f] using (Int.floor_le x)
    have hflt : (f : ℝ) < x := lt_of_le_of_ne hfl hne_f
    have hxc : x ≤ (c : ℝ) := by simpa [c] using (Int.le_ceil x)
    have hfcR : (f : ℝ) < (c : ℝ) := lt_of_lt_of_le hflt hxc
    have hfc : f < c := (Int.cast_lt).mp hfcR
    have hceil_le : c ≤ f + 1 := by
      refine (Int.ceil_le).mpr ?_
      have hxlt : x < (f : ℝ) + 1 := by
        simpa [f] using (Int.lt_floor_add_one x)
      have : x ≤ (f : ℝ) + 1 := le_of_lt hxlt
      simpa [Int.cast_add, Int.cast_one] using this
    have hle' : f + 1 ≤ c := Int.add_one_le_iff.mpr hfc
    exact le_antisymm hceil_le hle'
  have hceilR : ((Zceil x : Int) : ℝ) = (Zfloor x : ℝ) + 1 := by
    simpa [Int.cast_add, Int.cast_one] using congrArg (fun z : Int => (z : ℝ)) hceil
  have hdist :
      (Zceil x : ℝ) - x = 1 - (x - (Zfloor x : ℝ)) := by
    linarith
  have hmiddle :=
    Rcompare_middle (x := x - (Zfloor x : ℝ)) (d := 0) (u := 1)
  calc
    Rcompare (x - (Zfloor x : ℝ)) (1 / 2)
        = Rcompare (x - (Zfloor x : ℝ)) (1 - (x - (Zfloor x : ℝ))) := by
          simpa using hmiddle.symm
    _ = Rcompare (x - (Zfloor x : ℝ)) ((Zceil x : ℝ) - x) := by
          rw [hdist]

/-- Floor and ceiling hit {lit}`x` together, so comparing {lit}`⌊x⌋` with
    {lit}`x` agrees with comparing {lit}`x` with {lit}`⌈x⌉`. -/
theorem Rcompare_floor_ceil_middle_spec (x : ℝ) :
    Rcompare ((Zfloor x : Int) : ℝ) x = Rcompare x ((Zceil x : Int) : ℝ) := by
  -- Reduce both sides to simple if-forms using monotonicity of floor/ceil
  have hcodeL : (Rcompare ((Int.floor x : ℝ)) x) = (if x = (Int.floor x : ℝ) then 0 else -1) := by
    unfold Rcompare
    have hle : (Int.floor x : ℝ) ≤ x := Int.floor_le x
    by_cases heq : (Int.floor x : ℝ) = x
    · -- If equality holds, the "<" branch is impossible.
      have hnotlt : ¬ (Int.floor x : ℝ) < x := by
        -- Reduce to ¬ x < x
        simpa [heq] using (lt_irrefl x : ¬ x < x)
      simp [heq]
    · have hlt : (Int.floor x : ℝ) < x := lt_of_le_of_ne hle heq
      -- In the strict case, the comparison code is -1
      have : (Rcompare ((Int.floor x : ℝ)) x) = -1 := by
        simp [Rcompare, hlt]
      -- And the target if-form also reduces to -1 since x ≠ ⌊x⌋
      have : (Rcompare ((Int.floor x : ℝ)) x)
              = (if x = (Int.floor x : ℝ) then 0 else -1) := by
        simpa [this, ite_eq_right (by simpa [eq_comm] using heq)]
      exact this
  have hcodeR : (Rcompare x ((Int.ceil x : ℝ))) = (if x = (Int.ceil x : ℝ) then 0 else -1) := by
    unfold Rcompare
    have hle : x ≤ (Int.ceil x : ℝ) := Int.le_ceil x
    by_cases heq : x = (Int.ceil x : ℝ)
    · -- Equality case: code is 0
      have hnotlt : ¬ x < (Int.ceil x : ℝ) := by
        -- If x = ⌈x⌉, then x < ⌈x⌉ would imply x < x
        intro hxlt
        have : x < x := lt_of_lt_of_eq hxlt heq.symm
        exact (lt_irrefl _) this
      -- Evaluate the nested-ifs directly using rewrites
      have : (if x < (Int.ceil x : ℝ) then (-1 : Int) else if x = (Int.ceil x : ℝ) then 0 else 1) = 0 := by
        rw [ite_eq_right hnotlt, ite_eq_left heq]
      -- Right-hand side also reduces to 0 under heq
      simpa [ite_eq_left heq] using this
    · -- Strict case: code is -1
      have hlt : x < (Int.ceil x : ℝ) := lt_of_le_of_ne hle heq
      have : (if x < (Int.ceil x : ℝ) then (-1 : Int) else if x = (Int.ceil x : ℝ) then 0 else 1) = -1 := by
        simp [hlt]
      simpa [heq] using this
  -- Floor hits x iff ceil hits x; transport the cases
  have hiff : (x = (Int.floor x : ℝ)) ↔ (x = (Int.ceil x : ℝ)) := by
    constructor
    · intro hfx
      have : Int.ceil x = Int.floor x := by
        have h1 : Int.ceil ((Int.floor x : ℝ)) = Int.floor x := Int.ceil_intCast (Int.floor x)
        have h2 : Int.ceil x = Int.ceil ((Int.floor x : ℝ)) := congrArg Int.ceil hfx
        exact h2.trans h1
      exact by
        have : (Int.ceil x : ℝ) = (Int.floor x : ℝ) := congrArg (fun n : Int => (n : ℝ)) this
        simpa [this] using hfx
    · intro hcx
      have : Int.floor x = Int.ceil x := by
        have h1 : Int.floor ((Int.ceil x : ℝ)) = Int.ceil x := Int.floor_intCast (Int.ceil x)
        have h2 : Int.floor x = Int.floor ((Int.ceil x : ℝ)) := congrArg Int.floor hcx
        exact h2.trans h1
      exact by
        have : (Int.floor x : ℝ) = (Int.ceil x : ℝ) := congrArg (fun n : Int => (n : ℝ)) this
        simpa [this] using hcx
  -- Conclude by rewriting both codes with the if-forms and equating conditions
  have : (Rcompare ((Int.floor x : ℝ)) x) = (Rcompare x ((Int.ceil x : ℝ))) := by
    by_cases hx : x = (Int.floor x : ℝ)
    · -- Equality case: both codes evaluate to 0
      have hx' : x = (Int.ceil x : ℝ) := (hiff.mp hx)
      have hL0 : (Rcompare ((Int.floor x : ℝ)) x) = 0 := by
        rw [hcodeL, ite_eq_left hx]
      have hR0 : (Rcompare x ((Int.ceil x : ℝ))) = 0 := by
        rw [hcodeR, ite_eq_left hx']
      rw [hL0, hR0]
    · -- Strict inequalities case: both codes evaluate to -1
      have hx' : x ≠ (Int.ceil x : ℝ) := by
        intro h; exact hx ((hiff.mpr h))
      have hL1 : (Rcompare ((Int.floor x : ℝ)) x) = -1 := by
        -- Using the simplified code form hcodeL and inequality of x ≠ ⌊x⌋
        have hneq : x ≠ (Int.floor x : ℝ) := by simpa [eq_comm] using hx
        rw [hcodeL, ite_eq_right hneq]
      have hR1 : (Rcompare x ((Int.ceil x : ℝ))) = -1 := by
        -- Using the simplified code form hcodeR and inequality of x ≠ ⌈x⌉
        rw [hcodeR, ite_eq_right hx']
      rw [hL1, hR1]
  -- Finish by restating the goal through the floor/ceiling definitions.
  change Rcompare ((Int.floor x : Int) : ℝ) x =
    Rcompare x ((Int.ceil x : Int) : ℝ)
  exact this

/-- Coq theorem {lit}`Rcompare_ceil_floor_middle`: in the non-integral case,
    comparing the distance from {lean}`x` to its ceiling with {lean}`1 / 2`
    is the same as comparing it with the fractional part of {lean}`x`. -/
theorem Rcompare_ceil_floor_middle (x : ℝ)
    (hne : ((Zfloor x) : ℝ) ≠ x) :
    Rcompare ((Zceil x : ℝ) - x) (1 / 2) =
      Rcompare ((Zceil x : ℝ) - x) (x - (Zfloor x : ℝ)) := by
  have hceil : Zceil x = Zfloor x + 1 := by
    unfold Zceil Zfloor
    set f := Int.floor x
    set c := Int.ceil x
    have hne_f : (f : ℝ) ≠ x := by simpa [Zfloor, f] using hne
    have hfl : (f : ℝ) ≤ x := by simpa [f] using (Int.floor_le x)
    have hflt : (f : ℝ) < x := lt_of_le_of_ne hfl hne_f
    have hxc : x ≤ (c : ℝ) := by simpa [c] using (Int.le_ceil x)
    have hfcR : (f : ℝ) < (c : ℝ) := lt_of_lt_of_le hflt hxc
    have hfc : f < c := (Int.cast_lt).mp hfcR
    have hceil_le : c ≤ f + 1 := by
      refine (Int.ceil_le).mpr ?_
      have hxlt : x < (f : ℝ) + 1 := by
        simpa [f] using (Int.lt_floor_add_one x)
      have : x ≤ (f : ℝ) + 1 := le_of_lt hxlt
      simpa [Int.cast_add, Int.cast_one] using this
    have hle' : f + 1 ≤ c := Int.add_one_le_iff.mpr hfc
    exact le_antisymm hceil_le hle'
  have hceilR : ((Zceil x : Int) : ℝ) = (Zfloor x : ℝ) + 1 := by
    simpa [Int.cast_add, Int.cast_one] using congrArg (fun z : Int => (z : ℝ)) hceil
  have hdist :
      x - (Zfloor x : ℝ) = 1 - ((Zceil x : ℝ) - x) := by
    linarith
  have hmiddle :=
    Rcompare_middle (x := (Zceil x : ℝ) - x) (d := 0) (u := 1)
  calc
    Rcompare ((Zceil x : ℝ) - x) (1 / 2)
        = Rcompare ((Zceil x : ℝ) - x) (1 - ((Zceil x : ℝ) - x)) := by
          simpa using hmiddle.symm
    _ = Rcompare ((Zceil x : ℝ) - x) (x - (Zfloor x : ℝ)) := by
          rw [hdist]

/-- Comparing {lit}`⌈x⌉` with {lit}`x` agrees with comparing {lit}`x` with
    {lit}`⌊x⌋`. -/
theorem Rcompare_ceil_floor_middle_spec (x : ℝ) :
    Rcompare ((Zceil x : Int) : ℝ) x = Rcompare x ((Zfloor x : Int) : ℝ) := by
  -- Show both comparison codes coincide by splitting on whether x hits its ceil/floor.
  -- Compute each code using monotonicity facts: x ≤ ⌈x⌉ and ⌊x⌋ ≤ x.
  have hL : (Rcompare ((Int.ceil x : ℝ)) x) = (if x = (Int.ceil x : ℝ) then (0 : Int) else 1) := by
    unfold Rcompare
    have hnotlt : ¬ (Int.ceil x : ℝ) < x := not_lt.mpr (Int.le_ceil x)
    -- The equality test is commutative; rewrite to match the statement
    simp [hnotlt, eq_comm]
  have hR : (Rcompare x ((Int.floor x : ℝ))) = (if x = (Int.floor x : ℝ) then (0 : Int) else 1) := by
    unfold Rcompare
    have hnotlt : ¬ x < (Int.floor x : ℝ) := not_lt.mpr (Int.floor_le x)
    simp [hnotlt]
  -- Using standard floor/ceil-on-integers facts, the equality tests are equivalent.
  have hiff : (x = (Int.ceil x : ℝ)) ↔ (x = (Int.floor x : ℝ)) := by
    constructor
    · intro hcx
      -- From x = ⌈x⌉, infer ⌊x⌋ = ⌈x⌉, hence x = ⌊x⌋ as reals.
      have h1 : Int.floor x = Int.floor ((Int.ceil x : ℝ)) := by
        exact congrArg Int.floor hcx
      have h2 : Int.floor ((Int.ceil x : ℝ)) = Int.ceil x := Int.floor_intCast (Int.ceil x)
      have hfloor_eq_ceil : Int.floor x = Int.ceil x := by
        exact h1.trans h2
      -- Conclude x = ⌊x⌋ by transporting hcx through hfloor_eq_ceil
      have hcast : (Int.ceil x : ℝ) = (Int.floor x : ℝ) := by
        exact congrArg (fun n : Int => (n : ℝ)) hfloor_eq_ceil.symm
      exact hcx.trans hcast
    · intro hfx
      -- From x = ⌊x⌋, infer ⌈x⌉ = ⌊x⌋, hence x = ⌈x⌉ as reals.
      have h1 : Int.ceil x = Int.ceil ((Int.floor x : ℝ)) := by
        exact congrArg Int.ceil hfx
      have h2 : Int.ceil ((Int.floor x : ℝ)) = Int.floor x := Int.ceil_intCast (Int.floor x)
      have hceil_eq_floor : Int.ceil x = Int.floor x := by
        exact h1.trans h2
      -- Conclude x = ⌈x⌉ by transporting hfx through hceil_eq_floor
      have hcast : (Int.floor x : ℝ) = (Int.ceil x : ℝ) := by
        exact congrArg (fun n : Int => (n : ℝ)) hceil_eq_floor.symm
      exact hfx.trans hcast
  -- Discharge the equality by rewriting and cases.
  -- Goal after simp: prove (Rcompare (↑⌈x⌉) x) = (Rcompare x ↑⌊x⌋).
  -- Rewrite both sides with hL and hR, then case on x = ⌈x⌉.
  have : (Rcompare ((Int.ceil x : ℝ)) x) = (Rcompare x ((Int.floor x : ℝ))) := by
    by_cases hx : x = (Int.ceil x : ℝ)
    · -- Then also x = ⌊x⌋, by hiff
      have hx' : x = (Int.floor x : ℝ) := (hiff.mp hx)
      -- Evaluate each code via hL/hR and the equalities
      have hL0 : (Rcompare ((Int.ceil x : ℝ)) x) = 0 := by
        -- Use hL to rewrite, then evaluate the if using hx
        have : (if x = (Int.ceil x : ℝ) then (0 : Int) else 1) = 0 := ite_eq_left hx
        exact hL ▸ this
      have hR0 : (Rcompare x ((Int.floor x : ℝ))) = 0 := by
        -- Use hR to rewrite, then evaluate the if using hx'
        have : (if x = (Int.floor x : ℝ) then (0 : Int) else 1) = 0 := ite_eq_left hx'
        exact hR ▸ this
      rw [hL0, hR0]
    · -- Otherwise, x < ⌈x⌉ and ⌊x⌋ < x, so both codes reduce to 1
      -- Show each side evaluates to 1 explicitly.
      have hneqL : (Int.ceil x : ℝ) ≠ x := by simpa [eq_comm] using hx
      have hnotltL : ¬ (Int.ceil x : ℝ) < x := not_lt.mpr (Int.le_ceil x)
      have hfxne : x ≠ (Int.floor x : ℝ) := by
        -- If x = ⌊x⌋, then by hiff we would have x = ⌈x⌉, contradicting hx
        intro hxfloor; exact hx ((hiff.mpr hxfloor))
      have hnotltR : ¬ x < (Int.floor x : ℝ) := not_lt.mpr (Int.floor_le x)
      have hL1 : (Rcompare ((Int.ceil x : ℝ)) x) = 1 := by
        -- Not less and not equal ⇒ code = 1
        simp [Rcompare, hnotltL, hneqL]
      have hR1 : (Rcompare x ((Int.floor x : ℝ))) = 1 := by
        -- Not less and not equal ⇒ code = 1
        simp [Rcompare, hnotltR, hfxne]
      rw [hL1, hR1]
  -- Finish by restating the goal through the floor/ceiling definitions.
  change Rcompare ((Int.ceil x : Int) : ℝ) x =
    Rcompare x ((Int.floor x : Int) : ℝ)
  exact this

end CompareIntBounds

/-
  Basic results on radix and bpow (Coq Raux.v Section pow)
  In this Lean port, we express bpow via real integer powers (zpow).
-/
section PowBasics

/-- Coq {lit}`radix_pos`: the radix is positive as a real number. -/
theorem radix_pos (beta : Int) (hβ : 1 < beta) :
    0 < (beta : ℝ) := by
  -- From 1 < beta in ℤ, we get (1 : ℝ) < (beta : ℝ) by monotone casting,
  -- hence 0 < (beta : ℝ) by transitivity with 0 < 1.
  have h1β : (1 : ℝ) < (beta : ℝ) := by exact_mod_cast hβ
  have h01 : (0 : ℝ) < (1 : ℝ) := by exact zero_lt_one
  exact lt_trans h01 h1β

/-- Realization of bpow using real integer powers. -/
noncomputable def bpow (beta e : Int) : ℝ :=
  ((beta : ℝ) ^ e)

/-- Coq `IZR_Zpower_pos`: casting a positive integer power agrees with the
corresponding real integer power. -/
theorem IZR_Zpower_pos (n : Int) (m : FloatSpec.Core.Zaux.Positive) :
    ((FloatSpec.Core.Zaux.Zpower_pos n m : Int) : ℝ) =
      (n : ℝ) ^ (Int.ofNat (FloatSpec.Core.Zaux.positiveToNat m)) := by
  simp [FloatSpec.Core.Zaux.Zpower_pos, zpow_natCast]

/-- Coq {lit}`bpow_powerRZ`: {lean}`bpow` is the real integer power of the radix. -/
theorem bpow_powerRZ (beta e : Int) (_hβ : 1 < beta) :
    bpow beta e = (beta : ℝ) ^ e :=
  rfl

/-- Nonnegativity of bpow -/
theorem bpow_ge_0 (beta e : Int) (hβ : 1 < beta) :
    0 ≤ bpow beta e := by
  unfold bpow
  -- From 1 < beta in ℤ, we get (1 : ℝ) < (beta : ℝ), hence 0 < (beta : ℝ)
  have h1β : (1 : ℝ) < (beta : ℝ) := by exact_mod_cast hβ
  have hbpos : 0 < (beta : ℝ) := lt_trans zero_lt_one h1β
  -- Positive base to any integer power is positive, therefore nonnegative
  exact le_of_lt (zpow_pos hbpos e)

/-- Positivity of bpow -/
theorem bpow_gt_0 (beta e : Int) (hβ : 1 < beta) :
    0 < bpow beta e := by
  unfold bpow
  -- From 1 < beta in ℤ, get (beta : ℝ) > 1, hence positive
  have h1β : (1 : ℝ) < (beta : ℝ) := by exact_mod_cast hβ
  have hbpos : 0 < (beta : ℝ) := lt_trans zero_lt_one h1β
  -- Positive base to any integer power stays positive
  exact zpow_pos hbpos e

/-- Addition law for bpow exponents -/
theorem bpow_plus (beta e1 e2 : Int) (hβ : 1 < beta) :
    (beta : ℝ) ^ (e1 + e2) = (beta : ℝ) ^ e1 * (beta : ℝ) ^ e2 := by
  -- Goal: (beta : ℝ) ^ (e1 + e2) = (beta : ℝ) ^ e1 * (beta : ℝ) ^ e2
  -- This is `zpow_add₀` for a nonzero base
  have h1β : (1 : ℝ) < (beta : ℝ) := by exact_mod_cast hβ
  have hbpos : (0 : ℝ) < (beta : ℝ) := lt_trans zero_lt_one h1β
  have hbne : (beta : ℝ) ≠ 0 := ne_of_gt hbpos
  simpa using (zpow_add₀ hbne e1 e2)

/-- Value of bpow at 1 -/
theorem bpow_1 (beta : Int) (_hβ : 1 < beta) :
    (beta : ℝ) ^ (1 : Int) = (beta : ℝ) := by
  -- Use zpow at 1
  simp [zpow_one]

/-- Coq {lit}`bpow_plus_1`: {lit}`bpow (e + 1) = beta * bpow e`. -/
theorem bpow_plus_1 (beta e : Int) (hβ : 1 < beta) :
    (beta : ℝ) ^ (e + 1) = (beta : ℝ) * (beta : ℝ) ^ e := by
  -- zpow addition specialized to 1; use zpow_add₀ for nonzero base
  have h1β : (1 : ℝ) < (beta : ℝ) := by exact_mod_cast hβ
  have hbpos : (0 : ℝ) < (beta : ℝ) := lt_trans zero_lt_one h1β
  have hbne : (beta : ℝ) ≠ 0 := ne_of_gt hbpos
  -- Rearrange to match the target `(beta : ℝ) * (beta : ℝ) ^ e`
  simpa [zpow_one, mul_comm] using (zpow_add₀ hbne e (1 : Int))

/-- Opposite exponent law: bpow (-e) = 1 / bpow e -/
theorem bpow_opp (beta e : Int) (_hβ : 1 < beta) :
    (beta : ℝ) ^ (-e) = 1 / (beta : ℝ) ^ e := by
  -- Use zpow_neg
  simp [zpow_neg, one_div]

/-- Strict monotonicity of bpow in the exponent

    If {lean}`1 < beta` and {lean}`e1 < e2`, then {lean}`(beta : ℝ) ^ e1 < (beta : ℝ) ^ e2`.
-/
theorem bpow_lt (beta e1 e2 : Int) (hβ : 1 < beta) (hlt : e1 < e2) :
    (beta : ℝ) ^ e1 < (beta : ℝ) ^ e2 := by
  -- Transport base inequality to ℝ and apply strict monotonicity of zpow in the exponent
  have hβR : (1 : ℝ) < (beta : ℝ) := by exact_mod_cast hβ
  exact (zpow_lt_zpow_right₀ hβR hlt)

/-- Converse monotonicity: compare exponents via bpow values

    If {lean}`1 < beta` and {lean}`(beta : ℝ) ^ e1 < (beta : ℝ) ^ e2`, then {lean}`e1 < e2`.
-/
theorem lt_bpow (beta e1 e2 : Int)
    (hβ : 1 < beta) (hbpowlt : (beta : ℝ) ^ e1 < (beta : ℝ) ^ e2) :
    e1 < e2 := by
  -- Use strict monotonicity of zpow in the exponent for bases > 1
  -- to transport the inequality back to the exponents.
  have hβR : (1 : ℝ) < (beta : ℝ) := by exact_mod_cast hβ
  -- Strict monotonicity gives: (beta:ℝ)^e1 < (beta:ℝ)^e2 ↔ e1 < e2
  exact ((zpow_right_strictMono₀ hβR).lt_iff_lt).1 hbpowlt

/-- Monotonicity (≤) of bpow in the exponent -/
theorem bpow_le (beta e1 e2 : Int) (hβ : 1 < beta) (hle : e1 ≤ e2) :
    (beta : ℝ) ^ e1 ≤ (beta : ℝ) ^ e2 := by
  -- Transport base inequality to ℝ
  have hβR : (1 : ℝ) < (beta : ℝ) := by exact_mod_cast hβ
  -- Strict monotonicity in the exponent for bases > 1 yields monotonicity (≤)
  exact ((zpow_right_strictMono₀ hβR).monotone hle)

/-- Converse (≤) direction via bpow values -/
theorem le_bpow (beta e1 e2 : Int)
    (hβ : 1 < beta) (hle_pow : (beta : ℝ) ^ e1 ≤ (beta : ℝ) ^ e2) :
    e1 ≤ e2 := by
  -- Transport 1 < beta to ℝ
  have hβR : (1 : ℝ) < (beta : ℝ) := by exact_mod_cast hβ
  -- Prove by contradiction: assume ¬ e1 ≤ e2, i.e. e2 < e1
  by_contra hle
  have hlt_e : e2 < e1 := lt_of_not_ge hle
  -- Strict monotonicity of zpow in the exponent for bases > 1
  have hlt_pow : (beta : ℝ) ^ e2 < (beta : ℝ) ^ e1 :=
    zpow_lt_zpow_right₀ hβR hlt_e
  -- This contradicts (beta^e1) ≤ (beta^e2)
  have : (beta : ℝ) ^ e2 < (beta : ℝ) ^ e2 := lt_of_lt_of_le hlt_pow hle_pow
  exact (lt_irrefl _ this)

/-- Injectivity of bpow on the exponent -/
theorem bpow_inj (beta e1 e2 : Int)
    (hβ : 1 < beta) (heq : (beta : ℝ) ^ e1 = (beta : ℝ) ^ e2) :
    e1 = e2 := by
  have hβR : (1 : ℝ) < (beta : ℝ) := by exact_mod_cast hβ
  -- Strict monotonicity in the exponent implies injectivity
  exact (zpow_right_strictMono₀ hβR).injective heq

/-- Exponential form of bpow via Real.exp and Real.log -/
theorem bpow_exp (beta e : Int) (hβ : 1 < beta) :
    (beta : ℝ) ^ e = Real.exp ((e : ℝ) * Real.log (beta : ℝ)) := by
  -- From 1 < beta (as an integer), we get positivity on ℝ
  have hbposℤ : (0 : Int) < beta := lt_trans (by decide) hβ
  have hbposR : (0 : ℝ) < (beta : ℝ) := by exact_mod_cast hbposℤ
  -- Hence every zpow is positive, in particular (beta : ℝ) ^ e > 0
  have hpow_pos : 0 < (beta : ℝ) ^ e := zpow_pos hbposR _
  -- Logarithm of a positive zpow scales the exponent
  have hlog_zpow : Real.log ((beta : ℝ) ^ e) = (e : ℝ) * Real.log (beta : ℝ) := by
    simpa using Real.log_zpow hbposR e
  -- Conclude by exp∘log and the log_zpow identity
  -- (beta : ℝ) ^ e = exp (log ((beta : ℝ) ^ e)) = exp ((e : ℝ) * log beta)
  calc
    (beta : ℝ) ^ e
        = Real.exp (Real.log ((beta : ℝ) ^ e)) := (Real.exp_log hpow_pos).symm
    _ = Real.exp ((e : ℝ) * Real.log (beta : ℝ)) := by simpa [hlog_zpow]

/-- From bpow (e1 - 1) < bpow e2, deduce e1 ≤ e2 -/
theorem bpow_lt_bpow (beta e1 e2 : Int)
    (hβ : 1 < beta) (hpowlt : (beta : ℝ) ^ (e1 - 1) < (beta : ℝ) ^ e2) :
    e1 ≤ e2 := by
  -- From the strict inequality on powers, get a strict inequality on exponents
  have hβR : (1 : ℝ) < (beta : ℝ) := by exact_mod_cast hβ
  have hlt_exp : e1 - 1 < e2 := ((zpow_right_strictMono₀ hβR).lt_iff_lt).1 hpowlt
  -- Add 1 to both sides and use Int.lt_add_one_iff
  have hlt_add1 : e1 < e2 + 1 := by
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
      (add_lt_add_right hlt_exp 1)
  exact (Int.lt_add_one_iff).1 hlt_add1

/-- Uniqueness of the integer exponent bounding an absolute value by bpow -/
theorem bpow_unique_from_abs_payload (beta : Int) (x : ℝ) (e1 e2 : Int)
    (hβ : 1 < beta)
    (h1 : (beta : ℝ) ^ (e1 - 1) ≤ |x| ∧ |x| < (beta : ℝ) ^ e1)
    (h2 : (beta : ℝ) ^ (e2 - 1) ≤ |x| ∧ |x| < (beta : ℝ) ^ e2) :
    e1 = e2 := by
  -- Split hypotheses
  rcases h1 with ⟨hle1, hlt1⟩
  rcases h2 with ⟨hle2, hlt2⟩
  -- Transport base inequality to ℝ and use strict monotonicity of zpow in the exponent
  have hβR : (1 : ℝ) < (beta : ℝ) := by exact_mod_cast hβ
  -- From hle2 ≤ |x| and |x| < bpow e1, deduce bpow (e2-1) < bpow e1 ⇒ e2 ≤ e1
  have hlt21 : (beta : ℝ) ^ (e2 - 1) < (beta : ℝ) ^ e1 := lt_of_le_of_lt hle2 hlt1
  have hlt_exp21 : e2 - 1 < e1 := ((zpow_right_strictMono₀ hβR).lt_iff_lt).1 hlt21
  have hle21 : e2 ≤ e1 := by
    -- e2 - 1 < e1 ⇒ e2 < e1 + 1 ⇒ e2 ≤ e1
    have : e2 < e1 + 1 := by
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
        (add_lt_add_right hlt_exp21 1)
    exact (Int.lt_add_one_iff.mp this)
  -- Symmetrically, from hle1 ≤ |x| and |x| < bpow e2, deduce e1 ≤ e2
  have hlt12 : (beta : ℝ) ^ (e1 - 1) < (beta : ℝ) ^ e2 := lt_of_le_of_lt hle1 hlt2
  have hlt_exp12 : e1 - 1 < e2 := ((zpow_right_strictMono₀ hβR).lt_iff_lt).1 hlt12
  have hle12 : e1 ≤ e2 := by
    have : e1 < e2 + 1 := by
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
        (add_lt_add_right hlt_exp12 1)
    exact (Int.lt_add_one_iff.mp this)
  -- Antisymmetry yields equality of exponents
  exact le_antisymm hle12 hle21

/-- Coq `bpow_unique`: a real lying in both source half-open power bins has a
unique exponent.  Unlike the reusable absolute-value payload, the source
contract is stated directly about `x`. -/
theorem bpow_unique (beta : Int) (x : ℝ) (e1 e2 : Int)
    (hβ : 1 < beta)
    (h1 : (beta : ℝ) ^ (e1 - 1) ≤ x ∧ x < (beta : ℝ) ^ e1)
    (h2 : (beta : ℝ) ^ (e2 - 1) ≤ x ∧ x < (beta : ℝ) ^ e2) :
    e1 = e2 := by
  have hβR : (1 : ℝ) < (beta : ℝ) := by exact_mod_cast hβ
  have hbpos : (0 : ℝ) < (beta : ℝ) := zero_lt_one.trans hβR
  have hxpos : 0 < x := (zpow_pos hbpos (e1 - 1)).trans_le h1.1
  have hxabs : |x| = x := abs_of_pos hxpos
  exact bpow_unique_from_abs_payload beta x e1 e2 hβ
    (by simpa [hxabs] using h1) (by simpa [hxabs] using h2)

/-- Square-root law for even exponents: {lean}`Real.sqrt ((beta : ℝ) ^ (2 * e)) = (beta : ℝ) ^ e` -/
theorem sqrt_bpow (beta e : Int) (hβ : 1 < beta) :
    Real.sqrt ((beta : ℝ) ^ (2 * e)) = (beta : ℝ) ^ e := by
  -- From 1 < beta we get (beta : ℝ) > 0 hence nonzero
  have hbposℤ : (0 : Int) < beta := lt_trans (by decide) hβ
  have hbposR : (0 : ℝ) < (beta : ℝ) := by exact_mod_cast hbposℤ
  have hbne : (beta : ℝ) ≠ 0 := ne_of_gt hbposR
  -- Rewrite the exponent 2*e as e+e and expand using zpow_add₀
  have : Real.sqrt ((beta : ℝ) ^ (2 * e))
      = Real.sqrt (((beta : ℝ) ^ e) * ((beta : ℝ) ^ e)) := by
    simpa [two_mul, zpow_add₀ hbne]
  -- Now use √(x*x) = |x| and that (beta : ℝ) ^ e ≥ 0
  have hnonneg : 0 ≤ (beta : ℝ) ^ e := le_of_lt (zpow_pos hbposR e)
  have : Real.sqrt ((beta : ℝ) ^ (2 * e)) = |(beta : ℝ) ^ e| := by
    simpa [this]
      using (Real.sqrt_mul_self_eq_abs ((beta : ℝ) ^ e))
  -- Since (beta : ℝ) ^ e > 0, its absolute value is itself
  simpa [this, abs_of_nonneg hnonneg]

/-- Lower bound: bpow (e/2) ≤ sqrt (bpow e) -/
theorem sqrt_bpow_ge (beta e : Int) (hβ : 1 < beta) :
    (beta : ℝ) ^ (e / 2) ≤ Real.sqrt ((beta : ℝ) ^ e) := by
  -- Goal: (beta : ℝ)^(e/2) ≤ √((beta : ℝ)^e)
  -- From 1 < beta we get (beta : ℝ) > 0 hence nonzero
  have hbposℤ : (0 : Int) < beta := lt_trans (by decide) hβ
  have hbposR : (0 : ℝ) < (beta : ℝ) := by exact_mod_cast hbposℤ
  have hbne : (beta : ℝ) ≠ 0 := ne_of_gt hbposR
  -- Both sides are nonnegative
  have hx_nonneg : 0 ≤ (beta : ℝ) ^ (e / 2) := le_of_lt (zpow_pos hbposR (e / 2))
  have hy_nonneg : 0 ≤ (beta : ℝ) ^ e := le_of_lt (zpow_pos hbposR e)
  -- It suffices to show (beta^(e/2))^2 ≤ (beta^e)
  refine (Real.le_sqrt hx_nonneg hy_nonneg).2 ?_;
  -- Rewrite the right-hand side using the division algorithm: e = 2*(e/2) + e % 2
  have hdecomp : 2 * (e / 2) + e % 2 = e := by
    simpa using (Int.mul_ediv_add_emod e 2)
  -- Show: (beta^(e/2))^2 = (beta)^(2*(e/2))
  have hx_sq : ((beta : ℝ) ^ (e / 2)) ^ 2 = (beta : ℝ) ^ (2 * (e / 2)) := by
    -- x^2 = x*x and a^(m+n) = a^m * a^n (for a ≠ 0)
    -- so (beta^(e/2))^2 = beta^(e/2) * beta^(e/2) = beta^(2*(e/2))
    have hx_prod_exp :
        (beta : ℝ) ^ (e / 2) * (beta : ℝ) ^ (e / 2)
          = (beta : ℝ) ^ ((e / 2) + (e / 2)) := by
      simpa using (zpow_add₀ hbne (e / 2) (e / 2)).symm
    simpa [pow_two, two_mul] using hx_prod_exp
  -- Using the decomposition of e, rewrite (beta^e) as (beta)^(2*(e/2)) * (beta)^(e%2)
  have hy_fact : (beta : ℝ) ^ e
      = (beta : ℝ) ^ (2 * (e / 2)) * (beta : ℝ) ^ (e % 2) := by
    calc
      (beta : ℝ) ^ e
          = (beta : ℝ) ^ (2 * (e / 2) + e % 2) := by simpa [hdecomp]
      _ = (beta : ℝ) ^ (2 * (e / 2)) * (beta : ℝ) ^ (e % 2) := by
            simpa [zpow_add₀ hbne]
  -- Since (beta : ℝ) ^ (e % 2) ≥ 1 (as e%2 ∈ {0,1} and beta ≥ 1), we have the desired inequality
  have h_beta_ge_one : (1 : ℝ) ≤ (beta : ℝ) := by exact_mod_cast (le_of_lt hβ)
  -- For the remainder r = e % 2 ∈ {0,1}, we have 1 ≤ beta^r
  have honele : (1 : ℝ) ≤ (beta : ℝ) ^ (e % 2) := by
    -- For r = e % 2 ∈ {0,1}
    rcases (Int.emod_two_eq_zero_or_one e) with hr0 | hr1
    · simpa [hr0]
    · simpa [hr1] using h_beta_ge_one
  -- Put everything together: x^2 ≤ x^2 * beta^r = (beta^e)
  have hx2_le : ((beta : ℝ) ^ (e / 2)) ^ 2 ≤ (beta : ℝ) ^ e := by
    have hA_nonneg : 0 ≤ (beta : ℝ) ^ (2 * (e / 2)) := le_of_lt (zpow_pos hbposR _)
    calc
      ((beta : ℝ) ^ (e / 2)) ^ 2
          = (beta : ℝ) ^ (2 * (e / 2)) := hx_sq
      _ ≤ (beta : ℝ) ^ (2 * (e / 2)) * (beta : ℝ) ^ (e % 2) := by
            exact le_mul_of_one_le_right hA_nonneg honele
      _ = (beta : ℝ) ^ e := by simpa [hy_fact]
  exact hx2_le

/-- Coq `IZR_Zpower_nat`: integer natural powers cast to source `bpow`. -/
theorem IZR_Zpower_nat (r : FloatSpec.Core.Zaux.Radix) (e : Nat) :
    ((r.val ^ e : Int) : ℝ) = bpow r.val (Int.ofNat e) := by
  simp [bpow, zpow_natCast]

/-- Coq `IZR_Zpower`: nonnegative integer powers cast to source `bpow`. -/
theorem IZR_Zpower (r : FloatSpec.Core.Zaux.Radix) (e : Int) (he : 0 ≤ e) :
    ((FloatSpec.Core.Zaux.Zpower r.val e : Int) : ℝ) = bpow r.val e := by
  have he_cast : (e.toNat : Int) = e := Int.toNat_of_nonneg he
  rw [FloatSpec.Core.Zaux.Zpower, ite_eq_left he, bpow]
  simp only [Int.cast_pow, ← zpow_natCast, he_cast]

end PowBasics

/-
  Limited Principle of Omniscience (LPO) results from Coquelicot, via Raux.v.
  Public source exports return proof-carrying alternatives. The old optional
  choices and their direct specifications remain explicitly local adapters.
 -/
/-!  LPO (limited principle of omniscience) corner -/
section LPO

/-- Legacy optional projection for minimal natural witnesses. -/
@[flocq_local "Optional compatibility choice; source LPO_min returns a proof-carrying alternative"]
noncomputable def LPO_min_choice (P : Nat → Prop) : (Option Nat) :=
  by
    classical
    -- Choose the least witness when it exists
    exact
      if h : ∃ n, P n then
        some (Nat.find h)
      else
        none

/-- Compatibility specification of the optional minimal-witness choice. -/
@[flocq_local "Legacy optional-choice specification, not the proof-carrying LPO_min source export"]
theorem LPO_min_choice_spec (P : Nat → Prop)
    (_hdec : ∀ n : Nat, P n ∨ ¬ P n) :
    match LPO_min_choice P with
      | some n => P n ∧ ∀ i, i < n → ¬ P i
      | none => ∀ n : Nat, ¬ P n := by
  unfold LPO_min_choice
  classical
  -- Split on existence of a witness
  by_cases h : ∃ n, P n
  · -- some witness exists: return the least one via Nat.find
    simp [h]
    refine And.intro ?hP ?hmin
    · -- P (Nat.find h)
      exact Nat.find_spec h
    · -- minimality in the `simp`-rewritten form
      intro i hi
      -- `Nat.lt_find_iff` rewrites `i < Nat.find h` to `∀ m ≤ i, ¬ P m`.
      -- So we can instantiate it at `m = i`.
      exact hi i le_rfl
  · -- no witness exists: return none and prove ∀ n, ¬ P n
    -- From ¬∃ n, P n, derive ∀ n, ¬ P n
    simpa [h] using (not_exists.mp h)

/-- Legacy optional projection for natural witnesses. -/
@[flocq_local "Optional compatibility choice; source LPO returns a proof-carrying alternative"]
noncomputable def LPO_choice (P : Nat → Prop) : (Option Nat) :=
  by
    classical
    -- Choose a witness when it exists (take the least one), otherwise none
    exact
      if h : ∃ n, P n then
        some (Nat.find h)
      else
        none

/-- Compatibility specification of the optional natural-witness choice. -/
@[flocq_local "Legacy optional-choice specification, not the proof-carrying LPO source export"]
theorem LPO_choice_spec (P : Nat → Prop)
    (_hdec : ∀ n : Nat, P n ∨ ¬ P n) :
    match LPO_choice P with
      | some n => P n
      | none => ∀ n : Nat, ¬ P n := by
  unfold LPO_choice
  classical
  -- Split on existence of a witness
  by_cases h : ∃ n, P n
  · -- some witness exists: return the least one via Nat.find
    simp [h]
    -- We must show P (Nat.find h)
    exact Nat.find_spec h
  · -- no witness exists: return none and prove ∀ n, ¬ P n
    -- From ¬∃ n, P n, derive ∀ n, ¬ P n
    simpa [h] using (not_exists.mp h)

/-- Legacy optional projection for integer witnesses. -/
@[flocq_local "Optional compatibility choice; source LPO_Z returns a proof-carrying alternative"]
noncomputable def LPO_Z_choice (P : Int → Prop) : (Option Int) :=
  by
    classical
    -- Choose a witness when it exists (using classical choice), otherwise none
    exact
      if h : ∃ n, P n then
        some (Classical.choose h)
      else
        none

/-- Compatibility specification of the optional integer-witness choice. -/
@[flocq_local "Legacy optional-choice specification, not the proof-carrying LPO_Z source export"]
theorem LPO_Z_choice_spec (P : Int → Prop)
    (_hdec : ∀ n : Int, P n ∨ ¬ P n) :
    match LPO_Z_choice P with
      | some n => P n
      | none => ∀ n : Int, ¬ P n := by
  unfold LPO_Z_choice
  classical
  -- Split on existence of a witness
  by_cases h : ∃ n, P n
  · -- some witness exists: return one via classical choice
    simp [h]
    -- We must show P (Classical.choose h)
    exact Classical.choose_spec h
  · -- no witness exists: return none and prove ∀ n, ¬ P n
    -- From ¬∃ n, P n, derive ∀ n, ¬ P n
    simpa [h] using (not_exists.mp h)

/-- Source minimal-witness alternative, carrying both membership and the
absence of every smaller witness, or universal nonexistence. -/
@[flocq_source "src/Core/Raux.v" 2271 "LPO_min"]
noncomputable def LPO_min (P : Nat → Prop) (_hdec : ∀ n, P n ∨ ¬ P n) :
    PSum {n : Nat // P n ∧ ∀ i : Nat, i < n → ¬ P i} (∀ n : Nat, ¬ P n) := by
  classical
  exact if h : ∃ n, P n then
    .inl ⟨Nat.find h, Nat.find_spec h, fun _ hi => Nat.find_min h hi⟩
  else .inr (not_exists.mp h)

/-- Source natural-witness alternative. The positive branch retains its
membership proof rather than returning a bare optional natural. -/
@[flocq_source "src/Core/Raux.v" 2384 "LPO"]
noncomputable def LPO (P : Nat → Prop) (hdec : ∀ n, P n ∨ ¬ P n) :
    PSum {n : Nat // P n} (∀ n : Nat, ¬ P n) :=
  match LPO_min P hdec with
  | .inl witness => .inl ⟨witness.val, witness.property.1⟩
  | .inr noWitness => .inr noWitness

/-- Source integer-witness alternative. As in Rocq, first seek a
nonnegative witness, then the negation of a natural witness. -/
@[flocq_source "src/Core/Raux.v" 2396 "LPO_Z"]
noncomputable def LPO_Z (P : Int → Prop) (hdec : ∀ n, P n ∨ ¬ P n) :
    PSum {n : Int // P n} (∀ n : Int, ¬ P n) := by
  match LPO (fun n : Nat => P (n : Int)) (fun n => hdec n) with
  | .inl witness => exact .inl ⟨witness.val, witness.property⟩
  | .inr noPositive =>
    match LPO (fun n : Nat => P (-(n : Int))) (fun n => hdec (-(n : Int))) with
    | .inl witness => exact .inl ⟨-(witness.val : Int), witness.property⟩
    | .inr noNegative =>
      refine .inr (fun n => ?_)
      cases n with
      | ofNat n => exact noPositive n
      | negSucc n => exact noNegative (n + 1)

end LPO

/-
  Magnitude function and related lemmas (Coq Raux.v Section pow)
  We parameterize by an integer base `beta` (≥ 2), analogous to Coq's `radix`.
-/
section Mag

/-- Coq {lit}`mag_prop`: witness record for a magnitude exponent. -/
structure mag_prop (beta : Int) (x : ℝ) : Type where
  /-- The exponent witnessing the magnitude bound. -/
  mag_val : Int
  /-- Coq bound: if x ≠ 0 then β^(e-1) ≤ |x| < β^e. -/
  mag_spec : x ≠ 0 → bpow beta (mag_val - 1) ≤ |x| ∧ |x| < bpow beta mag_val

/-- Coq {lit}`mag_val` projection. -/
abbrev mag_val {beta : Int} {x : ℝ} (m : mag_prop beta x) : Int := m.mag_val

/-- Coq {lit}`Build_mag_prop` constructor alias. -/
abbrev Build_mag_prop {beta : Int} {x : ℝ} (e : Int)
    (h : x ≠ 0 → bpow beta (e - 1) ≤ |x| ∧ |x| < bpow beta e) : mag_prop beta x :=
  { mag_val := e, mag_spec := h }

/-- Magnitude of a real number with respect to base {lit}`beta`.

    In Coq, {lit}`mag` is characterized by {lit}`bpow` bounds: for nonzero {lit}`x`,
    {lit}`bpow (e - 1) ≤ |x| < bpow e`, where {lit}`e = mag x`.
    We model it as a pure computation.

    **IMPORTANT**: We use `⌊log|x|/log β⌋ + 1` (floor + 1) to match Coq's semantics.
    This ensures `mag(β^e) = e + 1`, giving the strict upper bound {lit}`|x| < β^(mag x)`.
    The previous ceiling-based definition gave `mag(β^e) = e`, which created
    boundary cases where {lit}`|x| = β^(mag x)` that don't exist in Coq.
-/
noncomputable def mag (beta : Int) (x : ℝ) : Int :=
  -- Use floor + 1 to match Coq's strict upper bound semantics.
  -- Coq's concrete witness is `Zfloor (ln |x| / ln beta) + 1`; since
  -- Coq's `ln 0` reduces to zero, its observable value at zero is one.
  if x = 0 then 1 else ⌊Real.log (abs x) / Real.log (beta : ℝ)⌋ + 1

/-- Uniqueness of magnitude from bpow bounds.
    With Coq semantics: β^(e-1) ≤ |x| < β^e implies mag(x) = e.
    Note: non-strict lower bound, strict upper bound. -/
theorem mag_unique (beta : Int) (x : ℝ) (e : Int)
    (hβ : 1 < beta)
    (hlow : (beta : ℝ) ^ (e - 1) ≤ |x|)
    (hupp : |x| < (beta : ℝ) ^ e) :
    mag beta x = e := by
  unfold mag
  -- From 1 < beta (as ℤ), get positivity on ℝ
  have hbposℤ : (0 : Int) < beta := lt_trans (by decide) hβ
  have hbposR : (0 : ℝ) < (beta : ℝ) := by exact_mod_cast hbposℤ
  have hb_gt1R : (1 : ℝ) < (beta : ℝ) := by exact_mod_cast hβ
  -- |x| is strictly positive since β^(e-1) > 0 and |x| ≥ β^(e-1)
  have hxpos : 0 < |x| := lt_of_lt_of_le (zpow_pos hbposR (e - 1)) hlow
  have hx0 : x ≠ 0 := abs_pos.mp hxpos
  -- Set L := log |x| / log β to simplify the algebra
  set L : ℝ := Real.log (abs x) / Real.log (beta : ℝ) with hLdef
  -- log β is positive (since β > 1)
  have hlogβ_pos : 0 < Real.log (beta : ℝ) := by
    have : 0 < Real.log (beta : ℝ) ↔ 1 < (beta : ℝ) :=
      Real.log_pos_iff (x := (beta : ℝ)) (le_of_lt hbposR)
    exact this.mpr hb_gt1R
  have hlogβ_ne : Real.log (beta : ℝ) ≠ 0 := ne_of_gt hlogβ_pos
  have hL_mul : L * Real.log (beta : ℝ) = Real.log (abs x) := by
    calc
      L * Real.log (beta : ℝ)
          = (Real.log (abs x) / Real.log (beta : ℝ)) * Real.log (beta : ℝ) := by
              simpa [hLdef]
      _   = Real.log (abs x) * Real.log (beta : ℝ) / Real.log (beta : ℝ) := by
              simpa [div_mul_eq_mul_div]
      _   = Real.log (abs x) := by
              simpa [hlogβ_ne] using
                (mul_div_cancel' (Real.log (abs x)) (Real.log (beta : ℝ)))
  -- Upper bound: |x| < β^e implies L < e
  have hlog_lt : Real.log (abs x) < Real.log ((beta : ℝ) ^ e) :=
    Real.log_lt_log hxpos hupp
  have hlog_zpow_e : Real.log ((beta : ℝ) ^ e) = (e : ℝ) * Real.log (beta : ℝ) := by
    simpa using Real.log_zpow hbposR e
  have hL_lt_e : L < (e : ℝ) := by
    have hmul_lt : L * Real.log (beta : ℝ) < (e : ℝ) * Real.log (beta : ℝ) := by
      simpa [hL_mul, hlog_zpow_e] using hlog_lt
    exact (lt_of_mul_lt_mul_right hmul_lt (le_of_lt hlogβ_pos))
  -- From L < e, floor(L) < e, so floor(L) ≤ e - 1
  have hfloor_lt : Int.floor L < e := Int.floor_lt.mpr hL_lt_e
  have hfloor_le_em1 : Int.floor L ≤ e - 1 := by grind
  -- Lower bound: β^(e-1) ≤ |x| implies (e-1) ≤ L
  have hlog_le : Real.log ((beta : ℝ) ^ (e - 1)) ≤ Real.log (abs x) :=
    Real.log_le_log (zpow_pos hbposR (e - 1)) hlow
  have hlog_zpow_em1 : Real.log ((beta : ℝ) ^ (e - 1))
      = (e - 1 : ℝ) * Real.log (beta : ℝ) := by
    simpa using Real.log_zpow hbposR (e - 1)
  have hexm1_le_L : (e - 1 : ℝ) ≤ L := by
    have hmul_le : (e - 1 : ℝ) * Real.log (beta : ℝ) ≤ L * Real.log (beta : ℝ) := by
      simpa [hL_mul, hlog_zpow_em1] using hlog_le
    exact (le_of_mul_le_mul_right hmul_le hlogβ_pos)
  -- From (e-1) ≤ L, we have e - 1 ≤ floor(L)
  have h_em1_le_floor : e - 1 ≤ Int.floor L := by
    have h : ((e - 1 : Int) : ℝ) ≤ L := by simpa using hexm1_le_L
    exact Int.le_floor.mpr h
  -- Combining: e - 1 ≤ floor(L) ≤ e - 1, so floor(L) = e - 1
  have hfloor_eq : Int.floor L = e - 1 := le_antisymm hfloor_le_em1 h_em1_le_floor
  -- Therefore floor(L) + 1 = e
  have hfloor_add1_eq : Int.floor L + 1 = e := by grind
  -- Finalize: discharge the conditional (x ≠ 0)
  simp only [hx0, ite_false]
  exact hfloor_add1_eq

/-- Opposite preserves magnitude: mag (-x) = mag x -/
theorem mag_opp (beta : Int) (x : ℝ) (_hβ : 1 < beta) :
    mag beta (-x) = mag beta x := by
  simp [mag]

/-- Absolute value preserves magnitude: mag |x| = mag x -/
theorem mag_abs (beta : Int) (x : ℝ) (_hβ : 1 < beta) :
    mag beta |x| = mag beta x := by
  simp [mag]

/-- Uniqueness under positivity: for {given -show}`β`, {given -show}`x : ℝ`, {given -show}`e : ℤ`, if {lean}`0 < x` and `β^(e-1) ≤ x < β^e`, then {lean}`mag β x = e`.

    Note: with Coq semantics (floor+1), bounds are: non-strict lower, strict upper.
-/
theorem mag_unique_pos_from_positive_payload (beta : Int) (x : ℝ) (e : Int)
    (hβ : 1 < beta)
    (hxpos : 0 < x)
    (hlow : (beta : ℝ) ^ (e - 1) ≤ x)
    (hupp : x < (beta : ℝ) ^ e) :
    mag beta x = e := by
  -- Reduce to `mag_unique` by rewriting |x| to x using positivity
  have hxabs : |x| = x := abs_of_pos hxpos
  -- Assemble the hypothesis required by `mag_unique` (Coq bounds: non-strict lower, strict upper)
  have hlow' : (beta : ℝ) ^ (e - 1) ≤ |x| := by
    simpa [hxabs] using hlow
  have hupp' : |x| < (beta : ℝ) ^ e := by
    simpa [hxabs] using hupp
  -- Apply the previously proven uniqueness lemma
  exact mag_unique beta x e hβ hlow' hupp'

/-- Coq `mag_unique_pos`: the source interval itself implies positivity; it is
not an additional public premise. -/
theorem mag_unique_pos (beta : Int) (x : ℝ) (e : Int)
    (hβ : 1 < beta)
    (h : (beta : ℝ) ^ (e - 1) ≤ x ∧ x < (beta : ℝ) ^ e) :
    mag beta x = e := by
  have hβR : (1 : ℝ) < (beta : ℝ) := by exact_mod_cast hβ
  have hbpos : (0 : ℝ) < (beta : ℝ) := zero_lt_one.trans hβR
  have hxpos : 0 < x := (zpow_pos hbpos (e - 1)).trans_le h.1
  exact mag_unique_pos_from_positive_payload beta x e hβ hxpos h.1 h.2

/-- Coq {lit}`mag_le_bpow`: if {lit}`x ≠ 0` and {lit}`|x| < bpow e`, then
    {lit}`mag x ≤ e`. -/
theorem mag_le_bpow (beta : Int) (x : ℝ) (e : Int)
    (hβ : 1 < beta)
    (hx_ne : x ≠ 0)
    (hx_lt : |x| < (beta : ℝ) ^ e) :
    mag beta x ≤ e := by
  unfold mag
  -- Base > 1 on ℝ and hence positive
  have hβR : (1 : ℝ) < (beta : ℝ) := by exact_mod_cast hβ
  have hbposR : (0 : ℝ) < (beta : ℝ) := lt_trans zero_lt_one hβR
  -- Positivity of |x| from x ≠ 0
  have hx_pos : 0 < |x| := by
    simpa using (abs_pos.mpr hx_ne)
  -- Take logs (strictly increasing on ℝ>0)
  have hlog_lt : Real.log (abs x) < Real.log ((beta : ℝ) ^ e) :=
    Real.log_lt_log hx_pos hx_lt
  -- Express log of the power
  have hlog_pow : Real.log ((beta : ℝ) ^ e) = (e : ℝ) * Real.log (beta : ℝ) := by
    simpa using Real.log_zpow hbposR e
  -- Denominator log β is positive since β > 1
  have hlogβ_pos : 0 < Real.log (beta : ℝ) := by
    -- Use the specialized equivalence 0 < log β ↔ 1 < β (for β > 0)
    have : 0 < Real.log (beta : ℝ) ↔ 1 < (beta : ℝ) :=
      Real.log_pos_iff (x := (beta : ℝ)) (le_of_lt hbposR)
    exact this.mpr hβR
  -- Let L := log|x| / log β
  set L : ℝ := Real.log (abs x) / Real.log (beta : ℝ) with hLdef
  -- From log|x| < e * log β and log β > 0, deduce L < e
  have hL_lt : L < e := by
    have : Real.log (abs x) < (e : ℝ) * Real.log (beta : ℝ) := by simpa [hlog_pow] using hlog_lt
    -- a/c < b  ↔  a < b*c for c>0
    have := (div_lt_iff₀ hlogβ_pos).mpr this
    simpa [hLdef] using this
  -- floor L + 1 ≤ e from L < e (since floor L < e implies floor L + 1 ≤ e)
  have hfloor_lt : Int.floor L < e := Int.floor_lt.mpr hL_lt
  have hfloor_add1_le : Int.floor L + 1 ≤ e := Int.lt_iff_add_one_le.mp hfloor_lt
  -- Under x ≠ 0, mag returns ⌊L⌋ + 1, so it suffices to use hfloor_add1_le
  simpa [mag, hLdef, hx_ne] using hfloor_add1_le

/-- Coq {lit}`mag_le_abs`: if x ≠ 0 and |x| ≤ |y| then mag x ≤ mag y

    The chosen zero magnitude is one, so the claim with x = 0 is false in general
    (for 1 < beta and 0 < |y| < 1, we have mag 0 = 1 > mag y). We therefore
    assume x ≠ 0; this also forces y ≠ 0 under |x| ≤ |y|.
-/
theorem mag_le_abs (beta : Int) (x y : ℝ)
    (hβ : 1 < beta)
    (hx_ne : x ≠ 0)
    (hxy : |x| ≤ |y|) :
    mag beta x ≤ mag beta y := by
  -- Unpack hypotheses and derive basic positivity facts
  have hβR : (1 : ℝ) < (beta : ℝ) := by exact_mod_cast hβ
  have hbpos : (0 : ℝ) < (beta : ℝ) := lt_trans zero_lt_one hβR
  have hx_pos : 0 < |x| := by simpa using (abs_pos.mpr hx_ne)
  have hy_pos : 0 < |y| := lt_of_lt_of_le hx_pos hxy
  have hy_ne : y ≠ 0 := by exact (abs_pos.mp hy_pos)
  -- Reduce to an inequality between floors
  -- using the nonzero facts to discharge the conditionals.
  simp [mag, hx_ne, hy_ne]
  -- Normalize the goal to use |x| and |y| explicitly
   -- logβ > 0, so dividing preserves ≤
  have hlogβ_pos : 0 < Real.log (beta : ℝ) := by
    have : 0 < Real.log (beta : ℝ) ↔ 1 < (beta : ℝ) :=
      Real.log_pos_iff (x := (beta : ℝ)) (le_of_lt hbpos)
    exact this.mpr hβR

  -- Lx, Ly as shorthands
  set Lx : ℝ := Real.log (abs x) / Real.log (beta : ℝ) with hLx
  set Ly : ℝ := Real.log (abs y) / Real.log (beta : ℝ) with hLy

  -- log is monotone on (0, ∞), so log|x| ≤ log|y|
  have hlog_le : Real.log (abs x) ≤ Real.log (abs y) :=
    Real.log_le_log hx_pos hxy

  -- Multiply by logβ and cancel (positive), to get Lx ≤ Ly
  have hLx_mul : Lx * Real.log (beta : ℝ) = Real.log (abs x) := by
    have hne : Real.log (beta : ℝ) ≠ 0 := ne_of_gt hlogβ_pos
    calc
      Lx * Real.log (beta : ℝ)
          = (Real.log (abs x) / Real.log (beta : ℝ)) * Real.log (beta : ℝ) := by simpa [hLx]
      _ = Real.log (abs x) := by
          simpa [hne, div_mul_eq_mul_div] using
            (mul_div_cancel' (Real.log (abs x)) (Real.log (beta : ℝ)))
  have hLy_mul : Ly * Real.log (beta : ℝ) = Real.log (abs y) := by
    have hne : Real.log (beta : ℝ) ≠ 0 := ne_of_gt hlogβ_pos
    calc
      Ly * Real.log (beta : ℝ)
          = (Real.log (abs y) / Real.log (beta : ℝ)) * Real.log (beta : ℝ) := by simpa [hLy]
      _ = Real.log (abs y) := by
          simpa [hne, div_mul_eq_mul_div] using
            (mul_div_cancel' (Real.log (abs y)) (Real.log (beta : ℝ)))

  have hmul_le : Lx * Real.log (beta : ℝ) ≤ Ly * Real.log (beta : ℝ) := by
    simpa [hLx_mul, hLy_mul] using hlog_le
  have hLx_le_Ly : Lx ≤ Ly := (le_of_mul_le_mul_right hmul_le hlogβ_pos)

  -- Floor is monotone, so floor+1 is also monotone
  have hfloor : Int.floor Lx ≤ Int.floor Ly := Int.floor_mono hLx_le_Ly
  have hfloor_add1 : Int.floor Lx + 1 ≤ Int.floor Ly + 1 := by grind

  -- Unfold mag on both sides.
  -- This makes the goal defeq to `⌊Lx⌋ + 1 ≤ ⌊Ly⌋ + 1`.
  simpa [mag, hx_ne, hy_ne, hLx, hLy]
    using hfloor_add1

/-- Coq `mag_le`: positive-order monotonicity of magnitude. -/
theorem mag_le (beta : Int) (x y : ℝ)
    (hβ : 1 < beta) (hx : 0 < x) (hxy : x ≤ y) :
    mag beta x ≤ mag beta y := by
  have hy : 0 < y := hx.trans_le hxy
  exact mag_le_abs beta x y hβ (ne_of_gt hx) (by simpa [abs_of_pos hx, abs_of_pos hy])

/-- If {lit}`0 < |x| < bpow e` then {lit}`mag x ≤ e`

    For nonzero inputs this port computes {lit}`mag` as the floor of the
    base-beta logarithm plus one. The strict bound {lit}`|x| < (beta : ℝ) ^ e`
    implies {lit}`log_beta |x| < e`, hence {lit}`mag x ≤ e`.
    This corrects the direction compared to an earlier draft. -/
theorem lt_mag_from_bpow_payload (beta : Int) (x : ℝ) (e : Int)
    (hβ : 1 < beta)
    (hxpos : 0 < |x|)
    (hxlt : |x| < (beta : ℝ) ^ e) :
    mag beta x ≤ e := by
  -- Strengthen 0 < |x| to x ≠ 0 and reuse `mag_le_bpow`.
  have hx_ne : x ≠ 0 := by
    intro hx; simpa [hx] using hxpos
  exact mag_le_bpow beta x e hβ hx_ne hxlt

/-- Magnitude of bpow e is e + 1 (Coq semantics).
    With floor+1 definition: mag(β^e) = ⌊log(β^e)/log β⌋ + 1 = ⌊e⌋ + 1 = e + 1.
    This matches Coq: β^e ≤ β^e < β^(e+1), so mag(β^e) = e + 1. -/
theorem mag_bpow (beta e : Int) (hβ : 1 < beta) :
    mag beta ((beta : ℝ) ^ e) = e + 1 := by
  -- Compute `mag` on the specific input `(β : ℝ)^e`.
  have hβR : (1 : ℝ) < (beta : ℝ) := by exact_mod_cast hβ
  have hbposR : (0 : ℝ) < (beta : ℝ) := lt_trans zero_lt_one hβR
  -- Positivity implies non-zeroness for zpow
  have hx_pos : 0 < (beta : ℝ) ^ e := zpow_pos hbposR e
  have hx_ne : ((beta : ℝ) ^ e) ≠ 0 := ne_of_gt hx_pos
  -- Compute the logarithm of the power
  have hlog_pow : Real.log ((beta : ℝ) ^ e) = (e : ℝ) * Real.log (beta : ℝ) := by
    simpa using Real.log_zpow hbposR e
  -- log β is positive hence nonzero (since β > 1)
  have hlogβ_pos : 0 < Real.log (beta : ℝ) := by
    have : 0 < Real.log (beta : ℝ) ↔ 1 < (beta : ℝ) :=
      Real.log_pos_iff (x := (beta : ℝ)) (le_of_lt hbposR)
    exact this.mpr hβR
  have hlogβ_ne : Real.log (beta : ℝ) ≠ 0 := ne_of_gt hlogβ_pos
  -- Quotient simplifies to `e` since `log (β) ≠ 0`
  have hquot : ((e : ℝ) * Real.log (beta : ℝ)) / Real.log (beta : ℝ) = (e : ℝ) := by
    simpa [hlogβ_ne] using (mul_div_cancel' (e : ℝ) (Real.log (beta : ℝ)))
  -- Now discharge the conditional `x = 0` and apply floor+1
  -- `⌊(e : ℝ)⌋ + 1 = e + 1` for any integer `e`.
  have hfloor_eq : Int.floor (e : ℝ) = e := Int.floor_intCast e
  -- With floor+1 definition, mag(β^e) = ⌊e⌋ + 1 = e + 1
  simp only [mag, hx_ne, ite_false,
         abs_of_nonneg (le_of_lt hx_pos), hlog_pow, hquot, hfloor_eq]

/-- Coq `Raux.mag_gt_bpow`: if `bpow e ≤ |x|`, then `e < mag x`. -/
theorem mag_gt_bpow (beta : Int) (x : ℝ) (e : Int)
    (hβ : 1 < beta)
    (hle : (beta : ℝ) ^ e ≤ |x|) :
    e < mag beta x := by
  have hβR : (1 : ℝ) < (beta : ℝ) := by exact_mod_cast hβ
  have hbpos : (0 : ℝ) < (beta : ℝ) := lt_trans zero_lt_one hβR
  have hx_pos : 0 < |x| := lt_of_lt_of_le (zpow_pos hbpos e) hle
  have hx_ne : x ≠ 0 := abs_pos.mp hx_pos
  set L : ℝ := Real.log (abs x) / Real.log (beta : ℝ)
  have hlogβ_pos : 0 < Real.log (beta : ℝ) := by
    have : 0 < Real.log (beta : ℝ) ↔ 1 < (beta : ℝ) :=
      Real.log_pos_iff (x := (beta : ℝ)) (le_of_lt hbpos)
    exact this.mpr hβR
  have hlog_le :
      Real.log ((beta : ℝ) ^ e) ≤ Real.log (abs x) :=
    Real.strictMonoOn_log.monotoneOn
      (Set.mem_Ioi.mpr (zpow_pos hbpos e)) (Set.mem_Ioi.mpr hx_pos) hle
  have hpow_log :
      Real.log ((beta : ℝ) ^ e) = (e : ℝ) * Real.log (beta : ℝ) := by
    simpa using Real.log_zpow hbpos e
  have he_le_L : (e : ℝ) ≤ L := by
    have := (le_div_iff₀ hlogβ_pos).mpr (by simpa [hpow_log] using hlog_le)
    simpa [L] using this
  have he_le_floor : e ≤ Int.floor L := Int.le_floor.mpr he_le_L
  have hfinal : e < Int.floor L + 1 := by omega
  simpa [mag, hx_ne, L] using hfinal

/-- Coq `Raux.mag_ge_bpow`: the non-strict shifted lower bound. -/
theorem mag_ge_bpow (beta : Int) (x : ℝ) (e : Int)
    (hβ : 1 < beta)
    (hle : (beta : ℝ) ^ (e - 1) ≤ |x|) :
    e ≤ mag beta x := by
  by_cases hxe : |x| < (beta : ℝ) ^ e
  · exact le_of_eq (mag_unique beta x e hβ hle hxe).symm
  · exact le_of_lt (mag_gt_bpow beta x e hβ (le_of_not_gt hxe))

/-- If mag x < e then |x| < bpow e -/
theorem bpow_mag_gt_from_strict_mag_payload (beta : Int) (x : ℝ) (e : Int)
    (hβ : 1 < beta)
    (hlt : (mag beta x) < e) :
    |x| < (beta : ℝ) ^ e := by
  have hβR : (1 : ℝ) < (beta : ℝ) := by exact_mod_cast hβ
  have hbpos : 0 < (beta : ℝ) := lt_trans zero_lt_one hβR
  by_cases hx0 : x = 0
  ·
    -- |x| = 0 and β^e > 0 when β > 0
    have : 0 < (beta : ℝ) ^ e := zpow_pos hbpos e
    simpa [hx0, abs_zero] using this
  ·
    -- Nonzero case
    have hx_pos : 0 < |x| := abs_pos.mpr hx0
    -- L := log|x| / logβ and mag = ⌊L⌋ + 1 (Coq semantics)
    set L : ℝ := Real.log (abs x) / Real.log (beta : ℝ) with hL
    have hmag_run : (mag beta x) = Int.floor L + 1 := by
      simp [mag, hx0, hL]
    have hfloor_add1_lt : Int.floor L + 1 < e := hmag_run ▸ hlt

    -- From ⌊L⌋ + 1 < e get L < e (since L < ⌊L⌋ + 1 by floor property)
    have hL_lt : L < (e : ℝ) := by
      have hL_lt_floor_add1 : L < Int.floor L + 1 := Int.lt_floor_add_one L
      calc L < Int.floor L + 1 := hL_lt_floor_add1
        _ < e := by exact_mod_cast hfloor_add1_lt

    -- log β > 0
    have hlogβ_pos : 0 < Real.log (beta : ℝ) := by
      have : 0 < Real.log (beta : ℝ) ↔ 1 < (beta : ℝ) :=
        Real.log_pos_iff (x := (beta : ℝ)) (le_of_lt hbpos)
      exact this.mpr hβR
    have hlogβ_ne : Real.log (beta : ℝ) ≠ 0 := ne_of_gt hlogβ_pos

    -- L * log β = log |x|
    have hL_mul : L * Real.log (beta : ℝ) = Real.log (abs x) := by
      calc
        L * Real.log (beta : ℝ)
            = (Real.log (abs x) / Real.log (beta : ℝ)) * Real.log (beta : ℝ) := by
                simpa [hL]
        _ = Real.log (abs x) * Real.log (beta : ℝ) / Real.log (beta : ℝ) := by
                simpa [div_mul_eq_mul_div]
        _ = Real.log (abs x) := by
                simpa [hlogβ_ne] using
                  (mul_div_cancel' (Real.log (abs x)) (Real.log (beta : ℝ)))

    -- Turn L < e into log|x| < e * log β
    have hlog_lt : Real.log (abs x) < (e : ℝ) * Real.log (beta : ℝ) := by
      have := mul_lt_mul_of_pos_right hL_lt hlogβ_pos
      simpa [hL_mul, mul_comm, mul_left_comm, mul_assoc] using this

    -- Exponentiate: |x| < exp(e * log β)
    have h_abs_lt : |x| < Real.exp ((e : ℝ) * Real.log (beta : ℝ)) :=
      (Real.log_lt_iff_lt_exp (x := |x|) hx_pos).1 hlog_lt

    -- exp(e * log β) = β^e  (NO `simp/simpa`, just `rw`)
    have h_exp_eq : Real.exp ((e : ℝ) * Real.log (beta : ℝ)) = (beta : ℝ) ^ e := by
      have hlog : (e : ℝ) * Real.log (beta : ℝ) = Real.log ((beta : ℝ) ^ e) := by
        -- log(β^e) = e * log β
        simpa using (Real.log_zpow hbpos e).symm
      have hbpow_pos : 0 < (beta : ℝ) ^ e := zpow_pos hbpos e
      -- rewrite then close with exp_log
      rw [hlog, Real.exp_log hbpow_pos]

    -- Conclude
    simpa [h_exp_eq] using h_abs_lt

/-- If e ≤ mag x then bpow (e - 1) ≤ |x|

    Note: this requires {lit}`x ≠ 0`. For {lit}`x = 0`, we have {lit}`mag beta 0 = 1`
    while {lit}`(beta : ℝ) ^ (e - 1) > 0` for all integers {lit}`e` when {lit}`1 < beta`,
    so the statement would be false for {lit}`e ≤ 1`.
-/
theorem bpow_mag_le_from_exp_payload (beta : Int) (x : ℝ) (e : Int)
    (hβ : 1 < beta)
    (hx_ne : x ≠ 0)
    (he_le : e ≤ (mag beta x)) :
    (beta : ℝ) ^ (e - 1) ≤ |x| := by
  -- Unpack hypotheses and basic facts
  have hβR : (1 : ℝ) < (beta : ℝ) := by exact_mod_cast hβ
  have hbpos : 0 < (beta : ℝ) := lt_trans zero_lt_one hβR
  have hx_pos : 0 < |x| := abs_pos.mpr hx_ne
  -- Abbreviation L := log |x| / log β
  set L : ℝ := Real.log (abs x) / Real.log (beta : ℝ)
  -- Evaluate `(mag beta x)` under `x ≠ 0` (Coq semantics: floor+1)
  have hmag_run : (mag beta x) = Int.floor L + 1 := by
    simp [mag, hx_ne, L]
  -- log β > 0
  have hlogβ_pos : 0 < Real.log (beta : ℝ) := by
    have : 0 < Real.log (beta : ℝ) ↔ 1 < (beta : ℝ) :=
      Real.log_pos_iff (x := (beta : ℝ)) (le_of_lt hbpos)
    exact this.mpr hβR
  have hlogβ_ne : Real.log (beta : ℝ) ≠ 0 := ne_of_gt hlogβ_pos
  -- From e ≤ ⌊L⌋ + 1, deduce (e - 1) ≤ ⌊L⌋, hence (e - 1 : ℝ) ≤ L
  have h_em1_le_L : (e - 1 : ℝ) ≤ L := by
    have hstep : e - 1 ≤ Int.floor L := by
      have : e ≤ Int.floor L + 1 := hmag_run ▸ he_le
      grind
    have hfloor_le_L : (Int.floor L : ℝ) ≤ L := Int.floor_le L
    calc (e - 1 : ℝ) ≤ Int.floor L := by exact_mod_cast hstep
      _ ≤ L := hfloor_le_L
  -- Multiply by log β > 0 to obtain a bound on log |x|
  have hlog_le : (e - 1 : ℝ) * Real.log (beta : ℝ) ≤ Real.log (abs x) := by
    have := mul_le_mul_of_nonneg_right h_em1_le_L (le_of_lt hlogβ_pos)
    -- L * log β = log |x|
    have hL_mul : L * Real.log (beta : ℝ) = Real.log (abs x) := by
      calc
        L * Real.log (beta : ℝ)
            = (Real.log (abs x) / Real.log (beta : ℝ)) * Real.log (beta : ℝ) := by
                simpa [L]
        _ = Real.log (abs x) * Real.log (beta : ℝ) / Real.log (beta : ℝ) := by
                simpa [div_mul_eq_mul_div]
        _ = Real.log (abs x) := by
                simpa [hlogβ_ne] using
                  (mul_div_cancel' (Real.log (abs x)) (Real.log (beta : ℝ)))
    simpa [hL_mul, mul_comm] using this
  -- Exponentiate: exp((e-1) * log β) ≤ |x|, and exp/log correspondence gives β^(e-1)
  have h_exp_eq : Real.exp ((e - 1 : ℝ) * Real.log (beta : ℝ)) = (beta : ℝ) ^ (e - 1) := by
    have hbpow_pos : 0 < (beta : ℝ) ^ (e - 1) := zpow_pos hbpos (e - 1)
    have hlog : Real.log ((beta : ℝ) ^ (e - 1)) = ((e - 1 : ℝ) * Real.log (beta : ℝ)) := by
      simpa using (Real.log_zpow hbpos (e - 1))
    have : Real.exp (Real.log ((beta : ℝ) ^ (e - 1))) = (beta : ℝ) ^ (e - 1) :=
      Real.exp_log hbpow_pos
    simpa [hlog] using this
  have hpow_le : (beta : ℝ) ^ (e - 1) ≤ |x| := by
    -- Compare exponentials and then rewrite each side
    have hexp_le :
        Real.exp ((e - 1 : ℝ) * Real.log (beta : ℝ))
          ≤ Real.exp (Real.log (abs x)) := Real.exp_le_exp.mpr hlog_le
    have hleft : Real.exp ((e - 1 : ℝ) * Real.log (beta : ℝ)) ≤ |x| := by
      simpa only [Real.exp_log hx_pos] using hexp_le
    have hleftrw : (beta : ℝ) ^ (e - 1) = Real.exp ((e - 1 : ℝ) * Real.log (beta : ℝ)) :=
      h_exp_eq.symm
    simpa [hleftrw] using hleft
  exact hpow_le

/-- Nonzero case of {lean}`bpow_mag_gt`: for x ≠ 0, |x| < beta^(mag x).
    This follows from the floor property: L < ⌊L⌋ + 1. -/
private theorem bpow_mag_gt_of_ne_zero (beta : Int) (x : ℝ)
    (hβ : 1 < beta)
    (hx_ne : x ≠ 0) :
    |x| < (beta : ℝ) ^ (mag beta x) := by
  have hβR : (1 : ℝ) < (beta : ℝ) := by exact_mod_cast hβ
  have hbpos : 0 < (beta : ℝ) := lt_trans zero_lt_one hβR
  have hx_pos : 0 < |x| := abs_pos.mpr hx_ne
  -- Abbreviation L := log |x| / log β
  set L : ℝ := Real.log (abs x) / Real.log (beta : ℝ)
  -- Evaluate `(mag beta x)` under `x ≠ 0` (Coq semantics: floor+1)
  have hmag_run : (mag beta x) = Int.floor L + 1 := by simp [mag, hx_ne, L]
  -- log β > 0
  have hlogβ_pos : 0 < Real.log (beta : ℝ) := by
    have : 0 < Real.log (beta : ℝ) ↔ 1 < (beta : ℝ) :=
      Real.log_pos_iff (x := (beta : ℝ)) (le_of_lt hbpos)
    exact this.mpr hβR
  have hlogβ_ne : Real.log (beta : ℝ) ≠ 0 := ne_of_gt hlogβ_pos
  -- From floor property: L < ⌊L⌋ + 1 (STRICT)
  have hL_lt_floor_add1 : L < Int.floor L + 1 := Int.lt_floor_add_one L
  -- Multiply by log β > 0: L * log β < (⌊L⌋ + 1) * log β
  have hmul : L * Real.log (beta : ℝ) < (Int.floor L + 1 : ℝ) * Real.log (beta : ℝ) :=
    mul_lt_mul_of_pos_right hL_lt_floor_add1 hlogβ_pos
  -- L * log β = log |x|
  have hL_mul : L * Real.log (beta : ℝ) = Real.log (abs x) := by
    calc L * Real.log (beta : ℝ)
        = (Real.log (abs x) / Real.log (beta : ℝ)) * Real.log (beta : ℝ) := by simp [L]
      _ = Real.log (abs x) := by field_simp
  -- log |x| < (⌊L⌋ + 1) * log β
  have hlog_lt : Real.log (abs x) < (Int.floor L + 1 : ℝ) * Real.log (beta : ℝ) := by
    simpa [hL_mul] using hmul
  -- (⌊L⌋ + 1) * log β = log (β^(⌊L⌋ + 1))
  have hlog_pow : (Int.floor L + 1 : ℝ) * Real.log (beta : ℝ) =
      Real.log ((beta : ℝ) ^ (Int.floor L + 1)) := by
    have h := Real.log_zpow (beta : ℝ) (Int.floor L + 1)
    -- h : log (β ^ (⌊L⌋ + 1)) = (⌊L⌋ + 1) * log β
    calc (Int.floor L + 1 : ℝ) * Real.log (beta : ℝ)
        = (↑(Int.floor L + 1) : ℝ) * Real.log (beta : ℝ) := by simp
      _ = Real.log ((beta : ℝ) ^ (Int.floor L + 1)) := h.symm
  -- log |x| < log (β^(⌊L⌋ + 1))
  have hlog_lt' : Real.log (abs x) < Real.log ((beta : ℝ) ^ (Int.floor L + 1)) := by
    calc Real.log (abs x) < (Int.floor L + 1 : ℝ) * Real.log (beta : ℝ) := hlog_lt
      _ = Real.log ((beta : ℝ) ^ (Int.floor L + 1)) := hlog_pow
  -- Exponentiate: |x| < β^(⌊L⌋ + 1)
  have hpow_pos : 0 < (beta : ℝ) ^ (Int.floor L + 1) := zpow_pos hbpos _
  have habs_lt : |x| < (beta : ℝ) ^ (Int.floor L + 1) :=
    (Real.log_lt_log_iff hx_pos hpow_pos).mp hlog_lt'
  -- Conclude: (mag beta x) = Int.floor L + 1
  have hmag : mag beta x = Int.floor L + 1 := hmag_run
  simp_rw [hmag]
  exact habs_lt

/-- Coq `bpow_mag_gt`: the strict upper magnitude bound, including `x = 0`. -/
theorem bpow_mag_gt (beta : Int) (x : ℝ) (hβ : 1 < beta) :
    |x| < (beta : ℝ) ^ (mag beta x) := by
  by_cases hx : x = 0
  · have hbpos : (0 : ℝ) < (beta : ℝ) := by
      exact_mod_cast (lt_trans (by decide : (0 : Int) < 1) hβ)
    simpa [hx, mag] using hbpos
  · exact bpow_mag_gt_of_ne_zero beta x hβ hx

/-- Coq `bpow_mag_le`: the lower magnitude bound for nonzero values. -/
theorem bpow_mag_le (beta : Int) (x : ℝ) (hβ : 1 < beta) (hx : x ≠ 0) :
    (beta : ℝ) ^ (mag beta x - 1) ≤ |x| :=
  bpow_mag_le_from_exp_payload beta x (mag beta x) hβ hx le_rfl

/-- Coq `lt_mag`: strict magnitude separation implies strict value separation
when the larger value is positive. -/
theorem lt_mag (beta : Int) (x y : ℝ)
    (hβ : 1 < beta) (hy : 0 < y) (hmag : mag beta x < mag beta y) :
    x < y := by
  by_cases hx : 0 < x
  · have hpow_exp : mag beta x ≤ mag beta y - 1 := by omega
    have hpow_le :
        (beta : ℝ) ^ (mag beta x) ≤ (beta : ℝ) ^ (mag beta y - 1) :=
      bpow_le beta (mag beta x) (mag beta y - 1) hβ hpow_exp
    have hx_upper := bpow_mag_gt beta x hβ
    have hy_lower := bpow_mag_le beta y hβ (ne_of_gt hy)
    have habs_lt : |x| < |y| := hx_upper.trans_le (hpow_le.trans hy_lower)
    simpa [abs_of_pos hx, abs_of_pos hy] using habs_lt
  · exact (le_of_not_gt hx).trans_lt hy

/-- Source-facing Coq `Raux.mag`.

Coq returns a dependent `mag_prop x` record, not a bare integer.  The integer
function `mag` above remains the reusable computational projection; this
constructor restores the exported source contract by pairing that value with
its machine-checked lower and upper bounds. -/
noncomputable def mag_with_spec (r : FloatSpec.Core.Zaux.Radix)
    (x : ℝ) : mag_prop r.val x :=
  { mag_val := mag r.val x
    mag_spec := by
      intro hx
      have hradix := r.prop
      have hbeta : 1 < r.val := by omega
      constructor
      · simpa [bpow] using bpow_mag_le r.val x hbeta hx
      · simpa [bpow] using bpow_mag_gt r.val x hbeta }

@[simp] theorem mag_with_spec_val (r : FloatSpec.Core.Zaux.Radix) (x : ℝ) :
    (mag_with_spec r x).mag_val = mag r.val x := by
  rfl

/-- Coq `Raux.mag_mult_bpow`: multiplying by a radix power shifts the
    magnitude by the same exponent. -/
theorem mag_mult_bpow (beta : Int) (x : ℝ) (e : Int) (hβ : 1 < beta)
    (hx : x ≠ 0) :
    mag beta (x * (beta : ℝ) ^ e) = mag beta x + e := by
  have hβR : (1 : ℝ) < (beta : ℝ) := by exact_mod_cast hβ
  have hbpos : (0 : ℝ) < (beta : ℝ) := lt_trans zero_lt_one hβR
  have hbne : (beta : ℝ) ≠ 0 := ne_of_gt hbpos
  have hpow_pos : 0 < (beta : ℝ) ^ e := zpow_pos hbpos e
  have hpow_nonneg : 0 ≤ (beta : ℝ) ^ e := le_of_lt hpow_pos
  have hlow_x' : (beta : ℝ) ^ (mag beta x - 1) ≤ |x| := bpow_mag_le beta x hβ hx
  have hupp_x' : |x| < (beta : ℝ) ^ (mag beta x) := bpow_mag_gt beta x hβ
  have habs : |x * (beta : ℝ) ^ e| = |x| * (beta : ℝ) ^ e := by
    rw [abs_mul, abs_of_pos hpow_pos]
  have hpow_low :
      (beta : ℝ) ^ (mag beta x + e - 1) =
        (beta : ℝ) ^ (mag beta x - 1) * (beta : ℝ) ^ e := by
    calc
      (beta : ℝ) ^ (mag beta x + e - 1)
          = (beta : ℝ) ^ ((mag beta x - 1) + e) := by ring_nf
      _ = (beta : ℝ) ^ (mag beta x - 1) * (beta : ℝ) ^ e :=
        zpow_add₀ hbne (mag beta x - 1) e
  have hpow_high :
      (beta : ℝ) ^ (mag beta x + e) =
        (beta : ℝ) ^ (mag beta x) * (beta : ℝ) ^ e :=
    zpow_add₀ hbne (mag beta x) e
  have hlow :
      (beta : ℝ) ^ (mag beta x + e - 1) ≤
        |x * (beta : ℝ) ^ e| := by
    rw [hpow_low, habs]
    exact mul_le_mul_of_nonneg_right hlow_x' hpow_nonneg
  have hupp :
      |x * (beta : ℝ) ^ e| <
        (beta : ℝ) ^ (mag beta x + e) := by
    rw [habs, hpow_high]
    exact mul_lt_mul_of_pos_right hupp_x' hpow_pos
  exact mag_unique beta (x * (beta : ℝ) ^ e) (mag beta x + e) hβ hlow hupp

/-- Coq `Raux.mag_le_Zpower`, with the source integer domain and nonzero
    precondition preserved exactly. -/
theorem mag_le_Zpower (beta : Int) (m e : Int)
    (hβ : 1 < beta)
    (hm : m ≠ 0)
    (hlt : |m| < FloatSpec.Core.Zaux.Zpower beta e) :
    mag beta (m : ℝ) ≤ e := by
  by_cases he : 0 ≤ e
  · have hpow_cast :
        ((FloatSpec.Core.Zaux.Zpower beta e : Int) : ℝ) =
          (beta : ℝ) ^ e := by
      have heq : (e.natAbs : Int) = e := Int.natAbs_of_nonneg he
      simp [FloatSpec.Core.Zaux.Zpower, he, Int.cast_pow,
        ← zpow_natCast, heq]
    have hltR : |(m : ℝ)| < (beta : ℝ) ^ e := by
      have hcast : ((|m| : Int) : ℝ) <
          ((FloatSpec.Core.Zaux.Zpower beta e : Int) : ℝ) := by
        exact_mod_cast hlt
      simpa [Int.cast_abs, hpow_cast] using hcast
    exact mag_le_bpow beta (m : ℝ) e hβ (by exact_mod_cast hm) hltR
  · have habs_nonneg : 0 ≤ |m| := abs_nonneg m
    simp [FloatSpec.Core.Zaux.Zpower, he] at hlt
    omega

/-- Coq `Raux.mag_gt_Zpower`, preserving its integer power premise and strict
    postcondition. -/
theorem mag_gt_Zpower (beta : Int) (m e : Int)
    (hβ : 1 < beta)
    (hm : m ≠ 0)
    (hle : FloatSpec.Core.Zaux.Zpower beta e ≤ |m|) :
    e < mag beta (m : ℝ) := by
  by_cases he : 0 ≤ e
  · have hpow_cast :
        ((FloatSpec.Core.Zaux.Zpower beta e : Int) : ℝ) =
          (beta : ℝ) ^ e := by
      have heq : (e.natAbs : Int) = e := Int.natAbs_of_nonneg he
      simp [FloatSpec.Core.Zaux.Zpower, he, Int.cast_pow,
        ← zpow_natCast, heq]
    have hleR : (beta : ℝ) ^ e ≤ |(m : ℝ)| := by
      have hcast :
          ((FloatSpec.Core.Zaux.Zpower beta e : Int) : ℝ) ≤
            ((|m| : Int) : ℝ) := by
        exact_mod_cast hle
      simpa [Int.cast_abs, hpow_cast] using hcast
    exact mag_gt_bpow beta (m : ℝ) e hβ hleR
  · have he_neg : e < 0 := lt_of_not_ge he
    have hmabs : (1 : ℝ) ≤ |(m : ℝ)| := by
      have hmabsZ : (1 : Int) ≤ |m| := Int.one_le_abs hm
      exact_mod_cast hmabsZ
    have hmag_pos : 0 < mag beta (m : ℝ) :=
      mag_gt_bpow beta (m : ℝ) 0 hβ (by simpa using hmabs)
    exact lt_trans he_neg hmag_pos

/-- Magnitude of a product versus sum of magnitudes -/
theorem mag_mult (beta : Int) (x y : ℝ)
    (hβ : 1 < beta)
    (hx_ne : x ≠ 0)
    (hy_ne : y ≠ 0) :
    mag beta (x * y) ≤ mag beta x + mag beta y ∧
      mag beta x + mag beta y - 1 ≤ mag beta (x * y) := by
  -- Unpack hypotheses and basic positivity facts
  have hβR : (1 : ℝ) < (beta : ℝ) := by exact_mod_cast hβ
  have hbpos : 0 < (beta : ℝ) := lt_trans zero_lt_one hβR
  have hxy_ne : x * y ≠ 0 := mul_ne_zero hx_ne hy_ne
  have hx_pos : 0 < |x| := abs_pos.mpr hx_ne
  have hy_pos : 0 < |y| := abs_pos.mpr hy_ne
  -- Unfold `mag` using the nonzero facts
  simp [mag, hxy_ne, hx_ne, hy_ne]
  -- Shorthands for logarithmic magnitudes
  set Lx : ℝ := Real.log (abs x) / Real.log (beta : ℝ) with hLx
  set Ly : ℝ := Real.log (abs y) / Real.log (beta : ℝ) with hLy
  set Lxy : ℝ := Real.log (abs (x * y)) / Real.log (beta : ℝ) with hLxy
  have hLx' : Lx = Real.log x / Real.log (beta : ℝ) := by
    simpa [log_abs] using hLx
  have hLy' : Ly = Real.log y / Real.log (beta : ℝ) := by
    simpa [log_abs] using hLy
  -- Relation between the logs: log |xy| = log |x| + log |y|
  have habs_mul : abs (x * y) = abs x * abs y := abs_mul x y
  have hLxy_eq : Lxy = Lx + Ly := by
    calc
      Lxy = Real.log (abs (x * y)) / Real.log (beta : ℝ) := rfl
      _ = Real.log (abs x * abs y) / Real.log (beta : ℝ) := by rw [habs_mul]
      _ = (Real.log (abs x) + Real.log (abs y)) / Real.log (beta : ℝ) := by
            have hx_ne' : (abs x) ≠ 0 := ne_of_gt hx_pos
            have hy_ne' : (abs y) ≠ 0 := ne_of_gt hy_pos
            rw [Real.log_mul hx_ne' hy_ne']
      _ = Lx + Ly := by rw [add_div, hLx, hLy]
  have hLxy_abs : Real.log (abs x * abs y) / Real.log (beta : ℝ) = Lxy := by
    simpa [habs_mul] using hLxy.symm
  have hlog_mul_abs : Real.log (abs x * abs y) / Real.log (beta : ℝ) = Lx + Ly := by
    simpa [hLxy_eq] using hLxy_abs
  -- Prove the inequality in terms of Lx/Ly, then rewrite back.
  have h_goal :
      (Int.floor (Lx + Ly) < 1 + (1 + (Int.floor Lx + Int.floor Ly))) ∧
        (Int.floor Lx + Int.floor Ly ≤ Int.floor (Lx + Ly)) := by
    exact ⟨by linarith [Int.le_floor_add_floor Lx Ly], Int.le_floor_add Lx Ly⟩
  simpa [hlog_mul_abs, hLx', hLy', add_assoc, add_left_comm, add_comm]
    using h_goal

/-- Magnitude of a sum under positivity and ordering

    Coq (Flocq) version: if 0 < y ≤ x then
      mag x ≤ mag (x + y) ≤ mag x + 1.
-/
theorem mag_plus (beta : Int) (x y : ℝ)
    (hβ : 1 < beta)
    (hy_pos : 0 < y)
    (hylex : y ≤ x) :
    mag beta x ≤ mag beta (x + y) ∧ mag beta (x + y) ≤ mag beta x + 1 := by
  -- Basic positivity facts
  have hx_pos : 0 < x := lt_of_lt_of_le hy_pos hylex
  have hxy_pos : 0 < x + y := add_pos hx_pos hy_pos
  have hbposR : 0 < (beta : ℝ) := by
    have hβR : (1 : ℝ) < (beta : ℝ) := by exact_mod_cast hβ
    exact lt_trans zero_lt_one hβR
  have hlogβ_pos : 0 < Real.log (beta : ℝ) := by
    -- 0 < log β ↔ 1 < β (for β > 0)
    have hβR : (1 : ℝ) < (beta : ℝ) := by exact_mod_cast hβ
    have : 0 < Real.log (beta : ℝ) ↔ 1 < (beta : ℝ) :=
      Real.log_pos_iff (x := (beta : ℝ)) (le_of_lt (lt_trans zero_lt_one hβR))
    exact this.mpr hβR
  have hlogβ_ne : Real.log (beta : ℝ) ≠ 0 := ne_of_gt hlogβ_pos

  -- All arguments are positive hence nonzero
  have hx_ne : x ≠ 0 := ne_of_gt hx_pos
  have hy_ne : y ≠ 0 := ne_of_gt hy_pos
  have hxy_ne : x + y ≠ 0 := ne_of_gt hxy_pos
  simp [mag, hx_ne, hy_ne, hxy_ne]

  -- Shorthands for logarithmic magnitudes
  set Lx : ℝ := Real.log x / Real.log (beta : ℝ) with hLx
  set Lxy : ℝ := Real.log (x + y) / Real.log (beta : ℝ) with hLxy

  -- Show Lx ≤ Lxy using monotonicity of log and x ≤ x + y
  have hxle : x ≤ x + y := by
    have : 0 ≤ y := le_of_lt hy_pos
    simpa [add_comm] using add_le_add_left this x
  have hlog_le : Real.log x ≤ Real.log (x + y) := Real.log_le_log hx_pos hxle
  have hLx_mul : Lx * Real.log (beta : ℝ) = Real.log x := by
    calc
      Lx * Real.log (beta : ℝ)
          = (Real.log x / Real.log (beta : ℝ)) * Real.log (beta : ℝ) := by simpa [hLx]
      _ = Real.log x := by
          simpa [hlogβ_ne, div_mul_eq_mul_div]
            using (mul_div_cancel' (Real.log x) (Real.log (beta : ℝ)))
  have hLxy_mul : Lxy * Real.log (beta : ℝ) = Real.log (x + y) := by
    calc
      Lxy * Real.log (beta : ℝ)
          = (Real.log (x + y) / Real.log (beta : ℝ)) * Real.log (beta : ℝ) := by simpa [hLxy]
      _ = Real.log (x + y) := by
          simpa [hlogβ_ne, div_mul_eq_mul_div]
            using (mul_div_cancel' (Real.log (x + y)) (Real.log (beta : ℝ)))
  have hLx_le_Lxy : Lx ≤ Lxy := by
    have : Lx * Real.log (beta : ℝ) ≤ Lxy * Real.log (beta : ℝ) := by
      simpa [hLx_mul, hLxy_mul] using hlog_le
    exact (le_of_mul_le_mul_right this hlogβ_pos)

  -- Show Lxy ≤ Lx + 1 via x + y ≤ β * x (since y ≤ x and β ≥ 2)
  have hβ_ge2ℤ : (2 : Int) ≤ beta := by
    -- From 1 < beta we obtain 2 ≤ beta using `add_one_le_iff` on integers
    simpa using (Int.add_one_le_iff.mpr hβ)
  have hβ_ge2 : (2 : ℝ) ≤ (beta : ℝ) := by exact_mod_cast hβ_ge2ℤ
  have hxle2 : x + y ≤ 2 * x := by
    have : y ≤ x := hylex
    -- x + y ≤ x + x = 2*x
    simpa [two_mul] using add_le_add_left this x
  have h2x_le_bx : (2 : ℝ) * x ≤ (beta : ℝ) * x := by
    exact mul_le_mul_of_nonneg_right hβ_ge2 (le_of_lt hx_pos)
  have hxy_le_bx : x + y ≤ (beta : ℝ) * x := le_trans hxle2 h2x_le_bx
  have hbx_pos : 0 < (beta : ℝ) * x := mul_pos hbposR hx_pos
  have hlog_le2 : Real.log (x + y) ≤ Real.log ((beta : ℝ) * x) :=
    Real.log_le_log hxy_pos hxy_le_bx
  -- Rewrite both sides and compare after multiplying by log β > 0
  have hlog_prod : Real.log ((beta : ℝ) * x) = Real.log (beta : ℝ) + Real.log x := by
    simpa using Real.log_mul (ne_of_gt hbposR) (ne_of_gt hx_pos)
  have hmul_right : (Lx + 1) * Real.log (beta : ℝ) = Real.log (beta : ℝ) + Real.log x := by
    calc
      (Lx + 1) * Real.log (beta : ℝ)
          = (Real.log x / Real.log (beta : ℝ) + 1) * Real.log (beta : ℝ) := by
              simpa [hLx]
      _ = (Real.log x / Real.log (beta : ℝ)) * Real.log (beta : ℝ)
            + 1 * Real.log (beta : ℝ) := by
              ring
      _ = Real.log (beta : ℝ) + Real.log x := by
            have : (Real.log x / Real.log (beta : ℝ)) * Real.log (beta : ℝ) = Real.log x := by
              simpa [div_mul_eq_mul_div, hlogβ_ne]
                using (mul_div_cancel' (Real.log x) (Real.log (beta : ℝ)))
            simpa [this] using (by simp [add_comm])
  have hmul_le2 : Lxy * Real.log (beta : ℝ) ≤ (Lx + 1) * Real.log (beta : ℝ) := by
    -- Chain with explicit rewrites
    have hx' : Real.log (x + y) ≤ Real.log (beta : ℝ) + Real.log x := by
      simpa [hlog_prod] using hlog_le2
    calc
      Lxy * Real.log (beta : ℝ)
          = Real.log (x + y) := by simpa [hLxy]
                using hLxy_mul
      _ ≤ Real.log (beta : ℝ) + Real.log x := hx'
      _ = (Lx + 1) * Real.log (beta : ℝ) := by
            -- rearrange using `hmul_right` (use the symmetric direction)
            have hsymm : Real.log (beta : ℝ) + Real.log x
                = (Lx + 1) * Real.log (beta : ℝ) := hmul_right.symm
            simpa [hLx] using hsymm
  have hLxy_le : Lxy ≤ Lx + 1 :=
    (le_of_mul_le_mul_right hmul_le2 hlogβ_pos)

  -- Turn inequalities on reals into inequalities on ceilings
  have hceil_lb : Int.ceil Lx ≤ Int.ceil Lxy :=
    (Int.ceil_le).mpr (hLx_le_Lxy.trans (Int.le_ceil _))
  have hceil_ub : Int.ceil Lxy ≤ Int.ceil (Lx + 1) :=
    Int.ceil_mono hLxy_le
  have hceil_add : Int.ceil (Lx + 1 : ℝ) = Int.ceil Lx + 1 := by
    simpa using Int.ceil_add_intCast (a := Lx) (z := 1)

  -- Conclude both bounds
  -- Use floor properties: Lx ≤ Lxy → ⌊Lx⌋ ≤ ⌊Lxy⌋, and Lxy ≤ Lx + 1 → ⌊Lxy⌋ ≤ ⌊Lx⌋ + 1
  constructor
  · -- Lower bound: ⌊Lx⌋ ≤ ⌊Lxy⌋
    exact Int.floor_mono hLx_le_Lxy
  · -- Upper bound: ⌊Lxy⌋ ≤ ⌊Lx⌋ + 1
    have hfloor_add : Int.floor (Lx + 1 : ℝ) = Int.floor Lx + 1 :=
      Int.floor_add_one Lx
    calc Int.floor Lxy ≤ Int.floor (Lx + 1) := Int.floor_mono hLxy_le
      _ = Int.floor Lx + 1 := hfloor_add

/-- Magnitude of a difference under positivity and strict ordering

    Coq (Flocq) version: if 0 < y < x then mag (x − y) ≤ mag x.
-/
theorem mag_minus (beta : Int) (x y : ℝ)
    (hβ : 1 < beta)
    (hy_pos : 0 < y)
    (hyx : y < x) :
    mag beta (x - y) ≤ mag beta x := by
  -- Basic positivity facts
  have hx_pos : 0 < x := lt_trans hy_pos hyx
  have hxy_pos : 0 < x - y := sub_pos.mpr hyx
  -- Discharge the conditionals
  have hx_ne : x ≠ 0 := ne_of_gt hx_pos
  have hy_ne : y ≠ 0 := ne_of_gt hy_pos
  have hxy_ne : x - y ≠ 0 := ne_of_gt hxy_pos
  simp [mag, hx_ne, hy_ne, hxy_ne]
  -- Compare via logarithms
  set Lx : ℝ := Real.log x / Real.log (beta : ℝ) with hLx
  set Lxy : ℝ := Real.log (x - y) / Real.log (beta : ℝ) with hLxy
  -- log β > 0 from 1 < β
  have hβR : (1 : ℝ) < (beta : ℝ) := by exact_mod_cast hβ
  have hlogβ_pos : 0 < Real.log (beta : ℝ) := by
    have : 0 < Real.log (beta : ℝ) ↔ 1 < (beta : ℝ) :=
      Real.log_pos_iff (x := (beta : ℝ)) (le_of_lt (lt_trans zero_lt_one hβR))
    exact this.mpr hβR
  -- log monotone on (0, ∞): x - y ≤ x ⇒ log (x - y) ≤ log x
  have hle : x - y ≤ x := by
    have : 0 ≤ y := le_of_lt hy_pos
    simpa using sub_le_self x this
  have hlog_le : Real.log (x - y) ≤ Real.log x :=
    Real.log_le_log (by exact_mod_cast hxy_pos) hle
  -- Cancel the positive factor log β
  have hmul_Lxy : Lxy * Real.log (beta : ℝ) = Real.log (x - y) := by
    have hne : Real.log (beta : ℝ) ≠ 0 := ne_of_gt hlogβ_pos
    calc
      Lxy * Real.log (beta : ℝ)
          = (Real.log (x - y) / Real.log (beta : ℝ)) * Real.log (beta : ℝ) := by simpa [hLxy]
      _ = Real.log (x - y) := by
            simpa [hne, div_mul_eq_mul_div]
              using (mul_div_cancel' (Real.log (x - y)) (Real.log (beta : ℝ)))
  have hmul_Lx : Lx * Real.log (beta : ℝ) = Real.log x := by
    have hne : Real.log (beta : ℝ) ≠ 0 := ne_of_gt hlogβ_pos
    calc
      Lx * Real.log (beta : ℝ)
          = (Real.log x / Real.log (beta : ℝ)) * Real.log (beta : ℝ) := by simpa [hLx]
      _ = Real.log x := by
            simpa [hne, div_mul_eq_mul_div]
              using (mul_div_cancel' (Real.log x) (Real.log (beta : ℝ)))
  have hLxy_le_Lx : Lxy ≤ Lx := by
    have : Lxy * Real.log (beta : ℝ) ≤ Lx * Real.log (beta : ℝ) := by
      simpa [hmul_Lxy, hmul_Lx] using hlog_le
    exact (le_of_mul_le_mul_right this hlogβ_pos)
  -- Floor monotonicity: Lxy ≤ Lx → ⌊Lxy⌋ ≤ ⌊Lx⌋
  exact Int.floor_mono hLxy_le_Lx

/-- Lower bound variant for magnitude of difference (Coq style)

    If 0 < x, 0 < y and mag y ≤ mag x − 2, then mag x − 1 ≤ mag (x − y).
-/
theorem mag_minus_lb (beta : Int) (x y : ℝ)
    (hβ : 1 < beta)
    (hx_pos : 0 < x)
    (hy_pos : 0 < y)
    (hmy_le : (mag beta y) ≤ (mag beta x) - 2) :
    mag beta x - 1 ≤ mag beta (x - y) := by
  -- Basic positivity facts and non-zeroness
  have hβR : (1 : ℝ) < (beta : ℝ) := by exact_mod_cast hβ
  have hbpos : 0 < (beta : ℝ) := lt_trans zero_lt_one hβR
  have hlogβ_pos : 0 < Real.log (beta : ℝ) := by
    have : 0 < Real.log (beta : ℝ) ↔ 1 < (beta : ℝ) :=
      Real.log_pos_iff (x := (beta : ℝ)) (le_of_lt hbpos)
    exact this.mpr hβR
  have hlogβ_ne : Real.log (beta : ℝ) ≠ 0 := ne_of_gt hlogβ_pos
  have hx_ne : x ≠ 0 := ne_of_gt hx_pos
  have hy_ne : y ≠ 0 := ne_of_gt hy_pos

  -- Rewrite the magnitude hypothesis using floor(log_beta |x|) + 1.
  set Lx : ℝ := Real.log x / Real.log (beta : ℝ) with hLx
  set Ly : ℝ := Real.log y / Real.log (beta : ℝ) with hLy
  -- From hmy_le: ⌊Ly⌋ + 1 ≤ (⌊Lx⌋ + 1) - 2, i.e., ⌊Ly⌋ ≤ ⌊Lx⌋ - 2
  have hfloor_le : Int.floor Ly ≤ Int.floor Lx - 2 := by
    simp only [mag, hx_ne, hy_ne, abs_of_pos hx_pos, abs_of_pos hy_pos, ite_false,
      hLx, hLy] at hmy_le
    linarith
  -- Use floor bounds instead of ceiling bounds (avoids issues when Lx is an integer)
  -- From ⌊Ly⌋ ≤ ⌊Lx⌋ - 2, we get ⌈Ly⌉ ≤ ⌊Ly⌋ + 1 ≤ ⌊Lx⌋ - 1
  have hceil_le_floor : Int.ceil Ly ≤ Int.floor Lx - 1 := by
    have h1 : Int.ceil Ly ≤ Int.floor Ly + 1 := Int.ceil_le_floor_add_one Ly
    -- From hfloor_le: ⌊Ly⌋ ≤ ⌊Lx⌋ - 2, so ⌊Ly⌋ + 1 ≤ ⌊Lx⌋ - 1
    linarith

  -- Upper bound on y: y ≤ (beta : ℝ) ^ (Int.ceil Ly)
  have hLy_mul : Ly * Real.log (beta : ℝ) = Real.log y := by
    calc
      Ly * Real.log (beta : ℝ)
          = (Real.log y / Real.log (beta : ℝ)) * Real.log (beta : ℝ) := by simpa [hLy]
      _ = Real.log y := by
            simpa [hlogβ_ne, div_mul_eq_mul_div]
              using (mul_div_cancel' (Real.log y) (Real.log (beta : ℝ)))
  have hlogy_le :
    Real.log y ≤ (Int.ceil Ly : ℝ) * Real.log (beta : ℝ) := by
    -- from Ly ≤ ceil Ly, multiply both sides by log β > 0
    have h' :
        Ly * Real.log (beta : ℝ)
          ≤ (Int.ceil Ly : ℝ) * Real.log (beta : ℝ) :=
      mul_le_mul_of_nonneg_right (Int.le_ceil Ly) (le_of_lt hlogβ_pos)
    -- now turn the left side into log y
    simpa [hLy_mul] using h'
  have hy_le_pow_ceil : y ≤ (beta : ℝ) ^ (Int.ceil Ly) := by
    -- Compare logs then exponentiate, and rewrite the RHS
    have hlog_rhs : Real.log ((beta : ℝ) ^ (Int.ceil Ly))
                      = (Int.ceil Ly : ℝ) * Real.log (beta : ℝ) := by
      simpa using (Real.log_zpow hbpos (Int.ceil Ly))
    have hlexp :
        Real.exp (Real.log y)
          ≤ Real.exp ((Int.ceil Ly : ℝ) * Real.log (beta : ℝ)) := by
      exact Real.exp_le_exp.mpr hlogy_le
    have hy_exp : y ≤ Real.exp ((Int.ceil Ly : ℝ) * Real.log (beta : ℝ)) := by
      -- Rewrite exp (log y) to y on the left-hand side
      have hyExpEq : Real.exp (Real.log y) = y := Real.exp_log hy_pos
      simpa [hyExpEq] using hlexp
    have hbpow_pos' : 0 < (beta : ℝ) ^ (Int.ceil Ly) := zpow_pos hbpos _
    have hexp_eq : Real.exp ((Int.ceil Ly : ℝ) * Real.log (beta : ℝ))
                      = (beta : ℝ) ^ (Int.ceil Ly) := by
      simpa [hlog_rhs] using (Real.exp_log hbpow_pos')
    simpa [hexp_eq] using hy_exp

  -- From Int.ceil Ly ≤ Int.floor Lx - 1, obtain y ≤ (beta : ℝ) ^ (Int.floor Lx - 1)
  have hy_le_pow_shift : y ≤ (beta : ℝ) ^ (Int.floor Lx - 1) := by
    have hmono : (beta : ℝ) ^ (Int.ceil Ly) ≤ (beta : ℝ) ^ (Int.floor Lx - 1) := by
      -- Monotonicity of zpow in the exponent for bases > 1
      exact ((zpow_right_strictMono₀ hβR).monotone hceil_le_floor)
    exact le_trans hy_le_pow_ceil hmono

  -- Reduce the goal to an inequality on floors.
  simp [mag, hLx, hLy, abs_of_pos hx_pos, abs_of_pos hy_pos]
  -- After establishing positivity of x - y, compare the logarithmic floors
  -- using Lx - 1 ≤ Lxy. Ceiling bounds below are intermediate estimates only.
  set Lxy : ℝ := Real.log (x - y) / Real.log (beta : ℝ) with hLxy

  -- Show x/β ≤ x - y, which implies log(x) - log(β) ≤ log(x - y)
  -- Also record: Lx * log β = log x (used later)
  have hLx_mul : Lx * Real.log (beta : ℝ) = Real.log x := by
    calc
      Lx * Real.log (beta : ℝ)
          = (Real.log x / Real.log (beta : ℝ)) * Real.log (beta : ℝ) := by simpa [hLx]
      _ = Real.log x := by
            simpa [hlogβ_ne, div_mul_eq_mul_div]
              using (mul_div_cancel' (Real.log x) (Real.log (beta : ℝ)))
  -- From (⌈Lx⌉ : ℝ) - 1 ≤ Lx and log β > 0, derive β^(⌈Lx⌉ - 1) ≤ x
  have hx_lb : (beta : ℝ) ^ (Int.ceil Lx - 1) ≤ x := by
    have hceil_le_Lx : (Int.ceil Lx : ℝ) - 1 ≤ Lx := by
      have : (Int.ceil Lx : ℝ) - 1 < Lx := by
        have h := Int.ceil_lt_add_one (a := Lx)
        simpa [sub_lt_iff_lt_add, add_comm] using h
      exact le_of_lt this
    have hlog_le' : ((Int.ceil Lx : ℝ) - 1) * Real.log (beta : ℝ) ≤ Real.log x := by
      have := mul_le_mul_of_nonneg_right hceil_le_Lx (le_of_lt hlogβ_pos)
      simpa [hLx_mul] using this
    have hbpow_pos'' : 0 < (beta : ℝ) ^ (Int.ceil Lx - 1) := zpow_pos hbpos _
    have hexp_le :
        Real.exp (((Int.ceil Lx : ℝ) - 1) * Real.log (beta : ℝ))
          ≤ Real.exp (Real.log x) := Real.exp_le_exp.mpr hlog_le'
    have hleft :
        Real.exp (((Int.ceil Lx : ℝ) - 1) * Real.log (beta : ℝ))
          = (beta : ℝ) ^ (Int.ceil Lx - 1) := by
      have hlog_eq :
          ((Int.ceil Lx : ℝ) - 1) * Real.log (beta : ℝ)
            = Real.log ((beta : ℝ) ^ (Int.ceil Lx - 1)) := by
        simpa using (Real.log_zpow hbpos (Int.ceil Lx - 1))
      have hstep :
          Real.exp (((Int.ceil Lx : ℝ) - 1) * Real.log (beta : ℝ))
            = Real.exp (Real.log ((beta : ℝ) ^ (Int.ceil Lx - 1))) := by
        exact congrArg Real.exp hlog_eq
      calc
        Real.exp (((Int.ceil Lx : ℝ) - 1) * Real.log (beta : ℝ))
            = Real.exp (Real.log ((beta : ℝ) ^ (Int.ceil Lx - 1))) := hstep
        _ = (beta : ℝ) ^ (Int.ceil Lx - 1) := by
            simpa using (Real.exp_log hbpow_pos'')
    have hright : Real.exp (Real.log x) = x := by simpa using Real.exp_log hx_pos
    simpa [hleft, hright] using hexp_le

  -- Use floor-based lower bound: β^⌊Lx⌋ ≤ x
  have hx_lb_floor : (beta : ℝ) ^ Int.floor Lx ≤ x := by
    have hfloor_le_Lx : (Int.floor Lx : ℝ) ≤ Lx := Int.floor_le Lx
    have hlog_le' : (Int.floor Lx : ℝ) * Real.log (beta : ℝ) ≤ Real.log x := by
      have := mul_le_mul_of_nonneg_right hfloor_le_Lx (le_of_lt hlogβ_pos)
      simpa [hLx_mul] using this
    have hbpow_pos'' : 0 < (beta : ℝ) ^ Int.floor Lx := zpow_pos hbpos _
    have hexp_le :
        Real.exp ((Int.floor Lx : ℝ) * Real.log (beta : ℝ))
          ≤ Real.exp (Real.log x) := Real.exp_le_exp.mpr hlog_le'
    have hleft : Real.exp ((Int.floor Lx : ℝ) * Real.log (beta : ℝ)) = (beta : ℝ) ^ Int.floor Lx := by
      have hlog_eq : (Int.floor Lx : ℝ) * Real.log (beta : ℝ) = Real.log ((beta : ℝ) ^ Int.floor Lx) := by
        simpa using (Real.log_zpow hbpos (Int.floor Lx))
      calc
        Real.exp ((Int.floor Lx : ℝ) * Real.log (beta : ℝ))
            = Real.exp (Real.log ((beta : ℝ) ^ Int.floor Lx)) := by rw [hlog_eq]
        _ = (beta : ℝ) ^ Int.floor Lx := Real.exp_log hbpow_pos''
    have hright : Real.exp (Real.log x) = x := Real.exp_log hx_pos
    simpa [hleft, hright] using hexp_le

  have hy_le_x_over_beta : y ≤ x / (beta : ℝ) := by
    -- From y ≤ β^(⌊Lx⌋ - 1) and x ≥ β^⌊Lx⌋, derive x/β ≥ β^(⌊Lx⌋-1) ≥ y
    have hbne : (beta : ℝ) ≠ 0 := ne_of_gt hbpos
    have hx_div_ge : x / (beta : ℝ) ≥ (beta : ℝ) ^ (Int.floor Lx - 1) := by
      -- From x ≥ β^⌊Lx⌋ = β * β^(⌊Lx⌋-1), divide by β
      have hpow_split : (beta : ℝ) ^ Int.floor Lx = (beta : ℝ) * (beta : ℝ) ^ (Int.floor Lx - 1) := by
        have heq : Int.floor Lx = 1 + (Int.floor Lx - 1) := by ring
        conv_lhs => rw [heq, zpow_add₀ hbne, zpow_one]
      have hgoal : (beta : ℝ) ^ (Int.floor Lx - 1) * (beta : ℝ) ≤ x := by
        rw [mul_comm, hpow_split.symm]
        exact hx_lb_floor
      exact (le_div_iff₀ hbpos).mpr hgoal
    -- Combine y ≤ β^(⌊Lx⌋-1) ≤ x/β
    exact le_trans hy_le_pow_shift hx_div_ge

  have hlog_lb : Real.log (x / (beta : ℝ)) ≤ Real.log (x - y) := by
    -- We show x/β ≤ x - y by two steps:
    -- (i) x/β ≤ x - x/β using β ≥ 2 and x > 0;
    -- (ii) x - x/β ≤ x - y since y ≤ x/β.
    have hbge2Z : (2 : Int) ≤ beta := by
      -- from 1 < beta ⇒ 2 ≤ beta
      exact (Int.add_one_le_iff.mpr hβ)
    have hbge2R : (2 : ℝ) ≤ (beta : ℝ) := by exact_mod_cast hbge2Z
    have hx_div_nonneg : 0 ≤ x / (beta : ℝ) := div_nonneg (le_of_lt hx_pos) (le_of_lt hbpos)
    have hxdiv_two_le : (2 : ℝ) * (x / (beta : ℝ)) ≤ (beta : ℝ) * (x / (beta : ℝ)) :=
      mul_le_mul_of_nonneg_right hbge2R hx_div_nonneg
    have hxdiv_le : x / (beta : ℝ) ≤ x - x / (beta : ℝ) := by
      -- Show (x/β) + (x/β) ≤ x by comparing x*(2/β) ≤ x
      have hbge2R : (2 : ℝ) ≤ (beta : ℝ) := by exact_mod_cast (Int.add_one_le_iff.mpr hβ)
      have hfrac_le_one : (2 : ℝ) / (beta : ℝ) ≤ 1 :=
        (div_le_iff₀ hbpos).mpr (by simpa using hbge2R)
      have hmul_le : x * ((2 : ℝ) / (beta : ℝ)) ≤ x * 1 :=
        mul_le_mul_of_nonneg_left hfrac_le_one (le_of_lt hx_pos)
      have htwo_mul_le : (2 : ℝ) * (x / (beta : ℝ)) ≤ x := by
        simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc, one_mul]
          using hmul_le
      have hxdiv_sum_le : x / (beta : ℝ) + x / (beta : ℝ) ≤ x := by
        simpa [two_mul] using htwo_mul_le
      exact (le_sub_iff_add_le).mpr hxdiv_sum_le
    have hx_sub_mono : x - x / (beta : ℝ) ≤ x - y := by
      -- From y ≤ x/β, subtract from x on both sides
      exact sub_le_sub_left hy_le_x_over_beta x
    have hchain : x / (beta : ℝ) ≤ x - y := le_trans hxdiv_le hx_sub_mono
    have hx_div_pos : 0 < x / (beta : ℝ) := by exact div_pos hx_pos hbpos
    exact Real.log_le_log hx_div_pos hchain

  -- From x/β ≤ x - y and x/β > 0, deduce x - y > 0 for later rewrites
  have hxy_pos : 0 < x - y := by
    -- Since 1 < β and 0 < x, we have x/β < x
    have hx_div_lt : x / (beta : ℝ) < x := by
      have hx_mul_lt : x < (beta : ℝ) * x := by
        have := mul_lt_mul_of_pos_left hβR hx_pos
        simpa [one_mul, mul_comm] using this
      -- Need the RHS as x * β for `div_lt_iff₀`; rewrite with commutativity
      have hx_mul_lt' : x < x * (beta : ℝ) := by simpa [mul_comm] using hx_mul_lt
      exact (div_lt_iff₀ hbpos).mpr hx_mul_lt'
    -- And y ≤ x/β, so y < x; hence 0 < x - y
    have hy_lt_x : y < x := lt_of_le_of_lt hy_le_x_over_beta hx_div_lt
    exact sub_pos.mpr hy_lt_x
  have hxy_ne : x - y ≠ 0 := ne_of_gt hxy_pos

  -- Now reduce the goal to an inequality on floors.
  simp [mag, hx_ne, hy_ne, hxy_ne, hLx, hLy, abs_of_pos hx_pos, abs_of_pos hy_pos]

  -- Translate to Lx - 1 ≤ Lxy
  have hLx_sub_le : Lx - 1 ≤ Lxy := by
    -- Multiply both sides by log β > 0 and use algebra
    -- Lx * logβ = log x, Lxy * logβ = log (x - y)
    have hlog_ineq : Real.log x - Real.log (beta : ℝ)
                      ≤ Real.log (x - y) := by
      -- log(x) - log(β) = log(x/β)
      have hlog_div : Real.log (x / (beta : ℝ))
                        = Real.log x - Real.log (beta : ℝ) := by
        have hbne : (beta : ℝ) ≠ 0 := ne_of_gt hbpos
        simpa using Real.log_div (ne_of_gt hx_pos) hbne
      simpa [hlog_div] using hlog_lb
    -- Compute Lxy * log β = log (x - y)
    have hLxy_mul : Lxy * Real.log (beta : ℝ) = Real.log (x - y) := by
      have hne : Real.log (beta : ℝ) ≠ 0 := ne_of_gt hlogβ_pos
      calc
        Lxy * Real.log (beta : ℝ)
            = (Real.log (x - y) / Real.log (beta : ℝ)) * Real.log (beta : ℝ) := by
                simpa [hLxy]
        _ = Real.log (x - y) := by
                simpa [hne, div_mul_eq_mul_div]
                  using (mul_div_cancel' (Real.log (x - y)) (Real.log (beta : ℝ)))
    have hmul_le : (Lx - 1) * Real.log (beta : ℝ) ≤ Lxy * Real.log (beta : ℝ) := by
      have hleft : (Lx - 1) * Real.log (beta : ℝ)
                      = Real.log x - Real.log (beta : ℝ) := by
        calc
          (Lx - 1) * Real.log (beta : ℝ)
              = Lx * Real.log (beta : ℝ) - 1 * Real.log (beta : ℝ) := by ring
          _   = Real.log x - Real.log (beta : ℝ) := by
                simpa [hLx_mul, one_mul]
      have hright : Lxy * Real.log (beta : ℝ) = Real.log (x - y) := hLxy_mul
      simpa [hleft, hright] using hlog_ineq
    exact (le_of_mul_le_mul_right hmul_le hlogβ_pos)

  -- From Lx - 1 ≤ Lxy, we get Lx ≤ Lxy + 1, hence ⌊Lx⌋ ≤ ⌊Lxy + 1⌋ = ⌊Lxy⌋ + 1
  have hLx_le : Lx ≤ Lxy + 1 := by linarith
  have hfloor_le' : Int.floor Lx ≤ Int.floor (Lxy + 1) := Int.floor_mono hLx_le
  have hfloor_add : Int.floor (Lxy + 1) = Int.floor Lxy + 1 := Int.floor_add_one Lxy
  simp only [hLx, hfloor_add] at hfloor_le' ⊢
  exact hfloor_le'

/-- Lower bound on the magnitude of a sum

    Coq (Flocq) version: if x ≠ 0 and mag y ≤ mag x − 2, then
    mag x − 1 ≤ mag (x + y).
-/
theorem mag_plus_ge (beta : Int) (x y : ℝ)
    (hβ : 1 < beta)
    (hx_ne : x ≠ 0)
    (hmy_le : (mag beta y) ≤ (mag beta x) - 2) :
    mag beta x - 1 ≤ mag beta (x + y) := by
  have hβR : (1 : ℝ) < (beta : ℝ) := by exact_mod_cast hβ
  have hβR_ge : (1 : ℝ) ≤ (beta : ℝ) := le_of_lt hβR
  have hbpos : 0 < (beta : ℝ) := lt_trans zero_lt_one hβR
  have hlogβ_pos : 0 < Real.log (beta : ℝ) := Real.log_pos hβR
  have hlogβ_ne : Real.log (beta : ℝ) ≠ 0 := ne_of_gt hlogβ_pos
  have hbne : (beta : ℝ) ≠ 0 := ne_of_gt hbpos

  -- Case split on y = 0
  by_cases hy_zero : y = 0
  · -- If y = 0, then x + y = x and result is trivial
    simp only [hy_zero, add_zero, mag, hx_ne, ite_false]
    show (Int.floor (Real.log |x| / Real.log ↑beta) + 1 - 1 ≤
        Int.floor (Real.log |x| / Real.log ↑beta) + 1)
    grind

  -- y ≠ 0 case
  have hx_abs_pos : 0 < |x| := abs_pos.mpr hx_ne
  have hy_abs_pos : 0 < |y| := abs_pos.mpr hy_zero

  -- Set up log expressions early
  set mx := Int.floor (Real.log |x| / Real.log (beta : ℝ)) + 1 with hmx_def
  set my := Int.floor (Real.log |y| / Real.log (beta : ℝ)) + 1 with hmy_def

  -- mag x = mx, mag y = my
  have hmag_x_eq : (mag beta x) = mx := by
    simp only [mag, hx_ne, ite_false, hmx_def]
  have hmag_y_eq : (mag beta y) = my := by
    simp only [mag, hy_zero, ite_false, hmy_def]

  -- From hypothesis: my ≤ mx - 2
  have hmy_le' : my ≤ mx - 2 := by
    simp only [hmag_x_eq, hmag_y_eq] at hmy_le
    exact hmy_le

  -- Direct bound: β^(mx - 1) ≤ |x| (from floor property)
  have hx_lb : (beta : ℝ) ^ (mx - 1) ≤ |x| := by
    have hfloor_le : (Int.floor (Real.log |x| / Real.log (beta : ℝ)) : ℝ) ≤
        Real.log |x| / Real.log (beta : ℝ) := Int.floor_le _
    have hmul : (mx - 1 : ℤ) = Int.floor (Real.log |x| / Real.log (beta : ℝ)) := by grind
    have hlog_ge : (mx - 1 : ℤ) * Real.log (beta : ℝ) ≤ Real.log |x| := by
      rw [hmul]
      have := mul_le_mul_of_nonneg_right hfloor_le (le_of_lt hlogβ_pos)
      field_simp at this ⊢
      exact this
    have hpow_log : Real.log ((beta : ℝ) ^ (mx - 1)) = (mx - 1 : ℤ) * Real.log (beta : ℝ) := by
      rw [Real.log_zpow]
    rw [← hpow_log] at hlog_ge
    have hpow_pos : 0 < (beta : ℝ) ^ (mx - 1) := zpow_pos hbpos _
    rw [← Real.log_le_log_iff hpow_pos hx_abs_pos]
    exact hlog_ge

  -- Direct bound: |y| < β^my (from floor property)
  have hy_ub_my : |y| < (beta : ℝ) ^ my := by
    have hfloor_lt : Real.log |y| / Real.log (beta : ℝ) <
        Int.floor (Real.log |y| / Real.log (beta : ℝ)) + 1 := Int.lt_floor_add_one _
    have hdiv_lt : Real.log |y| < (Int.floor (Real.log |y| / Real.log (beta : ℝ)) + 1) *
        Real.log (beta : ℝ) := by
      have := mul_lt_mul_of_pos_right hfloor_lt hlogβ_pos
      field_simp at this
      rw [mul_comm] at this
      exact this
    have hlog_lt : Real.log |y| < my * Real.log (beta : ℝ) := by
      convert hdiv_lt using 2
      simp only [hmy_def, Int.cast_add, Int.cast_one]
    have hpow_log : Real.log ((beta : ℝ) ^ my) = my * Real.log (beta : ℝ) := by
      rw [Real.log_zpow]
    rw [← hpow_log] at hlog_lt
    have hpow_pos : 0 < (beta : ℝ) ^ my := zpow_pos hbpos _
    rw [← Real.log_lt_log_iff hy_abs_pos hpow_pos]
    exact hlog_lt

  -- From my ≤ mx - 2: |y| < β^(mx - 2)
  have hy_lt_pow : |y| < (beta : ℝ) ^ (mx - 2) := by
    have hpow_le : (beta : ℝ) ^ my ≤ (beta : ℝ) ^ (mx - 2) := zpow_le_zpow_right₀ hβR_ge hmy_le'
    exact lt_of_lt_of_le hy_ub_my hpow_le

  -- |y| < |x| since β^(mx-2) < β^(mx-1) ≤ |x|
  have hy_lt_x : |y| < |x| := by
    have hpow_lt : (beta : ℝ) ^ (mx - 2) < (beta : ℝ) ^ (mx - 1) := by
      have hlt : mx - 2 < mx - 1 := by grind
      exact zpow_lt_zpow_right₀ hβR hlt
    calc |y| < (beta : ℝ) ^ (mx - 2) := hy_lt_pow
      _ < (beta : ℝ) ^ (mx - 1) := hpow_lt
      _ ≤ |x| := hx_lb

  -- x + y ≠ 0 (since |y| < |x|)
  have hxy_ne : x + y ≠ 0 := by
    intro h
    have : x = -y := by linarith
    rw [this] at hy_lt_x
    simp only [abs_neg] at hy_lt_x
    exact (lt_irrefl _) hy_lt_x

  -- Key bound: |x + y| ≥ |x| - |y| (reversed triangle inequality)
  have htri : |x| - |y| ≤ |x + y| := by
    have h_diff_pos : 0 ≤ |x| - |y| := by linarith
    have h_abs_diff : |x| - |y| = abs (|x| - |y|) := (abs_of_nonneg h_diff_pos).symm
    rw [h_abs_diff]
    have := abs_abs_sub_abs_le_abs_sub x (-y)
    simp only [abs_neg, sub_neg_eq_add] at this
    exact this

  -- |x| - |y| > β^(mx-1) - β^(mx-2) = β^(mx-2)(β - 1) ≥ β^(mx-2)
  have hdiff_lb : |x| - |y| > (beta : ℝ) ^ (mx - 2) := by
    have hdiff_ge : |x| - |y| > (beta : ℝ) ^ (mx - 1) - (beta : ℝ) ^ (mx - 2) := by
      linarith
    have hfactor : (beta : ℝ) ^ (mx - 1) - (beta : ℝ) ^ (mx - 2) =
        (beta : ℝ) ^ (mx - 2) * ((beta : ℝ) - 1) := by
      have heq : (mx - 1 : ℤ) = (mx - 2) + 1 := by ring
      rw [heq, zpow_add₀ hbne, zpow_one]
      ring
    rw [hfactor] at hdiff_ge
    -- beta ≥ 2 as integer, so (beta : ℝ) - 1 ≥ 1
    have hbeta_ge_two : (2 : ℤ) ≤ beta := hβ
    have hbeta_ge : (beta : ℝ) - 1 ≥ 1 := by
      have : (2 : ℝ) ≤ (beta : ℝ) := by exact_mod_cast hbeta_ge_two
      linarith
    have hpow_pos : 0 < (beta : ℝ) ^ (mx - 2) := zpow_pos hbpos _
    have hpow_nonneg : 0 ≤ (beta : ℝ) ^ (mx - 2) := le_of_lt hpow_pos
    have hone_le : (1 : ℝ) ≤ (beta : ℝ) - 1 := hbeta_ge
    have hmul_ineq : (beta : ℝ) ^ (mx - 2) * 1 ≤ (beta : ℝ) ^ (mx - 2) * ((beta : ℝ) - 1) :=
      mul_le_mul_of_nonneg_left hone_le hpow_nonneg
    have hpow_eq : (beta : ℝ) ^ (mx - 2) * 1 = (beta : ℝ) ^ (mx - 2) := mul_one _
    rw [hpow_eq] at hmul_ineq
    linarith

  -- |x + y| ≥ β^(mx-2)
  have hxy_lb : (beta : ℝ) ^ (mx - 2) ≤ |x + y| := by
    have hlt : (beta : ℝ) ^ (mx - 2) < |x + y| := lt_of_lt_of_le hdiff_lb htri
    exact le_of_lt hlt

  -- Set up mxy
  set mxy := Int.floor (Real.log |x + y| / Real.log (beta : ℝ)) + 1 with hmxy_def

  -- From |x + y| ≥ β^(mx-2), we get mxy ≥ mx - 1
  have hmxy_ge : mxy ≥ mx - 1 := by
    have hxy_abs_pos : 0 < |x + y| := abs_pos.mpr hxy_ne
    have hlog_lb : Real.log |x + y| ≥ (mx - 2 : ℤ) * Real.log (beta : ℝ) := by
      have hlog_pow : Real.log ((beta : ℝ) ^ (mx - 2)) = (mx - 2 : ℤ) * Real.log (beta : ℝ) := by
        rw [Real.log_zpow]
      rw [← hlog_pow]
      exact Real.log_le_log (zpow_pos hbpos _) hxy_lb
    have hdiv_lb : Real.log |x + y| / Real.log (beta : ℝ) ≥ (mx - 2 : ℤ) := by
      rw [ge_iff_le, le_div_iff₀ hlogβ_pos]
      exact hlog_lb
    have hfloor_lb : Int.floor (Real.log |x + y| / Real.log (beta : ℝ)) ≥ mx - 2 := by
      exact Int.le_floor.mpr hdiv_lb
    simp only [hmxy_def]
    grind

  -- Prove the WP goal
  simp only [mag, hxy_ne, ite_false, hx_ne, hmxy_def, hmx_def]
  exact hmxy_ge

/-- Bounds on magnitude under division -/
theorem mag_div (beta : Int) (x y : ℝ)
    (hβ : 1 < beta)
    (hx_ne : x ≠ 0)
    (hy_ne : y ≠ 0) :
    mag beta x - mag beta y ≤ mag beta (x / y) ∧
      mag beta (x / y) ≤ mag beta x - mag beta y + 1 := by
  have hβR : (1 : ℝ) < (beta : ℝ) := by exact_mod_cast hβ
  have hbpos : 0 < (beta : ℝ) := lt_trans zero_lt_one hβR
  have hlogβ_pos : 0 < Real.log (beta : ℝ) := Real.log_pos hβR
  have hlogβ_ne : Real.log (beta : ℝ) ≠ 0 := ne_of_gt hlogβ_pos

  -- x/y ≠ 0
  have hxy_ne : x / y ≠ 0 := div_ne_zero hx_ne hy_ne
  have hx_abs_pos : 0 < |x| := abs_pos.mpr hx_ne
  have hy_abs_pos : 0 < |y| := abs_pos.mpr hy_ne

  -- Reduce to floor expressions
  simp [mag, hx_ne, hy_ne, hxy_ne]

  -- Set up the log expressions
  set Lx := Real.log |x| / Real.log (beta : ℝ) with hLx
  set Ly := Real.log |y| / Real.log (beta : ℝ) with hLy
  set Lxy := Real.log |x / y| / Real.log (beta : ℝ) with hLxy_def
  have hLx' : Lx = Real.log x / Real.log (beta : ℝ) := by
    simpa [log_abs] using hLx
  have hLy' : Ly = Real.log y / Real.log (beta : ℝ) := by
    simpa [log_abs] using hLy
  have hLxy' : Lxy = Real.log (x / y) / Real.log (beta : ℝ) := by
    simpa [log_abs] using hLxy_def

  -- Key: log|x/y| = log|x| - log|y|
  have habs_div : |x / y| = |x| / |y| := abs_div x y
  have hlog_div : Real.log |x / y| = Real.log |x| - Real.log |y| := by
    rw [habs_div]
    exact Real.log_div (ne_of_gt hx_abs_pos) (ne_of_gt hy_abs_pos)

  -- Therefore Lxy = Lx - Ly
  have hLxy_eq : Lxy = Lx - Ly := by
    simp [hLxy_def, hLx, hLy, hlog_div]
    field_simp [hlogβ_ne]

  -- Floor bounds: ⌊Lx - Ly⌋ is between ⌊Lx⌋ - ⌊Ly⌋ - 1 and ⌊Lx⌋ - ⌊Ly⌋
  have hfloor_sub_lb : Int.floor Lx - Int.floor Ly - 1 ≤ Int.floor (Lx - Ly) := by
    have hlt : ((Int.floor Lx - Int.floor Ly - 1 : ℤ) : ℝ) < Lx - Ly := by
      have h1 : (Int.floor Lx : ℝ) ≤ Lx := Int.floor_le Lx
      have h2 : Ly < Int.floor Ly + 1 := Int.lt_floor_add_one Ly
      push_cast; linarith
    exact Int.le_floor.mpr (le_of_lt hlt)

  have hfloor_sub_ub : Int.floor (Lx - Ly) ≤ Int.floor Lx - Int.floor Ly := by
    have h1 : Lx < Int.floor Lx + 1 := Int.lt_floor_add_one Lx
    have h2 : (Int.floor Ly : ℝ) ≤ Ly := Int.floor_le Ly
    have hcast : Lx - Ly < ((Int.floor Lx - Int.floor Ly + 1 : ℤ) : ℝ) := by
      simp only [Int.cast_sub, Int.cast_add, Int.cast_one]
      linarith
    have := Int.floor_lt.mpr hcast
    linarith

  have h_goal :
      (Int.floor Lx ≤ 1 + (Int.floor Ly + Int.floor (Lx - Ly))) ∧
        (Int.floor Ly + Int.floor (Lx - Ly) ≤ Int.floor Lx) := by
    exact ⟨by linarith [hfloor_sub_lb], by linarith [hfloor_sub_ub]⟩
  have hlog_div_abs : Real.log (x / y) / Real.log (beta : ℝ) = Lx - Ly := by
    simpa [hLxy_eq] using hLxy'.symm
  simpa [hlog_div_abs, hLx', hLy', add_assoc, add_left_comm, add_comm, sub_eq_add_neg]
    using h_goal

/-- Magnitude of square root

    With floor+1 semantics: mag(√x) = ⌊log(√x)/log β⌋ + 1
-/
theorem mag_sqrt_from_log_payload (beta : Int) (x : ℝ)
    (hβ : 1 < beta)
    (hx_pos : 0 < x) :
    mag beta (Real.sqrt x) = Int.floor ((Real.log x / Real.log (beta : ℝ)) / 2) + 1 := by
  have hβR : (1 : ℝ) < (beta : ℝ) := by exact_mod_cast hβ
  have hbpos : 0 < (beta : ℝ) := lt_trans zero_lt_one hβR
  have hlogβ_pos : 0 < Real.log (beta : ℝ) := Real.log_pos hβR
  have hlogβ_ne : Real.log (beta : ℝ) ≠ 0 := ne_of_gt hlogβ_pos
  -- sqrt x > 0 and sqrt x ≠ 0
  have hsqrt_pos : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx_pos
  have hsqrt_ne : Real.sqrt x ≠ 0 := ne_of_gt hsqrt_pos
  have hx_ne : x ≠ 0 := ne_of_gt hx_pos
  have hx_nonneg : 0 ≤ x := le_of_lt hx_pos
  -- Reduce the monad
  simp only [mag]
  simp only [hsqrt_ne, hx_ne, ite_false]
  -- The key: log(sqrt x) = (1/2) * log x
  have hlog_sqrt : Real.log (Real.sqrt x) = Real.log x / 2 := Real.log_sqrt hx_nonneg
  -- Hence log(sqrt x) / log β = (log x / log β) / 2
  have heq : Real.log |Real.sqrt x| / Real.log (beta : ℝ)
           = (Real.log x / Real.log (beta : ℝ)) / 2 := by
    rw [abs_of_pos hsqrt_pos, hlog_sqrt]
    field_simp
  simp only [heq]

/-- Coq `mag_sqrt`: magnitude of a positive square root is the floor-half of
`mag x + 1` (Lean `/ 2` is the same floor division used by Coq `Z.div2`). -/
theorem mag_sqrt (beta : Int) (x : ℝ) (hβ : 1 < beta) (hx : 0 < x) :
    mag beta (Real.sqrt x) = (mag beta x + 1) / 2 := by
  set L : ℝ := Real.log x / Real.log (beta : ℝ)
  set n : Int := Int.floor L
  set q : Int := Int.floor (L / 2)
  have hnle : (n : ℝ) ≤ L := by
    simpa [n] using Int.floor_le L
  have hnlt : L < (n : ℝ) + 1 := by
    simpa [n] using Int.lt_floor_add_one L
  have hqle : (q : ℝ) ≤ L / 2 := by
    simpa [q] using Int.floor_le (L / 2)
  have hqlt : L / 2 < (q : ℝ) + 1 := by
    simpa [q] using Int.lt_floor_add_one (L / 2)
  have hlower : 2 * q ≤ n := by
    have hcast : ((2 * q : Int) : ℝ) < ((n + 1 : Int) : ℝ) := by
      push_cast
      linarith
    have hint : 2 * q < n + 1 := by exact_mod_cast hcast
    omega
  have hupper : n ≤ 2 * q + 1 := by
    have hcast : ((n : Int) : ℝ) < ((2 * q + 2 : Int) : ℝ) := by
      push_cast
      linarith
    have hint : n < 2 * q + 2 := by exact_mod_cast hcast
    omega
  have hsqrt : mag beta (Real.sqrt x) = q + 1 := by
    simpa [L, q] using mag_sqrt_from_log_payload beta x hβ hx
  have hmagx : mag beta x = n + 1 := by
    simp [mag, ne_of_gt hx, abs_of_pos hx, L, n]
  calc
    mag beta (Real.sqrt x) = q + 1 := hsqrt
    _ = (n + 2) / 2 := by omega
    _ = (mag beta x + 1) / 2 := by
      have hnum : n + 2 = mag beta x + 1 := by omega
      rw [hnum]

/-- Magnitude at 1

    With floor+1 semantics: mag(1) = ⌊0⌋ + 1 = 1
    This corresponds to 1 being in the interval from β^0 to β^1 (including left, excluding right).
-/
theorem mag_1 (beta : Int) (_hβ : 1 < beta) :
    mag beta (1 : ℝ) = 1 := by
  -- Direct computation from the definition of `mag`:
  -- |1| = 1 and log 1 = 0, hence floor(0 / log β) + 1 = 0 + 1 = 1.
  simp [mag, abs_one, Real.log_one]

end Mag

end FloatSpec.Core.Raux
