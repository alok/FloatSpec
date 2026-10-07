import FloatSpec.src.Core.Raux

namespace RauxFloorContracts
open FloatSpec.Core.Raux

-- Raux.v:785-1330. Rocq's `Zfloor x` is `up x - 1` for its archimedean primitive `up`; Lean's
-- floor plays that role. The other three bodies are the source's.
theorem raux_floor_contracts_check_1 (x : ℝ) : Zfloor x = ⌊x⌋ := rfl
theorem raux_floor_contracts_check_2 (x : ℝ) : Zceil x = -Zfloor (-x) := rfl
theorem raux_floor_contracts_check_3 (x : ℝ) : Ztrunc x = if Rlt_bool x 0 then Zceil x else Zfloor x := rfl
theorem raux_floor_contracts_check_4 (x : ℝ) : Zaway x = if Rlt_bool x 0 then Zfloor x else Zceil x := rfl

-- `IZR` is the integer cast; `Z.abs` is the cast of `natAbs`; `Z.div`/`Z.quot` are
-- `Int.fdiv`/`Int.tdiv`; `/2` is `(2 : ℝ)⁻¹`.
theorem floor_lb : ∀ x : ℝ, ((Zfloor x : Int) : ℝ) ≤ x := Zfloor_lb
theorem floor_ub : ∀ x : ℝ, x < ((Zfloor x : Int) : ℝ) + 1 := Zfloor_ub
theorem floor_lub : ∀ (n : Int) (x : ℝ), (n : ℝ) ≤ x → n ≤ Zfloor x := Zfloor_lub
theorem floor_imp : ∀ (n : Int) (x : ℝ), (n : ℝ) ≤ x ∧ x < ((n + 1 : Int) : ℝ) → Zfloor x = n :=
  Zfloor_imp
theorem floor_izr : ∀ n : Int, Zfloor (n : ℝ) = n := Zfloor_IZR
theorem floor_le : ∀ x y : ℝ, x ≤ y → Zfloor x ≤ Zfloor y := Zfloor_le
theorem ceil_ub : ∀ x : ℝ, x ≤ ((Zceil x : Int) : ℝ) := Zceil_ub
theorem ceil_lb : ∀ x : ℝ, ((Zceil x : Int) : ℝ) < x + 1 := Zceil_lb
theorem ceil_glb : ∀ (n : Int) (x : ℝ), x ≤ (n : ℝ) → Zceil x ≤ n := Zceil_glb
theorem ceil_imp : ∀ (n : Int) (x : ℝ), ((n - 1 : Int) : ℝ) < x ∧ x ≤ (n : ℝ) → Zceil x = n :=
  Zceil_imp
theorem ceil_izr : ∀ n : Int, Zceil (n : ℝ) = n := Zceil_IZR
theorem ceil_le : ∀ x y : ℝ, x ≤ y → Zceil x ≤ Zceil y := Zceil_le
theorem ceil_floor_neq : ∀ x : ℝ, ((Zfloor x : Int) : ℝ) ≠ x → Zceil x = Zfloor x + 1 :=
  Zceil_floor_neq
theorem trunc_izr : ∀ n : Int, Ztrunc (n : ℝ) = n := Ztrunc_IZR
theorem trunc_floor : ∀ x : ℝ, 0 ≤ x → Ztrunc x = Zfloor x := Ztrunc_floor
theorem trunc_ceil : ∀ x : ℝ, x ≤ 0 → Ztrunc x = Zceil x := Ztrunc_ceil
theorem trunc_le : ∀ x y : ℝ, x ≤ y → Ztrunc x ≤ Ztrunc y := Ztrunc_le
theorem trunc_opp : ∀ x : ℝ, Ztrunc (-x) = -Ztrunc x := Ztrunc_opp
theorem trunc_abs : ∀ x : ℝ, Ztrunc |x| = ((Ztrunc x).natAbs : Int) := Ztrunc_abs
theorem trunc_lub : ∀ (n : Int) (x : ℝ), (n : ℝ) ≤ |x| → n ≤ ((Ztrunc x).natAbs : Int) :=
  Ztrunc_lub
theorem away_izr : ∀ n : Int, Zaway (n : ℝ) = n := Zaway_IZR
theorem away_ceil : ∀ x : ℝ, 0 ≤ x → Zaway x = Zceil x := Zaway_ceil
theorem away_floor : ∀ x : ℝ, x ≤ 0 → Zaway x = Zfloor x := Zaway_floor
theorem away_le : ∀ x y : ℝ, x ≤ y → Zaway x ≤ Zaway y := Zaway_le
theorem away_opp : ∀ x : ℝ, Zaway (-x) = -Zaway x := Zaway_opp
theorem away_abs : ∀ x : ℝ, Zaway |x| = ((Zaway x).natAbs : Int) := Zaway_abs
theorem floor_ceil_middle : ∀ x : ℝ, ((Zfloor x : Int) : ℝ) ≠ x →
    Rcompare (x - (Zfloor x : ℝ)) (2 : ℝ)⁻¹ = Rcompare (x - (Zfloor x : ℝ)) ((Zceil x : ℝ) - x) :=
  Rcompare_floor_ceil_middle
theorem ceil_floor_middle : ∀ x : ℝ, ((Zfloor x : Int) : ℝ) ≠ x →
    Rcompare ((Zceil x : ℝ) - x) (2 : ℝ)⁻¹ = Rcompare ((Zceil x : ℝ) - x) (x - (Zfloor x : ℝ)) :=
  Rcompare_ceil_floor_middle
theorem floor_div : ∀ x y : Int, y ≠ 0 → Zfloor ((x : ℝ) / (y : ℝ)) = Int.fdiv x y := Zfloor_div
theorem trunc_div : ∀ x y : Int, y ≠ 0 → Ztrunc ((x : ℝ) / (y : ℝ)) = Int.tdiv x y := Ztrunc_div

#print axioms trunc_abs
#print axioms floor_div

-- Negative halves: floor and away go down, ceiling and truncation go up.
theorem raux_floor_contracts_check_5 : Zfloor (-5/2) = -3 ∧ Zceil (-5/2) = -2 ∧ Ztrunc (-5/2) = -2 ∧ Zaway (-5/2) = -3 := by
  have hf : Zfloor (-5/2) = -3 := Zfloor_imp (-3) _ (by norm_num)
  have hc : Zceil (-5/2) = -2 := Zceil_imp (-2) _ (by norm_num)
  exact ⟨hf, hc, (Ztrunc_ceil _ (by norm_num)).trans hc, (Zaway_floor _ (by norm_num)).trans hf⟩

private theorem trunc_floor_needs_nonneg : ¬ ∀ x : ℝ, Ztrunc x = Zfloor x := by
  intro h
  have := h (-1/2)
  rw [Ztrunc_ceil _ (by norm_num), Zceil_imp 0 _ (by norm_num), Zfloor_imp (-1) _ (by norm_num)]
    at this
  exact absurd this (by decide)

private theorem ceil_floor_neq_needs_premise : ¬ ∀ x : ℝ, Zceil x = Zfloor x + 1 := by
  intro h
  have := h 0
  rw [show (0 : ℝ) = ((0 : Int) : ℝ) by norm_num, Zceil_IZR, Zfloor_IZR] at this
  exact absurd this (by decide)

-- Both systems divide by zero to zero, so the source's `y ≠ 0` premise is not needed.
theorem raux_floor_contracts_check_6 (x : Int) : Zfloor ((x : ℝ) / ((0 : Int) : ℝ)) = Int.fdiv x 0 := by
  simp [Zfloor]
theorem raux_floor_contracts_check_7 (x : Int) : Ztrunc ((x : ℝ) / ((0 : Int) : ℝ)) = Int.tdiv x 0 := by
  simp [Ztrunc_eq_ite]

#print axioms trunc_floor_needs_nonneg

end RauxFloorContracts
