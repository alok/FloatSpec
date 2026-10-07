import FloatSpec.src.Core.Zaux

/-! The next source-ordered slice: parity, integer powers and the radix record.
Integer powers with negative exponent are zero, not real reciprocals. -/

namespace ZauxPowerRadixContracts
open FloatSpec.Core.Zaux

theorem zaux_power_radix_contracts_check_1 : ∀ x : Int, ∃ p : Int, x = 2 * p + if Z.even x then 0 else 1 := Zeven_ex
theorem zaux_power_radix_contracts_check_2 : ∀ n k₁ k₂ : Int, 0 ≤ k₁ → 0 ≤ k₂ →
    Zpower n (k₁ + k₂) = Zpower n k₁ * Zpower n k₂ := Zpower_plus
theorem zaux_power_radix_contracts_check_3 : ∀ b e : Int, 0 ≤ e → Zpower b e = b ^ e.natAbs := Zpower_Zpower_nat
theorem zaux_power_radix_contracts_check_4 : ∀ (b : Int) (e : Nat), b ^ (e + 1) = b * b ^ e := Zpower_nat_S
theorem zaux_power_radix_contracts_check_5 : ∀ (b : Int) (p : Positive), 0 < b → 0 < Zpower_pos b p := Zpower_pos_gt_0
theorem zaux_power_radix_contracts_check_6 : ∀ b e : Int, 0 ≤ e → Z.even b = false →
    Z.even (Zpower b e) = false := Zeven_Zpower_odd

-- The source Boolean-proof record and Lean proposition-proof record have the
-- same admissible values. Neither permits a radix less than two.
theorem zaux_power_radix_contracts_check_7 (r : Radix) : decide (2 ≤ r.val) = true := decide_eq_true r.prop
def zaux_power_radix_contracts_check_8 (value : Int) (h : decide (2 ≤ value) = true) : Radix :=
  ⟨value, of_decide_eq_true h⟩
theorem zaux_power_radix_contracts_check_9 : ∀ r₁ r₂ : Radix, r₁.val = r₂.val → r₁ = r₂ := radix_val_inj
theorem zaux_power_radix_contracts_check_10 : radix2.val = 2 := rfl
theorem zaux_power_radix_contracts_check_11 : ∀ r : Radix, 0 < r.val := radix_gt_0
theorem zaux_power_radix_contracts_check_12 : ∀ r : Radix, 1 < r.val := radix_gt_1
theorem zaux_power_radix_contracts_check_13 : ∀ (r : Radix) (e : Int), 0 < e → 1 < Zpower r.val e := Zpower_gt_1
theorem zaux_power_radix_contracts_check_14 : ∀ (r : Radix) (e : Int), 0 ≤ e → 0 < Zpower r.val e := Zpower_gt_0
theorem zaux_power_radix_contracts_check_15 : ∀ (r : Radix) (e : Int), 0 ≤ Zpower r.val e := Zpower_ge_0
theorem zaux_power_radix_contracts_check_16 : ∀ (r : Radix) (e₁ e₂ : Int), e₁ ≤ e₂ →
    Zpower r.val e₁ ≤ Zpower r.val e₂ := Zpower_le
theorem zaux_power_radix_contracts_check_17 : ∀ (r : Radix) (e₁ e₂ : Int), 0 ≤ e₂ → e₁ < e₂ →
    Zpower r.val e₁ < Zpower r.val e₂ := Zpower_lt
theorem zaux_power_radix_contracts_check_18 : ∀ (r : Radix) (e₁ e₂ : Int), Zpower r.val (e₁ - 1) < Zpower r.val e₂ →
    e₁ ≤ e₂ := Zpower_lt_Zpower
theorem zaux_power_radix_contracts_check_19 : ∀ (r : Radix) (n : Int), n < Zpower r.val n := Zpower_gt_id

private theorem negative_integer_powers : Zpower 2 (-2) = 0 ∧ Zpower 2 (-1) = 0 := by
  decide +kernel

private theorem strict_order_requires_nonnegative_upper :
    ¬ ∀ a b : Int, a < b → Zpower 2 a < Zpower 2 b := by
  intro h
  have impossible := h (-2) (-1) (by decide)
  norm_num [Zpower] at impossible

#print axioms strict_order_requires_nonnegative_upper

#eval do
  unless [Zpower 0 0, Zpower 0 (-1), Zpower (-2) 3, Zpower (-2) (-3), Zpower 2 0] ==
      [1, 0, -8, 0, 1] do
    throw (IO.userError "integer power boundary regression")
  IO.println "PASS: source power/radix contracts and integer negative-exponent boundary"

end ZauxPowerRadixContracts
