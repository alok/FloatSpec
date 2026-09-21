import FloatSpec.src.Core.Zaux

/-! The next source-ordered slice: parity, integer powers and the radix record.
Integer powers with negative exponent are zero, not real reciprocals. -/

namespace ZauxPowerRadixContracts
open FloatSpec.Core.Zaux

example (x : Int) : ∃ p : Int, x = 2 * p + if decide (Even x) then 0 else 1 := by
  simpa using Zeven_ex x
example : ∀ n k₁ k₂ : Int, 0 ≤ k₁ → 0 ≤ k₂ →
    Zpower n (k₁ + k₂) = Zpower n k₁ * Zpower n k₂ := Zpower_plus
example : ∀ b e : Int, 0 ≤ e → Zpower b e = b ^ e.natAbs := Zpower_Zpower_nat
example : ∀ (b : Int) (e : Nat), b ^ (e + 1) = b * b ^ e := Zpower_nat_S
example : ∀ (b : Int) (p : Positive), 0 < b → 0 < Zpower_pos b p := Zpower_pos_gt_0
example : ∀ b e : Int, 0 ≤ e → decide (Even b) = false →
    decide (Even (Zpower b e)) = false := Zeven_Zpower_odd

-- The source Boolean-proof record and Lean proposition-proof record have the
-- same admissible values. Neither permits a radix less than two.
example (r : Radix) : decide (2 ≤ r.val) = true := decide_eq_true r.prop
example (value : Int) (h : decide (2 ≤ value) = true) : Radix :=
  ⟨value, of_decide_eq_true h⟩
example : ∀ r₁ r₂ : Radix, r₁.val = r₂.val → r₁ = r₂ := radix_val_inj
example : radix2.val = 2 := rfl
example : ∀ r : Radix, 0 < r.val := radix_gt_0
example : ∀ r : Radix, 1 < r.val := radix_gt_1
example : ∀ (r : Radix) (e : Int), 0 < e → 1 < Zpower r.val e := Zpower_gt_1
example : ∀ (r : Radix) (e : Int), 0 ≤ e → 0 < Zpower r.val e := Zpower_gt_0
example : ∀ (r : Radix) (e : Int), 0 ≤ Zpower r.val e := Zpower_ge_0
example : ∀ (r : Radix) (e₁ e₂ : Int), e₁ ≤ e₂ →
    Zpower r.val e₁ ≤ Zpower r.val e₂ := Zpower_le
example : ∀ (r : Radix) (e₁ e₂ : Int), 0 ≤ e₂ → e₁ < e₂ →
    Zpower r.val e₁ < Zpower r.val e₂ := Zpower_lt
example : ∀ (r : Radix) (e₁ e₂ : Int), Zpower r.val (e₁ - 1) < Zpower r.val e₂ →
    e₁ ≤ e₂ := Zpower_lt_Zpower
example : ∀ (r : Radix) (n : Int), n < Zpower r.val n := Zpower_gt_id

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
