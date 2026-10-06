import FloatSpec.src.Core.Zaux

namespace ZauxBooleanContracts
open FloatSpec.Core.Zaux

-- Each source section is a Prop-valued graph indexed by the Boolean (or comparison) result.
-- Rocq's constructors take `x y` explicitly; Lean's take them implicitly, so `@` presents
-- the source shape. Premises are exact: the false branch of `Zle_bool_prop` is strict and
-- the false branch of `Zlt_bool_prop` is not.
theorem eq_true_ctor : ∀ x y : Int, x = y → Zeq_bool_prop x y true := @Zeq_bool_true_
theorem eq_false_ctor : ∀ x y : Int, x ≠ y → Zeq_bool_prop x y false := @Zeq_bool_false_
theorem le_true_ctor : ∀ x y : Int, x ≤ y → Zle_bool_prop x y true := @Zle_bool_true_
theorem le_false_ctor : ∀ x y : Int, y < x → Zle_bool_prop x y false := @Zle_bool_false_
theorem lt_true_ctor : ∀ x y : Int, x < y → Zlt_bool_prop x y true := @Zlt_bool_true_
theorem lt_false_ctor : ∀ x y : Int, y ≤ x → Zlt_bool_prop x y false := @Zlt_bool_false_
theorem cmp_lt_ctor : ∀ x y : Int, x < y → Zcompare_prop x y .lt := @Zcompare_Lt_
theorem cmp_eq_ctor : ∀ x y : Int, x = y → Zcompare_prop x y .eq := @Zcompare_Eq_
theorem cmp_gt_ctor : ∀ x y : Int, y < x → Zcompare_prop x y .gt := @Zcompare_Gt_

-- Rocq generates `_ind` (motive into Prop) and `_sind` (into SProp) with a motive over the
-- index only. Lean's single recursor has a dependent motive into Prop; specializing it gives
-- the `_ind` shape. Lean has no SProp, so `_sind` has no separate counterpart.
theorem eq_prop_ind : ∀ (x y : Int) (P : Bool → Prop),
    (x = y → P true) → (x ≠ y → P false) → ∀ b, Zeq_bool_prop x y b → P b :=
  fun _ _ P ht hf _ h => Zeq_bool_prop.rec (motive := fun b _ => P b) ht hf h
theorem le_prop_ind : ∀ (x y : Int) (P : Bool → Prop),
    (x ≤ y → P true) → (y < x → P false) → ∀ b, Zle_bool_prop x y b → P b :=
  fun _ _ P ht hf _ h => Zle_bool_prop.rec (motive := fun b _ => P b) ht hf h
theorem lt_prop_ind : ∀ (x y : Int) (P : Bool → Prop),
    (x < y → P true) → (y ≤ x → P false) → ∀ b, Zlt_bool_prop x y b → P b :=
  fun _ _ P ht hf _ h => Zlt_bool_prop.rec (motive := fun b _ => P b) ht hf h
theorem cmp_prop_ind : ∀ (x y : Int) (P : Ordering → Prop),
    (x < y → P .lt) → (x = y → P .eq) → (y < x → P .gt) →
    ∀ c, Zcompare_prop x y c → P c :=
  fun _ _ P hl he hg _ h => Zcompare_prop.rec (motive := fun c _ => P c) hl he hg h

-- The 27 source lemmas, with Rocq's argument order and orientation.
theorem eq_spec : ∀ x y : Int, Zeq_bool_prop x y (Zeq_bool x y) := Zeq_bool_spec
theorem eq_true : ∀ x y : Int, x = y → Zeq_bool x y = true := Zeq_bool_true
theorem eq_false : ∀ x y : Int, x ≠ y → Zeq_bool x y = false := Zeq_bool_false
theorem eq_diag : ∀ x : Int, Zeq_bool x x = true := Zeq_bool_diag
theorem eq_opp : ∀ x y : Int, Zeq_bool (-x) y = Zeq_bool x (-y) := Zeq_bool_opp
theorem eq_opp' : ∀ x y : Int, Zeq_bool (-x) (-y) = Zeq_bool x y := Zeq_bool_opp'

theorem le_spec : ∀ x y : Int, Zle_bool_prop x y (Zle_bool x y) := Zle_bool_spec
theorem le_true : ∀ x y : Int, x ≤ y → Zle_bool x y = true := Zle_bool_true
theorem le_false : ∀ x y : Int, y < x → Zle_bool x y = false := Zle_bool_false
theorem le_opp_l : ∀ x y : Int, Zle_bool (-x) y = Zle_bool (-y) x := Zle_bool_opp_l
theorem le_opp : ∀ x y : Int, Zle_bool (-x) (-y) = Zle_bool y x := Zle_bool_opp
theorem le_opp_r : ∀ x y : Int, Zle_bool x (-y) = Zle_bool y (-x) := Zle_bool_opp_r

theorem lt_spec : ∀ x y : Int, Zlt_bool_prop x y (Zlt_bool x y) := Zlt_bool_spec
theorem lt_true : ∀ x y : Int, x < y → Zlt_bool x y = true := Zlt_bool_true
theorem lt_false : ∀ x y : Int, y ≤ x → Zlt_bool x y = false := Zlt_bool_false
theorem negb_le : ∀ x y : Int, (!Zle_bool x y) = Zlt_bool y x := negb_Zle_bool
theorem negb_lt : ∀ x y : Int, (!Zlt_bool x y) = Zle_bool y x := negb_Zlt_bool
theorem lt_opp_l : ∀ x y : Int, Zlt_bool (-x) y = Zlt_bool (-y) x := Zlt_bool_opp_l
theorem lt_opp_r : ∀ x y : Int, Zlt_bool x (-y) = Zlt_bool y (-x) := Zlt_bool_opp_r
theorem lt_opp : ∀ x y : Int, Zlt_bool (-x) (-y) = Zlt_bool y x := Zlt_bool_opp

-- Rocq's `comparison` is Lean's `Ordering` and `Z.compare` is Lean's `compare` on `Int`.
theorem cmp_spec : ∀ x y : Int, Zcompare_prop x y (compare x y) := Zcompare_spec
theorem cmp_lt : ∀ x y : Int, x < y → compare x y = .lt := Zcompare_Lt
theorem cmp_eq : ∀ x y : Int, x = y → compare x y = .eq := Zcompare_Eq
theorem cmp_gt : ∀ x y : Int, y < x → compare x y = .gt := Zcompare_Gt

#print axioms eq_prop_ind
#print axioms cmp_prop_ind
#print axioms le_opp_l
#print axioms negb_le
#print axioms cmp_spec

-- The graphs are functional because the branches are disjoint: at x = y the `≤` graph
-- has no false branch and the `<` graph has no true branch.
private theorem le_graph_false_branch_is_strict : ¬ Zle_bool_prop 0 0 false := by
  intro h
  cases h with
  | Zle_bool_false_ h => exact absurd h (by decide)

private theorem lt_graph_true_branch_is_strict : ¬ Zlt_bool_prop 0 0 true := by
  intro h
  cases h with
  | Zlt_bool_true_ h => exact absurd h (by decide)

-- Orientation matters. Negating one side of the order moves both arguments.
private theorem le_opp_l_needs_swap : ¬ ∀ x y : Int, Zle_bool (-x) y = Zle_bool x (-y) := by
  intro h
  exact absurd (h 0 1) (by decide)

-- The complement of `x ≤ y` is `y < x`, not `x < y`.
private theorem negb_le_needs_swap : ¬ ∀ x y : Int, (!Zle_bool x y) = Zlt_bool x y := by
  intro h
  exact absurd (h 0 1) (by decide)

-- Moving one negation across equality negates the other side.
private theorem eq_opp_needs_negation : ¬ ∀ x y : Int, Zeq_bool (-x) y = Zeq_bool x y := by
  intro h
  exact absurd (h 1 (-1)) (by decide)

#print axioms le_graph_false_branch_is_strict
#print axioms lt_graph_true_branch_is_strict
#print axioms le_opp_l_needs_swap
#print axioms negb_le_needs_swap
#print axioms eq_opp_needs_negation

example : compare (-3 : Int) 2 = .lt ∧ compare (2 : Int) 2 = .eq ∧ compare (2 : Int) (-3) = .gt := by
  decide +kernel

-- Every law on small signed values and machine-word boundaries, including bignums.
#eval do
  let small := (List.range 17).map fun k => Int.ofNat k - 8
  let edges : List Int := [-2^64, -2^63 - 1, -2^63, 2^63 - 1, 2^63, 2^64]
  let values := small ++ edges
  let mut checked := 0
  for x in values do
    for y in values do
      let sign : Int := match compare x y with | .lt => -1 | .eq => 0 | .gt => 1
      unless Zeq_bool x y == (x == y) && Zle_bool x y == decide (x ≤ y) &&
          Zlt_bool x y == decide (x < y) && sign == (if x < y then -1 else if x = y then 0 else 1) do
        throw (IO.userError s!"Boolean comparison definition: {x}, {y}")
      unless Zeq_bool (-x) y == Zeq_bool x (-y) && Zeq_bool (-x) (-y) == Zeq_bool x y &&
          Zle_bool (-x) y == Zle_bool (-y) x && Zle_bool (-x) (-y) == Zle_bool y x &&
          Zle_bool x (-y) == Zle_bool y (-x) && (!Zle_bool x y) == Zlt_bool y x &&
          (!Zlt_bool x y) == Zle_bool y x && Zlt_bool (-x) y == Zlt_bool (-y) x &&
          Zlt_bool x (-y) == Zlt_bool y (-x) && Zlt_bool (-x) (-y) == Zlt_bool y x do
        throw (IO.userError s!"Boolean comparison law: {x}, {y}")
      checked := checked + 1
  IO.println s!"PASS: {checked} signed pairs; Boolean comparison definitions and laws"

end ZauxBooleanContracts
