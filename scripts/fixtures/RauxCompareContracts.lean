import FloatSpec.src.Core.Raux

namespace RauxCompareContracts
open FloatSpec.Core.Raux

-- Raux.v:347-783. Rocq's `comparison` is Lean's `Ordering` (Lt/Eq/Gt are .lt/.eq/.gt) and
-- `CompOpp` is `Ordering.swap`; `Z.compare` is `compare` on `Int`.

-- The bodies are the source's: `Rcompare` tests `x < y` then `x = y`, and each Boolean test
-- reads one comparison outcome.
theorem raux_compare_contracts_check_1 (x y : ℝ) : Rcompare x y = if x < y then .lt else if x = y then .eq else .gt := rfl
theorem raux_compare_contracts_check_2 (x y : ℝ) : Rle_bool x y = match Rcompare x y with | .gt => false | _ => true := rfl
theorem raux_compare_contracts_check_3 (x y : ℝ) : Rlt_bool x y = match Rcompare x y with | .lt => true | _ => false := rfl
theorem raux_compare_contracts_check_4 (x y : ℝ) : Req_bool x y = match Rcompare x y with | .eq => true | _ => false := rfl

-- Graphs. Rocq's constructors take `x y` explicitly; Lean's are implicit, hence `@`.
theorem cmp_lt_ctor : ∀ x y : ℝ, x < y → Rcompare_prop x y .lt := @Rcompare_Lt_
theorem cmp_eq_ctor : ∀ x y : ℝ, x = y → Rcompare_prop x y .eq := @Rcompare_Eq_
theorem cmp_gt_ctor : ∀ x y : ℝ, y < x → Rcompare_prop x y .gt := @Rcompare_Gt_
theorem le_true_ctor : ∀ x y : ℝ, x ≤ y → Rle_bool_prop x y true := @Rle_bool_true_
theorem le_false_ctor : ∀ x y : ℝ, y < x → Rle_bool_prop x y false := @Rle_bool_false_
theorem lt_true_ctor : ∀ x y : ℝ, x < y → Rlt_bool_prop x y true := @Rlt_bool_true_
theorem lt_false_ctor : ∀ x y : ℝ, y ≤ x → Rlt_bool_prop x y false := @Rlt_bool_false_
theorem eq_true_ctor : ∀ x y : ℝ, x = y → Req_bool_prop x y true := @Req_bool_true_
theorem eq_false_ctor : ∀ x y : ℝ, x ≠ y → Req_bool_prop x y false := @Req_bool_false_

-- Rocq's generated `_ind` schemes, from Lean's dependent recursor; `_sind` targets SProp.
theorem cmp_prop_ind : ∀ (x y : ℝ) (P : Ordering → Prop),
    (x < y → P .lt) → (x = y → P .eq) → (y < x → P .gt) → ∀ c, Rcompare_prop x y c → P c :=
  fun _ _ P hl he hg _ h => Rcompare_prop.rec (motive := fun c _ => P c) hl he hg h
theorem le_prop_ind : ∀ (x y : ℝ) (P : Bool → Prop),
    (x ≤ y → P true) → (y < x → P false) → ∀ b, Rle_bool_prop x y b → P b :=
  fun _ _ P ht hf _ h => Rle_bool_prop.rec (motive := fun b _ => P b) ht hf h
theorem lt_prop_ind : ∀ (x y : ℝ) (P : Bool → Prop),
    (x < y → P true) → (y ≤ x → P false) → ∀ b, Rlt_bool_prop x y b → P b :=
  fun _ _ P ht hf _ h => Rlt_bool_prop.rec (motive := fun b _ => P b) ht hf h
theorem eq_prop_ind : ∀ (x y : ℝ) (P : Bool → Prop),
    (x = y → P true) → (x ≠ y → P false) → ∀ b, Req_bool_prop x y b → P b :=
  fun _ _ P ht hf _ h => Req_bool_prop.rec (motive := fun b _ => P b) ht hf h

-- Rcompare lemmas.
theorem cmp_spec : ∀ x y : ℝ, Rcompare_prop x y (Rcompare x y) := Rcompare_spec
theorem cmp_lt : ∀ x y : ℝ, x < y → Rcompare x y = .lt := Rcompare_Lt
theorem cmp_lt_inv : ∀ x y : ℝ, Rcompare x y = .lt → x < y := Rcompare_Lt_inv
theorem cmp_not_lt : ∀ x y : ℝ, y ≤ x → Rcompare x y ≠ .lt := Rcompare_not_Lt
theorem cmp_not_lt_inv : ∀ x y : ℝ, Rcompare x y ≠ .lt → y ≤ x := Rcompare_not_Lt_inv
theorem cmp_eq : ∀ x y : ℝ, x = y → Rcompare x y = .eq := Rcompare_Eq
theorem cmp_eq_inv : ∀ x y : ℝ, Rcompare x y = .eq → x = y := Rcompare_Eq_inv
theorem cmp_gt : ∀ x y : ℝ, y < x → Rcompare x y = .gt := Rcompare_Gt
theorem cmp_gt_inv : ∀ x y : ℝ, Rcompare x y = .gt → y < x := Rcompare_Gt_inv
theorem cmp_not_gt : ∀ x y : ℝ, x ≤ y → Rcompare x y ≠ .gt := Rcompare_not_Gt
theorem cmp_not_gt_inv : ∀ x y : ℝ, Rcompare x y ≠ .gt → x ≤ y := Rcompare_not_Gt_inv
theorem cmp_izr : ∀ x y : Int, Rcompare (x : ℝ) (y : ℝ) = compare x y := Rcompare_IZR
theorem cmp_sym : ∀ x y : ℝ, Rcompare x y = (Rcompare y x).swap := Rcompare_sym
theorem cmp_opp : ∀ x y : ℝ, Rcompare (-x) (-y) = Rcompare y x := Rcompare_opp
theorem cmp_plus_r : ∀ z x y : ℝ, Rcompare (x + z) (y + z) = Rcompare x y := Rcompare_plus_r
theorem cmp_plus_l : ∀ z x y : ℝ, Rcompare (z + x) (z + y) = Rcompare x y := Rcompare_plus_l
theorem cmp_mult_r : ∀ z x y : ℝ, 0 < z → Rcompare (x * z) (y * z) = Rcompare x y :=
  Rcompare_mult_r
theorem cmp_mult_l : ∀ z x y : ℝ, 0 < z → Rcompare (z * x) (z * y) = Rcompare x y :=
  Rcompare_mult_l
theorem cmp_middle : ∀ x d u : ℝ, Rcompare (x - d) (u - x) = Rcompare x ((d + u) / 2) :=
  Rcompare_middle
theorem cmp_half_l : ∀ x y : ℝ, Rcompare (x / 2) y = Rcompare x (2 * y) := Rcompare_half_l
theorem cmp_half_r : ∀ x y : ℝ, Rcompare x (y / 2) = Rcompare (2 * x) y := Rcompare_half_r
theorem cmp_sqr : ∀ x y : ℝ, Rcompare (x * x) (y * y) = Rcompare |x| |y| := Rcompare_sqr
theorem min_compare : ∀ x y : ℝ,
    min x y = match Rcompare x y with | .lt => x | .eq => x | .gt => y := Rmin_compare

-- Boolean tests. In the source, `negb_Rlt_bool` is the lemma about `negb (Rle_bool ...)`.
theorem le_spec : ∀ x y : ℝ, Rle_bool_prop x y (Rle_bool x y) := Rle_bool_spec
theorem le_true : ∀ x y : ℝ, x ≤ y → Rle_bool x y = true := Rle_bool_true
theorem le_false : ∀ x y : ℝ, y < x → Rle_bool x y = false := Rle_bool_false
theorem lt_spec : ∀ x y : ℝ, Rlt_bool_prop x y (Rlt_bool x y) := Rlt_bool_spec
theorem negb_lt : ∀ x y : ℝ, (!Rle_bool x y) = Rlt_bool y x := negb_Rlt_bool
theorem negb_le : ∀ x y : ℝ, (!Rlt_bool x y) = Rle_bool y x := negb_Rle_bool
theorem lt_true : ∀ x y : ℝ, x < y → Rlt_bool x y = true := Rlt_bool_true
theorem lt_false : ∀ x y : ℝ, y ≤ x → Rlt_bool x y = false := Rlt_bool_false
theorem lt_opp : ∀ x y : ℝ, Rlt_bool (-x) (-y) = Rlt_bool y x := Rlt_bool_opp
theorem eq_spec : ∀ x y : ℝ, Req_bool_prop x y (Req_bool x y) := Req_bool_spec
theorem eq_true : ∀ x y : ℝ, x = y → Req_bool x y = true := Req_bool_true
theorem eq_false : ∀ x y : ℝ, x ≠ y → Req_bool x y = false := Req_bool_false

#print axioms cmp_prop_ind
#print axioms cmp_izr
#print axioms min_compare
#print axioms negb_lt

-- The graphs are functional: equal inputs have no strict branch.
private theorem le_graph_false_is_strict : ¬ Rle_bool_prop 0 0 false := by
  intro h
  cases h with
  | Rle_bool_false_ h => exact lt_irrefl _ h

private theorem lt_graph_true_is_strict : ¬ Rlt_bool_prop 0 0 true := by
  intro h
  cases h with
  | Rlt_bool_true_ h => exact lt_irrefl _ h

-- Scaling by a negative number reverses the comparison, so `0 < z` is needed.
private theorem mult_r_needs_pos :
    ¬ ∀ z x y : ℝ, Rcompare (x * z) (y * z) = Rcompare x y := by
  intro h
  have := h (-1) 0 1
  rw [Rcompare_Gt _ _ (by norm_num), Rcompare_Lt _ _ (by norm_num)] at this
  exact absurd this (by decide)

-- Comparison is antisymmetric: `Rcompare_sym` needs its swap.
private theorem sym_needs_swap : ¬ ∀ x y : ℝ, Rcompare x y = Rcompare y x := by
  intro h
  have := h 0 1
  rw [Rcompare_Lt _ _ (by norm_num), Rcompare_Gt _ _ (by norm_num)] at this
  exact absurd this (by decide)

#print axioms le_graph_false_is_strict
#print axioms mult_r_needs_pos

end RauxCompareContracts
