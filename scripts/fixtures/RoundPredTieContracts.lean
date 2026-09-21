import FloatSpec.src.Core.Round_pred

namespace RoundPredTieContracts
open FloatSpec.Core.Defs (round_pred round_pred_total round_pred_monotone)
open FloatSpec.Core.Round_pred

-- Pointwise liftings have no extra premises or different tie policies.
example (F r) : Rnd_DN F r = (∀ x, Rnd_DN_pt F x (r x)) := rfl
example (F r) : Rnd_UP F r = (∀ x, Rnd_UP_pt F x (r x)) := rfl
example (F r) : Rnd_ZR F r = (∀ x, Rnd_ZR_pt F x (r x)) := rfl
example (F r) : Rnd_N F r = (∀ x, Rnd_N_pt F x (r x)) := rfl
example (F P r) : Rnd_NG F P r = (∀ x, Rnd_NG_pt F P x (r x)) := rfl
example (F r) : Rnd_NA F r = (∀ x, Rnd_NA_pt F x (r x)) := rfl
example (F r) : Rnd_N0 F r = (∀ x, Rnd_N0_pt F x (r x)) := rfl

noncomputable def value_contract : ∀ rnd, round_pred rnd → ∀ x, {f : Real // rnd x f} :=
  round_val_of_pred
noncomputable def function_contract : ∀ rnd, round_pred rnd →
    {f : Real → Real // ∀ x, rnd x (f x)} := round_fun_of_pred

example : ∀ F, F 0 → Rnd_N_pt F 0 0 := Rnd_N_pt_0
example : ∀ F, F 0 → ∀ x f, 0 ≤ x → Rnd_N_pt F x f → 0 ≤ f := Rnd_N_pt_ge_0
example : ∀ F, F 0 → ∀ x f, x ≤ 0 → Rnd_N_pt F x f → f ≤ 0 := Rnd_N_pt_le_0
example : ∀ F, F 0 → (∀ x, F x → F (-x)) → ∀ x f,
    Rnd_N_pt F x f → Rnd_N_pt F |x| |f| := Rnd_N_pt_abs
example : ∀ F x d u f, F f → Rnd_DN_pt F x d → Rnd_UP_pt F x u →
    |f - x| ≤ x - d → |f - x| ≤ u - x → Rnd_N_pt F x f := Rnd_N_pt_DN_UP
example : ∀ F x d u, Rnd_DN_pt F x d → Rnd_UP_pt F x u →
    x - d ≤ u - x → Rnd_N_pt F x d := Rnd_N_pt_DN
example : ∀ F x d u, Rnd_DN_pt F x d → Rnd_UP_pt F x u →
    u - x ≤ x - d → Rnd_N_pt F x u := Rnd_N_pt_UP

-- The source uniqueness condition accepts Type-valued predicates; the actual
-- generic nearest relation uses Prop-valued predicates. Keep that distinction.
universe u
example (F) (P : Real → Real → Type u) : Rnd_NG_pt_unique_prop F P =
    (∀ x d u, Rnd_DN_pt F x d → Rnd_N_pt F x d →
      Rnd_UP_pt F x u → Rnd_N_pt F x u → P x d → P x u → d = u) := rfl
example : ∀ F P, Rnd_NG_pt_unique_prop F P → ∀ x f g,
    Rnd_NG_pt F P x f → Rnd_NG_pt F P x g → f = g := Rnd_NG_pt_unique
example : ∀ F P, Rnd_NG_pt_unique_prop F P → round_pred_monotone (Rnd_NG_pt F P) :=
  Rnd_NG_pt_monotone
example : ∀ F P x, F x → Rnd_NG_pt F P x x := Rnd_NG_pt_refl
example : ∀ F P, (∀ x, F x → F (-x)) → (∀ x f, P x f → P (-x) (-f)) →
    ∀ x f, Rnd_NG_pt F P (-x) (-f) → Rnd_NG_pt F P x f := Rnd_NG_pt_opp_inv
example : ∀ F P, Rnd_NG_pt_unique_prop F P → ∀ r s,
    Rnd_NG F P r → Rnd_NG F P s → ∀ x, r x = s x := Rnd_NG_unique

example : ∀ F, F 0 → ∀ x f,
    Rnd_NA_pt F x f ↔ Rnd_NG_pt F (fun x f ↦ |x| ≤ |f|) x f := Rnd_NA_NG_pt
example : ∀ F, F 0 → Rnd_NG_pt_unique_prop F (fun x f ↦ |x| ≤ |f|) :=
  Rnd_NA_pt_unique_prop
example : ∀ F, F 0 → ∀ x f g, Rnd_NA_pt F x f → Rnd_NA_pt F x g → f = g :=
  Rnd_NA_pt_unique
example : ∀ F, F 0 → ∀ x f, Rnd_N_pt F x f → |x| ≤ |f| → Rnd_NA_pt F x f :=
  Rnd_NA_pt_N
example : ∀ F, F 0 → ∀ r s, Rnd_NA F r → Rnd_NA F s → ∀ x, r x = s x := Rnd_NA_unique
example : ∀ F, F 0 → round_pred_monotone (Rnd_NA_pt F) := Rnd_NA_pt_monotone
example : ∀ F x, F x → Rnd_NA_pt F x x := Rnd_NA_pt_refl
example : ∀ F x f, Rnd_NA_pt F x f → F x → f = x := Rnd_NA_pt_idempotent
example : ∀ F, F 0 → ∀ x f,
    Rnd_N0_pt F x f ↔ Rnd_NG_pt F (fun x f ↦ |f| ≤ |x|) x f := Rnd_N0_NG_pt
example : ∀ F, F 0 → Rnd_NG_pt_unique_prop F (fun x f ↦ |f| ≤ |x|) :=
  Rnd_N0_pt_unique_prop
example : ∀ F, F 0 → ∀ x f g, Rnd_N0_pt F x f → Rnd_N0_pt F x g → f = g :=
  Rnd_N0_pt_unique
example : ∀ F, F 0 → ∀ x f, Rnd_N_pt F x f → |f| ≤ |x| → Rnd_N0_pt F x f :=
  Rnd_N0_pt_N
example : ∀ F, F 0 → ∀ r s, Rnd_N0 F r → Rnd_N0 F s → ∀ x, r x = s x := Rnd_N0_unique
example : ∀ F, F 0 → round_pred_monotone (Rnd_N0_pt F) := Rnd_N0_pt_monotone
example : ∀ F x, F x → Rnd_N0_pt F x x := Rnd_N0_pt_refl
example : ∀ F x f, Rnd_N0_pt F x f → F x → f = x := Rnd_N0_pt_idempotent

example : ∀ P, round_pred_monotone P → P 0 0 → ∀ x f,
    P x f → 0 ≤ x → 0 ≤ f := round_pred_ge_0
example : ∀ P, round_pred_monotone P → P 0 0 → ∀ x f,
    P x f → 0 < f → 0 < x := round_pred_gt_0
example : ∀ P, round_pred_monotone P → P 0 0 → ∀ x f,
    P x f → x ≤ 0 → f ≤ 0 := round_pred_le_0
example : ∀ P, round_pred_monotone P → P 0 0 → ∀ x f,
    P x f → f < 0 → x < 0 := round_pred_lt_0
example : ∀ F1 F2 a b, F1 a → (∀ x, a ≤ x ∧ x ≤ b → (F1 x ↔ F2 x)) →
    ∀ x f, a ≤ x ∧ x ≤ b → Rnd_DN_pt F1 x f → Rnd_DN_pt F2 x f := Rnd_DN_pt_equiv_format
example : ∀ F1 F2 a b, F1 b → (∀ x, a ≤ x ∧ x ≤ b → (F1 x ↔ F2 x)) →
    ∀ x f, a ≤ x ∧ x ≤ b → Rnd_UP_pt F1 x f → Rnd_UP_pt F2 x f := Rnd_UP_pt_equiv_format

example : ∀ F1 F2, (∀ x, F1 x ↔ F2 x) → satisfies_any F1 → satisfies_any F2 := satisfies_any_eq
example : ∀ F, satisfies_any F → round_pred (Rnd_DN_pt F) := satisfies_any_imp_DN
example : ∀ F, satisfies_any F → round_pred (Rnd_UP_pt F) := satisfies_any_imp_UP
example : ∀ F, satisfies_any F → round_pred (Rnd_ZR_pt F) := satisfies_any_imp_ZR
example (F P) : NG_existence_prop F P =
    (∀ x d u, ¬ F x → Rnd_DN_pt F x d → Rnd_UP_pt F x u → P x u ∨ P x d) := rfl
example : ∀ F P, satisfies_any F → NG_existence_prop F P →
    round_pred_total (Rnd_NG_pt F P) := satisfies_any_imp_NG
example : ∀ F, satisfies_any F → round_pred (Rnd_NA_pt F) := satisfies_any_imp_NA
example : ∀ F, F 0 → satisfies_any F → round_pred (Rnd_N0_pt F) := satisfies_any_imp_N0
example : ∀ F, F 0 → (∀ x, F x → F (-x)) → round_pred_total (Rnd_DN_pt F) →
    satisfies_any F := @satisfies_any.intro

-- The single-constructor proof can be eliminated into data, as in Rocq's rect.
def eliminate_to_data (F) (h : satisfies_any F) : Nat :=
  match h with | .intro _ _ _ => 7

-- A false policy is acceptable at exactly representable inputs: the definition
-- has a unique-nearest alternative. Requiring P at every input would be wrong.
example : Rnd_NG_pt (fun x : Real ↦ x = 0) (fun _ _ ↦ False) 0 0 :=
  Rnd_NG_pt_refl _ _ 0 rfl

-- One dependent eliminator covers Rocq's generated Prop/Set/Type schemes.
def eliminate_dependent (F) (motive : satisfies_any F → Sort u)
    (step : ∀ h0 hs ht, motive (.intro h0 hs ht)) (h : satisfies_any F) : motive h :=
  match h with | .intro h0 hs ht => step h0 hs ht

private def twoPoints (x : Real) : Prop := x = -1 ∨ x = 1

private theorem two_nearest (f : Real) (hf : twoPoints f) : Rnd_N_pt twoPoints 0 f := by
  refine ⟨hf, ?_⟩
  intro g hg
  rcases hf with rfl | rfl <;> rcases hg with rfl | rfl <;> norm_num

private theorem two_abs (f : Real) (hf : twoPoints f) : |f| = 1 := by
  rcases hf with rfl | rfl <;> norm_num

private theorem both_policies (f : Real) (hf : twoPoints f) :
    Rnd_NA_pt twoPoints 0 f ∧ Rnd_N0_pt twoPoints 0 f := by
  constructor
  · refine ⟨two_nearest f hf, ?_⟩
    intro g hg
    rw [two_abs f hf, two_abs g hg.1]
  · refine ⟨two_nearest f hf, ?_⟩
    intro g hg
    rw [two_abs f hf, two_abs g hg.1]

private theorem tie_uniqueness_needs_zero :
    (¬ ∀ x f g, Rnd_NA_pt twoPoints x f → Rnd_NA_pt twoPoints x g → f = g) ∧
    (¬ ∀ x f g, Rnd_N0_pt twoPoints x f → Rnd_N0_pt twoPoints x g → f = g) := by
  constructor
  · intro h
    have bad := h 0 (-1) 1 (both_policies (-1) (Or.inl rfl)).1
      (both_policies 1 (Or.inr rfl)).1
    norm_num at bad
  · intro h
    have bad := h 0 (-1) 1 (both_policies (-1) (Or.inl rfl)).2
      (both_policies 1 (Or.inr rfl)).2
    norm_num at bad

#print axioms tie_uniqueness_needs_zero

end RoundPredTieContracts
