import FloatSpec.src.Core.Round_pred

namespace RoundPredSourceContracts
open FloatSpec.Core.Defs (round_pred_monotone)
open FloatSpec.Core.Round_pred

-- Paired exact-typed clients: ordinary propositions, not Boolean-check contracts.
example : ∀ P, round_pred_monotone P → ∀ x f g, P x f → P x g → f = g := round_unique
example : ∀ F, round_pred_monotone (Rnd_DN_pt F) := Rnd_DN_pt_monotone
example : ∀ F x f g, Rnd_DN_pt F x f → Rnd_DN_pt F x g → f = g := Rnd_DN_pt_unique
example : ∀ F r s, Rnd_DN F r → Rnd_DN F s → ∀ x, r x = s x := Rnd_DN_unique
example : ∀ F, round_pred_monotone (Rnd_UP_pt F) := Rnd_UP_pt_monotone
example : ∀ F x f g, Rnd_UP_pt F x f → Rnd_UP_pt F x g → f = g := Rnd_UP_pt_unique
example : ∀ F r s, Rnd_UP F r → Rnd_UP F s → ∀ x, r x = s x := Rnd_UP_unique
example : ∀ F, (∀ x, F x → F (-x)) → ∀ x f,
    Rnd_DN_pt F x f → Rnd_UP_pt F (-x) (-f) := Rnd_UP_pt_opp
example : ∀ F, (∀ x, F x → F (-x)) → ∀ x f,
    Rnd_UP_pt F x f → Rnd_DN_pt F (-x) (-f) := Rnd_DN_pt_opp
example : ∀ F, (∀ x, F x → F (-x)) → ∀ r s,
    Rnd_DN F r → Rnd_UP F s → ∀ x, r (-x) = -s x := Rnd_DN_opp
example (F : Real → Prop) (x d u : Real) (hd : Rnd_DN_pt F x d)
    (hu : Rnd_UP_pt F x u) : ∀ f, F f → f ≤ d ∨ u ≤ f :=
  fun f hf ↦ Rnd_DN_UP_pt_split F x d u f hd hu hf
example : ∀ F x, F x → Rnd_DN_pt F x x := Rnd_DN_pt_refl
example : ∀ F x f, Rnd_DN_pt F x f → F x → f = x := Rnd_DN_pt_idempotent
example : ∀ F x, F x → Rnd_UP_pt F x x := Rnd_UP_pt_refl
example : ∀ F x f, Rnd_UP_pt F x f → F x → f = x := Rnd_UP_pt_idempotent
example : ∀ F x d u f, Rnd_DN_pt F x d → Rnd_UP_pt F x u → F f →
    d ≤ f ∧ f ≤ u → f = d ∨ f = u := Only_DN_or_UP
example : ∀ F r, Rnd_ZR F r → ∀ x, |r x| ≤ |x| := Rnd_ZR_abs
example : ∀ F, F 0 → round_pred_monotone (Rnd_ZR_pt F) := Rnd_ZR_pt_monotone
example : ∀ F x f, Rnd_N_pt F x f → Rnd_DN_pt F x f ∨ Rnd_UP_pt F x f :=
  Rnd_N_pt_DN_or_UP
example : ∀ F x d u f, Rnd_DN_pt F x d → Rnd_UP_pt F x u → Rnd_N_pt F x f →
    f = d ∨ f = u := Rnd_N_pt_DN_or_UP_eq
example (F : Real → Prop) (hF : ∀ x, F x → F (-x)) :
    ∀ x f, Rnd_N_pt F (-x) (-f) → Rnd_N_pt F x f :=
  fun x f h ↦ Rnd_N_pt_opp_inv F x f hF h
example : ∀ F x y f g, Rnd_N_pt F x f → Rnd_N_pt F y g → x < y → f ≤ g :=
  Rnd_N_pt_monotone
example : ∀ F x d u f g, Rnd_DN_pt F x d → Rnd_UP_pt F x u → x - d ≠ u - x →
    Rnd_N_pt F x f → Rnd_N_pt F x g → f = g := Rnd_N_pt_unique
example : ∀ F x, F x → Rnd_N_pt F x x := Rnd_N_pt_refl
example : ∀ F x f, Rnd_N_pt F x f → F x → f = x := Rnd_N_pt_idempotent

-- The finite format deliberately lacks zero. Neither endpoint is a unique
-- nearest value at zero, and truncation jumps backwards across zero.
private def twoPoints (x : Real) : Prop := x = -1 ∨ x = 1

private theorem tie_left : Rnd_N_pt twoPoints 0 (-1) := by
  refine ⟨Or.inl rfl, ?_⟩
  intro g hg
  rcases hg with rfl | rfl <;> norm_num

private theorem tie_right : Rnd_N_pt twoPoints 0 1 := by
  refine ⟨Or.inr rfl, ?_⟩
  intro g hg
  rcases hg with rfl | rfl <;> norm_num

private theorem nearest_is_not_nonstrict_monotone :
    ¬ round_pred_monotone (Rnd_N_pt twoPoints) := by
  intro h
  have bound := h 0 0 1 (-1) tie_right tie_left le_rfl
  norm_num at bound

private theorem nearest_is_not_unconditionally_unique :
    ¬ ∀ F x f g, Rnd_N_pt F x f → Rnd_N_pt F x g → f = g := by
  intro h
  have heq := h twoPoints 0 (-1) 1 tie_left tie_right
  norm_num at heq

private theorem zr_negative : Rnd_ZR_pt twoPoints (-(1/2)) 1 := by
  refine ⟨fun h ↦ by norm_num at h, fun _ ↦ ⟨Or.inr rfl, by norm_num, ?_⟩⟩
  intro g hg hle
  rcases hg with rfl | rfl <;> norm_num at *

private theorem zr_positive : Rnd_ZR_pt twoPoints (1/2) (-1) := by
  refine ⟨fun _ ↦ ⟨Or.inl rfl, by norm_num, ?_⟩, fun h ↦ by norm_num at h⟩
  intro g hg hle
  rcases hg with rfl | rfl <;> norm_num at *

private theorem zero_membership_is_necessary :
    ¬ round_pred_monotone (Rnd_ZR_pt twoPoints) := by
  intro h
  have bound := h (-(1/2)) (1/2) 1 (-1) zr_negative zr_positive (by norm_num)
  norm_num at bound

#print axioms nearest_is_not_nonstrict_monotone
#print axioms nearest_is_not_unconditionally_unique
#print axioms zero_membership_is_necessary

end RoundPredSourceContracts
