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

import FloatSpec.src.Core.Raux
import FloatSpec.src.Core.Defs
-- import Mathlib.Data.Real.Basic
import FloatSpec.src.Core.Generic_fmt

open Real
open FloatSpec.Core.Defs

namespace FloatSpec.Core.Round_pred


-- variable {beta : Int}

-- Re-export pointwise rounding predicates under this namespace for downstream files.
abbrev Rnd_DN_pt := FloatSpec.Core.Defs.Rnd_DN_pt
abbrev Rnd_UP_pt := FloatSpec.Core.Defs.Rnd_UP_pt
abbrev Rnd_N_pt  := FloatSpec.Core.Defs.Rnd_N_pt
abbrev Rnd_NG_pt := FloatSpec.Core.Defs.Rnd_NG_pt
abbrev Rnd_NA_pt := FloatSpec.Core.Defs.Rnd_NA_pt
abbrev Rnd_N0_pt := FloatSpec.Core.Defs.Rnd_N0_pt
abbrev Rnd_ZR_pt := FloatSpec.Core.Defs.Rnd_ZR_pt

section RoundingFunctionProperties

/-- Rounding down property for functions

    A rounding function rnd satisfies `Rnd_DN` if for every input x,
    rnd(x) is the round down value according to format F.
    This lifts the pointwise property to functions.
-/
@[flocq_source "src/Core/Round_pred.v" 30 "Rnd_DN"]
def Rnd_DN (F : ℝ → Prop) (rnd : ℝ → ℝ) : Prop :=
  (∀ x : ℝ, Rnd_DN_pt F x (rnd x))

/-- Unfolding equation for {name}`Rnd_DN`: a function rounds down exactly when it does
    so at every input. Lean-local; Flocq uses the definition directly. -/
theorem Rnd_DN_spec (F : ℝ → Prop) (rnd : ℝ → ℝ) :
    Rnd_DN F rnd = ∀ x : ℝ, Rnd_DN_pt F x (rnd x) := rfl

/-- Rounding up property for functions

    A rounding function rnd satisfies `Rnd_UP` if for every input x,
    rnd(x) is the round up value according to format F.
    This provides the functional counterpart to round-up.
-/
@[flocq_source "src/Core/Round_pred.v" 33 "Rnd_UP"]
def Rnd_UP (F : ℝ → Prop) (rnd : ℝ → ℝ) : Prop :=
  (∀ x : ℝ, Rnd_UP_pt F x (rnd x))

/-- Unfolding equation for {name}`Rnd_UP`: a function rounds up exactly when it does so
    at every input. Lean-local; Flocq uses the definition directly. -/
theorem Rnd_UP_spec (F : ℝ → Prop) (rnd : ℝ → ℝ) :
    Rnd_UP F rnd = ∀ x : ℝ, Rnd_UP_pt F x (rnd x) := rfl

/-- Rounding toward zero property for functions

    A function satisfies `Rnd_ZR` if it implements truncation:
    round toward zero for all inputs. This combines round-down
    for positive values and round up for negative values.
-/
@[flocq_source "src/Core/Round_pred.v" 36 "Rnd_ZR"]
def Rnd_ZR (F : ℝ → Prop) (rnd : ℝ → ℝ) : Prop :=
  -- Use the Coq-accurate predicate from Defs to ensure both directions (x ≥ 0 and x ≤ 0)
  (∀ x : ℝ, FloatSpec.Core.Defs.Rnd_ZR_pt F x (rnd x))

/-- Unfolding equation for {name}`Rnd_ZR`: a function rounds toward zero exactly when it
    does so at every input. Lean-local; Flocq uses the definition directly. -/
theorem Rnd_ZR_spec (F : ℝ → Prop) (rnd : ℝ → ℝ) :
    Rnd_ZR F rnd = ∀ x : ℝ, FloatSpec.Core.Defs.Rnd_ZR_pt F x (rnd x) := rfl

/-- Round to nearest property for functions

    A function satisfies `Rnd_N` when it selects a nearest
    representable value. This is the base property for all
    `round-to-nearest` modes without specifying tie breaking.
-/
@[flocq_source "src/Core/Round_pred.v" 39 "Rnd_N"]
def Rnd_N (F : ℝ → Prop) (rnd : ℝ → ℝ) : Prop :=
  (∀ x : ℝ, Rnd_N_pt F x (rnd x))

/-- Unfolding equation for {name}`Rnd_N`: a function rounds to nearest exactly when it
    does so at every input. Lean-local; Flocq uses the definition directly. -/
theorem Rnd_N_spec (F : ℝ → Prop) (rnd : ℝ → ℝ) :
    Rnd_N F rnd = ∀ x : ℝ, Rnd_N_pt F x (rnd x) := rfl

/-- Generic rounding property with tie-breaking predicate

    A function satisfies `Rnd_NG` with predicate P if it rounds
    to nearest and uses P to break ties. This generalizes
    all `round-to-nearest` variants with different tie policies.
-/
@[flocq_source "src/Core/Round_pred.v" 42 "Rnd_NG"]
def Rnd_NG (F : ℝ → Prop) (P : ℝ → ℝ → Prop) (rnd : ℝ → ℝ) : Prop :=
  (∀ x : ℝ, Rnd_NG_pt F P x (rnd x))

/-- Unfolding equation for {name}`Rnd_NG`: a function rounds to nearest under the tie
    policy `P` exactly when it does so at every input. Lean-local; Flocq uses the
    definition directly. -/
theorem Rnd_NG_spec (F : ℝ → Prop) (P : ℝ → ℝ → Prop) (rnd : ℝ → ℝ) :
    Rnd_NG F P rnd = ∀ x : ℝ, Rnd_NG_pt F P x (rnd x) := rfl

/-- Round ties away from zero property

    A function satisfies `Rnd_NA` if it rounds to nearest,
    breaking ties by choosing the value farther from zero.
    This implements IEEE 754's "away from zero" tie breaking.
-/
@[flocq_source "src/Core/Round_pred.v" 45 "Rnd_NA"]
def Rnd_NA (F : ℝ → Prop) (rnd : ℝ → ℝ) : Prop :=
  (∀ x : ℝ, Rnd_NA_pt F x (rnd x))

/-- Unfolding equation for {name}`Rnd_NA`: a function rounds to nearest with ties away
    from zero exactly when it does so at every input. Lean-local; Flocq uses the
    definition directly. -/
theorem Rnd_NA_spec (F : ℝ → Prop) (rnd : ℝ → ℝ) :
    Rnd_NA F rnd = ∀ x : ℝ, Rnd_NA_pt F x (rnd x) := rfl

/-- Round ties toward zero property

    A function satisfies `Rnd_N0` if it rounds to nearest,
    breaking ties by choosing the value closer to zero.
    This provides an alternative tie breaking strategy.
-/
@[flocq_source "src/Core/Round_pred.v" 48 "Rnd_N0"]
def Rnd_N0 (F : ℝ → Prop) (rnd : ℝ → ℝ) : Prop :=
  (∀ x : ℝ, Rnd_N0_pt F x (rnd x))

/-- Unfolding equation for {name}`Rnd_N0`: a function rounds to nearest with ties toward
    zero exactly when it does so at every input. Lean-local; Flocq uses the definition
    directly. -/
theorem Rnd_N0_spec (F : ℝ → Prop) (rnd : ℝ → ℝ) :
    Rnd_N0 F rnd = ∀ x : ℝ, Rnd_N0_pt F x (rnd x) := rfl

end RoundingFunctionProperties

section SourceDirectedRounding

/-- A monotone rounding relation has at most one result at each input. -/
@[flocq_source "src/Core/Round_pred.v" 89 "round_unique"]
theorem round_unique (rnd : ℝ → ℝ → Prop) (h : round_pred_monotone rnd)
    (x f1 f2 : ℝ) (h1 : rnd x f1) (h2 : rnd x f2) : f1 = f2 :=
  le_antisymm (h x x f1 f2 h1 h2 le_rfl) (h x x f2 f1 h2 h1 le_rfl)

set_option doc.verso true in
/--
Rounding down is monotone for every format: Flocq's {coq}`Rnd_DN_pt_monotone`.

```coq Rnd_DN_pt_monotone
Theorem Rnd_DN_pt_monotone :
  forall F : R -> Prop,
  round_pred_monotone (Rnd_DN_pt F).
```
-/
@[flocq_source "src/Core/Round_pred.v" 103 "Rnd_DN_pt_monotone"]
theorem Rnd_DN_pt_monotone (F : ℝ → Prop) : round_pred_monotone (Rnd_DN_pt F) :=
  fun _ _ _ _ hf hg hxy ↦ hg.2.2 _ hf.1 (le_trans hf.2.1 hxy)

/-- A downward rounding point is unique. -/
@[flocq_source "src/Core/Round_pred.v" 113 "Rnd_DN_pt_unique"]
theorem Rnd_DN_pt_unique (F : ℝ → Prop) (x f1 f2 : ℝ)
    (h1 : Rnd_DN_pt F x f1) (h2 : Rnd_DN_pt F x f2) : f1 = f2 :=
  round_unique _ (Rnd_DN_pt_monotone F) x f1 f2 h1 h2

/-- Two downward rounding functions agree at every input. -/
@[flocq_source "src/Core/Round_pred.v" 124 "Rnd_DN_unique"]
theorem Rnd_DN_unique (F : ℝ → Prop) (rnd1 rnd2 : ℝ → ℝ)
    (h1 : Rnd_DN F rnd1) (h2 : Rnd_DN F rnd2) (x : ℝ) : rnd1 x = rnd2 x :=
  Rnd_DN_pt_unique F x _ _ (h1 x) (h2 x)

/-- Rounding up is monotone for every format. -/
@[flocq_source "src/Core/Round_pred.v" 134 "Rnd_UP_pt_monotone"]
theorem Rnd_UP_pt_monotone (F : ℝ → Prop) : round_pred_monotone (Rnd_UP_pt F) :=
  fun _ _ _ _ hf hg hxy ↦ hf.2.2 _ hg.1 (le_trans hxy hg.2.1)

/-- An upward rounding point is unique. -/
@[flocq_source "src/Core/Round_pred.v" 144 "Rnd_UP_pt_unique"]
theorem Rnd_UP_pt_unique (F : ℝ → Prop) (x f1 f2 : ℝ)
    (h1 : Rnd_UP_pt F x f1) (h2 : Rnd_UP_pt F x f2) : f1 = f2 :=
  round_unique _ (Rnd_UP_pt_monotone F) x f1 f2 h1 h2

/-- Two upward rounding functions agree at every input. -/
@[flocq_source "src/Core/Round_pred.v" 155 "Rnd_UP_unique"]
theorem Rnd_UP_unique (F : ℝ → Prop) (rnd1 rnd2 : ℝ → ℝ)
    (h1 : Rnd_UP F rnd1) (h2 : Rnd_UP F rnd2) (x : ℝ) : rnd1 x = rnd2 x :=
  Rnd_UP_pt_unique F x _ _ (h1 x) (h2 x)

/-- Negation turns downward rounding into upward rounding in a symmetric format. -/
@[flocq_source "src/Core/Round_pred.v" 165 "Rnd_UP_pt_opp"]
theorem Rnd_UP_pt_opp (F : ℝ → Prop) (hF : ∀ x, F x → F (-x))
    (x f : ℝ) (h : Rnd_DN_pt F x f) : Rnd_UP_pt F (-x) (-f) := by
  refine ⟨hF f h.1, neg_le_neg h.2.1, ?_⟩
  intro g hg hxg
  have bound := h.2.2 (-g) (hF g hg) (by linarith)
  linarith

/-- Negation turns upward rounding into downward rounding in a symmetric format. -/
@[flocq_source "src/Core/Round_pred.v" 186 "Rnd_DN_pt_opp"]
theorem Rnd_DN_pt_opp (F : ℝ → Prop) (hF : ∀ x, F x → F (-x))
    (x f : ℝ) (h : Rnd_UP_pt F x f) : Rnd_DN_pt F (-x) (-f) := by
  refine ⟨hF f h.1, neg_le_neg h.2.1, ?_⟩
  intro g hg hgx
  have bound := h.2.2 (-g) (hF g hg) (by linarith)
  linarith

/-- Downward rounding of a negation is the negated upward rounding. -/
@[flocq_source "src/Core/Round_pred.v" 207 "Rnd_DN_opp"]
theorem Rnd_DN_opp (F : ℝ → Prop) (hF : ∀ x, F x → F (-x))
    (rnd1 rnd2 : ℝ → ℝ) (h1 : Rnd_DN F rnd1) (h2 : Rnd_UP F rnd2)
    (x : ℝ) : rnd1 (-x) = -rnd2 x :=
  Rnd_DN_pt_unique F (-x) _ _ (h1 (-x)) (Rnd_DN_pt_opp F hF x _ (h2 x))

/-- A representable value rounds downward to itself. -/
@[flocq_source "src/Core/Round_pred.v" 242 "Rnd_DN_pt_refl"]
theorem Rnd_DN_pt_refl (F : ℝ → Prop) (x : ℝ) (hx : F x) : Rnd_DN_pt F x x :=
  ⟨hx, le_rfl, fun _ _ h ↦ h⟩

/-- Downward rounding fixes each representable input. -/
@[flocq_source "src/Core/Round_pred.v" 254 "Rnd_DN_pt_idempotent"]
theorem Rnd_DN_pt_idempotent (F : ℝ → Prop) (x f : ℝ)
    (h : Rnd_DN_pt F x f) (hx : F x) : f = x :=
  Rnd_DN_pt_unique F x f x h (Rnd_DN_pt_refl F x hx)

/-- A representable value rounds upward to itself. -/
@[flocq_source "src/Core/Round_pred.v" 268 "Rnd_UP_pt_refl"]
theorem Rnd_UP_pt_refl (F : ℝ → Prop) (x : ℝ) (hx : F x) : Rnd_UP_pt F x x :=
  ⟨hx, le_rfl, fun _ _ h ↦ h⟩

/-- Upward rounding fixes each representable input. -/
@[flocq_source "src/Core/Round_pred.v" 280 "Rnd_UP_pt_idempotent"]
theorem Rnd_UP_pt_idempotent (F : ℝ → Prop) (x f : ℝ)
    (h : Rnd_UP_pt F x f) (hx : F x) : f = x :=
  Rnd_UP_pt_unique F x f x h (Rnd_UP_pt_refl F x hx)

/-- A total toward-zero rounding function never increases absolute value. -/
@[flocq_source "src/Core/Round_pred.v" 310 "Rnd_ZR_abs"]
theorem Rnd_ZR_abs (F : ℝ → Prop) (rnd : ℝ → ℝ) (h : Rnd_ZR F rnd)
    (x : ℝ) : |rnd x| ≤ |x| := by
  have hd := (h 0).1 le_rfl
  have hu := (h 0).2 le_rfl
  have hz : rnd 0 = 0 := le_antisymm hd.2.1 hu.2.1
  have hF0 : F 0 := hz ▸ hd.1
  rcases le_total 0 x with hx | hx
  · have hp := (h x).1 hx
    simpa [abs_of_nonneg hx, abs_of_nonneg (hp.2.2 0 hF0 hx)] using hp.2.1
  · have hp := (h x).2 hx
    simpa [abs_of_nonpos hx, abs_of_nonpos (hp.2.2 0 hF0 hx)] using neg_le_neg hp.2.1

/-- Toward-zero rounding is monotone when zero belongs to the format. -/
@[flocq_source "src/Core/Round_pred.v" 342 "Rnd_ZR_pt_monotone"]
theorem Rnd_ZR_pt_monotone (F : ℝ → Prop) (hF0 : F 0) :
    round_pred_monotone (Rnd_ZR_pt F) := by
  intro x y f g hx hy hxy
  rcases le_total 0 x with hx0 | hx0
  · exact Rnd_DN_pt_monotone F x y f g (hx.1 hx0) (hy.1 (le_trans hx0 hxy)) hxy
  · rcases le_total y 0 with hy0 | hy0
    · exact Rnd_UP_pt_monotone F x y f g (hx.2 hx0) (hy.2 hy0) hxy
    · exact le_trans ((hx.2 hx0).2.2 0 hF0 hx0) ((hy.1 hy0).2.2 0 hF0 hy0)

end SourceDirectedRounding

section ExistenceAndUniqueness

/-- Choose a rounded value with its witness, as in Flocq's dependent result.
The input proof supplies totality; no default value is introduced for an
unsatisfied relation. Classical choice makes this mathematical constructor
noncomputable, unlike the integer algorithms in the executable IEEE layer. -/
@[flocq_source "src/Core/Round_pred.v" 51 "round_val_of_pred"]
noncomputable def round_val_of_pred (rnd : ℝ → ℝ → Prop)
    (h : round_pred rnd) (x : ℝ) : {f : ℝ // rnd x f} :=
  ⟨Classical.choose (h.1 x), Classical.choose_spec (h.1 x)⟩

/-- The predicate proof carried by the source-shaped value constructor. -/
@[flocq_local "Lean projection of the proof carried by round_val_of_pred; no separate Flocq declaration"]
theorem round_val_of_pred_spec (rnd : ℝ → ℝ → Prop)
    (h : round_pred rnd) (x : ℝ) : rnd x (round_val_of_pred rnd h x).val :=
  (round_val_of_pred rnd h x).property

/-- Choose a rounding function together with its pointwise predicate proof. -/
@[flocq_source "src/Core/Round_pred.v" 78 "round_fun_of_pred"]
noncomputable def round_fun_of_pred (rnd : ℝ → ℝ → Prop)
    (h : round_pred rnd) : {f : ℝ → ℝ // ∀ x, rnd x (f x)} :=
  ⟨fun x => (round_val_of_pred rnd h x).val,
    fun x => (round_val_of_pred rnd h x).property⟩

/-- The pointwise proof carried by the source-shaped function constructor. -/
@[flocq_local "Lean projection of the proof carried by round_fun_of_pred; no separate Flocq declaration"]
theorem round_fun_of_pred_spec (rnd : ℝ → ℝ → Prop)
    (h : round_pred rnd) : ∀ x, rnd x ((round_fun_of_pred rnd h).val x) :=
  (round_fun_of_pred rnd h).property

end ExistenceAndUniqueness

section RoundUpProperties

/-- Pure version: Round up point is unique -/
lemma Rnd_UP_pt_unique_pure (F : ℝ → Prop) (x f1 f2 : ℝ)
    (hf1 : Rnd_UP_pt F x f1) (hf2 : Rnd_UP_pt F x f2) : f1 = f2 := by
  rcases hf1 with ⟨Ff1, hxle_f1, hmin1⟩
  rcases hf2 with ⟨Ff2, hxle_f2, hmin2⟩
  apply le_antisymm
  · exact hmin1 f2 Ff2 hxle_f2
  · exact hmin2 f1 Ff1 hxle_f1

end RoundUpProperties

section DualityProperties

/-- Pure version: From DN-point at x, get UP-point at -x via negation -/
lemma Rnd_UP_pt_opp_pure (F : ℝ → Prop) (x f : ℝ)
    (hFopp : ∀ y, F y → F (-y)) (hDN : Rnd_DN_pt F x f) :
    Rnd_UP_pt F (-x) (-f) := by
  rcases hDN with ⟨Hf, Hfx, Hmax⟩
  refine And.intro (hFopp _ Hf) ?_
  refine And.intro (by simpa using (neg_le_neg Hfx)) ?_
  intro g HgF Hlexg
  have Hg_le_x : -g ≤ x := by
    have := neg_le_neg Hlexg
    simpa [neg_neg] using this
  have Hneg_g : F (-g) := hFopp _ HgF
  have H_le_f : -g ≤ f := Hmax (-g) Hneg_g Hg_le_x
  have := neg_le_neg H_le_f
  simpa [neg_neg] using this

/-- Coq-compatible name: DN/UP split covers all representables -/
@[flocq_source "src/Core/Round_pred.v" 225 "Rnd_DN_UP_pt_split"]
theorem Rnd_DN_UP_pt_split (F : ℝ → Prop) (x d u f : ℝ)
    (hDN : Rnd_DN_pt F x d) (hUP : Rnd_UP_pt F x u) (hFf : F f) :
    f ≤ d ∨ u ≤ f := by
  rcases le_total f x with hf | hf
  · exact Or.inl (hDN.2.2 f hFf hf)
  · exact Or.inr (hUP.2.2 f hFf hf)

/-- Coq-compatible name: only DN or UP when bounded between them -/
@[flocq_source "src/Core/Round_pred.v" 294 "Only_DN_or_UP"]
theorem Only_DN_or_UP (F : ℝ → Prop) (x fd fu f : ℝ)
    (hDN : Rnd_DN_pt F x fd) (hUP : Rnd_UP_pt F x fu) (hFf : F f)
    (hbounds : fd ≤ f ∧ f ≤ fu) : f = fd ∨ f = fu := by
  rcases Rnd_DN_UP_pt_split F x fd fu f hDN hUP hFf with hd | hu
  · exact Or.inl (le_antisymm hd hbounds.1)
  · exact Or.inr (le_antisymm hbounds.2 hu)

end DualityProperties

section RoundNearestBasic

/-- Coq-compatible name: nearest point is DN or UP -/
@[flocq_source "src/Core/Round_pred.v" 368 "Rnd_N_pt_DN_or_UP"]
theorem Rnd_N_pt_DN_or_UP (F : ℝ → Prop) (x f : ℝ) (hN : Rnd_N_pt F x f) :
    Rnd_DN_pt F x f ∨ Rnd_UP_pt F x f := by
  rcases hN with ⟨HfF, Hmin⟩
  cases le_total f x with
  | inl hfxle =>
      left
      refine And.intro HfF ?_
      refine And.intro hfxle ?_
      intro g HgF hglex
      have hxmf_nonneg : 0 ≤ x - f := sub_nonneg.mpr hfxle
      have hxmg_nonneg : 0 ≤ x - g := sub_nonneg.mpr hglex
      have h_abs : |x - f| ≤ |x - g| := by
        simpa [abs_sub_comm] using (Hmin g HgF)
      have h_sub : x - f ≤ x - g := by
        simpa [abs_of_nonneg hxmf_nonneg, abs_of_nonneg hxmg_nonneg] using h_abs
      have hneg : -f ≤ -g := by
        have h' := add_le_add_left h_sub (-x)
        simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h'
      exact (neg_le_neg_iff).1 hneg
  | inr hxlef =>
      right
      refine And.intro HfF ?_
      refine And.intro hxlef ?_
      intro g HgF hxleg
      have hxmf_nonpos : x - f ≤ 0 := sub_nonpos.mpr hxlef
      have hxmg_nonpos : x - g ≤ 0 := sub_nonpos.mpr hxleg
      have h_abs : |x - f| ≤ |x - g| := by
        simpa [abs_sub_comm] using (Hmin g HgF)
      have h_sub : f - x ≤ g - x := by
        simpa [abs_of_nonpos hxmf_nonpos, abs_of_nonpos hxmg_nonpos, neg_sub] using h_abs
      have h' := add_le_add_right h_sub x
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h'

/-- Coq-compatible name: nearest equals DN or UP -/
@[flocq_source "src/Core/Round_pred.v" 400 "Rnd_N_pt_DN_or_UP_eq"]
theorem Rnd_N_pt_DN_or_UP_eq (F : ℝ → Prop) (x d u f : ℝ)
    (Hd : Rnd_DN_pt F x d) (Hu : Rnd_UP_pt F x u) (Hn : Rnd_N_pt F x f) :
    f = d ∨ f = u := by
  rcases Rnd_N_pt_DN_or_UP F x f Hn with hd | hu
  · exact Or.inl (Rnd_DN_pt_unique F x f d hd Hd)
  · exact Or.inr (Rnd_UP_pt_unique F x f u hu Hu)

end RoundNearestBasic

section RoundNearestAdvanced

/-- Coq-compatible name: nearest invariant under negation -/
@[flocq_source "src/Core/Round_pred.v" 415 "Rnd_N_pt_opp_inv"]
theorem Rnd_N_pt_opp_inv (F : ℝ → Prop) (x f : ℝ)
    (hFopp : ∀ y, F y → F (-y)) (hNearestNeg : Rnd_N_pt F (-x) (-f)) :
    Rnd_N_pt F x f := by
  rcases hNearestNeg with ⟨Hf_neg, Hmin_neg⟩
  -- Show `F f` using closure under negation from `F (-f)`.
  have Hf : F f := by
    simpa [neg_neg] using hFopp (-f) Hf_neg
  -- Show minimality at `x` from minimality at `-x` by rewriting via negations.
  refine And.intro Hf ?_
  intro g HgF
  have Hg_neg : F (-g) := hFopp g HgF
  have hneg := Hmin_neg (-g) Hg_neg
  have h1 : |x - f| ≤ |x - g| := by
    simpa [sub_eq_add_neg, add_comm] using hneg
  have h2 : |f - x| ≤ |g - x| := by
    simpa [abs_sub_comm] using h1
  exact h2

/-- Nearest rounding preserves strictly ordered inputs, even without a tie rule. -/
@[flocq_source "src/Core/Round_pred.v" 435 "Rnd_N_pt_monotone"]
theorem Rnd_N_pt_monotone (F : ℝ → Prop) (x y f g : ℝ)
    (hf : Rnd_N_pt F x f) (hg : Rnd_N_pt F y g) (hxy : x < y) : f ≤ g := by
  rcases hf with ⟨HfF, Hxmin⟩
  rcases hg with ⟨HgF, Hymin⟩
  -- By contradiction, assume `g < f`.
  by_contra hle
  have hgf : g < f := lt_of_not_ge hle
  -- From minimality at x and y (in the definition order |f - x| ≤ |g - x|)
  have Hfgx : |f - x| ≤ |g - x| := Hxmin g HgF
  have Hgfy : |g - y| ≤ |f - y| := Hymin f HfF
  -- Split on the order between x and g
  by_cases hxg : x ≤ g
  · -- Case 1: x ≤ g < f. Then |x - f| = f - x and |x - g| = g - x, contradicting g < f.
    have hxlt_f : x < f := lt_of_le_of_lt hxg hgf
    have hxmf_pos : 0 < f - x := sub_pos.mpr hxlt_f
    have hxmg_nonneg : 0 ≤ g - x := sub_nonneg.mpr hxg
    have Hfgx' : |f - x| ≤ |g - x| := by simpa [abs_sub_comm] using Hfgx
    have Hfgx'' : f - x ≤ g - x := by
      simpa [abs_of_nonneg (le_of_lt hxmf_pos), abs_of_nonneg hxmg_nonneg] using Hfgx'
    have : ¬ f - x ≤ g - x := by
      have h := sub_lt_sub_right hgf x
      exact not_le.mpr h
    exact this Hfgx''
  · -- Case 2: g < x. Then g < y by transitivity with x < y.
    have hgx : g < x := lt_of_not_ge hxg
    have hgy : g < y := lt_trans hgx hxy
    -- Subcase 2a: f ≤ y. Then |y - g| = y - g and |y - f| = y - f, contradicting g < f.
    by_cases hfy : f ≤ y
    · have hy_mg_pos : 0 < y - g := sub_pos.mpr hgy
      have hy_mf_nonneg : 0 ≤ y - f := sub_nonneg.mpr hfy
      have Hgfy' : |y - g| ≤ |y - f| := by
        simpa [abs_sub_comm] using Hgfy
      have Hgfy'' : y - g ≤ y - f := by
        simpa [abs_of_nonneg (le_of_lt hy_mg_pos), abs_of_nonneg hy_mf_nonneg] using Hgfy'
      have : ¬ y - g ≤ y - f := by
        have h := sub_lt_sub_left hgf y
        -- From g < f, we have y - f < y - g, contradicting the above ≤
        exact not_le.mpr h
      exact this Hgfy''
    · -- Subcase 2b: y < f. Use both minimalities and a rearrangement argument.
      have hy_lt_f : y < f := lt_of_not_ge hfy
      -- Rewrite Hfgx and Hgfy without absolutes using sign information.
      have hxmg_pos : 0 < x - g := sub_pos.mpr hgx
      -- From x < y < f, we get 0 < f - x
      have hxmf_pos : 0 < f - x := sub_pos.mpr (lt_trans hxy hy_lt_f)
      have hymg_pos : 0 < y - g := sub_pos.mpr hgy
      have hymf_neg : y - f < 0 := sub_neg.mpr hy_lt_f
      -- |x - f| = f - x and |x - g| = x - g
      have Hfgx' : f - x ≤ x - g := by
        have := Hfgx
        have : |f - x| ≤ |x - g| := by simpa [abs_sub_comm] using this
        simpa [abs_of_pos hxmf_pos, abs_of_pos hxmg_pos] using this
      -- |y - g| = y - g and |y - f| = f - y
      have Hgfy' : y - g ≤ f - y := by
        have habs : |y - g| ≤ |y - f| := by
          simpa [abs_sub_comm] using Hgfy
        simpa [abs_of_pos hymg_pos, abs_of_neg hymf_neg] using habs
      -- Sum inequalities: (f - x) + (y - g) ≤ (x - g) + (f - y)
      have Hsum : (f - x) + (y - g) ≤ (x - g) + (f - y) := add_le_add Hfgx' Hgfy'
      -- But (x - g) + (f - y) = (x - y) + (f - g)
      have hL : (x - g) + (f - y) = (x - y) + (f - g) := by
        simp [sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
      -- and (f - x) + (y - g) = (y - x) + (f - g)
      have hR : (f - x) + (y - g) = (y - x) + (f - g) := by
        simp [sub_eq_add_neg, add_left_comm, add_assoc]
      -- Since y - x > 0, we have (x - y) < (y - x), hence L < R after adding (f - g)
      have hyx_pos : 0 < y - x := sub_pos.mpr hxy
      have hxmy_lt_hyx : (x - y) < (y - x) := by
        -- Since 0 < y - x, we have -(y - x) < (y - x); note x - y = -(y - x).
        have : -(y - x) < (y - x) := neg_lt_self hyx_pos
        simpa [neg_sub, sub_eq_add_neg] using this
      have hStrict : (x - y) + (f - g) < (y - x) + (f - g) := by
        simpa only [add_comm (f - g)] using add_lt_add_right hxmy_lt_hyx (f - g)
      -- Combine with Hsum rewritten via hL and hR to reach a contradiction
      have : (y - x) + (f - g) ≤ (x - y) + (f - g) := by
        simpa [hL, hR, add_comm, add_left_comm, add_assoc] using Hsum
      exact (not_le_of_gt hStrict) this

/-- Nearest rounding is unique away from a midpoint between the directed endpoints. -/
@[flocq_source "src/Core/Round_pred.v" 485 "Rnd_N_pt_unique"]
theorem Rnd_N_pt_unique (F : ℝ → Prop) (x d u f1 f2 : ℝ)
    (hd : Rnd_DN_pt F x d) (hu : Rnd_UP_pt F x u) (hne : x - d ≠ u - x)
    (h1 : Rnd_N_pt F x f1) (h2 : Rnd_N_pt F x f2) : f1 = f2 := by
  -- Each nearest point is one of the two directed endpoints.
  have hc1 : f1 = d ∨ f1 = u := Rnd_N_pt_DN_or_UP_eq F x d u f1 hd hu h1
  have hc2 : f2 = d ∨ f2 = u := Rnd_N_pt_DN_or_UP_eq F x d u f2 hd hu h2
  -- Analyze the four cases.
  cases hc1 with
  | inl h1d =>
      cases hc2 with
      | inl h2d => simpa [h1d, h2d]
      | inr h2u =>
          -- f1 = d and f2 = u implies equal distances, contradicting hne
          have : x - d = u - x := by
            rcases h1 with ⟨_, Hmin1⟩
            rcases h2 with ⟨_, Hmin2⟩
            have h_le₁ : |x - d| ≤ |x - u| := by
              have := Hmin1 u hu.1
              simpa [h1d, abs_sub_comm] using this
            have h_le₂ : |x - u| ≤ |x - d| := by
              have := Hmin2 d hd.1
              simpa [h2u, abs_sub_comm] using this
            have h_eq : |x - d| = |x - u| := le_antisymm h_le₁ h_le₂
            -- Rewrite both sides of h_eq using sign information
            have hxmd_nonneg : 0 ≤ x - d := sub_nonneg.mpr hd.2.1
            have hxmu_nonpos : x - u ≤ 0 := sub_nonpos.mpr hu.2.1
            have h_eq' : x - d = |x - u| := by
              simpa [abs_of_nonneg hxmd_nonneg] using h_eq
            have h_absu : |x - u| = u - x := by
              simpa [abs_of_nonpos hxmu_nonpos, neg_sub, sub_eq_add_neg]
                using (abs_of_nonpos hxmu_nonpos)
            simpa [h_absu] using h_eq'
          exact (hne this).elim
  | inr h1u =>
      cases hc2 with
      | inl h2d =>
          have : x - d = u - x := by
            rcases h1 with ⟨_, Hmin1⟩
            rcases h2 with ⟨_, Hmin2⟩
            have h_le₁ : |x - u| ≤ |x - d| := by
              have := Hmin1 d hd.1
              simpa [h1u, abs_sub_comm] using this
            have h_le₂ : |x - d| ≤ |x - u| := by
              have := Hmin2 u hu.1
              simpa [h2d, abs_sub_comm] using this
            have h_eq : |x - d| = |x - u| := le_antisymm h_le₂ h_le₁
            -- Rewrite using sign information to obtain a linear equality
            have hxmd_nonneg : 0 ≤ x - d := sub_nonneg.mpr hd.2.1
            have hxmu_nonpos : x - u ≤ 0 := sub_nonpos.mpr hu.2.1
            have h_eq' : x - d = |x - u| := by
              simpa [abs_of_nonneg hxmd_nonneg] using h_eq
            have h_absu : |x - u| = u - x := by
              simpa [abs_of_nonpos hxmu_nonpos, neg_sub, sub_eq_add_neg]
                using (abs_of_nonpos hxmu_nonpos)
            simpa [h_absu] using h_eq'
          exact (hne this).elim
      | inr h2u => simpa [h1u, h2u]

/-- A representable value is nearest to itself. -/
@[flocq_source "src/Core/Round_pred.v" 525 "Rnd_N_pt_refl"]
theorem Rnd_N_pt_refl (F : ℝ → Prop) (x : ℝ) (hx : F x) : Rnd_N_pt F x x := by
  refine ⟨hx, fun g _ ↦ ?_⟩
  simpa using abs_nonneg (g - x)

/-- Nearest rounding fixes every representable input, regardless of tie policy. -/
@[flocq_source "src/Core/Round_pred.v" 539 "Rnd_N_pt_idempotent"]
theorem Rnd_N_pt_idempotent (F : ℝ → Prop) (x f : ℝ)
    (h : Rnd_N_pt F x f) (hx : F x) : f = x := by
  have bound : |f - x| ≤ 0 := by simpa using h.2 x hx
  exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm bound (abs_nonneg _)))

end RoundNearestAdvanced

section RoundNearestAuxiliary

/-- Zero is its own nearest value whenever it is representable. -/
@[flocq_source "src/Core/Round_pred.v" 559 "Rnd_N_pt_0"]
theorem Rnd_N_pt_0 (F : ℝ → Prop) (hF0 : F 0) : Rnd_N_pt F 0 0 :=
  Rnd_N_pt_refl F 0 hF0

/-- Nearest rounding preserves nonnegativity in a format containing zero. -/
@[flocq_source "src/Core/Round_pred.v" 572 "Rnd_N_pt_ge_0"]
theorem Rnd_N_pt_ge_0 (F : ℝ → Prop) (hF0 : F 0) (x f : ℝ)
    (hx : 0 ≤ x) (hf : Rnd_N_pt F x f) : 0 ≤ f := by
  -- From nearest minimality, using g = 0 (since F 0), we get |x - f| ≤ |x - 0| = x.
  have hmin0 : |x - f| ≤ x := by
    have := hf.2 0 hF0
    -- Rewrite |f - x| ≤ |0 - x| as |x - f| ≤ |x - 0| = x.
    simpa [abs_sub_comm, sub_zero, abs_of_nonneg hx] using this
  -- Prove by contradiction that f cannot be negative.
  by_contra hfneg
  have hf_lt0 : f < 0 := lt_of_not_ge hfneg
  -- Then x - f > x (since -f > 0), hence |x - f| > x, contradicting minimality.
  have hx_lt_xmf : x < x - f := by
    have : 0 < -f := neg_pos.mpr hf_lt0
    have := add_lt_add_left this x
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
  have hxmf_pos : 0 < x - f := by
    exact lt_of_le_of_lt (by simpa using hx) hx_lt_xmf
  have hx_lt_abs : x < |x - f| := by
    -- Since x - f > 0, |x - f| = x - f
    simpa [abs_of_pos hxmf_pos] using hx_lt_xmf
  exact (lt_irrefl _ (lt_of_lt_of_le hx_lt_abs hmin0))

/-- Nearest rounding preserves nonpositivity in a format containing zero. -/
@[flocq_source "src/Core/Round_pred.v" 588 "Rnd_N_pt_le_0"]
theorem Rnd_N_pt_le_0 (F : ℝ → Prop) (hF0 : F 0) (x f : ℝ)
    (hx : x ≤ 0) (hf : Rnd_N_pt F x f) : f ≤ 0 := by
  -- From nearest minimality with g = 0 (since F 0), obtain |f - x| ≤ |0 - x| = -x.
  have hmin0 : |f - x| ≤ -x := by
    have h := hf.2 0 hF0
    -- |0 - x| = | -x | = |x| = -x because x ≤ 0
    simpa [sub_eq_add_neg, abs_neg, abs_of_nonpos hx] using h
  -- Prove by contradiction that f cannot be positive.
  by_contra hfpos
  have hf_gt0 : 0 < f := lt_of_not_ge hfpos
  -- Since x ≤ 0 and f > 0, we have 0 < f - x, hence |f - x| = f - x.
  have hpos : 0 < f - x := by
    -- 0 < (-x) + f = f - x
    have := add_pos_of_nonneg_of_pos (neg_nonneg.mpr hx) hf_gt0
    simpa [sub_eq_add_neg, add_comm] using this
  -- And also -x < f - x, hence -x < |f - x|.
  have hx_abs_gt : -x < |f - x| := by
    have : -x < f - x := by
      have := add_lt_add_left hf_gt0 (-x)
      simpa [sub_eq_add_neg, add_comm] using this
    simpa [abs_of_pos hpos] using this
  -- Contradiction with minimality |f - x| ≤ -x.
  exact (lt_irrefl _ (lt_of_lt_of_le hx_abs_gt hmin0))

/-- Absolute values preserve nearest rounding in a symmetric format containing zero. -/
@[flocq_source "src/Core/Round_pred.v" 603 "Rnd_N_pt_abs"]
theorem Rnd_N_pt_abs (F : ℝ → Prop) (hF0 : F 0) (hsym : ∀ x, F x → F (-x))
    (x f : ℝ) (hf : Rnd_N_pt F x f) : Rnd_N_pt F |x| |f| := by
  -- We prove `Rnd_N_pt F |x| |f|` by a case split on the sign of `x`.
  by_cases hx : 0 ≤ x
  · -- Case `x ≥ 0`: then `|x| = x`.
    have hFx : |x| = x := by simpa [abs_of_nonneg hx]
    -- Prove `F |f|` using closure under negation if necessary.
    have Hfabs : F |f| := by
      by_cases hf0 : 0 ≤ f
      · simpa [abs_of_nonneg hf0] using hf.1
      · have hfneg : f < 0 := lt_of_not_ge hf0
        simpa [abs_of_neg hfneg] using hsym f hf.1
    -- Establish minimality at `x` for `|f|` using the reverse triangle inequality.
    refine And.intro (by simpa [hFx] using Hfabs) ?_;
    intro g HgF
    -- `||f| - x| ≤ |f - x|` and `|f - x| ≤ |g - x|` from nearest minimality.
    have h1 : abs (abs f - x) ≤ abs (f - x) := by
      simpa [abs_of_nonneg hx] using (abs_abs_sub_abs_le_abs_sub f x)
    have h2 : abs (f - x) ≤ abs (g - x) := hf.2 g HgF
    have : abs (abs f - x) ≤ abs (g - x) := le_trans h1 h2
    simpa [hFx] using this
  · -- Case `x ≤ 0`: then `|x| = -x`.
    have hFx : |x| = -x := by simpa [abs_of_nonpos (le_of_not_ge hx)]
    -- We will derive the needed inequality at `-x` directly from minimality at `x`.
    -- Prove `F |f|` using closure under negation if necessary.
    have Hfabs : F |f| := by
      by_cases hf0 : 0 ≤ f
      · simpa [abs_of_nonneg hf0] using hf.1
      · have hfneg : f < 0 := lt_of_not_ge hf0
        simpa [abs_of_neg hfneg] using hsym f hf.1
    -- Establish minimality at `-x` for `|f|` via the reverse triangle inequality
    -- and minimality of `-f` at `-x`.
    refine And.intro (by simpa [hFx] using Hfabs) ?_;
    intro g HgF
    have h1 : abs (abs f - abs x) ≤ abs ((-f) - (-x)) := by
      -- Apply the inequality to `-f` and `-x`; note `| -f | = |f|` and `| -x | = |x|`.
      simpa using (abs_abs_sub_abs_le_abs_sub (-f) (-x))
    -- From nearest minimality at `x` for `f` and closure under negation, obtain
    -- `|f - x| ≤ |(-g) - x|`. Rewrite both sides to the `-x` frame.
    have h2 : abs ((-f) - (-x)) ≤ abs (g - (-x)) := by
      -- Start from minimality at `x`.
      have h2' : abs (f - x) ≤ abs ((-g) - x) := hf.2 (-g) (hsym g HgF)
      -- Rewrite both sides via explicit equalities to avoid fragile `simpa`.
      have hL : abs ((-f) - (-x)) = abs (f - x) := by
        have hxL : (-f) - (-x) = x - f := by simp [sub_eq_add_neg, add_comm]
        simpa [hxL, abs_sub_comm]
      have hR : abs (g - (-x)) = abs ((-g) - x) := by
        have hx1 : abs (g - (-x)) = abs (g + x) := by
          simpa [sub_eq_add_neg]
        have hx2 : abs ((-g) - x) = abs (g + x) := by
          have hx2' : (-g) - x = -(g + x) := by
            simp [sub_eq_add_neg, add_comm]
          calc
            abs ((-g) - x) = abs (-(g + x)) := by simpa [hx2']
            _ = abs (g + x) := by exact abs_neg (g + x)
        exact hx1.trans hx2.symm
      -- Transport `h2'` to the `-x` frame and rewrite to `+` form.
      have t : abs ((-f) - (-x)) ≤ abs (g - (-x)) := by
        -- Use the equalities in the reverse direction to transport `h2'`.
        simpa [hL.symm, hR.symm] using h2'
      have t' : abs (-f + x) ≤ abs (g + x) := by
        simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using t
      exact t
    have : abs (abs f - abs x) ≤ abs (g - (-x)) := le_trans h1 h2
    simpa [hFx] using this

/-- A representable point no farther than either directed endpoint is nearest. -/
@[flocq_source "src/Core/Round_pred.v" 627 "Rnd_N_pt_DN_UP"]
theorem Rnd_N_pt_DN_UP (F : ℝ → Prop) (x d u f : ℝ) (hf : F f)
    (hd : Rnd_DN_pt F x d) (hu : Rnd_UP_pt F x u)
    (hfd : |f - x| ≤ x - d) (hfu : |f - x| ≤ u - x) : Rnd_N_pt F x f := by
  -- It suffices to provide the nearest-point witness and distance minimality.
  refine And.intro hf ?_
  intro g hFg
  -- Compare g with x and dispatch to the DN/UP bounds accordingly.
  cases le_total g x with
  | inl hgle =>
      -- Case g ≤ x: by maximality of DN-point, g ≤ d, hence x - d ≤ x - g.
      have h_g_le_d : g ≤ d := hd.2.2 g hFg hgle
      have h_sub : x - d ≤ x - g := by simpa using (sub_le_sub_left h_g_le_d x)
      -- Chain the inequalities and rewrite |g - x| when g ≤ x.
      have : |f - x| ≤ x - g := le_trans hfd h_sub
      simpa [abs_sub_comm, abs_of_nonneg (sub_nonneg_of_le hgle)] using this
  | inr hxle =>
      -- Case x ≤ g: by minimality of UP-point, u ≤ g, hence u - x ≤ g - x.
      have h_u_le_g : u ≤ g := hu.2.2 g hFg hxle
      have h_sub : u - x ≤ g - x := by simpa using (sub_le_sub_right h_u_le_g x)
      -- Chain the inequalities and rewrite |g - x| when x ≤ g.
      have : |f - x| ≤ g - x := le_trans hfu h_sub
      simpa [abs_of_nonneg (sub_nonneg_of_le hxle)] using this

/-- The downward endpoint is nearest when its distance is no larger. -/
@[flocq_source "src/Core/Round_pred.v" 660 "Rnd_N_pt_DN"]
theorem Rnd_N_pt_DN (F : ℝ → Prop) (x d u : ℝ)
    (hd : Rnd_DN_pt F x d) (hu : Rnd_UP_pt F x u)
    (hdist : x - d ≤ u - x) : Rnd_N_pt F x d := by
  -- From DN we immediately get representability and `d ≤ x`.
  have hFd : F d := hd.1
  have hd_le_x : d ≤ x := hd.2.1
  -- It suffices to show the distance minimality property for `d`.
  refine And.intro hFd ?_
  intro g hFg
  -- Case split on the position of g relative to x.
  cases le_total g x with
  | inl hgle =>
      -- If g ≤ x then, by DN maximality, g ≤ d, hence x - d ≤ x - g.
      have h_g_le_d : g ≤ d := hd.2.2 g hFg hgle
      have h_sub : x - d ≤ x - g := by simpa using (sub_le_sub_left h_g_le_d x)
      -- Rewrite absolute values using the sign information.
      have : |d - x| ≤ x - g := by
        -- |d - x| = x - d because d ≤ x
        simpa [abs_sub_comm, abs_of_nonneg (sub_nonneg_of_le hd_le_x)] using h_sub
      simpa [abs_sub_comm, abs_of_nonneg (sub_nonneg_of_le hgle)] using this
  | inr hxle =>
      -- If x ≤ g then, by UP minimality, u ≤ g, hence u - x ≤ g - x.
      have h_u_le_g : u ≤ g := hu.2.2 g hFg hxle
      have h_sub : u - x ≤ g - x := by simpa using (sub_le_sub_right h_u_le_g x)
      -- Chain with the hypothesis x - d ≤ u - x and rewrite absolutes.
      have : |d - x| ≤ g - x := by
        -- From |d - x| = x - d and x - d ≤ u - x ≤ g - x
        have : x - d ≤ g - x := le_trans hdist h_sub
        simpa [abs_sub_comm, abs_of_nonneg (sub_nonneg_of_le hd_le_x)] using this
      simpa [abs_of_nonneg (sub_nonneg_of_le hxle)] using this

/-- The upward endpoint is nearest when its distance is no larger. -/
@[flocq_source "src/Core/Round_pred.v" 681 "Rnd_N_pt_UP"]
theorem Rnd_N_pt_UP (F : ℝ → Prop) (x d u : ℝ)
    (hd : Rnd_DN_pt F x d) (hu : Rnd_UP_pt F x u)
    (hdist : u - x ≤ x - d) : Rnd_N_pt F x u := by
  -- From UP we immediately get representability and `x ≤ u`.
  have hFu : F u := hu.1
  have hx_le_u : x ≤ u := hu.2.1
  -- It suffices to show the distance minimality property for `u`.
  refine And.intro hFu ?_
  intro g hFg
  -- Case split on the position of g relative to x.
  cases le_total g x with
  | inl hgle =>
      -- If g ≤ x then, by DN maximality, g ≤ d, hence x - d ≤ x - g.
      have h_g_le_d : g ≤ d := hd.2.2 g hFg hgle
      have h_sub : x - d ≤ x - g := by simpa using (sub_le_sub_left h_g_le_d x)
      -- Chain with the hypothesis u - x ≤ x - d and rewrite absolutes.
      have : |u - x| ≤ x - g := by
        -- From |u - x| = u - x and u - x ≤ x - d ≤ x - g
        have : u - x ≤ x - g := le_trans hdist h_sub
        simpa [abs_of_nonneg (sub_nonneg_of_le hx_le_u)] using this
      simpa [abs_sub_comm, abs_of_nonneg (sub_nonneg_of_le hgle)] using this
  | inr hxle =>
      -- If x ≤ g then, by UP minimality, u ≤ g, hence u - x ≤ g - x.
      have h_u_le_g : u ≤ g := hu.2.2 g hFg hxle
      have h_sub : u - x ≤ g - x := by simpa using (sub_le_sub_right h_u_le_g x)
      -- Rewrite absolute values using the sign information.
      have : |u - x| ≤ g - x := by
        -- |u - x| = u - x because x ≤ u
        simpa [abs_of_nonneg (sub_nonneg_of_le hx_le_u)] using h_sub
      simpa [abs_of_nonneg (sub_nonneg_of_le hxle)] using this

end RoundNearestAuxiliary

section RoundNearestGeneric

universe u

noncomputable section

/-- FLoCq's uniqueness condition for a generic nearest tie predicate. -/
@[flocq_source "src/Core/Round_pred.v" 701 "Rnd_NG_pt_unique_prop"]
def Rnd_NG_pt_unique_prop (F : ℝ → Prop) (P : ℝ → ℝ → Sort u) : Prop :=
  ∀ x d u,
    Rnd_DN_pt F x d → Rnd_N_pt F x d →
    Rnd_UP_pt F x u → Rnd_N_pt F x u →
    P x d → P x u → d = u

end

/-- A generic nearest policy gives unique results under its tie-uniqueness condition. -/
@[flocq_source "src/Core/Round_pred.v" 707 "Rnd_NG_pt_unique"]
theorem Rnd_NG_pt_unique (F : ℝ → Prop) (P : ℝ → ℝ → Prop)
    (hP : Rnd_NG_pt_unique_prop F P) (x f g : ℝ)
    (hf : Rnd_NG_pt F P x f) (hg : Rnd_NG_pt F P x g) : f = g := by
  rcases hf with ⟨hN1, hT1⟩
  rcases hg with ⟨hN2, hT2⟩
  -- If either point uses the uniqueness branch, conclude immediately.
  cases hT1 with
  | inr huniq1 => exact (huniq1 g hN2).symm
  | inl hP1 =>
      cases hT2 with
      | inr huniq2 => exact huniq2 f hN1
      | inl hP2 =>
          -- Both satisfy the tie predicate: classify each as DN or UP.
          rcases Rnd_N_pt_DN_or_UP F x f hN1 with hDN1 | hUP1 <;>
            rcases Rnd_N_pt_DN_or_UP F x g hN2 with hDN2 | hUP2
          · exact Rnd_DN_pt_unique F x f g hDN1 hDN2
          · exact hP x f g hDN1 hN1 hUP2 hN2 hP1 hP2
          · exact (hP x g f hDN2 hN2 hUP1 hN1 hP2 hP1).symm
          · exact Rnd_UP_pt_unique F x f g hUP1 hUP2

/-- A unique generic nearest policy is monotone, including equal inputs. -/
@[flocq_source "src/Core/Round_pred.v" 729 "Rnd_NG_pt_monotone"]
theorem Rnd_NG_pt_monotone (F : ℝ → Prop) (P : ℝ → ℝ → Prop)
    (hP : Rnd_NG_pt_unique_prop F P) : round_pred_monotone (Rnd_NG_pt F P) := by
  intro x y f g hf hg hxy
  rcases lt_or_eq_of_le hxy with hlt | rfl
  · exact Rnd_N_pt_monotone F x y f g hf.1 hg.1 hlt
  · exact le_of_eq (Rnd_NG_pt_unique F P hP x f g hf hg)

/-- Every generic nearest policy fixes representable inputs, even if its predicate is false. -/
@[flocq_source "src/Core/Round_pred.v" 741 "Rnd_NG_pt_refl"]
theorem Rnd_NG_pt_refl (F : ℝ → Prop) (P : ℝ → ℝ → Prop)
    (x : ℝ) (hx : F x) : Rnd_NG_pt F P x x :=
  ⟨Rnd_N_pt_refl F x hx, Or.inr (fun f hf ↦ Rnd_N_pt_idempotent F x f hf hx)⟩

/-- Coq-compatible name: NG-point invariance under negation -/
@[flocq_source "src/Core/Round_pred.v" 753 "Rnd_NG_pt_opp_inv"]
theorem Rnd_NG_pt_opp_inv (F : ℝ → Prop) (P : ℝ → ℝ → Prop)
    (hF : ∀ y, F y → F (-y)) (hP : ∀ x f, P x f → P (-x) (-f))
    (x f : ℝ) (h : Rnd_NG_pt F P (-x) (-f)) : Rnd_NG_pt F P x f := by
  rcases h with ⟨hN_neg, hTie_neg⟩
  -- Transfer the nearest property from (-x,-f) to (x,f).
  have hN : Rnd_N_pt F x f := Rnd_N_pt_opp_inv F x f hF hN_neg
  refine And.intro hN ?tie
  cases hTie_neg with
  | inl hPneg =>
      -- P (-x) (-f) gives P x f by sign symmetry (instantiated at -x,-f).
      have hPx : P x f := by
        simpa [neg_neg] using hP (-x) (-f) hPneg
      exact Or.inl hPx
  | inr huniq_neg =>
      -- Uniqueness transfer: any nearest point at x maps to one at -x.
      refine Or.inr ?uniq
      intro f2 hNf2
      have hNf2_neg : Rnd_N_pt F (-x) (-f2) := by
        have hNf2_neg' : Rnd_N_pt F (-(-x)) (-(-f2)) := by simpa [neg_neg] using hNf2
        exact Rnd_N_pt_opp_inv F (-x) (-f2) hF hNf2_neg'
      have hneg_eq : -f2 = -f := huniq_neg (-f2) hNf2_neg
      have := congrArg Neg.neg hneg_eq
      simpa [neg_neg] using this

/-- Two generic nearest functions with a unique tie policy agree pointwise. -/
@[flocq_source "src/Core/Round_pred.v" 778 "Rnd_NG_unique"]
theorem Rnd_NG_unique (F : ℝ → Prop) (P : ℝ → ℝ → Prop)
    (hP : Rnd_NG_pt_unique_prop F P) (rnd1 rnd2 : ℝ → ℝ)
    (h1 : Rnd_NG F P rnd1) (h2 : Rnd_NG F P rnd2) (x : ℝ) : rnd1 x = rnd2 x :=
  Rnd_NG_pt_unique F P hP x _ _ (h1 x) (h2 x)

end RoundNearestGeneric

section RoundNearestTies

/-- Nearest ties away from zero are the corresponding generic nearest policy. -/
@[flocq_source "src/Core/Round_pred.v" 789 "Rnd_NA_NG_pt"]
theorem Rnd_NA_NG_pt (F : ℝ → Prop) (hF0 : F 0) (x f : ℝ) :
    Rnd_NA_pt F x f ↔ Rnd_NG_pt F (fun x f ↦ |x| ≤ |f|) x f := by
  classical
  constructor
  · -- (→) From NA to NG with predicate |x| ≤ |f| (or uniqueness)
    intro hNA
    rcases hNA with ⟨hN, hTie⟩
    refine And.intro hN ?_;
    -- Either there is a different nearest point, or f is unique among nearest
    by_cases huniq : ∀ f2, Rnd_N_pt F x f2 → f2 = f
    · exact Or.inr huniq
    · -- There exists f2 ≠ f that is also nearest; prove |x| ≤ |f|
      rcases not_forall.mp huniq with ⟨f2, hnot⟩
      have hN2 : Rnd_N_pt F x f2 ∧ f2 ≠ f := by
        exact Classical.not_imp.mp hnot
      have hN2' : Rnd_N_pt F x f2 := hN2.1
      have hneq : f2 ≠ f := hN2.2
      -- Equal distances to x for two nearest points
      have h1 : |x - f| ≤ |x - f2| := by
        simpa [abs_sub_comm] using (hN.2 f2 hN2'.1)
      have h2 : |x - f2| ≤ |x - f| := by
        simpa [abs_sub_comm] using (hN2'.2 f hN.1)
      have heqAbs : |x - f| = |x - f2| := le_antisymm h1 h2
      -- From |x - f| = |x - f2| and f2 ≠ f, deduce x = (f + f2)/2
      have hx_mid : x = (f + f2) / 2 := by
        have hcase := abs_eq_abs.mp heqAbs
        cases hcase with
        | inl hsame =>
            -- x - f = x - f2 ⇒ f = f2 (contradiction)
            have : f = f2 := by
              have := congrArg (fun t => t + (-x)) hsame
              simpa [add_comm, add_left_comm, add_assoc, sub_eq_add_neg] using this
            exact (hneq this.symm).elim
        | inr hopp =>
            -- x - f = -(x - f2) = f2 - x ⇒ 2x = f + f2
            have : x - f = f2 - x := by simpa [neg_sub] using hopp
            have hsum : (x - f) + (x + f) = (f2 - x) + (x + f) := congrArg (fun t => t + (x + f)) this
            -- Simplify both sides
            have h2x : 2 * x = f + f2 := by
              simpa [two_mul, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hsum
            -- Divide by 2 using `eq_div_iff_mul_eq`
            have hx2 : x * 2 = f + f2 := by simpa [mul_comm] using h2x
            have h2ne : (2 : ℝ) ≠ 0 := by norm_num
            exact (eq_div_iff_mul_eq h2ne).2 hx2
      -- Bound |x| via the average and the tie property |f2| ≤ |f|
      have havg_le : |x| ≤ (|f| + |f2|) / 2 := by
        -- |(f + f2)/2| = |f + f2|/2 ≤ (|f| + |f2|)/2
        have habs_div2 : |(f + f2) / 2| = |f + f2| / 2 := by
          simpa [abs_div, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ (2 : ℝ))]
        have htri : |f + f2| ≤ |f| + |f2| := by
          -- Use `abs_add'` with `b := -f2` and simplify
          simpa [abs_neg, add_comm, add_left_comm, add_assoc]
            using (abs_add' (f + f2) (-f2))
        have hdiv_le : |f + f2| / 2 ≤ (|f| + |f2|) / 2 :=
          (div_le_div_of_nonneg_right htri (by norm_num : (0 : ℝ) ≤ 2))
        have hxabs : |x| = |(f + f2) / 2| := by simpa [hx_mid]
        exact (by simpa [hxabs, habs_div2] using hdiv_le)
      have hP : |x| ≤ |f| := by
        have hf2_le_f : |f2| ≤ |f| := hTie f2 hN2'
        -- (|f| + |f2|)/2 ≤ |f|
        have : (|f| + |f2|) / 2 ≤ |f| := by
          have hmono :=
            (div_le_div_of_nonneg_right (add_le_add_left hf2_le_f |f|)
              (by norm_num : (0 : ℝ) ≤ 2))
          -- (|f| + |f|)/2 = |f|
          have hsimp : (|f| + |f|) / 2 = |f| := by
            have : (2 * |f|) / 2 = |f| := by
              simpa using (mul_div_cancel' |f| (2 : ℝ))
            simpa [two_mul, mul_comm] using this
          calc (|f| + |f2|) / 2 = (|f2| + |f|) / 2 := by rw [add_comm]
            _ ≤ (|f| + |f|) / 2 := hmono
            _ = |f| := hsimp
        exact le_trans havg_le this
      exact Or.inl hP
  · -- (←) From NG with predicate |x| ≤ |f| (or uniqueness) to NA
    intro hNG
    rcases hNG with ⟨hN, hbranch⟩
    refine And.intro hN ?_;
    intro f2 hN2
    -- Distances to x are equal for any two nearest points
    have h1 : |x - f| ≤ |x - f2| := by simpa [abs_sub_comm] using (hN.2 f2 hN2.1)
    have h2 : |x - f2| ≤ |x - f| := by simpa [abs_sub_comm] using (hN2.2 f hN.1)
    have heqAbs : |x - f| = |x - f2| := le_antisymm h1 h2
    -- If uniqueness holds in the NG branch, we are done immediately
    cases hbranch with
    | inr huniq =>
        simpa [huniq f2 hN2]
    | inl hP =>
        -- Use the sign of x to relate signs of f and f2, then compare linearly
        by_cases hx0 : 0 ≤ x
        · -- Nonnegative case: f, f2 are nonnegative; P gives x ≤ f
          have hf_nonneg : 0 ≤ f := Rnd_N_pt_ge_0 F hF0 x f hx0 hN
          have hf2_nonneg : 0 ≤ f2 := Rnd_N_pt_ge_0 F hF0 x f2 hx0 hN2
          have hx_le_f : x ≤ f := by simpa [abs_of_nonneg hx0, abs_of_nonneg hf_nonneg] using hP
          -- From equal distances and x ≤ f, deduce f2 ≤ f
          have hx_mid_or := abs_eq_abs.mp heqAbs
          have hf2_le_f : f2 ≤ f := by
            cases hx_mid_or with
            | inl hsame =>
                -- x - f = x - f2 ⇒ f = f2
                have hf_eq : f = f2 := by
                  have := congrArg (fun t => t + (-x)) hsame
                  simpa [add_comm, add_left_comm, add_assoc, sub_eq_add_neg] using this
                exact hf_eq.symm ▸ le_rfl
            | inr hopp =>
                -- x - f = -(x - f2) = f2 - x ⇒ 2x = f + f2
                have : x - f = f2 - x := by simpa [neg_sub] using hopp
                have hsum' : (x - f) + (x + f) = (f2 - x) + (x + f) :=
                  congrArg (fun t => t + (x + f)) this
                have hsum : 2 * x = f + f2 := by
                  simpa [two_mul, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hsum'
                -- From 2x ≤ 2f and 2x = f + f2, get f2 ≤ f
                have hineq : 2 * x ≤ 2 * f := by
                  simpa using
                    (mul_le_mul_of_nonneg_left hx_le_f (by norm_num : (0 : ℝ) ≤ 2))
                have : 2 * x - f ≤ 2 * f - f := sub_le_sub_right hineq f
                simpa [hsum, two_mul, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
          -- With nonnegativity, absolute values drop
          have : |f2| ≤ |f| := by simpa [abs_of_nonneg hf2_nonneg, abs_of_nonneg hf_nonneg] using hf2_le_f
          exact this
        · -- Nonpositive case: f, f2 are nonpositive; P gives -x ≤ -f i.e., f ≤ x
          have hxle0 : x ≤ 0 := le_of_lt (lt_of_not_ge hx0)
          have hf_nonpos : f ≤ 0 := Rnd_N_pt_le_0 F hF0 x f hxle0 hN
          have hf2_nonpos : f2 ≤ 0 := Rnd_N_pt_le_0 F hF0 x f2 hxle0 hN2
          have hf_le_x : f ≤ x := by
            -- |x| ≤ |f| ⇒ -x ≤ -f
            have : -x ≤ -f := by
              simpa [abs_of_nonpos hxle0, abs_of_nonpos hf_nonpos] using hP
            simpa using (neg_le_neg_iff.mp this)
          -- From equal distances and f ≤ x, deduce f ≤ f2, hence |f2| ≤ |f|
          have hx_mid_or := abs_eq_abs.mp heqAbs
          have hf_le_f2 : f ≤ f2 := by
            cases hx_mid_or with
            | inl hsame =>
                -- x - f = x - f2 ⇒ f = f2
                have hf_eq : f = f2 := by
                  have := congrArg (fun t => t + (-x)) hsame
                  simpa [add_comm, add_left_comm, add_assoc, sub_eq_add_neg] using this
                exact hf_eq ▸ le_rfl
            | inr hopp =>
                -- x - f = -(x - f2) = f2 - x ⇒ 2x = f + f2
                have : x - f = f2 - x := by simpa [neg_sub] using hopp
                have hsum' : (x - f) + (x + f) = (f2 - x) + (x + f) :=
                  congrArg (fun t => t + (x + f)) this
                have hsum : 2 * x = f + f2 := by
                  simpa [two_mul, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hsum'
                -- From 2f ≤ 2x and 2x = f + f2, get f ≤ f2
                have hineq : 2 * f ≤ 2 * x := by
                  simpa using
                    (mul_le_mul_of_nonneg_left hf_le_x (by norm_num : (0 : ℝ) ≤ 2))
                have : 2 * f ≤ f + f2 := by simpa [hsum] using hineq
                -- Subtract f on both sides to isolate f ≤ f2
                have := sub_le_sub_right this f
                simpa [two_mul, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
          -- both nonpositive ⇒ -f2 ≤ -f, i.e., |f2| ≤ |f|
          have : |f2| ≤ |f| := by
            have : -f2 ≤ -f := by exact neg_le_neg hf_le_f2
            simpa [abs_of_nonpos hf2_nonpos, abs_of_nonpos hf_nonpos] using this
          exact this

/-- The ties-away from zero predicate satisfies generic tie uniqueness. -/
@[flocq_source "src/Core/Round_pred.v" 890 "Rnd_NA_pt_unique_prop"]
theorem Rnd_NA_pt_unique_prop (F : ℝ → Prop) (hF0 : F 0) :
    Rnd_NG_pt_unique_prop F (fun x f ↦ |x| ≤ |f|) := by
  intro x d u hDN hNd hUP hNu hAd hAu
  -- Case split on the sign of x.
  by_cases hx : 0 ≤ x
  · -- Nonnegative case: deduce nonnegativity of nearest values d and u.
    have hd_nonneg : 0 ≤ d := Rnd_N_pt_ge_0 F hF0 x d hx hNd
    have hu_nonneg : 0 ≤ u := Rnd_N_pt_ge_0 F hF0 x u hx hNu
    -- From |x| ≤ |d| and nonnegativity, obtain x ≤ d; DN gives d ≤ x, hence d = x.
    have hx_le_d : x ≤ d := by
      simpa [abs_of_nonneg hx, abs_of_nonneg hd_nonneg] using hAd
    have hd_eq_x : d = x := le_antisymm hDN.2.1 hx_le_d
    -- From nearest minimality for u with candidate d = x, conclude u = x.
    have hdist : |u - x| ≤ |d - x| := hNu.2 d hDN.1
    have : |u - x| ≤ 0 := by simpa [hd_eq_x, sub_self] using hdist
    have hux0 : |u - x| = 0 := le_antisymm this (abs_nonneg _)
    have : u - x = 0 := by simpa using (abs_eq_zero.mp hux0)
    have hu_eq_x : u = x := sub_eq_zero.mp this
    simpa [hd_eq_x, hu_eq_x]
  · -- Nonpositive case: deduce nonpositivity of nearest values d and u.
    have hxle0 : x ≤ 0 := le_of_lt (lt_of_not_ge hx)
    have hd_nonpos : d ≤ 0 := Rnd_N_pt_le_0 F hF0 x d hxle0 hNd
    have hu_nonpos : u ≤ 0 := Rnd_N_pt_le_0 F hF0 x u hxle0 hNu
    -- Use |x| ≤ |u| together with nonpositivity and UP to get u = x.
    have hx_le_u : x ≤ u := hUP.2.1
    have hu_le_x : u ≤ x := by
      have : -x ≤ -u := by
        simpa [abs_of_nonpos hxle0, abs_of_nonpos hu_nonpos] using hAu
      exact (neg_le_neg_iff.mp this)
    have hu_eq_x : u = x := le_antisymm hu_le_x hx_le_u
    -- From nearest minimality for d with candidate u = x, conclude d = x.
    have hdist : |d - x| ≤ |u - x| := hNd.2 u hUP.1
    have hdx0 : |d - x| = 0 := by
      have : |d - x| ≤ 0 := by simpa [hu_eq_x, sub_self] using hdist
      exact le_antisymm this (abs_nonneg _)
    have : d - x = 0 := by simpa using (abs_eq_zero.mp hdx0)
    have hd_eq_x : d = x := sub_eq_zero.mp this
    simpa [hd_eq_x, hu_eq_x]

/-- Nearest ties toward zero are the corresponding generic nearest policy. -/
@[flocq_source "src/Core/Round_pred.v" 1030 "Rnd_N0_NG_pt"]
theorem Rnd_N0_NG_pt (F : ℝ → Prop) (hF0 : F 0) (x f : ℝ) :
    Rnd_N0_pt F x f ↔ Rnd_NG_pt F (fun x f ↦ |f| ≤ |x|) x f := by
  classical
  by_cases hx : 0 ≤ x
  · -- Case 0 ≤ x
    constructor
    · -- (→) From N0-point to NG-point with P := fun x f => |f| ≤ |x|
      intro hN0
      rcases hN0 with ⟨hN, hMinAbs⟩
      -- Classification of f as DN/UP for x using nearest property
      have hDU : Rnd_DN_pt F x f ∨ Rnd_UP_pt F x f := Rnd_N_pt_DN_or_UP F x f hN
      -- From nearest at nonnegative x, deduce f ≥ 0
      have h0le_f : 0 ≤ f := by
        -- Minimality vs g = 0 gives |x - f| ≤ |x|
        have hmin0 : |x - f| ≤ |x| := by
          have := hN.2 0 (by simpa using ‹F 0›)
          simpa [abs_sub_comm, sub_zero, abs_of_nonneg hx] using this
        -- Prove by contradiction that f < 0 is impossible
        by_contra hfneg
        have hf_lt0 : f < 0 := lt_of_not_ge hfneg
        have hx_lt_xmf : x < x - f := by
          have : 0 < -f := neg_pos.mpr hf_lt0
          have := add_lt_add_left this x
          simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
        have hxmf_pos : 0 < x - f := lt_of_le_of_lt hx hx_lt_xmf
        have hx_lt_abs : x < |x - f| := by simpa [abs_of_pos hxmf_pos] using hx_lt_xmf
        -- Compose inequalities and rewrite |x| = x (since 0 ≤ x)
        have hx_lt_abs' : x < |x| := lt_of_lt_of_le hx_lt_abs hmin0
        have hx_lt_x : x < x := by simpa [abs_of_nonneg hx] using hx_lt_abs'
        exact (lt_irrefl _ hx_lt_x)
      -- Build NG: nearest plus either P or uniqueness on ties
      refine And.intro hN ?_;
      -- Split on whether f is DN or UP
      cases hDU with
      | inl hDN =>
          -- DN case: since 0 ≤ f ≤ x, we have |f| ≤ |x|
          left
          have : f ≤ x := hDN.2.1
          simpa [abs_of_nonneg h0le_f, abs_of_nonneg hx] using this
      | inr hUP =>
          -- UP case: prove uniqueness among nearest points
          right
          intro f2 hN2
          -- Use the N0 minimal-abs property and classify f2
          have hMin : |f| ≤ |f2| := hMinAbs f2 hN2
          have hDU2 : Rnd_DN_pt F x f2 ∨ Rnd_UP_pt F x f2 := Rnd_N_pt_DN_or_UP F x f2 hN2
          -- Also f2 ≥ 0 under 0 ≤ x
          have h0le_f2 : 0 ≤ f2 := by
            -- As above, use minimality vs 0 and contradict f2 < 0
            have hmin0 : |x - f2| ≤ |x| := by
              have := hN2.2 0 (by simpa using ‹F 0›)
              simpa [abs_sub_comm, sub_zero, abs_of_nonneg hx] using this
            by_contra hf2neg
            have hf2_lt0 : f2 < 0 := lt_of_not_ge hf2neg
            have hx_lt_xmf : x < x - f2 := by
              have : 0 < -f2 := neg_pos.mpr hf2_lt0
              have := add_lt_add_left this x
              simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
            have hxmf_pos : 0 < x - f2 := lt_of_le_of_lt hx hx_lt_xmf
            have hx_lt_abs : x < |x - f2| := by simpa [abs_of_pos hxmf_pos] using hx_lt_xmf
            -- Compose inequalities and rewrite |x| = x (since 0 ≤ x)
            have hx_lt_abs' : x < |x| := lt_of_lt_of_le hx_lt_abs hmin0
            have hx_lt_x : x < x := by simpa [abs_of_nonneg hx] using hx_lt_abs'
            exact (lt_irrefl _ hx_lt_x)
          -- Now analyze f2 as DN or UP
          cases hDU2 with
          | inl hDN2 =>
              -- f2 DN, f UP: obtain f2 ≤ x ≤ f and combine with |f| ≤ |f2| to deduce equality
              have hle1 : f2 ≤ f := le_trans hDN2.2.1 hUP.2.1
              -- From |f| ≤ |f2| and nonnegativity, deduce f ≤ f2
              have hle2 : f ≤ f2 := by
                simpa [abs_of_nonneg h0le_f, abs_of_nonneg h0le_f2] using hMin
              exact le_antisymm hle1 hle2
          | inr hUP2 =>
              -- Both UP: uniqueness by mutual minimality
              have h12 : f ≤ f2 := hUP.2.2 f2 hUP2.1 hUP2.2.1
              have h21 : f2 ≤ f := hUP2.2.2 f hUP.1 hUP.2.1
              exact le_antisymm h21 h12
    · -- (←) From NG with P/uniqueness to N0
      intro hNG
      rcases hNG with ⟨hN, hTie⟩
      -- Show the minimal-absolute-value property required by N0
      refine And.intro hN ?_
      intro f2 hN2
      -- Nonnegativity of f and f2 under 0 ≤ x
      have h0le_f : 0 ≤ f := by
        -- Same argument as above for f
        have hmin0 : |x - f| ≤ |x| := by
          have := hN.2 0 (by simpa using ‹F 0›)
          simpa [abs_sub_comm, sub_zero, abs_of_nonneg hx] using this
        by_contra hfneg
        have hf_lt0 : f < 0 := lt_of_not_ge hfneg
        have hx_lt_xmf : x < x - f := by
          have : 0 < -f := neg_pos.mpr hf_lt0
          have := add_lt_add_left this x
          simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
        have hxmf_pos : 0 < x - f := lt_of_le_of_lt hx hx_lt_xmf
        have hx_lt_abs : x < |x - f| := by simpa [abs_of_pos hxmf_pos] using hx_lt_xmf
        have hx_lt_abs' : x < |x| := lt_of_lt_of_le hx_lt_abs hmin0
        have hx_lt_x : x < x := by simpa [abs_of_nonneg hx] using hx_lt_abs'
        exact (lt_irrefl _ hx_lt_x)
      have h0le_f2 : 0 ≤ f2 := by
        -- Same argument as above for f2
        have hmin0 : |x - f2| ≤ |x| := by
          have := hN2.2 0 (by simpa using ‹F 0›)
          simpa [abs_sub_comm, sub_zero, abs_of_nonneg hx] using this
        by_contra hf2neg
        have hf2_lt0 : f2 < 0 := lt_of_not_ge hf2neg
        have hx_lt_xmf : x < x - f2 := by
          have : 0 < -f2 := neg_pos.mpr hf2_lt0
          have := add_lt_add_left this x
          simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
        have hxmf_pos : 0 < x - f2 := lt_of_le_of_lt hx hx_lt_xmf
        have hx_lt_abs : x < |x - f2| := by simpa [abs_of_pos hxmf_pos] using hx_lt_xmf
        -- Compose inequalities and rewrite |x| = x (since 0 ≤ x)
        have hx_lt_abs' : x < |x| := lt_of_lt_of_le hx_lt_abs hmin0
        have hx_lt_x : x < x := by simpa [abs_of_nonneg hx] using hx_lt_abs'
        exact (lt_irrefl _ hx_lt_x)
      -- Classify f2 as DN or UP
      have hDU2 : Rnd_DN_pt F x f2 ∨ Rnd_UP_pt F x f2 := Rnd_N_pt_DN_or_UP F x f2 hN2
      -- Use the tie information
      cases hTie with
      | inl hP =>
          -- P: |f| ≤ |x|; with nonnegativity, this gives f ≤ x
          have hfle_x : f ≤ x := by simpa [abs_of_nonneg h0le_f, abs_of_nonneg hx] using hP
          -- Now deduce |f| ≤ |f2| by analyzing f2 as DN or UP
          cases hDU2 with
          | inl hDN2 =>
              -- f2 is DN: use maximality at x with candidate f
              have hle : f ≤ f2 := hDN2.2.2 f hN.1 hfle_x
              simpa [abs_of_nonneg h0le_f, abs_of_nonneg h0le_f2] using hle
          | inr hUP2 =>
              -- f2 is UP: since x ≤ f2, transitivity yields f ≤ f2
              have hle : f ≤ f2 := le_trans hfle_x hUP2.2.1
              simpa [abs_of_nonneg h0le_f, abs_of_nonneg h0le_f2] using hle
      | inr huniq =>
          -- Uniqueness: any nearest f2 must equal f
          have : f2 = f := huniq f2 hN2
          simpa [this]
  · -- Case x < 0 (so x ≤ 0)
    have hxle0 : x ≤ 0 := le_of_lt (lt_of_not_ge hx)
    constructor
    · -- (→) From N0-point to NG-point with P
      intro hN0
      rcases hN0 with ⟨hN, hMinAbs⟩
      -- Classification of f as DN/UP for x using nearest property
      have hDU : Rnd_DN_pt F x f ∨ Rnd_UP_pt F x f := Rnd_N_pt_DN_or_UP F x f hN
      -- From nearest at nonpositive x, deduce f ≤ 0
      have hf_le0 : f ≤ 0 := by
        -- Minimality vs g = 0 gives |f - x| ≤ | -x | = -x
        have hmin0 : |f - x| ≤ -x := by
          have h := hN.2 0 (by simpa using ‹F 0›)
          simpa [sub_eq_add_neg, abs_neg, abs_of_nonpos hxle0] using h
        -- Prove by contradiction that f > 0 is impossible
        by_contra hfpos
        have hf_gt0 : 0 < f := lt_of_not_ge hfpos
        have hpos : 0 < f - x := by
          have := add_pos_of_nonneg_of_pos (neg_nonneg.mpr hxle0) hf_gt0
          simpa [sub_eq_add_neg, add_comm] using this
        have hx_abs_gt : -x < |f - x| := by
          have : -x < f - x := by
            have := add_lt_add_left hf_gt0 (-x)
            simpa [sub_eq_add_neg, add_comm] using this
          simpa [abs_of_pos hpos] using this
        exact (lt_irrefl _ (lt_of_lt_of_le hx_abs_gt hmin0))
      -- Build NG: nearest plus either P or uniqueness
      refine And.intro hN ?_;
      cases hDU with
      | inl hDN =>
          -- DN case at x ≤ 0: uniqueness among nearest points
          right
          intro f2 hN2
          -- Use the N0 minimal-abs property and classify f2
          have hMin : |f| ≤ |f2| := hMinAbs f2 hN2
          have hDU2 : Rnd_DN_pt F x f2 ∨ Rnd_UP_pt F x f2 := Rnd_N_pt_DN_or_UP F x f2 hN2
          -- Also f2 ≤ 0 under x ≤ 0
          have hf2_le0 : f2 ≤ 0 := by
            -- Analogous argument for f2
            have hmin0 : |f2 - x| ≤ -x := by
              have h := hN2.2 0 (by simpa using ‹F 0›)
              simpa [sub_eq_add_neg, abs_neg, abs_of_nonpos hxle0] using h
            by_contra hf2pos
            have hf2_gt0 : 0 < f2 := lt_of_not_ge hf2pos
            have hpos : 0 < f2 - x := by
              have := add_pos_of_nonneg_of_pos (neg_nonneg.mpr hxle0) hf2_gt0
              simpa [sub_eq_add_neg, add_comm] using this
            have hx_abs_gt : -x < |f2 - x| := by
              have : -x < f2 - x := by
                have := add_lt_add_left hf2_gt0 (-x)
                simpa [sub_eq_add_neg, add_comm] using this
              simpa [abs_of_pos hpos] using this
            exact (lt_irrefl _ (lt_of_lt_of_le hx_abs_gt hmin0))
          -- Analyze f2 as DN or UP
          cases hDU2 with
          | inl hDN2 =>
              -- Both DN: uniqueness by mutual maximality
              have le12 : f ≤ f2 := hDN2.2.2 f hDN.1 hDN.2.1
              have le21 : f2 ≤ f := hDN.2.2 f2 hDN2.1 hDN2.2.1
              exact le_antisymm le21 le12
          | inr hUP2 =>
              -- f DN, f2 UP: obtain f ≤ x ≤ f2 and use |f| ≤ |f2| to deduce equality
              have hle1 : f ≤ f2 := le_trans hDN.2.1 hUP2.2.1
              have hle2' : f2 ≤ f := by
                have : -f ≤ -f2 := by
                  simpa [abs_of_nonpos hf_le0, abs_of_nonpos hf2_le0] using hMin
                simpa using (neg_le_neg_iff.mp this)
              exact le_antisymm hle2' hle1
      | inr hUP =>
          -- UP case at x ≤ 0: show P holds, i.e., |f| ≤ |x|
          left
          have hxle_f : x ≤ f := hUP.2.1
          -- From x ≤ 0 and x ≤ f, we get -f ≤ -x
          have : -f ≤ -x := by exact neg_le_neg hxle_f
          simpa [abs_of_nonpos hf_le0, abs_of_nonpos hxle0] using this
    · -- (←) From NG with P/uniqueness to N0
      intro hNG
      rcases hNG with ⟨hN, hTie⟩
      refine And.intro hN ?_
      intro f2 hN2
      -- f ≤ 0 and f2 ≤ 0 under x ≤ 0
      have hf_le0 : f ≤ 0 := by
        -- From nearest and x ≤ 0 as above
        have hmin0 : |f - x| ≤ -x := by
          have h := hN.2 0 (by simpa using ‹F 0›)
          simpa [sub_eq_add_neg, abs_neg, abs_of_nonpos hxle0] using h
        by_contra hfpos
        have hf_gt0 : 0 < f := lt_of_not_ge hfpos
        have hpos : 0 < f - x := by
          have := add_pos_of_nonneg_of_pos (neg_nonneg.mpr hxle0) hf_gt0
          simpa [sub_eq_add_neg, add_comm] using this
        have hx_abs_gt : -x < |f - x| := by
          have : -x < f - x := by
            have := add_lt_add_left hf_gt0 (-x)
            simpa [sub_eq_add_neg, add_comm] using this
          simpa [abs_of_pos hpos] using this
        exact (lt_irrefl _ (lt_of_lt_of_le hx_abs_gt hmin0))
      have hf2_le0 : f2 ≤ 0 := by
        -- Same for f2
        have hmin0 : |f2 - x| ≤ -x := by
          have h := hN2.2 0 (by simpa using ‹F 0›)
          simpa [sub_eq_add_neg, abs_neg, abs_of_nonpos hxle0] using h
        by_contra hfpos
        have hf_gt0 : 0 < f2 := lt_of_not_ge hfpos
        have hpos : 0 < f2 - x := by
          have := add_pos_of_nonneg_of_pos (neg_nonneg.mpr hxle0) hf_gt0
          simpa [sub_eq_add_neg, add_comm] using this
        have hx_abs_gt : -x < |f2 - x| := by
          have : -x < f2 - x := by
            have := add_lt_add_left hf_gt0 (-x)
            simpa [sub_eq_add_neg, add_comm] using this
          simpa [abs_of_pos hpos] using this
        exact (lt_irrefl _ (lt_of_lt_of_le hx_abs_gt hmin0))
      -- Classify f2 as DN or UP
      have hDU2 : Rnd_DN_pt F x f2 ∨ Rnd_UP_pt F x f2 := Rnd_N_pt_DN_or_UP F x f2 hN2
      -- Use the tie information
      cases hTie with
      | inl hP =>
          -- P: |f| ≤ |x|; with nonpositivity, this gives -f ≤ -x
          have hneg_le : -f ≤ -x := by
            -- rewrite |f| = -f and |x| = -x
            simpa [abs_of_nonpos hf_le0, abs_of_nonpos hxle0] using hP
          -- Goal: |f| ≤ |f2| i.e., -f ≤ -f2; analyze f2
          cases hDU2 with
          | inl hDN2 =>
              -- f2 DN: from hDN2.2.1 (f2 ≤ x) and hneg_le (−f ≤ −x) deduce -f ≤ -f2
              have hle : -f ≤ -f2 := le_trans hneg_le (by exact neg_le_neg hDN2.2.1)
              simpa [abs_of_nonpos hf_le0, abs_of_nonpos hf2_le0] using hle
          | inr hUP2 =>
              -- f2 UP: use minimality at f2 with g = f and x ≤ f to get f2 ≤ f, then negate
              have hxle_f : x ≤ f := (neg_le_neg_iff.mp hneg_le)
              have hle' : f2 ≤ f := hUP2.2.2 f hN.1 hxle_f
              have hle : -f ≤ -f2 := by exact neg_le_neg hle'
              simpa [abs_of_nonpos hf_le0, abs_of_nonpos hf2_le0] using hle
      | inr huniq =>
          -- Uniqueness: any nearest f2 must equal f
          have : f2 = f := huniq f2 hN2
          simpa [this]

/-- The ties-toward-zero predicate satisfies generic tie uniqueness. -/
@[flocq_source "src/Core/Round_pred.v" 1131 "Rnd_N0_pt_unique_prop"]
theorem Rnd_N0_pt_unique_prop (F : ℝ → Prop) (hF0 : F 0) :
    Rnd_NG_pt_unique_prop F (fun x f ↦ |f| ≤ |x|) := by
  intro x d u hDN hNd hUP hNu hAd hAu
  -- Case split on the sign of x.
  by_cases hx : 0 ≤ x
  · -- Case x ≥ 0: deduce u ≤ x from |u| ≤ |x| using nonnegativity of u.
    -- From nearest at nonnegative x, we have 0 ≤ u (using F 0).
    have hu_nonneg : 0 ≤ u := Rnd_N_pt_ge_0 F hF0 x u hx hNu
    have hu_le_x : u ≤ x := by
      simpa [abs_of_nonneg hu_nonneg, abs_of_nonneg hx] using hAu
    have hx_le_u : x ≤ u := hUP.2.1
    have hu_eq_x : u = x := le_antisymm hu_le_x hx_le_u
    -- From nearest minimality for d with candidate u, conclude d = x = u.
    have hFd : F d := hDN.1
    have hdist : |d - x| ≤ |u - x| := hNd.2 u hUP.1
    have hdx0 : |d - x| = 0 := by
      have : |d - x| ≤ 0 := by simpa [hu_eq_x, sub_self] using hdist
      exact le_antisymm this (abs_nonneg _)
    have hd_eq_x : d = x := by
      have : d - x = 0 := by simpa using (abs_eq_zero.mp hdx0)
      exact sub_eq_zero.mp this
    simpa [hd_eq_x, hu_eq_x]
  · -- Case x ≤ 0: deduce x ≤ d from |d| ≤ |x| using nonpositivity of d.
    have hxle0 : x ≤ 0 := le_of_lt (lt_of_not_ge hx)
    -- From nearest at nonpositive x, we have d ≤ 0 (using F 0).
    have hd_nonpos : d ≤ 0 := Rnd_N_pt_le_0 F hF0 x d hxle0 hNd
    have hx_le_d : x ≤ d := by
      have : -d ≤ -x := by
        simpa [abs_of_nonpos hd_nonpos, abs_of_nonpos hxle0] using hAd
      exact (neg_le_neg_iff.mp this)
    have hd_le_x : d ≤ x := hDN.2.1
    have hd_eq_x : d = x := le_antisymm hd_le_x hx_le_d
    -- From nearest minimality for u with candidate d, conclude u = x = d.
    have hdist : |u - x| ≤ |d - x| := hNu.2 d hDN.1
    have hux0 : |u - x| = 0 := by
      have : |u - x| ≤ 0 := by simpa [hd_eq_x, sub_self] using hdist
      exact le_antisymm this (abs_nonneg _)
    have hu_eq_x : u = x := by
      have : u - x = 0 := by simpa using (abs_eq_zero.mp hux0)
      exact sub_eq_zero.mp this
    simpa [hd_eq_x, hu_eq_x]

/-- Nearest rounding with ties away from zero has a unique result. -/
@[flocq_source "src/Core/Round_pred.v" 917 "Rnd_NA_pt_unique"]
theorem Rnd_NA_pt_unique (F : ℝ → Prop) (hF0 : F 0) (x f g : ℝ)
    (hf : Rnd_NA_pt F x f) (hg : Rnd_NA_pt F x g) : f = g :=
  Rnd_NG_pt_unique F (fun x f ↦ |x| ≤ |f|) (Rnd_NA_pt_unique_prop F hF0) x f g
    ((Rnd_NA_NG_pt F hF0 x f).mp hf) ((Rnd_NA_NG_pt F hF0 x g).mp hg)

/-- A nearest value satisfying the absolute-value bound obeys ties away from zero. -/
@[flocq_source "src/Core/Round_pred.v" 930 "Rnd_NA_pt_N"]
theorem Rnd_NA_pt_N (F : ℝ → Prop) (hF0 : F 0) (x f : ℝ)
    (hf : Rnd_N_pt F x f) (habs : |x| ≤ |f|) : Rnd_NA_pt F x f := by
  exact (Rnd_NA_NG_pt F hF0 x f).mpr ⟨hf, Or.inl habs⟩

/-- Two nearest functions with ties away from zero agree pointwise. -/
@[flocq_source "src/Core/Round_pred.v" 983 "Rnd_NA_unique"]
theorem Rnd_NA_unique (F : ℝ → Prop) (hF0 : F 0) (rnd1 rnd2 : ℝ → ℝ)
    (h1 : Rnd_NA F rnd1) (h2 : Rnd_NA F rnd2) (x : ℝ) : rnd1 x = rnd2 x :=
  Rnd_NA_pt_unique F hF0 x _ _ (h1 x) (h2 x)

/-- Nearest rounding with ties away from zero is monotone when zero is representable. -/
@[flocq_source "src/Core/Round_pred.v" 994 "Rnd_NA_pt_monotone"]
theorem Rnd_NA_pt_monotone (F : ℝ → Prop) (hF0 : F 0) :
    round_pred_monotone (Rnd_NA_pt F) := by
  intro x y f g hf hg hxy
  exact Rnd_NG_pt_monotone F (fun x f ↦ |x| ≤ |f|) (Rnd_NA_pt_unique_prop F hF0)
    x y f g ((Rnd_NA_NG_pt F hF0 x f).mp hf)
    ((Rnd_NA_NG_pt F hF0 y g).mp hg) hxy

/-- Representable inputs are fixed by nearest rounding with ties away from zero. -/
@[flocq_source "src/Core/Round_pred.v" 1006 "Rnd_NA_pt_refl"]
theorem Rnd_NA_pt_refl (F : ℝ → Prop) (x : ℝ) (hx : F x) : Rnd_NA_pt F x x := by
  refine ⟨Rnd_N_pt_refl F x hx, ?_⟩
  intro f hf
  rw [Rnd_N_pt_idempotent F x f hf hx]

/-- Nearest rounding with ties away from zero fixes representable inputs. -/
@[flocq_source "src/Core/Round_pred.v" 1020 "Rnd_NA_pt_idempotent"]
theorem Rnd_NA_pt_idempotent (F : ℝ → Prop) (x f : ℝ)
    (hf : Rnd_NA_pt F x f) (hx : F x) : f = x :=
  Rnd_N_pt_idempotent F x f hf.1 hx

/-- Nearest rounding with ties toward zero has a unique result. -/
@[flocq_source "src/Core/Round_pred.v" 1159 "Rnd_N0_pt_unique"]
theorem Rnd_N0_pt_unique (F : ℝ → Prop) (hF0 : F 0) (x f g : ℝ)
    (hf : Rnd_N0_pt F x f) (hg : Rnd_N0_pt F x g) : f = g :=
  Rnd_NG_pt_unique F (fun x f ↦ |f| ≤ |x|) (Rnd_N0_pt_unique_prop F hF0) x f g
    ((Rnd_N0_NG_pt F hF0 x f).mp hf) ((Rnd_N0_NG_pt F hF0 x g).mp hg)

/-- A nearest value satisfying the absolute-value bound obeys ties toward zero. -/
@[flocq_source "src/Core/Round_pred.v" 1172 "Rnd_N0_pt_N"]
theorem Rnd_N0_pt_N (F : ℝ → Prop) (hF0 : F 0) (x f : ℝ)
    (hf : Rnd_N_pt F x f) (habs : |f| ≤ |x|) : Rnd_N0_pt F x f := by
  exact (Rnd_N0_NG_pt F hF0 x f).mpr ⟨hf, Or.inl habs⟩

/-- Two nearest functions with ties toward zero agree pointwise. -/
@[flocq_source "src/Core/Round_pred.v" 1225 "Rnd_N0_unique"]
theorem Rnd_N0_unique (F : ℝ → Prop) (hF0 : F 0) (rnd1 rnd2 : ℝ → ℝ)
    (h1 : Rnd_N0 F rnd1) (h2 : Rnd_N0 F rnd2) (x : ℝ) : rnd1 x = rnd2 x :=
  Rnd_N0_pt_unique F hF0 x _ _ (h1 x) (h2 x)

/-- Nearest rounding with ties toward zero is monotone when zero is representable. -/
@[flocq_source "src/Core/Round_pred.v" 1236 "Rnd_N0_pt_monotone"]
theorem Rnd_N0_pt_monotone (F : ℝ → Prop) (hF0 : F 0) :
    round_pred_monotone (Rnd_N0_pt F) := by
  intro x y f g hf hg hxy
  exact Rnd_NG_pt_monotone F (fun x f ↦ |f| ≤ |x|) (Rnd_N0_pt_unique_prop F hF0)
    x y f g ((Rnd_N0_NG_pt F hF0 x f).mp hf)
    ((Rnd_N0_NG_pt F hF0 y g).mp hg) hxy

/-- Representable inputs are fixed by nearest rounding with ties toward zero. -/
@[flocq_source "src/Core/Round_pred.v" 1248 "Rnd_N0_pt_refl"]
theorem Rnd_N0_pt_refl (F : ℝ → Prop) (x : ℝ) (hx : F x) : Rnd_N0_pt F x x := by
  refine ⟨Rnd_N_pt_refl F x hx, ?_⟩
  intro f hf
  rw [Rnd_N_pt_idempotent F x f hf hx]

/-- Nearest rounding with ties toward zero fixes representable inputs. -/
@[flocq_source "src/Core/Round_pred.v" 1262 "Rnd_N0_pt_idempotent"]
theorem Rnd_N0_pt_idempotent (F : ℝ → Prop) (x f : ℝ)
    (hf : Rnd_N0_pt F x f) (hx : F x) : f = x :=
  Rnd_N_pt_idempotent F x f hf.1 hx

end RoundNearestTies

section MonotoneImplications

/-- A monotone relation fixing zero preserves nonnegative inputs. -/
@[flocq_source "src/Core/Round_pred.v" 1275 "round_pred_ge_0"]
theorem round_pred_ge_0 (P : ℝ → ℝ → Prop) (hP : round_pred_monotone P)
    (h0 : P 0 0) (x f : ℝ) (hf : P x f) (hx : 0 ≤ x) : 0 ≤ f :=
  hP 0 x 0 f h0 hf hx

/-- Positive rounded output implies positive input for a monotone relation fixing zero. -/
@[flocq_source "src/Core/Round_pred.v" 1285 "round_pred_gt_0"]
theorem round_pred_gt_0 (P : ℝ → ℝ → Prop) (hP : round_pred_monotone P)
    (h0 : P 0 0) (x f : ℝ) (hf : P x f) (hpos : 0 < f) : 0 < x :=
  lt_of_not_ge (fun hx ↦ not_le_of_gt hpos (hP x 0 f 0 hf h0 hx))

/-- A monotone relation fixing zero preserves nonpositive inputs. -/
@[flocq_source "src/Core/Round_pred.v" 1298 "round_pred_le_0"]
theorem round_pred_le_0 (P : ℝ → ℝ → Prop) (hP : round_pred_monotone P)
    (h0 : P 0 0) (x f : ℝ) (hf : P x f) (hx : x ≤ 0) : f ≤ 0 :=
  hP x 0 f 0 hf h0 hx

/-- Negative rounded output implies negative input for a monotone relation fixing zero. -/
@[flocq_source "src/Core/Round_pred.v" 1308 "round_pred_lt_0"]
theorem round_pred_lt_0 (P : ℝ → ℝ → Prop) (hP : round_pred_monotone P)
    (h0 : P 0 0) (x f : ℝ) (hf : P x f) (hneg : f < 0) : x < 0 :=
  lt_of_not_ge (fun hx ↦ not_le_of_gt hneg (hP 0 x 0 f h0 hf hx))

end MonotoneImplications

section FormatEquivalence

/-- Local format agreement transfers downward rounding when the lower endpoint belongs. -/
@[flocq_source "src/Core/Round_pred.v" 1321 "Rnd_DN_pt_equiv_format"]
theorem Rnd_DN_pt_equiv_format (F1 F2 : ℝ → Prop) (a b : ℝ) (ha : F1 a)
    (hF : ∀ x, a ≤ x ∧ x ≤ b → (F1 x ↔ F2 x)) (x f : ℝ)
    (hx : a ≤ x ∧ x ≤ b) (hf : Rnd_DN_pt F1 x f) : Rnd_DN_pt F2 x f := by
  rcases hx with ⟨hax, hxb⟩
  rcases hf with ⟨HfF1, hf_le_x, hmax1⟩
  -- First show that f lies in the interval [a,b].
  have ha_le_f : a ≤ f := hmax1 a ha hax
  have hf_le_b : f ≤ b := le_trans hf_le_x hxb
  have hf_interval : a ≤ f ∧ f ≤ b := ⟨ha_le_f, hf_le_b⟩
  -- Use format equivalence on [a,b] to transfer F1 f to F2 f.
  have HfF2 : F2 f := (hF f hf_interval).mp HfF1
  -- Assemble the DN-point for F2: membership, inequality, and maximality.
  refine And.intro HfF2 ?rest
  refine And.intro hf_le_x ?max2
  -- Prove maximality over F2 using the equivalence on [a,b] and maximality over F1.
  intro k HkF2 hk_le_x
  -- Split whether k is below a or within [a,b].
  by_cases hk_lt_a : k < a
  · -- If k < a ≤ f then k ≤ f immediately.
    exact le_trans (le_of_lt hk_lt_a) ha_le_f
  · -- Otherwise a ≤ k; also k ≤ b since k ≤ x ≤ b.
    have hk_ge_a : a ≤ k := le_of_not_gt hk_lt_a
    have hk_le_b : k ≤ b := le_trans hk_le_x hxb
    have hk_interval : a ≤ k ∧ k ≤ b := ⟨hk_ge_a, hk_le_b⟩
    -- Transfer membership to F1 and apply maximality there.
    have HkF1 : F1 k := (hF k hk_interval).mpr HkF2
    exact hmax1 k HkF1 hk_le_x

/-- Local format agreement transfers upward rounding when the upper endpoint belongs. -/
@[flocq_source "src/Core/Round_pred.v" 1351 "Rnd_UP_pt_equiv_format"]
theorem Rnd_UP_pt_equiv_format (F1 F2 : ℝ → Prop) (a b : ℝ) (hb : F1 b)
    (hF : ∀ x, a ≤ x ∧ x ≤ b → (F1 x ↔ F2 x)) (x f : ℝ)
    (hx : a ≤ x ∧ x ≤ b) (hf : Rnd_UP_pt F1 x f) : Rnd_UP_pt F2 x f := by
  rcases hx with ⟨hax, hxb⟩
  rcases hf with ⟨HfF1, hx_le_f, hmin1⟩
  -- Show that f lies in the interval [a,b].
  have ha_le_f : a ≤ f := le_trans hax hx_le_f
  have hf_le_b : f ≤ b := hmin1 b hb hxb
  have hf_interval : a ≤ f ∧ f ≤ b := ⟨ha_le_f, hf_le_b⟩
  -- Use format equivalence on [a,b] to transfer F1 f to F2 f.
  have HfF2 : F2 f := (hF f hf_interval).mp HfF1
  -- Assemble the UP-point for F2: membership, inequality, and minimality.
  refine And.intro HfF2 ?rest
  refine And.intro hx_le_f ?min2
  -- Prove minimality over F2 using the equivalence on [a,b] and minimality over F1.
  intro k HkF2 hx_le_k
  -- Either k ≤ b, in which case transfer membership to F1 via equivalence;
  -- otherwise, use f ≤ b < k.
  by_cases hk_le_b : k ≤ b
  · -- In this branch, a ≤ k since a ≤ x ≤ k.
    have ha_le_k : a ≤ k := le_trans hax hx_le_k
    have hk_interval : a ≤ k ∧ k ≤ b := ⟨ha_le_k, hk_le_b⟩
    have HkF1 : F1 k := (hF k hk_interval).mpr HkF2
    exact hmin1 k HkF1 hx_le_k
  · have hb_lt_k : b < k := lt_of_not_ge hk_le_b
    exact le_trans hf_le_b (le_of_lt hb_lt_k)

end FormatEquivalence

section SatisfiesAnyConsequences

/-- A format has the structural properties needed to make rounding total.

    This is the Lean counterpart of Flocq's `Round_pred.satisfies_any`.
-/
@[flocq_source "src/Core/Round_pred.v" 1382 "satisfies_any"]
inductive satisfies_any (F : ℝ → Prop) : Prop where
  | intro :
      F 0 →
      (∀ x : ℝ, F x → F (-x)) →
      round_pred_total (Rnd_DN_pt F) →
      satisfies_any F

/-- Pointwise-equivalent formats preserve `satisfies_any`.

    This restores Flocq theorem `satisfies_any_eq`.
-/
@[flocq_source "src/Core/Round_pred.v" 1387 "satisfies_any_eq"]
theorem satisfies_any_eq :
    ∀ F1 F2 : ℝ → Prop,
      (∀ x, F1 x ↔ F2 x) →
      satisfies_any F1 →
      satisfies_any F2 := by
  intro F1 F2 Heq hAny
  cases hAny with
  | intro Hzero Hsym Hrnd =>
      refine satisfies_any.intro ?zero ?sym ?total
      · exact (Heq 0).mp Hzero
      · intro x Hx
        exact (Heq (-x)).mp (Hsym x ((Heq x).mpr Hx))
      · intro x
        rcases Hrnd x with ⟨f, Hf, hf_le_x, hmax⟩
        exact ⟨f, (Heq f).mp Hf, hf_le_x, fun g Hg hg_le_x => hmax g ((Heq g).mpr Hg) hg_le_x⟩


/-- Flocq theorem `satisfies_any_imp_DN`. -/
@[flocq_source "src/Core/Round_pred.v" 1413 "satisfies_any_imp_DN"]
theorem satisfies_any_imp_DN (F : ℝ → Prop) :
    satisfies_any F →
    round_pred (Rnd_DN_pt F) := by
  intro hAny
  cases hAny with
  | intro _Hzero _Hsym Hrnd =>
      refine ⟨Hrnd, ?_⟩
      intro x y f g hx hy hxy
      rcases hx with ⟨hfF, hf_le_x, _hmax_x⟩
      rcases hy with ⟨_hgF, _hy_le_y, hmax_y⟩
      exact hmax_y f hfF (le_trans hf_le_x hxy)


/-- Flocq theorem `satisfies_any_imp_UP`. -/
@[flocq_source "src/Core/Round_pred.v" 1424 "satisfies_any_imp_UP"]
theorem satisfies_any_imp_UP (F : ℝ → Prop) :
    satisfies_any F →
    round_pred (Rnd_UP_pt F) := by
  intro hAny
  cases hAny with
  | intro _Hzero hsym hDNtotal =>
      refine ⟨?_, ?_⟩
      · intro x
        rcases hDNtotal (-x) with ⟨f, hf⟩
        refine ⟨-f, ?_⟩
        simpa [neg_neg] using Rnd_UP_pt_opp_pure F (-x) f hsym hf
      · intro x y f g hx hy hxy
        rcases hx with ⟨_hfF, _hx_le_f, hmin_x⟩
        rcases hy with ⟨hgF, hy_le_g, _hmin_y⟩
        exact hmin_x g hgF (le_trans hxy hy_le_g)


/-- Flocq theorem `satisfies_any_imp_ZR`. -/
@[flocq_source "src/Core/Round_pred.v" 1441 "satisfies_any_imp_ZR"]
theorem satisfies_any_imp_ZR (F : ℝ → Prop) :
    satisfies_any F →
    round_pred (Rnd_ZR_pt F) := by
  intro hAny
  cases hAny with
  | intro hF0 hsym hDNtotal =>
      have hAny' : satisfies_any F := satisfies_any.intro hF0 hsym hDNtotal
      refine ⟨?_, ?_⟩
      · intro x
        by_cases hx : 0 ≤ x
        · rcases hDNtotal x with ⟨f, hDN⟩
          refine ⟨f, ?_⟩
          constructor
          · intro _
            exact hDN
          · intro hxle0
            have hx_eq0 : x = 0 := le_antisymm hxle0 hx
            subst x
            have hf_eq0 : f = 0 := by
              exact le_antisymm hDN.2.1 (hDN.2.2 0 hF0 le_rfl)
            subst f
            exact ⟨hF0, le_rfl, fun g _ h0g => h0g⟩
        · rcases (satisfies_any_imp_UP F hAny').1 x with ⟨f, hUP⟩
          refine ⟨f, ?_⟩
          constructor
          · intro hx_nonneg
            exact False.elim (hx hx_nonneg)
          · intro _
            exact hUP
      · intro x y f g hx hy hxy
        by_cases hx0 : 0 ≤ x
        · have hDNx : Rnd_DN_pt F x f := (hx.1) hx0
          have hy0 : 0 ≤ y := le_trans hx0 hxy
          have hDNy : Rnd_DN_pt F y g := (hy.1) hy0
          exact hDNy.2.2 f hDNx.1 (le_trans hDNx.2.1 hxy)
        · have hUPx : Rnd_UP_pt F x f := (hx.2) (le_of_lt (lt_of_not_ge hx0))
          by_cases hy0 : 0 ≤ y
          · have hDNy : Rnd_DN_pt F y g := (hy.1) hy0
            have hxle0 : x ≤ 0 := le_of_lt (lt_of_not_ge hx0)
            have hfle0 : f ≤ 0 := hUPx.2.2 0 hF0 hxle0
            have h0leg : 0 ≤ g := hDNy.2.2 0 hF0 hy0
            exact le_trans hfle0 h0leg
          · have hUPy : Rnd_UP_pt F y g := (hy.2) (le_of_lt (lt_of_not_ge hy0))
            have hxleg : x ≤ g := le_trans hxy hUPy.2.1
            exact hUPx.2.2 g hUPy.1 hxleg


/-- Flocq `NG_existence_prop`.

    For a non-representable real number `x`, any DN/UP bracket must let the
    generic nearest predicate choose at least one endpoint.
-/
@[flocq_source "src/Core/Round_pred.v" 1478 "NG_existence_prop"]
def NG_existence_prop (F : ℝ → Prop) (P : ℝ → ℝ → Prop) : Prop :=
  ∀ x d u, ¬ F x → Rnd_DN_pt F x d → Rnd_UP_pt F x u → P x u ∨ P x d

/-- Flocq theorem `satisfies_any_imp_NG`. -/
@[flocq_source "src/Core/Round_pred.v" 1481 "satisfies_any_imp_NG"]
theorem satisfies_any_imp_NG (F : ℝ → Prop) (P : ℝ → ℝ → Prop) :
    satisfies_any F →
    NG_existence_prop F P →
    round_pred_total (Rnd_NG_pt F P) := by
  intro hAny hP x
  rcases (satisfies_any_imp_DN F hAny).1 x with ⟨d, hDN⟩
  rcases (satisfies_any_imp_UP F hAny).1 x with ⟨u, hUP⟩
  have hNearestDN (hdist : x - d ≤ u - x) : Rnd_N_pt F x d :=
    Rnd_N_pt_DN F x d u hDN hUP hdist
  have hNearestUP (hdist : u - x ≤ x - d) : Rnd_N_pt F x u :=
    Rnd_N_pt_UP F x d u hDN hUP hdist
  have hEndpoint (f : ℝ) (hf : Rnd_N_pt F x f) : f = d ∨ f = u :=
    Rnd_N_pt_DN_or_UP_eq F x d u f hDN hUP hf
  rcases lt_trichotomy (u - x) (x - d) with hlt | heq | hgt
  · refine ⟨u, ?_⟩
    have hN : Rnd_N_pt F x u := hNearestUP (le_of_lt hlt)
    refine ⟨hN, Or.inr ?_⟩
    intro f hf
    rcases hEndpoint f hf with hfd | hfu
    · subst f
      have hle_abs : |d - x| ≤ |u - x| := hf.2 u hUP.1
      have hle : x - d ≤ u - x := by
        simpa [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hDN.2.1),
          abs_of_nonneg (sub_nonneg.mpr hUP.2.1)] using hle_abs
      exact False.elim ((not_le_of_gt hlt) hle)
    · exact hfu
  · by_cases hxF : F x
    · refine ⟨x, ?_⟩
      exact Rnd_NG_pt_refl F P x hxF
    · rcases hP x d u hxF hDN hUP with hPu | hPd
      · refine ⟨u, ?_⟩
        exact ⟨hNearestUP (le_of_eq heq), Or.inl hPu⟩
      · refine ⟨d, ?_⟩
        exact ⟨hNearestDN (le_of_eq heq.symm), Or.inl hPd⟩
  · refine ⟨d, ?_⟩
    have hN : Rnd_N_pt F x d := hNearestDN (le_of_lt hgt)
    refine ⟨hN, Or.inr ?_⟩
    intro f hf
    rcases hEndpoint f hf with hfd | hfu
    · exact hfd
    · subst f
      have hle_abs : |u - x| ≤ |d - x| := hf.2 d hDN.1
      have hle : u - x ≤ x - d := by
        simpa [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hDN.2.1),
          abs_of_nonneg (sub_nonneg.mpr hUP.2.1)] using hle_abs
      exact False.elim ((not_le_of_gt hgt) hle)

/-- Flocq theorem `satisfies_any_imp_NA`. -/
@[flocq_source "src/Core/Round_pred.v" 1623 "satisfies_any_imp_NA"]
theorem satisfies_any_imp_NA (F : ℝ → Prop) :
    satisfies_any F →
    round_pred (Rnd_NA_pt F) := by
  intro hAny
  cases hAny with
  | intro hF0 hsym hDNtotal =>
      have hAny' : satisfies_any F := satisfies_any.intro hF0 hsym hDNtotal
      have hP : NG_existence_prop F (fun x f => |x| ≤ |f|) := by
        intro x d u _hxNF hDN hUP
        by_cases hx0 : 0 ≤ x
        · left
          have hu0 : 0 ≤ u := le_trans hx0 hUP.2.1
          simpa [abs_of_nonneg hx0, abs_of_nonneg hu0] using hUP.2.1
        · right
          have hxle0 : x ≤ 0 := le_of_lt (lt_of_not_ge hx0)
          have hdle0 : d ≤ 0 := le_trans hDN.2.1 hxle0
          have : -x ≤ -d := neg_le_neg hDN.2.1
          simpa [abs_of_nonpos hxle0, abs_of_nonpos hdle0] using this
      refine ⟨?_, ?_⟩
      · intro x
        rcases satisfies_any_imp_NG F (fun x f => |x| ≤ |f|) hAny' hP x with ⟨f, hNG⟩
        refine ⟨f, ?_⟩
        exact (Rnd_NA_NG_pt F hF0 x f).mpr hNG
      · exact Rnd_NA_pt_monotone F hF0

/-- Flocq theorem `satisfies_any_imp_N0`. -/
@[flocq_source "src/Core/Round_pred.v" 1659 "satisfies_any_imp_N0"]
theorem satisfies_any_imp_N0 (F : ℝ → Prop) :
    F 0 →
    satisfies_any F →
    round_pred (Rnd_N0_pt F) := by
  intro hF0 hAny
  have hP : NG_existence_prop F (fun x f => |f| ≤ |x|) := by
    intro x d u _hxNF hDN hUP
    by_cases hx0 : 0 ≤ x
    · right
      have hd0 : 0 ≤ d := hDN.2.2 0 hF0 hx0
      simpa [abs_of_nonneg hd0, abs_of_nonneg hx0] using hDN.2.1
    · left
      have hxle0 : x ≤ 0 := le_of_lt (lt_of_not_ge hx0)
      have hule0 : u ≤ 0 := hUP.2.2 0 hF0 hxle0
      have : -u ≤ -x := neg_le_neg hUP.2.1
      simpa [abs_of_nonpos hule0, abs_of_nonpos hxle0] using this
  have hTotal :
      round_pred_total (Rnd_NG_pt F (fun x f => |f| ≤ |x|)) :=
    satisfies_any_imp_NG F (fun x f => |f| ≤ |x|) hAny hP
  refine ⟨?_, ?_⟩
  · intro x
    rcases hTotal x with ⟨f, hNG⟩
    refine ⟨f, ?_⟩
    exact (Rnd_N0_NG_pt F hF0 x f).mpr hNG
  · exact Rnd_N0_pt_monotone F hF0

end SatisfiesAnyConsequences

end FloatSpec.Core.Round_pred
