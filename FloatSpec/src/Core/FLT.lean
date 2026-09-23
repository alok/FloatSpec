import FloatSpec.Linter.OmegaLinter
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

import FloatSpec.src.Core.Defs
import FloatSpec.src.Core.Generic_fmt
import FloatSpec.src.Core.Round_NE
import FloatSpec.src.Core.Ulp
import FloatSpec.src.Core.FLX
import FloatSpec.src.Core.FIX
import Mathlib.Data.Real.Basic
import Std.Do.Triple

open Real
open Std.Do
open FloatSpec.Core.Defs
open FloatSpec.Core.Raux
open FloatSpec.Core.Generic_fmt

set_option linter.coqSource true
set_option warningAsError true

namespace FloatSpec.Core.FLT

variable (prec emin : Int) [Prec_gt_0 prec]

/-- Floating-point exponent function

    The FLT exponent function combines fixed-precision behavior
    with a minimum exponent bound. It returns max(e - prec, emin),
    providing precision when possible but limiting underflow.
-/
-- Source: https://gitlab.inria.fr/flocq/flocq/-/blob/7aab8f55bceec0cfafc3b3bc0e77e0dbb5a70c5f/src/Core/FLT.v#L41
@[flocq_source "src/Core/FLT.v" 41 "FLT_exp"]
def FLT_exp (e : Int) : Int :=
  max (e - prec) emin

/-- Specification: FLT exponent calculation

    The FLT exponent function implements IEEE 754-style floating-point
    exponent calculation: it maintains precision by using e - prec
    when possible, but enforces a minimum exponent emin to prevent
    excessive underflow and maintain gradual underflow behavior.
    Local arithmetic regression for the Lean `FLT_exp` implementation.
-/
theorem FLT_exp_spec (e : Int) :
    FLT_exp prec emin e = max (e - prec) emin := by
  rfl

/-- Floating-point format predicate

    A real number x is in FLT format if it can be represented
    using the generic format with the FLT exponent function.
    This gives IEEE 754-style floating-point representation
    with both precision and minimum exponent constraints.
-/
@[flocq_local "Lean compatibility payload; Flocq uses the bounded-mantissa FLT_format"]
def FLT_format_from_generic_payload
    (beta : Int) [ValidRadix beta] (x : ℝ) : Prop :=
  0 ≤ prec ∧ generic_format beta (FLT_exp prec emin) x

/-- Exact FLoCq `FLT_format`: bounded mantissa and exponent representation. -/
-- Source: https://gitlab.inria.fr/flocq/flocq/-/blob/7aab8f55bceec0cfafc3b3bc0e77e0dbb5a70c5f/src/Core/FLT.v#L36
@[flocq_source "src/Core/FLT.v" 36 "FLT_format"]
def FLT_format (beta : Int) [ValidRadix beta] (x : ℝ) : Prop :=
  ∃ f : FlocqFloat beta,
    x = F2R f ∧
    |f.Fnum| < FloatSpec.Core.Zaux.Zpower beta prec ∧
    emin ≤ f.Fexp

/-- `Valid_exp `instance for the FLT exponent function. -/
instance FLT_exp_valid :
    FloatSpec.Core.Generic_fmt.Valid_exp (FLT_exp prec emin) := by
  refine ⟨?_⟩
  intro k
  refine And.intro ?h1 ?h2
  ·
    -- If max (k - prec) emin < k, then max (k + 1 - prec) emin ≤ k.
    intro hk
    have hprec_pos : 0 < prec := (Prec_gt_0.pos : 0 < prec)
    have hprec_ge1 : (1 : Int) ≤ prec := Int.add_one_le_iff.mpr hprec_pos
    -- From hk, we get emin ≤ k
    have hemin_le : emin ≤ k :=
      le_of_lt (lt_of_le_of_lt (le_max_right (k - prec) emin) hk)
    -- And (k + 1 - prec) ≤ k follows from 1 ≤ prec
    have hsub_nonpos : 1 - prec ≤ 0 := sub_nonpos.mpr hprec_ge1
    have hlin : k + (1 - prec) ≤ k + 0 := by grind
    have hlin' : k + 1 - prec ≤ k := by simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hlin
    -- Conclude using max_le_iff
    exact (max_le_iff.mpr ⟨hlin', hemin_le⟩)
  · intro hk
    refine And.intro ?hA ?hB
    · -- Show fexp (fexp k + 1) ≤ fexp k using 1 ≤ prec and emin ≤ fexp k
      have hprec_pos : 0 < prec := (Prec_gt_0.pos : 0 < prec)
      have hprec_ge1 : (1 : Int) ≤ prec := Int.add_one_le_iff.mpr hprec_pos
      have hsub_nonpos : 1 - prec ≤ 0 := sub_nonpos.mpr hprec_ge1
      have hlin : (FLT_exp prec emin k) + (1 - prec) ≤ (FLT_exp prec emin k) + 0 := by grind
      have hlin' : (FLT_exp prec emin k) + 1 - prec ≤ (FLT_exp prec emin k) := by
        simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hlin
      have hemin_le : emin ≤ FLT_exp prec emin k := le_max_right _ _
      -- max ((fexp k) + 1 - prec) emin ≤ fexp k
      simpa [FLT_exp] using (max_le_iff.mpr ⟨hlin', hemin_le⟩)
    · intro l hl
      -- If l ≤ fexp k and k ≤ fexp k with prec > 0, then fexp is constant and equals emin.
      have hprec_pos : 0 < prec := (Prec_gt_0.pos : 0 < prec)
      have hprec_nonneg : 0 ≤ prec := le_of_lt hprec_pos
      -- First, show fexp k = emin (small regime under hk and prec > 0)
      have hfk_eq : FLT_exp prec emin k = emin := by
        by_cases hemle : emin ≤ k - prec
        · -- Then fexp k = k - prec, but hk would force k ≤ k - prec, contradicting prec > 0
          have hf : FLT_exp prec emin k = k - prec := by simpa [FLT_exp, max_eq_left hemle]
          have hk' : k ≤ k - prec := by simpa [hf] using hk
          have h0le : (0 : Int) ≤ -prec := by
            have h' : k + 0 ≤ k + (-prec) := by
              simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hk'
            simpa using (le_of_add_le_add_left h')
          have hple0 : prec ≤ 0 := by simpa using (neg_nonneg.mp h0le)
          have : prec < prec := lt_of_le_of_lt hple0 hprec_pos
          exact (False.elim ((lt_irrefl (a := prec)) this))
        · -- Else k - prec ≤ emin, so fexp k = emin
          have : k - prec ≤ emin := le_of_not_ge hemle
          simpa [FLT_exp, max_eq_right this]
      -- From hl : l ≤ fexp k = emin, we deduce l ≤ emin
      have hl' : l ≤ emin := by
        have := hl
        simpa [hfk_eq] using this
      -- And l - prec ≤ l ≤ emin, so fexp l = emin as well
      have h_le_emin : l - prec ≤ emin := by
        have : -prec ≤ 0 := by simpa using (neg_nonpos.mpr hprec_nonneg)
        have h' := add_le_add_left this l
        have hll : l - prec ≤ l := by simpa [sub_eq_add_neg] using h'
        exact le_trans hll hl'
      have hfl : FLT_exp prec emin l = emin := by
        have : max (l - prec) emin = emin := max_eq_right h_le_emin
        simpa [FLT_exp, this]
      -- Conclude fexp l = fexp k
      simpa [hfk_eq, hfl]

instance FLT_exp_monotone :
    Monotone_exp (FLT_exp prec emin) :=
  ⟨by
    intro a b hab
    simp only [FLT_exp]
    exact max_le_max (sub_le_sub_right hab prec) le_rfl⟩

/-- Compatibility name retained for existing FloatSpec clients. -/
@[flocq_local "Lean alias for the FLT_exp_monotone instance"]
abbrev FLT_exp_mono := FLT_exp_monotone

/-
Coq (FLT.v):
Global Instance exists_NE_FLT :
  (Z.even beta = false \/ (1 < prec)%Z) ->
  Exists_NE beta FLT_exp.
-/
instance exists_NE_FLT (beta : Int) [ValidRadix beta]
    [hNE : Fact (beta % 2 ≠ 0 ∨ 1 < prec)] :
    FloatSpec.Core.RoundNE.Exists_NE beta (FLT_exp prec emin) where
  exists_ne := by
    rcases hNE.out with hodd | hprec
    · exact Or.inl hodd
    · right
      intro e
      constructor
      · intro hlarge
        unfold FLT_exp at hlarge ⊢
        rcases max_lt_iff.mp hlarge with ⟨_, hemin_lt⟩
        exact max_lt (by omega) hemin_lt
      · intro hsmall
        unfold FLT_exp at hsmall ⊢
        have hemin_ge : e ≤ emin := by
          by_contra hnot
          have hemin_lt : emin < e := lt_of_not_ge hnot
          have hmax_lt : max (e - prec) emin < e :=
            max_lt (by omega) hemin_lt
          exact (not_lt.mpr hsmall) hmax_lt
        have hfe : max (e - prec) emin = emin := by
          apply max_eq_right
          omega
        have hnext_le : emin + 1 - prec ≤ emin := by
          omega
        simpa [hfe] using max_eq_right hnext_le

/-- Specification: FLT format using generic format

    The FLT format combines the benefits of fixed-precision
    (for normal numbers) with minimum exponent protection
    (for subnormal numbers), matching IEEE 754 behavior.
-/
theorem FLT_format_from_generic_payload_spec
    (beta : Int) [ValidRadix beta] (x : ℝ) :
    FLT_format_from_generic_payload prec emin beta x ↔
      generic_format beta (FLT_exp prec emin) x := by
  have hp : 0 ≤ prec := le_of_lt (Prec_gt_0.pos : 0 < prec)
  simp [FLT_format_from_generic_payload, hp]

/-- Specification: FLT exponent function correctness

    The FLT exponent function correctly implements the IEEE 754
    exponent selection logic, choosing between precision-based
    and minimum-bounded exponents as appropriate.
    Local arithmetic regression for the Lean `FLT_exp` implementation.
-/
theorem FLT_exp_correct_spec (e : Int) :
    FLT_exp prec emin e = max (e - prec) emin := by
  rfl

/-- Legacy arithmetic regression: `Ztrunc 0 = 0`.

    This does not state `FLT_format` membership.  The translated Flocq
    structural contract is `FLT_format_satisfies_any`.
-/
theorem FLT_format_0_spec (beta : Int) [ValidRadix beta] (hβ : beta > 1) :
    FloatSpec.Core.Raux.Ztrunc (0 : ℝ) = 0 := by
  simpa using FloatSpec.Core.Generic_fmt.Ztrunc_int (0 : Int)

/-- Legacy arithmetic regression: `Ztrunc (-x) + Ztrunc x = 0`.

    This does not state `FLT_format` membership.  Actual FLT negation
    closure is a field of `FLT_format_satisfies_any`.
-/
theorem FLT_format_opp_spec (beta : Int) [ValidRadix beta] (x : ℝ) :
    FloatSpec.Core.Raux.Ztrunc (-x) + FloatSpec.Core.Raux.Ztrunc x = 0 := by
  rw [FloatSpec.Core.Generic_fmt.Ztrunc_neg]
  exact neg_add_cancel _

/-- Legacy arithmetic regression: `Ztrunc |x|` is the absolute value of `Ztrunc x`.

    This does not state `FLT_format` membership.  Actual FLT absolute-value
    closure follows from zero and negation closure in
    `FLT_format_satisfies_any`; this helper proves only an integer identity.
-/
theorem FLT_format_abs_spec (beta : Int) [ValidRadix beta] (x : ℝ) :
    FloatSpec.Core.Raux.Ztrunc (abs x) =
      Int.ofNat ((FloatSpec.Core.Raux.Ztrunc x).natAbs) := by
  -- First prove the equality on truncations
  have zabs_eq :
      (FloatSpec.Core.Raux.Ztrunc (abs x))
        = Int.ofNat ((FloatSpec.Core.Raux.Ztrunc x).natAbs) := by
    -- Expand truncation and split on the sign of x.
    -- On |x| we always take the floor branch since |x| ≥ 0.
    simp [FloatSpec.Core.Raux.Ztrunc, not_lt.mpr (abs_nonneg x)]
    by_cases hxlt : x < 0
    · -- Negative case: |x| = -x and ⌊-x⌋ = -⌈x⌉; natAbs(⌈x⌉) coerces to |-⌈x⌉|.
      have hxle : x ≤ 0 := le_of_lt hxlt
      have habs : |x| = -x := by simpa using (abs_of_neg hxlt)
      have hceil_nonpos : Int.ceil x ≤ 0 := (Int.ceil_le).mpr (by simpa using hxle)
      have hAbsCeil : |Int.ceil x| = - Int.ceil x := abs_of_nonpos hceil_nonpos
      have hNatAbsCeil : ((Int.ceil x).natAbs : Int) = |Int.ceil x| :=
        (Int.natCast_natAbs (Int.ceil x))
      simpa [habs, Int.floor_neg, hxlt, hAbsCeil, hNatAbsCeil]
    · -- Nonnegative case: |x| = x, so we compare ⌊x⌋ with its nonnegative abs.
      have hxge : 0 ≤ x := le_of_not_gt hxlt
      have hxabs : |x| = x := by simpa using (abs_of_nonneg hxge)
      have hfloor_nonneg : 0 ≤ (Int.floor x : Int) := by
        have : ((0 : Int) : ℝ) ≤ x := by simpa using hxge
        exact (Int.le_floor).mpr this
      have hAbsFloor : |Int.floor x| = Int.floor x := abs_of_nonneg hfloor_nonneg
      have hNatAbsFloor : ((Int.floor x).natAbs : Int) = |Int.floor x| :=
        (Int.natCast_natAbs (Int.floor x))
      simpa [hxabs, hxlt, hAbsFloor, hNatAbsFloor]
  exact zabs_eq

/-- Specification: FLT reduces to FLX for normal numbers

    When the precision-based exponent e - prec exceeds emin,
    FLT format behaves identically to FLX format. This captures
    the normal number range of IEEE 754 floating-point.
    Local normal-exponent comparison with FLX, not a Flocq declaration.
-/
theorem FLT_exp_FLX_spec (e : Int) (h : emin ≤ e - prec) :
    FLT_exp prec emin e = FLX.FLX_exp prec e := by
  -- Under this condition, `FLT_exp` coincides with `FLX_exp`.
  simp [FLT_exp, FLX.FLX_exp, max_eq_left h]

/-
Coq (FLT.v):
Theorem generic_format_FLT :
  forall x, FLT_format x -> generic_format beta FLT_exp x.
-/
omit [Prec_gt_0 prec] in
theorem generic_format_FLT (beta : Int) [ValidRadix beta] (x : ℝ) :
    FLT_format prec emin beta x → generic_format beta (FLT_exp prec emin) x := by
  intro hx
  rcases hx with ⟨f, rfl, hbound, hemin⟩
  by_cases hm : f.Fnum = 0
  · simp [F2R, hm, generic_format, scaled_mantissa, cexp, mag, Ztrunc]
  · have hmagm := FloatSpec.Core.Raux.mag_le_Zpower
      beta f.Fnum prec ValidRadix.valid hm hbound
    have hmag : mag beta (F2R f) = mag beta (f.Fnum : ℝ) + f.Fexp :=
      FloatSpec.Core.Float_prop.mag_F2R
      (beta := beta) f.Fnum f.Fexp ValidRadix.valid hm
    have hce : cexp beta (FLT_exp prec emin) (F2R f) ≤ f.Fexp := by
      simp only [cexp, FLT_exp]
      rw [hmag]
      exact max_le (by omega) hemin
    exact (generic_format_F2R (beta := beta) (fexp := FLT_exp prec emin)
      f.Fnum f.Fexp) ⟨ValidRadix.valid, fun _ => hce⟩

private theorem FLT_format_generic_run
    (beta : Int) [ValidRadix beta] (x : ℝ)
    (hx : generic_format beta (FLT_exp prec emin) x) :
    FLT_format prec emin beta x := by
  let m := Ztrunc (scaled_mantissa beta (FLT_exp prec emin) x)
  let e := cexp beta (FLT_exp prec emin) x
  refine ⟨(FlocqFloat.mk m e : FlocqFloat beta), ?_, ?_, ?_⟩
  · simpa [generic_format, m, e] using hx
  · have hsm := scaled_mantissa_generic
      (beta := beta) (fexp := FLT_exp prec emin) x hx
    have hsm_eq : scaled_mantissa beta (FLT_exp prec emin) x = (m : ℝ) := by
      simpa [wp, PostCond.noThrow, pure, m] using hsm
    have hlt := scaled_mantissa_lt_bpow
      (beta := beta) (fexp := FLT_exp prec emin) x ValidRadix.valid
    have hprec : 0 ≤ prec := le_of_lt (Prec_gt_0.pos : 0 < prec)
    have hpow : ((FloatSpec.Core.Zaux.Zpower beta prec : Int) : ℝ) =
        (beta : ℝ) ^ prec := by
      rw [FloatSpec.Core.Zaux.Zpower, ite_eq_left hprec, Int.cast_pow]
      exact (zpow_natCast (beta : ℝ) prec.toNat).symm.trans
        (by rw [Int.toNat_of_nonneg hprec])
    have hltR : |(m : ℝ)| < (beta : ℝ) ^ prec := by
      have hexp : mag beta x - FLT_exp prec emin (mag beta x) ≤ prec := by
        simp only [FLT_exp]
        omega
      exact lt_of_lt_of_le
        (by simpa [hsm_eq, cexp] using hlt)
        (zpow_le_zpow_right₀ (by exact_mod_cast (le_of_lt ValidRadix.valid)) hexp)
    rw [← hpow] at hltR
    change |m| < FloatSpec.Core.Zaux.Zpower beta prec
    exact (Int.cast_lt).mp (by
      show ((|m| : Int) : ℝ) < ((FloatSpec.Core.Zaux.Zpower beta prec : Int) : ℝ)
      rw [Int.cast_abs]
      exact hltR)
  · exact le_max_right _ _

/-
Coq (FLT.v):
Theorem FLT_format_generic :
  forall x, generic_format beta FLT_exp x -> FLT_format x.
-/
theorem FLT_format_generic (beta : Int) [ValidRadix beta] (x : ℝ) :
    generic_format beta (FLT_exp prec emin) x → FLT_format prec emin beta x := by
  intro hx
  exact FLT_format_generic_run (prec := prec) (emin := emin) beta x hx

/-- Compatibility specification: the exact source predicate agrees with
its generic-format characterization. -/
theorem FLT_format_spec (beta : Int) [ValidRadix beta] (x : ℝ) :
    FLT_format prec emin beta x ↔ generic_format beta (FLT_exp prec emin) x := by
  constructor
  · exact fun hx => (generic_format_FLT (prec := prec) (emin := emin) beta x) hx
  · exact FLT_format_generic_run (prec := prec) (emin := emin) beta x

/-
Coq (FLT.v):
Theorem FLT_format_satisfies_any :
  satisfies_any FLT_format.
-/
theorem FLT_format_satisfies_any (beta : Int) [ValidRadix beta] :
    FloatSpec.Core.Generic_fmt.satisfies_any (fun y => FLT_format prec emin beta y) := by
  apply FloatSpec.Core.Generic_fmt.satisfies_any_eq
    (F₁ := fun y => generic_format beta (FLT_exp prec emin) y)
  · intro x
    constructor
    · exact FLT_format_generic_run (prec := prec) (emin := emin) beta x
    · exact fun hx => (generic_format_FLT (prec := prec) (emin := emin) beta x) hx
  · exact FloatSpec.Core.Generic_fmt.generic_format_satisfies_any
      (beta := beta) (fexp := FLT_exp prec emin)

/-
Coq (FLT.v):
Theorem generic_format_FLT_bpow :
  forall e, (emin <= e)%Z -> generic_format beta FLT_exp (bpow e).
-/
theorem generic_format_FLT_bpow (beta : Int) [ValidRadix beta] (e : Int)
    (hemin_le_e : emin ≤ e) :
    generic_format beta (FLT_exp prec emin) ((beta : ℝ) ^ e) := by
  have hβ : 1 < beta := ValidRadix.valid
  -- We will use `generic_format_bpow` once we show
  -- `FLT_exp prec emin (e + 1) ≤ e`.
  have hprec_pos : 0 < prec := (Prec_gt_0.pos : 0 < prec)
  have hprec_ge1 : (1 : Int) ≤ prec := Int.add_one_le_iff.mpr hprec_pos
  have h1_sub_prec_nonpos : 1 - prec ≤ 0 := sub_nonpos.mpr hprec_ge1
  have h_e1_sub_prec_le_e : e + 1 - prec ≤ e := by
    have := add_le_add_left h1_sub_prec_nonpos e
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
  have hbound : (FLT_exp prec emin (e + 1)) ≤ e := by
    -- `max (e + 1 - prec) emin ≤ e` from the two bounds
    exact (max_le_iff.mpr ⟨h_e1_sub_prec_le_e, hemin_le_e⟩)
  -- Apply the generic lemma for powers in generic format.
  simpa [FLT_exp]
    using FloatSpec.Core.Generic_fmt.generic_format_bpow
      (beta := beta) (fexp := FLT_exp prec emin) (e := e) ⟨hβ, hbound⟩

/-
Coq (FLT.v):
Theorem FLT_format_bpow :
  forall e, (emin <= e)%Z -> FLT_format (bpow e).
-/
theorem FLT_format_bpow (beta : Int) [ValidRadix beta] (e : Int)
    (hemin_le_e : emin ≤ e) :
    FLT_format prec emin beta ((beta : ℝ) ^ e) := by
  have hβ : 1 < beta := ValidRadix.valid
  -- Show FLT_exp e ≤ e from `prec > 0` and `emin ≤ e`.
  have hprec_pos : 0 < prec := (Prec_gt_0.pos : 0 < prec)
  have hprec_nonneg : 0 ≤ prec := le_of_lt hprec_pos
  have h_e_sub_prec_le_e : e - prec ≤ e := by
    have : -prec ≤ 0 := by simpa using (neg_nonpos.mpr hprec_nonneg)
    have := add_le_add_left this e
    simpa [sub_eq_add_neg] using this
  have hfexp_le : (FLT_exp prec emin e) ≤ e :=
    (max_le_iff.mpr ⟨h_e_sub_prec_le_e, hemin_le_e⟩)
  have hgeneric := FloatSpec.Core.Generic_fmt.generic_format_bpow'
    (beta := beta) (fexp := FLT_exp prec emin) (e := e) ⟨hβ, hfexp_le⟩
  exact FLT_format_generic_run (prec := prec) (emin := emin) beta _ hgeneric

/-
Coq (FLT.v):
Theorem generic_format_FLT_FLX :
  forall x : R,
  (bpow (emin + prec - 1) <= Rabs x)%R ->
  generic_format beta (FLX_exp prec) x ->
  generic_format beta FLT_exp x.
-/
omit [Prec_gt_0 prec] in
@[flocq_source "src/Core/FLT.v" 179 "generic_format_FLT_FLX"]
theorem generic_format_FLT_FLX (beta : Int) [ValidRadix beta] (x : ℝ)
    (hx_lb : (beta : ℝ) ^ (emin + prec - 1) ≤ |x|)
    (hx_fmt : generic_format beta (FLX.FLX_exp prec) x) :
    generic_format beta (FLT_exp prec emin) x := by
  have hβ : 1 < beta := ValidRadix.valid
  -- Use the generic inclusion principle with a global lower bound e1 := emin + prec
  -- For e ≥ emin + prec, we have FLT_exp e = e - prec = FLX_exp prec e
  have hle_all : ∀ e : Int, (emin + prec - 1) < e → (FLT_exp prec emin e) ≤ (FLX.FLX_exp prec e) := by
    intro e he
    -- From emin + prec ≤ e, subtract prec from both sides
    have he' : emin + prec ≤ e := by omega
    have he_sub : emin + prec - prec ≤ e - prec := by
      exact sub_le_sub_right he' prec
    have hemin_le : emin ≤ e - prec := by
      -- Simplify left side to `emin`
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using he_sub
    simpa [FLT_exp, FLX.FLX_exp, max_eq_left hemin_le]
  -- Apply inclusion to transfer FLX-format to FLT-format under the lower bound
  have := FloatSpec.Core.Generic_fmt.generic_inclusion_ge
              (beta := beta)
              (fexp1 := FLX.FLX_exp prec)
              (fexp2 := FLT_exp prec emin)
              (e1 := emin + prec - 1)
  have hres := this hβ hle_all x hx_lb hx_fmt
  simpa using hres

/-
Coq (FLT.v):
Theorem cexp_FLT_FLX :
  forall x,
  (bpow (emin + prec - 1) <= Rabs x)%R ->
  cexp beta FLT_exp x = cexp beta (FLX_exp prec) x.
-/
omit [Prec_gt_0 prec] in
@[flocq_source "src/Core/FLT.v" 130 "cexp_FLT_FLX"]
theorem cexp_FLT_FLX (beta : Int) [ValidRadix beta] (x : ℝ)
    (hx_lb : (beta : ℝ) ^ (emin + prec - 1) ≤ |x|) :
    cexp beta (FLT_exp prec emin) x = cexp beta (FLX.FLX_exp prec) x := by
  have hβ : 1 < beta := ValidRadix.valid
  set M : Int := (FloatSpec.Core.Raux.mag beta x) with hM
  have hx_upper : |x| < (beta : ℝ) ^ M := by
    simpa [M] using FloatSpec.Core.Raux.bpow_mag_gt beta x hβ
  have h_e1_le_M : (emin + prec) ≤ M := by
    have hpow : (beta : ℝ) ^ ((emin + prec) - 1) < (beta : ℝ) ^ M :=
      lt_of_le_of_lt hx_lb hx_upper
    exact (FloatSpec.Core.Raux.bpow_lt_bpow beta (emin + prec) M hβ hpow) True.intro
  -- Under this condition, FLT_exp and FLX_exp coincide at M
  have hEqExp : FLT_exp prec emin M = FLX.FLX_exp prec M := by
    have : emin ≤ M - prec := by
      -- Subtract `prec` from both sides of (emin + prec) ≤ M
      have := sub_le_sub_right h_e1_le_M prec
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
    simpa [FLT_exp, FLX.FLX_exp, max_eq_left this]
  unfold FloatSpec.Core.Generic_fmt.cexp
  change FLT_exp prec emin M = FLX.FLX_exp prec M
  simpa [hEqExp]

end FloatSpec.Core.FLT

namespace FloatSpec.Core.FLT

variable (prec emin : Int) [Prec_gt_0 prec]

/-
Coq (FLT.v):
Lemma negligible_exp_FLT :
  exists n, negligible_exp FLT_exp = Some n /\\ (n <= emin)%Z.

Lean: prove existence of a negligible exponent bound for FLT.
-/
private lemma negligible_exp_FLT_exists (prec emin : Int) [Prec_gt_0 prec] :
    ∃ n : Int, FloatSpec.Core.Ulp.negligible_exp (fexp := FLT_exp prec emin) = some n ∧ n ≤ emin := by
  classical
  -- Build a witness that `∃ n, n ≤ fexp n` using `n = emin`.
  have hWitness : ∃ n : Int, n ≤ FLT_exp prec emin n :=
    ⟨emin, by simpa [FLT_exp] using le_max_right (emin - prec) emin⟩
  -- Use the canonical spec of `negligible_exp` and eliminate the `none` branch.
  rcases FloatSpec.Core.Ulp.negligible_exp_spec' (fexp := FLT_exp prec emin) with hnone | hsome
  · -- `none` branch contradicts `FLT_exp emin = emin`.
    rcases hnone with ⟨hEqNone, hforall⟩
    have hlt : FLT_exp prec emin emin < emin := hforall emin
    have hEq : FLT_exp prec emin emin = emin := by
      have : emin - prec ≤ emin := by
        have hprec_pos : 0 < prec := (Prec_gt_0.pos : 0 < prec)
        have : -prec ≤ 0 := neg_nonpos.mpr (le_of_lt hprec_pos)
        simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using add_le_add_left this emin
      simpa [FLT_exp, max_eq_right this]
    exact (False.elim ((lt_irrefl _ : ¬ (emin < emin)) (by simpa [hEq] using hlt)))
  · rcases hsome with ⟨n, hopt, hnle⟩
    -- Show any such witness `n` must satisfy `n ≤ emin` since `prec > 0`.
    have hprec_pos : 0 < prec := (Prec_gt_0.pos : 0 < prec)
    have hprec_ge1 : (1 : Int) ≤ prec := Int.add_one_le_iff.mpr hprec_pos
    have hcases : n ≤ n - prec ∨ n ≤ emin := by
      have : n ≤ max (n - prec) emin := by simpa [FLT_exp] using hnle
      exact (le_max_iff).1 this
    have hnot_left : ¬ (n ≤ n - prec) := by
      have hstep : n - prec ≤ n - 1 := sub_le_sub_left hprec_ge1 n
      intro hle
      have : n ≤ n - 1 := le_trans hle hstep
      have : n + 1 ≤ n := by simpa using (Int.add_le_add_right this 1)
      exact (lt_irrefl _ (Int.add_one_le_iff.mp this))
    have hle_emin : n ≤ emin := Or.resolve_left hcases hnot_left
    exact ⟨n, hopt, hle_emin⟩

theorem negligible_exp_FLT (beta : Int) [ValidRadix beta] :
    ∃ n, FloatSpec.Core.Ulp.negligible_exp (fexp := FLT_exp prec emin) = some n ∧ n ≤ emin :=
  negligible_exp_FLT_exists (prec := prec) (emin := emin)

/-
Coq (FLT.v):
Theorem generic_format_FIX_FLT :
  forall x : R,
  generic_format beta FLT_exp x ->
  generic_format beta (FIX_exp emin) x.
-/
omit [Prec_gt_0 prec] in
@[flocq_source "src/Core/FLT.v" 234 "generic_format_FIX_FLT"]
theorem generic_format_FIX_FLT (beta : Int) [ValidRadix beta] (x : ℝ)
    (hx : generic_format beta (FLT_exp prec emin) x) :
    generic_format beta (FloatSpec.Core.FIX.FIX_exp emin) x := by
  have hβ : 1 < beta := ValidRadix.valid
  classical
  -- Expand the hypothesis to the canonical F2R representation under FLT_exp
  unfold FloatSpec.Core.Generic_fmt.generic_format
    FloatSpec.Core.Generic_fmt.scaled_mantissa
    FloatSpec.Core.Generic_fmt.cexp at hx
  -- Notation for the magnitude and the FLT canonical exponent
  set M : Int := (FloatSpec.Core.Raux.mag beta x) with hM
  set e1 : Int := FLT_exp prec emin M with he1
  -- Notation for the truncated mantissa under FLT
  set m1 : Int := (FloatSpec.Core.Raux.Ztrunc (x * (beta : ℝ) ^ (-(FLT_exp prec emin M)))) with hm1
  -- Unfold F2R at the hypothesis side to obtain x = m1 * β^e1
  have hx_eq : x = ((m1 : ℝ) * (beta : ℝ) ^ e1) := by
    -- Reduce the hypothesis to a concrete equality
    -- After unfolding, hx is exactly the equality we need
    simpa [hM, he1, hm1, FloatSpec.Core.Defs.F2R]
      using hx
  -- We will prove that this very (m1, e1) also certifies FIX generic format.
  -- Use the generic F2R constructor for FIX_exp, providing the required bound.
  -- First, express that the F2R built from (m1, e1) equals x.
  have hF2R : (FloatSpec.Core.Defs.F2R (FloatSpec.Core.Defs.FlocqFloat.mk m1 e1 : FloatSpec.Core.Defs.FlocqFloat beta)) = x := by
    simpa [FloatSpec.Core.Defs.F2R] using hx_eq.symm
  -- The bound required by `generic_format_F2R` under FIX_exp reduces to `emin ≤ e1`.
  have hbound : m1 ≠ 0 →
      (FloatSpec.Core.Generic_fmt.cexp beta (FloatSpec.Core.FIX.FIX_exp (emin := emin))
          (FloatSpec.Core.Defs.F2R (FloatSpec.Core.Defs.FlocqFloat.mk m1 e1 : FloatSpec.Core.Defs.FlocqFloat beta))) ≤ e1 := by
    intro _
    -- Compute cexp under FIX: it is FIX_exp applied to the magnitude.
    -- Replace the real by x using hF2R
    have :
        (FloatSpec.Core.Generic_fmt.cexp beta (FloatSpec.Core.FIX.FIX_exp (emin := emin))
            (FloatSpec.Core.Defs.F2R (FloatSpec.Core.Defs.FlocqFloat.mk m1 e1 : FloatSpec.Core.Defs.FlocqFloat beta)))
          = FloatSpec.Core.FIX.FIX_exp (emin := emin)
              ((FloatSpec.Core.Raux.mag beta x)) := by
      simp only [FloatSpec.Core.Generic_fmt.cexp, FloatSpec.Core.Raux.mag, Id.run, pure, Bind.bind]
      -- Use hF2R to rewrite the F2R to x
      have hF2R_eq : (FloatSpec.Core.Defs.F2R { Fnum := m1, Fexp := e1 }) = x := hF2R
      simp only [hF2R_eq]
    -- Under FIX, the canonical exponent is constantly `emin`
    -- and `emin ≤ e1 = max (M - prec) emin` holds by construction.
    have hemin_le_e1 : emin ≤ e1 := by
      -- e1 = FLT_exp M = max (M - prec) emin
      simpa [he1, FLT_exp] using (le_max_right (M - prec) emin)
    -- Conclude by rewriting the computed cexp
    simpa [this]
  -- Apply the F2R generic-format constructor for FIX_exp
  -- This step packages the previous bound into the desired generic_format fact.
  -- Build the precondition pair for `generic_format_F2R` and conclude.
  have hgf := FloatSpec.Core.Generic_fmt.generic_format_F2R
              (beta := beta)
              (fexp := FloatSpec.Core.FIX.FIX_exp (emin := emin))
              (m := m1) (e := e1) ⟨hβ, hbound⟩
  -- Rewriting F2R (m1,e1) back to x as established above
  rw [← hF2R]
  exact hgf

end FloatSpec.Core.FLT

namespace FloatSpec.Core.FLT

variable (prec emin : Int) [Prec_gt_0 prec]

/-
Coq (FLT.v):
```
Theorem generic_format_FLT_FIX :
  forall x : R,
  (Rabs x <= bpow (emin + prec))%R ->
  generic_format beta (FIX_exp emin) x ->
  generic_format beta FLT_exp x.
```
-/
theorem generic_format_FLT_FIX (beta : Int) [ValidRadix beta] (x : ℝ)
    (hx_le : |x| ≤ (beta : ℝ) ^ (emin + prec))
    (hx_fmt : generic_format beta (FloatSpec.Core.FIX.FIX_exp (emin := emin)) x) :
    generic_format beta (FLT_exp prec emin) x := by
  have hβ : 1 < beta := ValidRadix.valid
  -- Use inclusion under an upper bound with e2 := emin + prec
  have hle_all : ∀ e : Int, e ≤ (emin + prec) → (FLT_exp prec emin e) ≤ (FloatSpec.Core.FIX.FIX_exp (emin := emin) e) := by
    intro e he
    -- From e ≤ emin + prec, get e - prec ≤ emin
    have : e - prec ≤ emin + prec - prec := sub_le_sub_right he prec
    have hsub : e - prec ≤ emin := by
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
    -- Then max (e - prec) emin ≤ emin and FIX_exp e = emin
    have : (FLT_exp prec emin e) ≤ emin := by
      simpa [FLT_exp] using (max_le_iff.mpr ⟨hsub, le_rfl⟩)
    simpa [FloatSpec.Core.FIX.FIX_exp] using this
  -- Apply the generic inclusion lemma (≤ case)
  have hres := FloatSpec.Core.Generic_fmt.generic_inclusion_le
                (beta := beta)
                (fexp1 := FloatSpec.Core.FIX.FIX_exp (emin := emin))
                (fexp2 := FLT_exp prec emin)
                (e2 := emin + prec)
                hβ hle_all x hx_le hx_fmt
  simpa using hres

end FloatSpec.Core.FLT

namespace FloatSpec.Core.FLT

variable (prec emin : Int) [Prec_gt_0 prec]

/-- Coq ({lit}`FLT.v`):
Theorem {lit}`ulp_FLT_0`: {lit}`ulp beta FLT_exp 0 = bpow emin`.

Lean (spec): The ULP under FLT at 0 equals {lit}`β^emin`.
-/
theorem ulp_FLT_0 (beta : Int) [ValidRadix beta] :
    FloatSpec.Core.Ulp.ulp beta (FLT_exp prec emin) 0 = (beta : ℝ) ^ emin := by
  classical
  -- From FLT, `negligible_exp` supplies a witness `n` with `n ≤ emin`.
  have ⟨n, hsome, hn_le_emin⟩ :=
    negligible_exp_FLT_exists (prec := prec) (emin := emin)
  -- Evaluate `ulp` at zero using the computed witness.
  -- Under the `some` branch, ulp 0 = β^(fexp n).
  have :
      (FloatSpec.Core.Ulp.ulp beta (FLT_exp prec emin) 0)
        = ((beta : ℝ) ^ (FLT_exp prec emin n)) := by
    simp [FloatSpec.Core.Ulp.ulp, hsome]
  -- Show that for any `n ≤ emin`, FLT_exp n = emin.
  have h_fexp_n_eq : FLT_exp prec emin n = emin := by
    -- Since `prec > 0`, we have `0 ≤ prec`, hence `n - prec ≤ n ≤ emin`.
    have hprec_pos : 0 < prec := (Prec_gt_0.pos : 0 < prec)
    have hprec_nonneg : 0 ≤ prec := le_of_lt hprec_pos
    have hsub_le_self : n - prec ≤ n := by
      have : -prec ≤ 0 := by simpa using (neg_nonpos.mpr hprec_nonneg)
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using add_le_add_left this n
    have hsub_le_emin : n - prec ≤ emin := le_trans hsub_le_self hn_le_emin
    simpa [FLT_exp, max_eq_right hsub_le_emin]
  -- Conclude by rewriting with the computed branch and simplifying the exponent.
  simpa [this, h_fexp_n_eq]

/-- Coq ({lit}`FLT.v`):
Theorem {lit}`ulp_FLT_small`:
  {lit}`forall x, Rabs x < bpow (emin + prec) -> ulp beta FLT_exp x = bpow emin`.

Lean (spec): If {lit}`|x| < β^(emin+prec)`, then ULP under FLT at x equals {lit}`β^emin`.
-/
theorem ulp_FLT_small (beta : Int) [ValidRadix beta] (x : ℝ)
    (hx_lt : |x| < (beta : ℝ) ^ (emin + prec)) :
    FloatSpec.Core.Ulp.ulp beta (FLT_exp prec emin) x = (beta : ℝ) ^ emin := by
  have hβ : 1 < beta := ValidRadix.valid
  classical
  by_cases hx0 : x = 0
  · -- Small regime at zero: this is the FLT zero lemma.
    rw [hx0]
    exact ulp_FLT_0 (prec := prec) (emin := emin) (beta := beta)
  · -- Nonzero small inputs: ulp x = β^(cexp x) and cexp x = emin under FLT bounds.
    have hx_ne : x ≠ 0 := hx0
    -- Let M be the logarithmic magnitude of x.
    set M : Int := (FloatSpec.Core.Raux.mag beta x) with hM
    -- From |x| < β^(emin+prec), deduce mag x ≤ emin + prec.
    have hM_le : M ≤ (emin + prec) := by
      -- Use `mag_le_bpow` with separate arguments and unwrap the Hoare triple.
      have hspec := FloatSpec.Core.Raux.mag_le_bpow (beta := beta) (x := x) (e := (emin + prec)) hβ hx_ne hx_lt
      have hcall := hspec trivial
      simpa [FloatSpec.Core.Raux.mag, hM, wp, PostCond.noThrow, Id.run, pure]
        using hcall
    -- Hence M - prec ≤ emin, so FLT_exp M = emin.
    have hsub_le : M - prec ≤ emin := by
      have := sub_le_sub_right hM_le prec
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
    have hfexp_eq : FLT_exp prec emin M = emin := by
      simpa [FLT_exp, max_eq_right hsub_le]
    -- Evaluate `ulp` at a nonzero input, inline `cexp`, and rewrite the exponent to `emin`.
    have hcexp_run :
        (FloatSpec.Core.Generic_fmt.cexp beta (FLT_exp prec emin) x)
          = FLT_exp prec emin ((FloatSpec.Core.Raux.mag beta x)) := by
      unfold FloatSpec.Core.Generic_fmt.cexp
      simp [FloatSpec.Core.Raux.mag]
    have hfexp_mag_eq :
        FLT_exp prec emin ((FloatSpec.Core.Raux.mag beta x)) = emin := by
      simpa [hM]
        using hfexp_eq
    have hxrun : (FloatSpec.Core.Ulp.ulp beta (FLT_exp prec emin) x) = (beta : ℝ) ^ emin := by
      unfold FloatSpec.Core.Ulp.ulp
      -- Use transitivity to show cexp = emin
      have hcexp_eq : FloatSpec.Core.Generic_fmt.cexp beta (FLT_exp prec emin) x = emin := by
        calc FloatSpec.Core.Generic_fmt.cexp beta (FLT_exp prec emin) x
          = FLT_exp prec emin (FloatSpec.Core.Raux.mag beta x) := hcexp_run
          _ = FLT_exp prec emin M := by rw [hM]
          _ = emin := hfexp_eq
      simp [hx_ne, hcexp_eq]
    exact hxrun

/-
Coq (FLT.v):
Theorem cexp_FLT_FIX :
  forall x, x <> 0%R ->
  (Rabs x < bpow (emin + prec))%R ->
  cexp beta FLT_exp x = cexp beta (FIX_exp emin) x.
-/
omit [Prec_gt_0 prec] in
@[flocq_source "src/Core/FLT.v" 217 "cexp_FLT_FIX"]
theorem cexp_FLT_FIX (beta : Int) [ValidRadix beta] (x : ℝ)
    (hx_ne : x ≠ 0) (hx_lt : |x| < (beta : ℝ) ^ (emin + prec)) :
    cexp beta (FLT_exp prec emin) x =
      cexp beta (FloatSpec.Core.FIX.FIX_exp emin) x := by
  have hβ : 1 < beta := ValidRadix.valid
  classical
  -- Let M be the logarithmic magnitude of x
  set M : Int := (FloatSpec.Core.Raux.mag beta x) with hM
  -- From |x| < β^(emin+prec), deduce mag x ≤ emin + prec
  have hM_le : M ≤ (emin + prec) := by
    have := FloatSpec.Core.Raux.mag_le_bpow (beta := beta) (x := x) (e := (emin + prec))
    have hspec := this hβ hx_ne hx_lt
    have hcall := hspec trivial
    simpa [FloatSpec.Core.Raux.mag, hM, wp, PostCond.noThrow, Id.run, pure] using hcall
  -- Hence M - prec ≤ emin, so FLT_exp M = emin
  have hsub_le : M - prec ≤ emin := by
    have := sub_le_sub_right hM_le prec
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
  have hfexp_eq : FLT_exp prec emin M = emin := by
    simpa [FLT_exp, max_eq_right hsub_le]
  -- Compute both canonical exponents and show they coincide
  have hcexp_FLT_run :
      (FloatSpec.Core.Generic_fmt.cexp beta (FLT_exp prec emin) x)
        = FLT_exp prec emin ((FloatSpec.Core.Raux.mag beta x)) := by
    unfold FloatSpec.Core.Generic_fmt.cexp
    simp [FloatSpec.Core.Raux.mag]
  have hcexp_FIX_run :
      (FloatSpec.Core.Generic_fmt.cexp beta (FloatSpec.Core.FIX.FIX_exp (emin := emin)) x)
        = (FloatSpec.Core.FIX.FIX_exp (emin := emin)) ((FloatSpec.Core.Raux.mag beta x)) := by
    unfold FloatSpec.Core.Generic_fmt.cexp
    simp [FloatSpec.Core.Raux.mag]
  have hxrun :
      (FloatSpec.Core.Generic_fmt.cexp beta (FLT_exp prec emin) x)
        = (FloatSpec.Core.Generic_fmt.cexp beta (FloatSpec.Core.FIX.FIX_exp (emin := emin)) x) := by
    simpa [hcexp_FLT_run, hcexp_FIX_run, hM, hfexp_eq, FloatSpec.Core.FIX.FIX_exp]
  simpa [wp, PostCond.noThrow, Id.run, bind, pure] using hxrun

end FloatSpec.Core.FLT

namespace FloatSpec.Core.FLT

variable (prec emin : Int) [Prec_gt_0 prec]

/-
Coq (FLT.v):
Theorem generic_format_FLT_1 :
  (emin <= 0)%Z ->
  generic_format beta FLT_exp 1.
-/
theorem generic_format_FLT_1 (beta : Int) [ValidRadix beta] (hemin_le_zero : emin ≤ 0) :
    generic_format beta (FLT_exp prec emin) 1 := by
  have hβ : 1 < beta := ValidRadix.valid
  -- We will use `generic_format_bpow` at exponent e = 0.
  -- It requires `FLT_exp (0+1) ≤ 0`, which follows from `prec > 0` and `emin ≤ 0`.
  have hprec_pos : 0 < prec := (Prec_gt_0.pos : 0 < prec)
  have hprec_ge1 : (1 : Int) ≤ prec := Int.add_one_le_iff.mpr hprec_pos
  have h1_sub_prec_nonpos : 1 - prec ≤ 0 := sub_nonpos.mpr hprec_ge1
  have hbound : (FLT_exp prec emin (0 + 1)) ≤ 0 := by
    simpa [FLT_exp] using (max_le_iff.mpr ⟨h1_sub_prec_nonpos, hemin_le_zero⟩)
  -- Apply the power lemma and rewrite `(β : ℝ)^0 = 1`.
  have h := FloatSpec.Core.Generic_fmt.generic_format_bpow
              (beta := beta) (fexp := FLT_exp prec emin) (e := (0 : Int)) ⟨hβ, hbound⟩
  simpa using h

end FloatSpec.Core.FLT

namespace FloatSpec.Core.FLT

variable (prec emin : Int) [Prec_gt_0 prec]

/-
Coq (FLT.v):
Theorem generic_format_FLX_FLT :
  forall x : R,
  generic_format beta FLT_exp x -> generic_format beta (FLX_exp prec) x.
-/
omit [Prec_gt_0 prec] in
@[flocq_source "src/Core/FLT.v" 193 "generic_format_FLX_FLT"]
theorem generic_format_FLX_FLT (beta : Int) [ValidRadix beta] (x : ℝ)
    (hx : generic_format beta (FLT_exp prec emin) x) :
    generic_format beta (FLX.FLX_exp prec) x := by
  have hβ : 1 < beta := ValidRadix.valid
  -- Use the generic inclusion on magnitude: FLX_exp ≤ FLT_exp pointwise
  have hpoint : x ≠ 0 →
      (FLX.FLX_exp prec) ((FloatSpec.Core.Raux.mag beta x))
        ≤ (FLT_exp prec emin) ((FloatSpec.Core.Raux.mag beta x)) := by
    intro _
    -- FLT_exp m = max (m - prec) emin, whereas FLX_exp m = m - prec
    -- Hence the inequality holds by `le_max_left`.
    simpa [FLT_exp, FLX.FLX_exp]
  -- Conclude via the inclusion lemma from Generic_fmt
  have hrun : (generic_format beta (FLX.FLX_exp prec) x) :=
    (FloatSpec.Core.Generic_fmt.generic_inclusion_mag
      (beta := beta)
      (fexp1 := FLT_exp prec emin)
      (fexp2 := FLX.FLX_exp prec)
      (x := x)) hβ hpoint hx
  exact hrun

end FloatSpec.Core.FLT

namespace FloatSpec.Core.FLT

variable (prec emin : Int) [Prec_gt_0 prec]

/-
Coq (FLT.v):
Theorem ulp_FLT_le:
  forall x, (bpow (emin + prec - 1) <= Rabs x)%R ->
  (ulp beta FLT_exp x <= Rabs x * bpow (1 - prec))%R.
-/
omit [Prec_gt_0 prec] in
@[flocq_source "src/Core/FLT.v" 324 "ulp_FLT_le"]
theorem ulp_FLT_le (beta : Int) [ValidRadix beta] (x : ℝ)
    (hx_lb : (beta : ℝ) ^ (emin + prec - 1) ≤ |x|) :
    FloatSpec.Core.Ulp.ulp beta (FLT_exp prec emin) x ≤ |x| * (beta : ℝ) ^ (1 - prec) := by
  have hβ : 1 < beta := ValidRadix.valid
  classical
  -- Basic positivity from 1 < beta
  have hbposℤ : (0 : Int) < beta := lt_trans Int.zero_lt_one hβ
  have hbposR : (0 : ℝ) < (beta : ℝ) := by exact_mod_cast hbposℤ
  have hbne : (beta : ℝ) ≠ 0 := ne_of_gt hbposR
  -- From the lower bound, deduce |x| > 0 hence x ≠ 0
  have hpow_pos : 0 < (beta : ℝ) ^ (emin + prec - 1) := zpow_pos hbposR _
  have hx_pos : 0 < |x| := lt_of_lt_of_le hpow_pos hx_lb
  have hx_ne : x ≠ 0 := (abs_pos).1 hx_pos
  -- Notation for the logarithmic magnitude and canonical exponent
  set M : Int := (FloatSpec.Core.Raux.mag beta x) with hM
  have hcexp_run :
      (FloatSpec.Core.Generic_fmt.cexp beta (FLT_exp prec emin) x)
        = FLT_exp prec emin ((FloatSpec.Core.Raux.mag beta x)) := by
    unfold FloatSpec.Core.Generic_fmt.cexp
    simp [FloatSpec.Core.Raux.mag]
  -- Evaluate `ulp` on a nonzero input
  have hulp_run :
      (FloatSpec.Core.Ulp.ulp beta (FLT_exp prec emin) x)
        = (beta : ℝ) ^ (FLT_exp prec emin M) := by
    unfold FloatSpec.Core.Ulp.ulp
    -- Align cexp at Id monad level
    have hcexp_eq : FloatSpec.Core.Generic_fmt.cexp beta (FLT_exp prec emin) x = FLT_exp prec emin M := by
      simp only [Id.run, ← hM] at hcexp_run ⊢
      exact hcexp_run
    simp [hx_ne, hcexp_eq]
  -- We aim to show: β^(fexp M) ≤ |x| * β^(1 - prec).
  -- Split the exponent so we can factor out β^(1 - prec).
  have hsplit :
      (beta : ℝ) ^ (FLT_exp prec emin M)
        = (beta : ℝ) ^ ((FLT_exp prec emin M) + prec + -1) * (beta : ℝ) ^ (1 + -prec) := by
    -- zpow_add₀ on (e + prec - 1) and (1 - prec), noting their sum is e
    have := zpow_add₀ hbne ((FLT_exp prec emin M) + prec + -1) (1 + -prec)
    -- Rearrange the sum in the exponent to `e`
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
      using this
  -- It suffices to show: β^( (FLT_exp M) + prec - 1 ) ≤ |x|
  have hcore : (beta : ℝ) ^ ((FLT_exp prec emin M) + prec - 1) ≤ |x| := by
    -- Case analysis on which branch of the max defines FLT_exp
    by_cases hcase : emin ≤ M - prec
    · -- Normal range: fexp M = M - prec, so exponent reduces to M - 1
      have hfexp_eq : FLT_exp prec emin M = M - prec := by
        simpa [FLT_exp, max_eq_left hcase]
      -- From `mag` lower bound: β^(M - 1) ≤ |x|
      have hcall :=
        (FloatSpec.Core.Raux.bpow_mag_le_from_exp_payload (beta := beta) (x := x) (e := M) hβ hx_ne le_rfl) trivial
      -- Simplify the returned triple and rewrite the exponent
      have hM_lb : (beta : ℝ) ^ (M - 1) ≤ |x| := by
        simpa [FloatSpec.Core.Raux.abs_val, hM, wp, PostCond.noThrow, Id.run, pure, sub_eq_add_neg]
          using hcall
      -- Convert the goal exponent using `hfexp_eq`
      simpa [hfexp_eq, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
        using hM_lb
    · -- Subnormal range: fexp M = emin, so exponent reduces to emin + prec - 1
      have hfexp_eq : FLT_exp prec emin M = emin := by
        have : M - prec ≤ emin := le_of_not_ge hcase
        simpa [FLT_exp, max_eq_right this]
      -- Use the given lower bound
      simpa [hfexp_eq, sub_eq_add_neg] using hx_lb
  -- Put everything together: multiply by the positive factor β^(1 - prec)
  have hfac_nonneg : 0 ≤ (beta : ℝ) ^ (1 - prec) := le_of_lt (zpow_pos hbposR _)
  have : (beta : ℝ) ^ (FLT_exp prec emin M)
            ≤ |x| * (beta : ℝ) ^ (1 - prec) := by
    -- Rewrite the left-hand side using `hsplit` and multiply the core bound
    have := mul_le_mul_of_nonneg_right hcore hfac_nonneg
    simpa [hsplit, mul_comm, mul_left_comm, mul_assoc, sub_eq_add_neg]
      using this
  have hout : (FloatSpec.Core.Ulp.ulp beta (FLT_exp prec emin) x)
                ≤ |x| * (beta : ℝ) ^ (1 - prec) := by
    rw [hulp_run]
    exact this
  exact hout

/-
Coq (FLT.v):
Theorem ulp_FLT_gt:
  forall x, (Rabs x * bpow (-prec) < ulp beta FLT_exp x)%R.
-/
theorem ulp_FLT_gt (beta : Int) [ValidRadix beta] (x : ℝ) :
    |x| * (beta : ℝ) ^ (-prec) < FloatSpec.Core.Ulp.ulp beta (FLT_exp prec emin) x := by
  classical
  have hβ : 1 < beta := ValidRadix.valid
  -- Basic positivity facts from 1 < beta
  have hbposℤ : (0 : Int) < beta := lt_trans Int.zero_lt_one hβ
  have hbposR : (0 : ℝ) < (beta : ℝ) := by exact_mod_cast hbposℤ
  have hb_nonneg : 0 ≤ (beta : ℝ) := le_of_lt hbposR
  have hfac_nonneg : 0 ≤ (beta : ℝ) ^ (-prec) := le_of_lt (zpow_pos hbposR _)
  by_cases hx : x = 0
  · -- Zero case: ulp equals β^emin and the left-hand side is 0
    have hulp0 :
        (FloatSpec.Core.Ulp.ulp beta (FLT_exp prec emin) 0) = (beta : ℝ) ^ emin := by
      -- Use the dedicated zero lemma
      exact ulp_FLT_0 (prec := prec) (emin := emin) (beta := beta)
    -- Show 0 ≤ β^emin using positivity of the base
    have hpow_pos : 0 < (beta : ℝ) ^ emin := zpow_pos hbposR _
    have : |x| * (beta : ℝ) ^ (-prec) < (FloatSpec.Core.Ulp.ulp beta (FLT_exp prec emin) x) := by
      -- Left-hand side is 0; right-hand side is strictly positive
      have hpow_nonneg : 0 ≤ (beta : ℝ) ^ emin := le_of_lt hpow_pos
      simp only [hx, abs_zero, zero_mul]
      rw [hulp0]
      exact hpow_pos
    exact this
  · -- Nonzero case: ulp x = β^(cexp x) and cexp = FLT_exp (mag x)
    have hx_ne : x ≠ 0 := hx
    -- Evaluate cexp on x
    have hcexp_run :
        (FloatSpec.Core.Generic_fmt.cexp beta (FLT_exp prec emin) x)
          = FLT_exp prec emin ((FloatSpec.Core.Raux.mag beta x)) := by
      unfold FloatSpec.Core.Generic_fmt.cexp
      simp [FloatSpec.Core.Raux.mag]
    -- Evaluate ulp on a nonzero input
    have hulp_run :
        (FloatSpec.Core.Ulp.ulp beta (FLT_exp prec emin) x)
          = (beta : ℝ) ^ ((FloatSpec.Core.Generic_fmt.cexp beta (FLT_exp prec emin) x)) := by
      -- Use the generic `ulp_neq_0` lemma
      have h := (FloatSpec.Core.Ulp.ulp_neq_0 (beta := beta) (fexp := FLT_exp prec emin) x hx_ne) (by exact True.intro)
      simpa [wp, PostCond.noThrow, Id.run, bind, pure] using h
    -- Abbreviation: M = mag beta x
    set M : Int := (FloatSpec.Core.Raux.mag beta x) with hM
    -- Goal reduces to bounding |x| by β^M and then using monotonicity of bpow
    -- Step 1: |x| ≤ β^M (by definition of mag via ceiling)
    -- Let L := log |x| / log β; then M = ⌈L⌉ and hence L ≤ M.
    have hlogβ_pos : 0 < Real.log (beta : ℝ) := by
      have : 0 < Real.log (beta : ℝ) ↔ 1 < (beta : ℝ) :=
        Real.log_pos_iff (x := (beta : ℝ)) (le_of_lt hbposR)
      exact this.mpr (by exact_mod_cast hβ)
    have hlogβ_ne : Real.log (beta : ℝ) ≠ 0 := ne_of_gt hlogβ_pos
    have hx_pos : 0 < |x| := by simpa using (abs_pos.mpr hx_ne)
    set L : ℝ := Real.log (abs x) / Real.log (beta : ℝ) with hLdef
    have hM_run : M = Int.floor L + 1 := by
      have : (FloatSpec.Core.Raux.mag beta x) = Int.floor L + 1 := by
        simp [FloatSpec.Core.Raux.mag, hx_ne, hLdef]
      simpa [hM] using this
    -- From L ≤ ⌊L⌋ + 1, deduce |x| ≤ β^M
    have h_abs_lt : |x| < (beta : ℝ) ^ M := by
      -- Multiply by log β and identify L * log β = log |x|
      have hfloor_ge : (L : ℝ) ≤ (Int.floor L : ℝ) + 1 := by
        have : L ≤ Int.ceil L := Int.le_ceil L
        have : (Int.ceil L : ℝ) ≤ (Int.floor L : ℝ) + 1 := by exact_mod_cast Int.ceil_le_floor_add_one L
        linarith
      have hmul_le : L * Real.log (beta : ℝ) ≤ ((Int.floor L : ℝ) + 1) * Real.log (beta : ℝ) :=
        mul_le_mul_of_nonneg_right hfloor_ge (le_of_lt hlogβ_pos)
      have hL_mul : L * Real.log (beta : ℝ) = Real.log (abs x) := by
        have hne : Real.log (beta : ℝ) ≠ 0 := ne_of_gt hlogβ_pos
        calc
          L * Real.log (beta : ℝ)
              = (Real.log (abs x) / Real.log (beta : ℝ)) * Real.log (beta : ℝ) := by
                  simpa [hLdef]
          _   = Real.log (abs x) := by
                  simpa [hne, div_mul_eq_mul_div] using
                    (mul_div_cancel' (Real.log (abs x)) (Real.log (beta : ℝ)))
      -- Relate log(β^M) to M * log β
      have hlog_zpow_M : Real.log ((beta : ℝ) ^ M) = (M : ℝ) * Real.log (beta : ℝ) := by
        simpa using Real.log_zpow hbposR M
      -- Get log |x| ≤ log (β^M)
      have hlog_le : Real.log (abs x) ≤ Real.log ((beta : ℝ) ^ M) := by
        have : Real.log (abs x) ≤ (M : ℝ) * Real.log (beta : ℝ) := by
          simpa [hL_mul, hM_run] using hmul_le
        simpa [hlog_zpow_M] using this
      -- Move back via exp and rewrite β^M
      have hxpos' : 0 < abs x := hx_pos
      have h_exp_le : abs x ≤ Real.exp ((M : ℝ) * Real.log (beta : ℝ)) := by
        have := (Real.log_le_iff_le_exp hxpos').1 hlog_le
        simpa [hlog_zpow_M] using this
      have hpow_pos : 0 < (beta : ℝ) ^ M := zpow_pos hbposR _
      have h_exp_eq_pow : Real.exp ((M : ℝ) * Real.log (beta : ℝ)) = (beta : ℝ) ^ M := by
        have : Real.exp (Real.log ((beta : ℝ) ^ M)) = (beta : ℝ) ^ M := Real.exp_log hpow_pos
        simpa [hlog_zpow_M] using this
      have h_abs_le : abs x ≤ (beta : ℝ) ^ M := by
        simpa [h_exp_eq_pow] using h_exp_le
      exact lt_of_le_of_ne h_abs_le (by
        intro heq
        have hlogeq : Real.log (abs x) = (M : ℝ) * Real.log (beta : ℝ) := by
          rw [heq]
          exact hlog_zpow_M
        have hLeq : L = (M : ℝ) := by
          rw [hLdef]
          apply (div_eq_iff hlogβ_ne).2
          simpa [mul_comm] using hlogeq
        have hMcast : (M : ℝ) = (Int.floor L : ℝ) + 1 := by
          exact_mod_cast hM_run
        have hfloor_eq : L = (Int.floor L : ℝ) + 1 := by
          exact hLeq.trans hMcast
        exact (ne_of_lt (Int.lt_floor_add_one L)) hfloor_eq)
    -- Step 2: β^(M - prec) ≤ β^(FLT_exp M)
    have hmono_pow : (beta : ℝ) ^ (M - prec) ≤ (beta : ℝ) ^ (FLT_exp prec emin M) := by
      -- Monotonicity of zpow on nonnegative bases
      have hb_ge1 : (1 : ℝ) ≤ (beta : ℝ) := by exact_mod_cast (le_of_lt hβ)
      have hle_exp : M - prec ≤ FLT_exp prec emin M := by
        -- Since FLT_exp M = max (M - prec) emin
        simpa [FLT_exp] using (le_max_left (M - prec) emin)
      exact zpow_le_zpow_right₀ hb_ge1 hle_exp
    -- Multiply both sides of Step 1 by β^(-prec) ≥ 0 to get
    -- |x| * β^(-prec) ≤ β^M * β^(-prec) = β^(M - prec)
    have hscaled : |x| * (beta : ℝ) ^ (-prec) < (beta : ℝ) ^ (M - prec) := by
      have hmul :
          |x| * (beta : ℝ) ^ (-prec) <
            (beta : ℝ) ^ M * (beta : ℝ) ^ (-prec) :=
        mul_lt_mul_of_pos_right h_abs_lt (zpow_pos hbposR (-prec))
      simpa [sub_eq_add_neg, zpow_add₀ (ne_of_gt hbposR)] using hmul
    -- Combine with Step 2 and rewrite ulp on the right-hand side
    have : |x| * (beta : ℝ) ^ (-prec)
            < (beta : ℝ) ^ (FLT_exp prec emin M) :=
      lt_of_lt_of_le hscaled hmono_pow
    -- Transport along the `cexp` and `ulp` evaluations computed above
    have : |x| * (beta : ℝ) ^ (-prec)
            < (FloatSpec.Core.Ulp.ulp beta (FLT_exp prec emin) x) := by
      rw [hulp_run, hcexp_run]
      exact this
    exact this

/-
Coq (FLT.v):
Lemma ulp_FLT_exact_shift:
  forall x e,
  (x <> 0)%R ->
  (emin + prec <= mag beta x)%Z ->
  (emin + prec - mag beta x <= e)%Z ->
  (ulp beta FLT_exp (x * bpow e) = ulp beta FLT_exp x * bpow e)%R.
-/
omit [Prec_gt_0 prec] in
@[flocq_source "src/Core/FLT.v" 366 "ulp_FLT_exact_shift"]
theorem ulp_FLT_exact_shift (beta : Int) [ValidRadix beta] (x : ℝ) (e : Int)
    (hx_ne : x ≠ 0) (hMx_lb : emin + prec ≤ FloatSpec.Core.Raux.mag beta x)
    (hshift : emin + prec - FloatSpec.Core.Raux.mag beta x ≤ e) :
    FloatSpec.Core.Ulp.ulp beta (FLT_exp prec emin) (x * (beta : ℝ) ^ e) =
      FloatSpec.Core.Ulp.ulp beta (FLT_exp prec emin) x * (beta : ℝ) ^ e := by
  have hβ : 1 < beta := ValidRadix.valid
  classical
  -- Basic facts about the base and the scaled input
  have hbposℤ : (0 : Int) < beta := lt_trans Int.zero_lt_one hβ
  have hbposR : (0 : ℝ) < (beta : ℝ) := by exact_mod_cast hbposℤ
  have hbne : (beta : ℝ) ≠ 0 := ne_of_gt hbposR
  have hpow_ne : (beta : ℝ) ^ e ≠ 0 := by
    simpa using (zpow_ne_zero e hbne)
  have hy_ne : x * (beta : ℝ) ^ e ≠ 0 := mul_ne_zero hx_ne hpow_ne
  -- Notations for magnitudes
  set M : Int := (FloatSpec.Core.Raux.mag beta x) with hM
  set N : Int := (FloatSpec.Core.Raux.mag beta (x * (beta : ℝ) ^ e)) with hN
  -- Evaluate ulp on both sides (nonzero branch)
  have hcexp_x :
      (FloatSpec.Core.Generic_fmt.cexp beta (FLT_exp prec emin) x)
        = FLT_exp prec emin M := by
    unfold FloatSpec.Core.Generic_fmt.cexp
    simp [FloatSpec.Core.Raux.mag, hM]
  have hcexp_y :
      (FloatSpec.Core.Generic_fmt.cexp beta (FLT_exp prec emin) (x * (beta : ℝ) ^ e))
        = FLT_exp prec emin N := by
    unfold FloatSpec.Core.Generic_fmt.cexp
    simp [FloatSpec.Core.Raux.mag, hN]
  have hulp_x :
      (FloatSpec.Core.Ulp.ulp beta (FLT_exp prec emin) x)
        = (beta : ℝ) ^ (FLT_exp prec emin M) := by
    unfold FloatSpec.Core.Ulp.ulp
    have hcexp_eq : FloatSpec.Core.Generic_fmt.cexp beta (FLT_exp prec emin) x = FLT_exp prec emin M := by
      exact hcexp_x
    simp [hx_ne, hcexp_eq]
  have hulp_y :
      (FloatSpec.Core.Ulp.ulp beta (FLT_exp prec emin) (x * (beta : ℝ) ^ e))
        = (beta : ℝ) ^ (FLT_exp prec emin N) := by
    unfold FloatSpec.Core.Ulp.ulp
    have hcexp_eq : FloatSpec.Core.Generic_fmt.cexp beta (FLT_exp prec emin) (x * (beta : ℝ) ^ e) = FLT_exp prec emin N := by
      exact hcexp_y
    simp [hy_ne, hcexp_eq]
  -- Relate magnitudes under scaling directly: N = M + e
  have hN_eq : N = M + e := by
    -- Notation for logarithmic magnitude
    set L : ℝ := Real.log (abs x) / Real.log (beta : ℝ)
    have hx_ne' : x ≠ 0 := hx_ne
    have hM_run : M = Int.floor L + 1 := by
      simp [FloatSpec.Core.Raux.mag, hM, hx_ne', L]
    -- Rewrite mag at the scaled input and compute its ceiling form
    have hbpos : 0 < (beta : ℝ) := by exact_mod_cast hbposℤ
    have hdiv :
        Real.log (abs (x * (beta : ℝ) ^ e)) / Real.log (beta : ℝ)
          = L + (e : ℝ) := by
      -- Algebra: log |x * β^e| = log |x| + e * log β, then divide by log β
      have hbpow_pos : 0 < (beta : ℝ) ^ e := zpow_pos hbpos _
      have hxabs_pos : 0 < |x| := abs_pos.mpr hx_ne'
      have hbpow_abs_pos : 0 < |(beta : ℝ) ^ e| := abs_pos.mpr (ne_of_gt hbpow_pos)
      have hlog_prod :
          Real.log (|x| * |(beta : ℝ) ^ e|)
            = Real.log (|x|) + (e : ℝ) * Real.log (beta : ℝ) := by
        calc
          Real.log (|x| * |(beta : ℝ) ^ e|)
              = Real.log (|x|) + Real.log (|(beta : ℝ) ^ e|) := by
                    simpa using Real.log_mul (ne_of_gt hxabs_pos) (ne_of_gt hbpow_abs_pos)
          _   = Real.log (|x|) + Real.log ((beta : ℝ) ^ e) := by
                    simpa [abs_of_nonneg (le_of_lt hbpow_pos)]
          _   = Real.log (|x|) + (e : ℝ) * Real.log (beta : ℝ) := by
                    simpa using Real.log_zpow hbpos e
      have habs_mul : abs (x * (beta : ℝ) ^ e) = |x| * |(beta : ℝ) ^ e| := by
        have hbnonneg : 0 ≤ (beta : ℝ) ^ e := le_of_lt hbpow_pos
        simp [abs_mul, abs_of_nonneg hbnonneg]
      have hlogβ_pos : 0 < Real.log (beta : ℝ) := by
        have : 0 < Real.log (beta : ℝ) ↔ 1 < (beta : ℝ) :=
          Real.log_pos_iff (x := (beta : ℝ)) (le_of_lt hbpos)
        have hβR : (1 : ℝ) < (beta : ℝ) := by exact_mod_cast hβ
        simpa using this.mpr hβR
      have hlogβ_ne : Real.log (beta : ℝ) ≠ 0 := ne_of_gt hlogβ_pos
      have hmul_div : ((e : ℝ) * Real.log (beta : ℝ)) / Real.log (beta : ℝ) = (e : ℝ) := by
        simpa [hlogβ_ne] using (mul_div_cancel' (e : ℝ) (Real.log (beta : ℝ)))
      calc
        Real.log (abs (x * (beta : ℝ) ^ e)) / Real.log (beta : ℝ)
            = Real.log (|x| * |(beta : ℝ) ^ e|) / Real.log (beta : ℝ) := by simpa [habs_mul]
        _   = (Real.log (|x|) + (e : ℝ) * Real.log (beta : ℝ)) / Real.log (beta : ℝ) := by
                rw [hlog_prod]
        _   = Real.log (|x|) / Real.log (beta : ℝ)
                + ((e : ℝ) * Real.log (beta : ℝ)) / Real.log (beta : ℝ) := by
                simpa using (add_div (Real.log (|x|)) ((e : ℝ) * Real.log (beta : ℝ)) (Real.log (beta : ℝ)))
        _   = L + (e : ℝ) := by simpa [L, hmul_div]
    have hN_run : N = Int.floor (L + (e : ℝ)) + 1 := by
      have hy_ne' : x * (beta : ℝ) ^ e ≠ 0 := hy_ne
      -- First, rewrite the floor of the logarithm using hdiv
      have hfloor_div :
          Int.floor (Real.log (abs (x * (beta : ℝ) ^ e)) / Real.log (beta : ℝ))
            = Int.floor (L + (e : ℝ)) := by
        simpa using congrArg Int.floor hdiv
      -- Then fold back the definition of mag in the nonzero branch
      have : (FloatSpec.Core.Raux.mag beta (x * (beta : ℝ) ^ e))
              = Int.floor (L + (e : ℝ)) + 1 := by
        simp only [FloatSpec.Core.Raux.mag, hy_ne', ite_false, Id.run, pure, hfloor_div]
      simpa [hN] using this
    -- Conclude N = M + e via floors arithmetic
    -- Key fact: ⌊L + e⌋ = ⌊L⌋ + e for integer e
    have hfloor_add : Int.floor (L + (e : ℝ)) = Int.floor L + e :=
      Int.floor_add_intCast L e
    have hN_eq' : N = M + e := by
      rw [hN_run, hfloor_add, hM_run]
      ring
    exact hN_eq'
  -- Given N = M + e and the bounds on M, both maxima are in the linear branch
  have hM_large : emin ≤ M - prec := by
    -- From emin + prec ≤ M
    have := sub_le_sub_right hMx_lb prec
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
  have hN_large : emin ≤ N - prec := by
    -- From emin + prec - M ≤ e and N = M + e, we get emin ≤ N - prec
    have : emin + prec ≤ M + e := by
      -- rearrange the hypothesis hshift
      have := add_le_add_right hshift M
      -- M + (emin + prec - M) ≤ M + e ⇒ emin + prec ≤ M + e
      simpa [add_comm, add_left_comm, add_assoc, sub_eq_add_neg] using this
    -- Now subtract prec on both sides
    have := sub_le_sub_right this prec
    simpa [hN_eq, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
  -- Compute the exponents
  have hExp_y : FLT_exp prec emin N = N - prec := by simpa [FLT_exp, max_eq_left hN_large]
  have hExp_x : FLT_exp prec emin M = M - prec := by simpa [FLT_exp, max_eq_left hM_large]
  -- Conclude by rewriting powers and using zpow_add₀
  have : (FloatSpec.Core.Ulp.ulp beta (FLT_exp prec emin) (x * (beta : ℝ) ^ e))
            = (FloatSpec.Core.Ulp.ulp beta (FLT_exp prec emin) x) * (beta : ℝ) ^ e := by
    -- Express both sides in terms of powers of β and use exponent arithmetic.
    have hExp_eq : FLT_exp prec emin N = (FLT_exp prec emin M) + e := by
      -- Rewrite both exponents to linear forms and use N = M + e
      have : N - prec = (M - prec) + e := by
        simpa [hN_eq, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
      simpa [hExp_y, hExp_x] using this
    -- (β^ (a + e)) = (β^a) * (β^e)
    have hzadd := zpow_add₀ hbne (FLT_exp prec emin M) e
    -- Put everything together and rewrite ulp runs
    have hpow_eq : (beta : ℝ) ^ (FLT_exp prec emin N) = (beta : ℝ) ^ (FLT_exp prec emin M) * (beta : ℝ) ^ e := by
      rw [hExp_eq, hzadd]
    rw [hulp_y, hulp_x]
    exact hpow_eq
  exact this

end FloatSpec.Core.FLT

namespace FloatSpec.Core.FLT

variable (prec emin : Int) [Prec_gt_0 prec]

/-
Coq (FLT.v):
Theorem round_FLT_FLX : forall rnd x,
  (bpow (emin + prec - 1) <= Rabs x)%R ->
  round beta FLT_exp rnd x = round beta (FLX_exp prec) rnd x.

Lean (spec): Under the lower-bound condition on |x|, rounding in
FLT equals rounding in FLX for any rounding predicate `rnd`.
-/
omit [Prec_gt_0 prec] in
@[flocq_source "src/Core/FLT.v" 207 "round_FLT_FLX"]
theorem round_FLT_FLX (beta : Int) [ValidRadix beta] (rnd : ℝ → Int) (x : ℝ) :
    (beta : ℝ) ^ (emin + prec - 1) ≤ |x| →
      round_to_generic (beta := beta) (fexp := FLT_exp prec emin) (mode := rnd) x =
      round_to_generic (beta := beta) (fexp := FLX.FLX_exp prec) (mode := rnd) x := by
  intro hx
  have hmag : emin + prec ≤ FloatSpec.Core.Raux.mag beta x :=
    FloatSpec.Core.Raux.mag_ge_bpow beta x (emin + prec) ValidRadix.valid hx
  have hexp :
      FLT_exp prec emin (FloatSpec.Core.Raux.mag beta x) =
        FLX.FLX_exp prec (FloatSpec.Core.Raux.mag beta x) := by
    simp only [FLT_exp, FLX.FLX_exp]
    rw [max_eq_left]
    omega
  simp only [round_to_generic, FloatSpec.Core.Generic_fmt.roundR,
    FloatSpec.Core.Generic_fmt.scaled_mantissa,
    FloatSpec.Core.Generic_fmt.cexp]
  rw [hexp]

end FloatSpec.Core.FLT

namespace FloatSpec.Core.FLT

variable (prec emin : Int) [Prec_gt_0 prec]

/-
Coq (FLT.v):
Lemma succ_FLT_exact_shift_pos:
  forall x e,
  (0 < x)%R ->
  (emin + prec <= mag beta x)%Z ->
  (emin + prec - mag beta x <= e)%Z ->
  (succ beta FLT_exp (x * bpow e) = succ beta FLT_exp x * bpow e)%R.
-/
omit [Prec_gt_0 prec] in
@[flocq_source "src/Core/FLT.v" 381 "succ_FLT_exact_shift_pos"]
theorem succ_FLT_exact_shift_pos (beta : Int) [ValidRadix beta] (x : ℝ) (e : Int)
    (hx_pos : 0 < x) (hMx_lb : emin + prec ≤ FloatSpec.Core.Raux.mag beta x)
    (hshift : emin + prec - FloatSpec.Core.Raux.mag beta x ≤ e) :
    FloatSpec.Core.Ulp.succ beta (FLT_exp prec emin) (x * (beta : ℝ) ^ e) =
      FloatSpec.Core.Ulp.succ beta (FLT_exp prec emin) x * (beta : ℝ) ^ e := by
  classical
  have hβ : 1 < beta := ValidRadix.valid
  -- Basic positivity facts from beta > 1
  have hbposℤ : (0 : Int) < beta := lt_trans Int.zero_lt_one hβ
  have hbposR : (0 : ℝ) < (beta : ℝ) := by exact_mod_cast hbposℤ
  -- Positivity of the scaled input and nonnegativity for selecting the `succ` branch
  have hy_pos : 0 < x * (beta : ℝ) ^ e := mul_pos hx_pos (zpow_pos hbposR e)
  have hy_nonneg : 0 ≤ x * (beta : ℝ) ^ e := le_of_lt hy_pos
  have hx_nonneg : 0 ≤ x := le_of_lt hx_pos
  -- Abbreviations for magnitudes
  set M : Int := (FloatSpec.Core.Raux.mag beta x) with hM
  -- We will use `ulp_FLT_exact_shift` (proved above).
  -- Its magnitude and shift hypotheses are exactly the ones available here.
  have hMx_lb : emin + prec ≤ M := by simpa [M] using hMx_lb
  have hshift : emin + prec - M ≤ e := by simpa [M] using hshift
  -- Evaluate `succ` in the positive branch and use the ULP scaling lemma
  have hsucc_y_run : (FloatSpec.Core.Ulp.succ beta (FLT_exp prec emin) (x * (beta : ℝ) ^ e))
                      = x * (beta : ℝ) ^ e + (FloatSpec.Core.Ulp.ulp beta (FLT_exp prec emin) (x * (beta : ℝ) ^ e)) := by
    unfold FloatSpec.Core.Ulp.succ
    simp [hy_nonneg]
  have hsucc_x_run : (FloatSpec.Core.Ulp.succ beta (FLT_exp prec emin) x)
                      = x + (FloatSpec.Core.Ulp.ulp beta (FLT_exp prec emin) x) := by
    unfold FloatSpec.Core.Ulp.succ
    simp [hx_nonneg]
  -- Apply ULP exact shift to relate ulp at x and at the scaled input
  have hulp_shift :
      (FloatSpec.Core.Ulp.ulp beta (FLT_exp prec emin) (x * (beta : ℝ) ^ e))
        = (FloatSpec.Core.Ulp.ulp beta (FLT_exp prec emin) x) * (beta : ℝ) ^ e := by
    exact ulp_FLT_exact_shift (prec := prec) (emin := emin) beta x e
      (ne_of_gt hx_pos) hMx_lb hshift
  -- Combine the two real equalities.
  have hsucc_run_eq : (FloatSpec.Core.Ulp.succ beta (FLT_exp prec emin) (x * (beta : ℝ) ^ e))
            = ((FloatSpec.Core.Ulp.succ beta (FLT_exp prec emin) x)) * (beta : ℝ) ^ e := by
    -- Expand both sides using the `succ` evaluations and the ULP shift
    rw [hsucc_y_run, hsucc_x_run, hulp_shift]
    ring
  exact hsucc_run_eq

/-
Coq (FLT.v):
Lemma succ_FLT_exact_shift:
  forall x e,
  (x <> 0)%R ->
  (emin + prec + 1 <= mag beta x)%Z ->
  (emin + prec - mag beta x + 1 <= e)%Z ->
(succ beta FLT_exp (x * bpow e) = succ beta FLT_exp x * bpow e)%R.
-/
-- Auxiliary lemma: pred exact shift for positive inputs (used to handle negative `x` for succ)
omit [Prec_gt_0 prec] in
private theorem pred_FLT_exact_shift_pos_aux (beta : Int) [ValidRadix beta] (x : ℝ) (e : Int)
    (hx_pos : 0 < x) (hMx_lb1 : emin + prec + 1 ≤ FloatSpec.Core.Raux.mag beta x)
    (hshift1 : emin + prec - FloatSpec.Core.Raux.mag beta x + 1 ≤ e) :
    FloatSpec.Core.Ulp.pred beta (FLT_exp prec emin) (x * (beta : ℝ) ^ e) =
      FloatSpec.Core.Ulp.pred beta (FLT_exp prec emin) x * (beta : ℝ) ^ e := by
  have hβ : 1 < beta := ValidRadix.valid
  classical
  have hbposℤ : (0 : Int) < beta := lt_trans Int.zero_lt_one hβ
  have hbposR : (0 : ℝ) < (beta : ℝ) := by exact_mod_cast hbposℤ
  have hbne : (beta : ℝ) ≠ 0 := ne_of_gt hbposR
  have hpow_pos : 0 < (beta : ℝ) ^ e := zpow_pos hbposR e
  have hpow_ne : (beta : ℝ) ^ e ≠ 0 := ne_of_gt hpow_pos
  set y : ℝ := x * (beta : ℝ) ^ e with hy
  have hy_pos : 0 < y := by
    simpa [hy] using mul_pos hx_pos hpow_pos
  have hy_nonneg : 0 ≤ y := le_of_lt hy_pos
  have hx_nonneg : 0 ≤ x := le_of_lt hx_pos
  set M : Int := FloatSpec.Core.Raux.mag beta x with hM
  set N : Int := FloatSpec.Core.Raux.mag beta y with hN
  have hx_ne : x ≠ 0 := ne_of_gt hx_pos
  have hy_ne : y ≠ 0 := ne_of_gt hy_pos
  have hMx_lb1_M : emin + prec + 1 ≤ M := by
    simpa [hM] using hMx_lb1
  have hshift1_M : emin + prec - M + 1 ≤ e := by
    simpa [hM] using hshift1
  have hN_eq : N = M + e := by
    set L : ℝ := Real.log (abs x) / Real.log (beta : ℝ)
    have hM_run : M = Int.floor L + 1 := by
      simp [FloatSpec.Core.Raux.mag, hM, hx_ne, L]
    have hdiv :
        Real.log (abs y) / Real.log (beta : ℝ)
          = L + (e : ℝ) := by
      have hxabs_pos : 0 < |x| := abs_pos.mpr hx_ne
      have hbpow_abs_pos : 0 < |(beta : ℝ) ^ e| := abs_pos.mpr hpow_ne
      have hlog_prod :
          Real.log (|x| * |(beta : ℝ) ^ e|)
            = Real.log (|x|) + (e : ℝ) * Real.log (beta : ℝ) := by
        calc
          Real.log (|x| * |(beta : ℝ) ^ e|)
              = Real.log (|x|) + Real.log (|(beta : ℝ) ^ e|) := by
                    simpa using Real.log_mul (ne_of_gt hxabs_pos) (ne_of_gt hbpow_abs_pos)
          _   = Real.log (|x|) + Real.log ((beta : ℝ) ^ e) := by
                    simpa [abs_of_nonneg (le_of_lt hpow_pos)]
          _   = Real.log (|x|) + (e : ℝ) * Real.log (beta : ℝ) := by
                    simpa using Real.log_zpow hbposR e
      have habs_mul : abs y = |x| * |(beta : ℝ) ^ e| := by
        have hbnonneg : 0 ≤ (beta : ℝ) ^ e := le_of_lt hpow_pos
        simp [hy, abs_mul, abs_of_nonneg hbnonneg]
      have hlogβ_pos : 0 < Real.log (beta : ℝ) := by
        have hβR : (1 : ℝ) < (beta : ℝ) := by exact_mod_cast hβ
        exact (Real.log_pos_iff (x := (beta : ℝ)) (le_of_lt hbposR)).mpr hβR
      have hlogβ_ne : Real.log (beta : ℝ) ≠ 0 := ne_of_gt hlogβ_pos
      have hmul_div : ((e : ℝ) * Real.log (beta : ℝ)) / Real.log (beta : ℝ) = (e : ℝ) := by
        simpa [hlogβ_ne] using (mul_div_cancel' (e : ℝ) (Real.log (beta : ℝ)))
      calc
        Real.log (abs y) / Real.log (beta : ℝ)
            = Real.log (|x| * |(beta : ℝ) ^ e|) / Real.log (beta : ℝ) := by
                  simpa [habs_mul]
        _   = (Real.log (|x|) + (e : ℝ) * Real.log (beta : ℝ)) / Real.log (beta : ℝ) := by
                  rw [hlog_prod]
        _   = Real.log (|x|) / Real.log (beta : ℝ)
                + ((e : ℝ) * Real.log (beta : ℝ)) / Real.log (beta : ℝ) := by
                  simpa using (add_div (Real.log (|x|)) ((e : ℝ) * Real.log (beta : ℝ)) (Real.log (beta : ℝ)))
        _   = L + (e : ℝ) := by simpa [L, hmul_div]
    have hN_run : N = Int.floor (L + (e : ℝ)) + 1 := by
      have hfloor_div :
          Int.floor (Real.log (abs y) / Real.log (beta : ℝ))
            = Int.floor (L + (e : ℝ)) := by
        simpa using congrArg Int.floor hdiv
      have : FloatSpec.Core.Raux.mag beta y = Int.floor (L + (e : ℝ)) + 1 := by
        simp only [FloatSpec.Core.Raux.mag, hy_ne, ite_false, Id.run, pure, hfloor_div]
      simpa [hN] using this
    have hfloor_add : Int.floor (L + (e : ℝ)) = Int.floor L + e :=
      Int.floor_add_intCast L e
    have : N = M + e := by
      rw [hN_run, hfloor_add, hM_run]
      ring
    exact this
  have hpred_y_pos :
      FloatSpec.Core.Ulp.pred beta (FLT_exp prec emin) y =
        FloatSpec.Core.Ulp.pred_pos beta (FLT_exp prec emin) y := by
    have hneg : ¬ 0 ≤ -y := by linarith
    simp only [FloatSpec.Core.Ulp.pred, FloatSpec.Core.Ulp.succ, hneg, ite_false, neg_neg]
  have hpred_x_pos :
      FloatSpec.Core.Ulp.pred beta (FLT_exp prec emin) x =
        FloatSpec.Core.Ulp.pred_pos beta (FLT_exp prec emin) x := by
    have hneg : ¬ 0 ≤ -x := by linarith
    simp only [FloatSpec.Core.Ulp.pred, FloatSpec.Core.Ulp.succ, hneg, ite_false, neg_neg]
  have hMx_lb : emin + prec ≤ FloatSpec.Core.Raux.mag beta x := by
    have : emin + prec ≤ emin + prec + 1 := by exact le_of_lt (Int.lt_add_one_iff.mpr le_rfl)
    exact le_trans this hMx_lb1
  have hshift : emin + prec - FloatSpec.Core.Raux.mag beta x ≤ e := by
    have : emin + prec - FloatSpec.Core.Raux.mag beta x ≤ emin + prec - FloatSpec.Core.Raux.mag beta x + 1 := by
      exact le_of_lt (Int.lt_add_one_iff.mpr le_rfl)
    exact le_trans this hshift1
  have hboundary_y_of_x :
      x = (beta : ℝ) ^ (M - 1) →
        y = (beta : ℝ) ^ (N - 1) := by
    intro hxB
    have hExp : (M - 1) + e = N - 1 := by omega
    calc
      y = x * (beta : ℝ) ^ e := hy
      _ = (beta : ℝ) ^ (M - 1) * (beta : ℝ) ^ e := by rw [hxB]
      _ = (beta : ℝ) ^ ((M - 1) + e) := by rw [zpow_add₀ hbne]
      _ = (beta : ℝ) ^ (N - 1) := by rw [hExp]
  have hboundary_x_of_y :
      y = (beta : ℝ) ^ (N - 1) →
        x = (beta : ℝ) ^ (M - 1) := by
    intro hyB
    have hExp : N - 1 = (M - 1) + e := by omega
    have hmul :
        x * (beta : ℝ) ^ e = (beta : ℝ) ^ (M - 1) * (beta : ℝ) ^ e := by
      calc
        x * (beta : ℝ) ^ e = y := hy.symm
        _ = (beta : ℝ) ^ (N - 1) := hyB
        _ = (beta : ℝ) ^ ((M - 1) + e) := by rw [hExp]
        _ = (beta : ℝ) ^ (M - 1) * (beta : ℝ) ^ e := by rw [zpow_add₀ hbne]
    exact mul_right_cancel₀ hpow_ne hmul
  have hrunEq :
      FloatSpec.Core.Ulp.pred beta (FLT_exp prec emin) y =
        FloatSpec.Core.Ulp.pred beta (FLT_exp prec emin) x * (beta : ℝ) ^ e := by
    by_cases hxB : x = (beta : ℝ) ^ (M - 1)
    · have hyB : y = (beta : ℝ) ^ (N - 1) := hboundary_y_of_x hxB
      have hpredpos_x :
          FloatSpec.Core.Ulp.pred_pos beta (FLT_exp prec emin) x =
            x - (beta : ℝ) ^ (FLT_exp prec emin (M - 1)) := by
        have hxB' : x = (beta : ℝ) ^ (FloatSpec.Core.Raux.mag beta x - 1) := by
          simpa [← hM] using hxB
        unfold FloatSpec.Core.Ulp.pred_pos
        rw [ite_eq_left hxB']
      have hpredpos_y :
          FloatSpec.Core.Ulp.pred_pos beta (FLT_exp prec emin) y =
            y - (beta : ℝ) ^ (FLT_exp prec emin (N - 1)) := by
        have hyB' : y = (beta : ℝ) ^ (FloatSpec.Core.Raux.mag beta y - 1) := by
          simpa [← hN] using hyB
        unfold FloatSpec.Core.Ulp.pred_pos
        rw [ite_eq_left hyB']
      have hM_prev_large : emin ≤ M - 1 - prec := by omega
      have hN_prev_large : emin ≤ N - 1 - prec := by omega
      have hExp_x : FLT_exp prec emin (M - 1) = M - 1 - prec := by
        simpa [FLT_exp, max_eq_left hM_prev_large]
      have hExp_y : FLT_exp prec emin (N - 1) = N - 1 - prec := by
        simpa [FLT_exp, max_eq_left hN_prev_large]
      have hExp : FLT_exp prec emin (N - 1) = FLT_exp prec emin (M - 1) + e := by
        have : N - 1 - prec = (M - 1 - prec) + e := by omega
        simpa [hExp_y, hExp_x] using this
      have hpow_shift :
          (beta : ℝ) ^ (FLT_exp prec emin (N - 1)) =
            (beta : ℝ) ^ (FLT_exp prec emin (M - 1)) * (beta : ℝ) ^ e := by
        have := congrArg (fun t : Int => (beta : ℝ) ^ t) hExp
        simpa [zpow_add₀ hbne] using this
      calc
        FloatSpec.Core.Ulp.pred beta (FLT_exp prec emin) y
            = FloatSpec.Core.Ulp.pred_pos beta (FLT_exp prec emin) y := hpred_y_pos
        _ = y - (beta : ℝ) ^ (FLT_exp prec emin (N - 1)) := hpredpos_y
        _ = (x - (beta : ℝ) ^ (FLT_exp prec emin (M - 1))) * (beta : ℝ) ^ e := by
              rw [hy, hpow_shift]
              ring
        _ = FloatSpec.Core.Ulp.pred_pos beta (FLT_exp prec emin) x * (beta : ℝ) ^ e := by
              rw [hpredpos_x]
        _ = FloatSpec.Core.Ulp.pred beta (FLT_exp prec emin) x * (beta : ℝ) ^ e := by
              rw [hpred_x_pos]
    · have hyB_not : y ≠ (beta : ℝ) ^ (N - 1) := by
        intro hyB
        exact hxB (hboundary_x_of_y hyB)
      have hpredpos_x :
          FloatSpec.Core.Ulp.pred_pos beta (FLT_exp prec emin) x =
            x - FloatSpec.Core.Ulp.ulp beta (FLT_exp prec emin) x := by
        have hxB' : x ≠ (beta : ℝ) ^ (FloatSpec.Core.Raux.mag beta x - 1) := by
          intro h
          exact hxB (by simpa [← hM] using h)
        unfold FloatSpec.Core.Ulp.pred_pos
        rw [ite_eq_right hxB']
      have hpredpos_y :
          FloatSpec.Core.Ulp.pred_pos beta (FLT_exp prec emin) y =
            y - FloatSpec.Core.Ulp.ulp beta (FLT_exp prec emin) y := by
        have hyB_not' : y ≠ (beta : ℝ) ^ (FloatSpec.Core.Raux.mag beta y - 1) := by
          intro h
          exact hyB_not (by simpa [← hN] using h)
        unfold FloatSpec.Core.Ulp.pred_pos
        rw [ite_eq_right hyB_not']
      have hulp_shift :
          FloatSpec.Core.Ulp.ulp beta (FLT_exp prec emin) y =
            FloatSpec.Core.Ulp.ulp beta (FLT_exp prec emin) x * (beta : ℝ) ^ e := by
        simpa [hy] using ulp_FLT_exact_shift (prec := prec) (emin := emin)
          beta x e hx_ne hMx_lb hshift
      calc
        FloatSpec.Core.Ulp.pred beta (FLT_exp prec emin) y
            = FloatSpec.Core.Ulp.pred_pos beta (FLT_exp prec emin) y := hpred_y_pos
        _ = y - FloatSpec.Core.Ulp.ulp beta (FLT_exp prec emin) y := hpredpos_y
        _ = (x - FloatSpec.Core.Ulp.ulp beta (FLT_exp prec emin) x) * (beta : ℝ) ^ e := by
              rw [hy, hulp_shift]
              ring
        _ = FloatSpec.Core.Ulp.pred_pos beta (FLT_exp prec emin) x * (beta : ℝ) ^ e := by
              rw [hpredpos_x]
        _ = FloatSpec.Core.Ulp.pred beta (FLT_exp prec emin) x * (beta : ℝ) ^ e := by
              rw [hpred_x_pos]
  have hrunEq' :
      FloatSpec.Core.Ulp.pred beta (FLT_exp prec emin) (x * (beta : ℝ) ^ e) =
        FloatSpec.Core.Ulp.pred beta (FLT_exp prec emin) x * (beta : ℝ) ^ e := by
    simpa [hy] using hrunEq
  exact hrunEq'

-- Auxiliary lemma: pred exact shift for positive inputs (used to handle negative `x` for succ)
-- (moved earlier)

omit [Prec_gt_0 prec] in
@[flocq_source "src/Core/FLT.v" 394 "succ_FLT_exact_shift"]
theorem succ_FLT_exact_shift (beta : Int) [ValidRadix beta] (x : ℝ) (e : Int)
    (hx_ne : x ≠ 0) (hMx_lb1 : emin + prec + 1 ≤ FloatSpec.Core.Raux.mag beta x)
    (hshift1 : emin + prec - FloatSpec.Core.Raux.mag beta x + 1 ≤ e) :
    FloatSpec.Core.Ulp.succ beta (FLT_exp prec emin) (x * (beta : ℝ) ^ e) =
      FloatSpec.Core.Ulp.succ beta (FLT_exp prec emin) x * (beta : ℝ) ^ e := by
  have hβ : 1 < beta := ValidRadix.valid
  classical
  -- Split on the sign of x
  by_cases hxpos : 0 < x
  · -- Positive case: use the specialized positive lemma
    have hpos_pre : 0 < x ∧ emin + prec ≤ (FloatSpec.Core.Raux.mag beta x) ∧
                    emin + prec - (FloatSpec.Core.Raux.mag beta x) ≤ e := by
      exact ⟨hxpos, by omega, by omega⟩
    -- Apply the positive-input scaling lemma.
    have := succ_FLT_exact_shift_pos (prec := prec) (emin := emin) (beta := beta) (x := x) (e := e) hpos_pre.1 hpos_pre.2.1 hpos_pre.2.2
    exact this
  · -- Negative case: reduce to `pred` on positive input `-x` via `pred` definition
    have hxle : x ≤ 0 := le_of_not_gt hxpos
    have hxlt : x < 0 := lt_of_le_of_ne hxle hx_ne
    have hxneg_pos : 0 < -x := by exact neg_pos.mpr hxlt
    -- We will prove: pred((-x) * β^e) = pred(-x) * β^e and transfer via `pred`/`succ` relation
    have hpred_pos_shift :
        (FloatSpec.Core.Ulp.pred beta (FLT_exp prec emin) ((-x) * (beta : ℝ) ^ e))
          = (FloatSpec.Core.Ulp.pred beta (FLT_exp prec emin) (-x)) * (beta : ℝ) ^ e := by
      -- mag(-x) = mag(x), so hypotheses carry over
      have hmag_eq : FloatSpec.Core.Raux.mag beta (-x) = FloatSpec.Core.Raux.mag beta x := by
        have hxne : x ≠ 0 := ne_of_lt hxlt
        have hnxne : -x ≠ 0 := by linarith
        simp only [FloatSpec.Core.Raux.mag, Id.run, abs_neg, hxne, hnxne, ite_false]
      have hpos_pre : beta > 1 ∧ 0 < -x ∧ emin + prec + 1 ≤ (FloatSpec.Core.Raux.mag beta (-x)) ∧
                      emin + prec - (FloatSpec.Core.Raux.mag beta (-x)) + 1 ≤ e := by
        rw [hmag_eq]
        exact ⟨hβ, hxneg_pos, hMx_lb1, hshift1⟩
      have := pred_FLT_exact_shift_pos_aux (prec := prec) (emin := emin) (beta := beta) (-x) e hpos_pre.2.1 hpos_pre.2.2.1 hpos_pre.2.2.2
      exact this
    -- succ z = - pred (-z)
    have hsucc_y : (FloatSpec.Core.Ulp.succ beta (FLT_exp prec emin) (x * (beta : ℝ) ^ e))
                    = - (FloatSpec.Core.Ulp.pred beta (FLT_exp prec emin) (-(x * (beta : ℝ) ^ e))) := by
      simp [FloatSpec.Core.Ulp.pred]
    have hsucc_x : (FloatSpec.Core.Ulp.succ beta (FLT_exp prec emin) x)
                    = - (FloatSpec.Core.Ulp.pred beta (FLT_exp prec emin) (-x)) := by
      simp [FloatSpec.Core.Ulp.pred]
    -- Now combine via the positive pred-shift on -x and cancel the negations
    have : (FloatSpec.Core.Ulp.succ beta (FLT_exp prec emin) (x * (beta : ℝ) ^ e))
              = ((FloatSpec.Core.Ulp.succ beta (FLT_exp prec emin) x)) * (beta : ℝ) ^ e := by
      -- Key step: -(x * β^e) = (-x) * β^e
      have hneg_factor : -(x * (beta : ℝ) ^ e) = (-x) * (beta : ℝ) ^ e := by ring
      rw [hsucc_y, hneg_factor, hpred_pos_shift, hsucc_x]
      ring
    exact this

/-
Coq (FLT.v):
Lemma pred_FLT_exact_shift:
  forall x e,
  (x <> 0)%R ->
  (emin + prec + 1 <= mag beta x)%Z ->
  (emin + prec - mag beta x + 1 <= e)%Z ->
  (pred beta FLT_exp (x * bpow e) = pred beta FLT_exp x * bpow e)%R.
-/
omit [Prec_gt_0 prec] in
@[flocq_source "src/Core/FLT.v" 419 "pred_FLT_exact_shift"]
theorem pred_FLT_exact_shift (beta : Int) [ValidRadix beta] (x : ℝ) (e : Int)
    (hx_ne : x ≠ 0) (hMx_lb1 : emin + prec + 1 ≤ FloatSpec.Core.Raux.mag beta x)
    (hshift1 : emin + prec - FloatSpec.Core.Raux.mag beta x + 1 ≤ e) :
    FloatSpec.Core.Ulp.pred beta (FLT_exp prec emin) (x * (beta : ℝ) ^ e) =
      FloatSpec.Core.Ulp.pred beta (FLT_exp prec emin) x * (beta : ℝ) ^ e := by
  have hβ : 1 < beta := ValidRadix.valid
  classical
  -- Split on the sign of x
  by_cases hxpos : 0 < x
  · -- Positive case: reduce to the auxiliary positive lemma
    have hpos_pre : beta > 1 ∧ 0 < x ∧ emin + prec + 1 ≤ (FloatSpec.Core.Raux.mag beta x) ∧
                    emin + prec - (FloatSpec.Core.Raux.mag beta x) + 1 ≤ e := by
      exact ⟨hβ, hxpos, hMx_lb1, hshift1⟩
    -- Apply the positive-input predecessor lemma.
    have := pred_FLT_exact_shift_pos_aux (prec := prec) (emin := emin) (beta := beta) (x := x) (e := e) hpos_pre.2.1 hpos_pre.2.2.1 hpos_pre.2.2.2
    exact this
  · -- Negative case: use `pred_opp` to transfer to `succ` on positive input `-x`
    have hxle : x ≤ 0 := le_of_not_gt hxpos
    have hxlt : x < 0 := lt_of_le_of_ne hxle hx_ne
    have hxneg_pos : 0 < -x := by exact neg_pos.mpr hxlt
    -- pred (x*β^e) = - succ (-(x*β^e)) and pred x = - succ (-x)
    have hpred_y_eq :
        (FloatSpec.Core.Ulp.pred beta (FLT_exp prec emin) (x * (beta : ℝ) ^ e))
          = - (FloatSpec.Core.Ulp.succ beta (FLT_exp prec emin) (-(x * (beta : ℝ) ^ e))) := by
      simp [FloatSpec.Core.Ulp.pred]
    have hpred_x_eq :
        (FloatSpec.Core.Ulp.pred beta (FLT_exp prec emin) x)
          = - (FloatSpec.Core.Ulp.succ beta (FLT_exp prec emin) (-x)) := by
      simp [FloatSpec.Core.Ulp.pred]
    -- Apply the positive succ-shift lemma to `-x`
    have hxne : x ≠ 0 := hx_ne
    have hnxne : -x ≠ 0 := by linarith
    have hmag_eq : FloatSpec.Core.Raux.mag beta (-x) = FloatSpec.Core.Raux.mag beta x := by
      simp only [FloatSpec.Core.Raux.mag, Id.run, abs_neg, hxne, hnxne, ite_false]
    have hpos_pre : 0 < -x ∧ emin + prec ≤ (FloatSpec.Core.Raux.mag beta (-x)) ∧
                    emin + prec - (FloatSpec.Core.Raux.mag beta (-x)) ≤ e := by
      rw [hmag_eq]
      exact ⟨hxneg_pos, by omega, by omega⟩
    have hsucc_pos :
        (FloatSpec.Core.Ulp.succ beta (FLT_exp prec emin) ((-x) * (beta : ℝ) ^ e))
          = (FloatSpec.Core.Ulp.succ beta (FLT_exp prec emin) (-x)) * (beta : ℝ) ^ e := by
      have := succ_FLT_exact_shift_pos (prec := prec) (emin := emin) (beta := beta) (-x) e hpos_pre.1 hpos_pre.2.1 hpos_pre.2.2
      exact this
    -- Combine and cancel the negations
    have : (FloatSpec.Core.Ulp.pred beta (FLT_exp prec emin) (x * (beta : ℝ) ^ e))
              = (FloatSpec.Core.Ulp.pred beta (FLT_exp prec emin) x) * (beta : ℝ) ^ e := by
      -- Key step: -(x * β^e) = (-x) * β^e
      have hneg_factor : -(x * (beta : ℝ) ^ e) = (-x) * (beta : ℝ) ^ e := by ring
      rw [hpred_y_eq, hneg_factor, hsucc_pos, hpred_x_eq]
      ring
    exact this

/-
Coq (FLT.v):
Theorem ulp_FLT_pred_pos:
  forall x,
  generic_format beta FLT_exp x ->
  (0 <= x)%R ->
  ulp beta FLT_exp (pred beta FLT_exp x) = ulp beta FLT_exp x \/
  (x = bpow (mag beta x - 1) /\\ ulp beta FLT_exp (pred beta FLT_exp x) = (ulp beta FLT_exp x / IZR beta)%R).
-/
theorem ulp_FLT_pred_pos (beta : Int) [ValidRadix beta] (x : ℝ)
    (Fx : FloatSpec.Core.Generic_fmt.generic_format beta (FLT_exp prec emin) x)
    (hx0 : 0 ≤ x) :
    FloatSpec.Core.Ulp.ulp beta (FLT_exp prec emin) (FloatSpec.Core.Ulp.pred beta (FLT_exp prec emin) x) =
        FloatSpec.Core.Ulp.ulp beta (FLT_exp prec emin) x ∨
      (x = (beta : ℝ) ^ ((FloatSpec.Core.Raux.mag beta x) - 1) ∧
        FloatSpec.Core.Ulp.ulp beta (FLT_exp prec emin) (FloatSpec.Core.Ulp.pred beta (FLT_exp prec emin) x) =
          FloatSpec.Core.Ulp.ulp beta (FLT_exp prec emin) x / (beta : ℝ)) := by
  have hβ : 1 < beta := ValidRadix.valid
  classical
  -- Notation for predecessor and both ULPs (run-level equalities)
  set p : ℝ := (FloatSpec.Core.Ulp.pred beta (FLT_exp prec emin) x) with hp
  set up : ℝ := (FloatSpec.Core.Ulp.ulp beta (FLT_exp prec emin) p) with hup
  set ux : ℝ := (FloatSpec.Core.Ulp.ulp beta (FLT_exp prec emin) x) with hux
  -- Split on x = 0
  by_cases hxz : x = 0
  · -- At x = 0, use pred_0 and ulp symmetry to reduce to ulp(ulp 0) = ulp 0
    have hpred0_run :
        (FloatSpec.Core.Ulp.pred beta (FLT_exp prec emin) 0)
          = - (FloatSpec.Core.Ulp.ulp beta (FLT_exp prec emin) 0) := by
      -- Evaluate pred at 0 via the Hoare-style lemma
      have := FloatSpec.Core.Ulp.pred_0 (beta := beta) (fexp := FLT_exp prec emin)
      simpa [wp, PostCond.noThrow, Id.run, bind, pure]
        using (this True.intro)
    have hpred0 : p = - (FloatSpec.Core.Ulp.ulp beta (FLT_exp prec emin) 0) := by
      -- Rewrite p := (pred x).run and substitute x = 0
      have : p = (FloatSpec.Core.Ulp.pred beta (FLT_exp prec emin) 0) := by
        simpa [hp, hxz]
      simpa [this]
        using hpred0_run
    have hsym : (FloatSpec.Core.Ulp.ulp beta (FLT_exp prec emin) p)
                = (FloatSpec.Core.Ulp.ulp beta (FLT_exp prec emin) ((FloatSpec.Core.Ulp.ulp beta (FLT_exp prec emin) 0))) := by
      -- ulp(-y) = ulp(y); rewrite p via hpred0
      have := FloatSpec.Core.Ulp.ulp_opp (beta := beta) (fexp := FLT_exp prec emin) ((FloatSpec.Core.Ulp.ulp beta (FLT_exp prec emin) 0))
      -- Reduce the Hoare triple and rewrite
      simpa [wp, PostCond.noThrow, Id.run, bind, pure, hpred0, hup]
        using (this True.intro)
    -- Compute ulp at 0 under FLT and then ulp at that value using the small‑regime lemma
    have hulp0 : (FloatSpec.Core.Ulp.ulp beta (FLT_exp prec emin) 0) = (beta : ℝ) ^ emin :=
      -- Use the dedicated FLT lemma for ulp at zero
      ulp_FLT_0 (prec := prec) (emin := emin) (beta := beta)
    -- Since prec > 0 and 1 < beta, we have (β : ℝ)^emin < (β : ℝ)^(emin + prec)
    have hx_lt : |(FloatSpec.Core.Ulp.ulp beta (FLT_exp prec emin) 0)|
                  < (beta : ℝ) ^ (emin + prec) := by
      -- Rewrite absolute value and use base positivity
      have hbposℤ : (0 : Int) < beta := lt_trans Int.zero_lt_one hβ
      have hbposR : (0 : ℝ) < (beta : ℝ) := by exact_mod_cast hbposℤ
      have hprec_pos : 0 < prec := (Prec_gt_0.pos : 0 < prec)
      -- (β^emin) < (β^(emin+prec)) since prec > 0 and β > 1
      have : (beta : ℝ) ^ emin < (beta : ℝ) ^ (emin + prec) := by
        -- Convert to strict monotonicity in exponent
        have hβR : (1 : ℝ) < (beta : ℝ) := by exact_mod_cast hβ
        have hlt : emin < emin + prec := lt_add_of_pos_right _ hprec_pos
        exact zpow_lt_zpow_right₀ hβR hlt
      rw [hulp0, abs_of_nonneg (le_of_lt (zpow_pos hbposR _))]
      exact this
    -- Apply the small‑regime ULP lemma at x = ulp 0 to show `ulp (ulp 0) = β^emin = ulp 0`.
    have hulp_of_ulp0 : (FloatSpec.Core.Ulp.ulp beta (FLT_exp prec emin) ((FloatSpec.Core.Ulp.ulp beta (FLT_exp prec emin) 0)))
                        = (beta : ℝ) ^ emin := by
      exact ulp_FLT_small (prec := prec) (emin := emin) (beta := beta)
              (x := (FloatSpec.Core.Ulp.ulp beta (FLT_exp prec emin) 0)) hx_lt
    -- Conclude: up = ulp(ulp 0) = β^emin and ux = ulp 0 = β^emin
    have hux0 : ux = (beta : ℝ) ^ emin := by simpa [hux, hxz, hulp0]
    have hup0 : up = (beta : ℝ) ^ emin := by
      rw [hup, hsym, hulp_of_ulp0]
    -- Discharge the postcondition using the equality branch
    have heq_up_ux : up = ux := by simpa [hup0, hux0]
    have hdisj : (up = ux) ∨ (x = (beta : ℝ) ^ ((FloatSpec.Core.Raux.mag beta x) - 1) ∧ up = ux / (beta : ℝ)) :=
      Or.inl heq_up_ux
    simpa [up, ux] using hdisj
  · -- x > 0: follow the FLT proof split between the small regime and binade boundaries.
    have hxpos : 0 < x := lt_of_le_of_ne hx0 (Ne.symm hxz)
    have hsum : (FloatSpec.Core.Ulp.pred beta (FLT_exp prec emin) x)
                  + (FloatSpec.Core.Ulp.ulp beta (FLT_exp prec emin)
                      ((FloatSpec.Core.Ulp.pred beta (FLT_exp prec emin) x)))
                  = x := by
      have := FloatSpec.Core.Ulp.pred_plus_ulp (beta := beta) (fexp := FLT_exp prec emin)
                    (x := x) (hx := hxpos) (Fx := Fx)
      simpa [wp, PostCond.noThrow, Id.run, bind, pure]
        using (this hβ)
    have hbposℤ : (0 : Int) < beta := lt_trans Int.zero_lt_one hβ
    have hbposR : (0 : ℝ) < (beta : ℝ) := by exact_mod_cast hbposℤ
    have hbne : (beta : ℝ) ≠ 0 := ne_of_gt hbposR
    set T : ℝ := (beta : ℝ) ^ (emin + prec) with hT
    by_cases hlarge : T ≤ x
    · by_cases hxB : x = (beta : ℝ) ^ ((FloatSpec.Core.Raux.mag beta x) - 1)
      · set M : Int := FloatSpec.Core.Raux.mag beta x with hM
        have hxB_M : x = (beta : ℝ) ^ (M - 1) := by
          simpa [← hM] using hxB
        have hT_le_pow : (beta : ℝ) ^ (emin + prec) ≤ (beta : ℝ) ^ (M - 1) := by
          simpa [T, hxB_M] using hlarge
        have hM_prev_lb : emin + prec ≤ M - 1 := by
          have h := FloatSpec.Core.Raux.le_bpow (beta := beta) (e1 := emin + prec) (e2 := M - 1)
              hβ hT_le_pow
          simpa [wp, PostCond.noThrow, Id.run, pure] using (h True.intro)
        have hM_large : emin ≤ M - prec := by omega
        have hM_prev_large : emin ≤ M - 1 - prec := by omega
        have hpred_pos :
            FloatSpec.Core.Ulp.pred beta (FLT_exp prec emin) x =
              FloatSpec.Core.Ulp.pred_pos beta (FLT_exp prec emin) x := by
          have h := FloatSpec.Core.Ulp.pred_eq_pos (beta := beta) (fexp := FLT_exp prec emin)
              (x := x) (hx := hx0)
          simpa [wp, PostCond.noThrow, Id.run, bind, pure] using (h hβ)
        have hpred_boundary :
            FloatSpec.Core.Ulp.pred beta (FLT_exp prec emin) x =
              x - (beta : ℝ) ^ (FLT_exp prec emin (M - 1)) := by
          have hxB' : x = (beta : ℝ) ^ (FloatSpec.Core.Raux.mag beta x - 1) := by
            simpa [← hM] using hxB_M
          have hpos :
              FloatSpec.Core.Ulp.pred_pos beta (FLT_exp prec emin) x =
                x - (beta : ℝ) ^ (FLT_exp prec emin (M - 1)) := by
            unfold FloatSpec.Core.Ulp.pred_pos
            rw [ite_eq_left hxB']
          exact hpred_pos.trans hpos
        have hup_step :
            FloatSpec.Core.Ulp.ulp beta (FLT_exp prec emin)
                (FloatSpec.Core.Ulp.pred beta (FLT_exp prec emin) x)
              = (beta : ℝ) ^ (FLT_exp prec emin (M - 1)) := by
          have h' := hsum
          rw [hpred_boundary] at h'
          linarith
        have hux_pow :
            FloatSpec.Core.Ulp.ulp beta (FLT_exp prec emin) x =
              (beta : ℝ) ^ (FLT_exp prec emin M) := by
          have h := FloatSpec.Core.Ulp.ulp_neq_0 (beta := beta) (fexp := FLT_exp prec emin)
              x (ne_of_gt hxpos)
          have hrun := h True.intro
          have hcexp :
              FloatSpec.Core.Generic_fmt.cexp beta (FLT_exp prec emin) x =
                FLT_exp prec emin M := by
            unfold FloatSpec.Core.Generic_fmt.cexp
            simp [FloatSpec.Core.Raux.mag, hM]
          simpa [wp, PostCond.noThrow, Id.run, bind, pure, hcexp] using hrun
        have hExp_M : FLT_exp prec emin M = M - prec := by
          simpa [FLT_exp, max_eq_left hM_large]
        have hExp_prev : FLT_exp prec emin (M - 1) = M - 1 - prec := by
          simpa [FLT_exp, max_eq_left hM_prev_large]
        have hExp_step : FLT_exp prec emin M = FLT_exp prec emin (M - 1) + 1 := by
          omega
        have hpow_step :
            (beta : ℝ) ^ (FLT_exp prec emin (M - 1)) =
              (beta : ℝ) ^ (FLT_exp prec emin M) / (beta : ℝ) := by
          have hadd :
              (beta : ℝ) ^ (FLT_exp prec emin M) =
                (beta : ℝ) ^ (FLT_exp prec emin (M - 1)) * (beta : ℝ) := by
            have := congrArg (fun t : Int => (beta : ℝ) ^ t) hExp_step
            simpa [zpow_add₀ hbne] using this
          field_simp [hbne]
          linarith
        have hright :
            x = (beta : ℝ) ^ (FloatSpec.Core.Raux.mag beta x - 1) ∧ up = ux / (beta : ℝ) := by
          refine ⟨hxB, ?_⟩
          have hup_pow : up = (beta : ℝ) ^ (FLT_exp prec emin (M - 1)) := by
            calc
              up = FloatSpec.Core.Ulp.ulp beta (FLT_exp prec emin) p := hup
              _ = FloatSpec.Core.Ulp.ulp beta (FLT_exp prec emin)
                    (FloatSpec.Core.Ulp.pred beta (FLT_exp prec emin) x) := by rw [hp]
              _ = (beta : ℝ) ^ (FLT_exp prec emin (M - 1)) := hup_step
          have hux_pow' : ux = (beta : ℝ) ^ (FLT_exp prec emin M) := hux.trans hux_pow
          simpa [hup_pow, hux_pow', hpow_step]
        have hdisj : (up = ux) ∨ (x = (beta : ℝ) ^ ((FloatSpec.Core.Raux.mag beta x) - 1) ∧ up = ux / (beta : ℝ)) :=
          Or.inr hright
        simpa [up, ux] using hdisj
      · have hpred_pos :
            FloatSpec.Core.Ulp.pred beta (FLT_exp prec emin) x =
              FloatSpec.Core.Ulp.pred_pos beta (FLT_exp prec emin) x := by
          have h := FloatSpec.Core.Ulp.pred_eq_pos (beta := beta) (fexp := FLT_exp prec emin)
              (x := x) (hx := hx0)
          simpa [wp, PostCond.noThrow, Id.run, bind, pure] using (h hβ)
        have hpred_run :
            FloatSpec.Core.Ulp.pred beta (FLT_exp prec emin) x =
              x - FloatSpec.Core.Ulp.ulp beta (FLT_exp prec emin) x := by
          have hpos :
              FloatSpec.Core.Ulp.pred_pos beta (FLT_exp prec emin) x =
                x - FloatSpec.Core.Ulp.ulp beta (FLT_exp prec emin) x := by
            unfold FloatSpec.Core.Ulp.pred_pos
            rw [ite_eq_right hxB]
          exact hpred_pos.trans hpos
        have heq : FloatSpec.Core.Ulp.ulp beta (FLT_exp prec emin)
              (FloatSpec.Core.Ulp.pred beta (FLT_exp prec emin) x)
            = FloatSpec.Core.Ulp.ulp beta (FLT_exp prec emin) x := by
          have h' := hsum
          rw [hpred_run] at h'
          linarith
        have heq_up_ux : up = ux := by simpa [up, ux] using heq
        have hdisj : (up = ux) ∨ (x = (beta : ℝ) ^ ((FloatSpec.Core.Raux.mag beta x) - 1) ∧ up = ux / (beta : ℝ)) :=
          Or.inl heq_up_ux
        simpa [up, ux] using hdisj
    · have hx_small : x < T := lt_of_not_ge hlarge
      have hpred_lt_T :
          FloatSpec.Core.Ulp.pred beta (FLT_exp prec emin) x < T := by
        have htrip := FloatSpec.Core.Ulp.pred_lt_le (beta := beta) (fexp := FLT_exp prec emin)
            (x := x) (y := T) (hx := ne_of_gt hxpos) (hxy := le_of_lt hx_small)
        simpa [wp, PostCond.noThrow, Id.run, bind, pure] using (htrip hβ)
      have hpred_nonneg :
          0 ≤ FloatSpec.Core.Ulp.pred beta (FLT_exp prec emin) x := by
        have F0 : FloatSpec.Core.Generic_fmt.generic_format beta (FLT_exp prec emin) 0 :=
          FloatSpec.Core.Generic_fmt.generic_format_0_run (beta := beta) (fexp := FLT_exp prec emin)
        have htrip := FloatSpec.Core.Ulp.pred_ge_gt (beta := beta) (fexp := FLT_exp prec emin)
            (x := 0) (y := x) (Fx := F0) (Fy := Fx) hxpos
        simpa [wp, PostCond.noThrow, Id.run, bind, pure] using (htrip hβ)
      have hux_small :
          FloatSpec.Core.Ulp.ulp beta (FLT_exp prec emin) x = (beta : ℝ) ^ emin := by
        have hxabs : |x| < (beta : ℝ) ^ (emin + prec) := by
          simpa [T, abs_of_nonneg hx0] using hx_small
        exact ulp_FLT_small (prec := prec) (emin := emin) (beta := beta) (x := x) hxabs
      have hup_small :
          FloatSpec.Core.Ulp.ulp beta (FLT_exp prec emin)
              (FloatSpec.Core.Ulp.pred beta (FLT_exp prec emin) x) = (beta : ℝ) ^ emin := by
        have hpabs : |FloatSpec.Core.Ulp.pred beta (FLT_exp prec emin) x| < (beta : ℝ) ^ (emin + prec) := by
          simpa [T, abs_of_nonneg hpred_nonneg] using hpred_lt_T
        exact ulp_FLT_small (prec := prec) (emin := emin) (beta := beta)
          (x := FloatSpec.Core.Ulp.pred beta (FLT_exp prec emin) x) hpabs
      have heq_up_ux : up = ux := by
        simpa [up, ux, hup_small, hux_small]
      have hdisj : (up = ux) ∨ (x = (beta : ℝ) ^ ((FloatSpec.Core.Raux.mag beta x) - 1) ∧ up = ux / (beta : ℝ)) :=
        Or.inl heq_up_ux
      simpa [up, ux] using hdisj
where
  -- Helper for rewriting (a + b) - a = b without importing extra lemmas
  sub_eq {a b : ℝ} : (a + b) - a = b := by ring

end FloatSpec.Core.FLT
