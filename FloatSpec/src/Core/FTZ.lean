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
-- import Mathlib.Data.Real.Basic
import Std.Do.Triple
import FloatSpec.src.Core.Ulp
import FloatSpec.src.Core.FLX

open Real
open Std.Do
open FloatSpec.Core.Generic_fmt

set_option linter.coqSource true
set_option warningAsError true

namespace FloatSpec.Core.FTZ

variable (prec emin : Int) [Fact (0 < prec)]

/-- Flush-to-zero exponent function

    Use the precision-based exponent `e - prec` when it is at least `emin`;
    otherwise use the fixed exponent `emin + prec - 1`. This describes the
    abrupt-underflow format without subnormals. The integer rounder separately
    determines how an unrepresentable input is rounded.
-/
-- Source: https://gitlab.inria.fr/flocq/flocq/-/blob/7aab8f55bceec0cfafc3b3bc0e77e0dbb5a70c5f/src/Core/FTZ.v#L43
@[flocq_source "src/Core/FTZ.v" 43 "FTZ_exp"]
def FTZ_exp (e : Int) : Int :=
  if e - prec < emin then emin + prec - 1 else e - prec

/-- Specification: FTZ exponent calculation

    The FTZ exponent function provides full precision for normal
    numbers but flushes small numbers to the minimum exponent,
    eliminating subnormal numbers from the representation.
    Local arithmetic regression for the Lean `FTZ_exp` implementation.
-/
theorem FTZ_exp_spec (e : Int) :
    FTZ_exp prec emin e = if e - prec < emin then emin + prec - 1 else e - prec := by
  rfl

/-- Flush-to-zero format predicate

    A real number has a witnessing float with exponent at least `emin`.
    For nonzero values, its mantissa is normalized between the two precision
    bounds. The source states this representation predicate directly;
    equivalence with the generic-format characterization is a separate theorem.
-/
-- Source: https://gitlab.inria.fr/flocq/flocq/-/blob/7aab8f55bceec0cfafc3b3bc0e77e0dbb5a70c5f/src/Core/FTZ.v#L36
@[flocq_source "src/Core/FTZ.v" 36 "FTZ_format"]
def FTZ_format (beta : Int) [ValidRadix beta] (x : ℝ) : Prop :=
  ∃ f : FloatSpec.Core.Defs.FlocqFloat beta,
    x = FloatSpec.Core.Defs.F2R f ∧
      (x ≠ 0 →
        FloatSpec.Core.Zaux.Zpower beta (prec - 1) ≤ |f.Fnum| ∧
        |f.Fnum| < FloatSpec.Core.Zaux.Zpower beta prec) ∧
      emin ≤ f.Fexp

/-- Integer rounding with flush-to-zero behavior.

Values with magnitude less than 1 are rounded to 0, otherwise we reuse the
underlying integer rounding `rnd`. -/
-- Source: https://gitlab.inria.fr/flocq/flocq/-/blob/7aab8f55bceec0cfafc3b3bc0e77e0dbb5a70c5f/src/Core/FTZ.v#L216
@[flocq_source "src/Core/FTZ.v" 216 "Zrnd_FTZ"]
noncomputable def Zrnd_FTZ (rnd : ℝ → Int) (x : ℝ) : Int :=
  if FloatSpec.Core.Raux.Rle_bool 1 |x| then rnd x else 0

/-- `Zrnd_FTZ` preserves the basic rounding-function laws required by Flocq. -/
instance valid_rnd_FTZ (rnd : ℝ → Int) [Valid_rnd rnd] : Valid_rnd (Zrnd_FTZ rnd) := by
  refine ⟨?_, ?_⟩
  · intro x y hxy
    unfold Zrnd_FTZ
    by_cases hx : 1 ≤ |x|
    · by_cases hy : 1 ≤ |y|
      · simp [FloatSpec.Core.Raux.Rle_bool, hx, hy]
        exact Valid_rnd.Zrnd_le (rnd := rnd) x y hxy
      · have hx_nonpos : x ≤ 0 := by
          by_contra hx_pos
          have hx_pos' : 0 < x := lt_of_not_ge hx_pos
          have h1x : 1 ≤ x := by
            simpa [abs_of_pos hx_pos'] using hx
          have h1y : 1 ≤ y := le_trans h1x hxy
          have h1abs_y : 1 ≤ |y| := by
            have hy_nonneg : 0 ≤ y := le_trans (by positivity) h1y
            simpa [abs_of_nonneg hy_nonneg] using h1y
          exact hy h1abs_y
        simp [FloatSpec.Core.Raux.Rle_bool, hx, hy]
        have hle : rnd x ≤ rnd 0 :=
          Valid_rnd.Zrnd_le (rnd := rnd) x 0 hx_nonpos
        have hzero : rnd 0 = 0 := by
          simpa using (Valid_rnd.Zrnd_IZR (rnd := rnd) (0 : Int))
        simpa [hzero] using hle
    · by_cases hy : 1 ≤ |y|
      · have hy_nonneg : 0 ≤ y := by
          by_contra hy_neg
          have hy_neg' : y < 0 := lt_of_not_ge hy_neg
          have hy_le_neg1 : y ≤ -1 := by
            have h1 : 1 ≤ -y := by
              simpa [abs_of_nonpos (le_of_lt hy_neg')] using hy
            linarith
          have hx_le_neg1 : x ≤ -1 := le_trans hxy hy_le_neg1
          have h1abs_x : 1 ≤ |x| := by
            have hx_nonpos : x ≤ 0 := by linarith
            have h1 : 1 ≤ -x := by linarith
            simpa [abs_of_nonpos hx_nonpos] using h1
          exact hx h1abs_x
        simp [FloatSpec.Core.Raux.Rle_bool, hx, hy]
        have hle : rnd 0 ≤ rnd y :=
          Valid_rnd.Zrnd_le (rnd := rnd) 0 y hy_nonneg
        have hzero : rnd 0 = 0 := by
          simpa using (Valid_rnd.Zrnd_IZR (rnd := rnd) (0 : Int))
        simpa [hzero] using hle
      · simp [FloatSpec.Core.Raux.Rle_bool, hx, hy]
  · intro n
    unfold Zrnd_FTZ
    by_cases h : 1 ≤ |(n : ℝ)|
    · simp [FloatSpec.Core.Raux.Rle_bool, h, Valid_rnd.Zrnd_IZR (rnd := rnd) n]
    · have hlt : |(n : ℝ)| < 1 := lt_of_not_ge h
      have h_abs_natAbs : (Int.natAbs n : ℝ) = |(n : ℝ)| := by
        simpa [Nat.cast_natAbs, Int.cast_abs]
      have hnat_lt1 : (Int.natAbs n : ℝ) < 1 := by
        simpa [h_abs_natAbs] using hlt
      have hnat_zero : Int.natAbs n = 0 := by
        by_contra hne
        have hpos : 0 < Int.natAbs n := Nat.pos_of_ne_zero hne
        have hge1 : (1 : ℝ) ≤ (Int.natAbs n : ℝ) := by
          exact_mod_cast (Nat.succ_le_of_lt hpos)
        exact (not_lt_of_ge hge1) hnat_lt1
      have hn : n = 0 := Int.natAbs_eq_zero.mp hnat_zero
      simp [FloatSpec.Core.Raux.Rle_bool, h, hn, Valid_rnd.Zrnd_IZR (rnd := rnd) 0]

/-- `Valid_exp` instance for the FTZ exponent function. -/
instance FTZ_exp_valid :
    FloatSpec.Core.Generic_fmt.Valid_exp (FTZ_exp prec emin) := by
  refine ⟨?_⟩
  intro k; constructor
  · -- Large regime: if fexp k < k, then fexp (k+1) ≤ k
    intro hklt
    have hprec1 : 1 ≤ prec := by simpa using (Int.add_one_le_iff).mpr (Fact.out : 0 < prec)
    by_cases hk : k - prec < emin
    · by_cases hk1 : (k + 1) - prec < emin
      · simp [FTZ_exp, hk, hk1] at hklt ⊢
        omega
      · simp [FTZ_exp, hk, hk1] at hklt ⊢
        omega
    · by_cases hk1 : (k + 1) - prec < emin
      · simp [FTZ_exp, hk, hk1] at hklt ⊢
        omega
      · simp [FTZ_exp, hk, hk1] at hklt ⊢
        omega
  · -- Small regime: if k ≤ fexp k, then stability at fexp k and constancy below it
    intro hk
    have hprec1 : 1 ≤ prec := by simpa using (Int.add_one_le_iff).mpr (Fact.out : 0 < prec)
    have hk_branch : k - prec < emin := by
      by_contra hnot
      have hk_le : k ≤ k - prec := by simpa [FTZ_exp, hnot] using hk
      omega
    have hfexp_k : FTZ_exp prec emin k = emin + prec - 1 := by
      simp [FTZ_exp, hk_branch]
    refine And.intro ?hA ?hB
    · -- fexp (fexp k + 1) ≤ fexp k
      have hgoal : FTZ_exp prec emin (emin + prec) ≤ emin + prec - 1 := by
        have hbranch : ¬ emin + prec - prec < emin := by omega
        simp [FTZ_exp, hbranch]
        omega
      simpa [hfexp_k, add_comm, add_left_comm, add_assoc] using hgoal
    · -- Constancy below fexp k = emin
      intro l hl
      have hlt : l - prec < emin := by
        have hl' : l ≤ emin + prec - 1 := by
          simpa [hfexp_k] using hl
        omega
      have hfl : FTZ_exp prec emin l = emin + prec - 1 := by
        simp [FTZ_exp, hlt]
      -- Conclude constancy below fexp k
      simpa [hfexp_k] using hfl

/-
Coq (FTZ.v):
Theorem generic_format_FTZ :
  forall x, FTZ_format x -> generic_format beta FTZ_exp x.

Proof outline (mirrors Flocq): an `FTZ_format` number is in particular an
`FLXN_format` number, hence in `generic_format` for `FLX_exp`.  For nonzero `x`
the normalized mantissa bound forces `prec ≤ mag beta (Fnum f)`, so
`emin + prec ≤ mag beta x` and the flush branch of `FTZ_exp` is unreachable at
`mag beta x`; there `FTZ_exp` and `FLX_exp` agree, and `generic_inclusion_mag`
transfers membership.
-/
omit [Fact (0 < prec)] in
private theorem FTZ_generic_format_run (beta : Int) [ValidRadix beta] (x : ℝ)
    (hx : FTZ_format prec emin beta x) :
    FloatSpec.Core.Generic_fmt.generic_format beta (FTZ_exp prec emin) x := by
  have hbeta : 1 < beta := ValidRadix.valid
  -- Step 1: FTZ_format ⊆ FLXN_format, which lands in `generic_format` for FLX_exp.
  have hflx :
      FloatSpec.Core.Generic_fmt.generic_format beta
        (FloatSpec.Core.FLX.FLX_exp prec) x := by
    refine FloatSpec.Core.FLX.generic_format_FLXN (prec := prec) beta x ?_
    obtain ⟨f, hxf, hb, _⟩ := hx
    exact ⟨f, hxf, hb⟩
  -- Step 2: at `mag beta x` the two exponent functions agree.
  refine FloatSpec.Core.Generic_fmt.generic_inclusion_mag beta
    (FloatSpec.Core.FLX.FLX_exp prec) (FTZ_exp prec emin) x hbeta ?_ hflx
  intro hx0
  obtain ⟨f, hxf, hb, hemin⟩ := hx
  obtain ⟨hlow, _⟩ := hb hx0
  have hfnum : f.Fnum ≠ 0 := by
    intro h0
    exact hx0 (by rw [hxf]; simp [FloatSpec.Core.Defs.F2R, h0])
  -- The normalized lower bound gives `prec - 1 < mag beta (Fnum f)`.
  have hmagm : prec - 1 < FloatSpec.Core.Raux.mag beta ((f.Fnum : Int) : ℝ) :=
    FloatSpec.Core.Raux.mag_gt_Zpower beta f.Fnum (prec - 1) hbeta hfnum hlow
  have hmagx : FloatSpec.Core.Raux.mag beta x
      = FloatSpec.Core.Raux.mag beta ((f.Fnum : Int) : ℝ) + f.Fexp := by
    rw [hxf]
    exact FloatSpec.Core.Float_prop.mag_F2R (beta := beta) f.Fnum f.Fexp hbeta hfnum
  have hbranch : ¬ (FloatSpec.Core.Raux.mag beta x - prec < emin) := by omega
  simp [FTZ_exp, FloatSpec.Core.FLX.FLX_exp, hbranch]

/-
Coq (FTZ.v):
Theorem FTZ_format_generic :
  forall x, generic_format beta FTZ_exp x -> FTZ_format x.

Proof outline (mirrors Flocq): zero is witnessed by `Float 0 emin`.  For nonzero
`x`, `mag_generic_gt` says the canonical exponent is strictly below `mag beta x`;
since the flush value `emin + prec - 1` is *above* `mag beta x` exactly when the
flush branch is taken, that branch is impossible and `cexp = mag beta x - prec`.
The canonical float then has a mantissa normalized between `β^(prec-1)` and
`β^prec`.
-/
private theorem FTZ_format_generic_run (beta : Int) [ValidRadix beta] (x : ℝ)
    (hx : FloatSpec.Core.Generic_fmt.generic_format beta (FTZ_exp prec emin) x) :
    FTZ_format prec emin beta x := by
  classical
  have hbeta : 1 < beta := ValidRadix.valid
  have hbposR : (0 : ℝ) < (beta : ℝ) := by
    exact_mod_cast lt_trans Int.zero_lt_one hbeta
  have hbne : (beta : ℝ) ≠ 0 := ne_of_gt hbposR
  have hprec : 0 < prec := Fact.out
  by_cases hx0 : x = 0
  · refine ⟨(FloatSpec.Core.Defs.FlocqFloat.mk 0 emin :
      FloatSpec.Core.Defs.FlocqFloat beta), ?_, ?_, le_rfl⟩
    · simp [hx0, FloatSpec.Core.Defs.F2R]
    · intro h; exact absurd hx0 h
  · set ex : Int := FloatSpec.Core.Raux.mag beta x with hex
    -- The canonical exponent of a nonzero generic number is below its magnitude.
    have hcexp_lt : FTZ_exp prec emin ex < ex := by
      have h := FloatSpec.Core.Generic_fmt.mag_generic_gt beta (FTZ_exp prec emin) x
      simpa [FloatSpec.Core.Generic_fmt.cexp, wp, PostCond.noThrow, Id.run, pure, hex]
        using h ⟨hbeta, hx0, hx⟩
    -- Hence the flush branch is unreachable.
    have hbranch : ¬ (ex - prec < emin) := by
      intro hlt
      simp only [FTZ_exp, hlt, ite_true] at hcexp_lt
      omega
    have hcexp : FloatSpec.Core.Generic_fmt.cexp beta (FTZ_exp prec emin) x = ex - prec := by
      simp [FloatSpec.Core.Generic_fmt.cexp, FTZ_exp, hbranch, ← hex]
    set m : Int := FloatSpec.Core.Raux.Ztrunc
      (FloatSpec.Core.Generic_fmt.scaled_mantissa beta (FTZ_exp prec emin) x) with hm
    -- The scaled mantissa is exactly `m`.
    have hsm_eq :
        FloatSpec.Core.Generic_fmt.scaled_mantissa beta (FTZ_exp prec emin) x = (m : ℝ) := by
      have h := FloatSpec.Core.Generic_fmt.scaled_mantissa_generic
        (beta := beta) (fexp := FTZ_exp prec emin) x hx
      simpa [wp, PostCond.noThrow, Id.run, pure, hm] using h
    have hxeq : x = (m : ℝ) * (beta : ℝ) ^ (ex - prec) := by
      simpa [FloatSpec.Core.Generic_fmt.generic_format, hcexp, hm] using hx
    -- Upper bound: |m| < β^prec.
    have hupperR : |(m : ℝ)| < (beta : ℝ) ^ prec := by
      have h := FloatSpec.Core.Generic_fmt.scaled_mantissa_lt_bpow
        (beta := beta) (fexp := FTZ_exp prec emin) (x := x) hbeta
      rw [hsm_eq, hcexp] at h
      simpa [← hex, sub_sub_cancel] using h
    -- Lower bound: β^(prec-1) ≤ |m|.
    have hlowerR : (beta : ℝ) ^ (prec - 1) ≤ |(m : ℝ)| := by
      have hmag_low : (beta : ℝ) ^ (ex - 1) ≤ |x| :=
        FloatSpec.Core.Raux.bpow_mag_le beta x hbeta hx0
      have hpow_pos : 0 < (beta : ℝ) ^ (prec - ex) := zpow_pos hbposR _
      have hmul :
          (beta : ℝ) ^ (ex - 1) * (beta : ℝ) ^ (prec - ex) ≤
            |x| * (beta : ℝ) ^ (prec - ex) :=
        mul_le_mul_of_nonneg_right hmag_low (le_of_lt hpow_pos)
      have hcollapse :
          (beta : ℝ) ^ (ex - 1) * (beta : ℝ) ^ (prec - ex) = (beta : ℝ) ^ (prec - 1) := by
        rw [← zpow_add₀ hbne]
        congr 1
        ring
      have habs : |x| * (beta : ℝ) ^ (prec - ex) = |(m : ℝ)| := by
        rw [hxeq, abs_mul, abs_of_pos (zpow_pos hbposR (ex - prec)), mul_assoc,
          ← zpow_add₀ hbne]
        have : (ex - prec) + (prec - ex) = (0 : Int) := by ring
        rw [this, zpow_zero, mul_one]
      rw [hcollapse, habs] at hmul
      exact hmul
    -- Transfer the two real bounds to the integer `Zpower` bounds.
    have hpowR : ∀ k : Int, 0 ≤ k →
        ((FloatSpec.Core.Zaux.Zpower beta k : Int) : ℝ) = (beta : ℝ) ^ k := by
      intro k hk
      have heq : (k.toNat : Int) = k := Int.toNat_of_nonneg hk
      simp [FloatSpec.Core.Zaux.Zpower, hk, Int.cast_pow, ← zpow_natCast, heq]
    refine ⟨(FloatSpec.Core.Defs.FlocqFloat.mk m (ex - prec) :
      FloatSpec.Core.Defs.FlocqFloat beta), hxeq, ?_, ?_⟩
    swap
    · show emin ≤ ex - prec
      omega
    intro _
    constructor
    · have : ((FloatSpec.Core.Zaux.Zpower beta (prec - 1) : Int) : ℝ) ≤ ((|m| : Int) : ℝ) := by
        rw [hpowR (prec - 1) (by omega), Int.cast_abs]
        exact hlowerR
      exact_mod_cast this
    · have : ((|m| : Int) : ℝ) < ((FloatSpec.Core.Zaux.Zpower beta prec : Int) : ℝ) := by
        rw [hpowR prec (by omega), Int.cast_abs]
        exact hupperR
      exact_mod_cast this

/-- The source-shaped FTZ carrier agrees with its generic-format characterization. -/
theorem FTZ_format_iff_generic (beta : Int) [ValidRadix beta] (x : ℝ) :
    FTZ_format prec emin beta x ↔
      FloatSpec.Core.Generic_fmt.generic_format beta (FTZ_exp prec emin) x :=
  ⟨FTZ_generic_format_run (prec := prec) (emin := emin) beta x,
   FTZ_format_generic_run (prec := prec) (emin := emin) beta x⟩

/-- Specification: FTZ exponent function correctness

    The FTZ exponent function correctly implements flush-to-zero
    semantics, choosing between precision-based and minimum
    exponents based on the magnitude of the input.
    Local arithmetic regression for the Lean `FTZ_exp` implementation.
-/
theorem FTZ_exp_correct_spec (e : Int) :
    FTZ_exp prec emin e = if e - prec < emin then emin + prec - 1 else e - prec := by
  rfl

/-- Legacy arithmetic regression: `Ztrunc 0 = 0`.

    This does not state `FTZ_format` membership.  The translated Flocq
    structural contract is `FTZ_format_satisfies_any`.
-/
theorem FTZ_format_0_spec (beta : Int) [ValidRadix beta] (hβ : beta > 1) :
    FloatSpec.Core.Raux.Ztrunc (0 : ℝ) = 0 := by
  -- Ztrunc 0 reduces to ⌊0⌋, which is 0.
  simp [FloatSpec.Core.Raux.Ztrunc]

/-- Legacy arithmetic regression: `Ztrunc (-x) + Ztrunc x = 0`.

    This does not state `FTZ_format` membership.  Actual FTZ negation
    closure is a field of `FTZ_format_satisfies_any`.
-/
theorem FTZ_format_opp_spec (beta : Int) [ValidRadix beta] (x : ℝ) :
    FloatSpec.Core.Raux.Ztrunc (-x) + FloatSpec.Core.Raux.Ztrunc x = 0 := by
  -- Use truncation under negation: Ztrunc (-x) = - Ztrunc x
  rw [FloatSpec.Core.Generic_fmt.Ztrunc_neg]
  exact neg_add_cancel _

/-- Legacy arithmetic regression: `Ztrunc |x|` is the absolute value of `Ztrunc x`.

    This does not state `FTZ_format` membership.  Actual FTZ absolute-value
    closure follows from zero and negation closure in
    `FTZ_format_satisfies_any`; this helper proves only an integer identity.
-/
theorem FTZ_format_abs_spec (beta : Int) [ValidRadix beta] (x : ℝ) :
    FloatSpec.Core.Raux.Ztrunc (abs x) =
      Int.ofNat ((FloatSpec.Core.Raux.Ztrunc x).natAbs) := by
  -- Compute Ztrunc(|x|) in terms of Ztrunc(x)
  have zabs_eq :
      (FloatSpec.Core.Raux.Ztrunc (abs x))
        = Int.ofNat ((FloatSpec.Core.Raux.Ztrunc x).natAbs) := by
    -- Expand truncation and split on the sign of x; |x| ≥ 0 always
    simp [FloatSpec.Core.Raux.Ztrunc, not_lt.mpr (abs_nonneg x)]
    by_cases hxlt : x < 0
    · -- Negative case: |x| = -x and ⌊-x⌋ = -⌈x⌉; natAbs coerces to |·|
      have hxle : x ≤ 0 := le_of_lt hxlt
      have habs : |x| = -x := by simpa using (abs_of_neg hxlt)
      have hceil_nonpos : Int.ceil x ≤ 0 := (Int.ceil_le).mpr (by simpa using hxle)
      have hAbsCeil : |Int.ceil x| = - Int.ceil x := abs_of_nonpos hceil_nonpos
      have hNatAbsCeil : ((Int.ceil x).natAbs : Int) = |Int.ceil x| :=
        (Int.natCast_natAbs (Int.ceil x))
      -- LHS: ⌊|x|⌋ = ⌊-x⌋ = -⌈x⌉; RHS: ↑(natAbs ⌈x⌉) = |⌈x⌉| = -⌈x⌉
      simpa [habs, Int.floor_neg, hxlt, hAbsCeil, hNatAbsCeil]
    · -- Nonnegative case: |x| = x and ⌊x⌋ ≥ 0, so |⌊x⌋| = ⌊x⌋
      have hxge : 0 ≤ x := le_of_not_gt hxlt
      have hxabs : |x| = x := by simpa using (abs_of_nonneg hxge)
      -- ⌊x⌋ ≥ 0 when x ≥ 0
      have hfloor_nonneg : 0 ≤ (Int.floor x : Int) := by
        have : ((0 : Int) : ℝ) ≤ x := by simpa using hxge
        have : (0 : Int) ≤ Int.floor x := (Int.le_floor).mpr this
        simpa using this
      have hAbsFloor : |Int.floor x| = Int.floor x := abs_of_nonneg hfloor_nonneg
      have hNatAbsFloor : ((Int.floor x).natAbs : Int) = |Int.floor x| :=
        (Int.natCast_natAbs (Int.floor x))
      -- LHS: ⌊|x|⌋ = ⌊x⌋; RHS: ↑(natAbs ⌊x⌋) = |⌊x⌋| = ⌊x⌋
      simpa [hxabs, hAbsFloor, hNatAbsFloor, hxlt]
  exact zabs_eq

end FloatSpec.Core.FTZ

namespace FloatSpec.Core.FTZ

variable (prec emin : Int)

/-- Coq ({lit}`FTZ.v`):
Theorem {lit}`FLXN_format_FTZ`:
  {lit}`forall x, FTZ_format x -> FLXN_format beta prec x.`

Lean (spec): Any FTZ-format number is in {lean}`FloatSpec.Core.FLX.FLXN_format` for the same
base and precision.
-/
@[flocq_source "src/Core/FTZ.v" 71 "FLXN_format_FTZ"]
theorem FLXN_format_FTZ (beta : Int) [ValidRadix beta] (x : ℝ) :
    FTZ_format prec emin beta x → FloatSpec.Core.FLX.FLXN_format prec beta x := by
  rintro ⟨f, hval, hbound, _⟩
  exact ⟨f, hval, hbound⟩

end FloatSpec.Core.FTZ

namespace FloatSpec.Core.FTZ

variable (prec emin : Int) [Fact (0 < prec)]

/-- Coq ({lit}`FTZ.v`):
Theorem {lit}`FTZ_format_FLXN`:
  {lit}`forall x : R, (bpow (emin + prec - 1) <= Rabs x)%R -> FLXN_format beta prec x -> FTZ_format x.`

Lean (spec): If {lit}`|x| ≥ β^(emin + prec - 1)` and x is in {lean}`FloatSpec.Core.FLX.FLXN_format`,
then x is in {lean}`FloatSpec.Core.FTZ.FTZ_format` for the same base and precision.
-/
theorem FTZ_format_FLXN (beta : Int) [ValidRadix beta] (x : ℝ)
    (hlb : (beta : ℝ) ^ (emin + prec - 1) ≤ |x|)
    (hx_flx : FloatSpec.Core.FLX.FLXN_format (prec := prec) beta x) :
    FTZ_format prec emin beta x := by
  -- The radix invariant carried by `ValidRadix`
  have hβ : 1 < beta := ValidRadix.valid
  -- Abbreviations
  set e1 : Int := emin + prec - 1
  -- Provide the FLX generic_format view of the hypothesis
  have hx_gf_flx :
      (FloatSpec.Core.Generic_fmt.generic_format beta (FloatSpec.Core.FLX.FLX_exp prec) x) := by
    exact (FloatSpec.Core.FLX.generic_format_FLXN (prec := prec) beta x) hx_flx
  -- Case split on whether the lower bound is strict
  by_cases hstrict : (beta : ℝ) ^ e1 < |x|
  ·
    -- Strict lower bound case: use inclusion over the band (e1, M+1]
    classical
    -- Notation: M := mag beta x
    set M : Int := (FloatSpec.Core.Raux.mag beta x) with hM
    -- Strict upper bound at M+1: |x| < β^(M+1)
    have hupper : |x| < (beta : ℝ) ^ (M + 1) := by
      -- Using Raux.bpow_mag_gt with e := M+1
      have hxlt :=
        (FloatSpec.Core.Raux.bpow_mag_gt_from_strict_mag_payload (beta := beta) (x := x) (e := M + 1))
      -- Precondition: 1 < beta ∧ (mag x) < M+1
      have hpre' : 1 < beta ∧ (FloatSpec.Core.Raux.mag beta x) < (M + 1) := by
        have hlt : M < M + 1 := by
          simpa [add_comm, add_left_comm, add_assoc] using
            (lt_add_of_pos_right M (by exact Int.zero_lt_one))
        simpa [hM] using And.intro hβ hlt
      -- Discharge the Hoare triple and get the raw inequality
      simpa [FloatSpec.Core.Raux.abs_val] using (hxlt hpre'.1 hpre'.2 trivial)
    -- Pointwise exponent inequality on (e1, M+1]: FTZ_exp e = FLX_exp e
    have hle_band : ∀ e : Int, e1 < e ∧ e ≤ (M + 1) →
        FTZ_exp prec emin e ≤ FloatSpec.Core.FLX.FLX_exp prec e := by
      intro e he
      have he_ge : e1 + 1 ≤ e := (Int.add_one_le_iff).2 he.left
      -- Hence e - prec ≥ emin
      have hbranch : emin ≤ e - prec := by
        -- e ≥ emin + prec
        have : emin + prec ≤ e := by
          -- e1 + 1 = emin + prec
          have : e1 + 1 = emin + prec := by
            -- e1 = emin + prec - 1
            have : e1 = emin + prec - 1 := rfl
            simpa [this, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
          exact le_trans (by simpa [this] using he_ge) le_rfl
        -- Subtract prec on both sides
        have := sub_le_sub_right this prec
        simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
      -- In this band, FTZ_exp = e - prec, same as FLX_exp.
      have hnot : ¬ e - prec < emin := not_lt.mpr hbranch
      simpa [FTZ_exp, FloatSpec.Core.FLX.FLX_exp, hnot]
    -- Apply inclusion on the strict band (e1, M+1]
    have hrun :
        (FloatSpec.Core.Generic_fmt.generic_format beta (FTZ_exp prec emin) x) := by
      exact
        (FloatSpec.Core.Generic_fmt.generic_inclusion_lt_ge
          (beta := beta)
          (fexp1 := FloatSpec.Core.FLX.FLX_exp prec)
          (fexp2 := FTZ_exp prec emin)
          (e1 := e1)
          (e2 := M + 1))
          hβ hle_band x ⟨le_of_lt hstrict, hupper⟩ hx_gf_flx
    -- Repackage to FTZ_format
    exact (FTZ_format_iff_generic (prec := prec) (emin := emin) beta x).mpr hrun
  ·
    -- Boundary case: |x| = β^e1. Build a direct FTZ witness via bpow.
    have heq : |x| = (beta : ℝ) ^ e1 := le_antisymm (le_of_not_gt hstrict) hlb
    -- Show FTZ_exp e1 ≤ e1
    have hle_e1 : FTZ_exp prec emin e1 ≤ e1 := by
      -- Candidate bounds: (e1 - prec) ≤ e1 and emin ≤ e1
      have hsub : e1 - prec ≤ e1 := by
        exact sub_le_self _ (le_of_lt (Fact.out : 0 < prec))
      have hmin : emin ≤ e1 := by
        -- e1 = emin + (prec - 1) and (prec - 1) ≥ 0
        have hprec1 : 1 ≤ prec := by simpa using (Int.add_one_le_iff).mpr (Fact.out : 0 < prec)
        have hnonneg : 0 ≤ prec - 1 := by
          simpa [sub_eq_add_neg] using sub_nonneg.mpr hprec1
        -- emin ≤ emin + (prec - 1) = e1
        simpa [e1, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
          using le_add_of_nonneg_right hnonneg
      have hbranch : e1 - prec < emin := by
        simp [e1]
        omega
      simp [FTZ_exp, hbranch, e1]
    -- Apply generic_format_bpow' for FTZ_exp at exponent e1 and rewrite x by |x|
    have hfmt_ftz :
        (FloatSpec.Core.Generic_fmt.generic_format beta (FTZ_exp prec emin) ((beta : ℝ) ^ e1)) := by
      exact
        (FloatSpec.Core.Generic_fmt.generic_format_bpow'
          (beta := beta) (fexp := FTZ_exp prec emin) (e := e1))
          ⟨hβ, hle_e1⟩
    -- Finally, since |x| = β^e1, FTZ holds for |x|, and hence for x by symmetry of abs in generic_format
    -- We can use that generic_format works on the exact real value; replace x by its absolute value equality.
    -- Build the target by rewriting x = (sign x) * |x|, then using generic_format closure under sign.
    -- Here, we simply rewrite the goal at x using heq.
    -- generic_format is a predicate on x; equality of reals suffices.
    have : (FloatSpec.Core.Generic_fmt.generic_format beta (FTZ_exp prec emin) x) := by
      classical
      rcases lt_trichotomy x 0 with hlt | heq0 | hgt
      · -- x < 0 ⇒ |x| = -x
        have habs : |x| = -x := by simpa using (abs_of_neg hlt)
        -- Start from generic_format at |x| = β^e1
        have h_at_abs : (FloatSpec.Core.Generic_fmt.generic_format beta (FTZ_exp prec emin) |x|) := by
          simpa [heq.symm] using hfmt_ftz
        -- Transfer along x = -|x|
        have hxneg : (FloatSpec.Core.Generic_fmt.generic_format beta (FTZ_exp prec emin) (-|x|)) := by
          -- Use closure under opposite from |x| to -|x|
          have := FloatSpec.Core.Generic_fmt.generic_format_opp (beta := beta) (fexp := FTZ_exp prec emin) (x := |x|)
          simpa using this h_at_abs
        -- Since x = -|x| in this branch, rewrite
        simpa [habs] using hxneg
      · -- x = 0 contradicts the lower bound since β^e1 > 0
        exfalso
        -- β > 1 ⇒ β^e1 > 0
        have hbposℤ : (0 : Int) < beta := lt_trans Int.zero_lt_one hβ
        have hbpos : (0 : ℝ) < (beta : ℝ) := by exact_mod_cast hbposℤ
        have hbpow_pos : 0 < (beta : ℝ) ^ e1 := zpow_pos hbpos _
        have hle0 : (beta : ℝ) ^ e1 ≤ 0 := by simpa [heq0, abs_zero] using hlb
        exact (not_le_of_gt hbpow_pos) hle0
      · -- x > 0 ⇒ |x| = x
        have habs : |x| = x := by simpa using (abs_of_pos hgt)
        have : (FloatSpec.Core.Generic_fmt.generic_format beta (FTZ_exp prec emin) |x|) := by
          simpa [heq.symm] using hfmt_ftz
        simpa [habs] using this
    -- Repackage to FTZ_format
    exact (FTZ_format_iff_generic (prec := prec) (emin := emin) beta x).mpr this

end FloatSpec.Core.FTZ

namespace FloatSpec.Core.FTZ

variable (prec emin : Int) [Fact (0 < prec)]

/-- Coq ({lit}`FTZ.v`):
Theorem {lit}`round_FTZ_FLX`:
{lit}`forall x, (bpow (emin + prec - 1) <= Rabs x) -> round beta FTZ_exp Zrnd_FTZ x = round beta (FLX_exp prec) rnd x.`

Lean (spec): Under the lower-bound condition on |x|, rounding in
FTZ equals rounding in FLX for any rounding predicate {lit}`rnd`.
-/
theorem round_FTZ_FLX (beta : Int) [ValidRadix beta]
    [FloatSpec.Core.Generic_fmt.Valid_exp (FloatSpec.Core.FLX.FLX_exp prec)]
    (rnd : ℝ → Int) [Valid_rnd rnd] (x : ℝ) :
    (beta : ℝ) ^ (emin + prec - 1) ≤ |x| →
      round_to_generic (beta := beta) (fexp := FTZ_exp prec emin)
          (mode := Zrnd_FTZ rnd) x =
      round_to_generic (beta := beta) (fexp := FloatSpec.Core.FLX.FLX_exp prec)
          (mode := rnd) x := by
  intro hx
  let M := FloatSpec.Core.Raux.mag beta x
  have hβ : 1 < beta := ValidRadix.valid
  have hbpos : (0 : ℝ) < beta := by
    exact_mod_cast (lt_trans Int.zero_lt_one hβ)
  have hbne : (beta : ℝ) ≠ 0 := ne_of_gt hbpos
  have hxne : x ≠ 0 := by
    have hp : 0 < (beta : ℝ) ^ (emin + prec - 1) := zpow_pos hbpos _
    exact (abs_pos.mp (lt_of_lt_of_le hp hx))
  have hmag : emin + prec ≤ M :=
    FloatSpec.Core.Raux.mag_ge_bpow beta x (emin + prec) hβ hx
  have hcase : emin ≤ M - prec := by omega
  have hexp : FTZ_exp prec emin M = FloatSpec.Core.FLX.FLX_exp prec M := by
    simp [FTZ_exp, FloatSpec.Core.FLX.FLX_exp, hcase]
  have hmagLower : (beta : ℝ) ^ (M - 1) ≤ |x| := by
    simpa [FloatSpec.Core.Raux.abs_val] using
      (FloatSpec.Core.Raux.bpow_mag_le_from_exp_payload beta x M hβ hxne le_rfl True.intro)
  have hprec : 0 < prec := Fact.out
  have hpowOne : (1 : ℝ) ≤ (beta : ℝ) ^ (prec - 1) := by
    exact one_le_zpow₀ (le_of_lt (by exact_mod_cast hβ : (1 : ℝ) < beta)) (by omega)
  have hfactorPos : 0 < (beta : ℝ) ^ (prec - M) := zpow_pos hbpos _
  have hscaledLower :
      (1 : ℝ) ≤ |x * (beta : ℝ) ^ (prec - M)| := by
    have hmul :
        (beta : ℝ) ^ (M - 1) * (beta : ℝ) ^ (prec - M) ≤
          |x| * (beta : ℝ) ^ (prec - M) :=
      mul_le_mul_of_nonneg_right hmagLower (le_of_lt hfactorPos)
    have hpow :
        (beta : ℝ) ^ (M - 1) * (beta : ℝ) ^ (prec - M) =
          (beta : ℝ) ^ (prec - 1) := by
      calc
        (beta : ℝ) ^ (M - 1) * (beta : ℝ) ^ (prec - M) =
            (beta : ℝ) ^ ((M - 1) + (prec - M)) :=
          (zpow_add₀ hbne (M - 1) (prec - M)).symm
        _ = (beta : ℝ) ^ (prec - 1) := by congr 1 <;> omega
    calc
      (1 : ℝ) ≤ (beta : ℝ) ^ (prec - 1) := hpowOne
      _ ≤ |x| * (beta : ℝ) ^ (prec - M) := by simpa [hpow] using hmul
      _ = |x * (beta : ℝ) ^ (prec - M)| := by
        rw [abs_mul, abs_of_pos hfactorPos]
  have hscaled :
      (1 : ℝ) ≤
        |FloatSpec.Core.Generic_fmt.scaled_mantissa beta
          (FloatSpec.Core.FLX.FLX_exp prec) x| := by
    simpa [FloatSpec.Core.Generic_fmt.scaled_mantissa,
      FloatSpec.Core.Generic_fmt.cexp, FloatSpec.Core.FLX.FLX_exp, M,
      sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hscaledLower
  simp only [round_to_generic, FloatSpec.Core.Generic_fmt.roundR,
    FloatSpec.Core.Generic_fmt.scaled_mantissa,
    FloatSpec.Core.Generic_fmt.cexp]
  rw [hexp]
  have hscaledBool : FloatSpec.Core.Raux.Rle_bool 1
      |x * (beta : ℝ) ^ (-FloatSpec.Core.FLX.FLX_exp prec M)| = true := by
    simpa [FloatSpec.Core.Raux.Rle_bool, FloatSpec.Core.FLX.FLX_exp,
      sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hscaledLower
  simp only [Zrnd_FTZ, hscaledBool, Bool.true_eq, ite_true]
  simpa [FloatSpec.Core.Generic_fmt.scaled_mantissa,
    FloatSpec.Core.Generic_fmt.cexp, M] using hscaled

end FloatSpec.Core.FTZ

namespace FloatSpec.Core.FTZ

variable (prec emin : Int) [Fact (0 < prec)]

/-- Coq ({lit}`FTZ.v`):
Theorem {lit}`round_FTZ_small`:
{lit}`forall x, (Rabs x < bpow (emin + prec - 1)) -> round beta FTZ_exp Zrnd_FTZ x = 0.`

Lean (spec): If |x| is smaller than {lit}`β^(emin+prec-1)`, then rounding in
FTZ flushes to zero for any rounding predicate {lit}`rnd`.
-/
theorem round_FTZ_small (beta : Int) [ValidRadix beta]
    (rnd : ℝ → Int) [Valid_rnd rnd] (x : ℝ)
    (hxlt : |x| < (beta : ℝ) ^ (emin + prec - 1)) :
    round_to_generic (beta := beta) (fexp := FTZ_exp prec emin)
      (mode := Zrnd_FTZ rnd) x = 0 := by
  have hβ : 1 < beta := ValidRadix.valid
  let e0 : Int := emin + prec - 1
  -- From |x| < β^e0 and the FTZ small-regime property at e0,
  -- the scaled mantissa is strictly within (-1, 1).
  have hbranch : e0 - prec < emin := by
    simp [e0]
    omega
  have hfexp_e0 : FTZ_exp prec emin e0 = e0 := by
    simp [FTZ_exp, hbranch, e0]
  have hex_le : e0 ≤ FTZ_exp prec emin e0 := by
    simpa [hfexp_e0]
  have hsm_lt1 :
      abs (FloatSpec.Core.Generic_fmt.scaled_mantissa beta (FTZ_exp prec emin) x) < 1 := by
    -- Apply the generic scaled_mantissa bound with ex = emin
    exact
      FloatSpec.Core.Generic_fmt.scaled_mantissa_lt_1
        (beta := beta) (fexp := FTZ_exp prec emin) (x := x) (ex := e0)
        hβ (by simpa using hxlt) hex_le
  -- Let sm be the scaled mantissa; from |sm| < 1 we deduce Ztrunc sm = 0
  set sm : ℝ := (FloatSpec.Core.Generic_fmt.scaled_mantissa beta (FTZ_exp prec emin) x) with hsm
  have hbounds : -1 < sm ∧ sm < 1 := by
    -- abs sm < 1 ↔ -1 < sm ∧ sm < 1
    simpa [hsm] using (abs_lt.mp hsm_lt1)
  have hmode : Zrnd_FTZ rnd sm = 0 := by
    have hnot : ¬ 1 ≤ |sm| := not_le.mpr (by simpa [hsm] using hsm_lt1)
    simp [Zrnd_FTZ, FloatSpec.Core.Raux.Rle_bool, hnot]
  have hround :
      round_to_generic (beta := beta) (fexp := FTZ_exp prec emin)
        (mode := Zrnd_FTZ rnd) x = 0 := by
    have hmode' : Zrnd_FTZ rnd
        (FloatSpec.Core.Generic_fmt.scaled_mantissa beta
          (FTZ_exp prec emin) x) = 0 := by
      simpa [hsm] using hmode
    simp [round_to_generic, FloatSpec.Core.Generic_fmt.roundR, hmode']
  exact hround

end FloatSpec.Core.FTZ

namespace FloatSpec.Core.FTZ

variable (prec emin : Int) [Fact (0 < prec)]

/-
Coq (FTZ.v):
Theorem generic_format_FTZ :
  forall x, FTZ_format x -> generic_format beta FTZ_exp x.
-/
omit [Fact (0 < prec)] in
@[flocq_source "src/Core/FTZ.v" 80 "generic_format_FTZ"]
theorem generic_format_FTZ (beta : Int) [ValidRadix beta] (x : ℝ) :
    FTZ_format prec emin beta x →
      FloatSpec.Core.Generic_fmt.generic_format beta (FTZ_exp prec emin) x := by
  exact FTZ_generic_format_run (prec := prec) (emin := emin) beta x

/-
Coq (FTZ.v):
Theorem FTZ_format_generic :
  forall x, generic_format beta FTZ_exp x -> FTZ_format x.
-/
theorem FTZ_format_generic (beta : Int) [ValidRadix beta] (x : ℝ) :
    FloatSpec.Core.Generic_fmt.generic_format beta (FTZ_exp prec emin) x →
      FTZ_format prec emin beta x := by
  exact (FTZ_format_iff_generic (prec := prec) (emin := emin) beta x).mpr

end FloatSpec.Core.FTZ

namespace FloatSpec.Core.FTZ

variable (prec emin : Int) [Fact (0 < prec)]

/-
Coq (FTZ.v):
Theorem FTZ_format_satisfies_any :
  satisfies_any FTZ_format.
-/
theorem FTZ_format_satisfies_any (beta : Int) [ValidRadix beta] :
    FloatSpec.Core.Generic_fmt.satisfies_any (fun y => FTZ_format prec emin beta y) := by
  apply FloatSpec.Core.Generic_fmt.satisfies_any_eq
    (F₁ := fun y => FloatSpec.Core.Generic_fmt.generic_format beta (FTZ_exp prec emin) y)
  · intro x
    constructor
    · exact FTZ_format_generic (prec := prec) (emin := emin) beta x
    · exact generic_format_FTZ (prec := prec) (emin := emin) beta x
  · exact FloatSpec.Core.Generic_fmt.generic_format_satisfies_any
      (beta := beta) (fexp := FTZ_exp prec emin)

end FloatSpec.Core.FTZ

namespace FloatSpec.Core.FTZ

variable (prec emin : Int) [Fact (0 < prec)]

/-- Coq ({lit}`FTZ.v`):
Theorem {lit}`ulp_FTZ_0`: {lit}`ulp beta FTZ_exp 0 = bpow (emin + prec - 1)`.

Lean (spec): The ULP under FTZ at 0 equals {lit}`β^(emin+prec-1)`.
-/
theorem ulp_FTZ_0 (beta : Int) [ValidRadix beta] :
    FloatSpec.Core.Ulp.ulp beta (FTZ_exp prec emin) 0 = (beta : ℝ) ^ (emin + prec - 1) := by
  classical
  let e0 : Int := emin + prec - 1
  have hbranch : e0 - prec < emin := by
    simp [e0]
    omega
  have hfexp_e0 : FTZ_exp prec emin e0 = e0 := by
    simp [FTZ_exp, hbranch, e0]
  -- Hence there exists a negligible exponent witness (take `n = e0`).
  have h_le_wit : e0 ≤ FTZ_exp prec emin e0 := by
    simpa [hfexp_e0]
  -- Use the canonical spec for `negligible_exp` to extract a concrete witness.
  have hsome : ∃ n : Int,
      FloatSpec.Core.Ulp.negligible_exp (FTZ_exp prec emin) = some n ∧ n ≤ FTZ_exp prec emin n := by
    have H := FloatSpec.Core.Ulp.negligible_exp_spec' (fexp := FTZ_exp prec emin)
    -- Eliminate the impossible `none` branch using the witness at `emin`.
    cases H with
    | inl hnone =>
        rcases hnone with ⟨hEqNone, hall_lt⟩
        have : (FTZ_exp prec emin e0) < e0 := hall_lt e0
        -- Contradiction with `fexp e0 = e0`.
        have : False := by simpa [hfexp_e0] using this
        cases this
    | inr hsome =>
        exact hsome
  rcases hsome with ⟨n, hneg_eq, hnle⟩
  -- Any negligible witness yields the same exponent; specialize to `e0`.
  have hfexp_eq : FTZ_exp prec emin n = FTZ_exp prec emin e0 := by
    simpa using
      (FloatSpec.Core.Ulp.fexp_negligible_exp_eq
        (fexp := FTZ_exp prec emin) (n := n) (m := e0)
        hnle h_le_wit)
  -- Compute ulp at 0 using the `some` branch and rewrite the exponent.
  have : FloatSpec.Core.Ulp.ulp beta (FTZ_exp prec emin) 0 = ((beta : ℝ) ^ e0) := by
    unfold FloatSpec.Core.Ulp.ulp
    -- Select the `some n` branch and rewrite its exponent to `e0`.
    simpa [hneg_eq, hfexp_eq, hfexp_e0]
  exact this

end FloatSpec.Core.FTZ
