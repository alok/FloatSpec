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

import FloatSpec.Linter.OmegaLinter
import FloatSpec.src.Core.Defs
import FloatSpec.src.Core.Generic_fmt
import FloatSpec.src.Core.Round_NE
import FloatSpec.src.Core.Ulp
import Mathlib.Data.Real.Basic

open Real
open FloatSpec.Core.Generic_fmt

set_option linter.coqSource true
set_option warningAsError true

namespace FloatSpec.Core.FIX

variable (emin : Int)

/-- Fixed-point exponent function

    In fixed-point format, all numbers have the same exponent emin.
    This creates a uniform representation where the position of
    the binary/decimal point is fixed across all values.
-/
-- Source: https://gitlab.inria.fr/flocq/flocq/-/blob/7aab8f55bceec0cfafc3b3bc0e77e0dbb5a70c5f/src/Core/FIX.v#L38
@[flocq_source "src/Core/FIX.v" 38 "FIX_exp"]
def FIX_exp (_ : Int) : Int :=
  emin

/-- Specification: fixed exponent yields emin

    The fixed-point exponent function ignores its input and
    yields the fixed exponent emin. This ensures
    uniform scaling across all representable values.
-/
theorem FIX_exp_spec (e : Int) : FIX_exp emin e = emin := rfl

/-- Fixed-point format predicate: a float witness whose exponent is `emin`. -/
-- Source: https://gitlab.inria.fr/flocq/flocq/-/blob/7aab8f55bceec0cfafc3b3bc0e77e0dbb5a70c5f/src/Core/FIX.v#L34
@[flocq_source "src/Core/FIX.v" 34 "FIX_format"]
def FIX_format (beta : Int) [ValidRadix beta] (x : ℝ) : Prop :=
  ∃ f : FloatSpec.Core.Defs.FlocqFloat beta,
    x = FloatSpec.Core.Defs.F2R f ∧ f.Fexp = emin

/-- Exponent-validity instance for the fixed exponent function. -/
instance FIX_exp_valid :
    FloatSpec.Core.Generic_fmt.Valid_exp (FIX_exp emin) := by
  refine ⟨?_⟩
  intro k
  refine And.intro ?h1 ?h2
  · -- Large regime: if fexp k < k, then fexp (k+1) ≤ k
    intro hk
    -- Here fexp is constant = emin
    simpa [FIX_exp] using (le_of_lt hk)
  · -- Small regime: if k ≤ fexp k, then stability and constancy below fexp k
    intro hk
    refine And.intro ?hA ?hB
    · -- fexp (fexp k + 1) ≤ fexp k
      -- Both sides are emin for the constant fexp
      simpa [FIX_exp]
    · -- ∀ l ≤ fexp k, fexp l = fexp k
      intro l _
      simpa [FIX_exp]

/- Coq (FIX.v):
Global Instance FIX_exp_monotone : Monotone_exp FIX_exp.
-/
instance FIX_exp_monotone :
    FloatSpec.Core.Generic_fmt.Monotone_exp (FIX_exp emin) :=
  ⟨by
    intro a b hab
    exact le_rfl⟩

/- Coq (FIX.v):
Global Instance exists_NE_FIX :
      Exists_NE beta FIX_exp.
-/
instance exists_NE_FIX (beta : Int) [ValidRadix beta] :
    FloatSpec.Core.RoundNE.Exists_NE beta (FIX_exp emin) where
  exists_ne := by
    right
    intro e
    constructor
    · intro h
      simpa [FIX_exp] using h
    · intro _
      simp [FIX_exp]

/-- Zero belongs to the fixed-point format. -/
theorem FIX_format_zero (beta : Int) [ValidRadix beta] : FIX_format emin beta 0 := by
  refine ⟨⟨0, emin⟩, ?_, rfl⟩
  simp [FloatSpec.Core.Defs.F2R]

/-- The fixed-point format is closed under negation. -/
theorem FIX_format_neg (beta : Int) [ValidRadix beta] (x : ℝ)
    (hx : FIX_format emin beta x) : FIX_format emin beta (-x) := by
  rcases hx with ⟨f, hxf, hfexp⟩
  refine ⟨⟨-f.Fnum, f.Fexp⟩, ?_, hfexp⟩
  simp [hxf, FloatSpec.Core.Defs.F2R]

/-
Coq (FIX.v):
Theorem generic_format_FIX :
  forall x, FIX_format x -> generic_format beta FIX_exp x.
-/
theorem generic_format_FIX (beta : Int) [ValidRadix beta] (x : ℝ) :
    FIX_format emin beta x →
      FloatSpec.Core.Generic_fmt.generic_format beta (FIX_exp emin) x := by
  rintro ⟨f, rfl, hfexp⟩
  apply FloatSpec.Core.Generic_fmt.generic_format_canonical
  simpa [FloatSpec.Core.Generic_fmt.canonical, FIX_exp] using hfexp

/-
Coq (FIX.v):
Theorem FIX_format_generic :
  forall x, generic_format beta FIX_exp x -> FIX_format x.
-/
theorem FIX_format_generic (beta : Int) [ValidRadix beta] (x : ℝ) :
    FloatSpec.Core.Generic_fmt.generic_format beta (FIX_exp emin) x →
      FIX_format emin beta x := by
  intro hx
  obtain ⟨f, hxf, hcan⟩ :=
    FloatSpec.Core.Generic_fmt.canonical_generic_format beta (FIX_exp emin) x hx
  exact ⟨f, hxf, by simpa [FloatSpec.Core.Generic_fmt.canonical, FIX_exp] using hcan⟩

/-
Coq (FIX.v):
Theorem FIX_format_satisfies_any :
  satisfies_any FIX_format.
-/
theorem FIX_format_satisfies_any (beta : Int) [ValidRadix beta] :
    FloatSpec.Core.Generic_fmt.satisfies_any (fun y => FIX_format emin beta y) := by
  apply FloatSpec.Core.Generic_fmt.satisfies_any_eq
    (F₁ := fun y => FloatSpec.Core.Generic_fmt.generic_format beta (FIX_exp emin) y)
  · intro x
    constructor
    · exact FIX_format_generic (emin := emin) beta x
    · exact generic_format_FIX (emin := emin) beta x
  · exact FloatSpec.Core.Generic_fmt.generic_format_satisfies_any
      (beta := beta) (fexp := FIX_exp emin)

/-- Coq (FIX.v):
Theorem ulp_FIX : forall x, ulp beta FIX_exp x = bpow emin.

Lean (spec): For any real {name}`x`, the ULP under FIX exponent equals β^emin.
-/
private lemma ulp_FIX_run_eq (beta : Int) [ValidRadix beta] (emin : Int) (x : ℝ) :
    (FloatSpec.Core.Ulp.ulp beta (FIX_exp (emin := emin)) x) = (beta : ℝ) ^ emin := by
  classical
  by_cases hx : x = 0
  · subst hx
    rcases FloatSpec.Core.Ulp.negligible_exp_spec' (fexp := FIX_exp emin) with
      ⟨_hnone, hlt⟩ | ⟨n, hn, _hle⟩
    · have impossible : emin < emin := by simpa [FIX_exp] using hlt emin
      exact False.elim (lt_irrefl emin impossible)
    · simp [FloatSpec.Core.Ulp.ulp, hn, FIX_exp]
  · simp [FloatSpec.Core.Ulp.ulp, FloatSpec.Core.Generic_fmt.cexp, FloatSpec.Core.Raux.mag,
          FIX_exp, hx]

theorem ulp_FIX (beta : Int) [ValidRadix beta] (x : ℝ) :
    FloatSpec.Core.Ulp.ulp beta (FIX_exp emin) x = (beta : ℝ) ^ emin :=
  ulp_FIX_run_eq (beta := beta) (emin := emin) (x := x)

end FloatSpec.Core.FIX

namespace FloatSpec.Core.FIX

/-- Coq ({lit}`FIX.v`):
Theorem {lit}`round_FIX_IZR`: {lit}`forall f x, round radix2 (FIX_exp 0) f x = IZR (f x).`

Lean: for {lit}`fexp = FIX_exp 0`, the canonical exponent is zero, so the
result is exactly the integer selected by the supplied rounding function.
-/
theorem round_FIX_IZR
    (f : ℝ → Int) (x : ℝ) :
    round_to_generic (beta := 2) (fexp := FIX_exp (emin := (0 : Int)))
      (mode := f) x = ((f x : Int) : ℝ) := by
  -- Unfold the rounding model and compute with the constant exponent 0
  simp [
        round_to_generic,
        FloatSpec.Core.Generic_fmt.roundR,
        FloatSpec.Core.Generic_fmt.scaled_mantissa,
        FloatSpec.Core.Generic_fmt.cexp,
        FloatSpec.Core.Raux.mag,
        FIX_exp]

end FloatSpec.Core.FIX
