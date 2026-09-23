import FloatSpec.src.Core.Ulp

/-! Typed clients retain the pre-repair Lean conclusions and parameters, removing
only the Valid_exp binder absent from the paired compiled Rocq source type.
The radix bound {lit}`1 < beta` comes from {lit}`ValidRadix` unless a declaration
still takes it explicitly. They supplement the structural premise guards;
they are not automatic proofs of cross-language semantic equivalence. -/

namespace FloatSpec.Test.CorePremiseBoundary

/-- Expected source boundary: no exponent-validity premise. -/
theorem Ulp_negligible_exp_spec_unrestricted :
    ∀ (fexp : ℤ → ℤ) ,
  FloatSpec.Core.Ulp.negligible_exp_prop fexp (FloatSpec.Core.Ulp.negligible_exp fexp) := @FloatSpec.Core.Ulp.negligible_exp_spec

#print axioms Ulp_negligible_exp_spec_unrestricted

/-- Expected source boundary: no exponent-validity premise. -/
theorem Ulp_negligible_exp_spec_prime_unrestricted :
    ∀ (fexp : ℤ → ℤ) ,
  (FloatSpec.Core.Ulp.negligible_exp fexp = none ∧ ∀ (n : ℤ), fexp n < n) ∨
    ∃ n, FloatSpec.Core.Ulp.negligible_exp fexp = some n ∧ n ≤ fexp n := @FloatSpec.Core.Ulp.negligible_exp_spec'

#print axioms Ulp_negligible_exp_spec_prime_unrestricted

/-- Expected source boundary: no exponent-validity premise. -/
theorem Ulp_succ_le_plus_ulp_unrestricted :
    ∀ (beta : ℤ) [ValidRadix beta] (fexp : ℤ → ℤ)
  [FloatSpec.Core.Ulp.Monotone_exp fexp] (x : ℝ),
    FloatSpec.Core.Ulp.succ beta fexp x ≤ x + FloatSpec.Core.Ulp.ulp beta fexp x := @FloatSpec.Core.Ulp.succ_le_plus_ulp

#print axioms Ulp_succ_le_plus_ulp_unrestricted

/-- Expected source boundary: no exponent-validity premise. -/
theorem Ulp_pred_lt_le_unrestricted :
    ∀ (beta : ℤ) [ValidRadix beta] (fexp : ℤ → ℤ)
  (x y : ℝ),
  x ≠ 0 → x ≤ y → FloatSpec.Core.Ulp.pred beta fexp x < y := @FloatSpec.Core.Ulp.pred_lt_le

#print axioms Ulp_pred_lt_le_unrestricted

/-- Expected source boundary: no exponent-validity premise. -/
theorem Ulp_succ_gt_ge_unrestricted :
    ∀ (beta : ℤ) [ValidRadix beta] (fexp : ℤ → ℤ)
  (x y : ℝ),
  y ≠ 0 → x ≤ y → x < FloatSpec.Core.Ulp.succ beta fexp y := @FloatSpec.Core.Ulp.succ_gt_ge

#print axioms Ulp_succ_gt_ge_unrestricted

/-- Expected source boundary: no exponent-validity premise. -/
theorem Ulp_pred_pos_plus_ulp_aux1_unrestricted :
    ∀ (beta : ℤ) [ValidRadix beta] (fexp : ℤ → ℤ)
  (x : ℝ),
  0 < x →
    FloatSpec.Core.Generic_fmt.generic_format beta fexp x →
      x ≠ ↑beta ^ (FloatSpec.Core.Raux.mag beta x - 1) →
          x - FloatSpec.Core.Ulp.ulp beta fexp x +
              FloatSpec.Core.Ulp.ulp beta fexp (x - FloatSpec.Core.Ulp.ulp beta fexp x) = x := @FloatSpec.Core.Ulp.pred_pos_plus_ulp_aux1

#print axioms Ulp_pred_pos_plus_ulp_aux1_unrestricted

/-- Expected source boundary: no exponent-validity premise. -/
theorem Ulp_id_p_ulp_le_bpow_unrestricted :
    ∀ (beta : ℤ) [ValidRadix beta] (fexp : ℤ → ℤ)
  (x : ℝ) (e : ℤ),
  0 < x →
    FloatSpec.Core.Generic_fmt.generic_format beta fexp x →
      x < ↑beta ^ e →
        x + FloatSpec.Core.Ulp.ulp beta fexp x ≤ ↑beta ^ e := @FloatSpec.Core.Ulp.id_p_ulp_le_bpow

#print axioms Ulp_id_p_ulp_le_bpow_unrestricted

/-- Expected source boundary: no exponent-validity premise. -/
theorem Ulp_ulp_succ_pos_unrestricted :
    ∀ (beta : ℤ) [ValidRadix beta] (fexp : ℤ → ℤ)
  (x : ℝ),
  FloatSpec.Core.Generic_fmt.generic_format beta fexp x →
    0 < x →
        FloatSpec.Core.Ulp.ulp beta fexp (FloatSpec.Core.Ulp.succ beta fexp x) =
            FloatSpec.Core.Ulp.ulp beta fexp x ∨
          FloatSpec.Core.Ulp.succ beta fexp x = ↑beta ^ FloatSpec.Core.Raux.mag beta x := @FloatSpec.Core.Ulp.ulp_succ_pos

#print axioms Ulp_ulp_succ_pos_unrestricted

/-- Expected source boundary: no exponent-validity premise. -/
theorem Ulp_not_FTZ_generic_format_ulp_unrestricted :
    ∀ (beta : ℤ) [ValidRadix beta] (fexp : ℤ → ℤ)
  ,
  (∀ (x : ℝ), FloatSpec.Core.Generic_fmt.generic_format beta fexp (FloatSpec.Core.Ulp.ulp beta fexp x)) →
    1 < beta → FloatSpec.Core.Ulp.Exp_not_FTZ fexp := @FloatSpec.Core.Ulp.not_FTZ_generic_format_ulp

#print axioms Ulp_not_FTZ_generic_format_ulp_unrestricted

/-- Expected source boundary: no exponent-validity premise. -/
theorem Ulp_id_m_ulp_ge_bpow_unrestricted :
    ∀ (beta : ℤ) [ValidRadix beta] (fexp : ℤ → ℤ)
  (x : ℝ) (e : ℤ),
  FloatSpec.Core.Generic_fmt.generic_format beta fexp x →
    x ≠ FloatSpec.Core.Ulp.ulp beta fexp x →
      ↑beta ^ e < x →
        1 < beta → ↑beta ^ e ≤ x - FloatSpec.Core.Ulp.ulp beta fexp x := @FloatSpec.Core.Ulp.id_m_ulp_ge_bpow

#print axioms Ulp_id_m_ulp_ge_bpow_unrestricted

/-- Expected source boundary: no exponent-validity premise. -/
theorem Ulp_round_UP_DN_ulp_unrestricted :
    ∀ (beta : ℤ) [ValidRadix beta] (fexp : ℤ → ℤ)
  (x : ℝ),
  ¬FloatSpec.Core.Generic_fmt.generic_format beta fexp x →
    FloatSpec.Core.Generic_fmt.roundR beta fexp FloatSpec.Core.Generic_fmt.rnd_ceil x =
      FloatSpec.Core.Generic_fmt.roundR beta fexp FloatSpec.Core.Generic_fmt.rnd_floor x +
        FloatSpec.Core.Ulp.ulp beta fexp x := @FloatSpec.Core.Ulp.round_UP_DN_ulp

#print axioms Ulp_round_UP_DN_ulp_unrestricted

/-- Expected source boundary: no exponent-validity premise. -/
theorem Generic_fmt_generic_format_ge_bpow_unrestricted :
    ∀ (beta : ℤ) [ValidRadix beta] (fexp : ℤ → ℤ)
  (emin : ℤ),
  (1 < beta ∧ ∀ (e : ℤ), emin ≤ fexp e) →
    ∀ (x : ℝ), 0 < x → FloatSpec.Core.Generic_fmt.generic_format beta fexp x → ↑beta ^ emin ≤ x := @FloatSpec.Core.Generic_fmt.generic_format_ge_bpow

#print axioms Generic_fmt_generic_format_ge_bpow_unrestricted

/-- Expected source boundary: no exponent-validity premise. -/
theorem Generic_fmt_round_N_middle_unrestricted :
    ∀ (beta : ℤ) [ValidRadix beta] (fexp : ℤ → ℤ)
  (choice : ℤ → Bool) (x : ℝ),
  1 < beta →
    x - FloatSpec.Core.Generic_fmt.roundR beta fexp (fun y => FloatSpec.Core.Raux.Zfloor y) x =
        FloatSpec.Core.Generic_fmt.roundR beta fexp (fun y => FloatSpec.Core.Raux.Zceil y) x - x →
      FloatSpec.Core.Generic_fmt.roundR beta fexp (FloatSpec.Core.Generic_fmt.Znearest choice) x =
        if choice (FloatSpec.Core.Raux.Zfloor (FloatSpec.Core.Generic_fmt.scaled_mantissa beta fexp x)) = true then
          FloatSpec.Core.Generic_fmt.roundR beta fexp (fun y => FloatSpec.Core.Raux.Zceil y) x
        else FloatSpec.Core.Generic_fmt.roundR beta fexp (fun y => FloatSpec.Core.Raux.Zfloor y) x := @FloatSpec.Core.Generic_fmt.round_N_middle

#print axioms Generic_fmt_round_N_middle_unrestricted

/-- Expected source boundary: no exponent-validity premise. -/
theorem Generic_fmt_round_N_small_pos_unrestricted :
    ∀ (beta : ℤ) [ValidRadix beta] (fexp : ℤ → ℤ)
  (choice : ℤ → Bool) (x : ℝ) (ex : ℤ),
  1 < beta →
    ↑beta ^ (ex - 1) ≤ x ∧ x < ↑beta ^ ex →
      fexp ex > ex → FloatSpec.Core.Generic_fmt.roundR beta fexp (FloatSpec.Core.Generic_fmt.Znearest choice) x = 0 := @FloatSpec.Core.Generic_fmt.round_N_small_pos

#print axioms Generic_fmt_round_N_small_pos_unrestricted

/-- Expected source boundary: no exponent-validity premise. -/
theorem Generic_fmt_round_N_opp_unrestricted :
    ∀ (beta : ℤ) [ValidRadix beta] (fexp : ℤ → ℤ)
  (choice : ℤ → Bool) (x : ℝ),
  FloatSpec.Core.Generic_fmt.roundR beta fexp (FloatSpec.Core.Generic_fmt.Znearest choice) (-x) =
    -FloatSpec.Core.Generic_fmt.roundR beta fexp (FloatSpec.Core.Generic_fmt.Znearest fun t => !choice (-(t + 1))) x := @FloatSpec.Core.Generic_fmt.round_N_opp

#print axioms Generic_fmt_round_N_opp_unrestricted

/-- Expected source boundary: no exponent-validity premise. -/
theorem Generic_fmt_round_N0_opp_unrestricted :
    ∀ (beta : ℤ) [ValidRadix beta] (fexp : ℤ → ℤ)
  (x : ℝ),
  FloatSpec.Core.Generic_fmt.roundR beta fexp (FloatSpec.Core.Generic_fmt.Znearest fun t => decide (t < 0)) (-x) =
    -FloatSpec.Core.Generic_fmt.roundR beta fexp (FloatSpec.Core.Generic_fmt.Znearest fun t => decide (t < 0)) x := @FloatSpec.Core.Generic_fmt.round_N0_opp

#print axioms Generic_fmt_round_N0_opp_unrestricted

/-- Expected source boundary: no exponent-validity premise. -/
theorem Generic_fmt_round_N_small_unrestricted :
    ∀ (beta : ℤ) [ValidRadix beta] (fexp : ℤ → ℤ)
  (choice : ℤ → Bool) (x : ℝ) (ex : ℤ),
  1 < beta →
    ↑beta ^ (ex - 1) ≤ |x| ∧ |x| < ↑beta ^ ex →
      fexp ex > ex → FloatSpec.Core.Generic_fmt.roundR beta fexp (FloatSpec.Core.Generic_fmt.Znearest choice) x = 0 := @FloatSpec.Core.Generic_fmt.round_N_small

#print axioms Generic_fmt_round_N_small_unrestricted

/-- Expected source boundary: no exponent-validity premise. -/
theorem Generic_fmt_round_NA_opp_unrestricted :
    ∀ (beta : ℤ) [ValidRadix beta] (fexp : ℤ → ℤ)
  (x : ℝ),
  FloatSpec.Core.Generic_fmt.roundR beta fexp (FloatSpec.Core.Generic_fmt.Znearest fun t => decide (0 ≤ t)) (-x) =
    -FloatSpec.Core.Generic_fmt.roundR beta fexp (FloatSpec.Core.Generic_fmt.Znearest fun t => decide (0 ≤ t)) x := @FloatSpec.Core.Generic_fmt.round_NA_opp

#print axioms Generic_fmt_round_NA_opp_unrestricted

/-- Expected source boundary: no exponent-validity premise. -/
theorem Generic_fmt_scaled_mantissa_generic_unrestricted :
    ∀ (beta : ℤ) [ValidRadix beta] (fexp : ℤ → ℤ)
  (x : ℝ),
  FloatSpec.Core.Generic_fmt.generic_format beta fexp x →
    FloatSpec.Core.Generic_fmt.scaled_mantissa beta fexp x =
      ↑(FloatSpec.Core.Raux.Ztrunc (FloatSpec.Core.Generic_fmt.scaled_mantissa beta fexp x)) := @FloatSpec.Core.Generic_fmt.scaled_mantissa_generic

#print axioms Generic_fmt_scaled_mantissa_generic_unrestricted

/-- Expected source boundary: no exponent-validity premise. -/
theorem Generic_fmt_round_DN_or_UP_unrestricted :
    ∀ (beta : ℤ) [ValidRadix beta] (fexp : ℤ → ℤ)
  (rnd : ℝ → ℤ) [FloatSpec.Core.Generic_fmt.Valid_rnd rnd] (x : ℝ),
  FloatSpec.Core.Generic_fmt.roundR beta fexp rnd x =
      FloatSpec.Core.Generic_fmt.roundR beta fexp FloatSpec.Core.Generic_fmt.rnd_floor x ∨
    FloatSpec.Core.Generic_fmt.roundR beta fexp rnd x =
      FloatSpec.Core.Generic_fmt.roundR beta fexp FloatSpec.Core.Generic_fmt.rnd_ceil x := @FloatSpec.Core.Generic_fmt.round_DN_or_UP

#print axioms Generic_fmt_round_DN_or_UP_unrestricted

/-- Expected source boundary: no exponent-validity premise. -/
theorem Generic_fmt_round_ZR_or_AW_unrestricted :
    ∀ (beta : ℤ) [ValidRadix beta] (fexp : ℤ → ℤ)
  (rnd : ℝ → ℤ) [FloatSpec.Core.Generic_fmt.Valid_rnd rnd] (x : ℝ),
  FloatSpec.Core.Generic_fmt.round_to_generic beta fexp rnd x =
      FloatSpec.Core.Generic_fmt.round_to_generic beta fexp FloatSpec.Core.Raux.Ztrunc x ∨
    FloatSpec.Core.Generic_fmt.round_to_generic beta fexp rnd x =
      FloatSpec.Core.Generic_fmt.round_to_generic beta fexp FloatSpec.Core.Raux.Zaway x := @FloatSpec.Core.Generic_fmt.round_ZR_or_AW

#print axioms Generic_fmt_round_ZR_or_AW_unrestricted

/-- Expected source boundary: no exponent-validity premise. -/
theorem Generic_fmt_round_bounded_small_pos_unrestricted :
    ∀ (beta : ℤ) [ValidRadix beta] (fexp : ℤ → ℤ)
  (rnd : ℝ → ℤ) [FloatSpec.Core.Generic_fmt.Valid_rnd rnd] {x : ℝ} {ex : ℤ},
  ex ≤ fexp ex →
    ↑beta ^ (ex - 1) ≤ x ∧ x < ↑beta ^ ex →
      FloatSpec.Core.Generic_fmt.round_to_generic beta fexp rnd x = 0 ∨
        FloatSpec.Core.Generic_fmt.round_to_generic beta fexp rnd x = ↑beta ^ fexp ex := @FloatSpec.Core.Generic_fmt.round_bounded_small_pos

#print axioms Generic_fmt_round_bounded_small_pos_unrestricted

/-- Expected source boundary: no exponent-validity premise. -/
theorem Generic_fmt_round_bounded_large_pos_unrestricted :
    ∀ (beta : ℤ) [ValidRadix beta] (fexp : ℤ → ℤ)
  (rnd : ℝ → ℤ) [FloatSpec.Core.Generic_fmt.Valid_rnd rnd] {x : ℝ} {ex : ℤ},
  fexp ex < ex →
    ↑beta ^ (ex - 1) ≤ x ∧ x < ↑beta ^ ex →
      ↑beta ^ (ex - 1) ≤ FloatSpec.Core.Generic_fmt.round_to_generic beta fexp rnd x ∧
        FloatSpec.Core.Generic_fmt.round_to_generic beta fexp rnd x ≤ ↑beta ^ ex := @FloatSpec.Core.Generic_fmt.round_bounded_large_pos

#print axioms Generic_fmt_round_bounded_large_pos_unrestricted

/-- Expected source boundary: no exponent-validity premise. -/
theorem Generic_fmt_round_DN_small_pos_unrestricted :
    ∀ (beta : ℤ) [ValidRadix beta] (fexp : ℤ → ℤ)
  (x : ℝ) (ex : ℤ),
  ↑beta ^ (ex - 1) ≤ x ∧ x < ↑beta ^ ex →
    ex ≤ fexp ex → 1 < beta → FloatSpec.Core.Generic_fmt.roundR beta fexp FloatSpec.Core.Generic_fmt.rnd_floor x = 0 := @FloatSpec.Core.Generic_fmt.round_DN_small_pos

#print axioms Generic_fmt_round_DN_small_pos_unrestricted

/-- Expected source boundary: no exponent-validity premise. -/
theorem Generic_fmt_round_UP_small_pos_unrestricted :
    ∀ (beta : ℤ) [ValidRadix beta] (fexp : ℤ → ℤ)
  (x : ℝ) (ex : ℤ),
  ↑beta ^ (ex - 1) ≤ x ∧ x < ↑beta ^ ex → ex ≤ fexp ex →
    FloatSpec.Core.Generic_fmt.round_to_generic beta fexp FloatSpec.Core.Generic_fmt.rnd_ceil x =
      ↑beta ^ fexp ex := @FloatSpec.Core.Generic_fmt.round_UP_small_pos

#print axioms Generic_fmt_round_UP_small_pos_unrestricted

/-- Expected source boundary: no exponent-validity premise. -/
theorem Generic_fmt_round_large_pos_ge_bpow_unrestricted :
    ∀ (beta : ℤ) [ValidRadix beta] (fexp : ℤ → ℤ)
  (rnd : ℝ → ℤ) [FloatSpec.Core.Generic_fmt.Valid_rnd rnd] {x : ℝ} {e : ℤ},
  0 < FloatSpec.Core.Generic_fmt.round_to_generic beta fexp rnd x →
    ↑beta ^ e ≤ x → ↑beta ^ e ≤ FloatSpec.Core.Generic_fmt.round_to_generic beta fexp rnd x := @FloatSpec.Core.Generic_fmt.round_large_pos_ge_bpow

#print axioms Generic_fmt_round_large_pos_ge_bpow_unrestricted

/-- Expected source boundary: no exponent-validity premise. -/
theorem Generic_fmt_exp_small_round_0_pos_unrestricted :
    ∀ (beta : ℤ) [ValidRadix beta] (fexp : ℤ → ℤ)
  (rnd : ℝ → ℤ) [FloatSpec.Core.Generic_fmt.Valid_rnd rnd] {x : ℝ} {ex : ℤ},
  ↑beta ^ (ex - 1) ≤ x ∧ x < ↑beta ^ ex → FloatSpec.Core.Generic_fmt.round_to_generic beta fexp rnd x = 0 → ex ≤ fexp ex := @FloatSpec.Core.Generic_fmt.exp_small_round_0_pos

#print axioms Generic_fmt_exp_small_round_0_pos_unrestricted

end FloatSpec.Test.CorePremiseBoundary
