import Lean
import FloatSpec.src.Prop.Div_sqrt_error
import FloatSpec.src.Prop.Round_odd
import FloatSpec.src.IEEE754.BinarySingleNaNSourceFacade

open Lean Meta Elab Command

/-- Reject a direct predicate premise on the named parameter of an elaborated
declaration. This detects accidental section-instance leakage; it is not a
translator or a proof that the entire statement matches Rocq. -/
elab "#guard_no_source_premise " target:ident cls:ident " at " parameter:ident : command =>
  liftTermElabM do
    let targetName ← realizeGlobalConstNoOverloadWithInfo target
    let className ← realizeGlobalConstNoOverloadWithInfo cls
    let info ← getConstInfo targetName
    forallTelescope info.type fun binders _ => do
      let some param ← binders.findM? fun binder => do
        return (← binder.fvarId!.getDecl).userName == parameter.getId
        | throwErrorAt parameter "unknown parameter {parameter.getId} on {target.getId}"
      let expected ← mkAppM className #[param]
      unless ← isProp expected do
        throwErrorAt cls "{cls.getId} does not produce a proposition"
      for binder in binders do
        let domain ← withTransparency .all <| whnf (← inferType binder)
        if ← withTransparency .all <| isDefEq domain expected then
          throwErrorAt target "unexpected premise {cls.getId} on parameter {parameter.getId} of {target.getId}"

namespace FloatSpec.Test.SourcePremiseGuard

theorem instanceLeak (fexp : Int → Int) [FloatSpec.Core.Generic_fmt.Valid_exp fexp] :
    fexp 0 = fexp 0 := rfl
theorem explicitLeak (fexp : Int → Int) (_h : FloatSpec.Core.Generic_fmt.Valid_exp fexp) :
    fexp 0 = fexp 0 := rfl
abbrev Alias (fexp : Int → Int) := FloatSpec.Core.Generic_fmt.Valid_exp fexp
theorem aliasLeak (fexp : Int → Int) (_h : Alias fexp) : fexp 0 = fexp 0 := rfl
theorem selective (fexp fexpe : Int → Int) [FloatSpec.Core.Generic_fmt.Valid_exp fexp] : fexpe 0 = fexpe 0 := rfl

/-- error: unexpected premise FloatSpec.Core.Generic_fmt.Valid_exp on parameter fexp of instanceLeak -/
#guard_msgs in
#guard_no_source_premise instanceLeak FloatSpec.Core.Generic_fmt.Valid_exp at fexp

/-- error: unexpected premise FloatSpec.Core.Generic_fmt.Valid_exp on parameter fexp of explicitLeak -/
#guard_msgs in
#guard_no_source_premise explicitLeak FloatSpec.Core.Generic_fmt.Valid_exp at fexp

/-- error: unexpected premise FloatSpec.Core.Generic_fmt.Valid_exp on parameter fexp of aliasLeak -/
#guard_msgs in
#guard_no_source_premise aliasLeak FloatSpec.Core.Generic_fmt.Valid_exp at fexp

/-- error: unknown parameter typo on selective -/
#guard_msgs in
#guard_no_source_premise selective FloatSpec.Core.Generic_fmt.Valid_exp at typo

#guard_no_source_premise selective FloatSpec.Core.Generic_fmt.Valid_exp at fexpe

end FloatSpec.Test.SourcePremiseGuard

-- Compiled-type checks for the manually source-compared premise boundary.
#guard_no_source_premise round_repr_same_exp FloatSpec.Core.Generic_fmt.Valid_exp at fexp
#guard_no_source_premise generic_format_plus_prec Prec_gt_0 at prec
#guard_no_source_premise sqrt_error_N_FLX_aux1 Prec_gt_0 at prec
#guard_no_source_premise mult_bpow_exact_FLX Prec_gt_0 at prec
#guard_no_source_premise mult_bpow_exact_FLT Prec_gt_0 at prec
#guard_no_source_premise mult_bpow_pos_exact_FLT Prec_gt_0 at prec
#guard_no_source_premise round_plus_neq_0_aux FloatSpec.Core.Generic_fmt.Monotone_exp at fexp
#guard_no_source_premise round_plus_neq_0 FloatSpec.Core.Generic_fmt.Monotone_exp at fexp
#guard_no_source_premise round_plus_eq_0 FloatSpec.Core.Generic_fmt.Monotone_exp at fexp
#guard_no_source_premise plus_error_le_l FloatSpec.Core.Generic_fmt.Monotone_exp at fexp
#guard_no_source_premise plus_error_le_r FloatSpec.Core.Generic_fmt.Monotone_exp at fexp
#guard_no_source_premise ex_shift FloatSpec.Core.Generic_fmt.Valid_exp at fexp
#guard_no_source_premise relative_error_lt_conversion FloatSpec.Core.Generic_fmt.Valid_exp at fexp
#guard_no_source_premise relative_error_le_conversion FloatSpec.Core.Generic_fmt.Valid_exp at fexp
#guard_no_source_premise relative_error_le_conversion_inv FloatSpec.Core.Generic_fmt.Valid_exp at fexp
#guard_no_source_premise relative_error_le_conversion_round_inv FloatSpec.Core.Generic_fmt.Valid_exp at fexp
#guard_no_source_premise Rnd_odd_pt_opp_inv FloatSpec.Core.Generic_fmt.Valid_exp at fexp
#guard_no_source_premise generic_format_fexpe_fexp FloatSpec.Core.Generic_fmt.Valid_exp at fexp
#guard_no_source_premise d_le_m FloatSpec.Core.Generic_fmt.Valid_exp at fexp
#guard_no_source_premise m_le_u FloatSpec.Core.Generic_fmt.Valid_exp at fexp
#guard_no_source_premise m_eq_0 FloatSpec.Core.Generic_fmt.Valid_exp at fexp
#guard_no_source_premise ex_shift FloatSpec.Core.Generic_fmt.Monotone_exp at fexp
#guard_no_source_premise ex_shift FloatSpec.Core.Ulp.Exp_not_FTZ at fexp
#guard_no_source_premise round_plus_F2R FloatSpec.Core.Ulp.Exp_not_FTZ at fexp
#guard_no_source_premise round_plus_ge_ulp FloatSpec.Core.Ulp.Exp_not_FTZ at fexp
#guard_no_source_premise plus_error_le_l FloatSpec.Core.Ulp.Exp_not_FTZ at fexp
#guard_no_source_premise plus_error_le_r FloatSpec.Core.Ulp.Exp_not_FTZ at fexp
#guard_no_source_premise u_ro_pos Prec_gt_0 at prec
#guard_no_source_premise generic_format_fexpe_fexp FloatSpec.Core.Generic_fmt.Valid_exp at fexpe
#guard_no_source_premise Fm FloatSpec.Core.Generic_fmt.Valid_exp at fexpe
#guard_no_source_premise Zm FloatSpec.Core.Generic_fmt.Valid_exp at fexpe

-- Pinned Binary exports require prec < emax, not an extra positive-precision premise.
#guard_no_source_premise Binary.Bnearbyint Prec_gt_0 at prec
#guard_no_source_premise Binary.Bnearbyint_correct Prec_gt_0 at prec
#guard_no_source_premise Binary.Btrunc Prec_gt_0 at prec
#guard_no_source_premise Binary.Btrunc_correct Prec_gt_0 at prec
#guard_no_source_premise BinarySingleNaN.Btrunc Prec_gt_0 at prec
#guard_no_source_premise BinarySingleNaN.Btrunc_correct Prec_gt_0 at prec

-- Magnitude comparisons need monotonicity, not validity as a rounding format.
#guard_no_source_premise FloatSpec.Core.Generic_fmt.lt_cexp_pos FloatSpec.Core.Generic_fmt.Valid_exp at fexp
#guard_no_source_premise FloatSpec.Core.Generic_fmt.lt_cexp FloatSpec.Core.Generic_fmt.Valid_exp at fexp
#guard_no_source_premise FloatSpec.Core.Generic_fmt.cexp_le_bpow FloatSpec.Core.Generic_fmt.Valid_exp at fexp
#guard_no_source_premise FloatSpec.Core.Generic_fmt.cexp_ge_bpow FloatSpec.Core.Generic_fmt.Valid_exp at fexp

#guard_no_source_premise Binary.Bcompare Prec_gt_0 at prec
#guard_no_source_premise Binary.Bcompare_correct Prec_gt_0 at prec
#guard_no_source_premise BinarySingleNaN.Bcompare Prec_gt_0 at prec
#guard_no_source_premise BinarySingleNaN.Bcompare_correct Prec_gt_0 at prec

/-! Typed consumers deliberately omit proof-only section assumptions.
Unlike a bare `#check`, each example fails if a public theorem accidentally
inherits a stronger premise than its pinned Rocq counterpart. -/

namespace SourcePremiseContracts

variable (beta : Int) [ValidRadix beta] (hβ : 1 < beta)

example (fexp : Int → Int) [FloatSpec.Core.Generic_fmt.Monotone_exp fexp]
    (x y : ℝ) (hy : 0 < y)
    (h : FloatSpec.Core.Generic_fmt.cexp beta fexp x <
      FloatSpec.Core.Generic_fmt.cexp beta fexp y) : x < y :=
  FloatSpec.Core.Generic_fmt.lt_cexp_pos beta fexp x y hβ hy h

example (fexp : Int → Int) [FloatSpec.Core.Generic_fmt.Monotone_exp fexp]
    (x y : ℝ) (hy : y ≠ 0)
    (h : FloatSpec.Core.Generic_fmt.cexp beta fexp x <
      FloatSpec.Core.Generic_fmt.cexp beta fexp y) : |x| < |y| :=
  FloatSpec.Core.Generic_fmt.lt_cexp beta fexp x y hβ hy h

example (fexp : Int → Int) [FloatSpec.Core.Generic_fmt.Monotone_exp fexp]
    (x : ℝ) (e : Int) (hx : x ≠ 0) (h : |x| < (beta : ℝ) ^ e) :
    FloatSpec.Core.Generic_fmt.cexp beta fexp x ≤ fexp e :=
  FloatSpec.Core.Generic_fmt.cexp_le_bpow beta fexp x e hβ hx h

example (fexp : Int → Int) [FloatSpec.Core.Generic_fmt.Monotone_exp fexp]
    (x : ℝ) (e : Int) (h : (beta : ℝ) ^ (e - 1) ≤ |x|) :
    fexp e ≤ FloatSpec.Core.Generic_fmt.cexp beta fexp x :=
  FloatSpec.Core.Generic_fmt.cexp_ge_bpow beta fexp x e hβ h

example (fexp : Int → Int) (rnd : ℝ → Int)
    [FloatSpec.Core.Generic_fmt.Valid_rnd rnd] (m e : Int) :
    ∃ m', FloatSpec.Core.Generic_fmt.roundR beta fexp rnd
        (_root_.F2R (FloatSpec.Core.Defs.FlocqFloat.mk m e :
          FloatSpec.Core.Defs.FlocqFloat beta)) =
      _root_.F2R (FloatSpec.Core.Defs.FlocqFloat.mk m' e :
        FloatSpec.Core.Defs.FlocqFloat beta) :=
  round_repr_same_exp beta fexp rnd hβ m e

example (prec : Int) (fexp : Int → Int) (hbound : ∀ e, fexp e ≤ e - prec)
    (x y : ℝ) (fx fy : FloatSpec.Core.Defs.FlocqFloat beta)
    (hx : x = _root_.F2R fx) (hy : y = _root_.F2R fy)
    (hleft : |x + y| < FloatSpec.Core.Raux.bpow beta (prec + fx.Fexp))
    (hright : |x + y| < FloatSpec.Core.Raux.bpow beta (prec + fy.Fexp)) :
    generic_format beta fexp (x + y) :=
  generic_format_plus_prec beta prec fexp hbound hβ x y fx fy hx hy hleft hright

example (prec : Int) (x : ℝ) (e : Int)
    (hx : generic_format beta (FLX_exp prec) x) :
    generic_format beta (FLX_exp prec) (x * FloatSpec.Core.Raux.bpow beta e) :=
  mult_bpow_exact_FLX beta prec x e hβ hx

example (prec emin : Int) (x : ℝ) (e : Int)
    (hx : generic_format beta (FLT_exp emin prec) x)
    (hbound : emin + prec - mag beta x ≤ e) :
    generic_format beta (FLT_exp emin prec) (x * FloatSpec.Core.Raux.bpow beta e) :=
  mult_bpow_exact_FLT beta prec emin x e hβ hx hbound

example (prec emin : Int) (x : ℝ) (e : Int)
    (hx : generic_format beta (FLT_exp emin prec) x) (he : 0 ≤ e) :
    generic_format beta (FLT_exp emin prec) (x * FloatSpec.Core.Raux.bpow beta e) :=
  mult_bpow_pos_exact_FLT beta prec emin x e hβ hx he

example (prec : Int) (x : ℝ)
    (hx : generic_format beta (FLX_exp prec) x) (hpos : 0 < x) :
    ∃ (mu : ℝ) (e : Int), generic_format beta (FLX_exp prec) mu ∧
      x = mu * (beta : ℝ) ^ (2 * e) ∧ 1 ≤ mu ∧ mu < (beta : ℝ) ^ (2 : Int) :=
  sqrt_error_N_FLX_aux1 beta prec x hβ hx hpos

end SourcePremiseContracts

namespace IntegerSourcePremiseContracts

example (prec emax : Int) (x : binary_float prec emax) : Int := Binary.Btrunc x
example (prec emax : Int) (x : BinarySingleNaN.binary_float prec emax) : Int :=
  BinarySingleNaN.Btrunc x

example (prec emax : Int) [Prec_lt_emax prec emax]
    (nan : Binary.BnearbyintNaNHandler prec emax) (mode : RoundingMode)
    (x : binary_float prec emax) :
    Binary.is_finite (Binary.Bnearbyint nan mode x) = Binary.is_finite x :=
  (Binary.Bnearbyint_correct nan mode x).2.1

example (prec emax : Int) [Prec_lt_emax prec emax] (x : binary_float prec emax) :
    (Binary.Btrunc x : ℝ) = FloatSpec.Core.Generic_fmt.round_to_generic 2
      (FloatSpec.Core.FIX.FIX_exp 0) FloatSpec.Core.Raux.Ztrunc (Binary.B2R x) :=
  Binary.Btrunc_correct x

example (prec emax : Int) [Prec_lt_emax prec emax]
    (x : BinarySingleNaN.binary_float prec emax) :
    (BinarySingleNaN.Btrunc x : ℝ) = FloatSpec.Core.Generic_fmt.round_to_generic 2
      (FloatSpec.Core.FIX.FIX_exp 0) FloatSpec.Core.Raux.Ztrunc (BinarySingleNaN.B2R x) :=
  BinarySingleNaN.Btrunc_correct x

private instance : Prec_lt_emax (0 : Int) (1 : Int) := ⟨by decide⟩

example : BinarySingleNaN.Bnearbyint (prec := 0) (emax := 1) .RNE (.B754_zero true) =
    .B754_zero true := rfl

end IntegerSourcePremiseContracts

namespace CanonicalExponentPremiseControls

private def badExponent (e : Int) : Int := e + 1

private instance : FloatSpec.Core.Generic_fmt.Monotone_exp badExponent :=
  ⟨by intro x y h; dsimp [badExponent]; grind⟩

example : ¬FloatSpec.Core.Generic_fmt.Valid_exp badExponent := by
  intro h
  have impossible := (h.valid_exp 0).2 (by decide)
  norm_num [badExponent] at impossible

example (x y : ℝ) (hy : 0 < y)
    (h : FloatSpec.Core.Generic_fmt.cexp 2 badExponent x <
      FloatSpec.Core.Generic_fmt.cexp 2 badExponent y) : x < y :=
  FloatSpec.Core.Generic_fmt.lt_cexp_pos 2 badExponent x y (by decide) hy h

end CanonicalExponentPremiseControls

-- Both source comparisons work without any precision/exponent instances.
example (prec emax : Int) (x y : binary_float prec emax) : Option Ordering :=
  Binary.Bcompare x y
example (prec emax : Int) (x y : BinarySingleNaN.binary_float prec emax) : Option Ordering :=
  BinarySingleNaN.Bcompare x y
example (prec emax : Int) (x y : binary_float prec emax)
    (hx : Binary.is_finite x = true) (hy : Binary.is_finite y = true) :
    Binary.Bcompare x y = some (BinarySingleNaN.RcompareOrdering (Binary.B2R x) (Binary.B2R y)) :=
  Binary.Bcompare_correct x y hx hy
example (prec emax : Int) (x y : BinarySingleNaN.binary_float prec emax)
    (hx : BinarySingleNaN.is_finite x = true) (hy : BinarySingleNaN.is_finite y = true) :
    BinarySingleNaN.Bcompare x y =
      some (BinarySingleNaN.RcompareOrdering (BinarySingleNaN.B2R x) (BinarySingleNaN.B2R y)) :=
  BinarySingleNaN.Bcompare_correct x y hx hy

-- Source theorem names must denote propositions, not numeric doc-link wrappers.
-- Raux still uses an explicitly documented integer comparison encoding.
example (x y : ℝ) (h : x < y) : FloatSpec.Core.Raux.Rcompare x y = -1 :=
  FloatSpec.Core.Raux.Rcompare_Lt x y h
example (x y : ℝ) (h : x = y) : FloatSpec.Core.Raux.Rcompare x y = 0 :=
  FloatSpec.Core.Raux.Rcompare_Eq x y h
example (x y : ℝ) (h : y < x) : FloatSpec.Core.Raux.Rcompare x y = 1 :=
  FloatSpec.Core.Raux.Rcompare_Gt x y h
example (x y : ℝ) (h : y ≤ x) : FloatSpec.Core.Raux.Rcompare x y ≠ -1 :=
  FloatSpec.Core.Raux.Rcompare_not_Lt x y h
example (x y : ℝ) (h : x ≤ y) : FloatSpec.Core.Raux.Rcompare x y ≠ 1 :=
  FloatSpec.Core.Raux.Rcompare_not_Gt x y h

example (left right : Int) :
    FloatSpec.Core.Raux.Rcompare (left : ℝ) (right : ℝ) =
      FloatSpec.Core.Raux.Zcompare_int left right :=
  FloatSpec.Core.Raux.Rcompare_IZR left right
