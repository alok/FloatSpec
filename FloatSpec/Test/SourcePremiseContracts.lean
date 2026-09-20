import Lean
import FloatSpec.src.Calc.Div
import FloatSpec.src.Calc.Sqrt
import FloatSpec.src.Core.FTZ
import FloatSpec.src.Prop.Div_sqrt_error
import FloatSpec.src.Prop.Round_odd
import FloatSpec.src.IEEE754.BinarySingleNaNSourceFacade
import FloatSpec.src.Pff.Pff2Flocq

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

/-- Name the proposition used by legacy precision section instances. -/
abbrev PositivePrecisionFact (prec : Int) : Prop := Fact (0 < prec)
theorem factLeak (prec : Int) [Fact (0 < prec)] : prec = prec := rfl

/-- error: unexpected premise PositivePrecisionFact on parameter prec of factLeak -/
#guard_msgs in
#guard_no_source_premise factLeak PositivePrecisionFact at prec

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

-- Injectivity comes from constructor validity and canonical representation,
-- not positivity or a precision/exponent separation assumption.
#guard_no_source_premise canonical_canonical_mantissa_compat Prec_gt_0 at prec
#guard_no_source_premise _root_.B2R_inj Prec_gt_0 at prec
#guard_no_source_premise Binary.canonical_canonical_mantissa Prec_gt_0 at prec
#guard_no_source_premise Binary.B2R_inj Prec_gt_0 at prec
#guard_no_source_premise Binary.B2R_Bsign_inj Prec_gt_0 at prec
#guard_no_source_premise Binary.binary_round_aux Prec_gt_0 at prec
#guard_no_source_premise Binary.binary_round Prec_gt_0 at prec

-- Raw rounding and structural laws do not require a valid exponent function.
#guard_no_source_premise FloatSpec.Core.Generic_fmt.roundR_opp FloatSpec.Core.Generic_fmt.Valid_exp at fexp
#guard_no_source_premise FloatSpec.Core.Generic_fmt.round_to_generic FloatSpec.Core.Generic_fmt.Valid_exp at fexp
#guard_no_source_premise FloatSpec.Core.Generic_fmt.round_to_generic_int_eq_roundR FloatSpec.Core.Generic_fmt.Valid_exp at fexp
#guard_no_source_premise FloatSpec.Core.Generic_fmt.round_to_generic_spec FloatSpec.Core.Generic_fmt.Valid_exp at fexp
#guard_no_source_premise FloatSpec.Core.Generic_fmt.round_generic FloatSpec.Core.Generic_fmt.Valid_exp at fexp
#guard_no_source_premise FloatSpec.Core.Generic_fmt.round_generic_identity FloatSpec.Core.Generic_fmt.Valid_exp at fexp
#guard_no_source_premise FloatSpec.Core.Generic_fmt.round_ext FloatSpec.Core.Generic_fmt.Valid_exp at fexp
#guard_no_source_premise FloatSpec.Core.Generic_fmt.round_opp FloatSpec.Core.Generic_fmt.Valid_exp at fexp
#guard_no_source_premise FloatSpec.Core.Generic_fmt.round_0 FloatSpec.Core.Generic_fmt.Valid_exp at fexp
#guard_no_source_premise FloatSpec.Core.Generic_fmt.round_DN_opp FloatSpec.Core.Generic_fmt.Valid_exp at fexp
#guard_no_source_premise FloatSpec.Core.Generic_fmt.round_UP_opp FloatSpec.Core.Generic_fmt.Valid_exp at fexp
#guard_no_source_premise FloatSpec.Core.Generic_fmt.round_ZR_opp FloatSpec.Core.Generic_fmt.Valid_exp at fexp
#guard_no_source_premise FloatSpec.Core.Generic_fmt.round_AW_opp FloatSpec.Core.Generic_fmt.Valid_exp at fexp
#guard_no_source_premise FloatSpec.Core.Generic_fmt.round_ZR_DN FloatSpec.Core.Generic_fmt.Valid_exp at fexp
#guard_no_source_premise FloatSpec.Core.Generic_fmt.round_ZR_UP FloatSpec.Core.Generic_fmt.Valid_exp at fexp
#guard_no_source_premise FloatSpec.Core.Generic_fmt.round_AW_UP FloatSpec.Core.Generic_fmt.Valid_exp at fexp
#guard_no_source_premise FloatSpec.Core.Generic_fmt.round_AW_DN FloatSpec.Core.Generic_fmt.Valid_exp at fexp
#guard_no_source_premise FloatSpec.Calc.Round.round_0 FloatSpec.Core.Generic_fmt.Valid_exp at fexp
#guard_no_source_premise mult_error_FLT_ge_bpow Prec_gt_0 at prec
#guard_no_source_premise mult_error_FLT_ge_bpow' Prec_gt_0 at prec
#guard_no_source_premise FloatSpec.Calc.Sqrt.Fsqrt_correct FloatSpec.Core.Generic_fmt.Valid_exp at fexp
#guard_no_source_premise FloatSpec.Core.FTZ.FLXN_format_FTZ FloatSpec.Test.SourcePremiseGuard.PositivePrecisionFact at prec
#guard_no_source_premise FloatSpec.Core.FTZ.generic_format_FTZ FloatSpec.Test.SourcePremiseGuard.PositivePrecisionFact at prec

/-! Typed consumers deliberately omit proof-only section assumptions.
Unlike a bare `#check`, each example fails if a public theorem accidentally
inherits a stronger premise than its pinned Rocq counterpart. -/

namespace SourcePremiseContracts

example {prec emax : Int} (mode : RoundingMode) (sign : Bool)
    (mantissa exponent : Int) (location : FloatSpec.Calc.Bracket.Location) : full_float :=
  Binary.binary_round_aux (prec := prec) (emax := emax)
    mode sign mantissa exponent location

example {prec emax : Int} (mode : RoundingMode) (sign : Bool)
    (mantissa : FloatSpec.Core.Zaux.Positive) (exponent : Int) : full_float :=
  Binary.binary_round (prec := prec) (emax := emax) mode sign mantissa exponent

example {prec emax : Int} (x y : binary_float prec emax)
    (hx : Binary.is_finite_strict x = true) (hy : Binary.is_finite_strict y = true)
    (hR : Binary.B2R x = Binary.B2R y) : x = y :=
  Binary.B2R_inj x y hx hy hR

example {prec emax : Int} (x y : binary_float prec emax)
    (hx : Binary.is_finite x = true) (hy : Binary.is_finite y = true)
    (hR : Binary.B2R x = Binary.B2R y) (hs : Binary.Bsign x = Binary.Bsign y) : x = y :=
  Binary.B2R_Bsign_inj x y hx hy hR hs

example {prec emax : Int} (sign : Bool) (mantissa : FloatSpec.Core.Zaux.Positive)
    (exponent : Int)
    (hc : canonical_mantissa (prec := prec) (emax := emax)
      (FloatSpec.Core.Zaux.positiveToNat mantissa) exponent = true) :
    FloatSpec.Core.Generic_fmt.canonical 2
      (FloatSpec.Core.FLT.FLT_exp prec (3 - emax - prec))
      (FloatSpec.Core.Defs.FlocqFloat.mk
        (if sign then -(FloatSpec.Core.Zaux.positiveToNat mantissa : Int)
         else (FloatSpec.Core.Zaux.positiveToNat mantissa : Int)) exponent) :=
  Binary.canonical_canonical_mantissa sign mantissa exponent hc

variable (beta : Int) [ValidRadix beta] (hβ : 1 < beta)

example (fexp : Int → Int) (rnd : ℝ → Int) (x : ℝ) :
    FloatSpec.Core.Generic_fmt.round_to_generic beta fexp rnd x =
      FloatSpec.Core.Generic_fmt.roundR beta fexp rnd x := rfl

example (fexp : Int → Int) (rnd : ℝ → Int)
    [FloatSpec.Core.Generic_fmt.Valid_rnd rnd] :
    FloatSpec.Core.Generic_fmt.round_to_generic beta fexp rnd 0 = 0 :=
  FloatSpec.Core.Generic_fmt.round_0 beta fexp rnd

example (fexp : Int → Int) (rnd : ℝ → Int)
    [FloatSpec.Core.Generic_fmt.Valid_rnd rnd] (x : ℝ)
    (hx : FloatSpec.Core.Generic_fmt.generic_format beta fexp x) :
    FloatSpec.Core.Generic_fmt.round_to_generic beta fexp rnd x = x :=
  FloatSpec.Core.Generic_fmt.round_generic beta fexp rnd x hx

example (fexp : Int → Int) (rnd1 rnd2 : ℝ → Int)
    (h : ∀ x, rnd1 x = rnd2 x) (x : ℝ) :
    FloatSpec.Core.Generic_fmt.round_to_generic beta fexp rnd1 x =
      FloatSpec.Core.Generic_fmt.round_to_generic beta fexp rnd2 x :=
  FloatSpec.Core.Generic_fmt.round_ext beta fexp rnd1 rnd2 h x

example (fexp : Int → Int) (rnd : ℝ → Int) (x : ℝ) :
    FloatSpec.Core.Generic_fmt.round_to_generic beta fexp rnd (-x) =
      -FloatSpec.Core.Generic_fmt.round_to_generic beta fexp
        (FloatSpec.Core.Generic_fmt.Zrnd_opp rnd) x :=
  FloatSpec.Core.Generic_fmt.round_opp beta fexp rnd x

example (fexp : Int → Int) (mode : FloatSpec.Calc.Round.Mode) :
    FloatSpec.Calc.Round.round beta fexp mode 0 = 0 :=
  FloatSpec.Calc.Round.round_0 (beta := beta) (fexp := fexp) mode

-- This exponent is genuinely invalid, yet the source zero theorem still applies.
example : ¬ FloatSpec.Core.Generic_fmt.Valid_exp (fun e : Int => e + 1) := by
  intro h
  have hbad := ((h.valid_exp 0).2 (by decide)).1
  norm_num at hbad

example (rnd : ℝ → Int) [FloatSpec.Core.Generic_fmt.Valid_rnd rnd] :
    FloatSpec.Core.Generic_fmt.round_to_generic 2 (fun e => e + 1) rnd 0 = 0 :=
  FloatSpec.Core.Generic_fmt.round_0 2 _ rnd

example (emin prec : Int) (rnd : ℝ → Int)
    [FloatSpec.Core.Generic_fmt.Valid_rnd rnd] (x y : ℝ) (e : Int)
    (hx : generic_format beta (FLT_exp emin prec) x)
    (hy : generic_format beta (FLT_exp emin prec) y)
    (hb : FloatSpec.Core.Raux.bpow beta (e + 2 * prec - 1) ≤ |x * y|)
    (hnz : FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (x * y) - x * y ≠ 0) :
    FloatSpec.Core.Raux.bpow beta e ≤
      |FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (x * y) - x * y| :=
  mult_error_FLT_ge_bpow (beta := beta) (emin := emin) (prec := prec)
    (rnd := rnd) x y e hβ hx hy hb hnz

example (emin prec : Int) (x y : ℝ) (e : Int)
    (hx : generic_format beta (FLT_exp emin prec) x)
    (hy : generic_format beta (FLT_exp emin prec) y)
    (hb : x * y = 0 ∨ FloatSpec.Core.Raux.bpow beta e ≤ |x * y|) :
    let rnd := FloatSpec.Core.Generic_fmt.Znearest (fun t : Int => !(decide (2 ∣ t)))
    x * y - FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (x * y) = 0 ∨
      FloatSpec.Core.Raux.bpow beta (e + 1 - 2 * prec) ≤
        |x * y - FloatSpec.Core.Generic_fmt.roundR beta (FLT_exp emin prec) rnd (x * y)| :=
  mult_error_FLT_ge_bpow' beta emin prec x y e hβ hx hy hb

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

namespace DivisionSourceContracts

open FloatSpec.Core.Defs FloatSpec.Core.Digits FloatSpec.Core.Raux FloatSpec.Calc.Bracket

-- These clients demand the source's computed bounds and direct proposition,
-- without an extra radix proof argument or an Id/Hoare wrapper.
example (beta : Int) [ValidRadix beta]
    (m1 e1 m2 e2 : Int) (hm1 : 0 < m1) (hm2 : 0 < m2) :
    let e := (Zdigits beta m1 + e1) - (Zdigits beta m2 + e2)
    e ≤ FloatSpec.Core.Raux.mag beta (FloatSpec.Core.Defs.F2R (FlocqFloat.mk m1 e1 : FlocqFloat beta) /
      FloatSpec.Core.Defs.F2R (FlocqFloat.mk m2 e2 : FlocqFloat beta)) ∧
    FloatSpec.Core.Raux.mag beta (FloatSpec.Core.Defs.F2R (FlocqFloat.mk m1 e1 : FlocqFloat beta) /
      FloatSpec.Core.Defs.F2R (FlocqFloat.mk m2 e2 : FlocqFloat beta)) ≤ e + 1 :=
  FloatSpec.Calc.Div.mag_div_F2R beta m1 e1 m2 e2 hm1 hm2

example (beta : Int) [ValidRadix beta]
    (m1 e1 m2 e2 e : Int) (hm1 : 0 < m1) (hm2 : 0 < m2) :
    let result := FloatSpec.Calc.Div.Fdiv_core beta m1 e1 m2 e2 e
    inbetween_float beta result.1 e
      (FloatSpec.Core.Defs.F2R (FlocqFloat.mk m1 e1 : FlocqFloat beta) /
        FloatSpec.Core.Defs.F2R (FlocqFloat.mk m2 e2 : FlocqFloat beta)) result.2 :=
  FloatSpec.Calc.Div.Fdiv_core_correct beta m1 e1 m2 e2 e hm1 hm2

end DivisionSourceContracts

namespace SquareRootSourceContracts

open FloatSpec.Core.Defs FloatSpec.Core.Digits FloatSpec.Calc.Bracket

example (beta : Int) [ValidRadix beta] (m e : Int) (hm : 0 < m) :
    FloatSpec.Core.Raux.mag beta
        (Real.sqrt (FloatSpec.Core.Defs.F2R (FlocqFloat.mk m e : FlocqFloat beta))) =
      (Zdigits beta m + e + 1) / 2 :=
  FloatSpec.Calc.Sqrt.mag_sqrt_F2R beta m e hm

theorem sqrt_core_contract (beta : Int) [ValidRadix beta] (m e target : Int)
    (hm : 0 < m) (he : 2 * target ≤ e) :
    let (result, location) := FloatSpec.Calc.Sqrt.Fsqrt_core beta m e target
    inbetween_float beta result target
      (Real.sqrt (FloatSpec.Core.Defs.F2R (FlocqFloat.mk m e : FlocqFloat beta))) location :=
  FloatSpec.Calc.Sqrt.Fsqrt_core_correct beta m e target hm he

-- No validity condition on the exponent function is needed to bracket sqrt.
theorem sqrt_result_contract (beta : Int) [ValidRadix beta] (fexp : Int → Int)
    (x : FlocqFloat beta) (hx : 0 < FloatSpec.Core.Defs.F2R x) :
    let (m, e, l) := FloatSpec.Calc.Sqrt.Fsqrt beta fexp x
    e ≤ FloatSpec.Core.Generic_fmt.cexp beta fexp (Real.sqrt (FloatSpec.Core.Defs.F2R x)) ∧
    inbetween_float beta m e (Real.sqrt (FloatSpec.Core.Defs.F2R x)) l :=
  FloatSpec.Calc.Sqrt.Fsqrt_correct beta fexp x hx

end SquareRootSourceContracts

namespace FTZSourceContracts

example (prec emin beta : Int) [ValidRadix beta] (x : ℝ)
    (hx : FloatSpec.Core.FTZ.FTZ_format prec emin beta x) :
    FloatSpec.Core.FLX.FLXN_format prec beta x :=
  FloatSpec.Core.FTZ.FLXN_format_FTZ prec emin beta x hx

example (prec emin beta : Int) [ValidRadix beta] (x : ℝ)
    (hx : FloatSpec.Core.FTZ.FTZ_format prec emin beta x) :
    FloatSpec.Core.Generic_fmt.generic_format beta (FloatSpec.Core.FTZ.FTZ_exp prec emin) x :=
  FloatSpec.Core.FTZ.generic_format_FTZ prec emin beta x hx

end FTZSourceContracts

-- Each of these compiled Rocq exports omits positive precision.
#guard_no_source_premise FloatSpec.Core.FLT.cexp_FLT_FLX Prec_gt_0 at prec
#guard_no_source_premise FloatSpec.Core.FLT.generic_format_FLT_FLX Prec_gt_0 at prec
#guard_no_source_premise FloatSpec.Core.FLT.generic_format_FLX_FLT Prec_gt_0 at prec
#guard_no_source_premise FloatSpec.Core.FLT.round_FLT_FLX Prec_gt_0 at prec
#guard_no_source_premise FloatSpec.Core.FLT.cexp_FLT_FIX Prec_gt_0 at prec
#guard_no_source_premise FloatSpec.Core.FLT.generic_format_FIX_FLT Prec_gt_0 at prec
#guard_no_source_premise FloatSpec.Core.FLT.ulp_FLT_le Prec_gt_0 at prec
#guard_no_source_premise FloatSpec.Core.FLT.ulp_FLT_exact_shift Prec_gt_0 at prec
#guard_no_source_premise FloatSpec.Core.FLT.succ_FLT_exact_shift_pos Prec_gt_0 at prec
#guard_no_source_premise FloatSpec.Core.FLT.succ_FLT_exact_shift Prec_gt_0 at prec
#guard_no_source_premise FloatSpec.Core.FLT.pred_FLT_exact_shift Prec_gt_0 at prec

namespace FLTUnrestrictedSourceContracts

open FloatSpec.Core.Generic_fmt
variable (beta prec emin : Int) [ValidRadix beta] (x : Real)
example (h : (beta : Real) ^ (emin + prec - 1) ≤ |x|) :
    FloatSpec.Core.Generic_fmt.cexp beta (FloatSpec.Core.FLT.FLT_exp prec emin) x =
      FloatSpec.Core.Generic_fmt.cexp beta (FloatSpec.Core.FLX.FLX_exp prec) x :=
  FloatSpec.Core.FLT.cexp_FLT_FLX prec emin beta x h
example (h : (beta : Real) ^ (emin + prec - 1) ≤ |x|)
    (hx : FloatSpec.Core.Generic_fmt.generic_format beta (FloatSpec.Core.FLX.FLX_exp prec) x) :
    FloatSpec.Core.Generic_fmt.generic_format beta (FloatSpec.Core.FLT.FLT_exp prec emin) x :=
  FloatSpec.Core.FLT.generic_format_FLT_FLX prec emin beta x h hx
example (hx : FloatSpec.Core.Generic_fmt.generic_format beta (FloatSpec.Core.FLT.FLT_exp prec emin) x) :
    FloatSpec.Core.Generic_fmt.generic_format beta (FloatSpec.Core.FLX.FLX_exp prec) x :=
  FloatSpec.Core.FLT.generic_format_FLX_FLT prec emin beta x hx
example (rnd : Real → Int) (h : (beta : Real) ^ (emin + prec - 1) ≤ |x|) :
    round_to_generic beta (FloatSpec.Core.FLT.FLT_exp prec emin) rnd x =
      round_to_generic beta (FloatSpec.Core.FLX.FLX_exp prec) rnd x :=
  FloatSpec.Core.FLT.round_FLT_FLX prec emin beta rnd x h
example (hne : x ≠ 0) (h : |x| < (beta : Real) ^ (emin + prec)) :
    FloatSpec.Core.Generic_fmt.cexp beta (FloatSpec.Core.FLT.FLT_exp prec emin) x =
      FloatSpec.Core.Generic_fmt.cexp beta (FloatSpec.Core.FIX.FIX_exp emin) x :=
  FloatSpec.Core.FLT.cexp_FLT_FIX prec emin beta x hne h
example (hx : FloatSpec.Core.Generic_fmt.generic_format beta (FloatSpec.Core.FLT.FLT_exp prec emin) x) :
    FloatSpec.Core.Generic_fmt.generic_format beta (FloatSpec.Core.FIX.FIX_exp emin) x :=
  FloatSpec.Core.FLT.generic_format_FIX_FLT prec emin beta x hx

example (h : (beta : Real) ^ (emin + prec - 1) ≤ |x|) :
    FloatSpec.Core.Ulp.ulp beta (FloatSpec.Core.FLT.FLT_exp prec emin) x ≤
      |x| * (beta : Real) ^ (1 - prec) :=
  FloatSpec.Core.FLT.ulp_FLT_le prec emin beta x h
example (e : Int) (hx : x ≠ 0)
    (hm : emin + prec ≤ FloatSpec.Core.Raux.mag beta x)
    (he : emin + prec - FloatSpec.Core.Raux.mag beta x ≤ e) :
    FloatSpec.Core.Ulp.ulp beta (FloatSpec.Core.FLT.FLT_exp prec emin) (x * (beta : Real) ^ e) =
      FloatSpec.Core.Ulp.ulp beta (FloatSpec.Core.FLT.FLT_exp prec emin) x * (beta : Real) ^ e :=
  FloatSpec.Core.FLT.ulp_FLT_exact_shift prec emin beta x e hx hm he
example (e : Int) (hx : 0 < x)
    (hm : emin + prec ≤ FloatSpec.Core.Raux.mag beta x)
    (he : emin + prec - FloatSpec.Core.Raux.mag beta x ≤ e) :
    FloatSpec.Core.Ulp.succ beta (FloatSpec.Core.FLT.FLT_exp prec emin) (x * (beta : Real) ^ e) =
      FloatSpec.Core.Ulp.succ beta (FloatSpec.Core.FLT.FLT_exp prec emin) x * (beta : Real) ^ e :=
  FloatSpec.Core.FLT.succ_FLT_exact_shift_pos prec emin beta x e hx hm he
example (e : Int) (hx : x ≠ 0)
    (hm : emin + prec + 1 ≤ FloatSpec.Core.Raux.mag beta x)
    (he : emin + prec - FloatSpec.Core.Raux.mag beta x + 1 ≤ e) :
    FloatSpec.Core.Ulp.succ beta (FloatSpec.Core.FLT.FLT_exp prec emin) (x * (beta : Real) ^ e) =
      FloatSpec.Core.Ulp.succ beta (FloatSpec.Core.FLT.FLT_exp prec emin) x * (beta : Real) ^ e :=
  FloatSpec.Core.FLT.succ_FLT_exact_shift prec emin beta x e hx hm he
example (e : Int) (hx : x ≠ 0)
    (hm : emin + prec + 1 ≤ FloatSpec.Core.Raux.mag beta x)
    (he : emin + prec - FloatSpec.Core.Raux.mag beta x + 1 ≤ e) :
    FloatSpec.Core.Ulp.pred beta (FloatSpec.Core.FLT.FLT_exp prec emin) (x * (beta : Real) ^ e) =
      FloatSpec.Core.Ulp.pred beta (FloatSpec.Core.FLT.FLT_exp prec emin) x * (beta : Real) ^ e :=
  FloatSpec.Core.FLT.pred_FLT_exact_shift prec emin beta x e hx hm he

-- Positive precision is genuinely necessary for the reverse FIX-to-FLT
-- inclusion: every other source premise holds in this zero-precision case.
theorem zero_precision_reverse_inclusion_counterexample :
    |(1 : Real)| ≤ (2 : Real) ^ (0 + 0 : Int) ∧
    FloatSpec.Core.Generic_fmt.generic_format 2 (FloatSpec.Core.FIX.FIX_exp 0) (1 : Real) ∧
    ¬FloatSpec.Core.Generic_fmt.generic_format 2 (FloatSpec.Core.FLT.FLT_exp 0 0) (1 : Real) := by
  norm_num [FloatSpec.Core.Generic_fmt.generic_format,
    FloatSpec.Core.Generic_fmt.scaled_mantissa, FloatSpec.Core.Generic_fmt.cexp,
    FloatSpec.Core.FLT.FLT_exp, FloatSpec.Core.FIX.FIX_exp,
    FloatSpec.Core.Raux.mag, FloatSpec.Core.Raux.Ztrunc, FloatSpec.Core.Defs.F2R]

end FLTUnrestrictedSourceContracts

namespace RoundingWitnessSourceContracts

open FloatSpec.Core.Defs FloatSpec.Core.Round_pred

-- The dependent result, and not just its projection, must fit the source client.
noncomputable def value_client (rnd : ℝ → ℝ → Prop)
    (h : round_pred rnd) (x : ℝ) : {f : ℝ // rnd x f} :=
  round_val_of_pred rnd h x

noncomputable def function_client (rnd : ℝ → ℝ → Prop)
    (h : round_pred rnd) : {f : ℝ → ℝ // ∀ x, rnd x (f x)} :=
  round_fun_of_pred rnd h

private theorem identity_predicate : round_pred (fun x y : ℝ => y = x) := by
  constructor
  · intro x
    exact ⟨x, rfl⟩
  · intro x y f g hf hg hxy
    simpa [hf, hg] using hxy

theorem identity_value (x : ℝ) :
    (value_client (fun x y : ℝ => y = x) identity_predicate x).val = x :=
  (value_client (fun x y : ℝ => y = x) identity_predicate x).property

theorem identity_function :
    (function_client (fun x y : ℝ => y = x) identity_predicate).val = id := by
  funext x
  exact (function_client (fun x y : ℝ => y = x) identity_predicate).property x

theorem no_empty_predicate : ¬round_pred (fun _ _ : ℝ => False) := by
  intro h
  obtain ⟨_, hf⟩ := h.1 0
  exact hf

-- Freeze the former body only inside this regression. For every valid input,
-- the new proof-carrying interface preserves the value previously selected.
private noncomputable def legacy_value (rnd : ℝ → ℝ → Prop) (x : ℝ) : ℝ := by
  classical
  exact if h : ∃ f : ℝ, rnd x f then Classical.choose h else 0

theorem preserves_legacy_value (rnd : ℝ → ℝ → Prop)
    (h : round_pred rnd) (x : ℝ) :
    legacy_value rnd x = (round_val_of_pred rnd h x).val := by
  classical
  simp [legacy_value, round_val_of_pred, h.1 x]

theorem preserves_legacy_function (rnd : ℝ → ℝ → Prop)
    (h : round_pred rnd) :
    (fun x => legacy_value rnd x) = (round_fun_of_pred rnd h).val := by
  classical
  funext x
  simp [legacy_value, round_fun_of_pred, round_val_of_pred, h.1 x]

end RoundingWitnessSourceContracts

-- These unit-value laws have no positive-precision premise in compiled Flocq.
#guard_no_source_premise FloatSpec.Core.FLX.ulp_FLX_1 Prec_gt_0 at prec
#guard_no_source_premise FloatSpec.Core.FLX.succ_FLX_1 Prec_gt_0 at prec
#guard_no_source_premise FloatSpec.Core.FLX.ulp_FLX_1 FloatSpec.Test.SourcePremiseGuard.PositivePrecisionFact at prec
#guard_no_source_premise FloatSpec.Core.FLX.succ_FLX_1 FloatSpec.Test.SourcePremiseGuard.PositivePrecisionFact at prec

namespace FLXUnitSourceContracts

example (beta prec : Int) [ValidRadix beta] :
    FloatSpec.Core.Ulp.ulp beta (FloatSpec.Core.FLX.FLX_exp prec) 1 =
      (beta : ℝ) ^ (1 - prec) :=
  FloatSpec.Core.FLX.ulp_FLX_1 prec beta

example (beta prec : Int) [ValidRadix beta] :
    FloatSpec.Core.Ulp.succ beta (FloatSpec.Core.FLX.FLX_exp prec) 1 =
      1 + (beta : ℝ) ^ (1 - prec) :=
  FloatSpec.Core.FLX.succ_FLX_1 prec beta

-- These are total-definition laws, not adjacency claims for a valid format.
theorem nonpositive_precision_examples :
    FloatSpec.Core.Ulp.ulp 2 (FloatSpec.Core.FLX.FLX_exp 0) 1 = 2 ∧
    FloatSpec.Core.Ulp.succ 2 (FloatSpec.Core.FLX.FLX_exp 0) 1 = 3 ∧
    FloatSpec.Core.Ulp.ulp 2 (FloatSpec.Core.FLX.FLX_exp (-1)) 1 = 4 ∧
    FloatSpec.Core.Ulp.succ 2 (FloatSpec.Core.FLX.FLX_exp (-1)) 1 = 5 := by
  norm_num [FloatSpec.Core.FLX.ulp_FLX_1, FloatSpec.Core.FLX.succ_FLX_1]

end FLXUnitSourceContracts
