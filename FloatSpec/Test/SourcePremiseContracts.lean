import Lean
import FloatSpec.src.Prop.Div_sqrt_error
import FloatSpec.src.Prop.Round_odd

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

/-! Typed consumers deliberately omit proof-only section assumptions.
Unlike a bare `#check`, each example fails if a public theorem accidentally
inherits a stronger premise than its pinned Rocq counterpart. -/

namespace SourcePremiseContracts

variable (beta : Int) [ValidRadix beta] (hβ : 1 < beta)

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
