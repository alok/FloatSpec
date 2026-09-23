import FloatSpec.src.Core.Ulp

/-! Source classical-witness construction and the exact boundary of its
choice independence. No native execution of real-valued ULP is claimed. -/

namespace FloatSpec.Test.UlpSourceChoice

open FloatSpec.Core.Ulp FloatSpec.Core.Generic_fmt FloatSpec.Core.Defs

private noncomputable def legacyNegligibleExp (fexp : Int → Int) : Option Int := by
  classical
  exact if h : ∃ n, n ≤ fexp n then some (Classical.choose h) else none

private noncomputable def legacyUlp (beta : Int) [ValidRadix beta]
    (fexp : Int → Int) (x : Real) : Real :=
  if x = 0 then
    match legacyNegligibleExp fexp with
    | some n => (beta : Real) ^ fexp n
    | none => 0
  else (beta : Real) ^ cexp beta fexp x

/-- For valid exponent functions, the repaired source witness construction
preserves every ULP value, including zero, under the same radix. -/
theorem valid_exp_ulp_preserved (beta : Int) [ValidRadix beta]
    (fexp : Int → Int) [Valid_exp fexp] (x : Real) :
    ulp beta fexp x = legacyUlp beta fexp x := by
  classical
  by_cases hx : x = 0
  · subst x
    rcases negligible_exp_spec' (fexp := fexp) with
      ⟨hnone, hlt⟩ | ⟨n, hsome, hsmall⟩
    · have hnot : ¬ ∃ n, n ≤ fexp n := by
        rintro ⟨n, hn⟩
        exact (not_lt_of_ge hn) (hlt n)
      simp [ulp, legacyUlp, legacyNegligibleExp, hnone, hnot]
    · have hex : ∃ n, n ≤ fexp n := ⟨n, hsmall⟩
      have he := fexp_negligible_exp_eq fexp n (Classical.choose hex)
        hsmall (Classical.choose_spec hex)
      simpa [ulp, legacyUlp, legacyNegligibleExp, hsome, hex] using
        congrArg (fun exponent : Int => (beta : Real) ^ exponent) he
  · simp [ulp, legacyUlp, hx]

/-- The witness projection now has the same definition shape as pinned Rocq. -/
theorem negligible_choice_contract (fexp : Int → Int) :
    negligible_exp fexp =
      match FloatSpec.Core.Raux.LPO_Z (fun n => n ≤ fexp n) (fun _ => Classical.em _) with
      | .inl witness => some witness.val
      | .inr _ => none := rfl

/-- Literal source ULP body; zero must inspect the negligible-exponent choice. -/
theorem ulp_body (beta : Int) [ValidRadix beta] (fexp : Int → Int) (x : Real) :
    ulp beta fexp x =
      if x = 0 then
        match negligible_exp fexp with
        | some n => (beta : Real) ^ fexp n
        | none => 0
      else (beta : Real) ^ cexp beta fexp x := rfl

/-- Literal positive-predecessor body retains the binade-boundary branch. -/
theorem pred_pos_body (beta : Int) [ValidRadix beta] (fexp : Int → Int) (x : Real) :
    pred_pos beta fexp x =
      if x = (beta : Real) ^ (FloatSpec.Core.Raux.mag beta x - 1) then
        x - (beta : Real) ^ fexp (FloatSpec.Core.Raux.mag beta x - 1)
      else x - ulp beta fexp x := rfl

/-- Literal source successor distinguishes the nonnegative and negative branches. -/
theorem succ_body (beta : Int) [ValidRadix beta] (fexp : Int → Int) (x : Real) :
    succ beta fexp x =
      if 0 ≤ x then x + ulp beta fexp x else -pred_pos beta fexp (-x) := rfl

/-- Literal source predecessor is successor under negation. -/
theorem pred_body (beta : Int) [ValidRadix beta] (fexp : Int → Int) (x : Real) :
    pred beta fexp x = -succ beta fexp (-x) := rfl

/-- Identity exponents fail the small-regime stability required by Valid_exp. -/
theorem identity_not_valid : ¬ Valid_exp (fun exponent : Int => exponent) := by
  intro h
  have impossible := (h.valid_exp 0).2 (by decide)
  norm_num at impossible

/-- Without validity, two acceptable witnesses can determine different spacings. -/
theorem invalid_choice_difference :
    (0 : Int) ≤ (fun exponent : Int => exponent) 0 ∧
    (1 : Int) ≤ (fun exponent : Int => exponent) 1 ∧
    (2 : Real) ^ ((fun exponent : Int => exponent) 0) ≠
      (2 : Real) ^ ((fun exponent : Int => exponent) 1) := by
  norm_num

section Unrestricted
variable (beta : Int) [ValidRadix beta] (fexp : Int → Int)

/-- Typed source client without an exponent-validity premise. -/
theorem succ_opp_unrestricted (x : Real) :
    succ beta fexp (-x) = -pred beta fexp x :=
  succ_opp beta fexp x

#print axioms succ_opp_unrestricted

/-- Typed source client without an exponent-validity premise. -/
theorem pred_opp_unrestricted (x : Real) :
    pred beta fexp (-x) = -succ beta fexp x :=
  pred_opp beta fexp x

#print axioms pred_opp_unrestricted

/-- Typed source client without an exponent-validity premise. -/
theorem ulp_opp_unrestricted (x : Real) :
    ulp beta fexp (-x) = ulp beta fexp x :=
  ulp_opp beta fexp x

#print axioms ulp_opp_unrestricted

/-- Typed source client without an exponent-validity premise. -/
theorem ulp_abs_unrestricted (x : Real) :
    ulp beta fexp |x| = ulp beta fexp x :=
  ulp_abs beta fexp x

#print axioms ulp_abs_unrestricted

/-- Typed source client without an exponent-validity premise. -/
theorem succ_eq_pos_unrestricted (x : Real) (hx : 0 ≤ x) :
    succ beta fexp x = x + ulp beta fexp x :=
  succ_eq_pos beta fexp x hx

#print axioms succ_eq_pos_unrestricted

/-- Typed source client without an exponent-validity premise. -/
theorem ulp_ge_0_unrestricted (x : Real) :
    0 ≤ ulp beta fexp x :=
  ulp_ge_0 beta fexp x

#print axioms ulp_ge_0_unrestricted

/-- Typed source client without an exponent-validity premise. -/
theorem pred_eq_pos_unrestricted (x : Real) (hx : 0 ≤ x) :
    pred beta fexp x = pred_pos beta fexp x :=
  pred_eq_pos beta fexp x hx

#print axioms pred_eq_pos_unrestricted

/-- Typed source client without an exponent-validity premise. -/
theorem ulp_le_id_unrestricted (x : Real) (hx : 0 < x) (hF : generic_format beta fexp x) :
    ulp beta fexp x ≤ x :=
  ulp_le_id beta fexp x hx hF

#print axioms ulp_le_id_unrestricted

/-- Typed source client without an exponent-validity premise. -/
theorem ulp_le_abs_unrestricted (x : Real) (hx : x ≠ 0) (hF : generic_format beta fexp x) :
    ulp beta fexp x ≤ |x| :=
  ulp_le_abs beta fexp x hx hF

#print axioms ulp_le_abs_unrestricted

/-- Typed source client without an exponent-validity premise. -/
theorem ulp_canonical_unrestricted (m e : Int) (hm : m ≠ 0)
    (hc : canonical beta fexp (FlocqFloat.mk m e)) :
    ulp beta fexp (F2R (FlocqFloat.mk m e : FlocqFloat beta)) = (beta : Real) ^ e :=
  ulp_canonical beta fexp m e hm ValidRadix.valid hc

#print axioms ulp_canonical_unrestricted

/-- Typed source client without an exponent-validity premise. -/
theorem ulp_bpow_unrestricted (e : Int) :
    ulp beta fexp ((beta : Real) ^ e) = (beta : Real) ^ fexp (e + 1) :=
  ulp_bpow beta fexp e

#print axioms ulp_bpow_unrestricted

/-- Typed source client without an exponent-validity premise. -/
theorem pred_bpow_unrestricted (e : Int) :
    pred beta fexp ((beta : Real) ^ e) = (beta : Real) ^ e - (beta : Real) ^ fexp e :=
  pred_bpow beta fexp e ValidRadix.valid

#print axioms pred_bpow_unrestricted

/-- Typed source client without an exponent-validity premise. -/
theorem generic_abs_unrestricted (x : Real) (hF : generic_format beta fexp x) :
    generic_format beta fexp |x| :=
  FloatSpec.Core.Generic_fmt.generic_format_abs beta fexp x hF

#print axioms generic_abs_unrestricted

/-- Typed source client without an exponent-validity premise. -/
theorem generic_abs_inv_unrestricted (x : Real) (hF : generic_format beta fexp |x|) :
    generic_format beta fexp x :=
  FloatSpec.Core.Generic_fmt.generic_format_abs_inv beta fexp x hF

#print axioms generic_abs_inv_unrestricted

/-- Typed neighbor client without exponent validity, matching pinned Rocq. -/
theorem pred_pos_lt_id_unrestricted (x : Real) (hx : x ≠ 0) :
    pred_pos beta fexp x < x :=
  pred_pos_lt_id beta fexp x hx

#print axioms pred_pos_lt_id_unrestricted

/-- Typed neighbor client without exponent validity, matching pinned Rocq. -/
theorem succ_gt_id_unrestricted (x : Real) (hx : x ≠ 0) :
    x < succ beta fexp x :=
  succ_gt_id beta fexp x hx

#print axioms succ_gt_id_unrestricted

/-- Typed neighbor client without exponent validity, matching pinned Rocq. -/
theorem pred_lt_id_unrestricted (x : Real) (hx : x ≠ 0) :
    pred beta fexp x < x :=
  pred_lt_id beta fexp x hx

#print axioms pred_lt_id_unrestricted

/-- Typed neighbor client without exponent validity, matching pinned Rocq. -/
theorem succ_ge_id_unrestricted (x : Real) :
    x ≤ succ beta fexp x :=
  succ_ge_id beta fexp x

#print axioms succ_ge_id_unrestricted

/-- Typed neighbor client without exponent validity, matching pinned Rocq. -/
theorem pred_le_id_unrestricted (x : Real) :
    pred beta fexp x ≤ x :=
  pred_le_id beta fexp x

#print axioms pred_le_id_unrestricted

/-- Typed neighbor client without exponent validity, matching pinned Rocq. -/
theorem succ_0_unrestricted  :
    succ beta fexp 0 = ulp beta fexp 0 :=
  succ_0 beta fexp

#print axioms succ_0_unrestricted

/-- Typed neighbor client without exponent validity, matching pinned Rocq. -/
theorem pred_0_unrestricted  :
    pred beta fexp 0 = -ulp beta fexp 0 :=
  pred_0 beta fexp

#print axioms pred_0_unrestricted

end Unrestricted

/-- The source integer witness lemma has no radix parameter or radix premise. -/
theorem witness_exponents_agree (fexp : Int → Int) [Valid_exp fexp]
    (n m : Int) (hn : n ≤ fexp n) (hm : m ≤ fexp m) : fexp n = fexp m :=
  fexp_negligible_exp_eq fexp n m hn hm

#print axioms witness_exponents_agree
#print axioms valid_exp_ulp_preserved
#print axioms negligible_choice_contract
#print axioms ulp_body
#print axioms pred_pos_body
#print axioms succ_body
#print axioms pred_body
#print axioms identity_not_valid
#print axioms invalid_choice_difference

end FloatSpec.Test.UlpSourceChoice
