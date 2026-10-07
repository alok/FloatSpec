import FloatSpec.src.Core.Raux

namespace RauxCondOppContracts
open FloatSpec.Core.Raux

-- Raux.v:2155-2266. Rocq's `Bool.eqb` is `==` on `Bool`; `IZR` is the integer cast.
theorem eqb_symm : ∀ a b : Bool, (a == b) = (b == a) := eqb_sym
theorem eqb_neg : ∀ a b : Bool, a = !b → (a == b) = false := eqb_false
theorem eqb_same : ∀ a b : Bool, a = b → (a == b) = true := eqb_true

theorem raux_cond_opp_contracts_check_1 (b : Bool) (m : ℝ) : cond_Ropp b m = if b then -m else m := rfl

theorem izr_cond_Zopp : ∀ (b : Bool) (m : Int),
    ((FloatSpec.Core.Zaux.cond_Zopp b m : Int) : ℝ) = cond_Ropp b (m : ℝ) := IZR_cond_Zopp
theorem abs_cond : ∀ (b : Bool) (m : ℝ), |cond_Ropp b m| = |m| := abs_cond_Ropp
theorem cond_lt : ∀ m : ℝ, cond_Ropp (Rlt_bool m 0) m = |m| := cond_Ropp_Rlt_bool
theorem lt_cond : ∀ (x : ℝ) (sx : Bool), 0 < x → Rlt_bool (cond_Ropp sx x) 0 = sx :=
  Rlt_bool_cond_Ropp
theorem involutive : ∀ (b : Bool) (x : ℝ), cond_Ropp b (cond_Ropp b x) = x := cond_Ropp_involutive
theorem inj : ∀ (b : Bool) (x y : ℝ), cond_Ropp b x = cond_Ropp b y → x = y := cond_Ropp_inj
theorem mult_l : ∀ (b : Bool) (x y : ℝ), cond_Ropp b (x * y) = cond_Ropp b x * y :=
  cond_Ropp_mult_l
theorem mult_r : ∀ (b : Bool) (x y : ℝ), cond_Ropp b (x * y) = x * cond_Ropp b y :=
  cond_Ropp_mult_r
theorem plus : ∀ (b : Bool) (x y : ℝ), cond_Ropp b (x + y) = cond_Ropp b x + cond_Ropp b y :=
  cond_Ropp_plus

#print axioms lt_cond

-- At zero the strict sign test reads false whatever the flag, so `0 < x` is needed.
private theorem lt_cond_needs_pos : ¬ ∀ (x : ℝ) (sx : Bool), Rlt_bool (cond_Ropp sx x) 0 = sx := by
  intro h
  have := h 0 true
  simp [cond_Ropp, Rlt_bool_eq_decide] at this

private theorem eqb_false_needs_negation : ¬ ∀ a b : Bool, (a == b) = false := by
  intro h
  exact absurd (h true true) (by decide)

#print axioms lt_cond_needs_pos

end RauxCondOppContracts
