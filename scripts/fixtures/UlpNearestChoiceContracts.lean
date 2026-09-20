import FloatSpec.src.Core.Ulp
import FloatSpec.src.Calc.Round

namespace FloatSpec.Test.UlpNearestChoiceContracts

open FloatSpec.Core.Generic_fmt
open FloatSpec.Core.Ulp Std.Do

variable (beta : Int) [ValidRadix beta] (fexp : Int → Int) [Valid_exp fexp]

theorem nearest_eq_down (choice : Int → Bool) (x : Real)
    (h : x < (roundR beta fexp rnd_floor x + roundR beta fexp rnd_ceil x) / 2) :
    roundR beta fexp (Znearest choice) x = roundR beta fexp rnd_floor x :=
  FloatSpec.Core.Ulp.round_N_eq_DN beta fexp choice x h

#print axioms nearest_eq_down

theorem nearest_eq_up (choice : Int → Bool) (x : Real)
    (h : (roundR beta fexp rnd_floor x + roundR beta fexp rnd_ceil x) / 2 < x) :
    roundR beta fexp (Znearest choice) x = roundR beta fexp rnd_ceil x :=
  FloatSpec.Core.Ulp.round_N_eq_UP beta fexp choice x h

#print axioms nearest_eq_up

theorem nearest_eq_down_pt (choice : Int → Bool) (x d u : Real)
    (Hd : Rnd_DN_pt (generic_format beta fexp) x d)
    (Hu : Rnd_UP_pt (generic_format beta fexp) x u)
    (h : x < (d + u) / 2) :
    roundR beta fexp (Znearest choice) x = d :=
  FloatSpec.Core.Ulp.round_N_eq_DN_pt beta fexp choice x d u Hd Hu h

#print axioms nearest_eq_down_pt

theorem nearest_eq_up_pt (choice : Int → Bool) (x d u : Real)
    (Hd : Rnd_DN_pt (generic_format beta fexp) x d)
    (Hu : Rnd_UP_pt (generic_format beta fexp) x u)
    (h : (d + u) / 2 < x) :
    roundR beta fexp (Znearest choice) x = u :=
  FloatSpec.Core.Ulp.round_N_eq_UP_pt beta fexp choice x d u Hd Hu h

#print axioms nearest_eq_up_pt

theorem nearest_choices_agree_away_from_ties (choice₁ choice₂ : Int → Bool) (x : Real)
    (hne : x - roundR beta fexp rnd_floor x ≠ roundR beta fexp rnd_ceil x - x) :
    roundR beta fexp (Znearest choice₁) x = roundR beta fexp (Znearest choice₂) x :=
  FloatSpec.Core.Ulp.round_N_eq_ties beta fexp choice₁ choice₂ x hne

#print axioms nearest_choices_agree_away_from_ties

theorem nearest_plus_ulp [FloatSpec.Core.Ulp.Monotone_exp fexp]
    (choice₁ choice₂ : Int → Bool) (x : Real) :
    let rx := roundR beta fexp (Znearest choice₂) x
    x ≤ roundR beta fexp (Znearest choice₁) (rx + ulp beta fexp rx) :=
  FloatSpec.Core.Ulp.round_N_plus_ulp_ge beta fexp choice₁ choice₂ x

#print axioms nearest_plus_ulp

/-- Source client for the upper-midpoint bound with the actual supplied policy. -/
theorem nearest_below_midpoint (choice : Int → Bool) (u v : Real)
    (Fu : generic_format beta fexp u)
    (h : v < (u + succ beta fexp u) / 2) :
    round_to_generic beta fexp (Znearest choice) v ≤ u :=
  FloatSpec.Core.Ulp.round_N_le_midp beta fexp choice u v Fu h

#print axioms nearest_below_midpoint

/-- Source client for the lower-midpoint bound with the actual supplied policy. -/
theorem nearest_above_midpoint (choice : Int → Bool) (u v : Real)
    (Fu : generic_format beta fexp u)
    (h : (u + pred beta fexp u) / 2 < v) :
    u ≤ round_to_generic beta fexp (Znearest choice) v :=
  FloatSpec.Core.Ulp.round_N_ge_midp beta fexp choice u v Fu h

#print axioms nearest_above_midpoint

/-- A tie is precisely where changing the policy can change the result. -/
theorem tie_choices_differ :
    roundR 2 (fun _ => 0) (Znearest (fun _ => false)) (1 / 2 : Real) = 0 ∧
    roundR 2 (fun _ => 0) (Znearest (fun _ => true)) (1 / 2 : Real) = 1 := by
  norm_num [roundR, scaled_mantissa, cexp, Znearest,
    FloatSpec.Core.Raux.Zfloor, FloatSpec.Core.Raux.Zceil, FloatSpec.Core.Raux.Rcompare]

#print axioms tie_choices_differ

/-- The integer rounding decision exposes the same two outcomes at a midpoint. -/
theorem executable_tie_decisions :
    [FloatSpec.Calc.Round.cond_incr
      (FloatSpec.Calc.Round.round_N false (.loc_Inexact .eq)) 0,
     FloatSpec.Calc.Round.cond_incr
      (FloatSpec.Calc.Round.round_N true (.loc_Inexact .eq)) 0] = [0, 1] := by
  decide +kernel

#print axioms executable_tie_decisions

#eval [FloatSpec.Calc.Round.cond_incr
  (FloatSpec.Calc.Round.round_N false (.loc_Inexact .eq)) 0,
 FloatSpec.Calc.Round.cond_incr
  (FloatSpec.Calc.Round.round_N true (.loc_Inexact .eq)) 0]

end FloatSpec.Test.UlpNearestChoiceContracts
