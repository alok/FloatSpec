import FloatSpec.src.Core.Round_NE

/-! Typed source clients distinguish the hypotheses on eight nearest-even exports.
The point theorems refer to the concrete rounded value, not merely existence. -/

namespace FloatSpec.Test.RoundNEPointContracts

open FloatSpec.Core.Generic_fmt FloatSpec.Core.RoundNE

variable (beta : Int) [ValidRadix beta] (fexp : Int → Int)

#check (round_NE_opp (beta := beta) (fexp := fexp) : ∀ x : Real,
  roundR beta fexp (Znearest (fun t ↦ !decide (2 ∣ t))) (-x) =
    -roundR beta fexp (Znearest (fun t ↦ !decide (2 ∣ t))) x)

#check (round_NE_opp_check_spec (beta := beta) (fexp := fexp) : ∀ x f : Real,
  Rnd_NE_pt beta fexp x f ↔ Rnd_NE_pt beta fexp (-x) (-f))

variable [Valid_exp fexp]

#check (round_NE_abs (beta := beta) (fexp := fexp) : ∀ x : Real,
  roundR beta fexp (Znearest (fun t ↦ !decide (2 ∣ t))) |x| =
    |roundR beta fexp (Znearest (fun t ↦ !decide (2 ∣ t))) x|)

variable [Exists_NE beta fexp]

#check (Rnd_NE_pt_total (beta := beta) (fexp := fexp) :
  FloatSpec.Core.Defs.round_pred_total (Rnd_NE_pt beta fexp))

#check (Rnd_NE_pt_monotone (beta := beta) (fexp := fexp) :
  FloatSpec.Core.Defs.round_pred_monotone (Rnd_NE_pt beta fexp))

#check (Rnd_NE_pt_round (beta := beta) (fexp := fexp) :
  FloatSpec.Core.Defs.round_pred (Rnd_NE_pt beta fexp))

#check (round_NE_pt_pos (beta := beta) (fexp := fexp) : ∀ x : Real, 0 < x →
  Rnd_NE_pt beta fexp x (roundR beta fexp (Znearest (fun t ↦ !decide (2 ∣ t))) x))

#check (round_NE_pt (beta := beta) (fexp := fexp) : ∀ x : Real,
  Rnd_NE_pt beta fexp x (roundR beta fexp (Znearest (fun t ↦ !decide (2 ∣ t))) x))

#print axioms round_NE_opp
#print axioms round_NE_opp_check_spec
#print axioms round_NE_abs
#print axioms round_NE_pt_pos
#print axioms round_NE_pt
#print axioms Rnd_NE_pt_total
#print axioms Rnd_NE_pt_monotone
#print axioms Rnd_NE_pt_round

/-- The two source APIs compose: the actual rounded-value function is monotone. -/
theorem rounded_values_monotone (x y : Real) (hxy : x ≤ y) :
    roundR beta fexp (Znearest (fun t ↦ !decide (2 ∣ t))) x ≤
      roundR beta fexp (Znearest (fun t ↦ !decide (2 ∣ t))) y :=
  Rnd_NE_pt_monotone beta fexp x y _ _
    (round_NE_pt beta fexp x) (round_NE_pt beta fexp y) hxy

#print axioms rounded_values_monotone

end FloatSpec.Test.RoundNEPointContracts
