import FloatSpec.src.Core.Round_NE

/-! Typed source clients distinguish the hypotheses on four nearest-even exports.
The point theorems refer to the concrete rounded value, not merely existence. -/

namespace FloatSpec.Test.RoundNEPointContracts

open FloatSpec.Core.Generic_fmt FloatSpec.Core.RoundNE

variable (beta : Int) [ValidRadix beta] (fexp : Int → Int)

#check (round_NE_opp (beta := beta) (fexp := fexp) : ∀ x : Real,
  roundR beta fexp (Znearest (fun t ↦ !decide (2 ∣ t))) (-x) =
    -roundR beta fexp (Znearest (fun t ↦ !decide (2 ∣ t))) x)

variable [Valid_exp fexp]

#check (round_NE_abs (beta := beta) (fexp := fexp) : ∀ x : Real,
  roundR beta fexp (Znearest (fun t ↦ !decide (2 ∣ t))) |x| =
    |roundR beta fexp (Znearest (fun t ↦ !decide (2 ∣ t))) x|)

variable [Exists_NE beta fexp]

#check (round_NE_pt_pos (beta := beta) (fexp := fexp) : ∀ x : Real, 0 < x →
  Rnd_NE_pt beta fexp x (roundR beta fexp (Znearest (fun t ↦ !decide (2 ∣ t))) x))

#check (round_NE_pt (beta := beta) (fexp := fexp) : ∀ x : Real,
  Rnd_NE_pt beta fexp x (roundR beta fexp (Znearest (fun t ↦ !decide (2 ∣ t))) x))

#print axioms round_NE_opp
#print axioms round_NE_abs
#print axioms round_NE_pt_pos
#print axioms round_NE_pt

end FloatSpec.Test.RoundNEPointContracts
