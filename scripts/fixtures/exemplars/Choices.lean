/-
FloatSpec exemplar lane: sign-magnitude choice functions for Compute.lean.
Lean counterpart of Choices.v in this directory (not upstream text).

Each choice is read off the matching lemma of Flocq src/Calc/Round.v
(pinned 7aab8f55), as ported in FloatSpec.Calc.Round, and each `*_choice`
theorem checks with Lean that it satisfies Compute.v's `rnd_choice`
hypothesis for its rounding. The Rocq file proves the same statements
against Flocq itself.
-/
import FloatSpec.src.Calc.Round

namespace Exemplars.Choices

open FloatSpec.Core FloatSpec.Calc FloatSpec.Calc.Bracket FloatSpec.Calc.Round

/-- Toward minus infinity (`Zfloor`). -/
def rnd_DN (s : Bool) (m : Int) (l : Location) : Int := cond_incr (round_sign_DN s l) m
/-- Toward plus infinity (`Zceil`). -/
def rnd_UP (s : Bool) (m : Int) (l : Location) : Int := cond_incr (round_sign_UP s l) m
/-- Toward zero (`Ztrunc`): the magnitude is already truncated. -/
def rnd_ZR (_s : Bool) (m : Int) (_l : Location) : Int := m
/-- Nearest, ties to even (`ZnearestE`); `Zeven` is the port of `Z.even`. -/
def rnd_NE (_s : Bool) (m : Int) (l : Location) : Int :=
  cond_incr (round_N (!(RoundNE.Zeven m)) l) m
/-- Nearest, ties away from zero (`ZnearestA`). -/
def rnd_NA (_s : Bool) (m : Int) (l : Location) : Int := cond_incr (round_N true l) m
/-- `Znearest c` for an arbitrary tie-breaking predicate `c`. -/
def rnd_N (c : Int → Bool) (s : Bool) (m : Int) (l : Location) : Int :=
  cond_incr (round_N (if s then !(c (-(m + 1))) else c m) l) m

theorem rnd_DN_choice (x : ℝ) (m : Int) (l : Location) (h : inbetween_int m |x| l) :
    Raux.Zfloor x = Zaux.cond_Zopp (Raux.Rlt_bool x 0) (rnd_DN (Raux.Rlt_bool x 0) m l) :=
  inbetween_int_DN_sign x m l h

theorem rnd_UP_choice (x : ℝ) (m : Int) (l : Location) (h : inbetween_int m |x| l) :
    Raux.Zceil x = Zaux.cond_Zopp (Raux.Rlt_bool x 0) (rnd_UP (Raux.Rlt_bool x 0) m l) :=
  inbetween_int_UP_sign x m l h

theorem rnd_ZR_choice (x : ℝ) (m : Int) (l : Location) (h : inbetween_int m |x| l) :
    Raux.Ztrunc x = Zaux.cond_Zopp (Raux.Rlt_bool x 0) (rnd_ZR (Raux.Rlt_bool x 0) m l) :=
  inbetween_int_ZR_sign x m l h

theorem rnd_NE_choice (x : ℝ) (m : Int) (l : Location) (h : inbetween_int m |x| l) :
    Generic_fmt.Znearest (fun t => !(decide (2 ∣ t))) x =
      Zaux.cond_Zopp (Raux.Rlt_bool x 0) (rnd_NE (Raux.Rlt_bool x 0) m l) :=
  inbetween_int_NE_sign x m l h

theorem rnd_NA_choice (x : ℝ) (m : Int) (l : Location) (h : inbetween_int m |x| l) :
    Generic_fmt.Znearest Generic_fmt.ZnearestA x =
      Zaux.cond_Zopp (Raux.Rlt_bool x 0) (rnd_NA (Raux.Rlt_bool x 0) m l) :=
  inbetween_int_NA_sign x m l h

theorem rnd_N_choice (c : Int → Bool) (x : ℝ) (m : Int) (l : Location)
    (h : inbetween_int m |x| l) :
    Generic_fmt.Znearest c x =
      Zaux.cond_Zopp (Raux.Rlt_bool x 0) (rnd_N c (Raux.Rlt_bool x 0) m l) :=
  inbetween_int_N_sign c x m l h

end Exemplars.Choices
