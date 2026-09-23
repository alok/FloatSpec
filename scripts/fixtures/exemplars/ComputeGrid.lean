/-
FloatSpec exemplar lane: ComputeGrid, the Lean counterpart of ComputeGrid.v.
FloatSpec-authored driver (not upstream text) over Compute.lean, the
transliteration of Flocq examples/Compute.v at 7aab8f55. See ComputeGrid.v
for the grid and the row layout.
-/
import Exemplars.Compute
import Exemplars.Choices
import FloatSpec.src.Core.FLX
import FloatSpec.src.Core.FLT
import FloatSpec.src.Core.FIX
import FloatSpec.src.Core.FTZ

namespace Exemplars.ComputeGrid

open FloatSpec.Core FloatSpec.Core.Defs FloatSpec.Calc.Bracket
open Exemplars.Compute Exemplars.Choices

instance : ValidRadix 3 := ⟨by decide⟩
instance : ValidRadix 10 := ⟨by decide⟩
instance : Prec_gt_0 3 := ⟨by decide⟩
instance : Fact ((0 : Int) < 3) := ⟨by decide⟩

/-- Flocq's `FLT_exp emin prec`, `FTZ_exp emin prec` take `emin` first;
the FloatSpec ports take `prec` first. -/
def fexp_of : Int → Int → Int
  | 0 => FLX.FLX_exp 3
  | 1 => FLT.FLT_exp 3 (-3)
  | 2 => FIX.FIX_exp (-1)
  | _ => FTZ.FTZ_exp 3 (-3)

def choice_of : Int → Bool → Int → Location → Int
  | 0 => rnd_DN
  | 1 => rnd_UP
  | 2 => rnd_ZR
  | 3 => rnd_NE
  | _ => rnd_NA

def inputs : List (Int × Int × Int × Int) :=
  [(0, 0, 1, 0), (1, 0, 1, 0), (1, 0, 3, 0), (-7, 0, 2, 0),
   (23, -1, -5, 2), (-122, -2, 7, -1), (999, -3, 13, 0), (1, -5, 1, -5),
   (5, 2, -1, -4), (27, 0, 8, 1), (-1, 0, -1, 0), (4, -6, 3, -7),
   (100, 0, 0, 0), (-26, 1, 9, -3), (15, -2, 15, -2), (2, 4, -2, -4)]

def row (beta : Int) [ValidRadix beta] (fk ck : Int) (p : Int × Int × Int × Int) :
    List Int :=
  let (mx, ex, my, ey) := p
  let x : FlocqFloat beta := ⟨mx, ex⟩
  let y : FlocqFloat beta := ⟨my, ey⟩
  let fexp := fexp_of fk
  let ch := choice_of ck
  let a := plus beta fexp ch x y
  let m := mult beta fexp ch x y
  let d := div beta fexp ch x y
  let r := sqrt beta fexp ch x
  [beta, fk, ck, mx, ex, my, ey, a.Fnum, a.Fexp, m.Fnum, m.Fexp,
   d.Fnum, d.Fexp, r.Fnum, r.Fexp]

def grid (beta : Int) [ValidRadix beta] : List (List Int) :=
  [0, 1, 2, 3].flatMap fun fk =>
    [0, 1, 2, 3, 4].flatMap fun ck => inputs.map (row beta fk ck)

end Exemplars.ComputeGrid

open Exemplars.ComputeGrid in
#eval IO.println (toString (grid 2 ++ grid 3 ++ grid 10 : List (List Int)))
