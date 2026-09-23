/-
FloatSpec exemplar lane: DoubleRoundingOddRadix, the Lean counterpart of
DoubleRoundingOddRadix.v.

Provenance: transliterates the trimmed Flocq
examples/Double_rounding_odd_radix.v at commit
7aab8f55bceec0cfafc3b3bc0e77e0dbb5a70c5f (upstream Copyright (C) 2014-2018
Pierre Roux, GNU LGPL version 3 or later; this transliteration is distributed
under the same terms). DoubleRoundingOddRadix.v states the upstream theorems,
the parameters and the row layout.
-/
import Exemplars.Compute
import Exemplars.Choices
import FloatSpec.src.Core.FLX
import FloatSpec.src.Core.FLT
import FloatSpec.src.Core.FTZ

namespace Exemplars.DoubleRoundingOddRadix

open FloatSpec.Core FloatSpec.Core.Defs FloatSpec.Calc
open Exemplars.Compute (plus mult sqrt)
open Exemplars.Choices (rnd_N)

instance : ValidRadix 3 := ⟨by decide⟩
instance : ValidRadix 5 := ⟨by decide⟩
instance : ValidRadix 7 := ⟨by decide⟩
instance : Prec_gt_0 2 := ⟨by decide⟩
instance : Prec_gt_0 3 := ⟨by decide⟩
instance : Fact ((0 : Int) < 2) := ⟨by decide⟩
instance : Fact ((0 : Int) < 3) := ⟨by decide⟩

/-- `(outer fexp1, inner fexp2)`. Flocq's `FLT_exp`/`FTZ_exp` take `emin`
first; the FloatSpec ports take `prec` first. -/
def formats : Int → (Int → Int) × (Int → Int)
  | 0 => (FLX.FLX_exp 2, FLX.FLX_exp 3)
  | 1 => (FLT.FLT_exp 2 (-4), FLT.FLT_exp 3 (-6))
  | _ => (FTZ.FTZ_exp 2 (-4), FTZ.FTZ_exp 3 (-5))

def tie : Int → Int → Bool
  | 0 => fun m => !(RoundNE.Zeven m)
  | 1 => Zaux.Zle_bool 0
  | 2 => fun _ => true
  | _ => fun _ => false

def op_round (beta : Int) [ValidRadix beta] (fexp : Int → Int) (c : Int → Bool) (op : Int)
    (x y : FlocqFloat beta) : FlocqFloat beta :=
  match op with
  | 0 => mult beta fexp (rnd_N c) x y
  | 1 => plus beta fexp (rnd_N c) x y
  | 2 => plus beta fexp (rnd_N c) x (Operations.Fopp beta y)
  | 3 => sqrt beta fexp (rnd_N c) x
  | _ => Compute.div beta fexp (rnd_N c) x y

def row (beta : Int) [ValidRadix beta] (family op k1 k2 : Int) (p : Int × Int × Int × Int) :
    List Int :=
  let (mx, ex, my, ey) := p
  let x : FlocqFloat beta := ⟨mx, ex⟩
  let y : FlocqFloat beta := ⟨my, ey⟩
  let (fexp1, fexp2) := formats family
  let inner := op_round beta fexp2 (tie k2) op x y
  let outer := plus beta fexp1 (rnd_N (tie k1)) inner ⟨0, 0⟩
  let direct := op_round beta fexp1 (tie k1) op x y
  [beta, family, op, k1, k2, mx, ex, my, ey,
   inner.Fnum, inner.Fexp, outer.Fnum, outer.Fexp, direct.Fnum, direct.Fexp,
   (Operations.Fminus beta outer direct).Fnum]

def inputs : Int → List (Int × Int × Int × Int)
  | 3 => [(8, -4, -8, -2), (-6, 0, 5, -3), (-5, 1, -3, -4), (7, -1, 8, -1),
          (-5, -1, 4, -1), (4, 1, 3, -4), (3, -1, 4, -2), (3, -2, 8, 1),
          (-5, -1, 8, -4), (3, 0, 8, 1), (-3, -1, 3, 1), (4, 1, 4, -1)]
  | 5 => [(-18, -4, 13, 1), (8, -2, -22, -2), (-10, -2, 9, 1), (19, -2, 11, -1),
          (9, -1, -18, -2), (-6, -3, 12, -4), (-7, -1, -12, -1), (-15, -2, -17, 0),
          (15, 1, -5, 0), (-23, -2, -14, 1), (19, -2, 21, -3), (6, 1, 12, -1)]
  | 7 => [(-45, 0, -30, 1), (12, -1, 45, 1), (34, -1, -17, 1), (24, 0, 25, -1),
          (-11, 1, -25, -3), (29, 0, 25, -1), (45, 0, -20, 0), (11, -3, -25, 1),
          (-26, -1, 40, 1), (-29, -2, 7, -2), (30, -1, 44, -3), (8, 1, 24, -1)]
  | _ => [(3, 1, -3, -2), (3, -1, -3, -2), (3, -4, -3, -4), (3, -1, 2, 1),
          (-3, -2, -3, 0), (3, -3, -2, -2), (3, -4, -3, 1), (2, -1, -2, -1),
          (2, 0, 3, -1), (2, -4, -3, -4), (2, -4, 3, -2), (-2, 1, -3, -2)]

def choice_pairs (op : Int) : List (Int × Int) :=
  if op == 4 then [(1, 1)] else [(0, 0), (1, 0), (0, 1), (3, 2)]

def rows (beta : Int) [ValidRadix beta] : List (List Int) :=
  [0, 1, 2].flatMap fun family => [0, 1, 2, 3, 4].flatMap fun op =>
    (choice_pairs op).flatMap fun (k1, k2) => (inputs beta).map (row beta family op k1 k2)

end Exemplars.DoubleRoundingOddRadix

open Exemplars.DoubleRoundingOddRadix in
#eval IO.println (toString (rows 3 ++ rows 5 ++ rows 7 ++ rows 2))
