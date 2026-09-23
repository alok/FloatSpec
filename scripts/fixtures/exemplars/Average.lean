/-
FloatSpec exemplar lane: Average, the Lean counterpart of Average.v.

Provenance: transliterates the trimmed Flocq examples/Average.v at commit
7aab8f55bceec0cfafc3b3bc0e77e0dbb5a70c5f (upstream Copyright (C) 2014-2018
Sylvie Boldo, GNU LGPL version 3 or later; this transliteration is
distributed under the same terms). Average.v lists what was kept and
replaced. It also proves, in Rocq, that the integer sign and magnitude tests
used by `average` equal upstream's real `Rle_bool` tests.
-/
import Exemplars.Compute
import Exemplars.Choices
import FloatSpec.src.Core.FLT

namespace Exemplars.Average

open FloatSpec.Core FloatSpec.Core.Defs FloatSpec.Calc
open Exemplars.Compute (plus)
open Exemplars.Choices (rnd_NE)

abbrev F := FlocqFloat 2

section Average

variable (emin prec : Int) [Prec_gt_0 prec]

/-- Flocq's `FLT_exp emin prec`; the FloatSpec port takes `prec` first. -/
def fexp := FLT.FLT_exp prec emin
def two : F := ⟨2, 0⟩

def avg_naive (x y : F) : F :=
  Compute.div 2 (fexp emin prec) rnd_NE (plus 2 (fexp emin prec) rnd_NE x y) two

def avg_sum_half (x y : F) : F :=
  plus 2 (fexp emin prec) rnd_NE (Compute.div 2 (fexp emin prec) rnd_NE x two)
    (Compute.div 2 (fexp emin prec) rnd_NE y two)

def avg_half_sub (x y : F) : F :=
  plus 2 (fexp emin prec) rnd_NE x
    (Compute.div 2 (fexp emin prec) rnd_NE
      (plus 2 (fexp emin prec) rnd_NE y (Operations.Fopp 2 x)) two)

def average (x y : F) : F :=
  let samesign := match Zaux.Zle_bool 0 x.Fnum, Zaux.Zle_bool 0 y.Fnum with
    | true, true => true
    | false, false => true
    | _, _ => false
  if samesign then
    match Zaux.Zle_bool (Operations.Fminus 2 (Operations.Fabs 2 x) (Operations.Fabs 2 y)).Fnum 0 with
    | true => avg_half_sub emin prec x y
    | false => avg_half_sub emin prec y x
  else avg_naive emin prec x y

end Average

instance : Prec_gt_0 3 := ⟨by decide⟩
instance : Prec_gt_0 4 := ⟨by decide⟩

def row (emin prec : Int) [Prec_gt_0 prec] (p : (Int × Int) × (Int × Int)) : List Int :=
  let ((mx, ex), (my, ey)) := p
  let x : F := ⟨mx, ex⟩
  let y : F := ⟨my, ey⟩
  let n := avg_naive emin prec x y
  let s := avg_sum_half emin prec x y
  let h := avg_half_sub emin prec x y
  let a := average emin prec x y
  [emin, prec, mx, ex, my, ey, n.Fnum, n.Fexp, s.Fnum, s.Fexp,
   h.Fnum, h.Fexp, a.Fnum, a.Fexp]

def signed (l : List (Int × Int)) : List (Int × Int) :=
  (0, 0) :: l ++ l.map fun p => (-p.1, p.2)

def values (prec : Int) : List (Int × Int) :=
  if prec == 3 then
    signed [(1, -6), (3, -6), (4, -6), (7, -6), (5, -5), (7, -1), (6, 2), (7, 3)]
  else
    signed [(1, -4), (5, -4), (8, -4), (15, -4), (9, -3), (13, 0), (11, 2), (15, 5)]

def grid (emin prec : Int) [Prec_gt_0 prec] : List (List Int) :=
  (values prec).flatMap fun x => (values prec).map fun y => row emin prec (x, y)

end Exemplars.Average

open Exemplars.Average in
#eval IO.println (toString (grid (-6) 3 ++ grid (-4) 4))
