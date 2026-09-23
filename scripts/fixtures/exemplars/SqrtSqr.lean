/-
FloatSpec exemplar lane: SqrtSqr, the Lean counterpart of SqrtSqr.v.

Provenance: transliterates the trimmed Flocq examples/Sqrt_sqr.v, Section
Sec6, at commit 7aab8f55bceec0cfafc3b3bc0e77e0dbb5a70c5f (upstream
Copyright (C) 2013-2018 Sylvie Boldo, GNU LGPL version 3 or later; this
transliteration is distributed under the same terms). SqrtSqr.v states the
upstream lemma and the trimming.
-/
import Exemplars.Compute
import Exemplars.Choices
import FloatSpec.src.Core.FLX

namespace Exemplars.SqrtSqr

open FloatSpec.Core FloatSpec.Core.Defs FloatSpec.Calc
open Exemplars.Compute (mult sqrt)
open Exemplars.Choices (rnd_N)

instance : ValidRadix 5 := ⟨by decide⟩

def prec : Int := 3
def r (c : Int → Bool) := rnd_N c

/-- Tie predicates: even (NE), `Zle_bool 0` (NA), always true, always false. -/
def tie : Int → Int → Bool
  | 0 => fun m => !(RoundNE.Zeven m)
  | 1 => Zaux.Zle_bool 0
  | 2 => fun _ => true
  | _ => fun _ => false

def row (k1 k2 mx : Int) : List Int :=
  let c1 := tie k1
  let c2 := tie k2
  let x : FlocqFloat 5 := ⟨mx, 0⟩
  let y := mult 5 (FLX.FLX_exp prec) (r c2) x x
  let z := sqrt 5 (FLX.FLX_exp prec) (r c1) y
  [k1, k2, mx, y.Fnum, y.Fexp, z.Fnum, z.Fexp, (Operations.Fminus 5 z x).Fnum]

end Exemplars.SqrtSqr

open Exemplars.SqrtSqr in
#eval IO.println (toString
  ([0, 1, 2, 3].flatMap fun k1 => [0, 1, 2, 3].flatMap fun k2 =>
    (List.range 125).map fun n => row k1 k2 n))
