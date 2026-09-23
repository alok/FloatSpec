/-
Lean transliteration of Flocq examples/Compute.v, the shared prelude of the
FloatSpec exemplar lane (see README.md in this directory).

Upstream: https://gitlab.inria.fr/flocq/flocq, examples/Compute.v at commit
7aab8f55bceec0cfafc3b3bc0e77e0dbb5a70c5f (the FloatSpec pin).
Copyright (C) 2015-2018 Sylvie Boldo, Guillaume Melquiond. Upstream is
distributed under the GNU Lesser General Public License, version 3 or later;
this transliteration is distributed under the same terms.

Kept: the four executable definitions `plus`, `mult`, `sqrt`, `div`, with
the same parameters (radix, exponent function, sign-magnitude choice).
Dropped: the correctness theorems and their section hypotheses. They stay in
the verbatim Rocq copy `Compute.v`, which the exemplar harness compiles as-is.

Every operation below calls the FloatSpec port of the Flocq function that
Compute.v calls (`Fplus`, `Fmult`, `Fabs`, `Fdiv`, `Fsqrt`, `truncate`,
`cond_Zopp`, `Zlt_bool`, `Zeq_bool`); there is no other mantissa arithmetic.
-/
import FloatSpec.src.Calc.Div
import FloatSpec.src.Calc.Sqrt
import FloatSpec.src.Calc.Round
import FloatSpec.src.Calc.Operations

namespace Exemplars.Compute

open FloatSpec.Core FloatSpec.Core.Defs FloatSpec.Calc FloatSpec.Calc.Bracket

variable (beta : Int) [ValidRadix beta] (fexp : Int → Int)
  (choice : Bool → Int → Location → Int)

/-- Compute.v `plus`: round the exact sum through `truncate` and `choice`. -/
def plus (x y : FlocqFloat beta) : FlocqFloat beta :=
  let f := Operations.Fplus beta x y
  let s := Zaux.Zlt_bool f.Fnum 0
  let (m', e', l) := Round.truncate beta fexp (|f.Fnum|, f.Fexp, Location.loc_Exact)
  ⟨Zaux.cond_Zopp s (choice s m' l), e'⟩

/-- Compute.v `mult`. -/
def mult (x y : FlocqFloat beta) : FlocqFloat beta :=
  let f := Operations.Fmult beta x y
  let s := Zaux.Zlt_bool f.Fnum 0
  let (m', e', l) := Round.truncate beta fexp (|f.Fnum|, f.Fexp, Location.loc_Exact)
  ⟨Zaux.cond_Zopp s (choice s m' l), e'⟩

/-- Compute.v `sqrt`; nonpositive inputs give `Float beta 0 0`. -/
def sqrt (x : FlocqFloat beta) : FlocqFloat beta :=
  if Zaux.Zlt_bool 0 x.Fnum then
    let (m', e', l) := Round.truncate beta fexp (Sqrt.Fsqrt beta fexp x)
    ⟨choice false m' l, e'⟩
  else ⟨0, 0⟩

/-- Compute.v `div`; a zero dividend gives `Float beta 0 0`. -/
def div (x y : FlocqFloat beta) : FlocqFloat beta :=
  if Zaux.Zeq_bool x.Fnum 0 then ⟨0, 0⟩
  else
    let (m, e, l) := Round.truncate beta fexp
      (Div.Fdiv beta fexp (Operations.Fabs beta x) (Operations.Fabs beta y))
    let s := xor (Zaux.Zlt_bool x.Fnum 0) (Zaux.Zlt_bool y.Fnum 0)
    ⟨Zaux.cond_Zopp s (choice s m l), e⟩

end Exemplars.Compute
