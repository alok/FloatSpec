/-
FloatSpec exemplar lane: DivisionU16, the Lean counterpart of DivisionU16.v.

Provenance: transliterates the trimmed Flocq examples/Division_u16.v at
commit 7aab8f55bceec0cfafc3b3bc0e77e0dbb5a70c5f (upstream Copyright (C)
2014-2018 Guillaume Melquiond, GNU LGPL version 3 or later; this
transliteration is distributed under the same terms). DivisionU16.v lists
what was kept and replaced, including the frcpa models that stand in for
the function upstream only postulates.
-/
import Exemplars.Compute
import Exemplars.Choices
import FloatSpec.src.Core.FLT
import FloatSpec.src.Core.FIX

namespace Exemplars.DivisionU16

open FloatSpec.Core FloatSpec.Core.Defs FloatSpec.Calc
open Exemplars.Compute (plus)
open Exemplars.Choices (rnd_NE rnd_DN rnd_UP)

instance : Prec_gt_0 64 := ⟨by decide⟩
instance : Prec_gt_0 11 := ⟨by decide⟩
instance : Prec_gt_0 8 := ⟨by decide⟩

abbrev F := FlocqFloat 2

/-- Flocq's `FLT_exp (-65597) 64`; the FloatSpec port takes `prec` first. -/
def register_fmt := FLT.FLT_exp 64 (-65597)
def fma (x y z : F) := plus 2 register_fmt rnd_NE (Operations.Fmult 2 x y) z
def fnma (x y z : F) :=
  plus 2 register_fmt rnd_NE z (Operations.Fopp 2 (Operations.Fmult 2 x y))

def frcpa (model b : Int) : F :=
  let one : F := ⟨1, 0⟩
  let fb : F := ⟨b, 0⟩
  match model with
  | 0 => Compute.div 2 (FLT.FLT_exp 11 (-65597)) rnd_NE one fb
  | 1 => Compute.div 2 (FLT.FLT_exp 11 (-65597)) rnd_DN one fb
  | 2 => Compute.div 2 (FLT.FLT_exp 11 (-65597)) rnd_UP one fb
  | _ => Compute.div 2 (FLT.FLT_exp 8 (-65597)) rnd_NE one fb

def div_u16_trace (model a b : Int) : List Int :=
  let y0 := frcpa model b
  let q0 := fma ⟨a, 0⟩ y0 ⟨0, 0⟩
  let e0 := fnma ⟨b, 0⟩ y0 ⟨131073, -17⟩
  let q1 := fma e0 q0 q0
  let quotient := (plus 2 (FIX.FIX_exp 0) rnd_DN q1 ⟨0, 0⟩).Fnum
  [a, b, model, y0.Fnum, y0.Fexp, q0.Fnum, q0.Fexp, e0.Fnum, e0.Fexp,
   q1.Fnum, q1.Fexp, quotient]

def pairs : List (Int × Int) :=
  [(1, 1), (65535, 1), (1, 65535), (65535, 65535), (65534, 65535), (65535, 65534),
   (32768, 3), (65535, 3), (40000, 7), (65535, 255), (65535, 256), (65535, 257),
   (12345, 678), (60001, 59999), (2, 3), (65533, 21845),
   (3, 3), (13, 13), (26, 13), (65533, 13), (255, 255), (7, 7),
   (59254, 47151), (44077, 47653), (23667, 6706), (59951, 33170), (505, 33527),
   (4945, 36199), (42267, 47654), (34038, 2545), (4280, 61523), (47952, 45027),
   (39671, 235), (43920, 213), (55873, 31), (33762, 111), (9975, 274), (34189, 56)]

end Exemplars.DivisionU16

open Exemplars.DivisionU16 in
#eval IO.println (toString
  ([0, 1, 2, 3].flatMap fun model => pairs.map fun (a, b) => div_u16_trace model a b))
