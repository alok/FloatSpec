/-
FloatSpec exemplar lane: CodyWaite, the Lean counterpart of CodyWaite.v.

Provenance: transliterates the trimmed Flocq examples/Cody_Waite.v at commit
7aab8f55bceec0cfafc3b3bc0e77e0dbb5a70c5f (upstream Copyright (C) 2014-2018
Guillaume Melquiond, GNU LGPL version 3 or later; this transliteration is
distributed under the same terms). CodyWaite.v lists what was kept and what
was replaced; this file follows it definition by definition.
-/
import Exemplars.Compute
import Exemplars.Choices
import FloatSpec.src.Core.FLT
import FloatSpec.src.Core.FIX

namespace Exemplars.CodyWaite

open FloatSpec.Core FloatSpec.Core.Defs FloatSpec.Calc
open Exemplars.Compute (plus mult)
open Exemplars.Choices (rnd_NE rnd_DN)

instance : Prec_gt_0 53 := ⟨by decide⟩

abbrev F := FlocqFloat 2

/-- Flocq's `FLT_exp (-1074) 53`; the FloatSpec port takes `prec` first. -/
def fexp := FLT.FLT_exp 53 (-1074)
def add (x y : F) := plus 2 fexp rnd_NE x y
def sub (x y : F) := plus 2 fexp rnd_NE x (Operations.Fopp 2 y)
def mul (x y : F) := mult 2 fexp rnd_NE x y
def div (x y : F) := Compute.div 2 fexp rnd_NE x y
def nearbyint (x : F) := plus 2 (FIX.FIX_exp 0) rnd_NE x ⟨0, 0⟩

def Log2h : F := ⟨3048493539143, -42⟩
def Log2l : F := ⟨544487923021427, -93⟩
def InvLog2 : F := ⟨3248660424278399, -51⟩

def p0 : F := ⟨1, -2⟩
def p1 : F := ⟨4002712888408905, -59⟩
def p2 : F := ⟨1218985200072455, -66⟩
def q0 : F := ⟨1, -1⟩
def q1 : F := ⟨8006155947364787, -57⟩
def q2 : F := ⟨4573527866750985, -63⟩

def cw_exp_trace (x : F) : List Int :=
  let k := nearbyint (mul x InvLog2)
  let t := sub (sub x (mul k Log2h)) (mul k Log2l)
  let t2 := mul t t
  let p := add p0 (mul t2 (add p1 (mul t2 p2)))
  let q := add q0 (mul t2 (add q1 (mul t2 q2)))
  let r := add (div (mul t p) (sub q (mul t p))) ⟨1, -1⟩
  let fk := (plus 2 (FIX.FIX_exp 0) rnd_DN k ⟨0, 0⟩).Fnum
  let y := Operations.Fmult 2 ⟨1, fk + 1⟩ r
  [x.Fnum, x.Fexp, k.Fnum, k.Fexp, t.Fnum, t.Fexp, p.Fnum, p.Fexp,
   q.Fnum, q.Fexp, r.Fnum, r.Fexp, fk, y.Fnum, y.Fexp]

def inputs : List (Int × Int) :=
  [(1, 0), (-1, 0), (1, -1), (7094959, -14), (-24, 0), (6004799503160661, -52),
   (5764607523034235, -60), (0, 0), (1, -1074), (-746, 0), (710, 0),
   (6243314768165359, -43), (-6554261109157969, -43), (-3115560397004393, -42),
   (355, -10), (-355, -10), (6243314768165359, -54), (6032057205060441, -1049),
   (-6490371073168535, -109), (3022314549036573, -78), (5, -1), (-5, -1),
   (100, 0), (-100, 0), (884279719003555, -48), (6243314768165359, -53),
   (6243314763971055, -46), (-1829096123485945, -44), (-7461829, -13), (1000, 0)]

end Exemplars.CodyWaite

open Exemplars.CodyWaite in
#eval IO.println (toString (inputs.map fun (m, e) => cw_exp_trace ⟨m, e⟩))
