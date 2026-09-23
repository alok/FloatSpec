(* FloatSpec exemplar lane: CodyWaite.

   Provenance: trimmed from Flocq examples/Cody_Waite.v at commit
   7aab8f55bceec0cfafc3b3bc0e77e0dbb5a70c5f (the FloatSpec pin).

   This example is part of the Flocq formalization of floating-point
   arithmetic in Coq: https://flocq.gitlabpages.inria.fr/
   Copyright (C) 2014-2018 Guillaume Melquiond
   This library is free software; you can redistribute it and/or
   modify it under the terms of the GNU Lesser General Public
   License as published by the Free Software Foundation; either
   version 3 of the License, or (at your option) any later version.
   This library is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
   COPYING file for more details.

   Kept verbatim: the constants Log2h, Log2l, InvLog2, p0..p2, q0..q2 (as
   mantissa/exponent pairs) and the let-structure of cw_exp.
   Replaced:
   - The real-valued `rnd (x op y)`, with rnd = round radix2
     (FLT_exp (-1074) 53) ZnearestE, becomes Compute.v's float-level
     plus/mult/div with the NE choice. plus_correct, mult_correct and
     div_correct prove the two equal.
   - `nearbyint x = round radix2 (FIX_exp 0) ZnearestE x` becomes
     Compute.plus at FIX_exp 0 with 0 as the second argument.
   - `pow2 (Zfloor k + 1) * r` becomes the exact Operations.Fmult
     (Float radix2 1 (Zfloor k + 1)) r. Zfloor k is Compute.plus at
     FIX_exp 0 with the DN choice.
   Dropped: the proofs and the Gappa and Interval imports, which only the
   proofs use.
   Row: [x m e; k m e; t m e; p m e; q m e; r m e; Zfloor k; cw_exp x m e].
   Oracle: exp_correct, |cw_exp x - exp x| <= 2^-51 exp x for binary64 x in
   [-746, 710], and argument_reduction's |t| <= 355/1024. *)
From Stdlib Require Import ZArith List.
From Flocq Require Import Core Bracket Round Operations Div Sqrt.
From Exemplars Require Import Compute Choices.
Import ListNotations.
Open Scope Z_scope.

Definition fexp := FLT_exp (-1074) 53.
Definition add x y := plus radix2 fexp rnd_NE x y.
Definition sub x y := plus radix2 fexp rnd_NE x (Fopp y).
Definition mul x y := mult radix2 fexp rnd_NE x y.
Definition div x y := Compute.div radix2 fexp rnd_NE x y.
Definition nearbyint x := plus radix2 (FIX_exp 0) rnd_NE x (Float radix2 0 0).

Definition Log2h := Float radix2 3048493539143 (-42).
Definition Log2l := Float radix2 544487923021427 (-93).
Definition InvLog2 := Float radix2 3248660424278399 (-51).

Definition p0 := Float radix2 1 (-2).
Definition p1 := Float radix2 4002712888408905 (-59).
Definition p2 := Float radix2 1218985200072455 (-66).
Definition q0 := Float radix2 1 (-1).
Definition q1 := Float radix2 8006155947364787 (-57).
Definition q2 := Float radix2 4573527866750985 (-63).

Definition cw_exp_trace (x : float radix2) : list Z :=
  let k := nearbyint (mul x InvLog2) in
  let t := sub (sub x (mul k Log2h)) (mul k Log2l) in
  let t2 := mul t t in
  let p := add p0 (mul t2 (add p1 (mul t2 p2))) in
  let q := add q0 (mul t2 (add q1 (mul t2 q2))) in
  let r := add (div (mul t p) (sub q (mul t p))) (Float radix2 1 (-1)) in
  let fk := Fnum (plus radix2 (FIX_exp 0) rnd_DN k (Float radix2 0 0)) in
  let y := Fmult (Float radix2 1 (fk + 1)) r in
  [Fnum x; Fexp x; Fnum k; Fexp k; Fnum t; Fexp t; Fnum p; Fexp p;
   Fnum q; Fexp q; Fnum r; Fexp r; fk; Fnum y; Fexp y].

Definition inputs : list (Z * Z) :=
  [(1, 0); (-1, 0); (1, -1); (7094959, -14); (-24, 0); (6004799503160661, -52);
   (5764607523034235, -60); (0, 0); (1, -1074); (-746, 0); (710, 0);
   (6243314768165359, -43); (-6554261109157969, -43); (-3115560397004393, -42);
   (355, -10); (-355, -10); (6243314768165359, -54); (6032057205060441, -1049);
   (-6490371073168535, -109); (3022314549036573, -78); (5, -1); (-5, -1);
   (100, 0); (-100, 0); (884279719003555, -48); (6243314768165359, -53);
   (6243314763971055, -46); (-1829096123485945, -44); (-7461829, -13); (1000, 0)].

Eval vm_compute in map (fun p => cw_exp_trace (Float radix2 (fst p) (snd p))) inputs.
