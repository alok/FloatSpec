(* FloatSpec exemplar lane: SqrtSqr.

   Provenance: trimmed from Flocq examples/Sqrt_sqr.v, Section Sec6, at
   commit 7aab8f55bceec0cfafc3b3bc0e77e0dbb5a70c5f (the FloatSpec pin).

   This example is part of the Flocq formalization of floating-point
   arithmetic in Coq: https://flocq.gitlabpages.inria.fr/
   Copyright (C) 2013-2018 Sylvie Boldo
   This library is free software; you can redistribute it and/or
   modify it under the terms of the GNU Lesser General Public
   License as published by the Free Software Foundation; either
   version 3 of the License, or (at your option) any later version.
   This library is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
   COPYING file for more details.

   Upstream lemma (Sec6):
     sqrt_sqr_special_case : let beta := 5 in let prec := 3 in
       forall c1 c2 mx, (0 <= mx < 125) ->
       round beta (FLX_exp prec) (Znearest c1)
         (sqrt (round beta (FLX_exp prec) (Znearest c2) (x * x))) = x.
   Its proof runs `vm_compute` on
     f mx := Fminus (sqrt beta (FLX_exp prec) (r c1)
                       (mult beta (FLX_exp prec) (r c2) x x)) x
   for all 125 mantissas, with Compute.v's sqrt and mult (upstream imports
   Compute.v as ComputeMore).
   Kept verbatim: beta, prec, the choice r, which is Choices.rnd_N, and f.
   Replaced: the proof's `vm_compute` on a Boolean fold over abstract c1 and
   c2 becomes an `Eval` over four concrete tie predicates: even (NE), Zle_bool
   0 (NA), always true and always false. Every mantissa and every
   intermediate is printed.
   Row: [c1; c2; mx; y m e; z m e; Fnum (f mx)].
   Oracle: Fnum (f mx) = 0, and y and z are the exact Znearest roundings of
   x * x and sqrt y. *)
From Stdlib Require Import ZArith List.
From Flocq Require Import Core Bracket Round Operations Div Sqrt.
From Exemplars Require Import Compute Choices.
Import ListNotations.
Open Scope Z_scope.

Definition beta := Build_radix 5 (eq_refl true).
Definition prec := 3%Z.
Definition r c := rnd_N c.

Definition tie (k : Z) : Z -> bool :=
  match k with
  | 0 => fun m => negb (Z.even m)
  | 1 => Z.leb 0
  | 2 => fun _ => true
  | _ => fun _ => false
  end.

Definition row (k1 k2 mx : Z) : list Z :=
  let c1 := tie k1 in
  let c2 := tie k2 in
  let x := Float beta mx 0 in
  let y := mult beta (FLX_exp prec) (r c2) x x in
  let z := sqrt beta (FLX_exp prec) (r c1) y in
  [k1; k2; mx; Fnum y; Fexp y; Fnum z; Fexp z; Fnum (Fminus z x)].

Eval vm_compute in
  flat_map (fun k1 => flat_map (fun k2 =>
    map (fun n => row k1 k2 (Z.of_nat n)) (seq 0 125)) [0; 1; 2; 3]) [0; 1; 2; 3].
