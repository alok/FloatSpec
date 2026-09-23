(* FloatSpec exemplar lane: DivisionU16.

   Provenance: trimmed from Flocq examples/Division_u16.v at commit
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

   Kept verbatim: the register format FLT_exp (-65597) 64 and the four steps
   of div_u16, which is Itanium's 16-bit unsigned division by reciprocal
   approximation.
   Replaced:
   - `fma x y z = round radix2 register_fmt rndNE (x * y + z)` becomes
     Compute.plus (NE) of the exact Operations.Fmult x y and z. fnma is
     handled the same way. plus_correct proves them equal.
   - Upstream, `Axiom frcpa : R -> R` is only specified by `frcpa_spec`
     (11-bit format and relative error <= 4433 * 2^-21). Here it becomes
     four executable models, Compute.div of 1 by b:
     - model 0: nearest-even at 11 bits;
     - model 1: toward -inf at 11 bits;
     - model 2: toward +inf at 11 bits;
     - model 3: nearest-even at 8 bits. This is a positive control: it can
       break frcpa_spec, and then div_u16 can return a wrong quotient.
   - `Zfloor q1` becomes Compute.plus at FIX_exp 0 with the DN choice.
   Dropped: the proofs and the Gappa import, which only the proofs use.
   Row: [a; b; model; y0 m e; q0 m e; e0 m e; q1 m e; div_u16].
   Oracle: div_u16_spec, div_u16 a b = a / b when 1 <= a, b <= 65535 and
   the model's y0 satisfies frcpa_spec. The oracle checks frcpa_spec itself,
   from the observed y0, for every row. *)
From Stdlib Require Import ZArith List.
From Flocq Require Import Core Bracket Round Operations Div Sqrt.
From Exemplars Require Import Compute Choices.
Import ListNotations.
Open Scope Z_scope.

Definition register_fmt := FLT_exp (-65597) 64.
Definition fma (x y z : float radix2) := plus radix2 register_fmt rnd_NE (Fmult x y) z.
Definition fnma (x y z : float radix2) := plus radix2 register_fmt rnd_NE z (Fopp (Fmult x y)).

Definition frcpa (model b : Z) : float radix2 :=
  let one := Float radix2 1 0 in
  let fb := Float radix2 b 0 in
  match model with
  | 0 => Compute.div radix2 (FLT_exp (-65597) 11) rnd_NE one fb
  | 1 => Compute.div radix2 (FLT_exp (-65597) 11) rnd_DN one fb
  | 2 => Compute.div radix2 (FLT_exp (-65597) 11) rnd_UP one fb
  | _ => Compute.div radix2 (FLT_exp (-65597) 8) rnd_NE one fb
  end.

Definition div_u16_trace (model a b : Z) : list Z :=
  let y0 := frcpa model b in
  let q0 := fma (Float radix2 a 0) y0 (Float radix2 0 0) in
  let e0 := fnma (Float radix2 b 0) y0 (Float radix2 131073 (-17)) in
  let q1 := fma e0 q0 q0 in
  let quotient := Fnum (plus radix2 (FIX_exp 0) rnd_DN q1 (Float radix2 0 0)) in
  [a; b; model; Fnum y0; Fexp y0; Fnum q0; Fexp q0; Fnum e0; Fexp e0;
   Fnum q1; Fexp q1; quotient].

Definition pairs : list (Z * Z) :=
  [(1, 1); (65535, 1); (1, 65535); (65535, 65535); (65534, 65535); (65535, 65534);
   (32768, 3); (65535, 3); (40000, 7); (65535, 255); (65535, 256); (65535, 257);
   (12345, 678); (60001, 59999); (2, 3); (65533, 21845);
   (3, 3); (13, 13); (26, 13); (65533, 13); (255, 255); (7, 7);
   (59254, 47151); (44077, 47653); (23667, 6706); (59951, 33170); (505, 33527);
   (4945, 36199); (42267, 47654); (34038, 2545); (4280, 61523); (47952, 45027);
   (39671, 235); (43920, 213); (55873, 31); (33762, 111); (9975, 274); (34189, 56)].

Eval vm_compute in
  flat_map (fun model => map (fun p => div_u16_trace model (fst p) (snd p)) pairs)
    [0; 1; 2; 3].
