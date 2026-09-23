(* FloatSpec exemplar lane: Average.

   Provenance: trimmed from Flocq examples/Average.v at commit
   7aab8f55bceec0cfafc3b3bc0e77e0dbb5a70c5f (the FloatSpec pin).

   This example is part of the Flocq formalization of floating-point
   arithmetic in Coq: https://flocq.gitlabpages.inria.fr/
   Copyright (C) 2014-2018 Sylvie Boldo
   This library is free software; you can redistribute it and/or
   modify it under the terms of the GNU Lesser General Public
   License as published by the Free Software Foundation; either
   version 3 of the License, or (at your option) any later version.
   This library is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
   COPYING file for more details.

   Kept: the definitions avg_naive, avg_sum_half, avg_half_sub and average,
   with the same structure and case split, in radix 2 with FLT_exp emin prec
   and round_flt = round radix2 (FLT_exp emin prec) ZnearestE.
   Replaced:
   - round_flt (u + v) becomes Compute.v plus (NE), and round_flt (u - v)
     is plus u (Fopp v);
   - round_flt (u / 2) is Compute.v div by Float radix2 2 0 (div_correct);
   - average's real tests Rle_bool 0 x and Rle_bool (Rabs x) (Rabs y)
     become integer tests on Fnum x and on Fnum (Fminus (Fabs x) (Fabs y)).
     The two lemmas below prove that these tests are equal.
   Dropped: all proofs of the properties. The Python oracle checks them.
   Formats: (emin, prec) = (-6, 3) and (-4, 4), each with all pairs from 17
   format values that reach the subnormal range.
   Row: [emin; prec; mx; ex; my; ey; avg_naive m e; avg_sum_half m e;
         avg_half_sub m e; average m e].
   Oracle: the lemmas below, with each premise checked per row:
   - avg_naive_correct;
   - avg_sum_half_correct, needing 2^(emin + 2 prec + 1) <= |x|;
   - avg_half_sub_correct, for same-sign x and y;
   - average_symmetry, average_symmetry_Ropp, average_same_sign_1/2,
     average_correct (|av - a| <= 3/2 ulp a), average_between,
     average_zero and average_no_underflow.
   Rows with |x| below the avg_sum_half_correct bound are positive controls:
   there the naive sum of halves does lose the average. *)
From Stdlib Require Import ZArith Reals List.
From Flocq Require Import Core Bracket Round Operations Div Sqrt.
From Exemplars Require Import Compute Choices.
Import ListNotations.
Open Scope Z_scope.

Lemma Rle_bool_0_F2R (x : float radix2) : Rle_bool 0 (F2R x) = Z.leb 0 (Fnum x).
Proof.
  case Z.leb_spec; intros H.
  - apply Rle_bool_true. now apply F2R_ge_0.
  - apply Rle_bool_false. now apply F2R_lt_0.
Qed.

Lemma Rle_bool_abs_F2R (x y : float radix2) :
  Rle_bool (Rabs (F2R x)) (Rabs (F2R y)) = Z.leb (Fnum (Fminus (Fabs x) (Fabs y))) 0.
Proof.
  rewrite <- 2!F2R_abs.
  generalize (F2R_minus (Fabs x) (Fabs y)); intros Hd.
  case Z.leb_spec; intros H.
  - apply Rle_bool_true. apply Rminus_le. rewrite <- Hd. now apply F2R_le_0.
  - apply Rle_bool_false. apply Rminus_gt. rewrite <- Hd. now apply F2R_gt_0.
Qed.

Section Average.

Variable emin prec : Z.

Let fexp := FLT_exp emin prec.
Let two := Float radix2 2 0.

Definition avg_naive (x y : float radix2) :=
  Compute.div radix2 fexp rnd_NE (plus radix2 fexp rnd_NE x y) two.

Definition avg_sum_half (x y : float radix2) :=
  plus radix2 fexp rnd_NE (Compute.div radix2 fexp rnd_NE x two)
    (Compute.div radix2 fexp rnd_NE y two).

Definition avg_half_sub (x y : float radix2) :=
  plus radix2 fexp rnd_NE x
    (Compute.div radix2 fexp rnd_NE (plus radix2 fexp rnd_NE y (Fopp x)) two).

Definition average (x y : float radix2) :=
  let samesign := match Z.leb 0 (Fnum x), Z.leb 0 (Fnum y) with
    | true, true => true
    | false, false => true
    | _, _ => false
    end in
  if samesign then
    match Z.leb (Fnum (Fminus (Fabs x) (Fabs y))) 0 with
    | true => avg_half_sub x y
    | false => avg_half_sub y x
    end
  else avg_naive x y.

End Average.

Definition row (emin prec : Z) (p : (Z * Z) * (Z * Z)) : list Z :=
  let '((mx, ex), (my, ey)) := p in
  let x := Float radix2 mx ex in
  let y := Float radix2 my ey in
  let n := avg_naive emin prec x y in
  let s := avg_sum_half emin prec x y in
  let h := avg_half_sub emin prec x y in
  let a := average emin prec x y in
  [emin; prec; mx; ex; my; ey; Fnum n; Fexp n; Fnum s; Fexp s;
   Fnum h; Fexp h; Fnum a; Fexp a].

Definition signed (l : list (Z * Z)) : list (Z * Z) :=
  (0, 0) :: l ++ map (fun p => (- fst p, snd p)) l.

Definition values (prec : Z) : list (Z * Z) :=
  if Z.eqb prec 3 then
    signed [(1, -6); (3, -6); (4, -6); (7, -6); (5, -5); (7, -1); (6, 2); (7, 3)]
  else
    signed [(1, -4); (5, -4); (8, -4); (15, -4); (9, -3); (13, 0); (11, 2); (15, 5)].

Definition grid (emin prec : Z) : list (list Z) :=
  flat_map (fun x => map (fun y => row emin prec (x, y)) (values prec)) (values prec).

Eval vm_compute in grid (-6) 3 ++ grid (-4) 4.
