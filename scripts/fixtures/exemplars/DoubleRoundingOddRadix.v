(* FloatSpec exemplar lane: DoubleRoundingOddRadix.

   Provenance: trimmed from Flocq examples/Double_rounding_odd_radix.v at
   commit 7aab8f55bceec0cfafc3b3bc0e77e0dbb5a70c5f (the FloatSpec pin),
   with round_round_eq from src/Prop/Double_rounding.v at the same commit.

   This example is part of the Flocq formalization of floating-point
   arithmetic in Coq: https://flocq.gitlabpages.inria.fr/
   Copyright (C) 2014-2018 Pierre Roux
   This library is free software; you can redistribute it and/or
   modify it under the terms of the GNU Lesser General Public
   License as published by the Free Software Foundation; either
   version 3 of the License, or (at your option) any later version.
   This library is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
   COPYING file for more details.

   Upstream proves, for an odd radix and any tie-breaking choices,
     round_round_eq beta fexp1 fexp2 choice1 choice2 (x op y) :
       round fexp1 (Znearest choice1) (round fexp2 (Znearest choice2) (x op y))
       = round fexp1 (Znearest choice1) (x op y)
   for op in mult/plus/minus
   (round_round_{mult,plus,minus}_beta_odd_{FLX,FLT,FTZ}), for sqrt x, and
   for x / y with ZnearestA only (round_round_div_rna_{FLX,FLT,FTZ}). The
   premises are:
   - FLX: prec <= prec';
   - FLT: additionally emin' <= emin;
   - FTZ: emin' + prec' <= emin + prec;
   - x and y belong to the outer format.
   Kept: the theorem statements, as the rows' meaning. Their executable
   content is below.
   Replaced: every real `round fexp (Znearest c) (x op y)` becomes Compute.v's
   plus/mult/div/sqrt with the choice Choices.rnd_N c. The outer rounding of
   an already-rounded float is Compute.plus with 0 (plus_correct).
   Dropped: the proofs.
   Grid:
   - outer: FLX 2, FLT (-4) 2, FTZ (-4) 2;
   - inner: FLX 3, FLT (-6) 3, FTZ (-5) 3;
   - radices: 3, 5 and 7, plus radix 2 as a positive control, since the
     theorem needs an odd radix;
   - tie predicate pairs: (even, even), (away, even), (even, away) and
     (false, true) for mult/plus/minus/sqrt, and (away, away) for div.
   Row: [beta; family; op; k1; k2; mx; ex; my; ey; inner m e; outer m e;
         direct m e; Fnum (outer - direct)].
   op codes: 0 mult, 1 plus, 2 minus, 3 sqrt, 4 div. *)
From Stdlib Require Import ZArith List.
From Flocq Require Import Core FTZ Bracket Round Operations Div Sqrt.
From Exemplars Require Import Compute Choices.
Import ListNotations.
Open Scope Z_scope.

Definition radix3 := Build_radix 3 (eq_refl true).
Definition radix5 := Build_radix 5 (eq_refl true).
Definition radix7 := Build_radix 7 (eq_refl true).

(* (outer fexp1, inner fexp2) *)
Definition formats (family : Z) : (Z -> Z) * (Z -> Z) :=
  match family with
  | 0 => (FLX_exp 2, FLX_exp 3)
  | 1 => (FLT_exp (-4) 2, FLT_exp (-6) 3)
  | _ => (FTZ_exp (-4) 2, FTZ_exp (-5) 3)
  end.

Definition tie (k : Z) : Z -> bool :=
  match k with
  | 0 => fun m => negb (Z.even m)
  | 1 => Z.leb 0
  | 2 => fun _ => true
  | _ => fun _ => false
  end.

Definition op_round (beta : radix) (fexp : Z -> Z) (c : Z -> bool) (op : Z)
    (x y : float beta) : float beta :=
  match op with
  | 0 => mult beta fexp (rnd_N c) x y
  | 1 => plus beta fexp (rnd_N c) x y
  | 2 => plus beta fexp (rnd_N c) x (Fopp y)
  | 3 => sqrt beta fexp (rnd_N c) x
  | _ => div beta fexp (rnd_N c) x y
  end.

Definition row (beta : radix) (family op k1 k2 : Z) (p : Z * Z * Z * Z) : list Z :=
  let '(mx, ex, my, ey) := p in
  let x := Float beta mx ex in
  let y := Float beta my ey in
  let '(fexp1, fexp2) := formats family in
  let inner := op_round beta fexp2 (tie k2) op x y in
  let outer := plus beta fexp1 (rnd_N (tie k1)) inner (Float beta 0 0) in
  let direct := op_round beta fexp1 (tie k1) op x y in
  [radix_val beta; family; op; k1; k2; mx; ex; my; ey;
   Fnum inner; Fexp inner; Fnum outer; Fexp outer; Fnum direct; Fexp direct;
   Fnum (Fminus outer direct)].

Definition inputs (b : Z) : list (Z * Z * Z * Z) :=
  match b with
  | 3 => [(8, -4, -8, -2); (-6, 0, 5, -3); (-5, 1, -3, -4); (7, -1, 8, -1);
          (-5, -1, 4, -1); (4, 1, 3, -4); (3, -1, 4, -2); (3, -2, 8, 1);
          (-5, -1, 8, -4); (3, 0, 8, 1); (-3, -1, 3, 1); (4, 1, 4, -1)]
  | 5 => [(-18, -4, 13, 1); (8, -2, -22, -2); (-10, -2, 9, 1); (19, -2, 11, -1);
          (9, -1, -18, -2); (-6, -3, 12, -4); (-7, -1, -12, -1); (-15, -2, -17, 0);
          (15, 1, -5, 0); (-23, -2, -14, 1); (19, -2, 21, -3); (6, 1, 12, -1)]
  | 7 => [(-45, 0, -30, 1); (12, -1, 45, 1); (34, -1, -17, 1); (24, 0, 25, -1);
          (-11, 1, -25, -3); (29, 0, 25, -1); (45, 0, -20, 0); (11, -3, -25, 1);
          (-26, -1, 40, 1); (-29, -2, 7, -2); (30, -1, 44, -3); (8, 1, 24, -1)]
  | _ => [(3, 1, -3, -2); (3, -1, -3, -2); (3, -4, -3, -4); (3, -1, 2, 1);
          (-3, -2, -3, 0); (3, -3, -2, -2); (3, -4, -3, 1); (2, -1, -2, -1);
          (2, 0, 3, -1); (2, -4, -3, -4); (2, -4, 3, -2); (-2, 1, -3, -2)]
  end.

Definition choice_pairs (op : Z) : list (Z * Z) :=
  if Z.eqb op 4 then [(1, 1)] else [(0, 0); (1, 0); (0, 1); (3, 2)].

Definition rows (beta : radix) : list (list Z) :=
  flat_map (fun family => flat_map (fun op =>
    flat_map (fun k => map (row beta family op (fst k) (snd k)) (inputs (radix_val beta)))
      (choice_pairs op)) [0; 1; 2; 3; 4]) [0; 1; 2].

Eval vm_compute in rows radix3 ++ rows radix5 ++ rows radix7 ++ rows radix2.
