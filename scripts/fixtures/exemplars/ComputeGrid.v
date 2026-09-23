(* FloatSpec exemplar lane: ComputeGrid.

   Provenance: drives the verbatim Flocq examples/Compute.v (pinned
   7aab8f55, LGPL-3.0-or-later; see Compute.v for its header). Compute.v has
   no executable content of its own, so this driver is new, FloatSpec-authored
   text, not upstream text.

   It runs Compute.v's plus/mult/div/sqrt over:
   - radices 2, 3 and 10;
   - FLX_exp 3, FLT_exp (-3) 3, FIX_exp (-1) and FTZ_exp (-3) 3;
   - the choices DN, UP, ZR, NE and NA from Choices.v;
   - sixteen input pairs.
   The loop order is radix, then format, then choice, then input.
   Row: [beta; format; choice; mx; ex; my; ey; plus m e; mult m e; div m e;
         sqrt m e].
   Oracle (Python, exact rationals): Compute.v's plus/mult/div/sqrt_correct,
   i.e. each result equals round beta fexp rnd of the exact operation. div
   requires F2R y <> 0. *)
From Stdlib Require Import ZArith List.
From Flocq Require Import Core FTZ Bracket Round Operations Div Sqrt.
From Exemplars Require Import Compute Choices.
Import ListNotations.
Open Scope Z_scope.

Definition radix3 := Build_radix 3 (eq_refl true).
Definition radix10 := Build_radix 10 (eq_refl true).

Definition fexp_of (k : Z) : Z -> Z :=
  match k with
  | 0 => FLX_exp 3
  | 1 => FLT_exp (-3) 3
  | 2 => FIX_exp (-1)
  | _ => FTZ_exp (-3) 3
  end.

Definition choice_of (k : Z) : bool -> Z -> location -> Z :=
  match k with
  | 0 => rnd_DN
  | 1 => rnd_UP
  | 2 => rnd_ZR
  | 3 => rnd_NE
  | _ => rnd_NA
  end.

Definition inputs : list (Z * Z * Z * Z) :=
  [(0, 0, 1, 0); (1, 0, 1, 0); (1, 0, 3, 0); (-7, 0, 2, 0);
   (23, -1, -5, 2); (-122, -2, 7, -1); (999, -3, 13, 0); (1, -5, 1, -5);
   (5, 2, -1, -4); (27, 0, 8, 1); (-1, 0, -1, 0); (4, -6, 3, -7);
   (100, 0, 0, 0); (-26, 1, 9, -3); (15, -2, 15, -2); (2, 4, -2, -4)].

Definition row (beta : radix) (fk ck : Z) (p : Z * Z * Z * Z) : list Z :=
  let '(mx, ex, my, ey) := p in
  let x := Float beta mx ex in
  let y := Float beta my ey in
  let fexp := fexp_of fk in
  let ch := choice_of ck in
  let a := plus beta fexp ch x y in
  let m := mult beta fexp ch x y in
  let d := div beta fexp ch x y in
  let r := sqrt beta fexp ch x in
  [radix_val beta; fk; ck; mx; ex; my; ey; Fnum a; Fexp a; Fnum m; Fexp m;
   Fnum d; Fexp d; Fnum r; Fexp r].

Definition grid (beta : radix) : list (list Z) :=
  flat_map (fun fk =>
    flat_map (fun ck => map (row beta fk ck) inputs) [0; 1; 2; 3; 4])
    [0; 1; 2; 3].

Eval vm_compute in grid radix2 ++ grid radix3 ++ grid radix10.
