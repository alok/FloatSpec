From Stdlib Require Import ZArith Reals Lra.
From Flocq Require Import Core.Raux.
Open Scope R_scope.

Example rcompare_body : forall x y, Rcompare x y =
  match total_order_T x y with
  | inleft (left _) => Lt | inleft (right _) => Eq | inright _ => Gt
  end := fun x y => eq_refl.
Example rle_bool_body : forall x y,
  Rle_bool x y = match Rcompare x y with Gt => false | _ => true end := fun x y => eq_refl.
Example rlt_bool_body : forall x y,
  Rlt_bool x y = match Rcompare x y with Lt => true | _ => false end := fun x y => eq_refl.
Example req_bool_body : forall x y,
  Req_bool x y = match Rcompare x y with Eq => true | _ => false end := fun x y => eq_refl.

Definition cmp_lt_ctor : forall x y, x < y -> Rcompare_prop x y Lt := Rcompare_Lt_.
Definition cmp_eq_ctor : forall x y, x = y -> Rcompare_prop x y Eq := Rcompare_Eq_.
Definition cmp_gt_ctor : forall x y, y < x -> Rcompare_prop x y Gt := Rcompare_Gt_.
Definition le_true_ctor : forall x y, x <= y -> Rle_bool_prop x y true := Rle_bool_true_.
Definition le_false_ctor : forall x y, y < x -> Rle_bool_prop x y false := Rle_bool_false_.
Definition lt_true_ctor : forall x y, x < y -> Rlt_bool_prop x y true := Rlt_bool_true_.
Definition lt_false_ctor : forall x y, y <= x -> Rlt_bool_prop x y false := Rlt_bool_false_.
Definition eq_true_ctor : forall x y, x = y -> Req_bool_prop x y true := Req_bool_true_.
Definition eq_false_ctor : forall x y, x <> y -> Req_bool_prop x y false := Req_bool_false_.

Definition cmp_prop_ind : forall x y (P : comparison -> Prop),
  (x < y -> P Lt) -> (x = y -> P Eq) -> (y < x -> P Gt) ->
  forall c, Rcompare_prop x y c -> P c := Rcompare_prop_ind.
Definition le_prop_ind : forall x y (P : bool -> Prop),
  (x <= y -> P true) -> (y < x -> P false) -> forall b, Rle_bool_prop x y b -> P b :=
  Rle_bool_prop_ind.
Definition lt_prop_ind : forall x y (P : bool -> Prop),
  (x < y -> P true) -> (y <= x -> P false) -> forall b, Rlt_bool_prop x y b -> P b :=
  Rlt_bool_prop_ind.
Definition eq_prop_ind : forall x y (P : bool -> Prop),
  (x = y -> P true) -> (x <> y -> P false) -> forall b, Req_bool_prop x y b -> P b :=
  Req_bool_prop_ind.
(* The SProp schemes, which Lean has no counterpart for. *)
Definition cmp_prop_sind : forall x y (P : comparison -> SProp),
  (x < y -> P Lt) -> (x = y -> P Eq) -> (y < x -> P Gt) ->
  forall c, Rcompare_prop x y c -> P c := Rcompare_prop_sind.
Definition le_prop_sind : forall x y (P : bool -> SProp),
  (x <= y -> P true) -> (y < x -> P false) -> forall b, Rle_bool_prop x y b -> P b :=
  Rle_bool_prop_sind.
Definition lt_prop_sind : forall x y (P : bool -> SProp),
  (x < y -> P true) -> (y <= x -> P false) -> forall b, Rlt_bool_prop x y b -> P b :=
  Rlt_bool_prop_sind.
Definition eq_prop_sind : forall x y (P : bool -> SProp),
  (x = y -> P true) -> (x <> y -> P false) -> forall b, Req_bool_prop x y b -> P b :=
  Req_bool_prop_sind.

Definition cmp_spec : forall x y, Rcompare_prop x y (Rcompare x y) := Rcompare_spec.
Definition cmp_lt : forall x y, x < y -> Rcompare x y = Lt := Rcompare_Lt.
Definition cmp_lt_inv : forall x y, Rcompare x y = Lt -> x < y := Rcompare_Lt_inv.
Definition cmp_not_lt : forall x y, y <= x -> Rcompare x y <> Lt := Rcompare_not_Lt.
Definition cmp_not_lt_inv : forall x y, Rcompare x y <> Lt -> y <= x := Rcompare_not_Lt_inv.
Definition cmp_eq : forall x y, x = y -> Rcompare x y = Eq := Rcompare_Eq.
Definition cmp_eq_inv : forall x y, Rcompare x y = Eq -> x = y := Rcompare_Eq_inv.
Definition cmp_gt : forall x y, y < x -> Rcompare x y = Gt := Rcompare_Gt.
Definition cmp_gt_inv : forall x y, Rcompare x y = Gt -> y < x := Rcompare_Gt_inv.
Definition cmp_not_gt : forall x y, x <= y -> Rcompare x y <> Gt := Rcompare_not_Gt.
Definition cmp_not_gt_inv : forall x y, Rcompare x y <> Gt -> x <= y := Rcompare_not_Gt_inv.
Definition cmp_izr : forall x y, Rcompare (IZR x) (IZR y) = Z.compare x y := Rcompare_IZR.
Definition cmp_sym : forall x y, Rcompare x y = CompOpp (Rcompare y x) := Rcompare_sym.
Definition cmp_opp : forall x y, Rcompare (- x) (- y) = Rcompare y x := Rcompare_opp.
Definition cmp_plus_r : forall z x y, Rcompare (x + z) (y + z) = Rcompare x y := Rcompare_plus_r.
Definition cmp_plus_l : forall z x y, Rcompare (z + x) (z + y) = Rcompare x y := Rcompare_plus_l.
Definition cmp_mult_r : forall z x y, 0 < z -> Rcompare (x * z) (y * z) = Rcompare x y :=
  Rcompare_mult_r.
Definition cmp_mult_l : forall z x y, 0 < z -> Rcompare (z * x) (z * y) = Rcompare x y :=
  Rcompare_mult_l.
Definition cmp_middle : forall x d u, Rcompare (x - d) (u - x) = Rcompare x ((d + u) / 2) :=
  Rcompare_middle.
Definition cmp_half_l : forall x y, Rcompare (x / 2) y = Rcompare x (2 * y) := Rcompare_half_l.
Definition cmp_half_r : forall x y, Rcompare x (y / 2) = Rcompare (2 * x) y := Rcompare_half_r.
Definition cmp_sqr : forall x y, Rcompare (x * x) (y * y) = Rcompare (Rabs x) (Rabs y) :=
  Rcompare_sqr.
Definition min_compare : forall x y,
  Rmin x y = match Rcompare x y with Lt => x | Eq => x | Gt => y end := Rmin_compare.

Definition le_spec : forall x y, Rle_bool_prop x y (Rle_bool x y) := Rle_bool_spec.
Definition le_true : forall x y, x <= y -> Rle_bool x y = true := Rle_bool_true.
Definition le_false : forall x y, y < x -> Rle_bool x y = false := Rle_bool_false.
Definition lt_spec : forall x y, Rlt_bool_prop x y (Rlt_bool x y) := Rlt_bool_spec.
Definition negb_lt : forall x y, negb (Rle_bool x y) = Rlt_bool y x := negb_Rlt_bool.
Definition negb_le : forall x y, negb (Rlt_bool x y) = Rle_bool y x := negb_Rle_bool.
Definition lt_true : forall x y, x < y -> Rlt_bool x y = true := Rlt_bool_true.
Definition lt_false : forall x y, y <= x -> Rlt_bool x y = false := Rlt_bool_false.
Definition lt_opp : forall x y, Rlt_bool (- x) (- y) = Rlt_bool y x := Rlt_bool_opp.
Definition eq_spec : forall x y, Req_bool_prop x y (Req_bool x y) := Req_bool_spec.
Definition eq_true : forall x y, x = y -> Req_bool x y = true := Req_bool_true.
Definition eq_false : forall x y, x <> y -> Req_bool x y = false := Req_bool_false.

Print Assumptions cmp_izr.
Print Assumptions min_compare.

Example le_graph_false_is_strict : ~ Rle_bool_prop 0 0 false.
Proof. intro H. inversion H. lra. Qed.
Example lt_graph_true_is_strict : ~ Rlt_bool_prop 0 0 true.
Proof. intro H. inversion H. lra. Qed.
Example mult_r_needs_pos : ~ forall z x y, Rcompare (x * z) (y * z) = Rcompare x y.
Proof.
intro H. specialize (H (-1) 0 1).
rewrite Rcompare_Gt in H by lra. rewrite Rcompare_Lt in H by lra. discriminate H.
Qed.
Example sym_needs_swap : ~ forall x y, Rcompare x y = Rcompare y x.
Proof.
intro H. specialize (H 0 1).
rewrite Rcompare_Lt in H by lra. rewrite Rcompare_Gt in H by lra. discriminate H.
Qed.
Print Assumptions mult_r_needs_pos.
