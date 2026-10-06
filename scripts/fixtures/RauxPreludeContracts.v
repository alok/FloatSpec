From Stdlib Require Import ZArith Reals Lra.
From Flocq Require Import Core.Raux.
Open Scope R_scope.

Definition le_0_minus : forall x y, x <= y -> 0 <= y - x := Rle_0_minus.
Definition abs_eq_abs : forall x y, Rabs x = Rabs y -> x = y \/ x = - y := Rabs_eq_Rabs.
Definition abs_minus_le : forall x y, 0 <= y -> y <= 2 * x -> Rabs (x - y) <= x := Rabs_minus_le.
Definition abs_eq_0 : forall x, Rabs x = 0 -> x = 0 := Rabs_eq_R0.
Definition mult_lt_compat : forall r1 r2 r3 r4, 0 <= r1 -> 0 <= r3 -> r1 < r2 -> r3 < r4 ->
  r1 * r3 < r2 * r4 := Rmult_lt_compat.
Definition mult_neq_reg_r : forall r1 r2 r3, r2 * r1 <> r3 * r1 -> r2 <> r3 := Rmult_neq_reg_r.
Definition mult_neq_compat_r : forall r1 r2 r3, r1 <> 0 -> r2 <> r3 -> r2 * r1 <> r3 * r1 :=
  Rmult_neq_compat_r.
Definition mult_min_distr_r : forall r r1 r2, 0 <= r -> Rmin r1 r2 * r = Rmin (r1 * r) (r2 * r) :=
  Rmult_min_distr_r.
Definition mult_min_distr_l : forall r r1 r2, 0 <= r -> r * Rmin r1 r2 = Rmin (r * r1) (r * r2) :=
  Rmult_min_distr_l.
Definition min_opp : forall x y, Rmin (- x) (- y) = - Rmax x y := Rmin_opp.
Definition max_opp : forall x y, Rmax (- x) (- y) = - Rmin x y := Rmax_opp.
Definition exp_mono : forall x y, x <= y -> exp x <= exp y := exp_le.
Definition inv_lt : forall x y, 0 < x -> x < y -> / y < / x := Rinv_lt.
Definition inv_le : forall x y, 0 < x -> x <= y -> / y <= / x := Rinv_le.
Definition sqrt_nonneg : forall x, 0 <= sqrt x := sqrt_ge_0.
Definition sqrt_nonpos : forall x, x <= 0 -> sqrt x = 0 := sqrt_neg.
Definition sqr_le_abs : forall x y, x * x <= y * y -> x <= Rabs y := Rsqr_le_abs_0_alt.
Definition abs_le_inv : forall x y, Rabs x <= y -> - y <= x <= y := Rabs_le_inv.
Definition abs_ge : forall x y, y <= - x \/ x <= y -> x <= Rabs y := Rabs_ge.
Definition abs_ge_inv : forall x y, x <= Rabs y -> y <= - x \/ x <= y := Rabs_ge_inv.
Definition abs_lt : forall x y, - y < x < y -> Rabs x < y := Rabs_lt.
Definition abs_lt_inv : forall x y, Rabs x < y -> - y < x < y := Rabs_lt_inv.
Definition abs_gt : forall x y, y < - x \/ x < y -> x < Rabs y := Rabs_gt.
Definition abs_gt_inv : forall x y, x < Rabs y -> y < - x \/ x < y := Rabs_gt_inv.
Definition izr_le_lt : forall m n p, (m <= n < p)%Z -> IZR m <= IZR n < IZR p := IZR_le_lt.
Definition le_lt_izr : forall m n p, IZR m <= IZR n < IZR p -> (m <= n < p)%Z := le_lt_IZR.
Definition neq_izr : forall m n, IZR m <> IZR n -> m <> n := neq_IZR.

Print Assumptions mult_lt_compat.
Print Assumptions inv_lt.
Print Assumptions neq_izr.

Example abs_minus_le_needs_nonneg : ~ forall x y, y <= 2 * x -> Rabs (x - y) <= x.
Proof.
intro H. specialize (H 0 (-1) ltac:(lra)).
rewrite Rabs_pos_eq in H; lra.
Qed.
Example abs_minus_le_needs_upper : ~ forall x y, 0 <= y -> Rabs (x - y) <= x.
Proof.
intro H. specialize (H 0 1 ltac:(lra)).
rewrite Rabs_left in H; lra.
Qed.
Example mult_lt_compat_needs_nonneg :
  ~ forall r1 r2 r3 r4, 0 <= r3 -> r1 < r2 -> r3 < r4 -> r1 * r3 < r2 * r4.
Proof. intro H. specialize (H (-2) (-1) 1 2 ltac:(lra) ltac:(lra) ltac:(lra)). lra. Qed.
Example mult_neq_compat_needs_nonzero : ~ forall r1 r2 r3, r2 <> r3 -> r2 * r1 <> r3 * r1.
Proof. intro H. apply (H 0 0 1 ltac:(lra)). ring. Qed.
Example mult_min_distr_needs_nonneg : ~ forall r r1 r2, Rmin r1 r2 * r = Rmin (r1 * r) (r2 * r).
Proof.
intro H. specialize (H (-1) 0 1).
rewrite Rmin_left in H by lra. rewrite Rmin_right in H by lra. lra.
Qed.
Example inv_lt_needs_pos : ~ forall x y, x < y -> / y < / x.
Proof.
intro H. specialize (H (-1) 1 ltac:(lra)).
rewrite Rinv_1 in H. replace (/ -1) with (-1) in H by field. lra.
Qed.
Print Assumptions abs_minus_le_needs_nonneg.
Print Assumptions inv_lt_needs_pos.
