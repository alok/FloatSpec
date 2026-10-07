From Stdlib Require Import ZArith Reals Lra Lia.
From Flocq Require Import Core.Zaux Core.Raux.
Open Scope R_scope.

Definition radix10 := Build_radix 10 eq_refl.

(* The record: an exponent and, for nonzero inputs, its two-sided power bound. *)
Example record_fields : forall (r : radix) x (m : mag_prop r x), Z := fun r x m => mag_val r x m.
Example record_bound : forall (r : radix) x (m : mag_prop r x), x <> 0 ->
  bpow r (mag_val r x m - 1) <= Rabs x < bpow r (mag_val r x m).
Proof. intros r x [e He] Hx. exact (He Hx). Qed.

Definition lt_bpow_bpow : forall (r : radix) e1 e2, bpow r (e1 - 1) < bpow r e2 -> (e1 <= e2)%Z :=
  bpow_lt_bpow.
Definition unique_exp : forall (r : radix) x e1 e2,
  bpow r (e1 - 1) <= x < bpow r e1 -> bpow r (e2 - 1) <= x < bpow r e2 -> e1 = e2 := bpow_unique.
Definition unique : forall (r : radix) x e,
  bpow r (e - 1) <= Rabs x < bpow r e -> mag r x = e :> Z := mag_unique.
Definition opp : forall (r : radix) x, mag r (- x) = mag r x :> Z := mag_opp.
Definition abs' : forall (r : radix) x, mag r (Rabs x) = mag r x :> Z := mag_abs.
Definition unique_pos : forall (r : radix) x e,
  bpow r (e - 1) <= x < bpow r e -> mag r x = e :> Z := mag_unique_pos.
Definition le_abs : forall (r : radix) x y, x <> 0 -> Rabs x <= Rabs y -> (mag r x <= mag r y)%Z :=
  mag_le_abs.
Definition le : forall (r : radix) x y, 0 < x -> x <= y -> (mag r x <= mag r y)%Z := mag_le.
Definition lt : forall (r : radix) x y, 0 < y -> (mag r x < mag r y)%Z -> x < y := lt_mag.
Definition of_bpow : forall (r : radix) e, mag r (bpow r e) = (e + 1)%Z :> Z := mag_bpow.
Definition mult_bpow : forall (r : radix) x e, x <> 0 ->
  mag r (x * bpow r e) = (mag r x + e)%Z :> Z := mag_mult_bpow.
Definition le_bpow : forall (r : radix) x e, x <> 0 -> Rabs x < bpow r e -> (mag r x <= e)%Z :=
  mag_le_bpow.
Definition gt_bpow : forall (r : radix) x e, bpow r e <= Rabs x -> (e < mag r x)%Z := mag_gt_bpow.
Definition ge_bpow : forall (r : radix) x e, bpow r (e - 1) <= Rabs x -> (e <= mag r x)%Z :=
  mag_ge_bpow.
Definition upper : forall (r : radix) x, Rabs x < bpow r (mag r x) := bpow_mag_gt.
Definition lower : forall (r : radix) x, x <> 0 -> bpow r (mag r x - 1) <= Rabs x := bpow_mag_le.
Definition le_Zpower : forall (r : radix) m e, m <> Z0 -> (Z.abs m < Zpower r e)%Z ->
  (mag r (IZR m) <= e)%Z := mag_le_Zpower.
Definition gt_Zpower : forall (r : radix) m e, m <> Z0 -> (Zpower r e <= Z.abs m)%Z ->
  (e < mag r (IZR m))%Z := mag_gt_Zpower.
Definition mult : forall (r : radix) x y, x <> 0 -> y <> 0 ->
  (mag r x + mag r y - 1 <= mag r (x * y) <= mag r x + mag r y)%Z := mag_mult.
Definition plus : forall (r : radix) x y, 0 < y -> y <= x ->
  (mag r x <= mag r (x + y) <= mag r x + 1)%Z := mag_plus.
Definition minus : forall (r : radix) x y, 0 < y -> y < x -> (mag r (x - y) <= mag r x)%Z :=
  mag_minus.
Definition minus_lb : forall (r : radix) x y, 0 < x -> 0 < y -> (mag r y <= mag r x - 2)%Z ->
  (mag r x - 1 <= mag r (x - y))%Z := mag_minus_lb.
Definition plus_ge : forall (r : radix) x y, x <> 0 -> (mag r y <= mag r x - 2)%Z ->
  (mag r x - 1 <= mag r (x + y))%Z := mag_plus_ge.
Definition div : forall (r : radix) x y, x <> 0 -> y <> 0 ->
  (mag r x - mag r y <= mag r (x / y) <= mag r x - mag r y + 1)%Z := mag_div.
Definition sqrt' : forall (r : radix) x, 0 < x -> mag r (sqrt x) = Z.div2 (mag r x + 1) :> Z :=
  mag_sqrt.
Definition one : forall r : radix, mag r 1 = 1%Z :> Z := mag_1.

Print Assumptions unique.
Print Assumptions mult.

(* Concrete magnitudes: 1000 has four decimal digits, 7/4 lies in [1, 2). *)
Example concrete : mag radix10 1000 = 4%Z :> Z /\ mag radix2 (7/4) = 1%Z :> Z.
Proof.
split; apply mag_unique; rewrite Rabs_pos_eq by lra; simpl; split; lra.
Qed.

Example le_needs_pos : ~ forall x y, x <= y -> (mag radix10 x <= mag radix10 y)%Z.
Proof.
intro H. specialize (H (-10) 1 ltac:(lra)).
rewrite (mag_unique radix10 (-10) 2) in H
  by (rewrite Rabs_left by lra; simpl; split; lra).
rewrite (mag_unique radix10 1 1) in H by (rewrite Rabs_pos_eq by lra; simpl; split; lra).
lia.
Qed.
Example lt_needs_pos : ~ forall x y, (mag radix10 x < mag radix10 y)%Z -> x < y.
Proof.
intro H. assert (Hlt : 1 < -10).
{ apply H.
  rewrite (mag_unique radix10 (-10) 2) by (rewrite Rabs_left by lra; simpl; split; lra).
  rewrite (mag_unique radix10 1 1) by (rewrite Rabs_pos_eq by lra; simpl; split; lra).
  lia. }
lra.
Qed.
Print Assumptions le_needs_pos.
