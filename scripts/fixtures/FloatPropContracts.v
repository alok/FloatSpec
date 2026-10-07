From Stdlib Require Import ZArith Reals Lra.
From Flocq Require Import Core.Zaux Core.Raux Core.Defs Core.Digits Core.Float_prop.
Open Scope R_scope.

(* Float_prop.v. After the section closes, every law takes the radix explicitly. *)
Definition compare : forall (beta : radix) e m1 m2,
  Rcompare (F2R (Float beta m1 e)) (F2R (Float beta m2 e)) = Z.compare m1 m2 := Rcompare_F2R.
Definition le_inv : forall (beta : radix) e m1 m2,
  F2R (Float beta m1 e) <= F2R (Float beta m2 e) -> (m1 <= m2)%Z := le_F2R.
Definition le : forall (beta : radix) m1 m2 e,
  (m1 <= m2)%Z -> F2R (Float beta m1 e) <= F2R (Float beta m2 e) := F2R_le.
Definition lt_inv : forall (beta : radix) e m1 m2,
  F2R (Float beta m1 e) < F2R (Float beta m2 e) -> (m1 < m2)%Z := lt_F2R.
Definition lt : forall (beta : radix) e m1 m2,
  (m1 < m2)%Z -> F2R (Float beta m1 e) < F2R (Float beta m2 e) := F2R_lt.
Definition eq : forall (beta : radix) e m1 m2,
  m1 = m2 -> F2R (Float beta m1 e) = F2R (Float beta m2 e) := F2R_eq.
Definition eq_inv : forall (beta : radix) e m1 m2,
  F2R (Float beta m1 e) = F2R (Float beta m2 e) -> m1 = m2 := eq_F2R.
Definition abs' : forall (beta : radix) m e,
  F2R (Float beta (Z.abs m) e) = Rabs (F2R (Float beta m e)) := F2R_Zabs.
Definition opp : forall (beta : radix) m e,
  F2R (Float beta (Z.opp m) e) = Ropp (F2R (Float beta m e)) := F2R_Zopp.
Definition cond_opp : forall (beta : radix) b m e,
  F2R (Float beta (cond_Zopp b m) e) = cond_Ropp b (F2R (Float beta m e)) := F2R_cond_Zopp.
Definition zero : forall (beta : radix) e, F2R (Float beta 0 e) = 0 := F2R_0.
Definition eq_0 : forall (beta : radix) m e, F2R (Float beta m e) = 0 -> m = Z0 := eq_0_F2R.
Definition ge_0 : forall (beta : radix) m e, 0 <= F2R (Float beta m e) -> (0 <= m)%Z := ge_0_F2R.
Definition le_0 : forall (beta : radix) m e, F2R (Float beta m e) <= 0 -> (m <= 0)%Z := le_0_F2R.
Definition gt_0 : forall (beta : radix) m e, 0 < F2R (Float beta m e) -> (0 < m)%Z := gt_0_F2R.
Definition lt_0 : forall (beta : radix) m e, F2R (Float beta m e) < 0 -> (m < 0)%Z := lt_0_F2R.
Definition of_ge_0 : forall (beta : radix) (f : float beta), (0 <= Fnum f)%Z -> 0 <= F2R f :=
  F2R_ge_0.
Definition of_le_0 : forall (beta : radix) (f : float beta), (Fnum f <= 0)%Z -> F2R f <= 0 :=
  F2R_le_0.
Definition of_gt_0 : forall (beta : radix) (f : float beta), (0 < Fnum f)%Z -> 0 < F2R f :=
  F2R_gt_0.
Definition of_lt_0 : forall (beta : radix) (f : float beta), (Fnum f < 0)%Z -> F2R f < 0 :=
  F2R_lt_0.
Definition of_neq_0 : forall (beta : radix) (f : float beta), (Fnum f <> 0)%Z -> F2R f <> 0 :=
  F2R_neq_0.
Definition fnum_ge_0 : forall (beta : radix) (f : float beta), 0 <= F2R f -> (0 <= Fnum f)%Z :=
  Fnum_ge_0.
Definition fnum_le_0 : forall (beta : radix) (f : float beta), F2R f <= 0 -> (Fnum f <= 0)%Z :=
  Fnum_le_0.
Definition of_bpow : forall (beta : radix) e, F2R (Float beta 1 e) = bpow beta e := F2R_bpow.
Definition bpow_le : forall (beta : radix) m e,
  (0 < m)%Z -> bpow beta e <= F2R (Float beta m e) := bpow_le_F2R.
Definition p1_le_bpow : forall (beta : radix) m e1 e2, (0 < m)%Z ->
  F2R (Float beta m e1) < bpow beta e2 -> F2R (Float beta (m + 1) e1) <= bpow beta e2 :=
  F2R_p1_le_bpow.
Definition bpow_le_m1 : forall (beta : radix) m e1 e2, (1 < m)%Z ->
  bpow beta e2 < F2R (Float beta m e1) -> bpow beta e2 <= F2R (Float beta (m - 1) e1) :=
  bpow_le_F2R_m1.
Definition lt_bpow : forall (beta : radix) (f : float beta) e',
  (Z.abs (Fnum f) < Zpower beta (e' - Fexp f))%Z -> Rabs (F2R f) < bpow beta e' := F2R_lt_bpow.
Definition change_exp : forall (beta : radix) e' m e, (e' <= e)%Z ->
  F2R (Float beta m e) = F2R (Float beta (m * Zpower beta (e - e')) e') := F2R_change_exp.
Definition prec_normalize : forall (beta : radix) m e e' p,
  (Z.abs m < Zpower beta p)%Z -> bpow beta (e' - 1) <= Rabs (F2R (Float beta m e)) ->
  F2R (Float beta m e) = F2R (Float beta (m * Zpower beta (e - e' + p)) (e' - p)) :=
  F2R_prec_normalize.
Definition mag_bounds : forall (beta : radix) x m e, (0 < m)%Z ->
  F2R (Float beta m e) <= x < F2R (Float beta (m + 1) e) ->
  mag beta x = mag beta (F2R (Float beta m e)) :> Z := mag_F2R_bounds.
Definition mag' : forall (beta : radix) m e, m <> Z0 ->
  (mag beta (F2R (Float beta m e)) = mag beta (IZR m) + e :> Z)%Z := mag_F2R.
Definition digits_mag : forall (beta : radix) n, n <> Z0 -> Zdigits beta n = mag beta (IZR n) :=
  Zdigits_mag.
Definition mag_digits : forall (beta : radix) m e, m <> Z0 ->
  (mag beta (F2R (Float beta m e)) = Zdigits beta m + e :> Z)%Z := mag_F2R_Zdigits.
Definition mag_bounds_digits : forall (beta : radix) x m e, (0 < m)%Z ->
  F2R (Float beta m e) <= x < F2R (Float beta (m + 1) e) ->
  mag beta x = (Zdigits beta m + e)%Z :> Z := mag_F2R_bounds_Zdigits.
Definition distribution_pos : forall (beta : radix) m1 e1 m2 e2, (0 < m1)%Z ->
  F2R (Float beta m1 e1) < F2R (Float beta m2 e2) < F2R (Float beta (m1 + 1) e1) ->
  (e2 < e1)%Z /\ (e1 + mag beta (IZR m1) = e2 + mag beta (IZR m2))%Z := float_distribution_pos.

Print Assumptions compare.
Print Assumptions prec_normalize.
Print Assumptions distribution_pos.

Definition radix10 := Build_radix 10 eq_refl.

(* 34 * 10^-1 = 3.4 changes exponent to 340 * 10^-2; it has two digits. *)
Example values :
  F2R (Float radix10 34 (-1)) = F2R (Float radix10 340 (-2)) /\ Zdigits radix10 34 = 2%Z.
Proof.
split; [| reflexivity].
rewrite (F2R_change_exp radix10 (-2) 34 (-1)) by easy. reflexivity.
Qed.

(* F2R_prec_normalize needs its lower bound: at 5 * 10^0 the shifted mantissa
   5 * Zpower 10 (-2) is zero. *)
Example prec_normalize_needs_bound : ~ (forall m e e' p,
  (Z.abs m < Zpower radix10 p)%Z ->
  F2R (Float radix10 m e) = F2R (Float radix10 (m * Zpower radix10 (e - e' + p)) (e' - p))).
Proof.
intros H. specialize (H 5%Z 0%Z 3%Z 1%Z ltac:(easy)).
unfold F2R in H. simpl in H. lra.
Qed.

Print Assumptions prec_normalize_needs_bound.
