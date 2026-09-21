From Stdlib Require Import Reals ZArith Lra Lia.
From Flocq Require Import Pff.Pff.
Open Scope Z_scope.

Check (Pff.Fzero : Z -> Pff.float).
Check (Pff.is_Fzero : Pff.float -> Prop).
Check (Pff.Fmult : Pff.float -> Pff.float -> Pff.float).
Check (Pff.FzeroisReallyZero : forall radix exponent : Z,
  Pff.FtoR radix (Pff.Fzero exponent) = 0%R).
Check (Pff.is_Fzero_rep1 : forall (radix : Z) (x : Pff.float),
  Pff.is_Fzero x -> Pff.FtoR radix x = 0%R).
Check (Pff.is_Fzero_rep2 : forall radix : Z, 1 < radix -> forall x : Pff.float,
  Pff.FtoR radix x = 0%R -> Pff.is_Fzero x).
Check (Pff.Fmult_correct : forall radix : Z, 0 < radix -> forall x y : Pff.float,
  Pff.FtoR radix (Pff.Fmult x y) = (Pff.FtoR radix x * Pff.FtoR radix y)%R).

Check (Pff.Fopp_correct : forall (radix : Z) (x : Pff.float),
  Pff.FtoR radix (Pff.Fopp x) = (- Pff.FtoR radix x)%R).
Check (Pff.Fopp_Fopp : forall x : Pff.float, Pff.Fopp (Pff.Fopp x) = x).
Check (Pff.Fabs_correct : forall radix : Z, 0 < radix -> forall x : Pff.float,
  Pff.FtoR radix (Pff.Fabs x) = Rabs (Pff.FtoR radix x)).
Check (Pff.Fabs_Fzero : forall x : Pff.float,
  ~ Pff.is_Fzero x -> ~ Pff.is_Fzero (Pff.Fabs x)).

Check (Pff.Fplus_correct : forall radix : Z, 0 < radix -> forall x y : Pff.float,
  Pff.FtoR radix (Pff.Fplus radix x y) = (Pff.FtoR radix x + Pff.FtoR radix y)%R).
Check (Pff.Fminus_correct : forall radix : Z, 0 < radix -> forall x y : Pff.float,
  Pff.FtoR radix (Pff.Fminus radix x y) = (Pff.FtoR radix x - Pff.FtoR radix y)%R).

Example radix_one_addition : forall x y : Pff.float,
  Pff.FtoR 1 (Pff.Fplus 1 x y) = (Pff.FtoR 1 x + Pff.FtoR 1 y)%R.
Proof. apply Pff.Fplus_correct. lia. Qed.
Example radix_one_subtraction : forall x y : Pff.float,
  Pff.FtoR 1 (Pff.Fminus 1 x y) = (Pff.FtoR 1 x - Pff.FtoR 1 y)%R.
Proof. apply Pff.Fminus_correct. lia. Qed.

Example zero_retains_exponent : Pff.Fzero (-7) = Pff.Float 0 (-7).
Proof. reflexivity. Qed.
Example multiplication_fields :
  Pff.Fmult (Pff.Float (-3) (-7)) (Pff.Float 5 9) = Pff.Float (-15) 2.
Proof. vm_compute. reflexivity. Qed.
Example radix_one_is_allowed : forall x y : Pff.float,
  Pff.FtoR 1 (Pff.Fmult x y) = (Pff.FtoR 1 x * Pff.FtoR 1 y)%R.
Proof. apply Pff.Fmult_correct. lia. Qed.

Example zero_radix_is_not_a_multiplication_model :
  Pff.FtoR 0 (Pff.Fmult (Pff.Float 1 1) (Pff.Float 1 (-1))) <>
  (Pff.FtoR 0 (Pff.Float 1 1) * Pff.FtoR 0 (Pff.Float 1 (-1)))%R.
Proof. unfold Pff.FtoR, Pff.Fmult; simpl. lra. Qed.

Example negative_radix_is_not_an_absolute_value_model :
  Pff.FtoR (-2) (Pff.Fabs (Pff.Float 1 1)) <>
  Rabs (Pff.FtoR (-2) (Pff.Float 1 1)).
Proof.
  unfold Pff.FtoR, Pff.Fabs; simpl. rewrite Rabs_left by lra. lra.
Qed.

Print Assumptions negative_radix_is_not_an_absolute_value_model.
Print Assumptions Pff.Fopp_correct.
Print Assumptions Pff.Fopp_Fopp.
Print Assumptions Pff.Fabs_correct.
Print Assumptions Pff.Fabs_Fzero.

Example zero_radix_is_not_an_addition_model :
  Pff.FtoR 0 (Pff.Fplus 0 (Pff.Float 1 0) (Pff.Float 0 (-1))) <>
  (Pff.FtoR 0 (Pff.Float 1 0) + Pff.FtoR 0 (Pff.Float 0 (-1)))%R.
Proof. unfold Pff.FtoR, Pff.Fplus; simpl. lra. Qed.

Example zero_radix_is_not_a_subtraction_model :
  Pff.FtoR 0 (Pff.Fminus 0 (Pff.Float 1 0) (Pff.Float 0 (-1))) <>
  (Pff.FtoR 0 (Pff.Float 1 0) - Pff.FtoR 0 (Pff.Float 0 (-1)))%R.
Proof. unfold Pff.FtoR, Pff.Fminus, Pff.Fplus, Pff.Fopp; simpl. lra. Qed.

Print Assumptions zero_radix_is_not_an_addition_model.
Print Assumptions zero_radix_is_not_a_subtraction_model.
Print Assumptions Pff.Fplus_correct.
Print Assumptions Pff.Fminus_correct.
