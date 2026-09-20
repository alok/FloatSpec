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
