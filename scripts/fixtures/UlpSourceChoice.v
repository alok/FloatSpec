From Stdlib Require Import Reals ZArith Lia Lra.
Require Import Flocq.Core.Core.
Open Scope R_scope.

Example negligible_choice_contract (fexp : Z -> Z) :
  negligible_exp fexp =
    match LPO_Z (fun n => (n <= fexp n)%Z) (fun n => Z_le_dec_aux n (fexp n)) with
    | inleft witness => Some (proj1_sig witness)
    | inright _ => None
    end.
Proof. reflexivity. Qed.

Section Bodies.
Variable beta : radix.
Variable fexp : Z -> Z.
Example ulp_body (x : R) : ulp beta fexp x =
  if Req_bool x 0 then
    match negligible_exp fexp with Some n => bpow beta (fexp n) | None => 0 end
  else bpow beta (cexp beta fexp x).
Proof. reflexivity. Qed.
Example pred_pos_body (x : R) : pred_pos beta fexp x =
  if Req_bool x (bpow beta (mag beta x - 1)) then
    x - bpow beta (fexp (mag beta x - 1)) else x - ulp beta fexp x.
Proof. reflexivity. Qed.
Example succ_body (x : R) : succ beta fexp x =
  if Rle_bool 0 x then x + ulp beta fexp x else - pred_pos beta fexp (-x).
Proof. reflexivity. Qed.
Example pred_body (x : R) : pred beta fexp x = - succ beta fexp (-x).
Proof. reflexivity. Qed.
End Bodies.

Example identity_not_valid : ~ Valid_exp (fun exponent : Z => exponent).
Proof.
  intros H. destruct (H 0%Z) as [_ Hsmall].
  destruct (Hsmall ltac:(lia)) as [Himpossible _]. lia.
Qed.

Example invalid_choice_difference :
  (0 <= (fun exponent : Z => exponent) 0)%Z /\
  (1 <= (fun exponent : Z => exponent) 1)%Z /\
  bpow radix2 0 <> bpow radix2 1.
Proof. repeat split; try lia. simpl. lra. Qed.
