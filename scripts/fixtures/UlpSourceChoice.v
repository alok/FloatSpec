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

Section SourcePremises.
Variable beta : radix.
Variable fexp : Z -> Z.
Variable x : R.
Example succ_opp_unrestricted : succ beta fexp (-x) = -pred beta fexp x.
Proof. apply succ_opp. Qed.
Example pred_opp_unrestricted : pred beta fexp (-x) = -succ beta fexp x.
Proof. apply pred_opp. Qed.
Example ulp_opp_unrestricted : ulp beta fexp (-x) = ulp beta fexp x.
Proof. apply ulp_opp. Qed.
Example ulp_abs_unrestricted : ulp beta fexp (Rabs x) = ulp beta fexp x.
Proof. apply ulp_abs. Qed.
Example succ_eq_pos_unrestricted (Hx : 0 <= x) :
  succ beta fexp x = x + ulp beta fexp x.
Proof. apply succ_eq_pos. exact Hx. Qed.
Example ulp_ge_0_unrestricted : 0 <= ulp beta fexp x.
Proof. apply ulp_ge_0. Qed.
Example pred_eq_pos_unrestricted (Hx : 0 <= x) :
  pred beta fexp x = pred_pos beta fexp x.
Proof. apply pred_eq_pos. exact Hx. Qed.
Example ulp_le_id_unrestricted (Hx : 0 < x) (Hf : generic_format beta fexp x) :
  ulp beta fexp x <= x.
Proof. apply ulp_le_id; assumption. Qed.
Example ulp_le_abs_unrestricted (Hx : x <> 0) (Hf : generic_format beta fexp x) :
  ulp beta fexp x <= Rabs x.
Proof. apply ulp_le_abs; assumption. Qed.
Example ulp_canonical_unrestricted (m e : Z) (Hm : m <> 0%Z)
  (Hc : canonical beta fexp (Float beta m e)) :
  ulp beta fexp (F2R (Float beta m e)) = bpow beta e.
Proof. apply ulp_canonical; assumption. Qed.
Example ulp_bpow_unrestricted (e : Z) :
  ulp beta fexp (bpow beta e) = bpow beta (fexp (e + 1)%Z).
Proof. apply ulp_bpow. Qed.
Example pred_bpow_unrestricted (e : Z) :
  pred beta fexp (bpow beta e) = bpow beta e - bpow beta (fexp e).
Proof. apply pred_bpow. Qed.
Example generic_abs_unrestricted (Hf : generic_format beta fexp x) :
  generic_format beta fexp (Rabs x).
Proof. apply generic_format_abs. exact Hf. Qed.
Example generic_abs_inv_unrestricted (Hf : generic_format beta fexp (Rabs x)) :
  generic_format beta fexp x.
Proof. apply generic_format_abs_inv. exact Hf. Qed.
End SourcePremises.

Example witness_exponents_agree (fexp : Z -> Z) (Hvalid : Valid_exp fexp)
  (n m : Z) (Hn : (n <= fexp n)%Z) (Hm : (m <= fexp m)%Z) : fexp n = fexp m.
Proof. exact (@fexp_negligible_exp_eq fexp Hvalid n m Hn Hm). Qed.
