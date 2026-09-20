From Stdlib Require Import Reals ZArith Lia Lra.
Require Import Flocq.Core.Core.
Open Scope Z_scope.

Definition zigzag (exponent : Z) : Z :=
  if Z.eqb (exponent mod 2) 0 then exponent - 1 else exponent - 3.

#[local] Instance zigzag_valid : Valid_exp zigzag.
Proof.
  intros exponent. split.
  - intros _. unfold zigzag. destruct (Z.eqb ((exponent + 1) mod 2) 0); lia.
  - unfold zigzag at 1. destruct (Z.eqb (exponent mod 2) 0); lia.
Qed.

Print Assumptions zigzag_valid.

Example zigzag_not_monotone : ~ Monotone_exp zigzag.
Proof.
  intros H. specialize (H 0 1 ltac:(lia)). change (-1 <= -2)%Z in H. lia.
Qed.

Print Assumptions zigzag_not_monotone.

Open Scope R_scope.

Example zigzag_contains_powers (exponent : Z) :
  generic_format radix2 zigzag (bpow radix2 exponent).
Proof.
  apply generic_format_bpow. unfold zigzag.
  destruct (Z.eqb ((exponent + 1) mod 2) 0); lia.
Qed.

Print Assumptions zigzag_contains_powers.

Example zigzag_ulp_half : ulp radix2 zigzag (1 / 2) = 1 / 2.
Proof.
  replace (1 / 2) with (bpow radix2 (-1)) by
    (unfold Rdiv; rewrite Rmult_1_l; reflexivity).
  rewrite ulp_bpow. reflexivity.
Qed.

Print Assumptions zigzag_ulp_half.

Example zigzag_ulp_one : ulp radix2 zigzag 1 = 1 / 4.
Proof.
  replace 1 with (bpow radix2 0) at 1 by reflexivity.
  rewrite ulp_bpow. change (/ 4 = 1 / 4). unfold Rdiv. ring.
Qed.

Print Assumptions zigzag_ulp_one.

Example valid_format_can_have_decreasing_ulp :
  0 <= 1 / 2 /\ 1 / 2 <= 1 /\
  ulp radix2 zigzag 1 < ulp radix2 zigzag (1 / 2).
Proof. rewrite zigzag_ulp_one, zigzag_ulp_half. repeat split; lra. Qed.

Print Assumptions valid_format_can_have_decreasing_ulp.
