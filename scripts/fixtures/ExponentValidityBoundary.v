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
  ~ (forall x y : R, 0 <= x -> x <= y ->
      ulp radix2 zigzag x <= ulp radix2 zigzag y).
Proof.
  intro claimed. specialize (claimed (1/2) 1 ltac:(lra) ltac:(lra)).
  rewrite zigzag_ulp_one, zigzag_ulp_half in claimed. lra.
Qed.

Print Assumptions valid_format_can_have_decreasing_ulp.

Lemma zigzag_magnitude_seven_quarters : (mag radix2 (7/4) : Z) = 1%Z.
Proof.
  apply mag_unique. change (1 <= Rabs (7/4) < 2).
  rewrite Rabs_right by lra. lra.
Qed.
Print Assumptions zigzag_magnitude_seven_quarters.

Lemma zigzag_magnitude_three_quarters : (mag radix2 (3/4) : Z) = 0%Z.
Proof.
  apply mag_unique. change (/2 <= Rabs (3/4) < 1).
  rewrite Rabs_right by lra. lra.
Qed.
Print Assumptions zigzag_magnitude_three_quarters.

Lemma zigzag_seven_quarters_representable : generic_format radix2 zigzag (7/4).
Proof.
  unfold generic_format, scaled_mantissa, cexp, F2R.
  rewrite zigzag_magnitude_seven_quarters. unfold zigzag. simpl.
  replace (Z.pow_pos 2 2) with 4%Z by reflexivity.
  replace (7/4 * 4) with (IZR 7) by (simpl; field).
  rewrite Ztrunc_IZR. simpl. field.
Qed.
Print Assumptions zigzag_seven_quarters_representable.

Lemma zigzag_three_quarters_not_representable : ~ generic_format radix2 zigzag (3/4).
Proof.
  unfold generic_format, scaled_mantissa, cexp, F2R.
  rewrite zigzag_magnitude_three_quarters. unfold zigzag. simpl.
  replace (Z.pow_pos 2 1) with 2%Z by reflexivity.
  rewrite Ztrunc_floor by lra.
  assert (Hfloor : Zfloor (3/4 * 2) = 1%Z).
  { apply Zfloor_imp. simpl. lra. }
  rewrite Hfloor. simpl. lra.
Qed.
Print Assumptions zigzag_three_quarters_not_representable.

Theorem truncation_remainder_needs_monotone_exponents :
  ~ (forall x y : R, generic_format radix2 zigzag x -> generic_format radix2 zigzag y ->
       generic_format radix2 zigzag (x - IZR (Ztrunc (x/y)) * y)).
Proof.
  intro claimed.
  assert (Hone : generic_format radix2 zigzag 1).
  { change (generic_format radix2 zigzag (bpow radix2 0)).
    apply zigzag_contains_powers. }
  assert (Htrunc : Ztrunc ((7/4)/1) = 1%Z).
  { rewrite Ztrunc_floor by lra. apply Zfloor_imp. simpl. lra. }
  specialize (claimed (7/4) 1 zigzag_seven_quarters_representable Hone).
  rewrite Htrunc in claimed. simpl in claimed.
  replace (7/4 - 1*1) with (3/4) in claimed by field.
  exact (zigzag_three_quarters_not_representable claimed).
Qed.
Print Assumptions truncation_remainder_needs_monotone_exponents.
