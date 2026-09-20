From Stdlib Require Import Reals ZArith Lra Lia.
Require Import Flocq.Core.Core Flocq.Prop.Div_sqrt_error.
Open Scope R_scope.

Definition positive_remainder_contract :
  forall (beta : radix) (fexp : Z -> Z), Valid_exp fexp -> Monotone_exp fexp ->
    forall rnd : R -> Z, Valid_rnd rnd -> forall x y : R,
      generic_format beta fexp x -> generic_format beta fexp y -> 0 <= x -> 0 < y ->
      ((0 < x / y < /2)%R -> rnd (x / y) = 0%Z) ->
      generic_format beta fexp (x - IZR (rnd (x / y)) * y) := @format_REM_aux.

Definition remainder_contract :
  forall (beta : radix) (fexp : Z -> Z), Valid_exp fexp -> Monotone_exp fexp ->
    forall rnd : R -> Z, Valid_rnd rnd -> forall x y : R,
      (Rabs (x / y) < /2 -> rnd (x / y) = 0%Z) ->
      generic_format beta fexp x -> generic_format beta fexp y ->
      generic_format beta fexp (x - IZR (rnd (x / y)) * y) := @format_REM.

Definition truncation_contract :
  forall (beta : radix) (fexp : Z -> Z), Valid_exp fexp -> Monotone_exp fexp ->
    forall x y : R, generic_format beta fexp x -> generic_format beta fexp y ->
      generic_format beta fexp (x - IZR (Ztrunc (x / y)) * y) := @format_REM_ZR.

Definition nearest_contract :
  forall (beta : radix) (fexp : Z -> Z), Valid_exp fexp -> Monotone_exp fexp ->
    forall (choice : Z -> bool) (x y : R),
      generic_format beta fexp x -> generic_format beta fexp y ->
      generic_format beta fexp (x - IZR (Znearest choice (x / y)) * y) := @format_REM_N.

Print Assumptions positive_remainder_contract.
Print Assumptions remainder_contract.
Print Assumptions truncation_contract.
Print Assumptions nearest_contract.

Lemma magnitude_minus_seven : (mag radix2 (-7) : Z) = 3%Z.
Proof.
  apply mag_unique.
  change (4 <= Rabs (-7) < 8)%R.
  rewrite Rabs_left by lra. lra.
Qed.
Print Assumptions magnitude_minus_seven.

Lemma minus_seven_not_format : ~ generic_format radix2 (FLX_exp 2) (-7).
Proof.
  unfold generic_format, scaled_mantissa, cexp, FLX_exp, F2R.
  rewrite magnitude_minus_seven. simpl.
  replace (Z.pow_pos 2 1) with 2%Z by reflexivity.
  rewrite Ztrunc_ceil by lra.
  assert (Hceil : Zceil (-7 * /2) = (-3)%Z).
  { apply Zceil_imp. simpl. lra. }
  rewrite Hceil. simpl. lra.
Qed.
Print Assumptions minus_seven_not_format.

Theorem ceiling_does_not_preserve_remainder_format :
  ~ (forall x y : R, generic_format radix2 (FLX_exp 2) x ->
    generic_format radix2 (FLX_exp 2) y ->
    generic_format radix2 (FLX_exp 2) (x - IZR (Zceil (x / y)) * y)).
Proof.
  intro H.
  assert (Hx : generic_format radix2 (FLX_exp 2) 1).
  { change (generic_format radix2 (FLX_exp 2) (bpow radix2 0)).
    apply generic_format_bpow. unfold FLX_exp. lia. }
  assert (Hy : generic_format radix2 (FLX_exp 2) 8).
  { change (generic_format radix2 (FLX_exp 2) (bpow radix2 3)).
    apply generic_format_bpow. unfold FLX_exp. lia. }
  assert (Hceil : Zceil (1 / 8) = 1%Z) by (apply Zceil_imp; simpl; lra).
  specialize (H 1 8 Hx Hy). rewrite Hceil in H. simpl in H.
  replace (1 - 1 * 8)%R with (-7)%R in H by ring.
  exact (minus_seven_not_format H).
Qed.
Print Assumptions ceiling_does_not_preserve_remainder_format.
