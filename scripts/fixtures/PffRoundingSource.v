From Stdlib Require Import Reals ZArith Lia Lra List.
Require Import Flocq.Pff.Pff.
Import ListNotations.
Open Scope R_scope.
Definition bound := Pff.Bound 9%positive 0%N.
Definition row (r : R) := [Pff.RND_Min bound 3 2 r; Pff.RND_Max bound 3 2 r;
  Pff.RND_EvenClosest bound 3 2 r].

Lemma minpos_small (r : R) (hr : r < 3) :
  Pff.RND_Min_Pos bound 3 2 r = Pff.Float (Pff.IRNDD r) 0.
Proof.
  unfold Pff.RND_Min_Pos.
  destruct (Rle_dec (Pff.FtoR 3 (Pff.firstNormalPos 3 bound 2)) r) as [H|H].
  - unfold Pff.FtoR, Pff.firstNormalPos, Pff.nNormMin, bound in H.
    simpl in H. exfalso. lra.
  - change (Pff.Float (Pff.IRNDD (r * 1)) 0 = Pff.Float (Pff.IRNDD r) 0).
    now rewrite Rmult_1_r.
Qed.

Ltac small_floor :=
  match goal with
  | |- context [Pff.IRNDD ?r] =>
      let H := fresh "Hfloor" in
      first [assert (H : Pff.IRNDD r = 0%Z) by
               (apply (Pff.IRNDD_eq bound 2 ltac:(lia)); simpl; lra)
            |assert (H : Pff.IRNDD r = 1%Z) by
               (apply (Pff.IRNDD_eq bound 2 ltac:(lia)); simpl; lra)
            |assert (H : Pff.IRNDD r = 2%Z) by
               (apply (Pff.IRNDD_eq bound 2 ltac:(lia)); simpl; lra)];
      rewrite H
  end.

Ltac rounding_literal :=
  unfold row, Pff.RND_EvenClosest, Pff.RND_Max, Pff.RND_Min, Pff.RND_Max_Pos;
  repeat match goal with
  | |- context [Rle_dec 0 ?r] => destruct (Rle_dec 0 r); try lra
  end;
  repeat match goal with
  | |- context [Pff.RND_Min_Pos bound 3 2 ?r] => rewrite (minpos_small r ltac:(lra))
  end;
  repeat small_floor;
  repeat match goal with
  | |- context [Req_EM_T ?r ?s] => destruct (Req_EM_T r s);
      try solve [unfold Pff.FtoR in *; cbn in *; lra]
  end;
  cbn [Pff.FSucc Pff.pPred Pff.nNormMin Pff.Fopp bound];
  unfold Pff.FtoR; cbn;
  unfold Rabs;
  repeat match goal with
  | |- context [Rcase_abs ?v] => destruct (Rcase_abs v); try lra
  | |- context [Rle_dec ?x ?y] => destruct (Rle_dec x y); try lra
  | |- context [Rle_lt_or_eq_dec ?x ?y ?H] => destruct (Rle_lt_or_eq_dec x y H); try lra
  end;
  repeat match goal with
  | |- context [Pff.OddEvenDec ?z] =>
      let Ho := fresh "Hodd" in let He := fresh "Heven" in
      destruct (Pff.OddEvenDec z) as [Ho|He];
      try solve [apply Z.odd_spec in Ho; discriminate];
      try solve [apply Z.even_spec in He; discriminate]
  end;
  reflexivity.

Example negative_half : row (-3/2) = [Pff.Float (-2) 0; Pff.Float (-1) 0; Pff.Float (-2) 0].
Proof. rounding_literal. Qed.

Example even_lower_half : row (5/2) = [Pff.Float 2 0; Pff.Float 3 0; Pff.Float 2 0].
Proof. rounding_literal. Qed.
Example negative_odd_lower_half : row (-5/2) = [Pff.Float (-3) 0; Pff.Float (-2) 0; Pff.Float (-2) 0].
Proof. rounding_literal. Qed.
Example below_half : row (4/3) = [Pff.Float 1 0; Pff.Float 2 0; Pff.Float 1 0].
Proof. rounding_literal. Qed.
Example above_half : row (5/3) = [Pff.Float 1 0; Pff.Float 2 0; Pff.Float 2 0].
Proof. rounding_literal. Qed.
Example exact_integer : row 2 = [Pff.Float 2 0; Pff.Float 2 0; Pff.Float 2 0].
Proof. rounding_literal. Qed.
Example zero : row 0 = [Pff.Float 0 0; Pff.Float 0 0; Pff.Float 0 0].
Proof. rounding_literal. Qed.

Lemma minpos_zero_precision :
  Pff.RND_Min_Pos (Pff.Bound 1 0) 2 0 2 = Pff.Float 0 2.
Proof.
  assert (Hln : ln 2 <> 0).
  { pose proof (ln_increasing 1 2 ltac:(lra) ltac:(lra)) as H.
    rewrite ln_1 in H. lra. }
  unfold Pff.RND_Min_Pos.
  destruct (Rle_dec (Pff.FtoR 2 (Pff.firstNormalPos 2 (Pff.Bound 1 0) 0)) 2) as [H|H].
  - replace (ln 2 / ln 2) with 1 by (field; exact Hln).
    change (Pff.Float (Pff.IRNDD (2 * powerRZ 2 (- Pff.IRNDD (1 + 1))))
      (Pff.IRNDD (1 + 1)) = Pff.Float 0 2).
    replace (1 + 1) with (IZR 2) by (simpl; ring).
    rewrite (Pff.IRNDD_projector bound 2 ltac:(lia)).
    change (Pff.Float (Pff.IRNDD (2 * / (2 * (2 * 1)))) 2 = Pff.Float 0 2).
    replace (2 * / (2 * (2 * 1))) with (1 / 2) by field.
    assert (Hfloor : Pff.IRNDD (1 / 2) = 0%Z).
    { apply (Pff.IRNDD_eq bound 2 ltac:(lia)); simpl; lra. }
    now rewrite Hfloor.
  - exfalso. apply H. unfold Pff.FtoR, Pff.firstNormalPos, Pff.nNormMin.
    simpl. lra.
Qed.

Example zero_precision :
  [Pff.RND_Min (Pff.Bound 1 0) 2 0 2; Pff.RND_Max (Pff.Bound 1 0) 2 0 2;
   Pff.RND_EvenClosest (Pff.Bound 1 0) 2 0 2] =
  [Pff.Float 0 2; Pff.Float 1 3; Pff.Float 0 2].
Proof.
  unfold Pff.RND_EvenClosest, Pff.RND_Min, Pff.RND_Max, Pff.RND_Max_Pos.
  destruct (Rle_dec 0 2); [|exfalso; lra].
  rewrite minpos_zero_precision.
  destruct (Req_EM_T 2 (Pff.FtoR 2 (Pff.Float 0 2))) as [Heq|Hneq].
  - unfold Pff.FtoR in Heq. cbn in Heq. exfalso. lra.
  - cbn [Pff.FSucc Pff.pPred Pff.nNormMin].
    unfold Pff.FtoR. cbn.
    replace (2 ^ Pos.to_nat 3) with 8 by (simpl; ring).
    replace (2 ^ Pos.to_nat 2) with 4 by (simpl; ring).
    unfold Rabs.
    repeat match goal with
    | |- context [Rcase_abs ?v] => destruct (Rcase_abs v); try lra
    | |- context [Rle_dec ?x ?y] => destruct (Rle_dec x y); try lra
    | |- context [Rle_lt_or_eq_dec ?x ?y ?H] => destruct (Rle_lt_or_eq_dec x y H); try lra
    end.
    reflexivity.
Qed.

Lemma minpos_negative_radix :
  Pff.RND_Min_Pos (Pff.Bound 4 0) (-2)%Z 2 2 = Pff.Float (-4) (-1).
Proof.
  assert (Hln : ln (-2) = 0).
  { unfold ln. destruct (Rlt_dec 0 (-2)); [exfalso; lra | reflexivity]. }
  unfold Pff.RND_Min_Pos.
  destruct (Rle_dec (Pff.FtoR (-2) (Pff.firstNormalPos (-2) (Pff.Bound 4 0) 2)) 2) as [H|H].
  - rewrite Hln. unfold Rdiv. rewrite Rinv_0, Rmult_0_r, Rplus_0_l.
    rewrite (Pff.IRNDD_projector bound 2 ltac:(lia)).
    change (Pff.Float (Pff.IRNDD (2 * ((-2) * 1))) (-1) = Pff.Float (-4) (-1)).
    replace (2 * (-2 * 1)) with (IZR (-4)) by (simpl; ring).
    rewrite (Pff.IRNDD_projector bound 2 ltac:(lia)). reflexivity.
  - exfalso. apply H. unfold Pff.FtoR, Pff.firstNormalPos, Pff.nNormMin.
    simpl. lra.
Qed.

Example negative_radix :
  [Pff.RND_Min (Pff.Bound 4 0) (-2) 2 2; Pff.RND_Max (Pff.Bound 4 0) (-2) 2 2;
   Pff.RND_EvenClosest (Pff.Bound 4 0) (-2) 2 2] =
  [Pff.Float (-4) (-1); Pff.Float (-4) (-1); Pff.Float (-4) (-1)].
Proof.
  unfold Pff.RND_EvenClosest, Pff.RND_Min, Pff.RND_Max, Pff.RND_Max_Pos.
  destruct (Rle_dec 0 2); [|exfalso; lra].
  rewrite minpos_negative_radix.
  assert (Hv : Pff.FtoR (-2) (Pff.Float (-4) (-1)) = 2).
  { unfold Pff.FtoR. change ((-4) * / ((-2) * 1) = 2). field. }
  rewrite Hv.
  destruct (Req_EM_T 2 2); [|contradiction].
  rewrite Hv. rewrite Rminus_diag, Rabs_R0.
  destruct (Rle_dec 0 0) as [H|H]; [|exfalso; lra].
  destruct (Rle_lt_or_eq_dec 0 0 H); [exfalso; lra|].
  cbn [Pff.Fnum]. destruct (Pff.OddEvenDec (-4)); reflexivity.
Qed.

Lemma floor_positive_half : Pff.IRNDD (3/2) = 1%Z.
Proof. apply (Pff.IRNDD_eq bound 2 ltac:(lia)); simpl; lra. Qed.

Example positive_half : row (3/2) = [Pff.Float 1 0; Pff.Float 2 0; Pff.Float 2 0].
Proof.
  unfold row, Pff.RND_EvenClosest, Pff.RND_Max, Pff.RND_Min, Pff.RND_Max_Pos.
  destruct (Rle_dec 0 (3/2)) as [Hr|Hr]; [|exfalso; lra].
  rewrite (minpos_small (3/2) ltac:(lra)), floor_positive_half.
  destruct (Req_EM_T (3/2) (Pff.FtoR 3 (Pff.Float 1 0))) as [Heq|Hneq].
  - unfold Pff.FtoR in Heq. cbn in Heq. exfalso. lra.
  - cbn [Pff.FSucc Pff.pPred Pff.nNormMin bound].
    unfold Pff.FtoR. cbn.
    unfold Rabs.
    repeat match goal with
    | |- context [Rcase_abs ?v] => destruct (Rcase_abs v); try lra
    | |- context [Rle_dec ?x ?y] => destruct (Rle_dec x y); try lra
    | |- context [Rle_lt_or_eq_dec ?x ?y ?H] => destruct (Rle_lt_or_eq_dec x y H); try lra
    end.
    destruct (Pff.OddEvenDec 1) as [Ho|He].
    + reflexivity.
    + apply Z.even_spec in He. discriminate.
Qed.
