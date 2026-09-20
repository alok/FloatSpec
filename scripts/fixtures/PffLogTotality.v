From Stdlib Require Import Reals ZArith Lia Lra.
Require Import Flocq.Pff.Pff.
Open Scope R_scope.
Definition b := Pff.Bound 4%positive 0%N.

Lemma ln_neg_two : ln (-2) = 0.
Proof. unfold ln. destruct (Rlt_dec 0 (-2)) as [H | H]; [exfalso; lra | reflexivity]. Qed.

Example source_negative_radix : Pff.RND_Min_Pos b (-2)%Z 2 2 = Pff.Float (-4) (-1).
Proof.
  unfold Pff.RND_Min_Pos.
  destruct (Rle_dec (Pff.FtoR (-2) (Pff.firstNormalPos (-2) b 2)) 2) as [H | H].
  - rewrite ln_neg_two. unfold Rdiv. rewrite Rinv_0, Rmult_0_r.
    rewrite Rplus_0_l.
    rewrite (Pff.IRNDD_projector b 2 ltac:(lia)).
    change (Pff.Float (Pff.IRNDD (2 * ((-2) * 1))) (-1) = Pff.Float (-4) (-1)).
    replace (2 * (-2 * 1)) with (IZR (-4)) by (simpl; ring).
    rewrite (Pff.IRNDD_projector b 2 ltac:(lia)). reflexivity.
  - exfalso. apply H.
    unfold Pff.FtoR, Pff.firstNormalPos, Pff.nNormMin, b.
    simpl.
    lra.
Qed.

Example source_negative_input : Pff.RND_Min_Pos b (-2)%Z 2 (-2) = Pff.Float 4 (-1).
Proof.
  unfold Pff.RND_Min_Pos.
  destruct (Rle_dec (Pff.FtoR (-2) (Pff.firstNormalPos (-2) b 2)) (-2)) as [H | H].
  - rewrite ln_neg_two. unfold Rdiv. rewrite Rinv_0, Rmult_0_r, Rplus_0_l.
    rewrite (Pff.IRNDD_projector b 2 ltac:(lia)).
    change (Pff.Float (Pff.IRNDD ((-2) * ((-2) * 1))) (-1) = Pff.Float 4 (-1)).
    replace ((-2) * (-2 * 1)) with (IZR 4) by (simpl; ring).
    rewrite (Pff.IRNDD_projector b 2 ltac:(lia)). reflexivity.
  - exfalso. apply H.
    unfold Pff.FtoR, Pff.firstNormalPos, Pff.nNormMin, b.
    simpl. lra.
Qed.
