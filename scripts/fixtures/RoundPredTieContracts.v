From Stdlib Require Import Reals Lra.
From Flocq Require Import Core.Defs Core.Round_pred.
Open Scope R_scope.

Example dn_lifting F r : Rnd_DN F r = (forall x, Rnd_DN_pt F x (r x)). Proof. reflexivity. Qed.
Example up_lifting F r : Rnd_UP F r = (forall x, Rnd_UP_pt F x (r x)). Proof. reflexivity. Qed.
Example zr_lifting F r : Rnd_ZR F r = (forall x, Rnd_ZR_pt F x (r x)). Proof. reflexivity. Qed.
Example nearest_lifting F r : Rnd_N F r = (forall x, Rnd_N_pt F x (r x)). Proof. reflexivity. Qed.
Example generic_lifting F P r : Rnd_NG F P r = (forall x, Rnd_NG_pt F P x (r x)).
Proof. reflexivity. Qed.
Example away_lifting F r : Rnd_NA F r = (forall x, Rnd_NA_pt F x (r x)). Proof. reflexivity. Qed.
Example zero_lifting F r : Rnd_N0 F r = (forall x, Rnd_N0_pt F x (r x)). Proof. reflexivity. Qed.
Definition value_contract : forall rnd, round_pred rnd -> forall x, {f : R | rnd x f} :=
  round_val_of_pred.
Definition function_contract : forall rnd, round_pred rnd ->
  {f : R -> R | forall x, rnd x (f x)} := round_fun_of_pred.

Definition nearest_zero_contract : forall F, F 0 -> Rnd_N_pt F 0 0 := Rnd_N_pt_0.
Definition nearest_nonneg_contract : forall F, F 0 -> forall x f,
  0 <= x -> Rnd_N_pt F x f -> 0 <= f := Rnd_N_pt_ge_0.
Definition nearest_nonpos_contract : forall F, F 0 -> forall x f,
  x <= 0 -> Rnd_N_pt F x f -> f <= 0 := Rnd_N_pt_le_0.
Definition nearest_abs_contract : forall F, F 0 -> (forall x, F x -> F (-x)) -> forall x f,
  Rnd_N_pt F x f -> Rnd_N_pt F (Rabs x) (Rabs f) := Rnd_N_pt_abs.
Definition nearest_bracket_contract : forall F x d u f,
  F f -> Rnd_DN_pt F x d -> Rnd_UP_pt F x u ->
  Rabs (f-x) <= x-d -> Rabs (f-x) <= u-x -> Rnd_N_pt F x f := Rnd_N_pt_DN_UP.
Definition nearest_down_contract : forall F x d u,
  Rnd_DN_pt F x d -> Rnd_UP_pt F x u -> x-d <= u-x -> Rnd_N_pt F x d := Rnd_N_pt_DN.
Definition nearest_up_contract : forall F x d u,
  Rnd_DN_pt F x d -> Rnd_UP_pt F x u -> u-x <= x-d -> Rnd_N_pt F x u := Rnd_N_pt_UP.

Example uniqueness_shape F (P : R -> R -> Type) : Rnd_NG_pt_unique_prop F P =
  (forall x d u, Rnd_DN_pt F x d -> Rnd_N_pt F x d ->
   Rnd_UP_pt F x u -> Rnd_N_pt F x u -> P x d -> P x u -> d = u).
Proof. reflexivity. Qed.
Definition generic_unique_contract : forall F (P : R -> R -> Prop),
  Rnd_NG_pt_unique_prop F P -> forall x f g,
  Rnd_NG_pt F P x f -> Rnd_NG_pt F P x g -> f = g := Rnd_NG_pt_unique.
Definition generic_monotone_contract : forall F (P : R -> R -> Prop), Rnd_NG_pt_unique_prop F P ->
  round_pred_monotone (Rnd_NG_pt F P) := Rnd_NG_pt_monotone.
Definition generic_refl_contract : forall F P x, F x -> Rnd_NG_pt F P x x := Rnd_NG_pt_refl.
Definition generic_opp_contract : forall F P,
  (forall x, F x -> F (-x)) -> (forall x f, P x f -> P (-x) (-f)) ->
  forall x f, Rnd_NG_pt F P (-x) (-f) -> Rnd_NG_pt F P x f := Rnd_NG_pt_opp_inv.
Definition generic_fun_unique_contract : forall F (P : R -> R -> Prop),
  Rnd_NG_pt_unique_prop F P -> forall r s,
  Rnd_NG F P r -> Rnd_NG F P s -> forall x, r x = s x := Rnd_NG_unique.

Definition away_generic_contract : forall F, F 0 -> forall x f,
  Rnd_NA_pt F x f <-> Rnd_NG_pt F (fun x f => Rabs x <= Rabs f) x f := Rnd_NA_NG_pt.
Definition away_unique_prop_contract : forall F, F 0 ->
  Rnd_NG_pt_unique_prop F (fun x f => Rabs x <= Rabs f) := Rnd_NA_pt_unique_prop.
Definition away_unique_contract : forall F, F 0 -> forall x f g,
  Rnd_NA_pt F x f -> Rnd_NA_pt F x g -> f = g := Rnd_NA_pt_unique.
Definition away_intro_contract : forall F, F 0 -> forall x f,
  Rnd_N_pt F x f -> Rabs x <= Rabs f -> Rnd_NA_pt F x f := Rnd_NA_pt_N.
Definition away_fun_unique_contract : forall F, F 0 -> forall r s,
  Rnd_NA F r -> Rnd_NA F s -> forall x, r x = s x := Rnd_NA_unique.
Definition away_monotone_contract : forall F, F 0 -> round_pred_monotone (Rnd_NA_pt F) :=
  Rnd_NA_pt_monotone.
Definition away_refl_contract : forall F x, F x -> Rnd_NA_pt F x x := Rnd_NA_pt_refl.
Definition away_idem_contract : forall F x f, Rnd_NA_pt F x f -> F x -> f = x :=
  Rnd_NA_pt_idempotent.
Definition zero_generic_contract : forall F, F 0 -> forall x f,
  Rnd_N0_pt F x f <-> Rnd_NG_pt F (fun x f => Rabs f <= Rabs x) x f := Rnd_N0_NG_pt.
Definition zero_unique_prop_contract : forall F, F 0 ->
  Rnd_NG_pt_unique_prop F (fun x f => Rabs f <= Rabs x) := Rnd_N0_pt_unique_prop.
Definition zero_unique_contract : forall F, F 0 -> forall x f g,
  Rnd_N0_pt F x f -> Rnd_N0_pt F x g -> f = g := Rnd_N0_pt_unique.
Definition zero_intro_contract : forall F, F 0 -> forall x f,
  Rnd_N_pt F x f -> Rabs f <= Rabs x -> Rnd_N0_pt F x f := Rnd_N0_pt_N.
Definition zero_fun_unique_contract : forall F, F 0 -> forall r s,
  Rnd_N0 F r -> Rnd_N0 F s -> forall x, r x = s x := Rnd_N0_unique.
Definition zero_monotone_contract : forall F, F 0 -> round_pred_monotone (Rnd_N0_pt F) :=
  Rnd_N0_pt_monotone.
Definition zero_refl_contract : forall F x, F x -> Rnd_N0_pt F x x := Rnd_N0_pt_refl.
Definition zero_idem_contract : forall F x f, Rnd_N0_pt F x f -> F x -> f = x :=
  Rnd_N0_pt_idempotent.

Definition nonnegative_contract : forall P, round_pred_monotone P -> P 0 0 -> forall x f,
  P x f -> 0 <= x -> 0 <= f := round_pred_ge_0.
Definition positive_contract : forall P, round_pred_monotone P -> P 0 0 -> forall x f,
  P x f -> 0 < f -> 0 < x := round_pred_gt_0.
Definition nonpositive_contract : forall P, round_pred_monotone P -> P 0 0 -> forall x f,
  P x f -> x <= 0 -> f <= 0 := round_pred_le_0.
Definition negative_contract : forall P, round_pred_monotone P -> P 0 0 -> forall x f,
  P x f -> f < 0 -> x < 0 := round_pred_lt_0.
Definition down_format_contract : forall F1 F2 a b,
  F1 a -> (forall x, a <= x <= b -> (F1 x <-> F2 x)) ->
  forall x f, a <= x <= b -> Rnd_DN_pt F1 x f -> Rnd_DN_pt F2 x f := Rnd_DN_pt_equiv_format.
Definition up_format_contract : forall F1 F2 a b,
  F1 b -> (forall x, a <= x <= b -> (F1 x <-> F2 x)) ->
  forall x f, a <= x <= b -> Rnd_UP_pt F1 x f -> Rnd_UP_pt F2 x f := Rnd_UP_pt_equiv_format.

Definition totality_equiv_contract : forall F1 F2, (forall x, F1 x <-> F2 x) ->
  satisfies_any F1 -> satisfies_any F2 := satisfies_any_eq.
Definition totality_down_contract : forall F, satisfies_any F -> round_pred (Rnd_DN_pt F) :=
  satisfies_any_imp_DN.
Definition totality_up_contract : forall F, satisfies_any F -> round_pred (Rnd_UP_pt F) :=
  satisfies_any_imp_UP.
Definition totality_zero_contract : forall F, satisfies_any F -> round_pred (Rnd_ZR_pt F) :=
  satisfies_any_imp_ZR.
Example existence_shape F P : NG_existence_prop F P =
  (forall x d u, ~ F x -> Rnd_DN_pt F x d -> Rnd_UP_pt F x u -> P x u \/ P x d).
Proof. reflexivity. Qed.
Definition totality_generic_contract : forall F P, satisfies_any F -> NG_existence_prop F P ->
  round_pred_total (Rnd_NG_pt F P) := satisfies_any_imp_NG.
Definition totality_away_contract : forall F, satisfies_any F -> round_pred (Rnd_NA_pt F) :=
  satisfies_any_imp_NA.
Definition totality_nearzero_contract : forall F, F 0 -> satisfies_any F -> round_pred (Rnd_N0_pt F) :=
  satisfies_any_imp_N0.
Definition constructor_contract : forall F, F 0 -> (forall x, F x -> F (-x)) ->
  round_pred_total (Rnd_DN_pt F) -> satisfies_any F := Satisfies_any.
Definition eliminate_to_data F (h : satisfies_any F) : nat :=
  match h with Satisfies_any _ _ _ _ => 7%nat end.

Example false_policy_at_representable :
  Rnd_NG_pt (fun x => x = 0) (fun _ _ => False) 0 0.
Proof. apply Rnd_NG_pt_refl; reflexivity. Qed.

Definition eliminate_dependent : forall F (motive : satisfies_any F -> Type),
  (forall h0 hs ht, motive (Satisfies_any F h0 hs ht)) -> forall h, motive h :=
  satisfies_any_rect.

Definition two_points (x : R) := x = -1 \/ x = 1.
Lemma two_nearest f : two_points f -> Rnd_N_pt two_points 0 f.
Proof.
  intro Hf. split; [exact Hf|]. intros g Hg.
  destruct Hf as [Hf|Hf]; destruct Hg as [Hg|Hg]; subst f; subst g;
    unfold Rabs; repeat destruct Rcase_abs; lra.
Qed.
Lemma two_abs f : two_points f -> Rabs f = 1.
Proof. intros [Hf|Hf]; subst f; unfold Rabs; destruct Rcase_abs; lra. Qed.
Lemma both_policies f : two_points f -> Rnd_NA_pt two_points 0 f /\ Rnd_N0_pt two_points 0 f.
Proof.
  intro Hf; split; split; try (now apply two_nearest).
  all: intros g [Hg _]; rewrite (two_abs f Hf), (two_abs g Hg); apply Rle_refl.
Qed.
Lemma tie_uniqueness_needs_zero :
  (~ (forall x f g, Rnd_NA_pt two_points x f -> Rnd_NA_pt two_points x g -> f = g)) /\
  (~ (forall x f g, Rnd_N0_pt two_points x f -> Rnd_N0_pt two_points x g -> f = g)).
Proof.
  pose proof (both_policies (-1) (or_introl eq_refl)) as [HNa HNz].
  pose proof (both_policies 1 (or_intror eq_refl)) as [HPa HPz].
  split; intro H; [pose proof (H 0 (-1) 1 HNa HPa)|pose proof (H 0 (-1) 1 HNz HPz)]; lra.
Qed.
Print Assumptions tie_uniqueness_needs_zero.
