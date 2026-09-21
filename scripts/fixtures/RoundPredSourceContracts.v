From Stdlib Require Import Reals Lra.
From Flocq Require Import Core.Defs Core.Round_pred.
Open Scope R_scope.

(* Exact source contracts: these clients fail if a premise or conclusion drifts. *)
Definition unique_contract : forall P, round_pred_monotone P -> forall x f g,
  P x f -> P x g -> f = g := round_unique.
Definition dn_monotone_contract : forall F, round_pred_monotone (Rnd_DN_pt F) :=
  Rnd_DN_pt_monotone.
Definition dn_unique_contract : forall F x f g,
  Rnd_DN_pt F x f -> Rnd_DN_pt F x g -> f = g := Rnd_DN_pt_unique.
Definition dn_fun_unique_contract : forall F r s,
  Rnd_DN F r -> Rnd_DN F s -> forall x, r x = s x := Rnd_DN_unique.
Definition up_monotone_contract : forall F, round_pred_monotone (Rnd_UP_pt F) :=
  Rnd_UP_pt_monotone.
Definition up_unique_contract : forall F x f g,
  Rnd_UP_pt F x f -> Rnd_UP_pt F x g -> f = g := Rnd_UP_pt_unique.
Definition up_fun_unique_contract : forall F r s,
  Rnd_UP F r -> Rnd_UP F s -> forall x, r x = s x := Rnd_UP_unique.
Definition up_opp_contract : forall F, (forall x, F x -> F (-x)) -> forall x f,
  Rnd_DN_pt F x f -> Rnd_UP_pt F (-x) (-f) := Rnd_UP_pt_opp.
Definition dn_opp_contract : forall F, (forall x, F x -> F (-x)) -> forall x f,
  Rnd_UP_pt F x f -> Rnd_DN_pt F (-x) (-f) := Rnd_DN_pt_opp.
Definition fun_opp_contract : forall F, (forall x, F x -> F (-x)) -> forall r s,
  Rnd_DN F r -> Rnd_UP F s -> forall x, r (-x) = -s x := Rnd_DN_opp.
Definition split_contract : forall F x d u, Rnd_DN_pt F x d -> Rnd_UP_pt F x u ->
  forall f, F f -> f <= d \/ u <= f := Rnd_DN_UP_pt_split.
Definition dn_refl_contract : forall F x, F x -> Rnd_DN_pt F x x := Rnd_DN_pt_refl.
Definition dn_idem_contract : forall F x f, Rnd_DN_pt F x f -> F x -> f = x :=
  Rnd_DN_pt_idempotent.
Definition up_refl_contract : forall F x, F x -> Rnd_UP_pt F x x := Rnd_UP_pt_refl.
Definition up_idem_contract : forall F x f, Rnd_UP_pt F x f -> F x -> f = x :=
  Rnd_UP_pt_idempotent.
Definition endpoints_contract : forall F x d u f,
  Rnd_DN_pt F x d -> Rnd_UP_pt F x u -> F f -> d <= f <= u -> f = d \/ f = u :=
  Only_DN_or_UP.
Definition zr_abs_contract : forall F r, Rnd_ZR F r -> forall x, Rabs (r x) <= Rabs x :=
  Rnd_ZR_abs.
Definition zr_monotone_contract : forall F, F 0 -> round_pred_monotone (Rnd_ZR_pt F) :=
  Rnd_ZR_pt_monotone.
Definition nearest_directed_contract : forall F x f,
  Rnd_N_pt F x f -> Rnd_DN_pt F x f \/ Rnd_UP_pt F x f := Rnd_N_pt_DN_or_UP.
Definition nearest_endpoints_contract : forall F x d u f,
  Rnd_DN_pt F x d -> Rnd_UP_pt F x u -> Rnd_N_pt F x f -> f = d \/ f = u :=
  Rnd_N_pt_DN_or_UP_eq.
Definition nearest_opp_contract : forall F, (forall x, F x -> F (-x)) -> forall x f,
  Rnd_N_pt F (-x) (-f) -> Rnd_N_pt F x f := Rnd_N_pt_opp_inv.
Definition nearest_monotone_contract : forall F x y f g,
  Rnd_N_pt F x f -> Rnd_N_pt F y g -> x < y -> f <= g := Rnd_N_pt_monotone.
Definition nearest_unique_contract : forall F x d u f g,
  Rnd_DN_pt F x d -> Rnd_UP_pt F x u -> x - d <> u - x ->
  Rnd_N_pt F x f -> Rnd_N_pt F x g -> f = g := Rnd_N_pt_unique.
Definition nearest_refl_contract : forall F x, F x -> Rnd_N_pt F x x := Rnd_N_pt_refl.
Definition nearest_idem_contract : forall F x f, Rnd_N_pt F x f -> F x -> f = x :=
  Rnd_N_pt_idempotent.

(* These are real counterexamples, not just failed attempts to apply a theorem. *)
Definition two_points (x : R) := x = -1 \/ x = 1.

Lemma tie_left : Rnd_N_pt two_points 0 (-1).
Proof.
  split; [left; reflexivity|]. intros g [Hg|Hg]; subst g;
    unfold Rabs; repeat destruct Rcase_abs; lra.
Qed.

Lemma tie_right : Rnd_N_pt two_points 0 1.
Proof.
  split; [right; reflexivity|]. intros g [Hg|Hg]; subst g;
    unfold Rabs; repeat destruct Rcase_abs; lra.
Qed.

Lemma nearest_is_not_nonstrict_monotone : ~ round_pred_monotone (Rnd_N_pt two_points).
Proof. intro H; pose proof (H 0 0 1 (-1) tie_right tie_left (Rle_refl 0)); lra. Qed.

Lemma nearest_is_not_unconditionally_unique :
  ~ (forall F x f g, Rnd_N_pt F x f -> Rnd_N_pt F x g -> f = g).
Proof. intro H; pose proof (H two_points 0 (-1) 1 tie_left tie_right); lra. Qed.

Lemma zr_negative : Rnd_ZR_pt two_points (- /2) 1.
Proof.
  split; [intro H; lra|]. intros _. split; [right; reflexivity|].
  split; [lra|]. intros g [Hg|Hg] H; subst g; lra.
Qed.

Lemma zr_positive : Rnd_ZR_pt two_points (/2) (-1).
Proof.
  split; [|intro H; lra]. intros _. split; [left; reflexivity|].
  split; [lra|]. intros g [Hg|Hg] H; subst g; lra.
Qed.

Lemma zero_membership_is_necessary : ~ round_pred_monotone (Rnd_ZR_pt two_points).
Proof.
  intro H; pose proof (H (- /2) (/2) 1 (-1) zr_negative zr_positive ltac:(lra)); lra.
Qed.

Print Assumptions nearest_is_not_nonstrict_monotone.
Print Assumptions nearest_is_not_unconditionally_unique.
Print Assumptions zero_membership_is_necessary.
