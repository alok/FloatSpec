From Stdlib Require Import Reals ZArith.
From Flocq Require Import Core.Core.
Open Scope R_scope.

Definition opposite_contract :
  forall (beta : radix) (fexp : Z -> Z) (x : R),
    round beta fexp ZnearestE (-x) = -round beta fexp ZnearestE x :=
  @round_NE_opp.

Definition absolute_contract :
  forall (beta : radix) (fexp : Z -> Z), Valid_exp fexp -> forall x : R,
    round beta fexp ZnearestE (Rabs x) = Rabs (round beta fexp ZnearestE x) :=
  @round_NE_abs.

Definition positive_point_contract :
  forall (beta : radix) (fexp : Z -> Z), Valid_exp fexp -> Exists_NE beta fexp ->
    forall x : R, 0 < x -> Rnd_NE_pt beta fexp x (round beta fexp ZnearestE x) :=
  @round_NE_pt_pos.

Definition point_contract :
  forall (beta : radix) (fexp : Z -> Z), Valid_exp fexp -> Exists_NE beta fexp ->
    forall x : R, Rnd_NE_pt beta fexp x (round beta fexp ZnearestE x) :=
  @round_NE_pt.

Print Assumptions opposite_contract.
Print Assumptions absolute_contract.
Print Assumptions positive_point_contract.
Print Assumptions point_contract.

Definition total_contract :
  forall (beta : radix) (fexp : Z -> Z), Valid_exp fexp -> Exists_NE beta fexp ->
    round_pred_total (Rnd_NE_pt beta fexp) := @Rnd_NE_pt_total.

Definition monotone_contract :
  forall (beta : radix) (fexp : Z -> Z), Valid_exp fexp -> Exists_NE beta fexp ->
    round_pred_monotone (Rnd_NE_pt beta fexp) := @Rnd_NE_pt_monotone.

Definition round_contract :
  forall (beta : radix) (fexp : Z -> Z), Valid_exp fexp -> Exists_NE beta fexp ->
    round_pred (Rnd_NE_pt beta fexp) := @Rnd_NE_pt_round.

Print Assumptions total_contract.
Print Assumptions monotone_contract.
Print Assumptions round_contract.

(* The relational API and concrete-result theorem compose without adapters. *)
Theorem rounded_values_monotone :
  forall (beta : radix) (fexp : Z -> Z), Valid_exp fexp -> Exists_NE beta fexp ->
    forall x y : R, x <= y -> round beta fexp ZnearestE x <= round beta fexp ZnearestE y.
Proof.
  intros beta fexp Hv He x y Hxy.
  exact (@Rnd_NE_pt_monotone beta fexp Hv He x y _ _
    (@round_NE_pt beta fexp Hv He x) (@round_NE_pt beta fexp Hv He y) Hxy).
Qed.
Print Assumptions rounded_values_monotone.
