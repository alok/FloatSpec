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
