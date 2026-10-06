From Stdlib Require Import ZArith List Lia Bool.
From Flocq Require Import Core.Zaux.
Import ListNotations.
Open Scope Z_scope.
Open Scope bool_scope.

(* Stdlib's Zeq_bool/Zle_bool/Zlt_bool are deprecated notations for Z.eqb/Z.leb/Z.ltb.
   Rocq 9.1's deprecation hint names Z.eqb for all three; the expansions are used here. *)

Definition eq_true_ctor : forall x y, x = y -> Zeq_bool_prop x y true := Zeq_bool_true_.
Definition eq_false_ctor : forall x y, x <> y -> Zeq_bool_prop x y false := Zeq_bool_false_.
Definition le_true_ctor : forall x y, x <= y -> Zle_bool_prop x y true := Zle_bool_true_.
Definition le_false_ctor : forall x y, y < x -> Zle_bool_prop x y false := Zle_bool_false_.
Definition lt_true_ctor : forall x y, x < y -> Zlt_bool_prop x y true := Zlt_bool_true_.
Definition lt_false_ctor : forall x y, y <= x -> Zlt_bool_prop x y false := Zlt_bool_false_.
Definition cmp_lt_ctor : forall x y, x < y -> Zcompare_prop x y Lt := Zcompare_Lt_.
Definition cmp_eq_ctor : forall x y, x = y -> Zcompare_prop x y Eq := Zcompare_Eq_.
Definition cmp_gt_ctor : forall x y, y < x -> Zcompare_prop x y Gt := Zcompare_Gt_.

Definition eq_prop_ind : forall x y (P : bool -> Prop),
  (x = y -> P true) -> (x <> y -> P false) -> forall b, Zeq_bool_prop x y b -> P b :=
  Zeq_bool_prop_ind.
Definition le_prop_ind : forall x y (P : bool -> Prop),
  (x <= y -> P true) -> (y < x -> P false) -> forall b, Zle_bool_prop x y b -> P b :=
  Zle_bool_prop_ind.
Definition lt_prop_ind : forall x y (P : bool -> Prop),
  (x < y -> P true) -> (y <= x -> P false) -> forall b, Zlt_bool_prop x y b -> P b :=
  Zlt_bool_prop_ind.
Definition cmp_prop_ind : forall x y (P : comparison -> Prop),
  (x < y -> P Lt) -> (x = y -> P Eq) -> (y < x -> P Gt) ->
  forall c, Zcompare_prop x y c -> P c :=
  Zcompare_prop_ind.
(* The SProp schemes, which Lean has no counterpart for. *)
Definition eq_prop_sind : forall x y (P : bool -> SProp),
  (x = y -> P true) -> (x <> y -> P false) -> forall b, Zeq_bool_prop x y b -> P b :=
  Zeq_bool_prop_sind.
Definition cmp_prop_sind : forall x y (P : comparison -> SProp),
  (x < y -> P Lt) -> (x = y -> P Eq) -> (y < x -> P Gt) ->
  forall c, Zcompare_prop x y c -> P c :=
  Zcompare_prop_sind.

Definition eq_spec : forall x y, Zeq_bool_prop x y (Z.eqb x y) := Zeq_bool_spec.
Definition eq_true : forall x y, x = y -> Z.eqb x y = true := Zeq_bool_true.
Definition eq_false : forall x y, x <> y -> Z.eqb x y = false := Zeq_bool_false.
Definition eq_diag : forall x, Z.eqb x x = true := Zeq_bool_diag.
Definition eq_opp : forall x y, Z.eqb (- x) y = Z.eqb x (- y) := Zeq_bool_opp.
Definition eq_opp' : forall x y, Z.eqb (- x) (- y) = Z.eqb x y := Zeq_bool_opp'.

Definition le_spec : forall x y, Zle_bool_prop x y (Z.leb x y) := Zle_bool_spec.
Definition le_true : forall x y, x <= y -> Z.leb x y = true := Zle_bool_true.
Definition le_false : forall x y, y < x -> Z.leb x y = false := Zle_bool_false.
Definition le_opp_l : forall x y, Z.leb (- x) y = Z.leb (- y) x := Zle_bool_opp_l.
Definition le_opp : forall x y, Z.leb (- x) (- y) = Z.leb y x := Zle_bool_opp.
Definition le_opp_r : forall x y, Z.leb x (- y) = Z.leb y (- x) := Zle_bool_opp_r.

Definition lt_spec : forall x y, Zlt_bool_prop x y (Z.ltb x y) := Zlt_bool_spec.
Definition lt_true : forall x y, x < y -> Z.ltb x y = true := Zlt_bool_true.
Definition lt_false : forall x y, y <= x -> Z.ltb x y = false := Zlt_bool_false.
Definition negb_le : forall x y, negb (Z.leb x y) = Z.ltb y x := negb_Zle_bool.
Definition negb_lt : forall x y, negb (Z.ltb x y) = Z.leb y x := negb_Zlt_bool.
Definition lt_opp_l : forall x y, Z.ltb (- x) y = Z.ltb (- y) x := Zlt_bool_opp_l.
Definition lt_opp_r : forall x y, Z.ltb x (- y) = Z.ltb y (- x) := Zlt_bool_opp_r.
Definition lt_opp : forall x y, Z.ltb (- x) (- y) = Z.ltb y x := Zlt_bool_opp.

Definition cmp_spec : forall x y, Zcompare_prop x y (Z.compare x y) := Zcompare_spec.
Definition cmp_lt : forall x y, x < y -> Z.compare x y = Lt := Zcompare_Lt.
Definition cmp_eq : forall x y, x = y -> Z.compare x y = Eq := Zcompare_Eq.
Definition cmp_gt : forall x y, y < x -> Z.compare x y = Gt := Zcompare_Gt.

Print Assumptions eq_prop_ind.
Print Assumptions cmp_prop_ind.
Print Assumptions le_opp_l.
Print Assumptions negb_le.
Print Assumptions cmp_spec.

Example le_graph_false_branch_is_strict : ~ Zle_bool_prop 0 0 false.
Proof. intro H. inversion H. lia. Qed.
Example lt_graph_true_branch_is_strict : ~ Zlt_bool_prop 0 0 true.
Proof. intro H. inversion H. lia. Qed.
Example le_opp_l_needs_swap : ~ forall x y, Z.leb (- x) y = Z.leb x (- y).
Proof. intro H. specialize (H 0 1). discriminate H. Qed.
Example negb_le_needs_swap : ~ forall x y, negb (Z.leb x y) = Z.ltb x y.
Proof. intro H. specialize (H 0 1). discriminate H. Qed.
Example eq_opp_needs_negation : ~ forall x y, Z.eqb (- x) y = Z.eqb x y.
Proof. intro H. specialize (H 1 (-1)). discriminate H. Qed.
Print Assumptions le_graph_false_branch_is_strict.
Print Assumptions lt_graph_true_branch_is_strict.
Print Assumptions le_opp_l_needs_swap.
Print Assumptions negb_le_needs_swap.
Print Assumptions eq_opp_needs_negation.

Example three_way : Z.compare (-3) 2 = Lt /\ Z.compare 2 2 = Eq /\ Z.compare 2 (-3) = Gt.
Proof. vm_compute. auto. Qed.

Definition sign_of (c : comparison) := match c with Lt => -1 | Eq => 0 | Gt => 1 end.

Definition boolean_laws x y :=
  Bool.eqb (Z.eqb x y) (Z.eqb y x) &&
  Z.eqb (sign_of (Z.compare x y)) (if Z.ltb x y then -1 else if Z.eqb x y then 0 else 1) &&
  Bool.eqb (Z.eqb (- x) y) (Z.eqb x (- y)) && Bool.eqb (Z.eqb (- x) (- y)) (Z.eqb x y) &&
  Bool.eqb (Z.leb (- x) y) (Z.leb (- y) x) && Bool.eqb (Z.leb (- x) (- y)) (Z.leb y x) &&
  Bool.eqb (Z.leb x (- y)) (Z.leb y (- x)) && Bool.eqb (negb (Z.leb x y)) (Z.ltb y x) &&
  Bool.eqb (negb (Z.ltb x y)) (Z.leb y x) && Bool.eqb (Z.ltb (- x) y) (Z.ltb (- y) x) &&
  Bool.eqb (Z.ltb x (- y)) (Z.ltb y (- x)) && Bool.eqb (Z.ltb (- x) (- y)) (Z.ltb y x).

Definition signed_values :=
  map (fun k => Z.of_nat k - 8) (seq 0 17) ++
  [-2^64; -2^63 - 1; -2^63; 2^63 - 1; 2^63; 2^64].

Example signed_boolean_grid :
  forallb (fun x => forallb (fun y => boolean_laws x y) signed_values) signed_values = true.
Proof. vm_compute. reflexivity. Qed.
