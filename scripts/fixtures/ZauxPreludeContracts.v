From Stdlib Require Import ZArith List.
From Flocq Require Import Version Core.Zaux.
Import ListNotations.
Open Scope Z_scope.

Example version_contract : Flocq_version = 40202%N.
Proof. vm_compute. reflexivity. Qed.
Definition neg_order_contract : forall x y : Z, -y <= -x -> x <= y := Zopp_le_cancel.
Definition neq_contract : forall x y : Z, y < x -> x <> y := Zgt_not_eq.
Example eqbool_true (P : bool -> Type) (h : P true) :
  eqbool_dep P h true = (fun h' => h = h').
Proof. reflexivity. Qed.
Example eqbool_false (P : bool -> Type) (h : P true) :
  eqbool_dep P h false = (fun _ => False).
Proof. reflexivity. Qed.
Definition irrelevance_contract : forall (b : bool) (h1 h2 : b = true), h1 = h2 := eqbool_irrelevance.
Example conditional_negation_contract (b : bool) (x : Z) :
  cond_Zopp b x = if b then -x else x.
Proof. reflexivity. Qed.

(* Flocq's generated eq_dep_elim is proof infrastructure, not a numeric API.
   Its sole local use proves eqbool_irrelevance; Lean uses proof irrelevance. *)
Check eq_dep_elim.
Print Corelib.Floats.SpecFloat.iter_pos.
Print Assumptions eqbool_irrelevance.

Definition positives : list positive := [1; 2; 3; 4; 5; 6; 7; 8]%positive.
Example iteration_observations :
  map (fun p => iter_pos (fun x : Z => 2*x+3) p (-2)) positives =
    [-1; 1; 5; 13; 29; 61; 125; 253].
Proof. vm_compute. reflexivity. Qed.
Example sign_observations :
  map (fun b => map (cond_Zopp b) [-1000000; -7; -1; 0; 1; 7; 1000000]) [false; true] =
    [[-1000000; -7; -1; 0; 1; 7; 1000000]; [1000000; 7; 1; 0; -1; -7; -1000000]].
Proof. vm_compute. reflexivity. Qed.
