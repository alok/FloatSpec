From Stdlib Require Import ZArith List.
From Flocq Require Import IEEE754.BinarySingleNaN.
Import ListNotations.
Open Scope Z_scope.

Definition observe (x : SpecFloat.spec_float) : list Z :=
  match x with
  | SpecFloat.S754_finite s m e => [if s then 1 else 0; Z.pos m; e]
  | _ => []
  end.

Definition direct (s : bool) := binary_round 3 10 mode_NE s 73 (-6).
Definition viaFour (s : bool) :=
  match binary_round 4 10 mode_NE s 73 (-6) with
  | SpecFloat.S754_finite sign m e => binary_round 3 10 mode_NE sign m e
  | x => x
  end.

Example double_rounding_counterexample :
  observe (direct false) = [0;5;-2] /\ observe (viaFour false) = [0;4;-2] /\
  observe (direct true) = [1;5;-2] /\ observe (viaFour true) = [1;4;-2].
Proof. vm_compute. repeat split; reflexivity. Qed.

Eval vm_compute in [observe (direct false); observe (viaFour false);
  observe (direct true); observe (viaFour true)].
