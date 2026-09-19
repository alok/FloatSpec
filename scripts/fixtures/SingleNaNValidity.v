From Stdlib Require Import ZArith List.
From Flocq Require Import IEEE754.BinarySingleNaN.
Import ListNotations.
Open Scope Z_scope.

Definition valid (m : positive) (e : Z) :=
  SpecFloat.valid_binary 3 4 (SpecFloat.S754_finite false m e).

Example validity_boundaries :
  valid 1 0 = false /\ valid 4 (-2) = true /\ valid 4 2 = false /\
  valid 1 (-4) = true /\ valid 1 (-5) = false.
Proof. vm_compute. repeat split; reflexivity. Qed.

(* Zero mantissas cannot even be constructed in the source positive type. *)
Eval vm_compute in [valid 1 0; valid 4 (-2); valid 4 2; valid 1 (-4); valid 1 (-5)].
