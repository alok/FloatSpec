From Stdlib Require Import Reals ZArith.
Require Import Flocq.Core.Raux.

Definition minClient (P : nat -> Prop) (hdec : forall n, P n \/ ~ P n) :
  {n : nat | P n /\ forall i, (i < n)%nat -> ~ P i} + {forall n, ~ P n} :=
  LPO_min P hdec.
Definition natClient (P : nat -> Prop) (hdec : forall n, P n \/ ~ P n) :
  {n : nat | P n} + {forall n, ~ P n} := LPO P hdec.
Definition intClient (P : Z -> Prop) (hdec : forall n, P n \/ ~ P n) :
  {n : Z | P n} + {forall n, ~ P n} := LPO_Z P hdec.

(* Consumers extract data and its proof from Type, not a proposition describing
   an unrelated optional choice. No native decision procedure is claimed. *)
Definition naturalWitness (P : nat -> Prop) (hdec : forall n, P n \/ ~ P n)
  (hex : exists n, P n) : {n : nat | P n}.
Proof.
  destruct (natClient P hdec) as [witness|none].
  - exact witness.
  - exfalso. destruct hex as [n hn]. exact (none n hn).
Defined.
Definition integerWitness (P : Z -> Prop) (hdec : forall n, P n \/ ~ P n)
  (hex : exists n, P n) : {n : Z | P n}.
Proof.
  destruct (intClient P hdec) as [witness|none].
  - exact witness.
  - exfalso. destruct hex as [n hn]. exact (none n hn).
Defined.

Example negative_witness (hdec : forall n : Z, n = (-3)%Z \/ n <> (-3)%Z) :
  proj1_sig (integerWitness (fun n => n = (-3)%Z) hdec
    (ex_intro _ (-3)%Z eq_refl)) = (-3)%Z.
Proof. apply proj2_sig. Qed.

Example empty_predicate (hdec : forall n : nat, False \/ ~ False) :
  match natClient (fun _ => False) hdec with inleft _ => False | inright _ => True end.
Proof.
  destruct (natClient (fun _ => False) hdec) as [[n hn]|hn].
  - exact hn.
  - exact I.
Qed.
