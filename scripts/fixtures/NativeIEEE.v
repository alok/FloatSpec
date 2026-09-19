From Stdlib Require Import ZArith List.
From Flocq Require Import IEEE754.Bits IEEE754.Binary.
Import ListNotations.
Open Scope Z_scope.

(* Match Lean's single-NaN observation quotient, not raw payload identity. *)
Definition canonical_bits (x : binary64) : Z :=
  if Binary.is_nan 53 1024 x then 9221120237041090560 else bits_of_b64 x.

Definition observation (word : Z) : list Z :=
  let x := b64_of_bits word in
  let result := Binary.Bfrexp 53 1024 (ltac:(compute; reflexivity)) x in
  [canonical_bits x; canonical_bits (b64_succ x); canonical_bits (b64_pred x);
   canonical_bits (fst result); snd result].

Example minimum_subnormal : observation 1 =
    [1; 2; 0; 4602678819172646912; -1073].
Proof. vm_compute. reflexivity. Qed.
