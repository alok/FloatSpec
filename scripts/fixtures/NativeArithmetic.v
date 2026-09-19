From Stdlib Require Import ZArith List.
From Flocq Require Import IEEE754.Bits IEEE754.Binary IEEE754.BinarySingleNaN.
Import ListNotations.
Open Scope Z_scope.

Definition canonical_bits (x : binary64) : Z :=
  if Binary.is_nan 53 1024 x then 9221120237041090560 else bits_of_b64 x.

Definition observation (left right : Z) : list Z :=
  let x := b64_of_bits left in
  let y := b64_of_bits right in
  [canonical_bits x; canonical_bits y;
   canonical_bits (b64_plus mode_NE x y); canonical_bits (b64_minus mode_NE x y);
   canonical_bits (b64_mult mode_NE x y); canonical_bits (b64_div mode_NE x y);
   canonical_bits (b64_sqrt mode_NE x)].

Example one_and_two : observation 4607182418800017408 4611686018427387904 =
    [4607182418800017408; 4611686018427387904; 4613937818241073152;
     13830554455654793216; 4611686018427387904; 4602678819172646912;
     4607182418800017408].
Proof. vm_compute. reflexivity. Qed.
