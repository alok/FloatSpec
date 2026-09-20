From Stdlib Require Import ZArith Bool List.
From Flocq Require Import IEEE754.BinarySingleNaN.
Import ListNotations.
Open Scope Z_scope.

Definition observe {prec emax : Z} (x y : binary_float prec emax) : list bool :=
  [@Beqb prec emax x y; @Bltb prec emax x y; @Bleb prec emax x y].

Definition finite (sign : bool) (mantissa : positive) (exponent : Z) : binary_float 3 4 :=
  @SF2B' 3 4 (SpecFloat.S754_finite sign mantissa exponent).

Definition table : list (list bool) :=
  [observe (@B754_zero 0 (-1) false) (@B754_zero 0 (-1) true);
   observe (@B754_nan 3 4) (@B754_nan 3 4);
   observe (@B754_infinity 3 4 false) (@B754_infinity 3 4 false);
   observe (@B754_infinity 1 1 true) (@B754_infinity 1 1 false);
   observe (finite true 4 (-1)) (finite true 4 (-2));
   observe (finite false 3 (-4)) (finite false 4 (-4));
   observe (finite true 3 (-4)) (finite true 4 (-4));
   observe (finite false 1 0) (finite false 4 (-2))].

Example boolean_comparison_boundaries : table =
  [[true; false; true]; [false; false; false]; [true; false; true];
   [false; true; true]; [false; true; true]; [false; true; true];
   [false; false; false]; [false; false; false]].
Proof. vm_compute. reflexivity. Qed.

Eval vm_compute in table.
