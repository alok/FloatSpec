From Stdlib Require Import ZArith List.
From Flocq Require Import IEEE754.Binary IEEE754.BinarySingleNaN.
Import ListNotations.
Open Scope Z_scope.

Definition rows : list SpecFloat.spec_float :=
  [@BinarySingleNaN.binary_overflow 0 1 mode_ZR false;
   @BinarySingleNaN.binary_overflow (-1) 1 mode_ZR true;
   @BinarySingleNaN.binary_overflow 0 (-4) mode_NE true;
   Binary.FF2SF (@Binary.binary_overflow 3 3 mode_ZR false);
   Binary.FF2SF (@Binary.binary_overflow 0 1 mode_ZR false);
   Binary.FF2SF (@Binary.binary_overflow (-3) (-4) mode_UP true);
   @BinarySingleNaN.binary_overflow 3 4 mode_ZR true].

Example raw_overflow_boundaries : rows =
  [SpecFloat.S754_finite false 1 1; SpecFloat.S754_finite true 1 2;
   SpecFloat.S754_infinity true; SpecFloat.S754_finite false 7 0;
   SpecFloat.S754_finite false 1 1; SpecFloat.S754_finite true 1 (-1);
   SpecFloat.S754_finite true 7 1].
Proof. vm_compute. reflexivity. Qed.
