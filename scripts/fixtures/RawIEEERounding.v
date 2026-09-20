From Stdlib Require Import ZArith List.
From Flocq Require Import IEEE754.Binary IEEE754.BinarySingleNaN.
Import ListNotations.
Open Scope Z_scope.

Definition rows : list SpecFloat.spec_float :=
  [@BinarySingleNaN.binary_round 3 4 mode_NE false 9 (-3);
   @BinarySingleNaN.binary_round 3 4 mode_NA false 9 (-3);
   Binary.FF2SF (@Binary.binary_round 3 4 mode_DN true 9 (-3));
   @BinarySingleNaN.binary_round_aux 3 4 mode_NE true 0 (-4) SpecFloat.loc_Exact;
   Binary.FF2SF (@Binary.binary_round_aux 3 4 mode_NE false (-1) (-4) SpecFloat.loc_Exact);
   Binary.FF2SF (@Binary.binary_round 3 3 mode_NE false 1 0);
   @BinarySingleNaN.binary_round_aux (-1) 1 mode_ZR false (-2) 2 SpecFloat.loc_Exact;
   Binary.FF2SF (@Binary.binary_round_aux 3 4 mode_NA true (-7) (-6) SpecFloat.loc_Exact);
   @BinarySingleNaN.binary_round_aux 3 3 mode_ZR true (-2) (-5) (SpecFloat.loc_Inexact Lt)].

Example raw_ieee_rounding_boundaries : rows =
  [SpecFloat.S754_finite false 4 (-2); SpecFloat.S754_finite false 5 (-2);
   SpecFloat.S754_finite true 5 (-2); SpecFloat.S754_zero true; SpecFloat.S754_nan;
   SpecFloat.S754_finite false 4 (-2); SpecFloat.S754_zero false;
   SpecFloat.S754_zero true; SpecFloat.S754_zero true].
Proof. vm_compute. reflexivity. Qed.
