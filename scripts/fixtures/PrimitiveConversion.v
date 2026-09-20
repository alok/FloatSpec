From Stdlib Require Import ZArith List Floats Uint63.
From Flocq Require Import IEEE754.PrimFloat IEEE754.BinarySingleNaN.
Import ListNotations.
Open Scope Z_scope.

Definition inputs : list SpecFloat.spec_float :=
  [SpecFloat.S754_finite false 3 (-1);
   SpecFloat.S754_finite false 9223372036854775808 (0);
   SpecFloat.S754_finite false 9223372036854775809 (0);
   SpecFloat.S754_finite false 9223372036854775807 (0);
   SpecFloat.S754_finite false 9007199254740997 (-1077);
   SpecFloat.S754_zero false;
   SpecFloat.S754_infinity false;
   SpecFloat.S754_finite false 4503599627370496 (-52);
   SpecFloat.S754_finite false 1 (-1074);
   SpecFloat.S754_finite false 9007199254740991 (971);
   SpecFloat.S754_finite false 1 (-1075);
   SpecFloat.S754_finite false 3 (-1075);
   SpecFloat.S754_finite false 1 (1024);
   SpecFloat.S754_finite false 1 (-1000000000000000000000000000000);
   SpecFloat.S754_finite false 1 (1000000000000000000000000000000);
   SpecFloat.S754_finite true 3 (-1);
   SpecFloat.S754_finite true 9223372036854775808 (0);
   SpecFloat.S754_finite true 9223372036854775809 (0);
   SpecFloat.S754_finite true 9223372036854775807 (0);
   SpecFloat.S754_finite true 9007199254740997 (-1077);
   SpecFloat.S754_zero true;
   SpecFloat.S754_infinity true;
   SpecFloat.S754_finite true 4503599627370496 (-52);
   SpecFloat.S754_finite true 1 (-1074);
   SpecFloat.S754_finite true 9007199254740991 (971);
   SpecFloat.S754_finite true 1 (-1075);
   SpecFloat.S754_finite true 3 (-1075);
   SpecFloat.S754_finite true 1 (1024);
   SpecFloat.S754_finite true 1 (-1000000000000000000000000000000);
   SpecFloat.S754_finite true 1 (1000000000000000000000000000000);
   SpecFloat.S754_nan].

Definition expected : list SpecFloat.spec_float :=
  [SpecFloat.S754_finite false 6755399441055744 (-52);
   SpecFloat.S754_zero false;
   SpecFloat.S754_finite false 4503599627370496 (-52);
   SpecFloat.S754_finite false 4503599627370496 (11);
   SpecFloat.S754_finite false 1125899906842624 (-1074);
   SpecFloat.S754_zero false;
   SpecFloat.S754_infinity false;
   SpecFloat.S754_finite false 4503599627370496 (-52);
   SpecFloat.S754_finite false 1 (-1074);
   SpecFloat.S754_finite false 9007199254740991 (971);
   SpecFloat.S754_zero false;
   SpecFloat.S754_finite false 2 (-1074);
   SpecFloat.S754_infinity false;
   SpecFloat.S754_zero false;
   SpecFloat.S754_infinity false;
   SpecFloat.S754_finite true 6755399441055744 (-52);
   SpecFloat.S754_zero true;
   SpecFloat.S754_finite true 4503599627370496 (-52);
   SpecFloat.S754_finite true 4503599627370496 (11);
   SpecFloat.S754_finite true 1125899906842624 (-1074);
   SpecFloat.S754_zero true;
   SpecFloat.S754_infinity true;
   SpecFloat.S754_finite true 4503599627370496 (-52);
   SpecFloat.S754_finite true 1 (-1074);
   SpecFloat.S754_finite true 9007199254740991 (971);
   SpecFloat.S754_zero true;
   SpecFloat.S754_finite true 2 (-1074);
   SpecFloat.S754_infinity true;
   SpecFloat.S754_zero true;
   SpecFloat.S754_infinity true;
   SpecFloat.S754_nan].

Definition outputs := map (fun x => FloatOps.Prim2SF (FloatOps.SF2Prim x)) inputs.
Example literal_conversions : outputs = expected.
Proof. vm_compute. reflexivity. Qed.

Example numeric_conversion_is_not_validation :
    FloatOps.Prim2SF (FloatOps.SF2Prim (SpecFloat.S754_finite false 3 (-1))) <>
      @BinarySingleNaN.B2SF 53 1024
        (@BinarySingleNaN.SF2B' 53 1024 (SpecFloat.S754_finite false 3 (-1))).
Proof. vm_compute. discriminate. Qed.

Example two_roundings_are_not_one :
    FloatOps.Prim2SF (FloatOps.SF2Prim (SpecFloat.S754_finite false 9007199254740997 (-1077))) =
      SpecFloat.S754_finite false 1125899906842624 (-1074) /\
    SpecFloat.binary_normalize 53 1024 9007199254740997 (-1077) false =
      SpecFloat.S754_finite false 1125899906842625 (-1074).
Proof. vm_compute. split; reflexivity. Qed.
