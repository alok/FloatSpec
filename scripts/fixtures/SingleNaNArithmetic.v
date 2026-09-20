From Stdlib Require Import ZArith List.
From Flocq Require Import IEEE754.BinarySingleNaN.
Import ListNotations.
Open Scope Z_scope.

Definition one := @BinarySingleNaN.SF2B' 1 2 (SpecFloat.S754_finite false 1 0).
Definition two := @BinarySingleNaN.SF2B' 1 2 (SpecFloat.S754_finite false 1 1).
Definition negTwo := @BinarySingleNaN.SF2B' 1 2 (SpecFloat.S754_finite true 1 1).

Definition row (m : mode) : list SpecFloat.spec_float :=
  map (@BinarySingleNaN.B2SF 1 2)
    [@Bplus 1 2 eq_refl eq_refl m two one;
     @Bminus 1 2 eq_refl eq_refl m one one;
     @Bmult 1 2 eq_refl eq_refl m two two;
     @Bdiv 1 2 eq_refl eq_refl m one two;
     @Bsqrt 1 2 eq_refl eq_refl m two;
     @Bfma 1 2 eq_refl eq_refl m two two negTwo].

Example one_bit_arithmetic : map row [mode_NE; mode_ZR; mode_DN; mode_UP; mode_NA] =
  [[SpecFloat.S754_infinity false; SpecFloat.S754_zero false; SpecFloat.S754_infinity false;
    SpecFloat.S754_zero false; SpecFloat.S754_finite false 1 0; SpecFloat.S754_finite false 1 1];
   [SpecFloat.S754_finite false 1 1; SpecFloat.S754_zero false; SpecFloat.S754_finite false 1 1;
    SpecFloat.S754_zero false; SpecFloat.S754_finite false 1 0; SpecFloat.S754_finite false 1 1];
   [SpecFloat.S754_finite false 1 1; SpecFloat.S754_zero true; SpecFloat.S754_finite false 1 1;
    SpecFloat.S754_zero false; SpecFloat.S754_finite false 1 0; SpecFloat.S754_finite false 1 1];
   [SpecFloat.S754_infinity false; SpecFloat.S754_zero false; SpecFloat.S754_infinity false;
    SpecFloat.S754_finite false 1 0; SpecFloat.S754_finite false 1 1; SpecFloat.S754_finite false 1 1];
   [SpecFloat.S754_infinity false; SpecFloat.S754_zero false; SpecFloat.S754_infinity false;
    SpecFloat.S754_finite false 1 0; SpecFloat.S754_finite false 1 0; SpecFloat.S754_finite false 1 1]].
Proof. vm_compute. reflexivity. Qed.
