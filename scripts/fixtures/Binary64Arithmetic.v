From Stdlib Require Import ZArith List.
From Flocq Require Import Core.FLX IEEE754.Binary IEEE754.BinarySingleNaN IEEE754.Bits.
Import ListNotations.
Open Scope Z_scope.

Definition one : binary64 := b64_of_bits 4607182418800017408.
Definition two : binary64 := b64_of_bits 4611686018427387904.
Definition max_finite : binary64 := b64_of_bits 9218868437227405311.

#[local] Instance prec64 : Prec_gt_0 53 := eq_refl.
#[local] Instance emax64 : Prec_lt_emax 53 1024 := eq_refl.

Definition rows : list Z :=
  [bits_of_b64 (b64_plus mode_NE one two);
   bits_of_b64 (b64_mult mode_NE max_finite two);
   bits_of_b64 (Binary.Bmult 53 1024 _ _ binop_nan_pl64 mode_NE (Binary.Bmax_float 53 1024 _ _) two);
   bits_of_b64 (Binary.Bmax_float 53 1024 _ _)].

Example binary64_boundaries : rows =
  [4613937818241073152; 9218868437227405312; 9218868437227405312;
   9218868437227405311].
Proof. vm_compute. reflexivity. Qed.

Definition neg_nan : binary64 := b64_of_bits 18444492273895866368.
Definition pos_zero : binary64 := b64_of_bits 0.
Definition neg_zero : binary64 := b64_of_bits 9223372036854775808.

Example neg_nan_sign : Binary.Bsign 53 1024 neg_nan = true.
Proof. vm_compute. reflexivity. Qed.

Example fma_szero_nan_sign :
  Binary.Bfma_szero 53 1024 mode_NE neg_nan pos_zero neg_zero = false.
Proof. vm_compute. reflexivity. Qed.
