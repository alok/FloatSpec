From Stdlib Require Import ZArith List Bool.
From Flocq Require Import Core IEEE754.BinarySingleNaN.
Import ListNotations.
Open Scope Z_scope.

Module IntegerOracle.

Definition positive_precision : Prec_gt_0 24 := eq_refl.
Definition precision_below_max : Prec_lt_emax 24 128 := eq_refl.

Definition expected mode numerator :=
  let lower := numerator / 8 in
  let remainder := numerator mod 8 in
  let upper := lower + if Z.eqb remainder 0 then 0 else 1 in
  match mode with
  | mode_DN => lower
  | mode_UP => upper
  | mode_ZR => if numerator <? 0 then upper else lower
  | mode_NE =>
      if remainder <? 4 then lower else if 4 <? remainder then upper
      else if Z.eqb (lower mod 2) 0 then lower else upper
  | mode_NA =>
      if remainder <? 4 then lower else if 4 <? remainder then upper
      else if numerator <? 0 then lower else upper
  end.

Definition observation (x : SpecFloat.spec_float) : list Z :=
  match x with
  | SpecFloat.S754_zero s => [0; if s then 1 else 0; 0; 0]
  | SpecFloat.S754_infinity s => [1; if s then 1 else 0; 0; 0]
  | SpecFloat.S754_nan => [2; 0; 0; 0]
  | SpecFloat.S754_finite s m e => [3; if s then 1 else 0; Zpos m; e]
  end.

Definition check mode numerator :=
  let x := binary_normalize 24 128 positive_precision precision_below_max
    mode_NE numerator (-3) false in
  let y := @Bnearbyint 24 128 precision_below_max mode x in
  let z := @Bnearbyint 24 128 precision_below_max mode y in
  Z.eqb (Btrunc x) (expected mode_ZR numerator) &&
    Z.eqb (Btrunc y) (expected mode numerator) &&
    if list_eq_dec Z.eq_dec (observation (B2SF z)) (observation (B2SF y)) then true else false.

Definition cases := flat_map (fun mode =>
  map (fun n => (mode, Z.of_nat n - 512)) (seq 0 1025))
  [mode_NE; mode_ZR; mode_DN; mode_UP; mode_NA].

Example integer_rounding_oracle_and_idempotence :
  forallb (fun '(mode,n) => check mode n) cases = true.
Proof. vm_compute. reflexivity. Qed.

Eval vm_compute in List.length cases.

End IntegerOracle.

