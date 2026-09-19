From Stdlib Require Import ZArith List Lia.
From Flocq Require Import IEEE754.BinarySingleNaN.
Import ListNotations.
Open Scope Z_scope.

Definition units (x : SpecFloat.spec_float) : option Z :=
  match x with
  | SpecFloat.S754_zero _ => Some 0
  | SpecFloat.S754_finite sign m e =>
      if Z.leb (-8) e then
        let magnitude := Z.pos m * 2 ^ (e + 8) in
        Some (if sign then -magnitude else magnitude)
      else None
  | _ => None
  end.

Definition bound (mode : mode) (sign : bool) (k : nat) : bool :=
  let m := Z.of_nat (S k) in
  let x := if sign then -m else m in
  match units (binary_round 3 4 mode sign (Pos.of_nat (S k)) (-8)) with
  | None => false
  | Some y => if Z.leb 64 m then Z.leb (8 * Z.abs (y - x)) m
              else Z.leb (Z.abs (y - x)) 8
  end.

Example finite_nearest_grid :
  forallb (fun mode => forallb (fun sign => forallb (bound mode sign) (seq 0 1023))
    [false; true]) [mode_NE; mode_NA] = true.
Proof. vm_compute. reflexivity. Qed.

Example underflow_requires_absolute_term :
  units (binary_round 3 4 mode_NE false 1 (-8)) = Some 0 /\
  ~ (8 * Z.abs (0 - 1) <= 1).
Proof. split; [vm_compute; reflexivity | simpl; lia]. Qed.
