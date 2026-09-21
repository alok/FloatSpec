From Stdlib Require Import ZArith List Lia Bool.
From Flocq Require Import Core.Zaux.
Import ListNotations.
Open Scope Z_scope.
Open Scope bool_scope.

Definition floor_nested_contract : forall n a b, 0 < a -> 0 <= b ->
  (n mod (a*b)) mod b = n mod b := Zmod_mod_mult.
Definition floor_division_contract : forall n a b, 0 <= a -> 0 <= b ->
  (n mod (a*b)) / a = (n / a) mod b := Zdiv_mod_mult.
Definition trunc_decomposition_contract : forall a b,
  Z.rem a b = a - Z.quot a b * b := ZOmod_eq.
Definition trunc_nested_contract : forall n a b,
  Z.rem (Z.rem n (a*b)) b = Z.rem n b := ZOmod_mod_mult.
Definition trunc_division_contract : forall n a b,
  Z.quot (Z.rem n (a*b)) a = Z.rem (Z.quot n a) b := ZOdiv_mod_mult.
Definition small_quotient_contract : forall a b, Z.abs a < b -> Z.quot a b = 0 := ZOdiv_small_abs.
Definition small_remainder_contract : forall a b, Z.abs a < b -> Z.rem a b = a := ZOmod_small_abs.
Definition trunc_addition_contract : forall a b c, 0 <= a*b ->
  Z.quot (a+b) c = Z.quot a c + Z.quot b c + Z.quot (Z.rem a c + Z.rem b c) c := ZOdiv_plus.

(* Unlike Lean's default Euclidean division, negative divisor gives floor -3. *)
Example negative_floor_divisor : 7 / (-3) = -3 /\ 7 mod (-3) = -2.
Proof. vm_compute. auto. Qed.
Example negative_trunc_dividend : Z.quot (-7) 3 = -2 /\ Z.rem (-7) 3 = -1.
Proof. vm_compute. auto. Qed.
Example zero_divisor : forall a, Z.quot a 0 = 0 /\ Z.rem a 0 = a.
Proof. intros [|p|p]; split; reflexivity. Qed.
Example quotient_addition_needs_sign_condition :
  ~ forall a b c, Z.quot (a+b) c = Z.quot a c + Z.quot b c + Z.quot (Z.rem a c + Z.rem b c) c.
Proof. intro H. specialize (H (-2) 1 2). vm_compute in H. discriminate. Qed.

Definition division_laws n a b :=
  Z.eqb (Z.rem n a) (n - Z.quot n a * a) &&
  Z.eqb (Z.rem (Z.rem n (a*b)) b) (Z.rem n b) &&
  Z.eqb (Z.quot (Z.rem n (a*b)) a) (Z.rem (Z.quot n a) b) &&
  (if Z.leb 0 a && Z.leb 0 b then Z.eqb ((n mod (a*b)) / a) ((n/a) mod b) else true) &&
  (if Z.leb 0 (n*a) then
    Z.eqb (Z.quot (n+a) b) (Z.quot n b + Z.quot a b + Z.quot (Z.rem n b + Z.rem a b) b)
    else true).
Example signed_division_grid :
  forallb (fun n => forallb (fun a => forallb (fun b =>
    division_laws (Z.of_nat n - 8) (Z.of_nat a - 4) (Z.of_nat b - 4)) (seq 0 9))
    (seq 0 9)) (seq 0 17) = true.
Proof. vm_compute. reflexivity. Qed.
