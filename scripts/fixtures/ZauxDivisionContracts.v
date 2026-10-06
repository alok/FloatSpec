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

Definition same_sign_trans_contract : forall v u w, v <> 0 ->
  0 <= u*v -> 0 <= v*w -> 0 <= u*w := Zsame_sign_trans.
Definition same_sign_trans_weak_contract : forall v u w, (v = 0 -> w = 0) ->
  0 <= u*v -> 0 <= v*w -> 0 <= u*w := Zsame_sign_trans_weak.
Definition same_sign_imp_contract : forall u v,
  (0 < u -> 0 <= v) -> (0 < -u -> 0 <= -v) -> 0 <= u*v := Zsame_sign_imp.
Definition same_sign_odiv_contract : forall u v, 0 <= v ->
  0 <= u * Z.quot u v := Zsame_sign_odiv.

Print Assumptions same_sign_trans_contract.
Print Assumptions same_sign_trans_weak_contract.
Print Assumptions same_sign_imp_contract.
Print Assumptions same_sign_odiv_contract.

Example same_sign_trans_needs_zero_condition :
  ~ forall v u w : Z, 0 <= u*v -> 0 <= v*w -> 0 <= u*w.
Proof. intro H. specialize (H 0 1 (-1)). lia. Qed.
Example same_sign_odiv_needs_nonnegative_divisor :
  ~ forall u v : Z, 0 <= u * Z.quot u v.
Proof. intro H. specialize (H 1 (-1)). change (0 <= -1)%Z in H. lia. Qed.
Print Assumptions same_sign_trans_needs_zero_condition.
Print Assumptions same_sign_odiv_needs_nonnegative_divisor.

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

Definition same_sign_laws n a b :=
  (if negb (Z.eqb n 0) && Z.leb 0 (a*n) && Z.leb 0 (n*b)
    then Z.leb 0 (a*b) else true) &&
  (if (negb (Z.eqb n 0) || Z.eqb b 0) && Z.leb 0 (a*n) && Z.leb 0 (n*b)
    then Z.leb 0 (a*b) else true) &&
  (if (Z.leb n 0 || Z.leb 0 a) && (Z.leb (-n) 0 || Z.leb 0 (-a))
    then Z.leb 0 (n*a) else true) &&
  (if Z.leb 0 a then Z.leb 0 (n * Z.quot n a) else true).

Example signed_division_grid :
  forallb (fun n => forallb (fun a => forallb (fun b =>
    division_laws (Z.of_nat n - 8) (Z.of_nat a - 4) (Z.of_nat b - 4) &&
    same_sign_laws (Z.of_nat n - 8) (Z.of_nat a - 4) (Z.of_nat b - 4)) (seq 0 9))
    (seq 0 9)) (seq 0 17) = true.
Proof. vm_compute. reflexivity. Qed.
