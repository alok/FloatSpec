From Stdlib Require Import ZArith List Lia.
From Flocq Require Import Core.Zaux.
Import ListNotations.
Open Scope Z_scope.

Definition parity_contract : forall x, exists p, x = 2*p + if Z.even x then 0 else 1 := Zeven_ex.
Definition power_add_contract : forall n k1 k2, 0 <= k1 -> 0 <= k2 ->
  Zpower n (k1+k2) = Zpower n k1 * Zpower n k2 := Zpower_plus.
Definition power_nat_contract : forall b e, 0 <= e ->
  Zpower b e = Zpower_nat b (Z.abs_nat e) := Zpower_Zpower_nat.
Definition power_succ_contract : forall b e, Zpower_nat b (S e) = b * Zpower_nat b e := Zpower_nat_S.
Definition positive_power_contract : forall b p, 0 < b -> 0 < Zpower_pos b p := Zpower_pos_gt_0.
Definition odd_power_contract : forall b e, 0 <= e -> Z.even b = false ->
  Z.even (Zpower b e) = false := Zeven_Zpower_odd.

(* The source spells the definitionally identical comparison Zle_bool. *)
Definition radix_field_contract : forall r : radix, Z.leb 2 (radix_val r) = true := radix_prop.
Definition radix_build_contract : forall value, Z.leb 2 value = true -> radix := Build_radix.
Definition radix_inj_contract : forall r1 r2 : radix, radix_val r1 = radix_val r2 -> r1 = r2 := radix_val_inj.
Example binary_radix_contract : radix_val radix2 = 2. Proof. reflexivity. Qed.
Definition radix_positive_contract : forall r : radix, 0 < r := radix_gt_0.
Definition radix_gt_one_contract : forall r : radix, 1 < r := radix_gt_1.
Definition power_gt_one_contract : forall (r : radix) p, 0 < p -> 1 < Zpower r p := Zpower_gt_1.
Definition power_positive_contract : forall (r : radix) p, 0 <= p -> 0 < Zpower r p := Zpower_gt_0.
Definition power_nonnegative_contract : forall (r : radix) e, 0 <= Zpower r e := Zpower_ge_0.
Definition power_le_contract : forall (r : radix) e1 e2, e1 <= e2 ->
  Zpower r e1 <= Zpower r e2 := Zpower_le.
Definition power_lt_contract : forall (r : radix) e1 e2, 0 <= e2 -> e1 < e2 ->
  Zpower r e1 < Zpower r e2 := Zpower_lt.
Definition power_inverse_contract : forall (r : radix) e1 e2,
  Zpower r (e1-1) < Zpower r e2 -> e1 <= e2 := Zpower_lt_Zpower.
Definition power_dominates_contract : forall (r : radix) n, n < Zpower r n := Zpower_gt_id.

Example negative_integer_powers : Zpower 2 (-2) = 0 /\ Zpower 2 (-1) = 0.
Proof. vm_compute. auto. Qed.
Example strict_order_requires_nonnegative_upper :
  ~ forall a b : Z, a < b -> Zpower 2 a < Zpower 2 b.
Proof. intro H. specialize (H (-2) (-1) ltac:(lia)). vm_compute in H. discriminate. Qed.
Example literal_boundaries :
  [Zpower 0 0; Zpower 0 (-1); Zpower (-2) 3; Zpower (-2) (-3); Zpower 2 0] =
  [1; 0; -8; 0; 1].
Proof. vm_compute. reflexivity. Qed.
