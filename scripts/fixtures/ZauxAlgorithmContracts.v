From Stdlib Require Import ZArith List Lia Bool.
From Flocq Require Import Core.Zaux.
Import ListNotations.
Open Scope Z_scope.
Open Scope bool_scope.

(* Zeq_bool and Zlt_bool are deprecated Stdlib notations for Z.eqb and Z.ltb. *)
Definition cond_zero : forall sx, cond_Zopp sx 0 = 0 := cond_Zopp_0.
Definition cond_negb : forall x y, cond_Zopp (negb x) y = - cond_Zopp x y := cond_Zopp_negb.
Definition cond_abs : forall b m, Z.abs (cond_Zopp b m) = Z.abs m := abs_cond_Zopp.
Definition cond_lt : forall m, cond_Zopp (Z.ltb m 0) m = Z.abs m := cond_Zopp_Zlt_bool.
Definition cond_eq : forall s m n,
  Z.eqb (cond_Zopp s m) n = Z.eqb m (cond_Zopp s n) := Zeq_bool_cond_Zopp.

Example pow_one : forall v, Zfast_pow_pos v xH = v := fun v => eq_refl.
Example pow_even : forall v e,
  Zfast_pow_pos v (xO e) = Z.square (Zfast_pow_pos v e) := fun v e => eq_refl.
Example pow_odd : forall v e,
  Zfast_pow_pos v (xI e) = v * Z.square (Zfast_pow_pos v e) := fun v e => eq_refl.
Definition fast_pow : forall v e, Zfast_pow_pos v e = Z.pow_pos v e := Zfast_pow_pos_correct.

Definition div_eucl_unique : forall a b,
  Z.div_eucl a b = (a / b, a mod b) := Zdiv_eucl_unique.
Example aux1_one : forall a, Zpos_div_eucl_aux1 a xH = (Zpos a, 0) := fun a => eq_refl.
Example aux1_odd : forall a b,
  Zpos_div_eucl_aux1 a (xI b) = Z.pos_div_eucl a (Zpos (xI b)) := fun a b => eq_refl.
Example aux1_small : forall b, Zpos_div_eucl_aux1 xH (xO b) = (0, Zpos xH) := fun b => eq_refl.
Example aux1_even : forall a b,
  Zpos_div_eucl_aux1 (xO a) (xO b) = let (q, r) := Zpos_div_eucl_aux1 a b in (q, 2 * r) :=
  fun a b => eq_refl.
Example aux1_odd_dividend : forall a b,
  Zpos_div_eucl_aux1 (xI a) (xO b) = let (q, r) := Zpos_div_eucl_aux1 a b in (q, 2 * r + 1) :=
  fun a b => eq_refl.
Definition aux1_correct : forall a b,
  Zpos_div_eucl_aux1 a b = Z.pos_div_eucl a (Zpos b) := Zpos_div_eucl_aux1_correct.
Definition aux_correct : forall a b,
  Zpos_div_eucl_aux a b = Z.pos_div_eucl a (Zpos b) := Zpos_div_eucl_aux_correct.
Definition fast_div : forall a b, Zfast_div_eucl a b = Z.div_eucl a b := Zfast_div_eucl_correct.

Example zero_divisor : 1 mod 0 = 1 /\ Zfast_div_eucl 7 0 = (0, 7) /\ Zfast_div_eucl (-7) 0 = (0, -7).
Proof. vm_compute. auto. Qed.

Example iter_unfold : forall (A : Type) (f : A -> A) n x,
  iter_nat f (S n) x = iter_nat f n (f x) := fun A f n x => eq_refl.
Definition iter_plus : forall (A : Type) (f : A -> A) p q x,
  iter_nat f (p + q) x = iter_nat f p (iter_nat f q x) := @iter_nat_plus.
Definition iter_S : forall (A : Type) (f : A -> A) p x,
  iter_nat f (S p) x = f (iter_nat f p x) := @iter_nat_S.
Definition iter_pos_eq : forall (A : Type) (f : A -> A) p x,
  iter_pos f p x = iter_nat f (Pos.to_nat p) x := @iter_pos_nat.

Print Assumptions fast_div.
Print Assumptions aux1_correct.
Print Assumptions fast_pow.
Print Assumptions iter_plus.
Print Assumptions cond_lt.

Example cond_lt_needs_orientation : ~ forall m, cond_Zopp (Z.ltb 0 m) m = Z.abs m.
Proof. intro H. specialize (H 1). discriminate H. Qed.
Example cond_eq_needs_negation : ~ forall s m n, Z.eqb (cond_Zopp s m) n = Z.eqb m n.
Proof. intro H. specialize (H true 1 (-1)). discriminate H. Qed.
Example fast_div_floor : Zfast_div_eucl 7 (-3) = (-3, -2).
Proof. vm_compute. reflexivity. Qed.
Print Assumptions cond_lt_needs_orientation.
Print Assumptions cond_eq_needs_negation.
Print Assumptions fast_div_floor.

Definition signed_values :=
  map (fun k => Z.of_nat k - 8) (seq 0 17) ++ [-2^64 - 1; -2^63; 2^63 - 1; 2^64 + 1].

Definition pair_eqb (p q : Z * Z) := Z.eqb (fst p) (fst q) && Z.eqb (snd p) (snd q).

Definition algorithm_laws x y :=
  pair_eqb (Zfast_div_eucl x y) (Z.div_eucl x y) &&
  Z.eqb (cond_Zopp (Z.ltb x 0) x) (Z.abs x) &&
  Z.eqb (Z.abs (cond_Zopp true x)) (Z.abs x).

Example signed_algorithm_grid :
  forallb (fun x => forallb (fun y => algorithm_laws x y) signed_values) signed_values = true.
Proof. vm_compute. reflexivity. Qed.

Example power_grid :
  forallb (fun v => forallb (fun n =>
    Z.eqb (Zfast_pow_pos v (Pos.of_nat (S n))) (v ^ Z.of_nat (S n))) (seq 0 20))
    (map (fun k => Z.of_nat k - 8) (seq 0 17)) = true.
Proof. vm_compute. reflexivity. Qed.
