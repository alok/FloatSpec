From Stdlib Require Import ZArith Reals Lra.
From Flocq Require Import Core.Zaux Core.Raux.
Open Scope R_scope.

(* Raux.v:1331-1582. After the section closes, every law takes the radix explicitly. *)
Example bpow_body : forall (r : radix) e, bpow r e =
  match e with
  | Zpos p => IZR (Zpower_pos r p)
  | Zneg p => Rinv (IZR (Zpower_pos r p))
  | Z0 => 1%R
  end := fun r e => eq_refl.

Definition radix_positive : forall r : radix, 0 < IZR r := radix_pos.
Definition izr_zpower_pos : forall n m, IZR (Zpower_pos n m) = powerRZ (IZR n) (Zpos m) :=
  IZR_Zpower_pos.
Definition bpow_is_powerRZ : forall (r : radix) e, bpow r e = powerRZ (IZR r) e := bpow_powerRZ.
Definition bpow_nonneg : forall (r : radix) e, 0 <= bpow r e := bpow_ge_0.
Definition bpow_positive : forall (r : radix) e, 0 < bpow r e := bpow_gt_0.
Definition bpow_add : forall (r : radix) e1 e2, bpow r (e1 + e2) = bpow r e1 * bpow r e2 :=
  bpow_plus.
Definition bpow_one : forall r : radix, bpow r 1 = IZR r := bpow_1.
Definition bpow_succ : forall (r : radix) e, bpow r (e + 1) = IZR r * bpow r e := bpow_plus_1.
Definition bpow_neg : forall (r : radix) e, bpow r (- e) = / bpow r e := bpow_opp.
Definition izr_zpower_nat : forall (r : radix) e, IZR (Zpower_nat r e) = bpow r (Z.of_nat e) :=
  IZR_Zpower_nat.
Definition izr_zpower : forall (r : radix) e, (0 <= e)%Z -> IZR (Zpower r e) = bpow r e :=
  IZR_Zpower.
Definition bpow_strict : forall (r : radix) e1 e2, (e1 < e2)%Z -> bpow r e1 < bpow r e2 := bpow_lt.
Definition bpow_strict_inv : forall (r : radix) e1 e2, bpow r e1 < bpow r e2 -> (e1 < e2)%Z :=
  lt_bpow.
Definition bpow_mono : forall (r : radix) e1 e2, (e1 <= e2)%Z -> bpow r e1 <= bpow r e2 := bpow_le.
Definition bpow_mono_inv : forall (r : radix) e1 e2, bpow r e1 <= bpow r e2 -> (e1 <= e2)%Z :=
  le_bpow.
Definition bpow_injective : forall (r : radix) e1 e2, bpow r e1 = bpow r e2 -> e1 = e2 := bpow_inj.
Definition bpow_exponential : forall (r : radix) e, bpow r e = exp (IZR e * ln (IZR r)) := bpow_exp.
Definition bpow_sqrt : forall (r : radix) e, sqrt (bpow r (2 * e)) = bpow r e := sqrt_bpow.
Definition bpow_sqrt_ge : forall (r : radix) e, bpow r (e / 2) <= sqrt (bpow r e) := sqrt_bpow_ge.

Print Assumptions bpow_mono.
Print Assumptions bpow_exponential.

(* Concrete values: negative exponents are reciprocals, not truncations. *)
Example bpow_values : bpow radix2 (-3) = / 8 /\ bpow (Build_radix 10 eq_refl) 2 = 100.
Proof. split; reflexivity. Qed.

(* Rocq's radix record carries 2 <= r, so a zero radix cannot be formed; Lean's unbundled
   radix needs the explicit 1 < beta instead. *)
Example radix_excludes_zero : forall r : radix, radix_val r <> 0%Z.
Proof. intros [v Hv] H. simpl in H. subst v. discriminate Hv. Qed.
