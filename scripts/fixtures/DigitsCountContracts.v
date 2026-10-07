From Stdlib Require Import ZArith.
From Stdlib Require SpecFloat.
From Flocq Require Import Core.Zaux Core.Digits.
Open Scope Z_scope.

(* Digits.v:722-1176. After both sections close, Zdigits_aux takes the radix, then p. The
   bodies say Zlt_bool and Zmult, notations for Z.ltb and Z.mul. *)
Example zdigits_aux_zero : forall (beta : radix) p nb pow, Zdigits_aux beta p nb pow O = nb :=
  fun _ _ _ _ => eq_refl.
Example zdigits_aux_succ : forall (beta : radix) p nb pow n,
  Zdigits_aux beta p nb pow (S n) =
    if Z.ltb p pow then nb else Zdigits_aux beta p (nb + 1) (beta * pow) n :=
  fun _ _ _ _ _ => eq_refl.
Example zdigits_body : forall (beta : radix) n,
  Zdigits beta n =
    match n with
    | Z0 => Z0
    | Zneg p => Zdigits_aux beta (Zpos p) 1 beta (digits2_Pnat p)
    | Zpos p => Zdigits_aux beta n 1 beta (digits2_Pnat p)
    end := fun _ _ => eq_refl.

Definition correct : forall (beta : radix) n,
  Zpower beta (Zdigits beta n - 1) <= Z.abs n < Zpower beta (Zdigits beta n) := Zdigits_correct.
Definition unique : forall (beta : radix) n d,
  Zpower beta (d - 1) <= Z.abs n < Zpower beta d -> Zdigits beta n = d := Zdigits_unique.
Definition abs' : forall (beta : radix) n, Zdigits beta (Z.abs n) = Zdigits beta n := Zdigits_abs.
Definition opp : forall (beta : radix) n, Zdigits beta (Z.opp n) = Zdigits beta n := Zdigits_opp.
Definition cond_opp : forall (beta : radix) s n, Zdigits beta (cond_Zopp s n) = Zdigits beta n :=
  Zdigits_cond_Zopp.
Definition gt_0 : forall (beta : radix) n, n <> Z0 -> 0 < Zdigits beta n := Zdigits_gt_0.
Definition ge_0 : forall (beta : radix) n, 0 <= Zdigits beta n := Zdigits_ge_0.
Definition digit_out : forall (beta : radix) n k, Zdigits beta n <= k -> Zdigit beta n k = Z0 :=
  Zdigit_out.
Definition digit_digits : forall (beta : radix) n, n <> Z0 ->
  Zdigit beta n (Zdigits beta n - 1) <> Z0 := Zdigit_digits.
Definition slice : forall (beta : radix) n k l, 0 <= l -> Zdigits beta (Zslice beta n k l) <= l :=
  Zdigits_slice.
Definition mult_Zpower : forall (beta : radix) m e, m <> Z0 -> 0 <= e ->
  Zdigits beta (m * Zpower beta e) = Zdigits beta m + e := Zdigits_mult_Zpower.
Definition of_Zpower : forall (beta : radix) e, 0 <= e -> Zdigits beta (Zpower beta e) = e + 1 :=
  Zdigits_Zpower.
Definition le : forall (beta : radix) x y, 0 <= x -> x <= y -> Zdigits beta x <= Zdigits beta y :=
  Zdigits_le.
Definition lt : forall (beta : radix) x y, 0 <= y -> Zdigits beta x < Zdigits beta y -> x < y :=
  lt_Zdigits.
Definition pow_le : forall (beta : radix) e x, e < Zdigits beta x -> Zpower beta e <= Z.abs x :=
  Zpower_le_Zdigits.
Definition le_pow : forall (beta : radix) e x, Z.abs x < Zpower beta e -> Zdigits beta x <= e :=
  Zdigits_le_Zpower.
Definition pow_gt : forall (beta : radix) e x, Zdigits beta x <= e -> Z.abs x < Zpower beta e :=
  Zpower_gt_Zdigits.
Definition gt_pow : forall (beta : radix) e x, Zpower beta e <= Z.abs x -> e < Zdigits beta x :=
  Zdigits_gt_Zpower.
Definition mult_strong : forall (beta : radix) x y, 0 <= x -> 0 <= y ->
  Zdigits beta (x + y + x * y) <= Zdigits beta x + Zdigits beta y := Zdigits_mult_strong.
Definition mult : forall (beta : radix) x y, Zdigits beta (x * y) <= Zdigits beta x + Zdigits beta y :=
  Zdigits_mult.
Definition mult_ge : forall (beta : radix) x y, x <> 0 -> y <> 0 ->
  Zdigits beta x + Zdigits beta y - 1 <= Zdigits beta (x * y) := Zdigits_mult_ge.
Definition div_Zpower : forall (beta : radix) m e, 0 <= m -> 0 <= e <= Zdigits beta m ->
  Zdigits beta (m / Zpower beta e) = Zdigits beta m - e := Zdigits_div_Zpower.
Definition succ_le : forall (beta : radix) x, 0 <= x -> Zdigits beta (x + 1) <= Zdigits beta x + 1 :=
  Zdigits_succ_le.
Definition binary_length : forall m : positive,
  Z.of_nat (S (digits2_Pnat m)) = Zdigits radix2 (Zpos m) := Z_of_nat_S_digits2_Pnat.
(* Zdigits2 is SpecFloat's binary digit count. *)
Definition binary_digits : forall n, SpecFloat.Zdigits2 n = Zdigits radix2 n := Zdigits2_Zdigits.

Print Assumptions correct.
Print Assumptions mult_ge.
Print Assumptions div_Zpower.

Definition radix10 := Build_radix 10 eq_refl.
Definition radix16 := Build_radix 16 eq_refl.

(* Counts by sign and at powers: 999 has three decimal digits, 1000 four. *)
Example counts :
  Zdigits radix10 0 = 0 /\ Zdigits radix10 (-999) = 3 /\ Zdigits radix10 1000 = 4 /\
  Zdigits radix2 (2 ^ 64) = 65 /\ Zdigits radix16 (- (16 ^ 32 - 1)) = 32.
Proof. repeat split; reflexivity. Qed.

(* The radix record carries 2 <= beta, so radix 1 cannot be formed; Lean needs 1 < beta. *)
Example radix_excludes_one : forall r : radix, radix_val r <> 1.
Proof. intros [v Hv] H. simpl in H. subst v. discriminate Hv. Qed.

(* Zdigits_le needs a nonnegative smaller argument: -1000 has more digits than 1. *)
Example le_needs_nonneg : ~ (forall x y, x <= y -> Zdigits radix10 x <= Zdigits radix10 y).
Proof. intros H. specialize (H (-1000) 1 ltac:(easy)). apply H. reflexivity. Qed.

Print Assumptions le_needs_nonneg.
