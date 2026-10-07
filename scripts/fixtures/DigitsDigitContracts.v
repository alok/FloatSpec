From Stdlib Require Import ZArith.
From Flocq Require Import Core.Zaux Core.Digits.
Open Scope Z_scope.

(* Digits.v:28-56: the binary length of a positive, by recursion on its digits. *)
Example digits2_one : digits2_Pnat 1 = O := eq_refl.
Example digits2_even : forall p, digits2_Pnat (xO p) = S (digits2_Pnat p) := fun _ => eq_refl.
Example digits2_odd : forall p, digits2_Pnat (xI p) = S (digits2_Pnat p) := fun _ => eq_refl.
Definition digits2_bounds : forall n,
  Zpower_nat 2 (digits2_Pnat n) <= Zpos n < Zpower_nat 2 (S (digits2_Pnat n)) :=
  digits2_Pnat_correct.

(* Digits.v:57-720. After the section closes, every law takes the radix explicitly. The
   bodies say Zle_bool, a deprecated notation for Z.leb. *)
Example zdigit_body : forall (beta : radix) n k,
  Zdigit beta n k = Z.rem (Z.quot n (Zpower beta k)) beta := fun _ _ _ => eq_refl.
Example zsum_digit_zero : forall (beta : radix) f, Zsum_digit beta f O = Z0 := fun _ _ => eq_refl.
Example zsum_digit_succ : forall (beta : radix) f k,
  Zsum_digit beta f (S k) = Zsum_digit beta f k + f (Z.of_nat k) * Zpower beta (Z.of_nat k) :=
  fun _ _ _ => eq_refl.
Example zscale_body : forall (beta : radix) n k,
  Zscale beta n k = if Z.leb 0 k then n * Zpower beta k else Z.quot n (Zpower beta (- k)) :=
  fun _ _ _ => eq_refl.
Example zslice_body : forall (beta : radix) n k1 k2,
  Zslice beta n k1 k2 = if Z.leb 0 k2 then Z.rem (Zscale beta n (- k1)) (Zpower beta k2) else Z0 :=
  fun _ _ _ _ => eq_refl.

Definition digit_lt : forall (beta : radix) n k, k < 0 -> Zdigit beta n k = Z0 := Zdigit_lt.
Definition digit_zero : forall (beta : radix) k, Zdigit beta 0 k = Z0 := Zdigit_0.
Definition digit_opp : forall (beta : radix) n k, Zdigit beta (- n) k = - Zdigit beta n k :=
  Zdigit_opp.
Definition digit_ge_pos : forall (beta : radix) e n, 0 <= n < Zpower beta e ->
  forall k, e <= k -> Zdigit beta n k = Z0 := Zdigit_ge_Zpower_pos.
Definition digit_ge : forall (beta : radix) e n, Z.abs n < Zpower beta e ->
  forall k, e <= k -> Zdigit beta n k = Z0 := Zdigit_ge_Zpower.
Definition digit_not_0_pos : forall (beta : radix) e n, 0 <= e ->
  Zpower beta e <= n < Zpower beta (e + 1) -> Zdigit beta n e <> Z0 := Zdigit_not_0_pos.
Definition digit_not_0 : forall (beta : radix) e n, 0 <= e ->
  Zpower beta e <= Z.abs n < Zpower beta (e + 1) -> Zdigit beta n e <> Z0 := Zdigit_not_0.
Definition digit_mul_pow : forall (beta : radix) n k k', 0 <= k' ->
  Zdigit beta (n * Zpower beta k') k = Zdigit beta n (k - k') := Zdigit_mul_pow.
Definition digit_div_pow : forall (beta : radix) n k k', 0 <= k -> 0 <= k' ->
  Zdigit beta (Z.quot n (Zpower beta k')) k = Zdigit beta n (k + k') := Zdigit_div_pow.
Definition digit_mod_pow : forall (beta : radix) n k k', k < k' ->
  Zdigit beta (Z.rem n (Zpower beta k')) k = Zdigit beta n k := Zdigit_mod_pow.
Definition digit_mod_pow_out : forall (beta : radix) n k k', 0 <= k' <= k ->
  Zdigit beta (Z.rem n (Zpower beta k')) k = Z0 := Zdigit_mod_pow_out.
Definition sum_digit_digit : forall (beta : radix) n k,
  Zsum_digit beta (Zdigit beta n) k = Z.rem n (Zpower beta (Z.of_nat k)) := Zsum_digit_digit.
Definition digit_ext : forall (beta : radix) n1 n2,
  (forall k, 0 <= k -> Zdigit beta n1 k = Zdigit beta n2 k) -> n1 = n2 := Zdigit_ext.
Definition mod_plus_pow_digit : forall (beta : radix) u v n, 0 <= u * v ->
  (forall k, 0 <= k < n -> Zdigit beta u k = Z0 \/ Zdigit beta v k = Z0) ->
  Z.rem (u + v) (Zpower beta n) = Z.rem u (Zpower beta n) + Z.rem v (Zpower beta n) :=
  ZOmod_plus_pow_digit.
Definition div_plus_pow_digit : forall (beta : radix) u v n, 0 <= u * v ->
  (forall k, 0 <= k < n -> Zdigit beta u k = Z0 \/ Zdigit beta v k = Z0) ->
  Z.quot (u + v) (Zpower beta n) = Z.quot u (Zpower beta n) + Z.quot v (Zpower beta n) :=
  ZOdiv_plus_pow_digit.
Definition digit_plus : forall (beta : radix) u v, 0 <= u * v ->
  (forall k, 0 <= k -> Zdigit beta u k = Z0 \/ Zdigit beta v k = Z0) ->
  forall k, Zdigit beta (u + v) k = Zdigit beta u k + Zdigit beta v k := Zdigit_plus.
Definition digit_scale : forall (beta : radix) n k k', 0 <= k' ->
  Zdigit beta (Zscale beta n k) k' = Zdigit beta n (k' - k) := Zdigit_scale.
Definition scale_zero : forall (beta : radix) k, Zscale beta 0 k = Z0 := Zscale_0.
Definition same_sign_scale : forall (beta : radix) n k, 0 <= n * Zscale beta n k :=
  Zsame_sign_scale.
Definition scale_mul_pow : forall (beta : radix) n k k', 0 <= k ->
  Zscale beta (n * Zpower beta k) k' = Zscale beta n (k + k') := Zscale_mul_pow.
Definition scale_scale : forall (beta : radix) n k k', 0 <= k ->
  Zscale beta (Zscale beta n k) k' = Zscale beta n (k + k') := Zscale_scale.
Definition digit_slice : forall (beta : radix) n k1 k2 k, 0 <= k < k2 ->
  Zdigit beta (Zslice beta n k1 k2) k = Zdigit beta n (k1 + k) := Zdigit_slice.
Definition digit_slice_out : forall (beta : radix) n k1 k2 k, k2 <= k ->
  Zdigit beta (Zslice beta n k1 k2) k = Z0 := Zdigit_slice_out.
Definition slice_zero : forall (beta : radix) k k', Zslice beta 0 k k' = Z0 := Zslice_0.
Definition same_sign_slice : forall (beta : radix) n k k', 0 <= n * Zslice beta n k k' :=
  Zsame_sign_slice.
Definition slice_slice : forall (beta : radix) n k1 k2 k1' k2', 0 <= k1' <= k2 ->
  Zslice beta (Zslice beta n k1 k2) k1' k2' = Zslice beta n (k1 + k1') (Z.min (k2 - k1') k2') :=
  Zslice_slice.
Definition slice_mul_pow : forall (beta : radix) n k k1 k2, 0 <= k ->
  Zslice beta (n * Zpower beta k) k1 k2 = Zslice beta n (k1 - k) k2 := Zslice_mul_pow.
Definition slice_div_pow : forall (beta : radix) n k k1 k2, 0 <= k -> 0 <= k1 ->
  Zslice beta (Z.quot n (Zpower beta k)) k1 k2 = Zslice beta n (k1 + k) k2 := Zslice_div_pow.
Definition slice_scale : forall (beta : radix) n k k1 k2, 0 <= k1 ->
  Zslice beta (Zscale beta n k) k1 k2 = Zslice beta n (k1 - k) k2 := Zslice_scale.
Definition slice_div_pow_scale : forall (beta : radix) n k k1 k2, 0 <= k ->
  Zslice beta (Z.quot n (Zpower beta k)) k1 k2 = Zscale beta (Zslice beta n k (k1 + k2)) (- k1) :=
  Zslice_div_pow_scale.
Definition plus_slice : forall (beta : radix) n k l1 l2, 0 <= l1 -> 0 <= l2 ->
  Zslice beta n k l1 + Zscale beta (Zslice beta n (k + l1) l2) l1 = Zslice beta n k (l1 + l2) :=
  Zplus_slice.

Print Assumptions digits2_bounds.
Print Assumptions digit_plus.
Print Assumptions slice_slice.

Definition radix10 := Build_radix 10 eq_refl.

(* Truncation keeps the sign: digits of a negative number are nonpositive. *)
Example signed_values :
  Zdigit radix10 (-4321) 1 = -2 /\ Zscale radix10 (-4321) (-2) = -43 /\
  Zslice radix10 (-654321) 2 3 = -543 /\ Zsum_digit radix10 (Zdigit radix10 (-654321)) 3 = -321 /\
  digits2_Pnat 8 = 3%nat.
Proof. repeat split; reflexivity. Qed.

(* A negative modulus exponent makes Zpower zero and the remainder the dividend. *)
Example mod_pow_out_needs_nonneg :
  ~ (forall n k k', k' <= k -> Zdigit radix10 (Z.rem n (Zpower radix10 k')) k = Z0).
Proof. intros H. specialize (H 5 0 (-1) ltac:(easy)). discriminate H. Qed.

(* The slice keeps exactly k2 digits: index k2 is already outside. *)
Example digit_slice_needs_bound :
  ~ (forall n k1 k2 k, 0 <= k <= k2 -> Zdigit radix10 (Zslice radix10 n k1 k2) k = Zdigit radix10 n (k1 + k)).
Proof. intros H. specialize (H 123 0 1 1 ltac:(easy)). discriminate H. Qed.

Print Assumptions mod_pow_out_needs_nonneg.
