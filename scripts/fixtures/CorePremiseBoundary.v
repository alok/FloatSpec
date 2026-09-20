From Stdlib Require Import Reals ZArith.
From Flocq Require Import Core.Core.
Open Scope R_scope.

(* Typed source clients paired with the Lean premise-boundary fixture. *)

Definition Ulp_negligible_exp_spec_unrestricted :
  forall fexp : Z -> Z, negligible_exp_prop fexp (negligible_exp fexp) := @Ulp.negligible_exp_spec.
Print Assumptions Ulp_negligible_exp_spec_unrestricted.

Definition Ulp_negligible_exp_spec_prime_unrestricted :
  forall fexp : Z -> Z, negligible_exp fexp = None /\ (forall n : Z, (fexp n < n)%Z) \/ (exists n : Z, negligible_exp fexp = Some n /\ (n <= fexp n)%Z) := @Ulp.negligible_exp_spec'.
Print Assumptions Ulp_negligible_exp_spec_prime_unrestricted.

Definition Ulp_succ_le_plus_ulp_unrestricted :
  forall (beta : radix) (fexp : Z -> Z), Monotone_exp fexp -> forall x : R, (succ beta fexp x <= x + ulp beta fexp x)%R := @Ulp.succ_le_plus_ulp.
Print Assumptions Ulp_succ_le_plus_ulp_unrestricted.

Definition Ulp_pred_lt_le_unrestricted :
  forall (beta : radix) (fexp : Z -> Z) (x y : R), x <> 0%R -> (x <= y)%R -> (pred beta fexp x < y)%R := @Ulp.pred_lt_le.
Print Assumptions Ulp_pred_lt_le_unrestricted.

Definition Ulp_succ_gt_ge_unrestricted :
  forall (beta : radix) (fexp : Z -> Z) (x y : R), y <> 0%R -> (x <= y)%R -> (x < succ beta fexp y)%R := @Ulp.succ_gt_ge.
Print Assumptions Ulp_succ_gt_ge_unrestricted.

Definition Ulp_pred_pos_plus_ulp_aux1_unrestricted :
  forall (beta : radix) (fexp : Z -> Z) (x : R),
       (0 < x)%R -> generic_format beta fexp x -> x <> bpow beta (mag beta x - 1) -> (x - ulp beta fexp x + ulp beta fexp (x - ulp beta fexp x))%R = x := @Ulp.pred_pos_plus_ulp_aux1.
Print Assumptions Ulp_pred_pos_plus_ulp_aux1_unrestricted.

Definition Ulp_id_p_ulp_le_bpow_unrestricted :
  forall (beta : radix) (fexp : Z -> Z) (x : R) (e : Z),
       (0 < x)%R -> generic_format beta fexp x -> (x < bpow beta e)%R -> (x + ulp beta fexp x <= bpow beta e)%R := @Ulp.id_p_ulp_le_bpow.
Print Assumptions Ulp_id_p_ulp_le_bpow_unrestricted.

Definition Ulp_ulp_succ_pos_unrestricted :
  forall (beta : radix) (fexp : Z -> Z) (x : R),
       generic_format beta fexp x -> (0 < x)%R -> ulp beta fexp (succ beta fexp x) = ulp beta fexp x \/ succ beta fexp x = bpow beta (mag beta x) := @Ulp.ulp_succ_pos.
Print Assumptions Ulp_ulp_succ_pos_unrestricted.

Definition Ulp_not_FTZ_generic_format_ulp_unrestricted :
  forall (beta : radix) (fexp : Z -> Z), (forall x : R, generic_format beta fexp (ulp beta fexp x)) -> Exp_not_FTZ fexp := @Ulp.not_FTZ_generic_format_ulp.
Print Assumptions Ulp_not_FTZ_generic_format_ulp_unrestricted.

Definition Ulp_id_m_ulp_ge_bpow_unrestricted :
  forall (beta : radix) (fexp : Z -> Z) (x : R) (e : Z),
       generic_format beta fexp x -> x <> ulp beta fexp x -> (bpow beta e < x)%R -> (bpow beta e <= x - ulp beta fexp x)%R := @Ulp.id_m_ulp_ge_bpow.
Print Assumptions Ulp_id_m_ulp_ge_bpow_unrestricted.

Definition Ulp_round_UP_DN_ulp_unrestricted :
  forall (beta : radix) (fexp : Z -> Z) (x : R), ~ generic_format beta fexp x -> round beta fexp Zceil x = (round beta fexp Zfloor x + ulp beta fexp x)%R := @Ulp.round_UP_DN_ulp.
Print Assumptions Ulp_round_UP_DN_ulp_unrestricted.

Definition Generic_fmt_generic_format_ge_bpow_unrestricted :
  forall (beta : radix) (fexp : Z -> Z) (emin : Z),
       (forall e : Z, (emin <= fexp e)%Z) -> forall x : R, (0 < x)%R -> generic_format beta fexp x -> (bpow beta emin <= x)%R := @Generic_fmt.generic_format_ge_bpow.
Print Assumptions Generic_fmt_generic_format_ge_bpow_unrestricted.

Definition Generic_fmt_round_N_middle_unrestricted :
  forall (beta : radix) (fexp : Z -> Z) (choice : Z -> bool) (x : R),
       (x - round beta fexp Zfloor x)%R = (round beta fexp Zceil x - x)%R ->
       round beta fexp (Znearest choice) x = (if choice (Zfloor (scaled_mantissa beta fexp x)) then round beta fexp Zceil x else round beta fexp Zfloor x) := @Generic_fmt.round_N_middle.
Print Assumptions Generic_fmt_round_N_middle_unrestricted.

Definition Generic_fmt_round_N_small_pos_unrestricted :
  forall (beta : radix) (fexp : Z -> Z) (choice : Z -> bool) (x : R) (ex : Z),
       (bpow beta (ex - 1) <= x < bpow beta ex)%R -> (ex < fexp ex)%Z -> round beta fexp (Znearest choice) x = 0%R := @Generic_fmt.round_N_small_pos.
Print Assumptions Generic_fmt_round_N_small_pos_unrestricted.

Definition Generic_fmt_round_N_opp_unrestricted :
  forall (beta : radix) (fexp : Z -> Z) (choice : Z -> bool) (x : R),
       round beta fexp (Znearest choice) (- x) = (- round beta fexp (Znearest (fun t : Z => negb (choice (- (t + 1))%Z))) x)%R := @Generic_fmt.round_N_opp.
Print Assumptions Generic_fmt_round_N_opp_unrestricted.

Definition Generic_fmt_round_N0_opp_unrestricted :
  forall (beta : radix) (fexp : Z -> Z) (x : R),
       round beta fexp (Znearest (fun x0 : Z => (x0 <? 0)%Z)) (- x) = (- round beta fexp (Znearest (fun x0 : Z => (x0 <? 0)%Z)) x)%R := @Generic_fmt.round_N0_opp.
Print Assumptions Generic_fmt_round_N0_opp_unrestricted.

Definition Generic_fmt_round_N_small_unrestricted :
  forall (beta : radix) (fexp : Z -> Z) (choice : Z -> bool) (x : R) (ex : Z),
       (bpow beta (ex - 1) <= Rabs x < bpow beta ex)%R -> (ex < fexp ex)%Z -> round beta fexp (Znearest choice) x = 0%R := @Generic_fmt.round_N_small.
Print Assumptions Generic_fmt_round_N_small_unrestricted.

Definition Generic_fmt_round_NA_opp_unrestricted :
  forall (beta : radix) (fexp : Z -> Z) (x : R), round beta fexp ZnearestA (- x) = (- round beta fexp ZnearestA x)%R := @Generic_fmt.round_NA_opp.
Print Assumptions Generic_fmt_round_NA_opp_unrestricted.

Definition Generic_fmt_scaled_mantissa_generic_unrestricted :
  forall (beta : radix) (fexp : Z -> Z) (x : R), generic_format beta fexp x -> scaled_mantissa beta fexp x = IZR (Ztrunc (scaled_mantissa beta fexp x)) := @Generic_fmt.scaled_mantissa_generic.
Print Assumptions Generic_fmt_scaled_mantissa_generic_unrestricted.

Definition Generic_fmt_round_DN_or_UP_unrestricted :
  forall (beta : radix) (fexp : Z -> Z) (rnd : R -> Z),
       Valid_rnd rnd -> forall x : R, round beta fexp rnd x = round beta fexp Zfloor x \/ round beta fexp rnd x = round beta fexp Zceil x := @Generic_fmt.round_DN_or_UP.
Print Assumptions Generic_fmt_round_DN_or_UP_unrestricted.

Definition Generic_fmt_round_ZR_or_AW_unrestricted :
  forall (beta : radix) (fexp : Z -> Z) (rnd : R -> Z),
       Valid_rnd rnd -> forall x : R, round beta fexp rnd x = round beta fexp Ztrunc x \/ round beta fexp rnd x = round beta fexp Zaway x := @Generic_fmt.round_ZR_or_AW.
Print Assumptions Generic_fmt_round_ZR_or_AW_unrestricted.

Definition Generic_fmt_round_bounded_small_pos_unrestricted :
  forall (beta : radix) (fexp : Z -> Z) (rnd : R -> Z),
       Valid_rnd rnd ->
       forall (x : R) (ex : Z),
       (ex <= fexp ex)%Z -> (bpow beta (ex - 1) <= x < bpow beta ex)%R -> round beta fexp rnd x = 0%R \/ round beta fexp rnd x = bpow beta (fexp ex) := @Generic_fmt.round_bounded_small_pos.
Print Assumptions Generic_fmt_round_bounded_small_pos_unrestricted.

Definition Generic_fmt_round_bounded_large_pos_unrestricted :
  forall (beta : radix) (fexp : Z -> Z) (rnd : R -> Z),
       Valid_rnd rnd ->
       forall (x : R) (ex : Z),
       (fexp ex < ex)%Z -> (bpow beta (ex - 1) <= x < bpow beta ex)%R -> (bpow beta (ex - 1) <= round beta fexp rnd x <= bpow beta ex)%R := @Generic_fmt.round_bounded_large_pos.
Print Assumptions Generic_fmt_round_bounded_large_pos_unrestricted.

Definition Generic_fmt_round_DN_small_pos_unrestricted :
  forall (beta : radix) (fexp : Z -> Z) (x : R) (ex : Z),
       (bpow beta (ex - 1) <= x < bpow beta ex)%R -> (ex <= fexp ex)%Z -> round beta fexp Zfloor x = 0%R := @Generic_fmt.round_DN_small_pos.
Print Assumptions Generic_fmt_round_DN_small_pos_unrestricted.

Definition Generic_fmt_round_UP_small_pos_unrestricted :
  forall (beta : radix) (fexp : Z -> Z) (x : R) (ex : Z),
       (bpow beta (ex - 1) <= x < bpow beta ex)%R -> (ex <= fexp ex)%Z -> round beta fexp Zceil x = bpow beta (fexp ex) := @Generic_fmt.round_UP_small_pos.
Print Assumptions Generic_fmt_round_UP_small_pos_unrestricted.

Definition Generic_fmt_round_large_pos_ge_bpow_unrestricted :
  forall (beta : radix) (fexp : Z -> Z) (rnd : R -> Z),
       Valid_rnd rnd -> forall (x : R) (e : Z), (0 < round beta fexp rnd x)%R -> (bpow beta e <= x)%R -> (bpow beta e <= round beta fexp rnd x)%R := @Generic_fmt.round_large_pos_ge_bpow.
Print Assumptions Generic_fmt_round_large_pos_ge_bpow_unrestricted.

Definition Generic_fmt_exp_small_round_0_pos_unrestricted :
  forall (beta : radix) (fexp : Z -> Z) (rnd : R -> Z),
       Valid_rnd rnd -> forall (x : R) (ex : Z), (bpow beta (ex - 1) <= x < bpow beta ex)%R -> round beta fexp rnd x = 0%R -> (ex <= fexp ex)%Z := @Generic_fmt.exp_small_round_0_pos.
Print Assumptions Generic_fmt_exp_small_round_0_pos_unrestricted.
