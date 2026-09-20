From Stdlib Require Import Reals ZArith Lra List.
From Flocq Require Import Core.Core Calc.Round.
Import ListNotations.
Open Scope R_scope.

Definition round_N_eq_DN_client :
  forall (beta : radix) (fexp : Z -> Z),
       Valid_exp fexp ->
       forall (choice : Z -> bool) (x : R),
       let d := round beta fexp Zfloor x in let u := round beta fexp Zceil x in (x < (d + u) / 2)%R -> round beta fexp (Znearest choice) x = d := @Ulp.round_N_eq_DN.
Print Assumptions round_N_eq_DN_client.

Definition round_N_eq_DN_pt_client :
  forall (beta : radix) (fexp : Z -> Z),
       Valid_exp fexp ->
       forall (choice : Z -> bool) (x d u : R),
       Rnd_DN_pt (generic_format beta fexp) x d -> Rnd_UP_pt (generic_format beta fexp) x u -> (x < (d + u) / 2)%R -> round beta fexp (Znearest choice) x = d := @Ulp.round_N_eq_DN_pt.
Print Assumptions round_N_eq_DN_pt_client.

Definition round_N_eq_UP_client :
  forall (beta : radix) (fexp : Z -> Z),
       Valid_exp fexp ->
       forall (choice : Z -> bool) (x : R),
       let d := round beta fexp Zfloor x in let u := round beta fexp Zceil x in ((d + u) / 2 < x)%R -> round beta fexp (Znearest choice) x = u := @Ulp.round_N_eq_UP.
Print Assumptions round_N_eq_UP_client.

Definition round_N_eq_UP_pt_client :
  forall (beta : radix) (fexp : Z -> Z),
       Valid_exp fexp ->
       forall (choice : Z -> bool) (x d u : R),
       Rnd_DN_pt (generic_format beta fexp) x d -> Rnd_UP_pt (generic_format beta fexp) x u -> ((d + u) / 2 < x)%R -> round beta fexp (Znearest choice) x = u := @Ulp.round_N_eq_UP_pt.
Print Assumptions round_N_eq_UP_pt_client.

Definition round_N_eq_ties_client :
  forall (beta : radix) (fexp : Z -> Z),
       Valid_exp fexp ->
       forall (c1 c2 : Z -> bool) (x : R),
       (x - round beta fexp Zfloor x)%R <> (round beta fexp Zceil x - x)%R -> round beta fexp (Znearest c1) x = round beta fexp (Znearest c2) x := @Ulp.round_N_eq_ties.
Print Assumptions round_N_eq_ties_client.

Definition round_N_plus_ulp_ge_client :
  forall (beta : radix) (fexp : Z -> Z),
       Valid_exp fexp ->
       Monotone_exp fexp ->
       forall (choice1 choice2 : Z -> bool) (x : R),
       let rx := round beta fexp (Znearest choice2) x in (x <= round beta fexp (Znearest choice1) (rx + ulp beta fexp rx))%R := @Ulp.round_N_plus_ulp_ge.
Print Assumptions round_N_plus_ulp_ge_client.

Definition round_N_le_midp_client :
  forall (beta : radix) (fexp : Z -> Z),
       Valid_exp fexp ->
       forall (choice : Z -> bool) (u v : R), generic_format beta fexp u -> (v < (u + succ beta fexp u) / 2)%R -> (round beta fexp (Znearest choice) v <= u)%R := @Ulp.round_N_le_midp.
Print Assumptions round_N_le_midp_client.

Definition round_N_ge_midp_client :
  forall (beta : radix) (fexp : Z -> Z),
       Valid_exp fexp ->
       forall (choice : Z -> bool) (u v : R), generic_format beta fexp u -> ((u + pred beta fexp u) / 2 < v)%R -> (u <= round beta fexp (Znearest choice) v)%R := @Ulp.round_N_ge_midp.
Print Assumptions round_N_ge_midp_client.

Example tie_choices_differ :
  round radix2 (fun _ => 0%Z) (Znearest (fun _ => false)) (1 / 2) = 0 /\
  round radix2 (fun _ => 0%Z) (Znearest (fun _ => true)) (1 / 2) = 1.
Proof.
  assert (Hfloor : Zfloor (1 / 2) = 0%Z) by (apply Zfloor_imp; simpl; lra).
  assert (Hceil : Zceil (1 / 2) = 1%Z) by (apply Zceil_imp; simpl; lra).
  unfold round, F2R, scaled_mantissa, cexp; simpl.
  repeat rewrite Rmult_1_r.
  unfold Znearest. rewrite Hfloor.
  replace (1 / 2 - IZR 0)%R with (/2)%R by (simpl; field).
  rewrite Rcompare_Eq by reflexivity.
  try rewrite Hceil. simpl. split; ring.
Qed.
Print Assumptions tie_choices_differ.

Example executable_tie_decisions :
  [Round.cond_incr (Round.round_N false (SpecFloat.loc_Inexact Eq)) 0;
   Round.cond_incr (Round.round_N true (SpecFloat.loc_Inexact Eq)) 0] = [0%Z; 1%Z].
Proof. vm_compute. reflexivity. Qed.
Print Assumptions executable_tie_decisions.

Eval vm_compute in
  [Round.cond_incr (Round.round_N false (SpecFloat.loc_Inexact Eq)) 0;
   Round.cond_incr (Round.round_N true (SpecFloat.loc_Inexact Eq)) 0].
