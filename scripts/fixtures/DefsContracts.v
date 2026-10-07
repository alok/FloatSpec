From Stdlib Require Import ZArith Reals Lra.
From Flocq Require Import Core.Zaux Core.Raux Core.Defs.
Open Scope R_scope.

Example fnum_field : forall (beta : radix) m e, Fnum (Float beta m e) = m := fun _ _ _ => eq_refl.
Example fexp_field : forall (beta : radix) m e, Fexp (Float beta m e) = e := fun _ _ _ => eq_refl.

Example f2r_body : forall (beta : radix) (f : float beta),
  F2R f = IZR (Fnum f) * bpow beta (Fexp f) := fun _ _ => eq_refl.
Example total_body : forall P, round_pred_total P = forall x, exists f, P x f := fun _ => eq_refl.
Example monotone_body : forall P,
  round_pred_monotone P = forall x y f g, P x f -> P y g -> x <= y -> f <= g := fun _ => eq_refl.
Example pred_body : forall P, round_pred P = (round_pred_total P /\ round_pred_monotone P) :=
  fun _ => eq_refl.
Example dn_body : forall F x f,
  Rnd_DN_pt F x f = (F f /\ f <= x /\ forall g, F g -> g <= x -> g <= f) := fun _ _ _ => eq_refl.
Example up_body : forall F x f,
  Rnd_UP_pt F x f = (F f /\ x <= f /\ forall g, F g -> x <= g -> f <= g) := fun _ _ _ => eq_refl.
Example zr_body : forall F x f,
  Rnd_ZR_pt F x f = ((0 <= x -> Rnd_DN_pt F x f) /\ (x <= 0 -> Rnd_UP_pt F x f)) :=
  fun _ _ _ => eq_refl.
Example n_body : forall F x f,
  Rnd_N_pt F x f = (F f /\ forall g, F g -> Rabs (f - x) <= Rabs (g - x)) := fun _ _ _ => eq_refl.
Example ng_body : forall F P x f,
  Rnd_NG_pt F P x f = (Rnd_N_pt F x f /\ (P x f \/ forall f2, Rnd_N_pt F x f2 -> f2 = f)) :=
  fun _ _ _ _ => eq_refl.
Example na_body : forall F x f,
  Rnd_NA_pt F x f = (Rnd_N_pt F x f /\ forall f2, Rnd_N_pt F x f2 -> Rabs f2 <= Rabs f) :=
  fun _ _ _ => eq_refl.
Example n0_body : forall F x f,
  Rnd_N0_pt F x f = (Rnd_N_pt F x f /\ forall f2, Rnd_N_pt F x f2 -> Rabs f <= Rabs f2) :=
  fun _ _ _ => eq_refl.

Definition radix10 := Build_radix 10 eq_refl.
Example f2r_values :
  F2R (Float radix2 3 (-1)) = 3 / 2 /\ F2R (Float radix10 (-7) 2) = -700.
Proof.
split; unfold F2R; cbn [Fnum Fexp].
- replace (bpow radix2 (-1)) with (/ 2) by reflexivity. lra.
- replace (bpow radix10 2) with 100 by reflexivity. lra.
Qed.
