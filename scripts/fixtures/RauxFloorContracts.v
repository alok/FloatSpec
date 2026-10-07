From Stdlib Require Import ZArith Reals Lra.
From Flocq Require Import Core.Raux.
Open Scope R_scope.

Example zfloor_body : forall x, Zfloor x = (up x - 1)%Z := fun x => eq_refl.
Example zceil_body : forall x, Zceil x = (- Zfloor (- x))%Z := fun x => eq_refl.
Example ztrunc_body : forall x,
  Ztrunc x = if Rlt_bool x 0 then Zceil x else Zfloor x := fun x => eq_refl.
Example zaway_body : forall x,
  Zaway x = if Rlt_bool x 0 then Zfloor x else Zceil x := fun x => eq_refl.

Definition floor_lb : forall x, IZR (Zfloor x) <= x := Zfloor_lb.
Definition floor_ub : forall x, x < IZR (Zfloor x) + 1 := Zfloor_ub.
Definition floor_lub : forall n x, IZR n <= x -> (n <= Zfloor x)%Z := Zfloor_lub.
Definition floor_imp : forall n x, IZR n <= x < IZR (n + 1) -> Zfloor x = n := Zfloor_imp.
Definition floor_izr : forall n, Zfloor (IZR n) = n := Zfloor_IZR.
Definition floor_le : forall x y, x <= y -> (Zfloor x <= Zfloor y)%Z := Zfloor_le.
Definition ceil_ub : forall x, x <= IZR (Zceil x) := Zceil_ub.
Definition ceil_lb : forall x, IZR (Zceil x) < x + 1 := Zceil_lb.
Definition ceil_glb : forall n x, x <= IZR n -> (Zceil x <= n)%Z := Zceil_glb.
Definition ceil_imp : forall n x, IZR (n - 1) < x <= IZR n -> Zceil x = n := Zceil_imp.
Definition ceil_izr : forall n, Zceil (IZR n) = n := Zceil_IZR.
Definition ceil_le : forall x y, x <= y -> (Zceil x <= Zceil y)%Z := Zceil_le.
Definition ceil_floor_neq : forall x, IZR (Zfloor x) <> x -> Zceil x = (Zfloor x + 1)%Z :=
  Zceil_floor_neq.
Definition trunc_izr : forall n, Ztrunc (IZR n) = n := Ztrunc_IZR.
Definition trunc_floor : forall x, 0 <= x -> Ztrunc x = Zfloor x := Ztrunc_floor.
Definition trunc_ceil : forall x, x <= 0 -> Ztrunc x = Zceil x := Ztrunc_ceil.
Definition trunc_le : forall x y, x <= y -> (Ztrunc x <= Ztrunc y)%Z := Ztrunc_le.
Definition trunc_opp : forall x, Ztrunc (- x) = Z.opp (Ztrunc x) := Ztrunc_opp.
Definition trunc_abs : forall x, Ztrunc (Rabs x) = Z.abs (Ztrunc x) := Ztrunc_abs.
Definition trunc_lub : forall n x, IZR n <= Rabs x -> (n <= Z.abs (Ztrunc x))%Z := Ztrunc_lub.
Definition away_izr : forall n, Zaway (IZR n) = n := Zaway_IZR.
Definition away_ceil : forall x, 0 <= x -> Zaway x = Zceil x := Zaway_ceil.
Definition away_floor : forall x, x <= 0 -> Zaway x = Zfloor x := Zaway_floor.
Definition away_le : forall x y, x <= y -> (Zaway x <= Zaway y)%Z := Zaway_le.
Definition away_opp : forall x, Zaway (- x) = Z.opp (Zaway x) := Zaway_opp.
Definition away_abs : forall x, Zaway (Rabs x) = Z.abs (Zaway x) := Zaway_abs.
Definition floor_ceil_middle : forall x, IZR (Zfloor x) <> x ->
  Rcompare (x - IZR (Zfloor x)) (/ 2) = Rcompare (x - IZR (Zfloor x)) (IZR (Zceil x) - x) :=
  Rcompare_floor_ceil_middle.
Definition ceil_floor_middle : forall x, IZR (Zfloor x) <> x ->
  Rcompare (IZR (Zceil x) - x) (/ 2) = Rcompare (IZR (Zceil x) - x) (x - IZR (Zfloor x)) :=
  Rcompare_ceil_floor_middle.
Definition floor_div : forall x y, y <> Z0 -> Zfloor (IZR x / IZR y) = (x / y)%Z := Zfloor_div.
Definition trunc_div : forall x y, y <> 0%Z -> Ztrunc (IZR x / IZR y) = Z.quot x y := Ztrunc_div.

Print Assumptions trunc_abs.
Print Assumptions floor_div.

(* Negative halves: floor and away go down, ceiling and truncation go up. *)
Example negative_half :
  Zfloor (-5/2) = (-3)%Z /\ Zceil (-5/2) = (-2)%Z /\
  Ztrunc (-5/2) = (-2)%Z /\ Zaway (-5/2) = (-3)%Z.
Proof.
assert (Hf : Zfloor (-5/2) = (-3)%Z) by (apply Zfloor_imp; simpl; lra).
assert (Hc : Zceil (-5/2) = (-2)%Z) by (apply Zceil_imp; simpl; lra).
repeat split; try assumption.
- rewrite Ztrunc_ceil by lra. exact Hc.
- rewrite Zaway_floor by lra. exact Hf.
Qed.

Example trunc_floor_needs_nonneg : ~ forall x, Ztrunc x = Zfloor x.
Proof.
intro H. specialize (H (-1/2)).
rewrite Ztrunc_ceil in H by lra.
rewrite (Zceil_imp 0) in H by (simpl; lra).
rewrite (Zfloor_imp (-1)) in H by (simpl; lra).
discriminate H.
Qed.
Example ceil_floor_neq_needs_premise : ~ forall x, Zceil x = (Zfloor x + 1)%Z.
Proof.
intro H. specialize (H 0). rewrite Zceil_IZR, Zfloor_IZR in H. discriminate H.
Qed.
(* Both systems divide by zero to zero, so the source's y <> 0 premise is not needed. *)
Example floor_div_by_zero : forall x, Zfloor (IZR x / IZR 0) = (x / 0)%Z.
Proof. intro x. unfold Rdiv. rewrite Rinv_0, Rmult_0_r, Zdiv_0_r. apply Zfloor_IZR. Qed.
Example trunc_div_by_zero : forall x, Ztrunc (IZR x / IZR 0) = Z.quot x 0.
Proof.
intro x. unfold Rdiv. rewrite Rinv_0, Rmult_0_r.
replace (Z.quot x 0) with 0%Z by (destruct x; reflexivity). apply Ztrunc_IZR.
Qed.
Print Assumptions trunc_floor_needs_nonneg.
