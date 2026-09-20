From Stdlib Require Import Reals ZArith Lia.
Require Import Flocq.Core.Core Flocq.Prop.Double_rounding.
Open Scope R_scope.
Section Contracts.
Variable beta : radix.
Variables fexp1 fexp2 : Z -> Z.
Variables choice1 choice2 : Z -> bool.

Example equality_contract (x : R) :
  round_round_eq beta fexp1 fexp2 choice1 choice2 x =
    (round beta fexp1 (Znearest choice1)
        (round beta fexp2 (Znearest choice2) x) =
      round beta fexp1 (Znearest choice1) x).
Proof. reflexivity. Qed.
Example midpoint_contract (x : R) :
  midp beta fexp1 x = round beta fexp1 Zfloor x + / 2 * ulp beta fexp1 x.
Proof. reflexivity. Qed.
Example upper_midpoint_contract (x : R) :
  midp' beta fexp1 x = round beta fexp1 Zceil x - / 2 * ulp beta fexp1 x.
Proof. reflexivity. Qed.

Example mult_hyp_contract : round_round_mult_hyp fexp1 fexp2 =
  ((forall ex ey, (fexp2 (ex + ey) <= fexp1 ex + fexp1 ey)%Z) /\
   (forall ex ey, (fexp2 (ex + ey - 1) <= fexp1 ex + fexp1 ey)%Z)).
Proof. reflexivity. Qed.
Example plus_hyp_contract : round_round_plus_hyp fexp1 fexp2 =
  ((forall ex ey, (fexp1 (ex + 1) - 1 <= ey)%Z -> (fexp2 ex <= fexp1 ey)%Z) /\
   (forall ex ey, (fexp1 (ex - 1) + 1 <= ey)%Z -> (fexp2 ex <= fexp1 ey)%Z) /\
   (forall ex ey, (fexp1 ex - 1 <= ey)%Z -> (fexp2 ex <= fexp1 ey)%Z) /\
   (forall ex ey, (ex - 1 <= ey)%Z -> (fexp2 ex <= fexp1 ey)%Z)).
Proof. reflexivity. Qed.
Example plus_ge3_hyp_contract : round_round_plus_radix_ge_3_hyp fexp1 fexp2 =
  ((forall ex ey, (fexp1 (ex + 1) <= ey)%Z -> (fexp2 ex <= fexp1 ey)%Z) /\
   (forall ex ey, (fexp1 (ex - 1) + 1 <= ey)%Z -> (fexp2 ex <= fexp1 ey)%Z) /\
   (forall ex ey, (fexp1 ex <= ey)%Z -> (fexp2 ex <= fexp1 ey)%Z) /\
   (forall ex ey, (ex - 1 <= ey)%Z -> (fexp2 ex <= fexp1 ey)%Z)).
Proof. reflexivity. Qed.
Example sqrt_hyp_contract : round_round_sqrt_hyp fexp1 fexp2 =
  ((forall ex, (2 * fexp1 ex <= fexp1 (2 * ex))%Z) /\
   (forall ex, (2 * fexp1 ex <= fexp1 (2 * ex - 1))%Z) /\
   (forall ex, (fexp1 (2 * ex) < 2 * ex)%Z ->
     (fexp2 ex + ex <= 2 * fexp1 ex - 2)%Z)).
Proof. reflexivity. Qed.
Example sqrt_ge4_hyp_contract : round_round_sqrt_radix_ge_4_hyp fexp1 fexp2 =
  ((forall ex, (2 * fexp1 ex <= fexp1 (2 * ex))%Z) /\
   (forall ex, (2 * fexp1 ex <= fexp1 (2 * ex - 1))%Z) /\
   (forall ex, (fexp1 (2 * ex) < 2 * ex)%Z ->
     (fexp2 ex + ex <= 2 * fexp1 ex - 1)%Z)).
Proof. reflexivity. Qed.
Example div_hyp_contract : round_round_div_hyp fexp1 fexp2 =
  ((forall ex, (fexp2 ex <= fexp1 ex - 1)%Z) /\
   (forall ex ey, (fexp1 ex < ex)%Z -> (fexp1 ey < ey)%Z ->
     (fexp1 (ex - ey) <= ex - ey + 1)%Z ->
     (fexp2 (ex - ey) <= fexp1 ex - ey)%Z) /\
   (forall ex ey, (fexp1 ex < ex)%Z -> (fexp1 ey < ey)%Z ->
     (fexp1 (ex - ey + 1) <= ex - ey + 1 + 1)%Z ->
     (fexp2 (ex - ey + 1) <= fexp1 ex - ey)%Z) /\
   (forall ex ey, (fexp1 ex < ex)%Z -> (fexp1 ey < ey)%Z ->
     (fexp1 (ex - ey) <= ex - ey)%Z ->
     (fexp2 (ex - ey) <= fexp1 (ex - ey) + fexp1 ey - ey)%Z) /\
   (forall ex ey, (fexp1 ex < ex)%Z -> (fexp1 ey < ey)%Z ->
     (fexp1 (ex - ey) = ex - ey + 1)%Z ->
     (fexp2 (ex - ey) <= ex - ey - ey + fexp1 ey)%Z)).
Proof. reflexivity. Qed.

Definition mult_aux_client (h : round_round_mult_hyp fexp1 fexp2)
  (x y : R) (hx : generic_format beta fexp1 x)
  (hy : generic_format beta fexp1 y) : generic_format beta fexp2 (x * y) :=
  @round_round_mult_aux beta fexp1 fexp2 h x y hx hy.
Definition mult_client (rnd : R -> Z) (hr : Valid_rnd rnd)
  (h : round_round_mult_hyp fexp1 fexp2)
  (x y : R) (hx : generic_format beta fexp1 x)
  (hy : generic_format beta fexp1 y) :
  round beta fexp1 rnd (round beta fexp2 rnd (x * y)) =
    round beta fexp1 rnd (x * y) :=
  @round_round_mult beta rnd hr fexp1 fexp2 h x y hx hy.

Variables (H1 : Valid_exp fexp1) (H2 : Valid_exp fexp2).
Definition plus_client (h : round_round_plus_hyp fexp1 fexp2)
  (x y : R) (hx : generic_format beta fexp1 x) (hy : generic_format beta fexp1 y) :
  round_round_eq beta fexp1 fexp2 choice1 choice2 (x + y) :=
  @round_round_plus beta fexp1 fexp2 H1 H2 choice1 choice2 h x y hx hy.
Definition minus_client (h : round_round_plus_hyp fexp1 fexp2)
  (x y : R) (hx : generic_format beta fexp1 x) (hy : generic_format beta fexp1 y) :
  round_round_eq beta fexp1 fexp2 choice1 choice2 (x - y) :=
  @round_round_minus beta fexp1 fexp2 H1 H2 choice1 choice2 h x y hx hy.
Definition sqrt_client (h : round_round_sqrt_hyp fexp1 fexp2)
  (x : R) (hx : generic_format beta fexp1 x) :
  round_round_eq beta fexp1 fexp2 choice1 choice2 (sqrt x) :=
  @round_round_sqrt beta fexp1 fexp2 H1 H2 choice1 choice2 h x hx.
Definition div_client (heven : exists n : Z, ((beta : Z) = 2 * n)%Z)
  (h : round_round_div_hyp fexp1 fexp2)
  (x y : R) (hne : y <> 0) (hx : generic_format beta fexp1 x)
  (hy : generic_format beta fexp1 y) :
  round_round_eq beta fexp1 fexp2 choice1 choice2 (x / y) :=
  @round_round_div beta fexp1 fexp2 H1 H2 choice1 choice2 heven h x y hne hx hy.
End Contracts.

Example sqrt_radix_four_gap :
  round_round_sqrt_radix_ge_4_hyp (fun exponent => (exponent - 1)%Z)
    (fun exponent => (exponent - 3)%Z) /\
  ~ round_round_sqrt_hyp (fun exponent => (exponent - 1)%Z)
    (fun exponent => (exponent - 3)%Z).
Proof.
  split.
  - repeat split; intros; lia.
  - intros [_ [_ H]]. specialize (H 0%Z ltac:(lia)). lia.
Qed.
