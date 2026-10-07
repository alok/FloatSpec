From Stdlib Require Import ZArith Reals Lra Bool.
From Flocq Require Import Core.Zaux Core.Raux.
Open Scope R_scope.

(* Raux.v:2155-2266: Boolean equality laws and conditional negation of reals. *)
Definition eqb_symm : forall x y, Bool.eqb x y = Bool.eqb y x := eqb_sym.
Definition eqb_neg : forall x y, x = negb y -> Bool.eqb x y = false := eqb_false.
Definition eqb_same : forall x y, x = y -> Bool.eqb x y = true := eqb_true.

Example cond_Ropp_body : forall b m, cond_Ropp b m = if b then - m else m := fun b m => eq_refl.

Definition izr_cond_Zopp : forall b m, IZR (cond_Zopp b m) = cond_Ropp b (IZR m) := IZR_cond_Zopp.
Definition abs_cond : forall b m, Rabs (cond_Ropp b m) = Rabs m := abs_cond_Ropp.
Definition cond_lt : forall m, cond_Ropp (Rlt_bool m 0) m = Rabs m := cond_Ropp_Rlt_bool.
Definition lt_cond : forall x sx, 0 < x -> Rlt_bool (cond_Ropp sx x) 0 = sx := Rlt_bool_cond_Ropp.
Definition involutive : forall b x, cond_Ropp b (cond_Ropp b x) = x := cond_Ropp_involutive.
Definition inj : forall b x y, cond_Ropp b x = cond_Ropp b y -> x = y := cond_Ropp_inj.
Definition mult_l : forall b x y, cond_Ropp b (x * y) = cond_Ropp b x * y := cond_Ropp_mult_l.
Definition mult_r : forall b x y, cond_Ropp b (x * y) = x * cond_Ropp b y := cond_Ropp_mult_r.
Definition plus : forall b x y, cond_Ropp b (x + y) = cond_Ropp b x + cond_Ropp b y := cond_Ropp_plus.

Print Assumptions lt_cond.

(* The sign read back from a negated positive value is the flag itself, but only for
   positive inputs: at zero the strict test reads false whatever the flag. *)
Example lt_cond_needs_pos : ~ forall x sx, Rlt_bool (cond_Ropp sx x) 0 = sx.
Proof.
intro H. specialize (H 0 true). simpl in H.
rewrite Ropp_0, Rlt_bool_false in H by lra. discriminate H.
Qed.
Example eqb_false_needs_negation : ~ forall x y, Bool.eqb x y = false.
Proof. intro H. specialize (H true true). discriminate H. Qed.
Print Assumptions lt_cond_needs_pos.
