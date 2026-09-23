(* FloatSpec exemplar lane: sign-magnitude choice functions for Compute.v.

   Not upstream text. Compute.v rounds with any integer rounding `rnd`, given
   a `choice` that satisfies its hypothesis `rnd_choice`:

     inbetween_int m (Rabs x) l ->
     rnd x = cond_Zopp (Rlt_bool x 0) (choice (Rlt_bool x 0) m l).

   Each choice below is read off the matching lemma of Flocq src/Calc/Round.v
   (pinned 7aab8f55), and each `*_choice` lemma checks, with Rocq, that it
   satisfies `rnd_choice` for its rounding. Guessing instead goes wrong: for
   example, the ZR choice is `m`, not `cond_incr (round_ZR s l) m`, because
   Round.v's `round_ZR` expects a signed mantissa. *)
From Stdlib Require Import ZArith Reals.
From Flocq Require Import Core Bracket Round.

Open Scope Z_scope.

Definition rnd_DN (s : bool) (m : Z) (l : location) := cond_incr (round_sign_DN s l) m.
Definition rnd_UP (s : bool) (m : Z) (l : location) := cond_incr (round_sign_UP s l) m.
Definition rnd_ZR (s : bool) (m : Z) (l : location) := m.
Definition rnd_NE (s : bool) (m : Z) (l : location) := cond_incr (round_N (negb (Z.even m)) l) m.
Definition rnd_NA (s : bool) (m : Z) (l : location) := cond_incr (round_N true l) m.
(* Znearest c for an arbitrary tie-breaking predicate c (Sqrt_sqr.v uses it). *)
Definition rnd_N (c : Z -> bool) (s : bool) (m : Z) (l : location) :=
  cond_incr (round_N (if s then negb (c (- (m + 1))) else c m) l) m.

Lemma rnd_DN_choice : forall x m l, inbetween_int m (Rabs x) l ->
  Zfloor x = cond_Zopp (Rlt_bool x 0) (rnd_DN (Rlt_bool x 0) m l).
Proof. exact inbetween_int_DN_sign. Qed.

Lemma rnd_UP_choice : forall x m l, inbetween_int m (Rabs x) l ->
  Zceil x = cond_Zopp (Rlt_bool x 0) (rnd_UP (Rlt_bool x 0) m l).
Proof. exact inbetween_int_UP_sign. Qed.

Lemma rnd_ZR_choice : forall x m l, inbetween_int m (Rabs x) l ->
  Ztrunc x = cond_Zopp (Rlt_bool x 0) (rnd_ZR (Rlt_bool x 0) m l).
Proof. exact inbetween_int_ZR_sign. Qed.

Lemma rnd_NE_choice : forall x m l, inbetween_int m (Rabs x) l ->
  ZnearestE x = cond_Zopp (Rlt_bool x 0) (rnd_NE (Rlt_bool x 0) m l).
Proof. exact inbetween_int_NE_sign. Qed.

Lemma rnd_NA_choice : forall x m l, inbetween_int m (Rabs x) l ->
  ZnearestA x = cond_Zopp (Rlt_bool x 0) (rnd_NA (Rlt_bool x 0) m l).
Proof. exact inbetween_int_NA_sign. Qed.

Lemma rnd_N_choice : forall c x m l, inbetween_int m (Rabs x) l ->
  Znearest c x = cond_Zopp (Rlt_bool x 0) (rnd_N c (Rlt_bool x 0) m l).
Proof. exact inbetween_int_N_sign. Qed.
