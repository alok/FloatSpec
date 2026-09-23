(* FloatSpec exemplar lane: CompCertFloats (shared prelude).

   Provenance: trimmed from CompCert (https://github.com/AbsInt/CompCert) at
   commit bd2b3826ccc94127995de44a44166745891c1260:
   - lib/IEEE754_extra.v: BofZ, ZofB, ZofB_range and Bconv, with verbatim
     bodies;
   - lib/Floats.v: the NaN payload policy (quiet_nan_*, expand/reduce,
     neg/abs/unop/binop/fma NaN handlers), the Float and Float32
     operations, and the conversions;
   - lib/Zbits.v: P_mod_two_p and P_mod_two_p_range, verbatim;
   - lib/Coqlib.v: two_power_nat_O and two_power_nat_pos, verbatim;
   - x86_64/Archi.v, aarch64/Archi.v and riscV/Archi.v: the NaN parameters.

   (* *********************************************************************)
   (*              The Compcert verified compiler                         *)
   (*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
   (*          Jacques-Henri Jourdan, INRIA Paris-Rocquencourt            *)
   (*  Copyright Institut National de Recherche en Informatique et en     *)
   (*  Automatique.  All rights reserved.  This file is distributed       *)
   (*  under the terms of the GNU Lesser General Public License as        *)
   (*  published by the Free Software Foundation, either version 2.1 of   *)
   (*  the License, or  (at your option) any later version.               *)
   (*  This file is also distributed under the terms of the               *)
   (*  INRIA Non-Commercial License Agreement.                            *)
   (* *********************************************************************)

   Replaced:
   - CompCert's Integers.int and int64 become Z in [0, 2^32) and [0, 2^64).
     Int.repr is `repr w` (mod 2^w), Int.signed is `signed w`, and
     Int64.hiword, loword and ofwords are Z division, modulo and sum.
   - The `Archi` module becomes a record parameter `A`. Its three instances
     copy the Archi.v definitions verbatim, with two exceptions: fma_order is
     encoded as a Boolean (true when the order is (z, x, y)), and
     `iter_nat 51 _ xO xH` is written with Flocq's iter_nat.
   - Coqlib's zeq becomes Z.eq_dec in normalized_nan's proof.
   Only Flocq and the Rocq standard library are imported. *)
From Stdlib Require Import ZArith List Bool Lia Zpower.
From Flocq Require Import Core Digits BinarySingleNaN Binary Bits.
Import ListNotations.
Open Scope Z_scope.

(* ---- lib/Coqlib.v ---- *)

Lemma two_power_nat_O : two_power_nat O = 1.
Proof. reflexivity. Qed.

Lemma two_power_nat_pos : forall n : nat, two_power_nat n > 0.
Proof.
  induction n. rewrite two_power_nat_O. lia.
  rewrite two_power_nat_S. lia.
Qed.

(* ---- lib/Zbits.v ---- *)

Fixpoint P_mod_two_p (p: positive) (n: nat) {struct n} : Z :=
  match n with
  | O => 0
  | S m =>
      match p with
      | xH => 1
      | xO q => Z.double (P_mod_two_p q m)
      | xI q => Z.succ_double (P_mod_two_p q m)
      end
  end.

Lemma P_mod_two_p_range:
  forall n p, 0 <= P_mod_two_p p n < two_power_nat n.
Proof.
  induction n; simpl; intros.
  - rewrite two_power_nat_O. lia.
  - rewrite two_power_nat_S. destruct p.
    + generalize (IHn p). rewrite Z.succ_double_spec. lia.
    + generalize (IHn p). rewrite Z.double_spec. lia.
    + generalize (two_power_nat_pos n). lia.
Qed.

(* ---- lib/Floats.v: normalization of NaN payloads ---- *)

Lemma normalized_nan: forall prec n p,
  Z.of_nat n = prec - 1 -> 1 < prec ->
  nan_pl prec (Z.to_pos (P_mod_two_p p n)) = true.
Proof.
  intros. unfold nan_pl. apply Z.ltb_lt. rewrite Digits.Zpos_digits2_pos.
  set (p' := P_mod_two_p p n).
  assert (A: 0 <= p' < 2 ^ Z.of_nat n).
  { rewrite <- two_power_nat_equiv; apply P_mod_two_p_range. }
  assert (B: Digits.Zdigits radix2 p' <= prec - 1).
  { apply Digits.Zdigits_le_Zpower. rewrite <- H. rewrite Z.abs_eq; tauto. }
  destruct (Z.eq_dec p' 0).
- rewrite e. simpl; auto.
- rewrite Z2Pos.id by lia. lia.
Qed.

Definition quiet_nan_64_payload (p: positive) :=
  Z.to_pos (P_mod_two_p (Pos.lor p ((iter_nat xO 51 1%positive))) 52%nat).

Lemma quiet_nan_64_proof: forall p, nan_pl 53 (quiet_nan_64_payload p) = true.
Proof. intros; apply normalized_nan; auto; lia. Qed.

Definition quiet_nan_64 (sp: bool * positive) : {x : binary64 | is_nan _ _ x = true} :=
  let (s, p) := sp in
  exist _ (B754_nan 53 1024 s (quiet_nan_64_payload p) (quiet_nan_64_proof p)) (eq_refl true).

Definition quiet_nan_32_payload (p: positive) :=
  Z.to_pos (P_mod_two_p (Pos.lor p ((iter_nat xO 22 1%positive))) 23%nat).

Lemma quiet_nan_32_proof: forall p, nan_pl 24 (quiet_nan_32_payload p) = true.
Proof. intros; apply normalized_nan; auto; lia. Qed.

Definition quiet_nan_32 (sp: bool * positive) : {x : binary32 | is_nan _ _ x = true} :=
  let (s, p) := sp in
  exist _ (B754_nan 24 128 s (quiet_nan_32_payload p) (quiet_nan_32_proof p)) (eq_refl true).

Definition expand_nan_payload (p: positive) := Pos.shiftl_nat p 29.

Lemma expand_nan_proof (p : positive) :
  nan_pl 24 p = true ->
  nan_pl 53 (expand_nan_payload p) = true.
Proof.
  unfold nan_pl, expand_nan_payload. intros K.
  rewrite Z.ltb_lt in *.
  unfold Pos.shiftl_nat, nat_rect, Digits.digits2_pos.
  fold (Digits.digits2_pos p).
  zify; lia.
Qed.

Definition expand_nan s p H : {x : binary64 | is_nan _ _ x = true} :=
  exist _ (B754_nan 53 1024 s (expand_nan_payload p) (expand_nan_proof p H)) (eq_refl true).

Definition reduce_nan_payload (p: positive) :=
  Pos.shiftr_nat (quiet_nan_64_payload p) 29.

(* ---- Archi.v, as a record ---- *)

Record archi := {
  a_default_nan_64 : bool * positive;
  a_default_nan_32 : bool * positive;
  a_choose_nan_64 : list (bool * positive) -> bool * positive;
  a_choose_nan_32 : list (bool * positive) -> bool * positive;
  a_fma_order_zxy : bool;
  a_fma_invalid_mul_is_nan : bool;
  a_float_of_single_preserves_sNaN : bool;
  a_float_conversion_default_nan : bool }.

(* x86_64/Archi.v: always choose the first NaN argument, if any. *)
Definition x86_64 : archi :=
  let default_nan_64 := (true, iter_nat xO 51 xH) in
  let default_nan_32 := (true, iter_nat xO 22 xH) in
  {| a_default_nan_64 := default_nan_64;
     a_default_nan_32 := default_nan_32;
     a_choose_nan_64 := fun l => match l with nil => default_nan_64 | n :: _ => n end;
     a_choose_nan_32 := fun l => match l with nil => default_nan_32 | n :: _ => n end;
     a_fma_order_zxy := false;
     a_fma_invalid_mul_is_nan := false;
     a_float_of_single_preserves_sNaN := false;
     a_float_conversion_default_nan := false |}.

(* aarch64/Archi.v: choose the first signaling NaN, if any; otherwise the
   first NaN; otherwise the default. *)
Definition choose_nan (is_signaling: positive -> bool)
                      (default: bool * positive)
                      (l0: list (bool * positive)) : bool * positive :=
  let fix choose_snan (l1: list (bool * positive)) :=
    match l1 with
    | nil =>
        match l0 with nil => default | n :: _ => n end
    | ((s, p) as n) :: l1 =>
        if is_signaling p then n else choose_snan l1
    end
  in choose_snan l0.

Definition aarch64 : archi :=
  let default_nan_64 := (false, iter_nat xO 51 xH) in
  let default_nan_32 := (false, iter_nat xO 22 xH) in
  {| a_default_nan_64 := default_nan_64;
     a_default_nan_32 := default_nan_32;
     a_choose_nan_64 := choose_nan (fun p => negb (Pos.testbit p 51)) default_nan_64;
     a_choose_nan_32 := choose_nan (fun p => negb (Pos.testbit p 22)) default_nan_32;
     a_fma_order_zxy := true;
     a_fma_invalid_mul_is_nan := true;
     a_float_of_single_preserves_sNaN := false;
     a_float_conversion_default_nan := false |}.

(* riscV/Archi.v: always the default NaN. *)
Definition riscV : archi :=
  let default_nan_64 := (false, iter_nat xO 51 xH) in
  let default_nan_32 := (false, iter_nat xO 22 xH) in
  {| a_default_nan_64 := default_nan_64;
     a_default_nan_32 := default_nan_32;
     a_choose_nan_64 := fun _ => default_nan_64;
     a_choose_nan_32 := fun _ => default_nan_32;
     a_fma_order_zxy := false;
     a_fma_invalid_mul_is_nan := false;
     a_float_of_single_preserves_sNaN := false;
     a_float_conversion_default_nan := true |}.

(* ---- lib/IEEE754_extra.v ---- *)

Section Extra.
Variable prec emax : Z.
Context (prec_gt_0_ : Prec_gt_0 prec) (Hmax : Prec_lt_emax prec emax).

Definition BofZ (n: Z) : binary_float prec emax :=
  binary_normalize prec emax _ Hmax mode_NE n 0 false.

Definition ZofB (f: binary_float prec emax): option Z :=
  match f with
    | B754_finite _ _ s m (Zpos e) _ => Some (cond_Zopp s (Zpos m) * Z.pow_pos radix2 e)%Z
    | B754_finite _ _ s m 0 _ => Some (cond_Zopp s (Zpos m))
    | B754_finite _ _ s m (Zneg e) _ => Some (cond_Zopp s (Zpos m / Z.pow_pos radix2 e))%Z
    | B754_zero _ _ _ => Some 0%Z
    | _ => None
  end.

Definition ZofB_range (f: binary_float prec emax) (zmin zmax: Z): option Z :=
  match ZofB f with
  | None => None
  | Some z => if Z.leb zmin z && Z.leb z zmax then Some z else None
  end.
End Extra.

Section Conv.
Variable prec1 emax1 prec2 emax2 : Z.
Context (Hprec2 : Prec_gt_0 prec2) (Hmax2 : Prec_lt_emax prec2 emax2).

Definition Bconv (conv_nan: binary_float prec1 emax1 -> {x | is_nan prec2 emax2 x = true})
    (md: mode) (f: binary_float prec1 emax1) : binary_float prec2 emax2 :=
  match f with
    | B754_nan _ _ _ _ _ => build_nan prec2 emax2 (conv_nan f)
    | B754_infinity _ _ s => B754_infinity _ _ s
    | B754_zero _ _ s => B754_zero _ _ s
    | B754_finite _ _ s m e _ => binary_normalize _ _ _ Hmax2 md (cond_Zopp s (Zpos m)) e s
  end.
End Conv.

(* ---- Integers.v, on Z ---- *)

Definition repr (w z : Z) := z mod 2 ^ w.
Definition signed (w x : Z) := if x <? 2 ^ (w - 1) then x else x - 2 ^ w.
Definition hiword (l : Z) := l / 2 ^ 32.
Definition loword (l : Z) := l mod 2 ^ 32.
Definition ofwords (hi lo : Z) := hi * 2 ^ 32 + lo.

(* ---- lib/Floats.v, Float and Float32, for a given Archi ---- *)

Local Notation __ := (eq_refl Datatypes.Lt).

(* Conversions that do not depend on Archi. *)
Definition to_int (f: binary64): option Z :=
  option_map (repr 32) (ZofB_range _ _ f (- 2 ^ 31) (2 ^ 31 - 1)).
Definition to_intu (f: binary64): option Z :=
  option_map (repr 32) (ZofB_range _ _ f 0 (2 ^ 32 - 1)).
Definition to_long (f: binary64): option Z :=
  option_map (repr 64) (ZofB_range _ _ f (- 2 ^ 63) (2 ^ 63 - 1)).
Definition to_longu (f: binary64): option Z :=
  option_map (repr 64) (ZofB_range _ _ f 0 (2 ^ 64 - 1)).

Definition of_int (n: Z): binary64 := BofZ 53 1024 __ __ (signed 32 n).
Definition of_intu (n: Z): binary64 := BofZ 53 1024 __ __ n.
Definition of_long (n: Z): binary64 := BofZ 53 1024 __ __ (signed 64 n).
Definition of_longu (n: Z): binary64 := BofZ 53 1024 __ __ n.

Definition to_bits (f: binary64): Z := repr 64 (bits_of_b64 f).
Definition of_bits (b: Z): binary64 := b64_of_bits b.
Definition from_words (hi lo: Z) : binary64 := of_bits (ofwords hi lo).

Definition of_long32 (n: Z): binary32 := BofZ 24 128 __ __ (signed 64 n).
Definition of_longu32 (n: Z): binary32 := BofZ 24 128 __ __ n.
Definition to_bits32 (f: binary32) : Z := repr 32 (bits_of_b32 f).
Definition of_bits32 (b: Z): binary32 := b32_of_bits b.

Section Floats.
Variable A : archi.

Definition default_nan_64 := quiet_nan_64 (a_default_nan_64 A).
Definition default_nan_32 := quiet_nan_32 (a_default_nan_32 A).

Definition of_single_nan (f : binary32) : { x : binary64 | is_nan _ _ x = true } :=
  match f with
  | B754_nan _ _ s p H =>
    if a_float_conversion_default_nan A
    then default_nan_64
    else if a_float_of_single_preserves_sNaN A
    then expand_nan s p H
    else quiet_nan_64 (s, expand_nan_payload p)
  | _ => default_nan_64
  end.

Definition to_single_nan (f : binary64) : { x : binary32 | is_nan _ _ x = true } :=
  match f with
  | B754_nan _ _ s p H =>
    if a_float_conversion_default_nan A
    then default_nan_32
    else quiet_nan_32 (s, reduce_nan_payload p)
  | _ => default_nan_32
  end.

Definition neg_nan (f : binary64) : { x : binary64 | is_nan _ _ x = true } :=
  match f with
  | B754_nan _ _ s p H => exist _ (B754_nan 53 1024 (negb s) p H) (eq_refl true)
  | _ => default_nan_64
  end.

Definition abs_nan (f : binary64) : { x : binary64 | is_nan _ _ x = true } :=
  match f with
  | B754_nan _ _ s p H => exist _ (B754_nan 53 1024 false p H) (eq_refl true)
  | _ => default_nan_64
  end.

Definition cons_pl (x: binary64) (l: list (bool * positive)) :=
  match x with B754_nan _ _ s p _ => (s, p) :: l | _ => l end.

Definition unop_nan (x: binary64) : {x : binary64 | is_nan _ _ x = true} :=
  quiet_nan_64 (a_choose_nan_64 A (cons_pl x [])).

Definition binop_nan (x y: binary64) : {x : binary64 | is_nan _ _ x = true} :=
  quiet_nan_64 (a_choose_nan_64 A (cons_pl x (cons_pl y []))).

Definition fma_order {T: Type} (x y z: T) :=
  if a_fma_order_zxy A then (z, x, y) else (x, y, z).

Definition fma_nan_1 (x y z: binary64) : {x : binary64 | is_nan _ _ x = true} :=
  let '(a, b, c) := fma_order x y z in
  quiet_nan_64 (a_choose_nan_64 A (cons_pl a (cons_pl b (cons_pl c [])))).

Definition fma_nan (x y z: binary64) : {x : binary64 | is_nan _ _ x = true} :=
  match x, y with
  | B754_infinity _ _ _, B754_zero _ _ _ | B754_zero _ _ _, B754_infinity _ _ _ =>
      if a_fma_invalid_mul_is_nan A
      then quiet_nan_64 (a_choose_nan_64 A (a_default_nan_64 A :: cons_pl z []))
      else fma_nan_1 x y z
  | _, _ =>
      fma_nan_1 x y z
  end.

Definition neg: binary64 -> binary64 := Bopp _ _ neg_nan.
Definition abs: binary64 -> binary64 := Babs _ _ abs_nan.
Definition sqrt: binary64 -> binary64 := Bsqrt 53 1024 __ __ unop_nan mode_NE.
Definition add: binary64 -> binary64 -> binary64 := Bplus 53 1024 __ __ binop_nan mode_NE.
Definition sub: binary64 -> binary64 -> binary64 := Bminus 53 1024 __ __ binop_nan mode_NE.
Definition mul: binary64 -> binary64 -> binary64 := Bmult 53 1024 __ __ binop_nan mode_NE.
Definition div: binary64 -> binary64 -> binary64 := Bdiv 53 1024 __ __ binop_nan mode_NE.
Definition fma: binary64 -> binary64 -> binary64 -> binary64 :=
  Bfma 53 1024 __ __ fma_nan mode_NE.

Definition of_single: binary32 -> binary64 := Bconv _ _ 53 1024 __ __ of_single_nan mode_NE.
Definition to_single: binary64 -> binary32 := Bconv _ _ 24 128 __ __ to_single_nan mode_NE.

(* Module Float32 *)
Definition neg_nan32 (f : binary32) : { x : binary32 | is_nan _ _ x = true } :=
  match f with
  | B754_nan _ _ s p H => exist _ (B754_nan 24 128 (negb s) p H) (eq_refl true)
  | _ => default_nan_32
  end.

Definition cons_pl32 (x: binary32) (l: list (bool * positive)) :=
  match x with B754_nan _ _ s p _ => (s, p) :: l | _ => l end.

Definition binop_nan32 (x y: binary32) : {x : binary32 | is_nan _ _ x = true} :=
  quiet_nan_32 (a_choose_nan_32 A (cons_pl32 x (cons_pl32 y []))).

Definition neg32: binary32 -> binary32 := Bopp _ _ neg_nan32.
Definition add32: binary32 -> binary32 -> binary32 := Bplus 24 128 __ __ binop_nan32 mode_NE.
Definition mul32: binary32 -> binary32 -> binary32 := Bmult 24 128 __ __ binop_nan32 mode_NE.
Definition of_double32 : binary64 -> binary32 := to_single.

End Floats.
