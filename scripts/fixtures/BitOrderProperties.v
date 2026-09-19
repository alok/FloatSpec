From Stdlib Require Import ZArith Bool.
From Flocq Require Import IEEE754.Binary IEEE754.Bits.

Open Scope Z_scope.

Definition comparison_code (c : option comparison) : Z :=
  match c with None => 2 | Some Lt => -1 | Some Eq => 0 | Some Gt => 1 end.

Definition reversed (c : Z) : Z := if Z.eqb c 2 then 2 else -c.

(* These invariants do not reimplement the ordering algorithm. *)
Definition laws32 (left right : Z) : bool :=
  let x := b32_of_bits left in
  let y := b32_of_bits right in
  Z.eqb (comparison_code (b32_compare x x)) (if Binary.is_nan 24 128 x then 2 else 0) &&
  Z.eqb (comparison_code (b32_compare x y)) (reversed (comparison_code (b32_compare y x))) &&
  (if Binary.is_nan 24 128 x then true else
    Z.leb (comparison_code (b32_compare (b32_pred x) x)) 0 &&
    Z.leb (comparison_code (b32_compare x (b32_succ x))) 0).

Definition laws64 (left right : Z) : bool :=
  let x := b64_of_bits left in
  let y := b64_of_bits right in
  Z.eqb (comparison_code (b64_compare x x)) (if Binary.is_nan 53 1024 x then 2 else 0) &&
  Z.eqb (comparison_code (b64_compare x y)) (reversed (comparison_code (b64_compare y x))) &&
  (if Binary.is_nan 53 1024 x then true else
    Z.leb (comparison_code (b64_compare (b64_pred x) x)) 0 &&
    Z.leb (comparison_code (b64_compare x (b64_succ x))) 0).

Definition next_word (state : Z) : Z :=
  (state * 6364136223846793005 + 1442695040888963407) mod 2^64.

Fixpoint check_order (count : nat) (state : Z) : bool :=
  match count with
  | O => true
  | S remaining =>
    let left := next_word state in
    let right := next_word left in
    laws64 left right && laws32 (left mod 2^32) (right mod 2^32) &&
    check_order remaining right
  end.

Example order_grid : check_order 1000 388312 = true.
Proof. vm_compute. reflexivity. Qed.

Example signed_zero_equality :
  b64_compare (b64_of_bits 0) (b64_of_bits 9223372036854775808) = Some Eq.
Proof. vm_compute. reflexivity. Qed.

Example negative_min_subnormal_succeeds_to_negative_zero :
  bits_of_b64 (b64_succ (b64_of_bits 9223372036854775809)) = 9223372036854775808.
Proof. vm_compute. reflexivity. Qed.

Example signed_signaling_nan_is_unordered :
  b32_compare (b32_of_bits 4286578689) (b32_of_bits 0) = None.
Proof. vm_compute. reflexivity. Qed.
