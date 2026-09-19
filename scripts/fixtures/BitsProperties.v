From Stdlib Require Import ZArith.
From Flocq Require Import IEEE754.Bits.

Open Scope Z_scope.

(* Independent roundtrip invariants, including every NaN payload encountered.
   The same documented recurrence is used by the compiled Lean test grid. *)
Fixpoint check_roundtrips (count : nat) (state : Z) : bool :=
  match count with
  | O => true
  | S remaining =>
    let word64 := (state * 6364136223846793005 + 1442695040888963407) mod 2^64 in
    let word32 := word64 mod 2^32 in
    Z.eqb (bits_of_b64 (b64_of_bits word64)) word64 &&
    Z.eqb (bits_of_b32 (b32_of_bits word32)) word32 &&
    check_roundtrips remaining word64
  end.

Example compiled_grid_reference : check_roundtrips 10000 526913 = true.
Proof. vm_compute. reflexivity. Qed.

(* Negative unbounded integers use the source's sign threshold, not uint64 wrapping. *)
Example negative_bits_are_not_word_wrapping :
  bits_of_b64 (b64_of_bits (-1)) = 9223372036854775807.
Proof. vm_compute. reflexivity. Qed.
