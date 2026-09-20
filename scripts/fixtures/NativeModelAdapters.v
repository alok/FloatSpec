From Stdlib Require Import ZArith List.
Require Import Flocq.IEEE754.Bits.
Import ListNotations.
Open Scope Z_scope.

(* This explicit adapter policy is not an additional Flocq export. Source bit
   decoding preserves NaN payload/sign; the Lean model canonicalizes NaNs. *)
Definition canonical32 (bits : Z) : Z :=
  let x := Bits.b32_of_bits bits in
  if Binary.is_nan 24 128 x then 2143289344 else Bits.bits_of_b32 x.
Definition canonical64 (bits : Z) : Z :=
  let x := Bits.b64_of_bits bits in
  if Binary.is_nan 53 1024 x then 9221120237041090560 else Bits.bits_of_b64 x.
Definition modelAdapterObserve32 (bits : Z) : list Z :=
  let raw := Bits.bits_of_b32 (Bits.b32_of_bits bits) in
  let wrapped := Z.modulo bits (2 ^ 32) in
  let sourceModel := canonical32 raw in
  let decoded := Bits.bits_of_b32 (Bits.b32_of_bits (canonical32 wrapped)) in
  [raw; sourceModel; decoded; canonical32 decoded;
   Bits.bits_of_b32 (Bits.b32_of_bits sourceModel)].
Definition modelAdapterObserve64 (bits : Z) : list Z :=
  let raw := Bits.bits_of_b64 (Bits.b64_of_bits bits) in
  let wrapped := Z.modulo bits (2 ^ 64) in
  let sourceModel := canonical64 raw in
  let decoded := Bits.bits_of_b64 (Bits.b64_of_bits (canonical64 wrapped)) in
  [raw; sourceModel; decoded; canonical64 decoded;
   Bits.bits_of_b64 (Bits.b64_of_bits sourceModel)].

Example signed_nan_distinction :
  modelAdapterObserve64 18442240474082181121 =
    [18442240474082181121; 9221120237041090560; 9221120237041090560;
     9221120237041090560; 9221120237041090560].
Proof. vm_compute. reflexivity. Qed.
Example wider_integer_distinction :
  modelAdapterObserve32 4294967297 = [2147483649; 2147483649; 1; 1; 2147483649].
Proof. vm_compute. reflexivity. Qed.
Example negative_integer_distinction :
  modelAdapterObserve64 (-9223372036854775808) =
    [0; 0; 9223372036854775808; 9223372036854775808; 0].
Proof. vm_compute. reflexivity. Qed.
