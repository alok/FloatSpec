(* FloatSpec exemplar lane: CompCertConversions.

   Provenance: identities proved in CompCert lib/Floats.v at commit
   bd2b3826ccc94127995de44a44166745891c1260 (Xavier Leroy and Jacques-Henri
   Jourdan, INRIA; LGPL-2.1-or-later, also under the INRIA Non-Commercial
   License Agreement; see CompCertFloats.v for the full notice). The
   statements are CompCert's; the row driver is FloatSpec-authored.

   Each row evaluates both sides of these Floats.v theorems on one 32-bit
   integer x and one 64-bit integer l:
   - of_intu_from_words, of_int_from_words;
   - of_intu_of_int_1/2 (whichever case applies) and of_intu_of_int_3;
   - of_longu_from_words, of_longu_decomp, of_long_from_words,
     of_long_decomp, and of_longu_of_long_1/2;
   - Float32.of_longu_double_1/2 and of_long_double_1/2, the round-to-odd
     trick;
   - mul2_add.
   Rows also observe to_int(u)/to_long(u) round trips and truncating
   conversions of quotients, which exercise ZofB's negative-exponent branch.
   The Archi parameter does not affect finite results, so x86_64 is used.
   Row: [x; l; of_intu x; rhs; of_int x; rhs; of_intu_of_int_1/2 rhs;
         of_intu_of_int_3 rhs; of_longu l; from_words rhs; decomp rhs;
         of_long l; from_words rhs; decomp rhs; of_longu_of_long_1/2 rhs;
         Float32.of_longu l; double_1 rhs; double_2 rhs; Float32.of_long l;
         double_1 rhs; double_2 rhs; to_int (of_int x); to_intu (of_intu x);
         to_long (of_long l); to_longu (of_longu l); add f f; mul f 2;
         to_int (of_int x / 7); to_long (of_long l / 1000)]
   Floats are bit patterns, and None is -1. *)
From Stdlib Require Import ZArith List Bool.
From Flocq Require Import Core BinarySingleNaN Binary Bits.
From Exemplars Require Import CompCertFloats.
Import ListNotations.
Open Scope Z_scope.

Local Notation __ := (eq_refl Datatypes.Lt).
Definition A := x86_64.
Definition bits (f : binary64) := to_bits f.
Definition bits32 (f : binary32) := to_bits32 f.
Definition obits (o : option Z) := match o with Some z => z | None => -1 end.
Definition ox8000_0000 := 2 ^ 31.
Definition ox4330_0000 := 1127219200.
Definition ox4530_0000 := 1160773632.

Definition row (x l : Z) : list Z :=
  let hi := hiword l in
  let lo := loword l in
  (* Int64.and (Int64.or n (Int64.add (Int64.and n 2047) 2047)) (Int64.repr (-2048)) *)
  let odd := Z.land (Z.lor l (repr 64 (Z.land l 2047 + 2047))) (repr 64 (-2048)) in
  let f := of_long l in
  [x; l;
   bits (of_intu x);
   bits (sub A (from_words ox4330_0000 x) (from_words ox4330_0000 0));
   bits (of_int x);
   bits (sub A (from_words ox4330_0000 (repr 32 (x + ox8000_0000)))
               (from_words ox4330_0000 ox8000_0000));
   (if x <? ox8000_0000 then bits (of_int x)
    else bits (add A (of_int (repr 32 (x - ox8000_0000))) (of_intu ox8000_0000)));
   bits (sub A (of_int (Z.land x (2 ^ 31 - 1))) (of_int (Z.land x ox8000_0000)));
   bits (of_longu l);
   bits (add A (sub A (from_words ox4530_0000 hi) (from_words ox4530_0000 (2 ^ 20)))
               (from_words ox4330_0000 lo));
   bits (add A (mul A (of_intu hi) (BofZ 53 1024 __ __ (2 ^ 32))) (of_intu lo));
   bits (of_long l);
   bits (add A (sub A (from_words ox4530_0000 (repr 32 (hi + ox8000_0000)))
                      (from_words ox4530_0000 (2 ^ 20 + 2 ^ 31)))
               (from_words ox4330_0000 lo));
   bits (add A (mul A (of_int hi) (BofZ 53 1024 __ __ (2 ^ 32))) (of_intu lo));
   (if l <? 2 ^ 63 then bits (of_long l)
    else bits (mul A (of_long (Z.lor (l / 2) (Z.land l 1))) (of_int 2)));
   bits32 (of_longu32 l);
   bits32 (of_double32 A (of_longu l));
   bits32 (of_double32 A (of_longu odd));
   bits32 (of_long32 l);
   bits32 (of_double32 A (of_long l));
   bits32 (of_double32 A (of_long odd));
   obits (to_int (of_int x));
   obits (to_intu (of_intu x));
   obits (to_long (of_long l));
   obits (to_longu (of_longu l));
   bits (add A f f);
   bits (mul A f (of_int 2));
   obits (to_int (div A (of_int x) (of_int 7)));
   obits (to_long (div A (of_long l) (of_int 1000)))].

Definition inputs : list (Z * Z) :=
  [(0, 0); (1, 1); (2, 68719476735); (7, 68719476736); (2147483647, 68719478783);
   (2147483648, 9007199254740992); (2147483649, 9007199254740993);
   (4294967295, 18014398509481987); (123456789, 9223372036854775807);
   (4000000000, 9223372036854775808); (3, 9223372036854776833);
   (2147483655, 18446744073709551615); (16777217, 18446744073709549568);
   (4294967289, 81985529216486895); (305419896, 18364758544493064720);
   (2863311530, 16777217)].

Eval vm_compute in map (fun p => row (fst p) (snd p)) inputs.
