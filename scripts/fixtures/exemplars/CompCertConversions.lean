/-
FloatSpec exemplar lane: CompCertConversions, the Lean counterpart of
CompCertConversions.v.

Provenance: evaluates both sides of identities proved in CompCert
lib/Floats.v at commit bd2b3826ccc94127995de44a44166745891c1260 (Xavier Leroy
and Jacques-Henri Jourdan, INRIA; LGPL-2.1-or-later, also under the INRIA
Non-Commercial License Agreement), over the transliterated prelude
CompCertFloats.lean. CompCertConversions.v lists the identities and the row
layout.
-/
import Exemplars.CompCertFloats

namespace Exemplars.CompCertConversions

open Exemplars.CompCertFloats

def A := x86_64
def bits (f : binary64) : Int := to_bits f
def bits32 (f : binary32) : Int := to_bits32 f
def obits (o : Option Int) : Int := o.getD (-1)
def ox8000_0000 : Int := 2 ^ 31
def ox4330_0000 : Int := 1127219200
def ox4530_0000 : Int := 1160773632

def row (x l : Int) : List Int :=
  let hi := hiword l
  let lo := loword l
  let odd := Z_land (Z_lor l (repr 64 (Z_land l 2047 + 2047))) (repr 64 (-2048))
  let f := of_long l
  [x, l,
   bits (of_intu x),
   bits (sub A (from_words ox4330_0000 x) (from_words ox4330_0000 0)),
   bits (of_int x),
   bits (sub A (from_words ox4330_0000 (repr 32 (x + ox8000_0000)))
               (from_words ox4330_0000 ox8000_0000)),
   (if x < ox8000_0000 then bits (of_int x)
    else bits (add A (of_int (repr 32 (x - ox8000_0000))) (of_intu ox8000_0000))),
   bits (sub A (of_int (Z_land x (2 ^ 31 - 1))) (of_int (Z_land x ox8000_0000))),
   bits (of_longu l),
   bits (add A (sub A (from_words ox4530_0000 hi) (from_words ox4530_0000 (2 ^ 20)))
               (from_words ox4330_0000 lo)),
   bits (add A (mul A (of_intu hi) (BofZ (prec := 53) (emax := 1024) (2 ^ 32))) (of_intu lo)),
   bits (of_long l),
   bits (add A (sub A (from_words ox4530_0000 (repr 32 (hi + ox8000_0000)))
                      (from_words ox4530_0000 (2 ^ 20 + 2 ^ 31)))
               (from_words ox4330_0000 lo)),
   bits (add A (mul A (of_int hi) (BofZ (prec := 53) (emax := 1024) (2 ^ 32))) (of_intu lo)),
   (if l < 2 ^ 63 then bits (of_long l)
    else bits (mul A (of_long (Z_lor (l / 2) (Z_land l 1))) (of_int 2))),
   bits32 (of_longu32 l),
   bits32 (of_double32 A (of_longu l)),
   bits32 (of_double32 A (of_longu odd)),
   bits32 (of_long32 l),
   bits32 (of_double32 A (of_long l)),
   bits32 (of_double32 A (of_long odd)),
   obits (to_int (of_int x)),
   obits (to_intu (of_intu x)),
   obits (to_long (of_long l)),
   obits (to_longu (of_longu l)),
   bits (add A f f),
   bits (mul A f (of_int 2)),
   obits (to_int (div A (of_int x) (of_int 7))),
   obits (to_long (div A (of_long l) (of_int 1000)))]

def inputs : List (Int × Int) :=
  [(0, 0), (1, 1), (2, 68719476735), (7, 68719476736), (2147483647, 68719478783),
   (2147483648, 9007199254740992), (2147483649, 9007199254740993),
   (4294967295, 18014398509481987), (123456789, 9223372036854775807),
   (4000000000, 9223372036854775808), (3, 9223372036854776833),
   (2147483655, 18446744073709551615), (16777217, 18446744073709549568),
   (4294967289, 81985529216486895), (305419896, 18364758544493064720),
   (2863311530, 16777217)]

end Exemplars.CompCertConversions

open Exemplars.CompCertConversions in
#eval IO.println (toString (inputs.map fun (x, l) => row x l))
