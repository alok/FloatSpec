/-
FloatSpec exemplar lane: CompCertNaN, the Lean counterpart of CompCertNaN.v.

Provenance: exercises the NaN payload policy of CompCert lib/Floats.v and
{x86_64,aarch64,riscV}/Archi.v at commit
bd2b3826ccc94127995de44a44166745891c1260 (Xavier Leroy and Jacques-Henri
Jourdan, INRIA; LGPL-2.1-or-later, also under the INRIA Non-Commercial
License Agreement), over the transliterated prelude CompCertFloats.lean.
CompCertNaN.v lists the cases and the row layout.
-/
import Exemplars.CompCertFloats

namespace Exemplars.CompCertNaN

open Exemplars.CompCertFloats

def SN : Int := 9218868437227405313
def SNb : Int := 18443366373989023744
def SNh : Int := 9221120236504219648
def QN : Int := 9221120237041090565
def QNn : Int := 18444492273895866368
def ONE : Int := 4607182418800017408
def MONE : Int := 13830554455654793216
def ZERO : Int := 0
def INF : Int := 9218868437227405312
def NINF : Int := 18442240474082181120
def SN32 : Int := 2139095041
def SN32b : Int := 4288675840
def QN32 : Int := 2143289347
def ONE32 : Int := 1065353216
def INF32 : Int := 2139095040
def NINF32 : Int := 4286578688

def eval (A : Archi) (op a b c : Int) : Int :=
  match op with
  | 0 => to_bits (add A (of_bits a) (of_bits b))
  | 1 => to_bits (sub A (of_bits a) (of_bits b))
  | 2 => to_bits (mul A (of_bits a) (of_bits b))
  | 3 => to_bits (div A (of_bits a) (of_bits b))
  | 4 => to_bits (fma A (of_bits a) (of_bits b) (of_bits c))
  | 5 => to_bits (sqrt A (of_bits a))
  | 6 => to_bits (neg A (of_bits a))
  | 7 => to_bits (abs A (of_bits a))
  | 8 => to_bits32 (to_single A (of_bits a))
  | 9 => to_bits (of_single A (of_bits32 a))
  | 10 => to_bits32 (add32 A (of_bits32 a) (of_bits32 b))
  | 11 => to_bits32 (mul32 A (of_bits32 a) (of_bits32 b))
  | _ => to_bits32 (neg32 A (of_bits32 a))

def cases : List (Int × Int × Int × Int) :=
  [(0, SN, QN, 0), (0, QN, SN, 0), (0, QNn, SN, 0), (0, ONE, SNb, 0), (0, INF, NINF, 0),
   (0, SNb, SN, 0), (0, QN, QNn, 0),
   (1, INF, INF, 0), (1, QN, ONE, 0),
   (2, ZERO, INF, 0), (2, SN, ZERO, 0), (2, QNn, QN, 0),
   (3, ZERO, ZERO, 0), (3, INF, INF, 0), (3, ONE, SNb, 0),
   (4, ZERO, INF, QN), (4, INF, ZERO, SN), (4, SN, QN, QNn), (4, QN, SN, ONE),
   (4, ONE, ONE, SN), (4, ZERO, INF, ONE), (4, ONE, INF, NINF), (4, QNn, QN, SNb),
   (4, INF, ZERO, QNn),
   (5, MONE, 0, 0), (5, SN, 0, 0), (5, QNn, 0, 0),
   (6, SN, 0, 0), (6, QN, 0, 0), (7, QNn, 0, 0), (7, SNb, 0, 0),
   (8, SN, 0, 0), (8, QN, 0, 0), (8, SNb, 0, 0), (8, SNh, 0, 0), (8, ONE, 0, 0),
   (9, SN32, 0, 0), (9, QN32, 0, 0), (9, SN32b, 0, 0), (9, ONE32, 0, 0),
   (10, SN32, QN32, 0), (10, INF32, NINF32, 0), (10, QN32, SN32b, 0),
   (11, 0, INF32, 0), (11, SN32b, ONE32, 0),
   (12, SN32, 0, 0)]

def row (k : Int) (A : Archi) (p : Int × Int × Int × Int) : List Int :=
  let (op, a, b, c) := p
  [k, op, a, b, c, eval A op a b c]

end Exemplars.CompCertNaN

open Exemplars.CompCertFloats Exemplars.CompCertNaN in
#eval IO.println (toString
  (cases.map (row 0 x86_64) ++ cases.map (row 1 aarch64) ++ cases.map (row 2 riscV)))
