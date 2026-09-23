(* FloatSpec exemplar lane: CompCertNaN.

   Provenance: exercises the NaN payload policy of CompCert lib/Floats.v and
   {x86_64,aarch64,riscV}/Archi.v at commit
   bd2b3826ccc94127995de44a44166745891c1260 (Xavier Leroy and Jacques-Henri
   Jourdan, INRIA; LGPL-2.1-or-later, also under the INRIA Non-Commercial
   License Agreement; see CompCertFloats.v for the full notice), as trimmed
   in CompCertFloats.v. The case table and driver are FloatSpec-authored.

   Each row applies one Float or Float32 operation to bit-pattern inputs
   under one Archi and prints the result's bits. The inputs are:
   - signaling and quiet NaNs, with both signs and with high payload bits;
   - infinities and zeros, to produce invalid operations.
   The cases cover the operations CompCert's NaN policy reaches:
   - add, sub, mul, div, fma and sqrt;
   - neg and abs, which keep the payload;
   - to_single and of_single, which shift the payload;
   - the fma special case `fma 0 inf nan`, which aarch64 treats as invalid.
   op codes: 0 add, 1 sub, 2 mul, 3 div, 4 fma, 5 sqrt, 6 neg, 7 abs,
   8 to_single, 9 of_single, 10 add32, 11 mul32, 12 neg32.
   Archi codes: 0 x86_64, 1 aarch64, 2 riscV.
   Row: [archi; op; a; b; c; result bits]. *)
From Stdlib Require Import ZArith List Bool.
From Flocq Require Import Core BinarySingleNaN Binary Bits.
From Exemplars Require Import CompCertFloats.
Import ListNotations.
Open Scope Z_scope.

Definition SN := 9218868437227405313.     (* 0x7FF0000000000001 *)
Definition SNb := 18443366373989023744.   (* 0xFFF4000000000000 *)
Definition SNh := 9221120236504219648.    (* 0x7FF7FFFFE0000000 *)
Definition QN := 9221120237041090565.     (* 0x7FF8000000000005 *)
Definition QNn := 18444492273895866368.   (* 0xFFF8000000000000 *)
Definition ONE := 4607182418800017408.    (* 0x3FF0000000000000 *)
Definition MONE := 13830554455654793216.  (* 0xBFF0000000000000 *)
Definition ZERO := 0.
Definition INF := 9218868437227405312.    (* 0x7FF0000000000000 *)
Definition NINF := 18442240474082181120.  (* 0xFFF0000000000000 *)
Definition SN32 := 2139095041.            (* 0x7F800001 *)
Definition SN32b := 4288675840.           (* 0xFFA00000 *)
Definition QN32 := 2143289347.            (* 0x7FC00003 *)
Definition ONE32 := 1065353216.           (* 0x3F800000 *)
Definition INF32 := 2139095040.           (* 0x7F800000 *)
Definition NINF32 := 4286578688.          (* 0xFF800000 *)

Definition eval (A : archi) (op a b c : Z) : Z :=
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
  end.

Definition cases : list (Z * Z * Z * Z) :=
  [(0, SN, QN, 0); (0, QN, SN, 0); (0, QNn, SN, 0); (0, ONE, SNb, 0); (0, INF, NINF, 0);
   (0, SNb, SN, 0); (0, QN, QNn, 0);
   (1, INF, INF, 0); (1, QN, ONE, 0);
   (2, ZERO, INF, 0); (2, SN, ZERO, 0); (2, QNn, QN, 0);
   (3, ZERO, ZERO, 0); (3, INF, INF, 0); (3, ONE, SNb, 0);
   (4, ZERO, INF, QN); (4, INF, ZERO, SN); (4, SN, QN, QNn); (4, QN, SN, ONE);
   (4, ONE, ONE, SN); (4, ZERO, INF, ONE); (4, ONE, INF, NINF); (4, QNn, QN, SNb);
   (4, INF, ZERO, QNn);
   (5, MONE, 0, 0); (5, SN, 0, 0); (5, QNn, 0, 0);
   (6, SN, 0, 0); (6, QN, 0, 0); (7, QNn, 0, 0); (7, SNb, 0, 0);
   (8, SN, 0, 0); (8, QN, 0, 0); (8, SNb, 0, 0); (8, SNh, 0, 0); (8, ONE, 0, 0);
   (9, SN32, 0, 0); (9, QN32, 0, 0); (9, SN32b, 0, 0); (9, ONE32, 0, 0);
   (10, SN32, QN32, 0); (10, INF32, NINF32, 0); (10, QN32, SN32b, 0);
   (11, 0, INF32, 0); (11, SN32b, ONE32, 0);
   (12, SN32, 0, 0)].

Definition row (k : Z) (A : archi) (p : Z * Z * Z * Z) : list Z :=
  let '(op, a, b, c) := p in [k; op; a; b; c; eval A op a b c].

Eval vm_compute in
  map (row 0 x86_64) cases ++ map (row 1 aarch64) cases ++ map (row 2 riscV) cases.
