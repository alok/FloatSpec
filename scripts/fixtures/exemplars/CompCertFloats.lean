/-
FloatSpec exemplar lane: CompCertFloats (shared prelude), the Lean
counterpart of CompCertFloats.v.

Provenance: transliterates the trimmed CompCert lib/IEEE754_extra.v,
lib/Floats.v, lib/Zbits.v and {x86_64,aarch64,riscV}/Archi.v at commit
bd2b3826ccc94127995de44a44166745891c1260 (Copyright Institut National de
Recherche en Informatique et en Automatique; Xavier Leroy and Jacques-Henri
Jourdan; GNU LGPL version 2.1 or later, also under the INRIA Non-Commercial
License Agreement). This transliteration is distributed under the same
terms. CompCertFloats.v lists the trimming.

Differences from the Rocq side:
- `Pos.lor`, `Pos.div2`, `Pos.shiftl_nat`, `Pos.shiftr_nat`, `Pos.testbit`,
  `Z.to_pos`, `Z.land` and `Z.lor` are Rocq standard-library functions with
  no FloatSpec port. They are transliterated here from Rocq 9.1
  `BinNums/PosDef.v` and `PArith/BinPosDef.v` onto FloatSpec's `Positive`.
  `Z.land` and `Z.lor` use two's-complement semantics on `Int`.
- CompCert proves that quiet payloads satisfy `nan_pl` (`quiet_nan_64_proof`
  via `normalized_nan`); this file does not port that proof. It decides
  `nan_pl` at run time instead. If the check ever failed, the result would be
  the marker NaN with payload 1 and sign true. No quiet NaN can have that
  payload, so a failure would show up as a mismatch; it never falls back
  silently to a legitimate default.
- FloatSpec's `Binary` operations take the IEEE rounding mode as
  `RoundingMode.RNE` (Flocq `mode_NE`) and need `Monotone_exp` instances
  for the FLT exponent function, which Flocq does not require.
-/
import FloatSpec.src.IEEE754.Bits

namespace Exemplars.CompCertFloats

open FloatSpec.Core
open FloatSpec.Core.Zaux (Positive iter_nat)

instance : Prec_gt_0 (53 : Int) := ⟨by decide⟩
instance : Prec_lt_emax (53 : Int) (1024 : Int) := ⟨by decide⟩
instance : Prec_gt_0 (24 : Int) := ⟨by decide⟩
instance : Prec_lt_emax (24 : Int) (128 : Int) := ⟨by decide⟩
instance : Generic_fmt.Monotone_exp (FLT_exp (3 - (1024 : Int) - (53 : Int)) (53 : Int)) := by
  refine ⟨?_⟩
  intro a b hab
  simp [FLT_exp, FLT.FLT_exp]
  grind
instance : Generic_fmt.Monotone_exp (FLT_exp (3 - (128 : Int) - (24 : Int)) (24 : Int)) := by
  refine ⟨?_⟩
  intro a b hab
  simp [FLT_exp, FLT.FLT_exp]
  grind

/-! ### Rocq standard-library positives (BinNums/PosDef.v, PArith/BinPosDef.v) -/

namespace Pos

/-- `Pos.lor`. -/
def lor : Positive → Positive → Positive
  | .xH, .xO q => .xI q
  | .xH, q => q
  | .xO p, .xH => .xI p
  | p, .xH => p
  | .xO p, .xO q => .xO (lor p q)
  | .xO p, .xI q => .xI (lor p q)
  | .xI p, .xO q => .xI (lor p q)
  | .xI p, .xI q => .xI (lor p q)

/-- `Pos.div2`: division by 2 rounded below, except `div2 1 = 1`. -/
def div2 : Positive → Positive
  | .xH => .xH
  | .xO p => p
  | .xI p => p

/-- `Pos.shiftl_nat p n = nat_rect _ p (fun _ => xO) n`. -/
def shiftl_nat (p : Positive) : Nat → Positive
  | 0 => p
  | n + 1 => .xO (shiftl_nat p n)

/-- `Pos.shiftr_nat p n = nat_rect _ p (fun _ => div2) n`. -/
def shiftr_nat (p : Positive) : Nat → Positive
  | 0 => p
  | n + 1 => div2 (shiftr_nat p n)

/-- `Pos.testbit`, with the `N` index as a natural number. -/
def testbit : Positive → Nat → Bool
  | .xO _, 0 => false
  | _, 0 => true
  | .xH, _ + 1 => false
  | .xO p, n + 1 => testbit p n
  | .xI p, n + 1 => testbit p n

end Pos

/-- Bitwise difference `m ∧ ¬n` on naturals (`N.ldiff`). -/
def N_ldiff (m n : Nat) : Nat := m ^^^ (m &&& n)

/-- `Z.land`, two's complement (a negative `-(n+1)` has the bits of `¬n`). -/
def Z_land : Int → Int → Int
  | .ofNat m, .ofNat n => .ofNat (m &&& n)
  | .ofNat m, .negSucc n => .ofNat (N_ldiff m n)
  | .negSucc m, .ofNat n => .ofNat (N_ldiff n m)
  | .negSucc m, .negSucc n => .negSucc (m ||| n)

/-- `Z.lor`, two's complement. -/
def Z_lor : Int → Int → Int
  | .ofNat m, .ofNat n => .ofNat (m ||| n)
  | .ofNat m, .negSucc n => .negSucc (N_ldiff n m)
  | .negSucc m, .ofNat n => .negSucc (N_ldiff m n)
  | .negSucc m, .negSucc n => .negSucc (m &&& n)

/-- `Z.to_pos`: `Zpos p ↦ p`, anything else `↦ 1`. -/
def Z_to_pos (z : Int) : Positive :=
  if h : 0 < z then binaryPositiveOfNat z.toNat (by grind) else .xH

/-! ### lib/Zbits.v -/

def P_mod_two_p (p : Positive) : Nat → Int
  | 0 => 0
  | m + 1 =>
      match p with
      | .xH => 1
      | .xO q => 2 * P_mod_two_p q m
      | .xI q => 2 * P_mod_two_p q m + 1

/-! ### lib/Floats.v: NaN payloads -/

/-- A NaN that no CompCert NaN handler returns (see the file header). -/
def impossible_nan64 : {x : binary64 // is_nan 53 1024 x = true} :=
  ⟨binary_float.B754_nan true .xH (by decide +kernel), rfl⟩
def impossible_nan32 : {x : binary32 // is_nan 24 128 x = true} :=
  ⟨binary_float.B754_nan true .xH (by decide +kernel), rfl⟩

def quiet_nan_64_payload (p : Positive) : Positive :=
  Z_to_pos (P_mod_two_p (Pos.lor p (iter_nat .xO 51 .xH)) 52)

def quiet_nan_64 (sp : Bool × Positive) : {x : binary64 // is_nan 53 1024 x = true} :=
  let (s, p) := sp
  if h : nan_pl 53 (quiet_nan_64_payload p) = true then
    ⟨binary_float.B754_nan s (quiet_nan_64_payload p) h, rfl⟩
  else impossible_nan64

def quiet_nan_32_payload (p : Positive) : Positive :=
  Z_to_pos (P_mod_two_p (Pos.lor p (iter_nat .xO 22 .xH)) 23)

def quiet_nan_32 (sp : Bool × Positive) : {x : binary32 // is_nan 24 128 x = true} :=
  let (s, p) := sp
  if h : nan_pl 24 (quiet_nan_32_payload p) = true then
    ⟨binary_float.B754_nan s (quiet_nan_32_payload p) h, rfl⟩
  else impossible_nan32

def expand_nan_payload (p : Positive) : Positive := Pos.shiftl_nat p 29

def expand_nan (s : Bool) (p : Positive) : {x : binary64 // is_nan 53 1024 x = true} :=
  if h : nan_pl 53 (expand_nan_payload p) = true then
    ⟨binary_float.B754_nan s (expand_nan_payload p) h, rfl⟩
  else impossible_nan64

def reduce_nan_payload (p : Positive) : Positive :=
  Pos.shiftr_nat (quiet_nan_64_payload p) 29

/-! ### Archi.v, as a structure -/

structure Archi where
  default_nan_64 : Bool × Positive
  default_nan_32 : Bool × Positive
  choose_nan_64 : List (Bool × Positive) → Bool × Positive
  choose_nan_32 : List (Bool × Positive) → Bool × Positive
  fma_order_zxy : Bool
  fma_invalid_mul_is_nan : Bool
  float_of_single_preserves_sNaN : Bool
  float_conversion_default_nan : Bool

/-- x86_64/Archi.v: always choose the first NaN argument, if any. -/
def x86_64 : Archi :=
  let default_nan_64 := (true, iter_nat .xO 51 .xH)
  let default_nan_32 := (true, iter_nat .xO 22 .xH)
  { default_nan_64, default_nan_32
    choose_nan_64 := fun l => match l with | [] => default_nan_64 | n :: _ => n
    choose_nan_32 := fun l => match l with | [] => default_nan_32 | n :: _ => n
    fma_order_zxy := false
    fma_invalid_mul_is_nan := false
    float_of_single_preserves_sNaN := false
    float_conversion_default_nan := false }

/-- aarch64/Archi.v `choose_nan`: the first signaling NaN, if any; otherwise
the first NaN; otherwise the default. -/
def choose_nan (is_signaling : Positive → Bool) (default : Bool × Positive)
    (l0 : List (Bool × Positive)) : Bool × Positive :=
  let rec choose_snan : List (Bool × Positive) → Bool × Positive
    | [] => match l0 with | [] => default | n :: _ => n
    | n :: l1 => if is_signaling n.2 then n else choose_snan l1
  choose_snan l0

def aarch64 : Archi :=
  let default_nan_64 := (false, iter_nat .xO 51 .xH)
  let default_nan_32 := (false, iter_nat .xO 22 .xH)
  { default_nan_64, default_nan_32
    choose_nan_64 := choose_nan (fun p => !(Pos.testbit p 51)) default_nan_64
    choose_nan_32 := choose_nan (fun p => !(Pos.testbit p 22)) default_nan_32
    fma_order_zxy := true
    fma_invalid_mul_is_nan := true
    float_of_single_preserves_sNaN := false
    float_conversion_default_nan := false }

/-- riscV/Archi.v: always the default NaN. -/
def riscV : Archi :=
  let default_nan_64 := (false, iter_nat .xO 51 .xH)
  let default_nan_32 := (false, iter_nat .xO 22 .xH)
  { default_nan_64, default_nan_32
    choose_nan_64 := fun _ => default_nan_64
    choose_nan_32 := fun _ => default_nan_32
    fma_order_zxy := false
    fma_invalid_mul_is_nan := false
    float_of_single_preserves_sNaN := false
    float_conversion_default_nan := true }

/-! ### lib/IEEE754_extra.v -/

section Extra
variable {prec emax : Int} [Prec_gt_0 prec] [Prec_lt_emax prec emax]

def BofZ (n : Int) : binary_float prec emax :=
  Binary.binary_normalize (prec := prec) (emax := emax) .RNE n 0 false

/-- `Z.pow_pos radix2 e` is `Zpower 2 e` for positive `e`; the Lean
`binary_float` stores the exponent as an integer, so the three Rocq patterns
`Zpos e`, `0`, `Zneg e` become a sign test. -/
def ZofB (f : binary_float prec emax) : Option Int :=
  match f with
  | .B754_finite s m e _ =>
      if 0 < e then some (Zaux.cond_Zopp s (Zaux.Zpos m) * Zaux.Zpower 2 e)
      else if e = 0 then some (Zaux.cond_Zopp s (Zaux.Zpos m))
      else some (Zaux.cond_Zopp s (Zaux.Zpos m / Zaux.Zpower 2 (-e)))
  | .B754_zero _ => some 0
  | _ => none

def ZofB_range (f : binary_float prec emax) (zmin zmax : Int) : Option Int :=
  match ZofB f with
  | none => none
  | some z => if decide (zmin ≤ z) && decide (z ≤ zmax) then some z else none

end Extra

def Bconv {prec1 emax1 prec2 emax2 : Int} [Prec_gt_0 prec2] [Prec_lt_emax prec2 emax2]
    (conv_nan : binary_float prec1 emax1 → {x : binary_float prec2 emax2 // Binary.is_nan x = true})
    (md : RoundingMode) (f : binary_float prec1 emax1) : binary_float prec2 emax2 :=
  match f with
  | .B754_nan _ _ _ => Binary.build_nan (conv_nan f)
  | .B754_infinity s => .B754_infinity s
  | .B754_zero s => .B754_zero s
  | .B754_finite s m e _ =>
      Binary.binary_normalize (prec := prec2) (emax := emax2) md
        (Zaux.cond_Zopp s (Zaux.Zpos m)) e s

/-! ### Integers.v, on integers -/

def repr (w z : Int) : Int := z % 2 ^ w.toNat
def signed (w x : Int) : Int := if x < 2 ^ (w - 1).toNat then x else x - 2 ^ w.toNat
def hiword (l : Int) : Int := l / 2 ^ 32
def loword (l : Int) : Int := l % 2 ^ 32
def ofwords (hi lo : Int) : Int := hi * 2 ^ 32 + lo

/-! ### lib/Floats.v: conversions that do not depend on Archi -/

def to_int (f : binary64) : Option Int :=
  (ZofB_range (prec := 53) (emax := 1024) f (-2 ^ 31) (2 ^ 31 - 1)).map (repr 32)
def to_intu (f : binary64) : Option Int :=
  (ZofB_range (prec := 53) (emax := 1024) f 0 (2 ^ 32 - 1)).map (repr 32)
def to_long (f : binary64) : Option Int :=
  (ZofB_range (prec := 53) (emax := 1024) f (-2 ^ 63) (2 ^ 63 - 1)).map (repr 64)
def to_longu (f : binary64) : Option Int :=
  (ZofB_range (prec := 53) (emax := 1024) f 0 (2 ^ 64 - 1)).map (repr 64)

def of_int (n : Int) : binary64 := BofZ (prec := 53) (emax := 1024) (signed 32 n)
def of_intu (n : Int) : binary64 := BofZ (prec := 53) (emax := 1024) n
def of_long (n : Int) : binary64 := BofZ (prec := 53) (emax := 1024) (signed 64 n)
def of_longu (n : Int) : binary64 := BofZ (prec := 53) (emax := 1024) n

def to_bits (f : binary64) : Int := repr 64 (bits_of_b64 f)
def of_bits (b : Int) : binary64 := b64_of_bits b
def from_words (hi lo : Int) : binary64 := of_bits (ofwords hi lo)

def of_long32 (n : Int) : binary32 := BofZ (prec := 24) (emax := 128) (signed 64 n)
def of_longu32 (n : Int) : binary32 := BofZ (prec := 24) (emax := 128) n
def to_bits32 (f : binary32) : Int := repr 32 (bits_of_b32 f)
def of_bits32 (b : Int) : binary32 := b32_of_bits b

/-! ### lib/Floats.v: Float and Float32 for a given Archi -/

section Floats
variable (A : Archi)

def default_nan_64 := quiet_nan_64 A.default_nan_64
def default_nan_32 := quiet_nan_32 A.default_nan_32

def of_single_nan (f : binary32) : {x : binary64 // is_nan 53 1024 x = true} :=
  match f with
  | .B754_nan s p _ =>
      if A.float_conversion_default_nan then default_nan_64 A
      else if A.float_of_single_preserves_sNaN then expand_nan s p
      else quiet_nan_64 (s, expand_nan_payload p)
  | _ => default_nan_64 A

def to_single_nan (f : binary64) : {x : binary32 // is_nan 24 128 x = true} :=
  match f with
  | .B754_nan s p _ =>
      if A.float_conversion_default_nan then default_nan_32 A
      else quiet_nan_32 (s, reduce_nan_payload p)
  | _ => default_nan_32 A

def neg_nan (f : binary64) : {x : binary64 // is_nan 53 1024 x = true} :=
  match f with
  | .B754_nan s p h => ⟨.B754_nan (!s) p h, rfl⟩
  | _ => default_nan_64 A

def abs_nan (f : binary64) : {x : binary64 // is_nan 53 1024 x = true} :=
  match f with
  | .B754_nan _ p h => ⟨.B754_nan false p h, rfl⟩
  | _ => default_nan_64 A

def cons_pl (x : binary64) (l : List (Bool × Positive)) : List (Bool × Positive) :=
  match x with
  | .B754_nan s p _ => (s, p) :: l
  | _ => l

def unop_nan (x : binary64) : {x : binary64 // is_nan 53 1024 x = true} :=
  quiet_nan_64 (A.choose_nan_64 (cons_pl x []))

def binop_nan (x y : binary64) : {x : binary64 // is_nan 53 1024 x = true} :=
  quiet_nan_64 (A.choose_nan_64 (cons_pl x (cons_pl y [])))

def fma_order {T : Type} (x y z : T) : T × T × T :=
  if A.fma_order_zxy then (z, x, y) else (x, y, z)

def fma_nan_1 (x y z : binary64) : {x : binary64 // is_nan 53 1024 x = true} :=
  let (a, b, c) := fma_order A x y z
  quiet_nan_64 (A.choose_nan_64 (cons_pl a (cons_pl b (cons_pl c []))))

def fma_nan (x y z : binary64) : {x : binary64 // is_nan 53 1024 x = true} :=
  match x, y with
  | .B754_infinity _, .B754_zero _ | .B754_zero _, .B754_infinity _ =>
      if A.fma_invalid_mul_is_nan then
        quiet_nan_64 (A.choose_nan_64 (A.default_nan_64 :: cons_pl z []))
      else fma_nan_1 A x y z
  | _, _ => fma_nan_1 A x y z

def neg (x : binary64) : binary64 := Binary.Bopp (neg_nan A) x
def abs (x : binary64) : binary64 := Binary.Babs (abs_nan A) x
def sqrt (x : binary64) : binary64 := Binary.Bsqrt (unop_nan A) .RNE x
def add (x y : binary64) : binary64 := Binary.Bplus (binop_nan A) .RNE x y
def sub (x y : binary64) : binary64 := Binary.Bminus (binop_nan A) .RNE x y
def mul (x y : binary64) : binary64 := Binary.Bmult (binop_nan A) .RNE x y
def div (x y : binary64) : binary64 := Binary.Bdiv (binop_nan A) .RNE x y
def fma (x y z : binary64) : binary64 := Binary.Bfma (fma_nan A) .RNE x y z

def of_single (f : binary32) : binary64 :=
  Bconv (prec2 := 53) (emax2 := 1024) (of_single_nan A) .RNE f
def to_single (f : binary64) : binary32 :=
  Bconv (prec2 := 24) (emax2 := 128) (to_single_nan A) .RNE f

/-- Module `Float32`. -/
def neg_nan32 (f : binary32) : {x : binary32 // is_nan 24 128 x = true} :=
  match f with
  | .B754_nan s p h => ⟨.B754_nan (!s) p h, rfl⟩
  | _ => default_nan_32 A

def cons_pl32 (x : binary32) (l : List (Bool × Positive)) : List (Bool × Positive) :=
  match x with
  | .B754_nan s p _ => (s, p) :: l
  | _ => l

def binop_nan32 (x y : binary32) : {x : binary32 // is_nan 24 128 x = true} :=
  quiet_nan_32 (A.choose_nan_32 (cons_pl32 x (cons_pl32 y [])))

def neg32 (x : binary32) : binary32 := Binary.Bopp (neg_nan32 A) x
def add32 (x y : binary32) : binary32 := Binary.Bplus (binop_nan32 A) .RNE x y
def mul32 (x y : binary32) : binary32 := Binary.Bmult (binop_nan32 A) .RNE x y
def of_double32 : binary64 → binary32 := to_single A

end Floats

end Exemplars.CompCertFloats
