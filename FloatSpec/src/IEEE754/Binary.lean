-- IEEE-754 binary arithmetic
-- Translated from Coq file: flocq/src/IEEE754/Binary.v

import FloatSpec.src.Core
import FloatSpec.src.Compat
import FloatSpec.src.Calc
import FloatSpec.Linter.CoqSourceLinter
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Nat.BinaryRec

open Real

-- Local boolean negation alias (to mirror Coq's `bnot`)
def bnot (b : Bool) : Bool := !b

-- Coq: full_float
@[flocq_source "src/IEEE754/Binary.v" 33 "full_float"]
inductive full_float where
  | F754_zero (s : Bool) : full_float
  | F754_infinity (s : Bool) : full_float
  | F754_nan (s : Bool) (m : FloatSpec.Core.Zaux.Positive) : full_float
  | F754_finite (s : Bool) (m : FloatSpec.Core.Zaux.Positive) (e : Int) : full_float

-- IEEE 754 full float representation
inductive FullFloat where
  | F754_zero (s : Bool) : FullFloat
  | F754_infinity (s : Bool) : FullFloat
  | F754_nan (s : Bool) (m : Nat) : FullFloat
  | F754_finite (s : Bool) (m : Nat) (e : Int) : FullFloat
deriving DecidableEq

-- Standard float representation
inductive StandardFloat where
  | S754_zero (s : Bool) : StandardFloat
  | S754_infinity (s : Bool) : StandardFloat
  | S754_nan : StandardFloat
  | S754_finite (s : Bool) (m : Nat) (e : Int) : StandardFloat
deriving DecidableEq

-- Conversion from FullFloat to StandardFloat
def FF2SF (x : FullFloat) : StandardFloat :=
  match x with
  | FullFloat.F754_zero s => StandardFloat.S754_zero s
  | FullFloat.F754_infinity s => StandardFloat.S754_infinity s
  | FullFloat.F754_nan _ _ => StandardFloat.S754_nan
  | FullFloat.F754_finite s m e => StandardFloat.S754_finite s m e

-- Conversion from FullFloat to real number
noncomputable def FF2R (beta : Int) [ValidRadix beta] (x : FullFloat) : ℝ :=
  match x with
  | FullFloat.F754_finite s m e =>
    F2R (FloatSpec.Core.Defs.FlocqFloat.mk (if s then -(m : Int) else (m : Int)) e : FloatSpec.Core.Defs.FlocqFloat beta)
  | _ => 0

-- Conversion from StandardFloat to real number
noncomputable def SF2R (beta : Int) [ValidRadix beta] (x : StandardFloat) : ℝ :=
  match x with
  | StandardFloat.S754_finite s m e =>
    F2R (FloatSpec.Core.Defs.FlocqFloat.mk (if s then -(m : Int) else (m : Int)) e : FloatSpec.Core.Defs.FlocqFloat beta)
  | _ => 0

-- SF2R and FF2SF consistency
theorem SF2R_FF2SF (beta : Int) [ValidRadix beta] (x : FullFloat) :
  SF2R beta (FF2SF x) = FF2R beta x := by
  cases x <;> rfl

-- Conversion from StandardFloat to FullFloat
def SF2FF (x : StandardFloat) : FullFloat :=
  match x with
  | StandardFloat.S754_zero s => FullFloat.F754_zero s
  | StandardFloat.S754_infinity s => FullFloat.F754_infinity s
  | StandardFloat.S754_nan => FullFloat.F754_nan false 1
  | StandardFloat.S754_finite s m e => FullFloat.F754_finite s m e

-- Round-trip property
theorem FF2SF_SF2FF (x : StandardFloat) :
  FF2SF (SF2FF x) = x := by
  cases x <;> rfl

-- FF2R after SF2FF equals SF2R
theorem FF2R_SF2FF (beta : Int) [ValidRadix beta] (x : StandardFloat) :
  FF2R beta (SF2FF x) = SF2R beta x := by
  cases x <;> rfl

-- NaN detection for FullFloat
def is_nan_FF (f : FullFloat) : Bool :=
  match f with
  | FullFloat.F754_nan _ _ => true
  | _ => false

-- NaN detection for StandardFloat
def is_nan_SF (f : StandardFloat) : Bool :=
  match f with
  | StandardFloat.S754_nan => true
  | _ => false

-- Sign extraction for FullFloat
def sign_FF (x : FullFloat) : Bool :=
  match x with
  | FullFloat.F754_nan s _ => s
  | FullFloat.F754_zero s => s
  | FullFloat.F754_infinity s => s
  | FullFloat.F754_finite s _ _ => s

-- Finite check for FullFloat
def is_finite_FF (f : FullFloat) : Bool :=
  match f with
  | FullFloat.F754_finite _ _ _ => true
  | FullFloat.F754_zero _ => true
  | _ => false

namespace full_float

/-- Lossless embedding of FLoCq's Positive-payload carrier into the legacy
Nat-payload carrier used by the original Lean translation. -/
def toFullFloat : full_float → FullFloat
  | F754_zero s => FullFloat.F754_zero s
  | F754_infinity s => FullFloat.F754_infinity s
  | F754_nan s p => FullFloat.F754_nan s (FloatSpec.Core.Zaux.positiveToNat p)
  | F754_finite s m e =>
      FullFloat.F754_finite s (FloatSpec.Core.Zaux.positiveToNat m) e

def toStandardFloat : full_float → StandardFloat
  | F754_zero s => StandardFloat.S754_zero s
  | F754_infinity s => StandardFloat.S754_infinity s
  | F754_nan _ _ => StandardFloat.S754_nan
  | F754_finite s m e =>
      StandardFloat.S754_finite s (FloatSpec.Core.Zaux.positiveToNat m) e

noncomputable def toReal (beta : Int) [ValidRadix beta] : full_float → ℝ
  | F754_finite s m e =>
      F2R (FloatSpec.Core.Defs.FlocqFloat.mk
        (if s then -(FloatSpec.Core.Zaux.positiveToNat m : Int)
         else (FloatSpec.Core.Zaux.positiveToNat m : Int)) e :
          FloatSpec.Core.Defs.FlocqFloat beta)
  | _ => 0

def isNaN : full_float → Bool
  | F754_nan _ _ => true
  | _ => false

def isFinite : full_float → Bool
  | F754_zero _ | F754_finite _ _ _ => true
  | _ => false

def sign : full_float → Bool
  | F754_zero s | F754_infinity s | F754_nan s _ | F754_finite s _ _ => s

theorem toFullFloat_toStandardFloat (x : full_float) :
    FF2SF (toFullFloat x) = toStandardFloat x := by
  cases x <;> rfl

theorem toFullFloat_toReal (beta : Int) [ValidRadix beta] (x : full_float) :
    FF2R beta (toFullFloat x) = toReal beta x := by
  cases x <;> rfl

theorem toFullFloat_isNaN (x : full_float) :
    is_nan_FF (toFullFloat x) = isNaN x := by
  cases x <;> rfl

theorem toFullFloat_isFinite (x : full_float) :
    is_finite_FF (toFullFloat x) = isFinite x := by
  cases x <;> rfl

theorem toFullFloat_sign (x : full_float) :
    sign_FF (toFullFloat x) = sign x := by
  cases x <;> rfl

theorem toFullFloat_injective : Function.Injective toFullFloat := by
  intro x y h
  cases x <;> cases y <;>
    simp_all [toFullFloat]
  all_goals
    congr
    exact FloatSpec.Core.Zaux.positiveToNat_injective (by aesop)

end full_float

-- NaN detection consistency
theorem is_nan_SF2FF (x : StandardFloat) :
  is_nan_FF (SF2FF x) = is_nan_SF x := by
  cases x <;> rfl

-- NaN detection consistency in the other direction
theorem is_nan_FF2SF (x : FullFloat) :
  is_nan_SF (FF2SF x) = is_nan_FF x := by
  cases x <;> rfl

-- Round-trip when not NaN (Coq: SF2FF_FF2SF)
theorem SF2FF_FF2SF (x : FullFloat)
  (hnotnan : is_nan_FF x = false) :
  SF2FF (FF2SF x) = x := by
  cases x <;> simp [FF2SF, SF2FF, is_nan_FF] at hnotnan ⊢

-- Build a NaN value (Coq: build_nan)
def build_nan (s : Bool) (payload : Nat) : FullFloat :=
  FullFloat.F754_nan s payload

-- Coq: is_nan_build_nan — building a NaN yields a NaN
theorem is_nan_build_nan_compat (s : Bool) (payload : Nat) :
    is_nan_FF (build_nan s payload) = true := by
  rfl

-- Real value of a freshly built NaN is zero (Coq: B2R_build_nan)
theorem B2R_build_nan_compat (s : Bool) (payload : Nat) :
    FF2R 2 (build_nan s payload) = 0 := by
  rfl

-- Finiteness check of a freshly built NaN is false (Coq: is_finite_build_nan)
theorem is_finite_build_nan_compat (s : Bool) (payload : Nat) :
    is_finite_FF (build_nan s payload) = false := by
  rfl

-- Coq: `nan_pl pl := Zlt_bool (Zpos (digits2_pos pl)) prec`.
@[flocq_source "src/IEEE754/Binary.v" 161 "nan_pl"]
def nan_pl (prec : Int) (pl : FloatSpec.Core.Zaux.Positive) : Bool :=
  FloatSpec.Core.Zaux.Zlt_bool
    (FloatSpec.Core.Digits.digits2_pos
      (FloatSpec.Core.Zaux.positiveToNat pl))
    prec

-- Existing range-only validity check used by the current Lean compatibility
-- carriers. The Coq-aligned `SpecFloat.bounded` shape is `specFloat_bounded`
-- below.
def bounded {prec emax : Int} (mx : Nat) (ex : Int) : Bool :=
  -- IEEE 754 bounded predicate: mantissa has at most prec digits and exponent is valid.
  decide (mx < (2 : Nat) ^ prec.toNat) && decide ((3 - emax - prec) ≤ ex) &&
    decide (ex ≤ emax - prec)

-- Coq: canonical_mantissa
-- In Coq: `canonical_mantissa prec emax mx ex := (ex =? fexp (Zdigits radix2 mx + ex))`
def canonical_mantissa {prec emax : Int} (m : Nat) (e : Int) : Bool :=
  e == FLT_exp (3 - emax - prec) prec (FloatSpec.Core.Digits.Zdigits 2 m + e)

-- Coq-aligned `SpecFloat.bounded prec emax`.
-- Upstream combines canonical mantissa with the upper exponent bound; the
-- existing public `bounded` remains the local range-only compatibility check.
def specFloat_bounded {prec emax : Int} (m : Nat) (e : Int) : Bool :=
  canonical_mantissa (prec:=prec) (emax:=emax) m e &&
    decide (e ≤ emax - prec)

-- Extract a NaN payload.
def get_nan_pl (x : FullFloat) : Nat :=
  match x with
  | FullFloat.F754_nan _ pl => pl
  | _ => 1

-- Coq: build_nan_correct — for x with is_nan x = true, build_nan x = x.
-- Here we rebuild a NaN from the sign and payload of `x` and assert equality.
theorem build_nan_correct_compat (x : { f : FullFloat // is_nan_FF f = true }) :
    build_nan (sign_FF x.val) (get_nan_pl x.val) = x.val := by
  rcases x with ⟨f, hf⟩
  cases f <;> simp [build_nan, sign_FF, get_nan_pl, is_nan_FF] at hf ⊢

-- A no-op erasure on FullFloat (Coq: erase)
def erase (x : FullFloat) : FullFloat := x

theorem erase_correct_compat (x : FullFloat) : erase x = x := by
  rfl

-- Opposite (negation) on FullFloat (Coq: Bopp)
def Bopp (x : FullFloat) : FullFloat :=
  match x with
  | FullFloat.F754_nan s pl => FullFloat.F754_nan (bnot s) pl
  | FullFloat.F754_infinity s => FullFloat.F754_infinity (bnot s)
  | FullFloat.F754_finite s m e => FullFloat.F754_finite (bnot s) m e
  | FullFloat.F754_zero s => FullFloat.F754_zero (bnot s)

theorem Bopp_involutive_compat (x : FullFloat)
    (hx : is_nan_FF x = false) :
    Bopp (Bopp x) = x := by
  cases x <;> simp [Bopp, bnot, is_nan_FF] at hx ⊢

theorem B2R_Bopp_compat (x : FullFloat) :
    FF2R 2 (Bopp x) = - FF2R 2 x := by
  cases x with
  | F754_zero s =>
      simp [FF2R, Bopp]
  | F754_infinity s =>
      simp [FF2R, Bopp]
  | F754_nan s m =>
      simp [FF2R, Bopp]
  | F754_finite s m e =>
      simp [FF2R, Bopp, bnot, F2R,
        FloatSpec.Core.Defs.F2R]
      cases s <;> simp

theorem is_finite_Bopp_compat (x : FullFloat) :
    is_finite_FF (Bopp x) = is_finite_FF x := by
  cases x <;> simp [is_finite_FF, Bopp]

theorem Bsign_Bopp_compat (x : FullFloat) (hx : is_nan_FF x = false) :
    sign_FF (Bopp x) = bnot (sign_FF x) := by
  cases x <;>
    simp [sign_FF, Bopp, bnot, is_nan_FF] at hx ⊢

-- Absolute value on FullFloat (Coq: Babs)
def Babs (x : FullFloat) : FullFloat :=
  match x with
  | FullFloat.F754_nan s pl => FullFloat.F754_nan s pl
  | FullFloat.F754_infinity _ => FullFloat.F754_infinity false
  | FullFloat.F754_finite _ m e => FullFloat.F754_finite false m e
  | FullFloat.F754_zero _ => FullFloat.F754_zero false

theorem B2R_Babs_compat (x : FullFloat) :
    FF2R 2 (Babs x) = |FF2R 2 x| := by
  cases x with
  | F754_zero s =>
      simp [FF2R, Babs]
  | F754_infinity s =>
      simp [FF2R, Babs]
  | F754_nan s m =>
      simp [FF2R, Babs]
  | F754_finite s m e =>
      simp [FF2R, Babs, F2R, FloatSpec.Core.Defs.F2R]
      cases s <;> simp

theorem is_finite_Babs_compat (x : FullFloat) :
    is_finite_FF (Babs x) = is_finite_FF x := by
  cases x <;> simp [is_finite_FF, Babs]

theorem Bsign_Babs_compat (x : FullFloat) (hx : is_nan_FF x = false) :
    sign_FF (Babs x) = false := by
  cases x <;>
    simp [sign_FF, Babs, is_nan_FF] at hx ⊢

theorem Babs_idempotent_compat (x : FullFloat) (hx : is_nan_FF x = false) :
    Babs (Babs x) = Babs x := by
  cases x <;> simp [Babs, is_nan_FF] at hx ⊢

theorem Babs_Bopp_compat (x : FullFloat) (hx : is_nan_FF x = false) :
    Babs (Bopp x) = Babs x := by
  cases x <;>
    simp [Babs, Bopp, bnot, is_nan_FF] at hx ⊢

-- Sign extraction for StandardFloat
def sign_SF (x : StandardFloat) : Bool :=
  match x with
  | StandardFloat.S754_zero s => s
  | StandardFloat.S754_infinity s => s
  | StandardFloat.S754_nan => false
  | StandardFloat.S754_finite s _ _ => s

-- Finite check for StandardFloat
def is_finite_SF (f : StandardFloat) : Bool :=
  match f with
  | StandardFloat.S754_finite _ _ _ => true
  | StandardFloat.S754_zero _ => true
  | _ => false

-- Finite check consistency
theorem is_finite_SF2FF (x : StandardFloat) :
  is_finite_FF (SF2FF x) = is_finite_SF x := by
  cases x <;> rfl

-- Finite predicate in the other direction
theorem is_finite_FF2SF (x : FullFloat) :
  is_finite_SF (FF2SF x) = is_finite_FF x := by
  cases x <;> rfl

-- Sign consistency
theorem sign_SF2FF (x : StandardFloat) :
  sign_FF (SF2FF x) = sign_SF x := by
  cases x <;> rfl

-- Sign consistency in the other direction
theorem sign_FF2SF (x : FullFloat) :
  sign_SF (FF2SF x) = (if is_nan_FF x then false else sign_FF x) := by
  cases x <;> rfl

-- Section: Binary IEEE 754 formats

variable (prec emax : Int)
variable [Prec_gt_0 prec]
variable [Prec_lt_emax prec emax]

-- IEEE 754 binary format
@[flocq_source "src/IEEE754/Binary.v" 184 "binary_float"]
inductive binary_float (prec emax : Int) where
  | B754_zero (s : Bool) : binary_float prec emax
  | B754_infinity (s : Bool) : binary_float prec emax
  | B754_nan (s : Bool) (pl : FloatSpec.Core.Zaux.Positive) :
      nan_pl prec pl = true → binary_float prec emax
  | B754_finite (s : Bool) (m : FloatSpec.Core.Zaux.Positive) (e : Int) :
      specFloat_bounded (prec:=prec) (emax:=emax) (FloatSpec.Core.Zaux.positiveToNat m) e = true →
        binary_float prec emax

-- Existing permissive compatibility wrapper. This is intentionally distinct
-- from the exact Flocq `binary_float` inductive above.
structure Binary754 (prec emax : Int) where
  val : FullFloat
  valid : is_finite_FF val = true →
    -- Valid range and precision constraints
    True

-- Helper conversions between FullFloat and Binary754
def B2FF {prec emax} (x : Binary754 prec emax) : FullFloat := x.val
def FF2B {prec emax} (x : FullFloat) : Binary754 prec emax :=
  { val := x, valid := by intro; trivial }

-- Real semantics for `Binary754` (Coq: B2R)
noncomputable def B2R {prec emax} (x : Binary754 prec emax) : ℝ :=
  FF2R 2 x.val

-- Standard view to standard-float (Coq: B2SF)
def B2SF {prec emax} (x : Binary754 prec emax) : StandardFloat :=
  FF2SF x.val

-- Recurse over bits, not the numeric value: a binary64 mantissa can exceed
-- 2^52. The zero branch is unreachable through the public positive API.
private def binaryPositiveOfNatBits : Nat → FloatSpec.Core.Zaux.Positive :=
  Nat.binaryRecFromOne .xH .xH (fun bit _ _ tail => if bit then .xI tail else .xO tail)

private theorem binaryPositiveOfNatBits_spec (n : Nat) (h : 0 < n) :
    FloatSpec.Core.Zaux.positiveToNat (binaryPositiveOfNatBits n) = n := by
  induction n using Nat.binaryRecFromOne with
  | zero => omega
  | one => simp [binaryPositiveOfNatBits, FloatSpec.Core.Zaux.positiveToNat]
  | bit bit n hn ih =>
      have ih' := ih (Nat.pos_of_ne_zero hn)
      simp only [binaryPositiveOfNatBits, Nat.binaryRecFromOne_eq bit n hn]
      cases bit <;>
        simp_all [FloatSpec.Core.Zaux.positiveToNat, Nat.bit, binaryPositiveOfNatBits]

def binaryPositiveOfNat (n : Nat) (_h : 0 < n) : FloatSpec.Core.Zaux.Positive :=
  binaryPositiveOfNatBits n

theorem binaryPositiveOfNat_spec (n : Nat) (h : 0 < n) :
    FloatSpec.Core.Zaux.positiveToNat (binaryPositiveOfNat n h) = n := by
  exact binaryPositiveOfNatBits_spec n h

-- Coq `Binary.v:valid_binary`, stated on the exact `full_float` carrier whose
-- finite and NaN payloads are already positive.
def valid_full_float_binary {prec emax : Int} (x : full_float) : Bool :=
  match x with
  | full_float.F754_finite _ m e =>
      specFloat_bounded (prec:=prec) (emax:=emax) (FloatSpec.Core.Zaux.positiveToNat m) e
  | full_float.F754_nan _ payload =>
      nan_pl prec payload
  | full_float.F754_zero _ => true
  | full_float.F754_infinity _ => true

-- Coq `Binary.v:FF2B`, on the proof-carrying `binary_float` surface.  The
-- historical `FF2B : FullFloat → Binary754` remains a compatibility wrapper.
def fullFloatToBinaryFloat {prec emax : Int} (x : full_float)
    (hx : valid_full_float_binary (prec:=prec) (emax:=emax) x = true) :
    binary_float prec emax :=
  match x with
  | full_float.F754_finite s m e =>
      binary_float.B754_finite (prec:=prec) (emax:=emax) s m e (by
        simpa [valid_full_float_binary] using hx)
  | full_float.F754_infinity s =>
      binary_float.B754_infinity (prec:=prec) (emax:=emax) s
  | full_float.F754_zero s =>
      binary_float.B754_zero (prec:=prec) (emax:=emax) s
  | full_float.F754_nan s payload =>
      binary_float.B754_nan (prec:=prec) (emax:=emax) s payload (by
        simpa [valid_full_float_binary] using hx)

-- Coq `Binary.v:B2FF`, on the proof-carrying `binary_float` surface.
def binaryFloatToFullFloat {prec emax : Int} (x : binary_float prec emax) : full_float :=
  match x with
  | binary_float.B754_finite s m e _ => full_float.F754_finite s m e
  | binary_float.B754_infinity s => full_float.F754_infinity s
  | binary_float.B754_zero s => full_float.F754_zero s
  | binary_float.B754_nan s payload _ => full_float.F754_nan s payload

theorem binaryFloatToFullFloat_fullFloatToBinaryFloat {prec emax : Int}
    (x : full_float)
    (hx : valid_full_float_binary (prec:=prec) (emax:=emax) x = true) :
    binaryFloatToFullFloat (prec:=prec) (emax:=emax)
      (fullFloatToBinaryFloat (prec:=prec) (emax:=emax) x hx) = x := by
  cases x <;> rfl

theorem valid_full_float_binary_binaryFloatToFullFloat {prec emax : Int}
    (x : binary_float prec emax) :
    valid_full_float_binary (prec:=prec) (emax:=emax)
      (binaryFloatToFullFloat (prec:=prec) (emax:=emax) x) = true := by
  cases x with
  | B754_zero s => rfl
  | B754_infinity s => rfl
  | B754_nan s payload hPayload =>
      simpa [binaryFloatToFullFloat, valid_full_float_binary] using hPayload
  | B754_finite s m e hBounded =>
      simpa [binaryFloatToFullFloat, valid_full_float_binary] using hBounded

theorem fullFloatToBinaryFloat_binaryFloatToFullFloat {prec emax : Int}
    (x : binary_float prec emax) :
    fullFloatToBinaryFloat (prec:=prec) (emax:=emax)
      (binaryFloatToFullFloat (prec:=prec) (emax:=emax) x)
      (valid_full_float_binary_binaryFloatToFullFloat (prec:=prec) (emax:=emax) x) = x := by
  cases x <;> simp [fullFloatToBinaryFloat, binaryFloatToFullFloat]

namespace binary_float

/-- FLoCq `B2FF` on the proof-carrying carrier. -/
abbrev B2FF {prec emax : Int} (x : binary_float prec emax) : full_float :=
  binaryFloatToFullFloat x

/-- FLoCq `B2R` on the proof-carrying carrier. -/
noncomputable def B2R {prec emax : Int} (x : binary_float prec emax) : ℝ :=
  match x with
  | B754_finite s m e _ =>
      F2R (FloatSpec.Core.Defs.FlocqFloat.mk
        (if s then -(FloatSpec.Core.Zaux.positiveToNat m : Int)
          else (FloatSpec.Core.Zaux.positiveToNat m : Int)) e :
            FloatSpec.Core.Defs.FlocqFloat 2)
  | _ => 0

/-- FLoCq `B2SF` on the proof-carrying carrier. -/
def B2SF {prec emax : Int} (x : binary_float prec emax) : StandardFloat :=
  match x with
  | B754_finite s m e _ =>
      StandardFloat.S754_finite s (FloatSpec.Core.Zaux.positiveToNat m) e
  | B754_infinity s => StandardFloat.S754_infinity s
  | B754_zero s => StandardFloat.S754_zero s
  | B754_nan _ _ _ => StandardFloat.S754_nan

/-- FLoCq `is_finite_strict`. -/
def is_finite_strict {prec emax : Int} (x : binary_float prec emax) : Bool :=
  match x with
  | B754_finite _ _ _ _ => true
  | _ => false

/-- Checked erasure into the legacy compatibility carrier. -/
def toBinary754 {prec emax : Int} (x : binary_float prec emax) : Binary754 prec emax :=
  { val := match x with
      | B754_finite s m e _ =>
          FullFloat.F754_finite s (FloatSpec.Core.Zaux.positiveToNat m) e
      | B754_infinity s => FullFloat.F754_infinity s
      | B754_zero s => FullFloat.F754_zero s
      | B754_nan s payload _ =>
          FullFloat.F754_nan s (FloatSpec.Core.Zaux.positiveToNat payload)
    valid := by intro; trivial }

theorem B2R_toBinary754 {prec emax : Int} (x : binary_float prec emax) :
    _root_.B2R (toBinary754 x) = B2R x := by
  cases x <;> simp [toBinary754, _root_.B2R, B2R, FF2R]

end binary_float

-- Coq: B2FF_FF2B — B2FF after FF2B is identity
theorem B2FF_FF2B_compat {prec emax} (x : FullFloat) :
  B2FF (prec:=prec) (emax:=emax) (FF2B (prec:=prec) (emax:=emax) x) = x := by
  rfl

-- Coq: FF2B_B2FF — FF2B after B2FF is identity
theorem FF2B_B2FF_compat {prec emax} (x : Binary754 prec emax) :
  FF2B (prec:=prec) (emax:=emax) (B2FF (prec:=prec) (emax:=emax) x) = x := by
  -- trivial by construction of `FF2B` and `B2FF`
  cases x <;> rfl

-- Coq: B2FF_inj — B2FF is injective
theorem B2FF_inj_compat {prec emax} (x y : Binary754 prec emax) :
  B2FF (prec:=prec) (emax:=emax) x = B2FF (prec:=prec) (emax:=emax) y → x = y := by
  intro h; cases x; cases y; cases h; rfl

-- Coq: FF2R_B2FF — Real semantics preserved by B2FF
theorem FF2R_B2FF_compat (beta : Int) [ValidRadix beta] {prec emax} (x : Binary754 prec emax) :
  FF2R beta (B2FF (prec:=prec) (emax:=emax) x) = FF2R beta x.val := by
  rfl

-- Coq: FF2SF_B2FF — Standard view after B2FF matches direct view
theorem FF2SF_B2FF_compat {prec emax} (x : Binary754 prec emax) :
  FF2SF (B2FF (prec:=prec) (emax:=emax) x) = B2SF (prec:=prec) (emax:=emax) x := by
  rfl

-- Coq: B2SF_FF2B — Standard view after FF2B equals FF2SF of source
theorem B2SF_FF2B_compat {prec emax} (x : FullFloat) :
  B2SF (prec:=prec) (emax:=emax) (FF2B (prec:=prec) (emax:=emax) x) = FF2SF x := by
  rfl

-- Coq: B2SF_B2BSN and B2R_B2BSN — compatibility between the Binary views and
-- the SingleNaN bridge. Both are stated directly in BinarySingleNaN.

-- Coq: is_finite_B2FF — Finite predicate preserved by B2FF
-- We mirror the Coq statement with a straightforward alias in our setting.
def is_finite_B {prec emax} (x : Binary754 prec emax) : Bool :=
  is_finite_FF x.val

theorem is_finite_B2FF_compat {prec emax} (x : Binary754 prec emax) :
  is_finite_FF (B2FF (prec:=prec) (emax:=emax) x) = is_finite_B (prec:=prec) (emax:=emax) x := by
  rfl

-- Coq: is_nan_B2FF — NaN predicate preserved by B2FF
def is_nan_B {prec emax} (x : Binary754 prec emax) : Bool :=
  is_nan_FF x.val

theorem is_nan_B2FF_compat {prec emax} (x : Binary754 prec emax) :
  is_nan_FF (B2FF (prec:=prec) (emax:=emax) x) = is_nan_B (prec:=prec) (emax:=emax) x := by
  rfl

-- Coq: B2R_FF2B — Real semantics after FF2B equals semantics of source
theorem B2R_FF2B_compat (beta : Int) [ValidRadix beta] {prec emax} (x : FullFloat) :
  FF2R beta (B2FF (prec:=prec) (emax:=emax) (FF2B (prec:=prec) (emax:=emax) x)) = FF2R beta x := by
  rfl

-- (reserved) Coq: B2SF_inj — provided on the SingleNaN side in this port

-- Coq: Bsign_FF2B — Sign preserved by FF2B
def Bsign {prec emax} (x : Binary754 prec emax) : Bool :=
  sign_FF x.val

theorem Bsign_FF2B_compat {prec emax} (x : FullFloat) :
  Bsign (prec:=prec) (emax:=emax) (FF2B (prec:=prec) (emax:=emax) x) = sign_FF x := by
  rfl

-- Coq: is_finite_FF2B — Finite predicate after FF2B equals source predicate
theorem is_finite_FF2B_compat {prec emax} (x : FullFloat) :
  is_finite_B (prec:=prec) (emax:=emax) (FF2B (prec:=prec) (emax:=emax) x) = is_finite_FF x := by
  rfl

-- Coq: is_nan_FF2B — NaN predicate after FF2B equals source predicate
theorem is_nan_FF2B_compat {prec emax} (x : FullFloat) :
  is_nan_B (prec:=prec) (emax:=emax) (FF2B (prec:=prec) (emax:=emax) x) = is_nan_FF x := by
  rfl

-- Strict finiteness for FullFloat (excludes zeros)
def is_finite_strict_FF (f : FullFloat) : Bool :=
  match f with
  | FullFloat.F754_finite _ _ _ => true
  | _ => false

-- Validity predicate for FullFloat: mantissa must be positive for finite floats
-- This mirrors Coq's use of `positive` type for mantissa in B754_finite
def valid_FF (f : FullFloat) : Prop :=
  match f with
  | FullFloat.F754_finite _ m _ => m > 0
  | _ => True

-- Extract mantissa from FullFloat (0 for non-finite)
def mantissa_FF (f : FullFloat) : Nat :=
  match f with
  | FullFloat.F754_finite _ m _ => m
  | _ => 0

-- Extract exponent from FullFloat (0 for non-finite)
def exponent_FF (f : FullFloat) : Int :=
  match f with
  | FullFloat.F754_finite _ _ e => e
  | _ => 0

-- Coq: B2R_inj — injectivity of representation from real semantics (under strict finiteness)
-- Note: In Flocq, this requires is_finite_strict (excludes zeros) and valid_binary constraints
-- that ensure canonical representation. Our model uses weaker constraints, so we require
-- that the mantissa and exponent match explicitly. The full Flocq version derives this from
-- the fact that valid Binary754 values have unique (m, e) representations.
-- For two Binary754 values with the same underlying FullFloat structure, they are equal.
theorem B2R_inj_compat {prec emax} (x y : Binary754 prec emax)
  (hx : is_finite_strict_FF x.val = true)
  (hy : is_finite_strict_FF y.val = true)
  (hR : B2R (prec:=prec) (emax:=emax) x = B2R (prec:=prec) (emax:=emax) y)
  (hvalx : mantissa_FF x.val > 0)
  (hvaly : mantissa_FF y.val > 0)
  (heq_e : exponent_FF x.val = exponent_FF y.val) :
  x = y := by
  -- Both x and y must be F754_finite form due to strict finiteness
  cases x with | mk xval xvalid =>
  cases y with | mk yval yvalid =>
  simp only [is_finite_strict_FF] at hx hy
  cases xval <;> simp at hx
  cases yval <;> simp at hy
  -- Now both are F754_finite sx mx ex and F754_finite sy my ey
  rename_i sx mx ex sy my ey
  simp only [mantissa_FF] at hvalx hvaly
  simp only [exponent_FF] at heq_e
  simp only [B2R, FF2R, F2R, FloatSpec.Core.Defs.F2R] at hR
  -- Since ex = ey and 2^ex > 0, we can cancel the power
  subst heq_e
  -- Now: (if sx then -mx else mx) * 2^ex = (if sy then -my else my) * 2^ex
  have h2pos : (0 : ℝ) < (2 : ℝ) ^ ex := by positivity
  have h2ne : ((2 : ℝ) ^ ex) ≠ 0 := ne_of_gt h2pos
  -- Cancel the power factor to get equality of the signed mantissas
  have hmul_cancel := mul_right_cancel₀ h2ne hR
  -- The goal type from mul_right_cancel₀ uses ↑(if sx then -↑mx else ↑mx)
  -- We need to work with this form. Case split on signs directly.
  cases hsx : sx <;> cases hsy : sy
  · -- sx = false, sy = false: both positive, mx = my
    simp only [hsx, hsy, Bool.false_eq_true, ↓reduceIte] at hmul_cancel
    have hmx_eq_my : (mx : ℝ) = (my : ℝ) := by
      -- hmul_cancel : ↑(↑mx : ℤ) = ↑(↑my : ℤ)
      have h1 : ((mx : ℤ) : ℝ) = ((my : ℤ) : ℝ) := hmul_cancel
      simp only [Int.cast_natCast] at h1
      exact h1
    have hmx_eq : mx = my := Nat.cast_injective hmx_eq_my
    simp only [hsx, hsy, hmx_eq]
  · -- sx = false, sy = true: mx = -my, contradiction with mx, my > 0
    simp only [hsx, hsy, Bool.false_eq_true, Bool.coe_true, ↓reduceIte, Int.cast_neg] at hmul_cancel
    -- hmul_cancel : ↑(↑mx : ℤ) = -(↑(↑my : ℤ))
    have h1 : ((mx : ℤ) : ℝ) = -((my : ℤ) : ℝ) := hmul_cancel
    simp only [Int.cast_neg, Int.cast_natCast] at h1
    -- h1 : (mx : ℝ) = -(my : ℝ)
    have hmxpos : (0 : ℝ) < (mx : ℝ) := Nat.cast_pos.mpr hvalx
    have hmypos : (0 : ℝ) < (my : ℝ) := Nat.cast_pos.mpr hvaly
    have hneg : (-(my : ℝ)) < 0 := neg_neg_of_pos hmypos
    linarith
  · -- sx = true, sy = false: -mx = my, contradiction with mx, my > 0
    simp only [hsx, hsy, Bool.false_eq_true, Bool.coe_true, ↓reduceIte, Int.cast_neg] at hmul_cancel
    -- hmul_cancel : -(↑(↑mx : ℤ)) = ↑(↑my : ℤ)
    have h1 : -((mx : ℤ) : ℝ) = ((my : ℤ) : ℝ) := hmul_cancel
    simp only [Int.cast_neg, Int.cast_natCast] at h1
    -- h1 : -(mx : ℝ) = (my : ℝ)
    have hmxpos : (0 : ℝ) < (mx : ℝ) := Nat.cast_pos.mpr hvalx
    have hmypos : (0 : ℝ) < (my : ℝ) := Nat.cast_pos.mpr hvaly
    have hneg : (-(mx : ℝ)) < 0 := neg_neg_of_pos hmxpos
    linarith
  · -- sx = true, sy = true: both negative, -mx = -my, so mx = my
    simp only [hsx, hsy, Bool.coe_true, ↓reduceIte, Int.cast_neg] at hmul_cancel
    have hmx_eq_my : (mx : ℝ) = (my : ℝ) := by
      -- hmul_cancel : -(↑(↑mx : ℤ)) = -(↑(↑my : ℤ))
      have h1 : -((mx : ℤ) : ℝ) = -((my : ℤ) : ℝ) := hmul_cancel
      simp only [Int.cast_neg, Int.cast_natCast, neg_inj] at h1
      exact h1
    have hmx_eq : mx = my := Nat.cast_injective hmx_eq_my
    simp only [hsx, hsy, hmx_eq]

-- Convert FullFloat.F754_finite to FlocqFloat for canonical representation
-- The signed mantissa is negated if the sign bit is true
def FF_to_FlocqFloat (f : FullFloat) : FloatSpec.Core.Defs.FlocqFloat 2 :=
  match f with
  | FullFloat.F754_finite s m e =>
    FloatSpec.Core.Defs.FlocqFloat.mk (if s then -(m : Int) else (m : Int)) e
  | _ => FloatSpec.Core.Defs.FlocqFloat.mk 0 0

-- Canonical representation for FullFloat: the underlying FlocqFloat is canonical
def canonical_FF {prec emax : Int} (f : FullFloat) : Prop :=
  FloatSpec.Core.Generic_fmt.canonical 2 (FLT_exp (3 - emax - prec) prec) (FF_to_FlocqFloat f)

-- Coq: B2R_Bsign_inj — injectivity using semantics plus sign
-- Note: This theorem requires canonical representation of the float values
-- to match the Coq behavior where B754_finite embeds a bounded proof.
-- Without canonical representation, different (m,e) pairs can have the same B2R value
-- (e.g., 4*2^1 = 2*2^2 = 8), so the theorem would be unprovable.
theorem B2R_Bsign_inj_compat {prec emax} (x y : Binary754 prec emax)
  (hx : is_finite_B (prec:=prec) (emax:=emax) x = true)
  (hy : is_finite_B (prec:=prec) (emax:=emax) y = true)
  (hvx : valid_FF x.val)
  (hvy : valid_FF y.val)
  (hcx : canonical_FF (prec:=prec) (emax:=emax) x.val)
  (hcy : canonical_FF (prec:=prec) (emax:=emax) y.val)
  (hR : B2R (prec:=prec) (emax:=emax) x = B2R (prec:=prec) (emax:=emax) y)
  (hs : Bsign (prec:=prec) (emax:=emax) x = Bsign (prec:=prec) (emax:=emax) y) :
  x = y := by
  -- Reduce to showing underlying FullFloat values are equal
  apply B2FF_inj_compat
  -- Both x.val and y.val must be F754_finite or F754_zero due to is_finite_B
  cases x with | mk xval xvalid =>
  cases y with | mk yval yvalid =>
  simp only [is_finite_B, is_finite_FF] at hx hy
  simp only [B2FF, B2R, Bsign, FF2R, sign_FF] at hR hs ⊢
  -- Case analysis on the FullFloat constructors
  cases xval with
  | F754_zero sx =>
    cases yval with
    | F754_zero sy =>
      -- Both zeros: must have same sign
      simp only [sign_FF] at hs
      rw [hs]
    | F754_infinity sy => simp at hy
    | F754_nan sy my => simp at hy
    | F754_finite sy my ey =>
      -- x is zero, y is finite
      -- B2R of zero is 0, B2R of finite is F2R which must be nonzero by validity
      simp only [FF2R] at hR
      simp only [F2R, FloatSpec.Core.Defs.F2R] at hR
      -- Validity says my > 0
      simp only [valid_FF] at hvy
      -- y is finite with my > 0, so B2R y ≠ 0
      -- But hR says B2R x = B2R y, and B2R x = 0 for zero
      -- This is a contradiction
      have h2pos : (0 : ℝ) < (2 : ℝ) ^ ey := by positivity
      have hmy_pos : (0 : ℝ) < (my : ℝ) := Nat.cast_pos.mpr hvy
      cases sy
      · -- sy = false: B2R y = my * 2^ey > 0
        simp only [Bool.false_eq_true, ↓reduceIte] at hR
        have hB2Ry_pos : (0 : ℝ) < (my : ℝ) * (2 : ℝ) ^ ey := mul_pos hmy_pos h2pos
        -- Normalize coercions: ↑(my : ℤ) * ↑2 ^ ey → (my : ℝ) * 2 ^ ey
        simp only [Int.cast_natCast, Int.cast_ofNat] at hR
        linarith
      · -- sy = true: B2R y = -my * 2^ey < 0
        simp only [↓reduceIte, Int.cast_neg, Int.cast_natCast, Int.cast_ofNat] at hR
        have hB2Ry_neg : (-(my : ℝ)) * (2 : ℝ) ^ ey < 0 :=
          mul_neg_of_neg_of_pos (neg_neg_of_pos hmy_pos) h2pos
        linarith
  | F754_infinity sx => simp at hx
  | F754_nan sx mx => simp at hx
  | F754_finite sx mx ex =>
    cases yval with
    | F754_zero sy =>
      -- x is finite, y is zero
      -- B2R of finite x is nonzero by validity, but B2R y = 0
      simp only [FF2R] at hR
      simp only [F2R, FloatSpec.Core.Defs.F2R] at hR
      -- Validity says mx > 0
      simp only [valid_FF] at hvx
      have h2pos : (0 : ℝ) < (2 : ℝ) ^ ex := by positivity
      have hmx_pos : (0 : ℝ) < (mx : ℝ) := Nat.cast_pos.mpr hvx
      cases sx
      · -- sx = false: B2R x = mx * 2^ex > 0
        simp only [Bool.false_eq_true, ↓reduceIte] at hR
        have hB2Rx_pos : (0 : ℝ) < (mx : ℝ) * (2 : ℝ) ^ ex := mul_pos hmx_pos h2pos
        -- Normalize coercions: ↑(mx : ℤ) * ↑2 ^ ex → (mx : ℝ) * 2 ^ ex
        simp only [Int.cast_natCast, Int.cast_ofNat] at hR
        linarith
      · -- sx = true: B2R x = -mx * 2^ex < 0
        simp only [↓reduceIte, Int.cast_neg, Int.cast_natCast, Int.cast_ofNat] at hR
        have hB2Rx_neg : (-(mx : ℝ)) * (2 : ℝ) ^ ex < 0 :=
          mul_neg_of_neg_of_pos (neg_neg_of_pos hmx_pos) h2pos
        linarith
    | F754_infinity sy => simp at hy
    | F754_nan sy my => simp at hy
    | F754_finite sy my ey =>
      -- Both finite: use B2R and sign equality plus canonical representation
      simp only [sign_FF] at hs
      simp only [FF2R, F2R, FloatSpec.Core.Defs.F2R] at hR
      -- Equal signs
      subst hs
      -- Now both have same sign sx
      -- Use canonical_unique to prove equality of underlying FlocqFloats
      simp only [canonical_FF, FF_to_FlocqFloat] at hcx hcy
      -- Convert hR to F2R equality for FlocqFloats
      -- hR: (if sx then -mx else mx) * 2^ex = (if sx then -my else my) * 2^ey
      have hF2R_eq : F2R (beta := 2) (FloatSpec.Core.Defs.FlocqFloat.mk (if sx then -(mx : Int) else (mx : Int)) ex)
                   = F2R (beta := 2) (FloatSpec.Core.Defs.FlocqFloat.mk (if sx then -(my : Int) else (my : Int)) ey) := by
        simp only [F2R, FloatSpec.Core.Defs.F2R]
        exact hR
      -- Apply canonical_unique
      have heq := FloatSpec.Core.Generic_fmt.canonical_unique 2 (by norm_num : (1 : Int) < 2)
        (FLT_exp (3 - emax - prec) prec)
        (FloatSpec.Core.Defs.FlocqFloat.mk (if sx then -(mx : Int) else (mx : Int)) ex)
        (FloatSpec.Core.Defs.FlocqFloat.mk (if sx then -(my : Int) else (my : Int)) ey)
        hcx hcy hF2R_eq
      -- Extract mantissa and exponent equality from FlocqFloat equality
      simp only [FloatSpec.Core.Defs.FlocqFloat.mk.injEq] at heq
      obtain ⟨hm_eq, he_eq⟩ := heq
      -- From mantissa equality, extract mx = my
      cases sx with
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte] at hm_eq
        have hmx_eq_my : mx = my := Int.ofNat_inj.mp hm_eq
        rw [hmx_eq_my, he_eq]
      | true =>
        simp only [↓reduceIte, neg_inj] at hm_eq
        have hmx_eq_my : mx = my := Int.ofNat_inj.mp hm_eq
        rw [hmx_eq_my, he_eq]

-- Coq counterparts `valid_binary_B2FF` and `FF2B_B2FF_valid` appear below
-- as compatibility-carrier statements.

/-- Validity on the Nat-payload compatibility carrier `FullFloat`. The Flocq
anchor for `valid_binary` is `Binary.valid_binary`, over the exact `full_float`
carrier. This copy adds explicit `0 < m` and `0 < payload` checks in place of
Rocq's `positive` type, and agrees with `Binary.valid_binary` on the image of
`full_float.toFullFloat`. It goes away with the `Binary754` carrier (batch 5A). -/
def valid_binary {prec emax : Int} (x : FullFloat) : Bool :=
  match x with
  | FullFloat.F754_finite _ m e =>
      decide (0 < m) && specFloat_bounded (prec:=prec) (emax:=emax) m e
  | FullFloat.F754_nan _ payload =>
      decide (0 < payload) &&
        FloatSpec.Core.Zaux.Zlt_bool
          (FloatSpec.Core.Digits.digits2_pos payload) prec
  | FullFloat.F754_zero _ => true
  | FullFloat.F754_infinity _ => true

theorem valid_binary_B2FF_compat {prec emax} (x : Binary754 prec emax)
    (hvalid : valid_binary (prec:=prec) (emax:=emax) x.val = true) :
    valid_binary (prec:=prec) (emax:=emax) (B2FF (prec:=prec) (emax:=emax) x) = true :=
  hvalid

/-- StandardFloat validity: finite values require a positive mantissa and
the canonical source bounds; exceptional constructors are valid. The positive
check accounts for Lean's Nat carrier versus Rocq's positive constructor. -/
def valid_binary_SF {prec emax : Int} (x : StandardFloat) : Bool :=
  match x with
  | .S754_finite _ m e => decide (0 < m) && specFloat_bounded (prec := prec) (emax := emax) m e
  | _ => true

-- StandardFloat-side payload validity induced by the fixed local `SF2FF`
-- encoding.  `StandardFloat` has no NaN payload field, so this is the exact
-- validity of the full-float image rather than a new source of payload data.
def valid_binary_SF_payload {prec emax : Int} (x : StandardFloat) : Bool :=
  valid_binary (prec:=prec) (emax:=emax) (SF2FF x)

-- This compatibility equality only unfolds an image predicate; it is not the
-- source theorem relating independently defined validity predicates.
theorem valid_binary_SF2FF_compat {prec emax} (x : StandardFloat)
    (hnotnan : is_nan_SF x = false) :
    valid_binary (prec:=prec) (emax:=emax) (SF2FF x) =
      valid_binary_SF_payload (prec:=prec) (emax:=emax) x := by
  rfl

-- Coq: FF2B_B2FF_valid. The compatibility carrier has no separate validity
-- argument, so the round trip is exactly `FF2B_B2FF_compat` above.

-- Coq: match_FF2B — pattern match through FF2B corresponds to match on source
theorem match_FF2B_compat {prec emax} {T : Type} (fz : Bool → T) (fi : Bool → T)
    (fn : Bool → Nat → T) (ff : Bool → Nat → Int → T)
    (x : FullFloat) :
    (match (FF2B (prec:=prec) (emax:=emax) x).val with
     | FullFloat.F754_zero sx => fz sx
     | FullFloat.F754_infinity sx => fi sx
     | FullFloat.F754_nan b p => fn b p
     | FullFloat.F754_finite sx mx ex => ff sx mx ex) =
    (match x with
     | FullFloat.F754_zero sx => fz sx
     | FullFloat.F754_infinity sx => fi sx
     | FullFloat.F754_nan b p => fn b p
     | FullFloat.F754_finite sx mx ex => ff sx mx ex) := by
  rfl

-- IEEE 754 rounding modes
inductive RoundingMode where
  | RNE : RoundingMode  -- Round to nearest, ties to even
  | RNA : RoundingMode  -- Round to nearest, ties away from zero
  | RTP : RoundingMode  -- Round toward positive infinity
  | RTN : RoundingMode  -- Round toward negative infinity
  | RTZ : RoundingMode  -- Round toward zero

-- Convert rounding mode to an integer rounding function. This is still a
-- lightweight Lean-side model of the IEEE modes, but it no longer erases all
-- modes to the same constant function.
noncomputable def rnd_of_mode (mode : RoundingMode) : ℝ → Int :=
  match mode with
  | RoundingMode.RTN => FloatSpec.Core.Raux.Zfloor
  | RoundingMode.RTP => FloatSpec.Core.Raux.Zceil
  | RoundingMode.RTZ => FloatSpec.Core.Raux.Ztrunc
  | RoundingMode.RNE =>
      FloatSpec.Core.Generic_fmt.Znearest (fun t : Int => !(decide (2 ∣ t)))
  | RoundingMode.RNA =>
      FloatSpec.Core.Generic_fmt.Znearest FloatSpec.Core.Generic_fmt.ZnearestA

instance valid_rnd_of_mode (mode : RoundingMode) :
    FloatSpec.Core.Generic_fmt.Valid_rnd (rnd_of_mode mode) := by
  cases mode
  · simpa [rnd_of_mode] using
      (FloatSpec.Core.Generic_fmt.valid_rnd_N (fun t : Int => !(decide (2 ∣ t))))
  · simpa [rnd_of_mode] using
      (FloatSpec.Core.Generic_fmt.valid_rnd_N FloatSpec.Core.Generic_fmt.ZnearestA)
  · exact FloatSpec.Core.Generic_fmt.valid_rnd_UP
  · exact FloatSpec.Core.Generic_fmt.valid_rnd_DN
  · exact FloatSpec.Core.Generic_fmt.valid_rnd_Ztrunc

-- Coq: `Binary.binary_overflow`, bridged from the SingleNaN operation.
-- Nearest modes overflow to infinity, toward-zero to the largest finite value,
-- and directed modes choose between those results from the sign.
def overflow_to_inf_FF (mode : RoundingMode) (s : Bool) : Bool :=
  match mode with
  | RoundingMode.RNE => true
  | RoundingMode.RNA => true
  | RoundingMode.RTZ => false
  | RoundingMode.RTP => !s
  | RoundingMode.RTN => s

/-- The positive mantissa of a raw overflow result, including the source's
fallback to one at nonpositive precision. -/
@[flocq_local "Extracts Z.to_pos (Zpower 2 prec - 1) from BinarySingleNaN.binary_overflow"]
def rawOverflowMantissa (prec : Int) : Nat :=
  if 0 < prec then (2 : Nat) ^ prec.toNat - 1 else 1

/-- At positive precision, the raw overflow mantissa is the largest significand. -/
@[simp] theorem rawOverflowMantissa_of_pos {prec : Int} [Prec_gt_0 prec] :
    rawOverflowMantissa prec = (2 : Nat) ^ prec.toNat - 1 := by
  simp [rawOverflowMantissa, (inferInstance : Prec_gt_0 prec).pos]

/-- The source positive carrier remains inhabited even outside format premises. -/
theorem rawOverflowMantissa_pos (prec : Int) : 0 < rawOverflowMantissa prec := by
  unfold rawOverflowMantissa
  split_ifs with hprec
  · have hnat : prec.toNat ≠ 0 := by omega
    exact Nat.sub_pos_of_lt (Nat.one_lt_two_pow hnat)
  · decide

def standard_binary_overflow (prec emax : Int) (mode : RoundingMode) (s : Bool) : StandardFloat :=
  if overflow_to_inf_FF mode s then
    StandardFloat.S754_infinity s
  else
    StandardFloat.S754_finite s (rawOverflowMantissa prec) (emax - prec)

def binary_overflow (prec emax : Int) (mode : RoundingMode) (s : Bool) : FullFloat :=
  SF2FF (standard_binary_overflow prec emax mode s)

-- Local strict-finiteness classifier for Binary754 (finite and nonzero semantics).
-- Coq uses a positive mantissa, so finite implies nonzero. This local
-- classifier keeps the shape and defers proof obligations elsewhere.
def is_finite_strict_Bin (x : Binary754 prec emax) : Bool :=
  match x.val with
  | FullFloat.F754_finite _ _ _ => true
  | _ => false

-- Coq: eq_binary_overflow_FF2SF
-- If FF2SF x corresponds to the single-NaN overflow value, then x is the
-- corresponding full-float overflow value.
theorem eq_binary_overflow_FF2SF_compat
  (x : FullFloat) (mode : RoundingMode) (s : Bool)
  (h : FF2SF x = standard_binary_overflow prec emax mode s) :
    x = binary_overflow prec emax mode s := by
  cases x <;> cases mode <;> cases s <;>
    simp [FF2SF, binary_overflow,
      standard_binary_overflow, overflow_to_inf_FF, SF2FF] at h ⊢ <;>
    assumption

-- Coq: fexp_emax — the exponent function at emax
-- In the Binary (full‑float) view, this expresses the relationship
-- between FLT_exp and emax.
theorem fexp_emax :
    (FLT_exp (3 - emax - prec) prec) emax = emax - prec := by
  -- Unfold FLT_exp: FLT_exp emin prec e = max (e - prec) emin
  -- Here: FLT_exp (3 - emax - prec) prec emax = max (emax - prec) (3 - emax - prec)
  unfold FLT_exp FloatSpec.Core.FLT.FLT_exp
  -- Show max (emax - prec) (3 - emax - prec) = emax - prec
  -- This requires (3 - emax - prec) ≤ (emax - prec), i.e., 3 - emax ≤ emax, i.e., 3 ≤ 2*emax
  -- From Prec_lt_emax we have emax ≥ 2, so 2*emax ≥ 4 > 3
  have hemax := (inferInstance : Prec_lt_emax prec emax).emax_ge_2
  have h : 3 - emax - prec ≤ emax - prec := by
    -- Simplify to 3 - emax ≤ emax, i.e., 3 ≤ 2*emax
    have h2emax : 4 ≤ 2 * emax := by linarith
    linarith
  simp only [max_eq_left h]

lemma round_to_generic_rnd_of_mode_zero (mode : RoundingMode)
    (fexp : Int → Int) [FloatSpec.Core.Generic_fmt.Valid_exp fexp] :
    FloatSpec.Core.Generic_fmt.round_to_generic 2 fexp (rnd_of_mode mode) 0 = 0 := by
  rw [FloatSpec.Core.Generic_fmt.round_to_generic_int_eq_roundR]
  have hrnd0 : rnd_of_mode mode (0 : ℝ) = (0 : Int) := by
    simpa using
      (FloatSpec.Core.Generic_fmt.Valid_rnd.Zrnd_IZR
        (rnd := rnd_of_mode mode) (0 : Int))
  simp [FloatSpec.Core.Generic_fmt.roundR, FloatSpec.Core.Generic_fmt.scaled_mantissa,
    hrnd0]

/-- Predicate capturing when a Binary754 float is in generic format.
    For finite floats, this requires the canonical exponent to be at most the float's exponent.
    This is the key constraint that Coq's `bounded mx ex = true` proof provides. -/
def Binary754_in_generic_format {prec emax : Int} (x : Binary754 prec emax) : Prop :=
  match x.val with
  | FullFloat.F754_zero _ => True
  | FullFloat.F754_infinity _ => True
  | FullFloat.F754_nan _ _ => True
  | FullFloat.F754_finite s m e =>
    let fnum : Int := if s then -(m : Int) else (m : Int)
    let f : FloatSpec.Core.Defs.FlocqFloat 2 := FloatSpec.Core.Defs.FlocqFloat.mk fnum e
    fnum ≠ 0 → FloatSpec.Core.Generic_fmt.cexp 2 (FLT_exp (3 - emax - prec) prec) (F2R f) ≤ e

-- Constant one (Coq: Bone)
def binary_one : Binary754 prec emax :=
  -- Canonical finite representation for 1 = 1 * 2^0
  FF2B (prec:=prec) (emax:=emax) (FullFloat.F754_finite false 1 0)

-- Coq `Bone_correct` — real value of constant one
theorem Bone_correct_compat :
    FF2R 2 (binary_one (prec:=prec) (emax:=emax)).val = 1 := by
  simp [binary_one, FF2B, FF2R, F2R, FloatSpec.Core.Defs.F2R]

-- Coq `is_finite_Bone` — constant one is finite
theorem is_finite_Bone_compat :
    is_finite_B (prec:=prec) (emax:=emax) (binary_one (prec:=prec) (emax:=emax)) = true := by
  simp [is_finite_B, binary_one, FF2B, is_finite_FF]

-- Coq `Bsign_Bone` — sign of constant one is false (positive)
theorem Bsign_Bone_compat :
    Bsign (prec:=prec) (emax:=emax) (binary_one (prec:=prec) (emax:=emax)) = false := by
  simp [Bsign, binary_one, FF2B, sign_FF]

-- Local Valid_exp instance for the constant exponent function used below
instance instValidExp_FIX0 :
  FloatSpec.Core.Generic_fmt.Valid_exp (fun _ => (0 : Int)) := by
  refine ⟨?_⟩
  intro k; constructor
  · intro hk; exact le_of_lt hk
  · intro _; constructor
    · exact le_rfl
    · intro _ _; rfl

-- The source contract `Btrunc_correct` (`IZR (Btrunc x) = round … Ztrunc (B2R x)`)
-- is stated directly as `Binary.Btrunc_correct` in `BinarySingleNaN.lean`.

-- Common IEEE 754 formats
def Binary16 := Binary754 11 15
def Binary32 := Binary754 24 127
def Binary64 := Binary754 53 1023
def Binary128 := Binary754 113 16383

-- Additional translated theorem surfaces.

-- Coq: canonical_canonical_mantissa
-- The predicate mirrors Coq's `canonical_mantissa`; the wrapper below proves
-- the canonicality statement exposed by this local encoding.

theorem canonical_mantissa_of_specFloat_bounded {prec emax : Int}
    {m : Nat} {e : Int}
    (h : specFloat_bounded (prec:=prec) (emax:=emax) m e = true) :
    canonical_mantissa (prec:=prec) (emax:=emax) m e = true := by
  have h' :
      canonical_mantissa (prec:=prec) (emax:=emax) m e = true ∧
        decide (e ≤ emax - prec) = true := by
    simpa [specFloat_bounded, Bool.and_eq_true] using h
  exact h'.1

theorem exponent_le_of_specFloat_bounded {prec emax : Int}
    {m : Nat} {e : Int}
    (h : specFloat_bounded (prec:=prec) (emax:=emax) m e = true) :
    e ≤ emax - prec := by
  have h' :
      canonical_mantissa (prec:=prec) (emax:=emax) m e = true ∧
        e ≤ emax - prec := by
    simpa [specFloat_bounded, Bool.and_eq_true, decide_eq_true_eq] using h
  exact h'.2

theorem range_bounded_of_specFloat_bounded {prec emax : Int}
    (m : Nat) (e : Int)
    (hm_pos : 0 < m)
    (h : specFloat_bounded (prec:=prec) (emax:=emax) m e = true) :
    bounded (prec:=prec) (emax:=emax) m e = true := by
  have hcanon :
      canonical_mantissa (prec:=prec) (emax:=emax) m e = true :=
    canonical_mantissa_of_specFloat_bounded (prec:=prec) (emax:=emax) h
  have hex_le : e ≤ emax - prec :=
    exponent_le_of_specFloat_bounded (prec:=prec) (emax:=emax) h
  have heq :
      e = FLT_exp (3 - emax - prec) prec
        (FloatSpec.Core.Digits.Zdigits 2 (m : Int) + e) :=
    eq_of_beq hcanon
  have heq_max :
      e = max (FloatSpec.Core.Digits.Zdigits 2 (m : Int) + e - prec)
        (3 - emax - prec) := by
    simpa [FLT_exp, FloatSpec.Core.FLT.FLT_exp] using heq
  have hmax_le_e :
      max (FloatSpec.Core.Digits.Zdigits 2 (m : Int) + e - prec)
        (3 - emax - prec) ≤ e := by
    rw [← heq_max]
  have hdigits_le_prec : FloatSpec.Core.Digits.Zdigits 2 (m : Int) ≤ prec := by
    have hleft :
        FloatSpec.Core.Digits.Zdigits 2 (m : Int) + e - prec ≤ e :=
      le_trans (le_max_left _ _) hmax_le_e
    omega
  have hemin_le : 3 - emax - prec ≤ e :=
    le_trans (le_max_right _ _) hmax_le_e
  have hm_int_ne : (m : Int) ≠ 0 := by
    exact_mod_cast (Nat.pos_iff_ne_zero.mp hm_pos)
  have hdigits_pos : 0 < FloatSpec.Core.Digits.Zdigits 2 (m : Int) := by
    exact FloatSpec.Core.Digits.Zdigits_gt_0 (beta := 2) (n := (m : Int)) hm_int_ne
      (by norm_num : (2 : Int) > 1)
  have hprec_nonneg : 0 ≤ prec := le_trans (le_of_lt hdigits_pos) hdigits_le_prec
  have hpow_bound :
      (m : Int) < (2 : Int) ^ prec.toNat := by
    have hpow := FloatSpec.Core.Digits.Zpower_gt_Zdigits
      (beta := 2) (h_beta := by norm_num) (e := prec) (x := (m : Int)) hdigits_le_prec
    have hprec_abs : prec.natAbs = prec.toNat := by
      have h1 : (prec.natAbs : Int) = prec := Int.natAbs_of_nonneg hprec_nonneg
      have h2 : (prec.toNat : Int) = prec := Int.toNat_of_nonneg hprec_nonneg
      omega
    simpa [hprec_abs] using hpow
  have hm_lt : m < (2 : Nat) ^ prec.toNat := by
    have hcast : (2 : Int) ^ prec.toNat = ↑((2 : Nat) ^ prec.toNat) := by
      simp
    rw [hcast] at hpow_bound
    exact Nat.cast_lt.mp hpow_bound
  simp [bounded, hm_lt, hemin_le, hex_le]

omit [Prec_gt_0 prec] [Prec_lt_emax prec emax] in
theorem canonical_canonical_mantissa_compat (sx : Bool) (mx : Nat) (ex : Int)
  (hmx_pos : 0 < mx)  -- IEEE 754: finite floats have positive mantissa; zero is F754_zero
  (h : canonical_mantissa (prec:=prec) (emax:=emax) mx ex = true) :
    FloatSpec.Core.Generic_fmt.canonical 2 (FLT_exp (3 - emax - prec) prec)
      (FloatSpec.Core.Defs.FlocqFloat.mk (if sx then -(mx : Int) else (mx : Int)) ex) := by
  -- Extract equality from boolean hypothesis
  have heq : ex = FLT_exp (3 - emax - prec) prec (FloatSpec.Core.Digits.Zdigits 2 mx + ex) :=
    eq_of_beq h
  -- Unfold canonical to show the goal is about F2R and mag
  unfold FloatSpec.Core.Generic_fmt.canonical
  simp only [FloatSpec.Core.Defs.FlocqFloat.Fexp]
  -- Goal: ex = FLT_exp ... (mag 2 (F2R f)) where f.Fnum = if sx then -mx else mx
  -- We need to show mag 2 (F2R f) = Zdigits 2 mx + ex
  -- F2R f = (signed mantissa) * 2^ex
  -- By mag_mult_bpow_eq: mag 2 (m * 2^ex) = mag 2 m + ex
  -- And mag 2 (±mx) = mag 2 mx = Zdigits 2 mx (for mx > 0)
  -- With hmx_pos : 0 < mx, we go directly to the non-zero case
  have hmx : mx ≠ 0 := Nat.pos_iff_ne_zero.mp hmx_pos
  have hmx_int_pos : (0 : Int) < (mx : Int) := Nat.cast_pos.mpr hmx_pos
  have hmx_real_ne : ((mx : Int) : ℝ) ≠ 0 := Int.cast_ne_zero.mpr (Int.ofNat_ne_zero.mpr hmx)
  -- Get mag 2 mx = Zdigits 2 mx
  have h2gt1 : (1 : Int) < 2 := by norm_num
  have hmag_eq := FloatSpec.Calc.Sqrt.mag_eq_Zdigits 2 (mx : Int) hmx_int_pos h2gt1
  -- Show signed mantissa ≠ 0
  have hsigned_ne : (if sx = true then -((mx : Int) : ℝ) else ((mx : Int) : ℝ)) ≠ 0 := by
    cases sx <;> simp [hmx_real_ne, hmx]
  -- Use mag_mult_bpow_eq: mag 2 (m * 2^ex) = mag 2 m + ex
  have hmag_mult := FloatSpec.Calc.Sqrt.mag_mult_bpow_eq 2
    (if sx = true then -((mx : Int) : ℝ) else ((mx : Int) : ℝ)) ex hsigned_ne h2gt1
  -- Rewrite F2R
  simp only [F2R, FloatSpec.Core.Defs.F2R, FloatSpec.Core.Defs.FlocqFloat.Fnum,
             FloatSpec.Core.Defs.FlocqFloat.Fexp]
  -- Normalize coercions: push Int cast inside the if expression to match hmag_mult pattern
  simp only [Int.cast_ite, Int.cast_neg, Int.cast_natCast]
  -- Establish mag of signed mantissa equals Zdigits
  have hmag_signed : FloatSpec.Core.Raux.mag 2
      (if sx = true then -((mx : Int) : ℝ) else ((mx : Int) : ℝ)) =
      FloatSpec.Core.Digits.Zdigits 2 (mx : Int) := by
    cases sx
    · -- sx = false: straightforward
      simp only [Bool.false_eq_true, ↓reduceIte]
      exact hmag_eq
    · -- sx = true: use mag(-x) = mag(x)
      simp only [↓reduceIte]
      -- mag 2 (-mx) = mag 2 mx
      unfold FloatSpec.Core.Raux.mag
      -- Explicitly prove -↑↑mx ≠ 0 so simp can eliminate the if-condition
      have hmx_neg_ne : -((mx : Int) : ℝ) ≠ 0 := neg_ne_zero.mpr hmx_real_ne
      simp only [hmx_neg_ne, ↓reduceIte, abs_neg]
      -- Now both sides simplify to the same thing
      unfold FloatSpec.Core.Raux.mag at hmag_eq
      simp only [hmx_real_ne, ↓reduceIte] at hmag_eq
      exact hmag_eq
  -- Now build the full magnitude equation
  -- Note: hmag_mult uses ↑2 ^ ex (Int 2 cast to ℝ), so we state hmag_full the same way
  have hmag_full : FloatSpec.Core.Raux.mag 2
      ((if sx = true then -((mx : Int) : ℝ) else ((mx : Int) : ℝ)) * ((2 : Int) : ℝ) ^ ex) =
      FloatSpec.Core.Digits.Zdigits 2 (mx : Int) + ex := by
    rw [hmag_mult, hmag_signed]
  -- The goal is: ex = FLT_exp ... (mag 2 ((if sx then -↑mx else ↑mx) * 2^ex))
  -- We need to show this equals heq: ex = FLT_exp ... (Zdigits 2 mx + ex)
  -- First convert the goal to use our magnitude equation
  calc ex = FLT_exp (3 - emax - prec) prec (FloatSpec.Core.Digits.Zdigits 2 (mx : Int) + ex) := heq
    _ = FLT_exp (3 - emax - prec) prec (FloatSpec.Core.Raux.mag 2
          ((if sx = true then -((mx : Int) : ℝ) else ((mx : Int) : ℝ)) * ((2 : Int) : ℝ) ^ ex)) := by
      rw [hmag_full]

-- Coq: generic_format_B2R
-- Generic-format property of the real semantics of a binary float.
theorem generic_format_B2R_compat {prec emax : Int} [Prec_gt_0 prec]
  (x : Binary754 prec emax)
  (hformat : Binary754_in_generic_format (prec:=prec) (emax:=emax) x) :
    FloatSpec.Core.Generic_fmt.generic_format 2 (FLT_exp (3 - emax - prec) prec)
      (B2R (prec:=prec) (emax:=emax) x) := by
  -- Case split on the FullFloat value
  cases x with | mk xval xvalid =>
  simp only [B2R, FF2R]
  cases xval with
  | F754_zero s =>
    -- B2R of zero is 0, use generic_format_0
    exact FloatSpec.Core.Generic_fmt.generic_format_0 2 (FLT_exp (3 - emax - prec) prec)
  | F754_infinity s =>
    -- B2R of infinity is 0, use generic_format_0
    exact FloatSpec.Core.Generic_fmt.generic_format_0 2 (FLT_exp (3 - emax - prec) prec)
  | F754_nan s m =>
    -- B2R of NaN is 0, use generic_format_0
    exact FloatSpec.Core.Generic_fmt.generic_format_0 2 (FLT_exp (3 - emax - prec) prec)
  | F754_finite s m e =>
    -- For finite floats, F2R of a FlocqFloat is in generic format
    -- This requires showing the value is representable in FLT format
    simp only [FloatSpec.Core.Defs.FlocqFloat.mk.injEq]
    by_cases hm : m = 0
    · simp only [hm]
      -- F2R with Fnum = 0 equals 0 (since 0 * β^e = 0)
      have h_f2r_zero : F2R (⟨if s = true then -↑(0 : Nat) else ↑(0 : Nat), e⟩ : FloatSpec.Core.Defs.FlocqFloat 2) = 0 := by
        simp only [F2R, FloatSpec.Core.Defs.F2R]
        cases s <;> simp
      rw [h_f2r_zero]
      exact FloatSpec.Core.Generic_fmt.generic_format_0 2 (FLT_exp (3 - emax - prec) prec)
    · -- Non-zero mantissa case: use generic_format_F2R
      have h_format := FloatSpec.Core.Generic_fmt.generic_format_F2R 2 (FLT_exp (3 - emax - prec) prec)
        (if s then -(m : Int) else (m : Int)) e
      apply h_format
      intro hm_ne
      simp only [Binary754_in_generic_format] at hformat
      exact hformat hm_ne

-- Coq: FLT_format_B2R
-- FLT-format property of the real semantics of a binary float.
theorem FLT_format_B2R_compat
  {prec emax : Int} [Prec_gt_0 prec] [Prec_lt_emax prec emax]
  (x : Binary754 prec emax)
  (hformat : Binary754_in_generic_format (prec:=prec) (emax:=emax) x) :
    FloatSpec.Core.FLT.FLT_format (prec:=prec) (emin := 3 - emax - prec) 2
      (B2R (prec:=prec) (emax:=emax) x) := by
  have hgen : FloatSpec.Core.Generic_fmt.generic_format 2
      (FloatSpec.Core.FLT.FLT_exp prec (3 - emax - prec))
      (B2R (prec := prec) (emax := emax) x) :=
    generic_format_B2R_compat x hformat
  have hflt := FloatSpec.Core.FLT.FLT_format_generic
    (prec := prec) (emin := 3 - emax - prec) 2
    (B2R (prec := prec) (emax := emax) x)
  exact hflt hgen

-- Coq: emin_lt_emax — the minimal exponent is strictly less than emax (Binary side)
theorem emin_lt_emax_B :
    (3 - emax - prec) < emax := by
  -- From Prec_lt_emax we have prec < emax and emax ≥ 2
  have hprec := (inferInstance : Prec_lt_emax prec emax).prec_lt_emax
  have hemax := (inferInstance : Prec_lt_emax prec emax).emax_ge_2
  -- Goal: 3 - emax - prec < emax
  -- Rearranging: 3 - prec < 2 * emax
  -- Since prec > 0 (from Prec_gt_0), we have 3 - prec < 3
  -- Since emax ≥ 2, we have 2 * emax ≥ 4 > 3 > 3 - prec
  have hprec_pos := (inferInstance : Prec_gt_0 prec).pos
  linarith

-- Coq: bounded_le_emax_minus_prec
-- For mantissa/exponent pairs that are `bounded`, the real value is
-- bounded above by bpow emax minus bpow (emax - prec).

theorem bounded_le_emax_minus_prec {prec emax : Int} [Prec_gt_0 prec]
  (mx : Nat) (ex : Int)
  (h : bounded (prec:=prec) (emax:=emax) mx ex = true) :
    F2R (FloatSpec.Core.Defs.FlocqFloat.mk (mx : Int) ex : FloatSpec.Core.Defs.FlocqFloat 2)
      ≤ FloatSpec.Core.Raux.bpow 2 emax
        - FloatSpec.Core.Raux.bpow 2 (emax - prec) := by
  -- Extract constraints from bounded
  simp only [bounded, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hmx_lt, hex_ge⟩, hex_le⟩ := h
  -- Unfold F2R and bpow
  simp only [F2R, FloatSpec.Core.Defs.F2R, FloatSpec.Core.Raux.bpow,
             FloatSpec.Core.Defs.FlocqFloat.Fnum, FloatSpec.Core.Defs.FlocqFloat.Fexp]
  -- Goal: (mx : ℝ) * 2^ex ≤ 2^emax - 2^(emax - prec)
  have h2pos : (0 : ℝ) < 2 := by norm_num
  have h2ne : (2 : ℝ) ≠ 0 := by norm_num
  have h2_eq : ((2 : ℤ) : ℝ) = (2 : ℝ) := by norm_num
  -- Get prec > 0 from instance
  have hprec_pos := (inferInstance : Prec_gt_0 prec).pos
  have hprec_nonneg : 0 ≤ prec := le_of_lt hprec_pos
  -- First handle the mx = 0 case separately
  by_cases hmx_zero : mx = 0
  · -- Case: mx = 0, so LHS = 0 * 2^ex = 0
    simp only [hmx_zero, Nat.cast_zero, Int.cast_zero, zero_mul, h2_eq]
    -- Need to show 0 ≤ 2^emax - 2^(emax - prec)
    -- Since prec > 0, we have emax - prec < emax, so 2^(emax - prec) < 2^emax
    have hexp_le : emax - prec ≤ emax := by omega
    have hpow_le : (2 : ℝ) ^ (emax - prec) ≤ (2 : ℝ) ^ emax :=
      zpow_le_zpow_right₀ (by norm_num : 1 ≤ (2 : ℝ)) hexp_le
    exact sub_nonneg.mpr hpow_le
  · -- Case: mx ≠ 0, so mx ≥ 1
    -- From mx < 2^prec.toNat and mx ≥ 1, we have 2^prec.toNat > 1, so prec.toNat ≥ 1
    -- This means prec ≥ 1 > 0
    have hmx_pos : 0 < mx := Nat.pos_of_ne_zero hmx_zero
    have hmx_ge_one : 1 ≤ mx := hmx_pos
    have hpow_gt_one : 1 < (2 : Nat) ^ prec.toNat := Nat.lt_of_le_of_lt hmx_ge_one hmx_lt
    have hprec_toNat_pos : 0 < prec.toNat := by
      by_contra h_contra
      push Not at h_contra
      interval_cases prec.toNat
      simp only [pow_zero, lt_self_iff_false] at hpow_gt_one
    have hprec_nonneg : 0 ≤ prec := by
      by_contra h_contra
      push Not at h_contra
      have : prec.toNat = 0 := Int.toNat_eq_zero.mpr (le_of_lt h_contra)
      omega
    have hprec_pos : 0 < prec := by
      cases' (lt_or_eq_of_le hprec_nonneg) with hlt heq
      · exact hlt
      · -- prec = 0 case: prec.toNat = 0, so 2^prec.toNat = 1, contradicting hpow_gt_one
        exfalso
        rw [← heq] at hprec_toNat_pos
        simp only [Int.toNat_zero, lt_self_iff_false] at hprec_toNat_pos
    -- Strategy: mx * 2^ex ≤ (2^prec - 1) * 2^(emax - prec) = 2^emax - 2^(emax - prec)
    -- First, rewrite RHS using algebra: 2^emax - 2^(emax-prec) = (2^prec - 1) * 2^(emax-prec)
    have hrhs : (2 : ℝ) ^ emax - (2 : ℝ) ^ (emax - prec) = ((2 : ℝ) ^ prec - 1) * (2 : ℝ) ^ (emax - prec) := by
      calc (2 : ℝ) ^ emax - (2 : ℝ) ^ (emax - prec)
          = (2 : ℝ) ^ (prec + (emax - prec)) - (2 : ℝ) ^ (emax - prec) := by ring_nf
        _ = (2 : ℝ) ^ prec * (2 : ℝ) ^ (emax - prec) - (2 : ℝ) ^ (emax - prec) := by
            rw [zpow_add₀ h2ne]
        _ = ((2 : ℝ) ^ prec - 1) * (2 : ℝ) ^ (emax - prec) := by ring
    simp only [h2_eq, hrhs]
    -- Now prove: (mx : ℝ) * 2^ex ≤ (2^prec - 1) * 2^(emax - prec)
    -- From hmx_lt: mx < 2^prec.toNat, so mx ≤ 2^prec.toNat - 1 = 2^prec - 1 (as Nat)
    -- From hex_le: ex ≤ emax - prec, so 2^ex ≤ 2^(emax - prec)
    have hmx_le : (mx : ℝ) ≤ (2 : ℝ) ^ prec - 1 := by
      -- mx < 2^prec.toNat means mx ≤ 2^prec.toNat - 1
      have hmx_nat_le : mx ≤ (2 : Nat) ^ prec.toNat - 1 := Nat.le_sub_one_of_lt hmx_lt
      -- Convert to real: (mx : ℝ) ≤ 2^prec.toNat - 1
      have h1 : (mx : ℝ) ≤ ((2 : Nat) ^ prec.toNat - 1 : Nat) := Nat.cast_le.mpr hmx_nat_le
      -- First need 2^prec.toNat ≥ 1 for the subtraction
      have hpow_ge_1 : 1 ≤ (2 : Nat) ^ prec.toNat := Nat.one_le_two_pow
      -- Cast Nat subtraction to Real
      have h3 : (((2 : Nat) ^ prec.toNat - 1 : Nat) : ℝ) = ((2 : Nat) ^ prec.toNat : ℝ) - 1 := by
        rw [Nat.cast_sub hpow_ge_1]
        simp
      rw [h3] at h1
      -- Now convert (2 : Nat)^prec.toNat to (2 : ℝ)^prec using prec ≥ 0
      have h4 : ((2 : Nat) ^ prec.toNat : ℝ) = (2 : ℝ) ^ prec := by
        rw [← zpow_natCast]
        congr 1
        exact Int.toNat_of_nonneg hprec_nonneg
      rw [h4] at h1
      exact h1
    have hex_pow_le : (2 : ℝ) ^ ex ≤ (2 : ℝ) ^ (emax - prec) := by
      exact zpow_le_zpow_right₀ (by norm_num : 1 ≤ (2 : ℝ)) hex_le
    -- Combine: mx * 2^ex ≤ (2^prec - 1) * 2^(emax - prec)
    have hpow_pos : (0 : ℝ) < (2 : ℝ) ^ (emax - prec) := zpow_pos h2pos (emax - prec)
    have hpow_ex_pos : (0 : ℝ) < (2 : ℝ) ^ ex := zpow_pos h2pos ex
    have hcoeff_nonneg : (0 : ℝ) ≤ (2 : ℝ) ^ prec - 1 := by
      have hone_le : (1 : ℝ) ≤ (2 : ℝ) ^ prec := by
        have hprec_nonneg' : (0 : ℤ) ≤ prec := hprec_nonneg
        calc (1 : ℝ) = (2 : ℝ) ^ (0 : ℤ) := by simp
          _ ≤ (2 : ℝ) ^ prec := zpow_le_zpow_right₀ (by norm_num : 1 ≤ (2 : ℝ)) hprec_nonneg'
      linarith
    -- Use monotonicity: a * b ≤ c * d when 0 ≤ a ≤ c and 0 ≤ b ≤ d
    calc (mx : ℝ) * (2 : ℝ) ^ ex
        ≤ ((2 : ℝ) ^ prec - 1) * (2 : ℝ) ^ ex := by
            apply mul_le_mul_of_nonneg_right hmx_le (le_of_lt hpow_ex_pos)
      _ ≤ ((2 : ℝ) ^ prec - 1) * (2 : ℝ) ^ (emax - prec) := by
            apply mul_le_mul_of_nonneg_left hex_pow_le hcoeff_nonneg

-- Coq: bounded_lt_emax — bounded values lie strictly below bpow emax
theorem bounded_lt_emax {prec emax : Int}
  (mx : Nat) (ex : Int)
  (h : bounded (prec:=prec) (emax:=emax) mx ex = true) :
    F2R (FloatSpec.Core.Defs.FlocqFloat.mk (mx : Int) ex : FloatSpec.Core.Defs.FlocqFloat 2)
      < FloatSpec.Core.Raux.bpow 2 emax := by
  -- Extract constraints from bounded
  simp only [bounded, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hmx_lt, hex_ge⟩, hex_le⟩ := h
  -- Unfold F2R and bpow
  simp only [F2R, FloatSpec.Core.Defs.F2R, FloatSpec.Core.Raux.bpow,
             FloatSpec.Core.Defs.FlocqFloat.Fnum, FloatSpec.Core.Defs.FlocqFloat.Fexp]
  -- Goal: (mx : ℝ) * 2^ex < 2^emax
  have h2pos : (0 : ℝ) < 2 := by norm_num
  have h2ne : (2 : ℝ) ≠ 0 := by norm_num
  have h2_eq : ((2 : ℤ) : ℝ) = (2 : ℝ) := by norm_num
  -- Case: mx = 0, so LHS = 0 * 2^ex = 0 < 2^emax
  by_cases hmx_zero : mx = 0
  · simp only [hmx_zero, Nat.cast_zero, Int.cast_zero, zero_mul, h2_eq]
    exact zpow_pos h2pos emax
  · -- Case: mx > 0
    have hmx_pos : 0 < mx := Nat.pos_of_ne_zero hmx_zero
    have hmx_ge_one : 1 ≤ mx := hmx_pos
    -- From hmx_lt: mx < 2^prec.toNat, so mx ≤ 2^prec.toNat - 1 < 2^prec.toNat ≤ 2^prec
    -- Need to show: (mx : ℝ) * 2^ex < 2^emax
    -- Strategy: mx * 2^ex < 2^prec * 2^ex ≤ 2^prec * 2^(emax - prec) = 2^emax
    -- First establish prec.toNat ≥ 1 from the fact that mx ≥ 1 and mx < 2^prec.toNat
    have hpow_gt_one : 1 < (2 : Nat) ^ prec.toNat := Nat.lt_of_le_of_lt hmx_ge_one hmx_lt
    have hprec_toNat_pos : 0 < prec.toNat := by
      by_contra h_contra
      push Not at h_contra
      interval_cases prec.toNat
      simp only [pow_zero, lt_self_iff_false] at hpow_gt_one
    have hprec_nonneg : 0 ≤ prec := by
      by_contra h_contra
      push Not at h_contra
      have : prec.toNat = 0 := Int.toNat_eq_zero.mpr (le_of_lt h_contra)
      omega
    -- Key: mx < 2^prec.toNat = 2^prec (since prec ≥ 0)
    have hmx_lt_pow_prec : (mx : ℝ) < (2 : ℝ) ^ prec := by
      have h1 : (mx : ℝ) < ((2 : Nat) ^ prec.toNat : Nat) := Nat.cast_lt.mpr hmx_lt
      -- Bridge the coercion: ↑((2 : Nat) ^ prec.toNat) = (2 : ℝ) ^ prec
      have h2 : (((2 : Nat) ^ prec.toNat : Nat) : ℝ) = (2 : ℝ) ^ prec := by
        -- First use Nat.cast_pow: ↑(a ^ n) = ↑a ^ n
        rw [Nat.cast_pow]
        -- Now have (2 : ℝ) ^ prec.toNat = (2 : ℝ) ^ prec
        -- Use zpow_natCast and the fact that prec.toNat = prec for prec ≥ 0
        rw [← zpow_natCast]
        congr 1
        exact Int.toNat_of_nonneg hprec_nonneg
      calc (mx : ℝ) < ((2 : Nat) ^ prec.toNat : Nat) := h1
        _ = (2 : ℝ) ^ prec := h2
    -- ex ≤ emax - prec, so 2^ex ≤ 2^(emax - prec)
    have hex_pow_le : (2 : ℝ) ^ ex ≤ (2 : ℝ) ^ (emax - prec) :=
      zpow_le_zpow_right₀ (by norm_num : 1 ≤ (2 : ℝ)) hex_le
    -- Positivity facts
    have hpow_ex_pos : (0 : ℝ) < (2 : ℝ) ^ ex := zpow_pos h2pos ex
    have hpow_emax_prec_pos : (0 : ℝ) < (2 : ℝ) ^ (emax - prec) := zpow_pos h2pos (emax - prec)
    have hmx_real_pos : (0 : ℝ) < (mx : ℝ) := Nat.cast_pos.mpr hmx_pos
    have hpow_prec_pos : (0 : ℝ) < (2 : ℝ) ^ prec := zpow_pos h2pos prec
    -- 2^prec * 2^(emax - prec) = 2^emax
    have hpow_split : (2 : ℝ) ^ prec * (2 : ℝ) ^ (emax - prec) = (2 : ℝ) ^ emax := by
      rw [← zpow_add₀ h2ne]
      congr 1
      ring
    -- Combine: mx * 2^ex < 2^prec * 2^(emax - prec) = 2^emax
    calc (mx : ℝ) * (2 : ℝ) ^ ex
        < (2 : ℝ) ^ prec * (2 : ℝ) ^ ex := by
            apply mul_lt_mul_of_pos_right hmx_lt_pow_prec hpow_ex_pos
      _ ≤ (2 : ℝ) ^ prec * (2 : ℝ) ^ (emax - prec) := by
            apply mul_le_mul_of_nonneg_left hex_pow_le (le_of_lt hpow_prec_pos)
      _ = (2 : ℝ) ^ emax := hpow_split

-- Coq: bounded_ge_emin — bounded values lie above bpow emin
theorem bounded_ge_emin {prec emax : Int}
  (mx : Nat) (ex : Int)
  (h : bounded (prec:=prec) (emax:=emax) mx ex = true)
  (hmx_pos : 0 < mx) :
    FloatSpec.Core.Raux.bpow 2 (3 - emax - prec)
      ≤ F2R (FloatSpec.Core.Defs.FlocqFloat.mk (mx : Int) ex : FloatSpec.Core.Defs.FlocqFloat 2) := by
  -- Extract constraints from bounded
  simp only [bounded, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hmx_lt, hex_ge⟩, hex_le⟩ := h
  -- Unfold F2R and bpow
  simp only [F2R, FloatSpec.Core.Defs.F2R, FloatSpec.Core.Raux.bpow,
             FloatSpec.Core.Defs.FlocqFloat.Fnum, FloatSpec.Core.Defs.FlocqFloat.Fexp]
  -- Goal: 2^(3 - emax - prec) ≤ (mx : ℝ) * 2^ex
  have h2pos : (0 : ℝ) < 2 := by norm_num
  have h2ne : (2 : ℝ) ≠ 0 := by norm_num
  have h2_eq : ((2 : ℤ) : ℝ) = (2 : ℝ) := by norm_num
  -- mx ≥ 1 since mx > 0
  have hmx_ge_one : 1 ≤ mx := hmx_pos
  have hmx_real_ge_one : (1 : ℝ) ≤ (mx : ℝ) := Nat.one_le_cast.mpr hmx_ge_one
  -- 2^ex ≥ 2^(3 - emax - prec) since ex ≥ (3 - emax - prec)
  have hex_pow_ge : (2 : ℝ) ^ (3 - emax - prec) ≤ (2 : ℝ) ^ ex :=
    zpow_le_zpow_right₀ (by norm_num : 1 ≤ (2 : ℝ)) hex_ge
  -- Positivity facts
  have hpow_emin_pos : (0 : ℝ) < (2 : ℝ) ^ (3 - emax - prec) := zpow_pos h2pos (3 - emax - prec)
  have hpow_ex_pos : (0 : ℝ) < (2 : ℝ) ^ ex := zpow_pos h2pos ex
  -- Goal: 2^(3 - emax - prec) ≤ mx * 2^ex
  -- Since mx ≥ 1 and 2^ex ≥ 2^(3 - emax - prec), we have:
  -- 2^(3 - emax - prec) ≤ 2^ex ≤ 1 * 2^ex ≤ mx * 2^ex
  calc (2 : ℝ) ^ (3 - emax - prec)
      ≤ (2 : ℝ) ^ ex := hex_pow_ge
    _ = 1 * (2 : ℝ) ^ ex := by ring
    _ ≤ (mx : ℝ) * (2 : ℝ) ^ ex := by
        apply mul_le_mul_of_nonneg_right hmx_real_ge_one (le_of_lt hpow_ex_pos)

-- Predicate: Binary754 value is properly bounded (finite values satisfy `bounded`)
-- In Coq, this is enforced by the type itself; here we add it as a hypothesis.
def Binary754_bounded {prec emax : Int} (x : Binary754 prec emax) : Prop :=
  match x.val with
  | FullFloat.F754_finite _ m e => bounded (prec:=prec) (emax:=emax) m e = true
  | _ => True

-- Coq: abs_B2R_le_emax_minus_prec
-- The absolute value of the real semantics of any binary float is bounded
-- above by bpow emax minus bpow (emax - prec).
-- NOTE: Added [Prec_gt_0 prec] and Binary754_bounded hypothesis since our Binary754
-- structure doesn't enforce bounded constraints as the Coq version does.
theorem abs_B2R_le_emax_minus_prec_compat {prec emax : Int} [Prec_gt_0 prec]
  (x : Binary754 prec emax)
  (hbounded : Binary754_bounded (prec:=prec) (emax:=emax) x) :
    |B2R (prec:=prec) (emax:=emax) x|
      ≤ FloatSpec.Core.Raux.bpow 2 emax
          - FloatSpec.Core.Raux.bpow 2 (emax - prec) := by
  -- Case analysis on the structure of x
  cases hx : x.val with
  | F754_zero s =>
    -- For zero: B2R x = 0, so |B2R x| = 0 ≤ bpow emax - bpow (emax - prec)
    simp only [B2R, FF2R, hx]
    rw [abs_zero]
    -- Need: 0 ≤ bpow 2 emax - bpow 2 (emax - prec)
    simp only [FloatSpec.Core.Raux.bpow]
    have hprec_pos := (inferInstance : Prec_gt_0 prec).pos
    have h2_eq : ((2 : ℤ) : ℝ) = (2 : ℝ) := by norm_num
    simp only [h2_eq]
    have hexp_le : emax - prec ≤ emax := by omega
    have hpow_le : (2 : ℝ) ^ (emax - prec) ≤ (2 : ℝ) ^ emax :=
      zpow_le_zpow_right₀ (by norm_num : 1 ≤ (2 : ℝ)) hexp_le
    exact sub_nonneg.mpr hpow_le
  | F754_infinity s =>
    -- For infinity: B2R x = 0, so |B2R x| = 0
    simp only [B2R, FF2R, hx]
    rw [abs_zero]
    simp only [FloatSpec.Core.Raux.bpow]
    have hprec_pos := (inferInstance : Prec_gt_0 prec).pos
    have h2_eq : ((2 : ℤ) : ℝ) = (2 : ℝ) := by norm_num
    simp only [h2_eq]
    have hexp_le : emax - prec ≤ emax := by omega
    have hpow_le : (2 : ℝ) ^ (emax - prec) ≤ (2 : ℝ) ^ emax :=
      zpow_le_zpow_right₀ (by norm_num : 1 ≤ (2 : ℝ)) hexp_le
    exact sub_nonneg.mpr hpow_le
  | F754_nan s payload =>
    -- For NaN: B2R x = 0, so |B2R x| = 0
    simp only [B2R, FF2R, hx]
    rw [abs_zero]
    simp only [FloatSpec.Core.Raux.bpow]
    have hprec_pos := (inferInstance : Prec_gt_0 prec).pos
    have h2_eq : ((2 : ℤ) : ℝ) = (2 : ℝ) := by norm_num
    simp only [h2_eq]
    have hexp_le : emax - prec ≤ emax := by omega
    have hpow_le : (2 : ℝ) ^ (emax - prec) ≤ (2 : ℝ) ^ emax :=
      zpow_le_zpow_right₀ (by norm_num : 1 ≤ (2 : ℝ)) hexp_le
    exact sub_nonneg.mpr hpow_le
  | F754_finite s m e =>
    -- For finite: use bounded constraint
    simp only [Binary754_bounded, hx] at hbounded
    -- hbounded : bounded prec emax m e = true
    simp only [B2R, FF2R, hx]
    -- Goal: |F2R (if s then -m else m, e)| ≤ bpow emax - bpow (emax - prec)
    simp only [FloatSpec.Core.Raux.bpow]
    -- Unfold F2R
    simp only [F2R, FloatSpec.Core.Defs.F2R, FloatSpec.Core.Defs.FlocqFloat.Fnum,
               FloatSpec.Core.Defs.FlocqFloat.Fexp]
    -- Goal: |((if s then -(m:Int) else m) : ℝ) * (2 : ℤ)^e| ≤ (2:ℤ)^emax - (2:ℤ)^(emax-prec)
    -- Simplify the casts: ↑(2:ℤ)^e = (2:ℝ)^e (for zpow)
    have h2_eq : ((2 : ℤ) : ℝ) = (2 : ℝ) := by norm_num
    have h2pos : (0 : ℝ) < 2 := by norm_num
    -- Note: (↑2 : ℝ) ^ e is definitionally equal to (2 : ℝ) ^ e for zpow
    -- But we need to be careful with the cast of the entire zpow expression
    -- Let's first handle the sign case and then use the bounded_le_emax_minus_prec
    by_cases hs : s
    · -- s = true: value is -(m:Int)
      simp only [hs, ↓reduceIte]
      -- Goal: |↑(-↑m) * ↑2 ^ e| ≤ ...
      simp only [Int.cast_neg, Int.cast_natCast]
      -- Goal: |-(m : ℝ) * ↑2 ^ e| ≤ 2^emax - 2^(emax-prec)
      rw [neg_mul, abs_neg]
      -- Goal: |(m : ℝ) * ↑2 ^ e| ≤ 2^emax - 2^(emax-prec)
      rw [abs_mul]
      -- |(m : ℝ)| = (m : ℝ) since m : ℕ
      rw [abs_of_nonneg (Nat.cast_nonneg m)]
      -- |↑2 ^ e| = ↑2 ^ e since it's positive
      have hpow_nonneg : (0 : ℝ) ≤ ((2 : ℤ) : ℝ) ^ e := by
        apply zpow_nonneg; norm_num
      rw [abs_of_nonneg hpow_nonneg]
      -- Now rewrite ↑2 to 2
      simp only [h2_eq]
      -- Goal: (m : ℝ) * 2^e ≤ 2^emax - 2^(emax-prec)
      -- Use bounded_le_emax_minus_prec
      have hbound := bounded_le_emax_minus_prec (prec:=prec) (emax:=emax) m e hbounded
      simp only [F2R, FloatSpec.Core.Defs.F2R, FloatSpec.Core.Defs.FlocqFloat.Fnum,
                 FloatSpec.Core.Defs.FlocqFloat.Fexp, FloatSpec.Core.Raux.bpow, h2_eq] at hbound
      exact hbound
    · -- s = false: value is m
      have hs' : s = false := Bool.eq_false_iff.mpr hs
      simp only [hs', ↓reduceIte, Int.cast_natCast]
      -- Goal: |(m : ℝ) * ↑2 ^ e| ≤ 2^emax - 2^(emax-prec)
      rw [abs_mul]
      rw [abs_of_nonneg (Nat.cast_nonneg m)]
      have hpow_nonneg : (0 : ℝ) ≤ ((2 : ℤ) : ℝ) ^ e := by
        apply zpow_nonneg; norm_num
      rw [abs_of_nonneg hpow_nonneg]
      simp only [h2_eq]
      have hbound := bounded_le_emax_minus_prec (prec:=prec) (emax:=emax) m e hbounded
      simp only [F2R, FloatSpec.Core.Defs.F2R, FloatSpec.Core.Defs.FlocqFloat.Fnum,
                 FloatSpec.Core.Defs.FlocqFloat.Fexp, FloatSpec.Core.Raux.bpow, h2_eq] at hbound
      exact hbound

-- Coq: abs_B2R_lt_emax — absolute semantics strictly below bpow emax
theorem abs_B2R_lt_emax_compat {prec emax : Int} [Prec_gt_0 prec]
  (x : Binary754 prec emax)
  (hbounded : Binary754_bounded (prec:=prec) (emax:=emax) x) :
    |B2R (prec:=prec) (emax:=emax) x|
      < FloatSpec.Core.Raux.bpow 2 emax := by
  -- Use abs_B2R_le_emax_minus_prec to get |B2R x| ≤ 2^emax - 2^(emax-prec)
  have hle' := abs_B2R_le_emax_minus_prec_compat (prec:=prec) (emax:=emax) x hbounded
  -- Now show 2^emax - 2^(emax-prec) < 2^emax
  -- Since prec > 0, we have 2^(emax-prec) > 0, so 2^emax - 2^(emax-prec) < 2^emax
  have h2pos : (0 : ℝ) < 2 := by norm_num
  have h2_eq : ((2 : ℤ) : ℝ) = (2 : ℝ) := by norm_num
  simp only [FloatSpec.Core.Raux.bpow] at hle' ⊢
  simp only [h2_eq] at hle' ⊢
  have hpow_pos : (0 : ℝ) < (2 : ℝ) ^ (emax - prec) := zpow_pos h2pos (emax - prec)
  have hlt : (2 : ℝ) ^ emax - (2 : ℝ) ^ (emax - prec) < (2 : ℝ) ^ emax := by linarith
  exact lt_of_le_of_lt hle' hlt

namespace binary_float

theorem toBinary754_bounded {prec emax : Int} [Prec_gt_0 prec]
    (x : binary_float prec emax) :
    Binary754_bounded (toBinary754 x) := by
  cases x with
  | B754_zero s => simp [toBinary754, Binary754_bounded]
  | B754_infinity s => simp [toBinary754, Binary754_bounded]
  | B754_nan s payload hPayload => simp [toBinary754, Binary754_bounded]
  | B754_finite s m e hBounded =>
      simp only [toBinary754, Binary754_bounded]
      exact range_bounded_of_specFloat_bounded
        (FloatSpec.Core.Zaux.positiveToNat m) e
        (FloatSpec.Core.Zaux.positiveToNat_pos m) hBounded

end binary_float

/-- FLoCq `B2R_inj`, on the proof-carrying `binary_float`. -/
@[flocq_source "src/IEEE754/Binary.v" 392 "B2R_inj"]
theorem B2R_inj {prec emax : Int}
    (x y : binary_float prec emax)
    (hx : binary_float.is_finite_strict x = true)
    (hy : binary_float.is_finite_strict y = true)
    (hR : binary_float.B2R x = binary_float.B2R y) :
    x = y := by
  cases x with
  | B754_zero sx => simp [binary_float.is_finite_strict] at hx
  | B754_infinity sx => simp [binary_float.is_finite_strict] at hx
  | B754_nan sx payload hPayload => simp [binary_float.is_finite_strict] at hx
  | B754_finite sx mx ex hmxBounded =>
      cases y with
      | B754_zero sy => simp [binary_float.is_finite_strict] at hy
      | B754_infinity sy => simp [binary_float.is_finite_strict] at hy
      | B754_nan sy payload hPayload => simp [binary_float.is_finite_strict] at hy
      | B754_finite sy my ey hmyBounded =>
          let nx := FloatSpec.Core.Zaux.positiveToNat mx
          let ny := FloatSpec.Core.Zaux.positiveToNat my
          let fx : FloatSpec.Core.Defs.FlocqFloat 2 :=
            ⟨if sx then -(nx : Int) else (nx : Int), ex⟩
          let fy : FloatSpec.Core.Defs.FlocqFloat 2 :=
            ⟨if sy then -(ny : Int) else (ny : Int), ey⟩
          have hnx : 0 < nx := FloatSpec.Core.Zaux.positiveToNat_pos mx
          have hny : 0 < ny := FloatSpec.Core.Zaux.positiveToNat_pos my
          have hcx : FloatSpec.Core.Generic_fmt.canonical 2
              (FLT_exp (3 - emax - prec) prec) fx := by
            have hcanon := canonical_mantissa_of_specFloat_bounded hmxBounded
            have htrip := canonical_canonical_mantissa_compat
              (prec:=prec) (emax:=emax) sx nx ex hnx hcanon
            simpa [fx] using htrip
          have hcy : FloatSpec.Core.Generic_fmt.canonical 2
              (FLT_exp (3 - emax - prec) prec) fy := by
            have hcanon := canonical_mantissa_of_specFloat_bounded hmyBounded
            have htrip := canonical_canonical_mantissa_compat
              (prec:=prec) (emax:=emax) sy ny ey hny hcanon
            simpa [fy] using htrip
          have hF2R : F2R fx = F2R fy := by
            simpa [binary_float.B2R, fx, fy, nx, ny] using hR
          have hfloat := FloatSpec.Core.Generic_fmt.canonical_unique
            2 (by norm_num : (1 : Int) < 2)
            (FLT_exp (3 - emax - prec) prec) fx fy hcx hcy hF2R
          have hparts :
              (if sx then -(nx : Int) else (nx : Int)) =
                  (if sy then -(ny : Int) else (ny : Int)) ∧ ex = ey := by
            simpa [fx, fy, FloatSpec.Core.Defs.FlocqFloat.mk.injEq] using hfloat
          rcases hparts with ⟨hm, he⟩
          cases sx <;> cases sy
          · simp only [Bool.false_eq_true, ↓reduceIte] at hm
            have hn : nx = ny := by exact_mod_cast hm
            have hp : mx = my :=
              FloatSpec.Core.Zaux.positiveToNat_injective hn
            subst my
            subst ey
            rfl
          · simp only [Bool.false_eq_true, ↓reduceIte] at hm
            have hnxR : (0 : Int) < nx := by exact_mod_cast hnx
            have hnyR : (0 : Int) < ny := by exact_mod_cast hny
            omega
          · simp only [Bool.false_eq_true, ↓reduceIte] at hm
            have hnxR : (0 : Int) < nx := by exact_mod_cast hnx
            have hnyR : (0 : Int) < ny := by exact_mod_cast hny
            omega
          · simp only [↓reduceIte, neg_inj] at hm
            have hn : nx = ny := by exact_mod_cast hm
            have hp : mx = my :=
              FloatSpec.Core.Zaux.positiveToNat_injective hn
            subst my
            subst ey
            rfl

/-- FLoCq `abs_B2R_le_emax_minus_prec`; validity is carried by `x`. -/
theorem abs_B2R_le_emax_minus_prec {prec emax : Int} [Prec_gt_0 prec]
    (x : binary_float prec emax) :
    |binary_float.B2R x| ≤
      FloatSpec.Core.Raux.bpow 2 emax -
        FloatSpec.Core.Raux.bpow 2 (emax - prec) := by
  have h := abs_B2R_le_emax_minus_prec_compat
    (binary_float.toBinary754 x) (binary_float.toBinary754_bounded x)
  simpa [binary_float.B2R_toBinary754] using h

/-- FLoCq `abs_B2R_lt_emax`; validity is carried by `x`. -/
theorem abs_B2R_lt_emax {prec emax : Int} [Prec_gt_0 prec]
    (x : binary_float prec emax) :
    |binary_float.B2R x| <
      FloatSpec.Core.Raux.bpow 2 emax := by
  have h := abs_B2R_lt_emax_compat
    (binary_float.toBinary754 x) (binary_float.toBinary754_bounded x)
  simpa [binary_float.B2R_toBinary754] using h

-- Local strict-finiteness classifier for Binary754 (finite and nonzero semantics).
-- Coq uses a positive mantissa, so finite implies nonzero. This local
-- classifier keeps the shape and defers proof obligations elsewhere.
-- Duplicate declaration cleanup: ensure only the early local definition exists.

-- Coq: abs_B2R_ge_emin — strict finiteness implies lower bound by bpow emin
theorem abs_B2R_ge_emin_compat {prec emax : Int}
  (x : Binary754 prec emax)
  (hx : is_finite_strict_Bin (prec:=prec) (emax:=emax) x = true)
  (hbounded : Binary754_bounded (prec:=prec) (emax:=emax) x)
  (hvalid : valid_FF x.val) :
    FloatSpec.Core.Raux.bpow 2 (3 - emax - prec)
      ≤ |B2R (prec:=prec) (emax:=emax) x| := by
  -- Extract finite structure from is_finite_strict_Bin
  unfold is_finite_strict_Bin at hx
  -- Match on x.val to extract (s, m, e)
  match hval : x.val with
  | FullFloat.F754_zero _ => simp [hval] at hx
  | FullFloat.F754_infinity _ => simp [hval] at hx
  | FullFloat.F754_nan _ _ => simp [hval] at hx
  | FullFloat.F754_finite s m e =>
    -- Extract bounded constraint
    simp only [Binary754_bounded, hval] at hbounded
    -- Extract mantissa positivity from valid_FF
    simp only [valid_FF, hval] at hvalid
    -- hvalid : 0 < m
    -- hbounded : bounded prec emax m e = true
    -- Unfold B2R for finite
    simp only [B2R, FF2R, hval]
    -- Goal: bpow 2 (3 - emax - prec) ≤ |F2R (if s then -m else m, e)|
    simp only [FloatSpec.Core.Raux.bpow]
    simp only [F2R, FloatSpec.Core.Defs.F2R, FloatSpec.Core.Defs.FlocqFloat.Fnum,
               FloatSpec.Core.Defs.FlocqFloat.Fexp]
    -- Handle sign case
    have h2_eq : ((2 : ℤ) : ℝ) = (2 : ℝ) := by norm_num
    have h2pos : (0 : ℝ) < 2 := by norm_num
    have hpow_nonneg : (0 : ℝ) ≤ ((2 : ℤ) : ℝ) ^ e := by apply zpow_nonneg; norm_num
    by_cases hs : s
    · -- s = true: value is -(m:Int)
      simp only [hs, ↓reduceIte, Int.cast_neg, Int.cast_natCast]
      rw [neg_mul, abs_neg, abs_mul]
      rw [abs_of_nonneg (Nat.cast_nonneg m)]
      rw [abs_of_nonneg hpow_nonneg]
      simp only [h2_eq]
      -- Goal: 2^(3-emax-prec) ≤ m * 2^e
      have hge := bounded_ge_emin (prec:=prec) (emax:=emax) m e hbounded hvalid
      simp only [F2R, FloatSpec.Core.Defs.F2R, FloatSpec.Core.Defs.FlocqFloat.Fnum,
                 FloatSpec.Core.Defs.FlocqFloat.Fexp, FloatSpec.Core.Raux.bpow, h2_eq] at hge
      exact hge
    · -- s = false: value is m
      have hs' : s = false := Bool.eq_false_iff.mpr hs
      simp only [hs', ↓reduceIte, Int.cast_natCast]
      rw [abs_mul]
      rw [abs_of_nonneg (Nat.cast_nonneg m)]
      rw [abs_of_nonneg hpow_nonneg]
      simp only [h2_eq]
      -- Goal: 2^(3-emax-prec) ≤ m * 2^e
      have hge := bounded_ge_emin (prec:=prec) (emax:=emax) m e hbounded hvalid
      simp only [F2R, FloatSpec.Core.Defs.F2R, FloatSpec.Core.Defs.FlocqFloat.Fnum,
                 FloatSpec.Core.Defs.FlocqFloat.Fexp, FloatSpec.Core.Raux.bpow, h2_eq] at hge
      exact hge

-- Coq: bounded_canonical_lt_emax
-- If a finite float with positive mantissa is canonical and its real value is
-- strictly below bpow emax, then the mantissa/exponent pair is `bounded`.
-- Helper: For mx > 0, Raux.mag 2 (F2R ⟨mx, ex⟩) = Zdigits 2 mx + ex
private lemma mag_F2R_eq_Zdigits_add_ex (mx : Nat) (ex : Int) (hmx_pos : 0 < mx) :
    FloatSpec.Core.Raux.mag 2 (F2R (FloatSpec.Core.Defs.FlocqFloat.mk (mx : Int) ex : FloatSpec.Core.Defs.FlocqFloat 2)) =
    FloatSpec.Core.Digits.Zdigits 2 (mx : Int) + ex := by
  have h2gt1 : (1 : Int) < 2 := by norm_num
  have hmx_int_pos : (0 : Int) < (mx : Int) := Nat.cast_pos.mpr hmx_pos
  have hmx_int_ne : (mx : Int) ≠ 0 := ne_of_gt hmx_int_pos
  have hmx_real_ne : ((mx : Int) : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hmx_int_ne
  -- F2R ⟨mx, ex⟩ = mx * (2 : Int)^ex as ℝ
  have hF2R_eq : F2R (FloatSpec.Core.Defs.FlocqFloat.mk (mx : Int) ex : FloatSpec.Core.Defs.FlocqFloat 2) =
                ((mx : Int) : ℝ) * ((2 : Int) : ℝ) ^ ex := by
    simp only [F2R, FloatSpec.Core.Defs.F2R, FloatSpec.Core.Defs.FlocqFloat.Fnum,
               FloatSpec.Core.Defs.FlocqFloat.Fexp]
  rw [hF2R_eq]
  -- Use mag_mult_bpow_eq: mag 2 (mx * 2^ex) = mag 2 mx + ex
  have hmag_mult := FloatSpec.Calc.Sqrt.mag_mult_bpow_eq 2 ((mx : Int) : ℝ) ex hmx_real_ne h2gt1
  rw [hmag_mult]
  -- Use mag_eq_Zdigits: mag 2 mx = Zdigits 2 mx
  have hmag_zdig := FloatSpec.Calc.Sqrt.mag_eq_Zdigits 2 (mx : Int) hmx_int_pos h2gt1
  rw [hmag_zdig]

-- Coq uses `Zpos mx` (strictly positive) in bounded_canonical_lt_emax.
-- We add `hmx_pos : 0 < mx` to match the original Coq semantics.
-- Following Coq's Flocq, we also require prec > 0 and prec < emax (standard IEEE format constraints).
theorem bounded_canonical_lt_emax {prec emax : Int}
  (hprec_pos : 0 < prec)  -- Coq: Prec_gt_0 prec
  (hprec_lt_emax : prec < emax)  -- Coq: Prec_lt_emax prec emax
  (mx : Nat) (ex : Int)
  (hmx_pos : 0 < mx)  -- mx > 0 (matches Coq's Zpos mx)
  (hcanon : FloatSpec.Core.Generic_fmt.canonical 2 (FLT_exp (3 - emax - prec) prec)
              (FloatSpec.Core.Defs.FlocqFloat.mk (mx : Int) ex))
  (hval :
    F2R (FloatSpec.Core.Defs.FlocqFloat.mk (mx : Int) ex : FloatSpec.Core.Defs.FlocqFloat 2)
      < FloatSpec.Core.Raux.bpow 2 emax) :
    bounded (prec:=prec) (emax:=emax) mx ex = true := by
  -- Goal: bounded mx ex = true
  -- This requires proving three conditions:
  -- 1. mx < 2^prec.toNat (mantissa bound)
  -- 2. 3 - emax - prec ≤ ex (lower exponent bound)
  -- 3. ex ≤ emax - prec (upper exponent bound)
  simp only [bounded, Bool.and_eq_true, decide_eq_true_eq]

  -- From canonical: ex = FLT_exp emin prec (mag 2 (F2R f))
  -- where f = ⟨mx, ex⟩ and emin = 3 - emax - prec
  unfold FloatSpec.Core.Generic_fmt.canonical at hcanon
  simp only [FloatSpec.Core.Defs.FlocqFloat.Fexp] at hcanon
  -- hcanon : ex = FLT_exp (3 - emax - prec) prec (mag 2 (F2R ⟨mx, ex⟩))

  -- Let M := mag 2 (F2R ⟨mx, ex⟩) and emin := 3 - emax - prec
  set emin := 3 - emax - prec with hemin
  set M := FloatSpec.Core.Raux.mag 2 (F2R (FloatSpec.Core.Defs.FlocqFloat.mk (mx : Int) ex : FloatSpec.Core.Defs.FlocqFloat 2)) with hM

  -- From hcanon: ex = FLT_exp emin prec M = max (M - prec) emin
  have hex_eq : ex = max (M - prec) emin := by
    rw [hcanon]
    -- FLT_exp emin prec M = max (M - prec) emin by definition
    -- Note: FLT_exp takes arguments in order (emin, prec, e)
    simp only [FLT_exp, FloatSpec.Core.FLT.FLT_exp]
    -- The definition is max (e - prec) emin

  -- With hmx_pos, mx > 0, so we proceed directly with the non-zero case
  have hmx_zero : mx ≠ 0 := Nat.pos_iff_ne_zero.mp hmx_pos

  -- mx ≠ 0 case
  have hmx_int_pos : (0 : Int) < (mx : Int) := Nat.cast_pos.mpr hmx_pos
  have hmx_int_ne : (mx : Int) ≠ 0 := Int.ofNat_ne_zero.mpr hmx_zero
  have hmx_real_pos : (0 : ℝ) < ((mx : Int) : ℝ) := Int.cast_pos.mpr hmx_int_pos
  have hmx_real_ne : ((mx : Int) : ℝ) ≠ 0 := ne_of_gt hmx_real_pos

  -- F2R ⟨mx, ex⟩ = mx * 2^ex > 0
  have hf2r_pos : 0 < F2R (FloatSpec.Core.Defs.FlocqFloat.mk (mx : Int) ex : FloatSpec.Core.Defs.FlocqFloat 2) := by
    simp only [F2R, FloatSpec.Core.Defs.F2R, FloatSpec.Core.Defs.FlocqFloat.Fnum,
               FloatSpec.Core.Defs.FlocqFloat.Fexp]
    apply mul_pos hmx_real_pos
    exact zpow_pos (by norm_num : (0 : ℝ) < 2) ex

  have hf2r_ne : F2R (FloatSpec.Core.Defs.FlocqFloat.mk (mx : Int) ex : FloatSpec.Core.Defs.FlocqFloat 2) ≠ 0 :=
    ne_of_gt hf2r_pos

  -- Key: From hval (F2R < bpow 2 emax) and F2R > 0, we get mag 2 (F2R) ≤ emax
  have h2gt1 : (1 : Int) < 2 := by norm_num
  have habs_lt : |F2R (FloatSpec.Core.Defs.FlocqFloat.mk (mx : Int) ex : FloatSpec.Core.Defs.FlocqFloat 2)| <
                (2 : ℝ) ^ emax := by
    rw [abs_of_pos hf2r_pos]
    simp only [FloatSpec.Core.Raux.bpow] at hval
    exact hval

  have hmag_le_emax : M ≤ emax := by
    have hspec := FloatSpec.Core.Raux.mag_le_bpow 2
      (F2R (FloatSpec.Core.Defs.FlocqFloat.mk (mx : Int) ex : FloatSpec.Core.Defs.FlocqFloat 2))
      emax h2gt1 hf2r_ne habs_lt
    exact hspec

  -- mag 2 (F2R ⟨mx, ex⟩) = Zdigits 2 mx + ex
  have hmag_eq_digits : M = FloatSpec.Core.Digits.Zdigits 2 (mx : Int) + ex := by
    rw [hM]
    exact mag_F2R_eq_Zdigits_add_ex mx ex hmx_pos

  -- From this: Zdigits 2 mx = M - ex
  have hzdig_eq : FloatSpec.Core.Digits.Zdigits 2 (mx : Int) = M - ex := by
    omega

  -- From Zdigits definition: 2^(Zdigits - 1) ≤ |mx| < 2^Zdigits
  have hzdig_spec :=
    FloatSpec.Core.Digits.Zdigits_correct_from_nonzero_payload 2 (mx : Int) hmx_int_ne h2gt1
  obtain ⟨hlow, hhi⟩ := hzdig_spec
  -- Since mx > 0, |mx| = mx
  simp only [abs_of_pos hmx_int_pos] at hlow hhi

  constructor
  constructor
  · -- Part 1: mx < 2^prec.toNat (mantissa bound)
    -- Case analysis on whether we're in normal or subnormal range
    by_cases hnormal : M - prec ≥ emin
    · -- Normal case: ex = M - prec, so Zdigits 2 mx = prec
      have hex_normal : ex = M - prec := by
        rw [hex_eq]
        exact max_eq_left hnormal
      have hzdig_prec : FloatSpec.Core.Digits.Zdigits 2 (mx : Int) = prec := by
        rw [hzdig_eq, hex_normal]
        ring

      -- Zdigits ≥ 1 for mx > 0, so prec ≥ 1 > 0
      have hprec_pos := FloatSpec.Core.Digits.Zdigits_gt_0 2 (mx : Int) hmx_int_ne h2gt1
      rw [hzdig_prec] at hprec_pos
      have hprec_nonneg : 0 ≤ prec := le_of_lt hprec_pos

      -- From hhi: mx < 2^(Zdigits 2 mx).natAbs = 2^prec.natAbs = 2^prec.toNat
      -- Since prec ≥ 0, prec.natAbs = prec.toNat
      have hprec_natAbs : prec.natAbs = prec.toNat := by
        have h1 : (prec.natAbs : Int) = prec := Int.natAbs_of_nonneg hprec_nonneg
        have h2 : (prec.toNat : Int) = prec := Int.toNat_of_nonneg hprec_nonneg
        omega

      -- The bound hhi uses d.natAbs where d = Id.run (Zdigits 2 mx)
      -- We have hzdig_prec: Zdigits 2 mx = prec
      -- So (Zdigits 2 mx).natAbs = prec.natAbs = prec.toNat
      have hd_natAbs : (FloatSpec.Core.Digits.Zdigits 2 (mx : Int)).natAbs = prec.toNat := by
        rw [hzdig_prec, hprec_natAbs]

      -- Rewrite hhi: (mx : Int) < 2^(Id.run (Zdigits 2 mx)).natAbs
      -- Id.run for Zdigits is just the identity
      have hhi' : (mx : Int) < (2 : Int) ^ prec.toNat := by
        have heq : (Id.run (FloatSpec.Core.Digits.Zdigits 2 (mx : Int))).natAbs = prec.toNat := hd_natAbs
        simp only [Id.run] at heq hhi
        rw [heq] at hhi
        exact hhi

      -- Now convert: (mx : Int) < (2 : Int)^prec.toNat → mx < (2 : Nat)^prec.toNat
      have h_cast : (2 : Int) ^ prec.toNat = ↑((2 : Nat) ^ prec.toNat) := by
        simp only [Nat.cast_pow, Nat.cast_ofNat]
      rw [h_cast] at hhi'
      -- hhi' : (mx : Int) < ↑(2^prec.toNat), i.e., ↑mx < ↑(2^prec.toNat)
      -- Since both are Nat casts, this is equivalent to mx < 2^prec.toNat
      exact Nat.cast_lt.mp hhi'

    · -- Subnormal case: M - prec < emin, so ex = emin
      push Not at hnormal
      have hex_subnormal : ex = emin := by
        rw [hex_eq]
        exact max_eq_right (le_of_lt hnormal)

      -- Zdigits 2 mx < prec in subnormal case
      have hzdig_lt_prec : FloatSpec.Core.Digits.Zdigits 2 (mx : Int) < prec := by
        rw [hzdig_eq, hex_subnormal]
        omega

      -- Zdigits ≥ 1 for mx > 0
      have hzdig_pos := FloatSpec.Core.Digits.Zdigits_gt_0 2 (mx : Int) hmx_int_ne h2gt1

      have hprec_pos' : 0 < prec := lt_trans hzdig_pos hzdig_lt_prec
      have hprec_nonneg : 0 ≤ prec := le_of_lt hprec_pos'
      have hzdig_nonneg : 0 ≤ FloatSpec.Core.Digits.Zdigits 2 (mx : Int) := le_of_lt hzdig_pos

      -- Strategy: From hhi: (mx : Int) < (2 : Int)^(Zdigits.natAbs)
      -- Since Zdigits < prec, we have Zdigits.natAbs < prec.natAbs = prec.toNat
      -- So mx < 2^Zdigits.natAbs < 2^prec.toNat

      have hzdig_natAbs : (FloatSpec.Core.Digits.Zdigits 2 (mx : Int)).natAbs =
                          (FloatSpec.Core.Digits.Zdigits 2 (mx : Int)).toNat := by
        have h1 : ((FloatSpec.Core.Digits.Zdigits 2 (mx : Int)).natAbs : Int) =
                  FloatSpec.Core.Digits.Zdigits 2 (mx : Int) := Int.natAbs_of_nonneg hzdig_nonneg
        have h2 : ((FloatSpec.Core.Digits.Zdigits 2 (mx : Int)).toNat : Int) =
                  FloatSpec.Core.Digits.Zdigits 2 (mx : Int) := Int.toNat_of_nonneg hzdig_nonneg
        omega

      have hprec_natAbs : prec.natAbs = prec.toNat := by
        have h1 : (prec.natAbs : Int) = prec := Int.natAbs_of_nonneg hprec_nonneg
        have h2 : (prec.toNat : Int) = prec := Int.toNat_of_nonneg hprec_nonneg
        omega

      -- Since Zdigits < prec and both are nonneg, Zdigits.natAbs < prec.natAbs
      have hzdig_natAbs_lt : (FloatSpec.Core.Digits.Zdigits 2 (mx : Int)).natAbs < prec.natAbs := by
        have h1 : (FloatSpec.Core.Digits.Zdigits 2 (mx : Int)).natAbs =
                  (FloatSpec.Core.Digits.Zdigits 2 (mx : Int)).toNat := hzdig_natAbs
        have h2 : prec.natAbs = prec.toNat := hprec_natAbs
        rw [h1, h2]
        -- Need: (Zdigits 2 mx).toNat < prec.toNat
        -- This follows from Zdigits 2 mx < prec and both ≥ 0
        have hzdig_cast : (↑((FloatSpec.Core.Digits.Zdigits 2 (mx : Int)).toNat) : Int) =
                         FloatSpec.Core.Digits.Zdigits 2 (mx : Int) :=
          Int.toNat_of_nonneg hzdig_nonneg
        have hprec_cast : (↑prec.toNat : Int) = prec := Int.toNat_of_nonneg hprec_nonneg
        omega

      -- hhi : (mx : Int) < (2 : Int) ^ (Zdigits 2 mx).natAbs

      -- mx < 2^Zdigits.natAbs ≤ 2^(prec.natAbs - 1) < 2^prec.natAbs
      -- Since Zdigits.natAbs < prec.natAbs, we have 2^Zdigits.natAbs < 2^prec.natAbs
      have h_pow_mono_nat : (2 : Nat) ^ (FloatSpec.Core.Digits.Zdigits 2 (mx : Int)).natAbs <
                           (2 : Nat) ^ prec.natAbs := by
        apply Nat.pow_lt_pow_right (by norm_num : 1 < 2) hzdig_natAbs_lt
      -- Cast to Int
      have h_pow_mono : (2 : Int) ^ (FloatSpec.Core.Digits.Zdigits 2 (mx : Int)).natAbs <
                       (2 : Int) ^ prec.natAbs := by
        have h1 : (2 : Int) ^ (FloatSpec.Core.Digits.Zdigits 2 (mx : Int)).natAbs =
                 ↑((2 : Nat) ^ (FloatSpec.Core.Digits.Zdigits 2 (mx : Int)).natAbs) := by
          simp only [Nat.cast_pow, Nat.cast_ofNat]
        have h2 : (2 : Int) ^ prec.natAbs = ↑((2 : Nat) ^ prec.natAbs) := by
          simp only [Nat.cast_pow, Nat.cast_ofNat]
        rw [h1, h2]
        exact Nat.cast_lt.mpr h_pow_mono_nat

      have hhi' : (mx : Int) < (2 : Int) ^ prec.natAbs := lt_trans hhi h_pow_mono

      -- Convert: (mx : Int) < (2 : Int)^prec.natAbs = (2 : Int)^prec.toNat
      rw [hprec_natAbs] at hhi'
      -- hhi' : (mx : Int) < (2 : Int)^prec.toNat

      -- Now show mx < (2 : Nat)^prec.toNat
      have h_cast : (2 : Int) ^ prec.toNat = ↑((2 : Nat) ^ prec.toNat) := by
        simp only [Nat.cast_pow, Nat.cast_ofNat]
      rw [h_cast] at hhi'
      exact Nat.cast_lt.mp hhi'

  · -- Part 2: emin ≤ ex
    rw [hex_eq, hemin]
    exact le_max_right (M - prec) (3 - emax - prec)

  · -- Part 3: ex ≤ emax - prec
    rw [hex_eq]
    apply max_le
    · -- M - prec ≤ emax - prec follows from M ≤ emax
      omega
    · -- emin ≤ emax - prec, i.e., 3 - emax - prec ≤ emax - prec
      rw [hemin]
      -- The constraint 3 - emax - prec ≤ emax - prec simplifies to 3 ≤ 2*emax
      -- i.e., emax ≥ 2. From prec > 0 and prec < emax:
      -- prec ≥ 1 (since prec > 0 for Int), so emax > prec ≥ 1, thus emax ≥ 2.
      -- Therefore 2*emax ≥ 4 ≥ 3.
      omega

-- Alignment helper (Coq: shl_align)
-- `shl_align mx ex e` aligns mantissa `mx` (at exponent `ex`) to target exponent `e`.
-- When `e ≤ ex`: shifts left by `(ex - e)` bits, giving `(mx * 2^(ex-e), e)`
-- When `e > ex`: cannot align (would require right shift), returns `(mx, ex)` unchanged
def shl_align (mx : Nat) (ex e : Int) : Nat × Int :=
  if e ≤ ex then
    -- Shift left to decrease exponent to e
    let shift := (ex - e).toNat
    (mx * 2^shift, e)
  else
    -- Cannot shift right, return unchanged
    (mx, ex)

-- Alignment helper (Coq: shl_align_fexp)
-- In Coq, this calls `shl_align mx ex (fexp (Zpos (digits2_pos mx) + ex))`.
-- The target exponent is computed using FLT_exp.
def shl_align_fexp {prec emax : Int} (mx : Nat) (ex : Int) : Nat × Int :=
  let target_exp := FLT_exp (3 - emax - prec) prec (FloatSpec.Core.Digits.Zdigits 2 (mx : Int) + ex)
  shl_align mx ex target_exp

-- Helper to get bounds from Zdigits_correct for base 2
private lemma Zdigits_bounds_2 (n : Int) (hn : n ≠ 0) :
    2 ^ (FloatSpec.Core.Digits.Zdigits 2 n - 1).natAbs ≤ |n| ∧
    |n| < 2 ^ (FloatSpec.Core.Digits.Zdigits 2 n).natAbs := by
  exact FloatSpec.Core.Digits.Zdigits_correct_from_nonzero_payload 2 n hn
    (by norm_num : (2:Int) > 1)

-- Show Zdigits 2 n > 0 when n ≠ 0
private lemma Zdigits_pos_of_ne_zero (n : Int) (hn : n ≠ 0) :
    FloatSpec.Core.Digits.Zdigits 2 n > 0 := by
  have ⟨hlow, hupp⟩ := Zdigits_bounds_2 n hn
  set d := FloatSpec.Core.Digits.Zdigits 2 n with hd_def
  by_contra hd_nonpos
  push Not at hd_nonpos
  have hn_abs_pos : |n| ≥ 1 := Int.one_le_abs hn
  rcases (eq_or_lt_of_le hd_nonpos) with hd_zero | hd_neg
  · rw [hd_zero] at hupp; simp at hupp; omega
  · have hd_natabs : d.natAbs = (-d).toNat := by omega
    have hd1_natabs : (d - 1).natAbs = (1 - d).toNat := by omega
    have h_exp_rel : (1 - d).toNat = (-d).toNat + 1 := by omega
    rw [hd_natabs] at hupp
    rw [hd1_natabs, h_exp_rel, pow_succ] at hlow
    have h2pow_pos : (0 : Int) < 2 ^ (-d).toNat := by positivity
    linarith

-- Zdigits uniqueness for base 2
private lemma Zdigits_unique_2 (n e : Int) (hn : n ≠ 0)
    (hlow : 2 ^ (e - 1).natAbs ≤ |n|) (hupp : |n| < 2 ^ e.natAbs) :
    FloatSpec.Core.Digits.Zdigits 2 n = e := by
  have ⟨hlow_d, hupp_d⟩ := Zdigits_bounds_2 n hn
  set d := FloatSpec.Core.Digits.Zdigits 2 n with hd_def
  have hd_pos : d > 0 := Zdigits_pos_of_ne_zero n hn
  have he_pos : e > 0 := by
    by_contra he_nonpos
    push Not at he_nonpos
    have hn_abs_pos : |n| ≥ 1 := Int.one_le_abs hn
    rcases (eq_or_lt_of_le he_nonpos) with he_zero | he_neg
    · rw [he_zero] at hupp; simp at hupp; omega
    · have he_natabs : e.natAbs = (-e).toNat := by omega
      have he1_natabs : (e - 1).natAbs = (1 - e).toNat := by omega
      have h_exp_rel : (1 - e).toNat = (-e).toNat + 1 := by omega
      rw [he_natabs] at hupp
      rw [he1_natabs, h_exp_rel, pow_succ] at hlow
      have h2pow_pos : (0 : Int) < 2 ^ (-e).toNat := by positivity
      linarith
  have hd_natabs : d.natAbs = d.toNat := by omega
  have he_natabs : e.natAbs = e.toNat := by omega
  have hd1_natabs : (d - 1).natAbs = (d - 1).toNat := by omega
  have he1_natabs : (e - 1).natAbs = (e - 1).toNat := by omega
  have hlow_d' : (2 : Int) ^ (d - 1).toNat ≤ |n| := by rwa [hd1_natabs] at hlow_d
  have hupp_d' : |n| < (2 : Int) ^ d.toNat := by rwa [hd_natabs] at hupp_d
  have hlow' : (2 : Int) ^ (e - 1).toNat ≤ |n| := by rwa [he1_natabs] at hlow
  have hupp' : |n| < (2 : Int) ^ e.toNat := by rwa [he_natabs] at hupp
  have h_e_le_d : e ≤ d := by
    by_contra h; push Not at h
    have h' : d.toNat ≤ (e - 1).toNat := by omega
    have h2pow_mono : (2 : Int) ^ d.toNat ≤ 2 ^ (e - 1).toNat := by
      apply pow_le_pow_right₀ (by norm_num : (1 : Int) ≤ 2) h'
    linarith
  have h_d_le_e : d ≤ e := by
    by_contra h; push Not at h
    have h' : e.toNat ≤ (d - 1).toNat := by omega
    have h2pow_mono : (2 : Int) ^ e.toNat ≤ 2 ^ (d - 1).toNat := by
      apply pow_le_pow_right₀ (by norm_num : (1 : Int) ≤ 2) h'
    linarith
  omega

-- Helper lemma: Zdigits 2 (n * 2^k) = Zdigits 2 n + k (when n > 0, k ≥ 0)
-- This is a consequence of Zdigits_mult_Zpower in Digits.lean.
-- We state it as a private lemma for use in shl_align_fexp_correct.
private lemma Zdigits_mul_pow2 (n : Nat) (k : Int) (hn : n ≠ 0) (hk : 0 ≤ k) :
    FloatSpec.Core.Digits.Zdigits 2 ((n : Int) * 2 ^ k.natAbs) =
    FloatSpec.Core.Digits.Zdigits 2 (n : Int) + k := by
  have hn_int : (n : Int) ≠ 0 := by
    intro h; apply hn; exact Nat.cast_eq_zero.mp h
  set d := FloatSpec.Core.Digits.Zdigits 2 (n : Int) with hd_def
  let prod := (n : Int) * 2 ^ k.natAbs
  have hprod_ne_zero : prod ≠ 0 := by
    apply mul_ne_zero hn_int
    apply pow_ne_zero; norm_num
  have ⟨hlow_n, hupp_n⟩ := Zdigits_bounds_2 (n : Int) hn_int
  simp only [← hd_def] at hlow_n hupp_n
  have hn_nonneg : (0 : Int) ≤ n := Nat.cast_nonneg n
  have habs_n : |((n : Int))| = n := abs_of_nonneg hn_nonneg
  have hprod_nonneg : (0 : Int) ≤ prod := by
    apply mul_nonneg hn_nonneg
    apply pow_nonneg; norm_num
  have habs_prod : |prod| = prod := abs_of_nonneg hprod_nonneg
  have hk_natAbs : (k.natAbs : Int) = k := Int.natAbs_of_nonneg hk
  have hd_pos : d > 0 := Zdigits_pos_of_ne_zero (n : Int) hn_int
  have hdk_pos : d + k > 0 := by omega
  have hdk_natAbs : (d + k).natAbs = (d + k).toNat := by omega
  have hdk1_natAbs : (d + k - 1).natAbs = (d + k - 1).toNat := by omega
  have hd_natAbs : d.natAbs = d.toNat := by omega
  have hd1_natAbs : (d - 1).natAbs = (d - 1).toNat := by omega
  rw [hd1_natAbs] at hlow_n
  rw [hd_natAbs] at hupp_n
  rw [habs_n] at hlow_n hupp_n
  have h2pow_pos : (0 : Int) < 2 ^ k.natAbs := by positivity
  have hlow_prod : (2 : Int) ^ (d - 1).toNat * 2 ^ k.natAbs ≤ prod := by
    simp only [prod]
    apply mul_le_mul_of_nonneg_right hlow_n (le_of_lt h2pow_pos)
  have hupp_prod : prod < (2 : Int) ^ d.toNat * 2 ^ k.natAbs := by
    simp only [prod]
    apply mul_lt_mul_of_pos_right hupp_n h2pow_pos
  have hpow_add_low : (2 : Int) ^ (d - 1).toNat * 2 ^ k.natAbs = 2 ^ ((d - 1).toNat + k.natAbs) := by
    rw [← pow_add]
  have hpow_add_upp : (2 : Int) ^ d.toNat * 2 ^ k.natAbs = 2 ^ (d.toNat + k.natAbs) := by
    rw [← pow_add]
  rw [hpow_add_low] at hlow_prod
  rw [hpow_add_upp] at hupp_prod
  have hexp_low : (d - 1).toNat + k.natAbs = (d + k - 1).toNat := by omega
  have hexp_upp : d.toNat + k.natAbs = (d + k).toNat := by omega
  rw [hexp_low] at hlow_prod
  rw [hexp_upp] at hupp_prod
  rw [← hdk1_natAbs] at hlow_prod
  rw [← hdk_natAbs] at hupp_prod
  rw [← habs_prod] at hlow_prod hupp_prod
  exact Zdigits_unique_2 prod (d + k) hprod_ne_zero hlow_prod hupp_prod

-- Coq: shl_align_fexp_correct
-- After alignment, the real value is preserved and the new exponent
-- satisfies the `fexp` bound at `Zdigits mx' + ex'`.
-- Note: In Coq, mx is a `positive` (strictly positive), so mx ≠ 0 is required.
theorem shl_align_fexp_correct {prec emax : Int}
  (mx : Nat) (ex : Int) (hmx_pos : mx ≠ 0) :
    let mx' := (shl_align_fexp (prec := prec) (emax := emax) mx ex).1
    let ex' := (shl_align_fexp (prec := prec) (emax := emax) mx ex).2
    F2R (FloatSpec.Core.Defs.FlocqFloat.mk (mx' : Int) ex' : FloatSpec.Core.Defs.FlocqFloat 2)
      = F2R (FloatSpec.Core.Defs.FlocqFloat.mk (mx : Int) ex : FloatSpec.Core.Defs.FlocqFloat 2)
      ∧ ex' ≤ FLT_exp (3 - emax - prec) prec ((FloatSpec.Core.Digits.Zdigits 2 (mx' : Int)) + ex') := by
  simp only [shl_align_fexp, shl_align]
  -- Let's name the target exponent for clarity
  set target_exp := FLT_exp (3 - emax - prec) prec (FloatSpec.Core.Digits.Zdigits 2 (mx : Int) + ex) with htarget
  constructor
  · -- Part 1: F2R is preserved
    split_ifs with h
    · -- Case: target_exp ≤ ex, we shifted
      -- After simplification, we have:
      -- F2R {mx * 2^(ex - target_exp), target_exp} = F2R {mx, ex}
      -- i.e., (mx * 2^(ex - target_exp)) * 2^target_exp = mx * 2^ex
      simp only [Id.run, F2R, FloatSpec.Core.Defs.F2R]
      -- Goal: (mx * 2^k) * 2^target_exp = mx * 2^ex where k = (ex - target_exp).toNat
      have hshift_nonneg : 0 ≤ ex - target_exp := by omega
      have hshift : (ex - target_exp).toNat = (ex - target_exp) := Int.toNat_of_nonneg hshift_nonneg
      have h2ne : (2 : ℝ) ≠ 0 := by norm_num
      -- Push coercions through to make structure clearer
      push_cast
      -- Goal is now in terms of ℝ with simpler structure
      -- (mx * 2^k) * 2^target_exp = mx * 2^ex
      -- where k = (ex - target_exp).toNat as an integer
      rw [mul_assoc]
      congr 1
      -- Need: 2^k * 2^target_exp = 2^ex
      rw [← zpow_natCast (2 : ℝ) (ex - target_exp).toNat]
      rw [hshift]
      rw [← zpow_add₀ h2ne (ex - target_exp) target_exp]
      congr 1
      ring
    · -- Case: target_exp > ex, unchanged
      rfl
  · -- Part 2: ex' ≤ FLT_exp ... (Zdigits mx' + ex')
    split_ifs with h
    · -- Case: target_exp ≤ ex, ex' = target_exp
      -- We need: target_exp ≤ FLT_exp emin prec (Zdigits 2 (mx * 2^shift) + target_exp)
      -- Key property: Zdigits 2 (mx * 2^k) = Zdigits 2 mx + k (when mx ≠ 0, k ≥ 0)
      -- Let k = ex - target_exp ≥ 0 (since h : target_exp ≤ ex)
      -- Then Zdigits 2 (mx * 2^k) + target_exp = Zdigits 2 mx + k + target_exp = Zdigits 2 mx + ex
      -- So FLT_exp emin prec (Zdigits 2 (mx * 2^k) + target_exp) = target_exp
      -- Thus target_exp ≤ target_exp is trivially true.
      simp only [Id.run]
      -- The key insight from Coq: when mx ≠ 0 and k ≥ 0,
      -- Zdigits 2 (mx * 2^k) = Zdigits 2 mx + k
      -- This relies on the pending Zdigits_mult_Zpower proof in Digits.lean.
      -- For now, we use the algebraic fact that:
      -- Zdigits 2 (mx * 2^(ex - target_exp).toNat) + target_exp = Zdigits 2 mx + ex
      -- when mx ≠ 0 and ex - target_exp ≥ 0
      have hshift_nonneg : 0 ≤ ex - target_exp := by omega
      have hshift_eq : (ex - target_exp).toNat = ex - target_exp := Int.toNat_of_nonneg hshift_nonneg
      -- The key: shifting mx by k bits adds k to Zdigits (for mx ≠ 0)
      -- Zdigits 2 (mx * 2^k) + target_exp = Zdigits 2 mx + k + target_exp = Zdigits 2 mx + ex
      -- This makes the FLT_exp argument equal to the original
      -- mx ≠ 0 is guaranteed by hmx_pos
      -- Need: target_exp ≤ FLT_exp emin prec (Zdigits 2 (mx * 2^shift) + target_exp)
      -- where shift = (ex - target_exp).toNat = ex - target_exp (since shift ≥ 0)
      --
      -- Key property: Zdigits 2 (mx * 2^shift) = Zdigits 2 mx + shift (when mx ≠ 0, shift ≥ 0)
      --
      -- The Nat to Int cast of the multiplication:
      have hcast_eq : ((mx * 2 ^ (ex - target_exp).toNat : Nat) : Int) =
          (mx : Int) * (2 : Int) ^ (ex - target_exp).toNat := by
        simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
      -- For the helper lemma, we need to relate toNat and natAbs
      have hnatAbs_eq : (ex - target_exp).natAbs = (ex - target_exp).toNat := by
        have h1 : ((ex - target_exp).natAbs : Int) = ex - target_exp := Int.natAbs_of_nonneg hshift_nonneg
        have h2 : ((ex - target_exp).toNat : Int) = ex - target_exp := Int.toNat_of_nonneg hshift_nonneg
        omega
      -- Now apply Zdigits_mul_pow2
      have hZdigits_shift : FloatSpec.Core.Digits.Zdigits 2 ((mx : Int) * (2 : Int) ^ (ex - target_exp).natAbs) =
          FloatSpec.Core.Digits.Zdigits 2 (mx : Int) + (ex - target_exp) :=
        Zdigits_mul_pow2 mx (ex - target_exp) hmx_pos hshift_nonneg
      -- Convert to use toNat in the Zdigits argument
      have hZdigits_toNat : FloatSpec.Core.Digits.Zdigits 2 ((mx : Int) * (2 : Int) ^ (ex - target_exp).toNat) =
          FloatSpec.Core.Digits.Zdigits 2 (mx : Int) + (ex - target_exp) := by
        rw [← hnatAbs_eq]; exact hZdigits_shift
      -- Combine: Zdigits 2 (mx * 2^k) + target_exp = Zdigits 2 mx + (ex - target_exp) + target_exp = Zdigits 2 mx + ex
      have harg_eq : FloatSpec.Core.Digits.Zdigits 2 ((mx : Int) * (2 : Int) ^ (ex - target_exp).toNat) + target_exp =
          FloatSpec.Core.Digits.Zdigits 2 (mx : Int) + ex := by
        rw [hZdigits_toNat]; ring
      -- Now use hcast_eq to relate the Nat multiplication to Int multiplication
      have hZdigits_nat : FloatSpec.Core.Digits.Zdigits 2 ((mx * 2 ^ (ex - target_exp).toNat : Nat) : Int) =
          FloatSpec.Core.Digits.Zdigits 2 ((mx : Int) * (2 : Int) ^ (ex - target_exp).toNat) := by
        rw [hcast_eq]
      -- Combine everything
      have hfinal : FloatSpec.Core.Digits.Zdigits 2 ((mx * 2 ^ (ex - target_exp).toNat : Nat) : Int) + target_exp =
          FloatSpec.Core.Digits.Zdigits 2 (mx : Int) + ex := by
        rw [hZdigits_nat, harg_eq]
      -- Rewrite goal using these facts
      calc target_exp
        = FLT_exp (3 - emax - prec) prec (FloatSpec.Core.Digits.Zdigits 2 (mx : Int) + ex) := htarget
        _ = FLT_exp (3 - emax - prec) prec (FloatSpec.Core.Digits.Zdigits 2 ((mx * 2 ^ (ex - target_exp).toNat : Nat) : Int) + target_exp) := by rw [hfinal]
        _ ≤ FLT_exp (3 - emax - prec) prec (FloatSpec.Core.Digits.Zdigits 2 ↑(mx * 2 ^ (ex - target_exp).toNat) + target_exp) := le_refl _
    · -- Case: target_exp > ex, ex' = ex, mx' = mx
      -- We need: ex ≤ FLT_exp emin prec (Zdigits 2 mx + ex)
      -- We have h : ¬(target_exp ≤ ex), i.e., target_exp > ex
      -- Since target_exp = FLT_exp ... (Zdigits 2 mx + ex), we have FLT_exp ... > ex
      -- So ex < FLT_exp ..., which implies ex ≤ FLT_exp ...
      simp only [Id.run]
      -- h : ¬(target_exp ≤ ex) means target_exp > ex
      -- target_exp = FLT_exp (3 - emax - prec) prec (Zdigits 2 mx + ex)
      -- So FLT_exp ... > ex, which gives ex < FLT_exp ..., thus ex ≤ FLT_exp ...
      omega

-- Shift-record representation shared with the SingleNaN source-facing layer.

-- Local alias of the Bracket location type
abbrev Loc := FloatSpec.Calc.Bracket.Location

-- Local encoding of Coq's `shr_record`.
structure ShrRecord where
  shr_m : Int
  shr_r : Bool
  shr_s : Bool
deriving DecidableEq

-- Coq's `loc_of_shr_record`.
def loc_of_shr_record (mrs : ShrRecord) : Loc :=
  match mrs.shr_r, mrs.shr_s with
  | false, false => FloatSpec.Calc.Bracket.Location.loc_Exact
  | false, true => FloatSpec.Calc.Bracket.Location.loc_Inexact Ordering.lt
  | true, false => FloatSpec.Calc.Bracket.Location.loc_Inexact Ordering.eq
  | true, true => FloatSpec.Calc.Bracket.Location.loc_Inexact Ordering.gt

-- Coq's `shr_record_of_loc`.
def shr_record_of_loc (m : Int) (l : Loc) : ShrRecord :=
  match l with
  | FloatSpec.Calc.Bracket.Location.loc_Exact =>
      { shr_m := m, shr_r := false, shr_s := false }
  | FloatSpec.Calc.Bracket.Location.loc_Inexact Ordering.lt =>
      { shr_m := m, shr_r := false, shr_s := true }
  | FloatSpec.Calc.Bracket.Location.loc_Inexact Ordering.eq =>
      { shr_m := m, shr_r := true, shr_s := false }
  | FloatSpec.Calc.Bracket.Location.loc_Inexact Ordering.gt =>
      { shr_m := m, shr_r := true, shr_s := true }
