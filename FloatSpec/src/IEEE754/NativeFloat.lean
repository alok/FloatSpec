import FloatSpec.src.IEEE754.LeanFloat
import FloatSpec.src.IEEE754.BinarySingleNaNSourceFacade
import FloatSpec.src.Prop.Relative

/-!
# Correct rounding of Lean's native `Float` and `Float32`

Lean core gives `Float` (IEEE 754 binary64) and `Float32` (binary32) a logical
model: `x + y` is `Float.ofModel (x.toModel + y.toModel)`, and likewise for
`-`, `*`, `/` and `Float.sqrt`.

This module composes two existing pieces of FloatSpec:

* Hantao Lou's bridge from Lean's `Float.Model` and `Float32.Model` to Flocq's
  single-NaN binary floats (`FloatSpec.IEEE754.LeanFloat` and the
  `FloatSpec.IEEE754.Native` adapters it re-exports). It proves, for example,
  `model64OfBinarySingleNaNFloat_Bplus_RNE`: the model addition of two encoded
  values is the encoding of Flocq's `Bplus` in round-to-nearest-even.
* The source-facing ports of Flocq's `Bplus_correct`, `Bminus_correct`,
  `Bmult_correct`, `Bdiv_correct` and `Bsqrt_correct`, namely
  `FloatSpec.IEEE754.BinarySingleNaN.Source.Bplus_correct` and its siblings in
  `BinarySingleNaNSourceFacade.lean`. They restate, over Coq's `mode` and
  `round_mode`, the proofs `BinarySingleNaN.Bplus_correct` and so on in
  `BinarySingleNaN.lean`. The root-level `Bplus_correct` and its siblings are
  the `Binary.v` versions with NaN payloads and are not used here.

Each theorem below is about a native operator. Its statement is Flocq's, with
every binary float replaced by `toBinary` of a native float:

* `add_correct`, `sub_correct`, `mul_correct`, `div_correct` and `sqrt_correct`
  restate Flocq's `B*_correct` in full, including the overflow branch and the
  sign and finiteness conjuncts, with the same premises.
* `add_eq_round` and its siblings specialize them to the no-overflow case, with
  Flocq's `Rlt_bool |round (exact result)| (bpow 2 1024)` written as a plain
  inequality. `round_abs_lt_of_abs_le` discharges that hypothesis whenever the
  exact result is at most the largest finite value in magnitude.
* `add_standard_model` and its siblings combine this with Flocq's `error_N_FLT`.
  The result is the standard model of floating-point arithmetic with underflow:
  `toReal (x + y) = (toReal x + toReal y) * (1 + ε) + η` with
  `|ε| ≤ 2 ^ (-53)`, `|η| ≤ 2 ^ (-1075)` and `ε * η = 0`.

`toReal` is Flocq's `B2R`, which sends infinities and NaN to `0`.
`FloatSpec.IEEE754.NativeFloat32` gives the same theorems for `Float32`, with
precision 24 and `emax = 128`: exponent function `FLT_exp (-149) 24`, overflow
bound `2 ^ 128`, `|ε| ≤ 2 ^ (-24)` and `|η| ≤ 2 ^ (-150)`.
-/

open FloatSpec.IEEE754.BinarySingleNaN.Source (mode round_mode)

namespace FloatSpec.IEEE754.NativeFloat

/-! ## Helpers shared by both formats -/

/-- `(1 / 2) * 2 ^ e = 2 ^ (e - 1)`, with the radix cast from `Int` as in
`error_N_FLT`. -/
theorem half_mul_two_zpow (e : ℤ) : (1 / 2 : ℝ) * ((2 : ℤ) : ℝ) ^ e = (2 : ℝ) ^ (e - 1) := by
  rw [zpow_sub₀ (two_ne_zero' ℝ), zpow_one]
  push_cast
  ring

/-- `Rlt_bool a (bpow 2 e)` from the plain inequality. -/
theorem rlt_bool_bpow_of_lt {a : ℝ} {e : ℤ} (h : a < (2 : ℝ) ^ e) :
    FloatSpec.Core.Raux.Rlt_bool a (FloatSpec.Core.Raux.bpow 2 e) = true := by
  simpa [FloatSpec.Core.Raux.Rlt_bool, FloatSpec.Core.Raux.bpow] using h

/-! ## binary64: `Float` -/

-- Flocq's binary64 section hypotheses, kept local as in `PrimFloat.lean`.
local instance : Prec_gt_0 (53 : Int) := FaithfulPrimFloat.Hprec
local instance : Prec_lt_emax (53 : Int) 1024 := FaithfulPrimFloat.Hmax

/-! ### Reading a native `Float` as a Flocq binary64 value -/

/-- The Flocq binary64 value of a native `Float`, in Flocq's single-NaN carrier
`BinarySingleNaNFloat 53 1024`. It decodes the IEEE fields of `x.toModel` with
`Native.standardFloatOfModel64` and attaches the binary64 validity proof. -/
def toBinary (x : Float) : BinarySingleNaNFloat 53 1024 :=
  standardFloatToBinarySingleNaNFloat (Native.standardFloatOfModel64 x.toModel)
    (Native.validStandardFloatOfModel64 x.toModel)

/-- Encode a Flocq binary64 value as a native `Float`; the inverse of
`toBinary`. -/
def ofBinary (z : BinarySingleNaNFloat 53 1024) : Float :=
  Float.ofModel (Native.model64OfBinarySingleNaNFloat z)

/-- The real number a native `Float` denotes: Flocq's `B2R` of `toBinary x`.
As in Flocq, infinities and NaN are sent to `0`. -/
noncomputable def toReal (x : Float) : ℝ :=
  BinarySingleNaN.B2R (toBinary x)

/-- Flocq's `Bsign` of `toBinary x`. It is the IEEE sign bit of a zero, an
infinity or a finite value. NaN has no sign in Flocq's single-NaN model, and
there it is `false`. -/
def signBit (x : Float) : Bool :=
  BinarySingleNaN.Bsign (toBinary x)

/-- Flocq's `StandardFloat` view of a native `Float`, `B2SF (toBinary x)`. It
equals `Native.standardFloatOfModel64 x.toModel` (`toStandardFloat_eq`). -/
def toStandardFloat (x : Float) : StandardFloat :=
  BinarySingleNaN.B2SF (toBinary x)

theorem ext_toModel {x y : Float} (h : x.toModel = y.toModel) : x = y := by
  cases x
  cases y
  cases h
  rfl

@[simp] theorem toModel_ofBinary (z : BinarySingleNaNFloat 53 1024) :
    (ofBinary z).toModel = Native.model64OfBinarySingleNaNFloat z :=
  rfl

@[simp] theorem model64OfBinarySingleNaNFloat_toBinary (x : Float) :
    Native.model64OfBinarySingleNaNFloat (toBinary x) = x.toModel := by
  rw [toBinary, Native.model64OfBinarySingleNaNFloat_standardFloatToBinarySingleNaNFloat,
    Native.model64OfStandardFloat_standardFloatOfModel64]

@[simp] theorem ofBinary_toBinary (x : Float) : ofBinary (toBinary x) = x :=
  ext_toModel (model64OfBinarySingleNaNFloat_toBinary x)

theorem toStandardFloat_eq (x : Float) :
    toStandardFloat x = Native.standardFloatOfModel64 x.toModel :=
  binarySingleNaNFloatToStandardFloat_standardFloatToBinarySingleNaNFloat _ _

@[simp] theorem toBinary_ofBinary (z : BinarySingleNaNFloat 53 1024) :
    toBinary (ofBinary z) = z := by
  apply BinarySingleNaN.B2SF_inj
  change toStandardFloat (ofBinary z) = _
  rw [toStandardFloat_eq, toModel_ofBinary,
    Native.model64OfBinarySingleNaNFloat_eq_model64OfStandardFloat,
    Native.standardFloatOfModel64_model64OfStandardFloat _
      (validBinarySingleNaNStandardFloat_binarySingleNaNFloatToStandardFloat z)]

/-- Native binary64 floats and Flocq's single-NaN binary64 floats are in
bijection. -/
def binaryEquiv : Float ≃ BinarySingleNaNFloat 53 1024 where
  toFun := toBinary
  invFun := ofBinary
  left_inv := ofBinary_toBinary
  right_inv := toBinary_ofBinary

theorem toBinary_injective : Function.Injective toBinary :=
  binaryEquiv.injective

theorem toBinary_eq_iff {x : Float} {z : BinarySingleNaNFloat 53 1024} :
    toBinary x = z ↔ x = ofBinary z :=
  ⟨fun h => by rw [← h, ofBinary_toBinary], fun h => by rw [h, toBinary_ofBinary]⟩

/-- `toBinary` agrees with the primitive-float path
`Prim2B (PrimitiveFloat.ofFloat x)` of `PrimFloat.lean`. -/
theorem toBinary_eq_Prim2B (x : Float) :
    toBinary x = FaithfulPrimFloat.Prim2B (FaithfulPrimFloat.PrimitiveFloat.ofFloat x) := by
  apply BinarySingleNaN.B2SF_inj
  change toStandardFloat x = FaithfulPrimFloat.B2SF _
  rw [toStandardFloat_eq, FaithfulPrimFloat.B2SF_Prim2B]
  simp [FaithfulPrimFloat.PrimitiveFloat.ofFloat]

/-- `toReal` through Flocq's `SF2R` of the decoded `StandardFloat`. -/
theorem toReal_eq_SF2R (x : Float) : toReal x = SF2R 2 (toStandardFloat x) :=
  (BinarySingleNaN.SF2R_B2SF (toBinary x)).symm

theorem isFinite_eq (x : Float) :
    x.isFinite = BinarySingleNaN.is_finite (toBinary x) := by
  change x.toModel.isFinite = _
  rw [← model64OfBinarySingleNaNFloat_toBinary x,
    Native.model64OfBinarySingleNaNFloat_eq_model64OfStandardFloat,
    Native.model64OfStandardFloat_isFinite _
      (validBinarySingleNaNStandardFloat_binarySingleNaNFloatToStandardFloat _)]
  exact BinarySingleNaN.is_finite_SF_B2SF _

theorem isNaN_eq (x : Float) :
    x.isNaN = BinarySingleNaN.is_nan (toBinary x) := by
  change x.toModel.isNaN = _
  rw [← model64OfBinarySingleNaNFloat_toBinary x,
    Native.model64OfBinarySingleNaNFloat_eq_model64OfStandardFloat,
    Native.model64OfStandardFloat_isNaN _
      (validBinarySingleNaNStandardFloat_binarySingleNaNFloatToStandardFloat _)]
  exact BinarySingleNaN.is_nan_SF_B2SF _

/-! ### Native operations are Flocq's round-to-nearest-even operations -/

theorem toBinary_add (x y : Float) :
    toBinary (x + y) =
      FloatSpec.IEEE754.BinarySingleNaN.Source.Bplus mode.mode_NE
        (toBinary x) (toBinary y) := by
  rw [toBinary_eq_iff]
  apply ext_toModel
  rw [toModel_ofBinary]
  change Float.Model.add x.toModel y.toModel = _
  rw [← model64OfBinarySingleNaNFloat_toBinary x, ← model64OfBinarySingleNaNFloat_toBinary y]
  exact (LeanFloat.model64OfBinarySingleNaNFloat_Bplus_RNE _ _).symm

theorem toBinary_sub (x y : Float) :
    toBinary (x - y) =
      FloatSpec.IEEE754.BinarySingleNaN.Source.Bminus mode.mode_NE
        (toBinary x) (toBinary y) := by
  rw [toBinary_eq_iff]
  apply ext_toModel
  rw [toModel_ofBinary]
  change Float.Model.sub x.toModel y.toModel = _
  rw [← model64OfBinarySingleNaNFloat_toBinary x, ← model64OfBinarySingleNaNFloat_toBinary y]
  exact (LeanFloat.model64OfBinarySingleNaNFloat_Bminus_RNE _ _).symm

theorem toBinary_mul (x y : Float) :
    toBinary (x * y) =
      FloatSpec.IEEE754.BinarySingleNaN.Source.Bmult mode.mode_NE
        (toBinary x) (toBinary y) := by
  rw [toBinary_eq_iff]
  apply ext_toModel
  rw [toModel_ofBinary]
  change Float.Model.mul x.toModel y.toModel = _
  rw [← model64OfBinarySingleNaNFloat_toBinary x, ← model64OfBinarySingleNaNFloat_toBinary y]
  exact (LeanFloat.model64OfBinarySingleNaNFloat_Bmult_RNE _ _).symm

theorem toBinary_div (x y : Float) :
    toBinary (x / y) =
      FloatSpec.IEEE754.BinarySingleNaN.Source.Bdiv mode.mode_NE
        (toBinary x) (toBinary y) := by
  rw [toBinary_eq_iff]
  apply ext_toModel
  rw [toModel_ofBinary]
  change Float.Model.div x.toModel y.toModel = _
  rw [← model64OfBinarySingleNaNFloat_toBinary x, ← model64OfBinarySingleNaNFloat_toBinary y]
  exact (LeanFloat.model64OfBinarySingleNaNFloat_Bdiv_RNE _ _).symm

theorem toBinary_sqrt (x : Float) :
    toBinary x.sqrt =
      FloatSpec.IEEE754.BinarySingleNaN.Source.Bsqrt mode.mode_NE (toBinary x) := by
  rw [toBinary_eq_iff]
  apply ext_toModel
  rw [toModel_ofBinary]
  change Float.Model.sqrt x.toModel = _
  rw [← model64OfBinarySingleNaNFloat_toBinary x]
  exact (LeanFloat.model64OfBinarySingleNaNFloat_Bsqrt_RNE _).symm

/-! ### Flocq's correctness theorems for the native operators

Each statement is the corresponding Flocq theorem at `prec = 53`,
`emax = 1024` and mode `mode_NE`, read through `toBinary`. Flocq's exponent
function `FLT_exp (3 - emax - prec) prec` is written `FLT_exp (-1074) 53`. -/

/-- Flocq's `Bplus_correct` for native `Float` addition. -/
theorem add_correct (x y : Float) (hx : x.isFinite = true) (hy : y.isFinite = true) :
    if FloatSpec.Core.Raux.Rlt_bool
        |FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp (-1074) 53) (round_mode .mode_NE)
          (toReal x + toReal y)|
        (FloatSpec.Core.Raux.bpow 2 1024) then
      toReal (x + y) =
          FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp (-1074) 53) (round_mode .mode_NE)
            (toReal x + toReal y) ∧
        (x + y).isFinite = true ∧
        signBit (x + y) =
          binaryPlusResultSign .RNE (signBit x) (signBit y) (toReal x + toReal y)
    else
      toStandardFloat (x + y) = bsn_binary_overflow 53 1024 .RNE (signBit x) ∧
        signBit x = signBit y := by
  rw [isFinite_eq] at hx hy
  simp only [isFinite_eq, toReal, signBit, toStandardFloat, toBinary_add]
  exact FloatSpec.IEEE754.BinarySingleNaN.Source.Bplus_correct mode.mode_NE
    (toBinary x) (toBinary y) hx hy

/-- Flocq's `Bminus_correct` for native `Float` subtraction. -/
theorem sub_correct (x y : Float) (hx : x.isFinite = true) (hy : y.isFinite = true) :
    if FloatSpec.Core.Raux.Rlt_bool
        |FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp (-1074) 53) (round_mode .mode_NE)
          (toReal x - toReal y)|
        (FloatSpec.Core.Raux.bpow 2 1024) then
      toReal (x - y) =
          FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp (-1074) 53) (round_mode .mode_NE)
            (toReal x - toReal y) ∧
        (x - y).isFinite = true ∧
        signBit (x - y) =
          binaryMinusResultSign .RNE (signBit x) (signBit y) (toReal x - toReal y)
    else
      toStandardFloat (x - y) = bsn_binary_overflow 53 1024 .RNE (signBit x) ∧
        signBit x = !(signBit y) := by
  rw [isFinite_eq] at hx hy
  simp only [isFinite_eq, toReal, signBit, toStandardFloat, toBinary_sub]
  exact FloatSpec.IEEE754.BinarySingleNaN.Source.Bminus_correct mode.mode_NE
    (toBinary x) (toBinary y) hx hy

/-- Flocq's `Bmult_correct` for native `Float` multiplication. Like Flocq's, it
has no finiteness premise. -/
theorem mul_correct (x y : Float) :
    if FloatSpec.Core.Raux.Rlt_bool
        |FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp (-1074) 53) (round_mode .mode_NE)
          (toReal x * toReal y)|
        (FloatSpec.Core.Raux.bpow 2 1024) then
      toReal (x * y) =
          FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp (-1074) 53) (round_mode .mode_NE)
            (toReal x * toReal y) ∧
        (x * y).isFinite = (x.isFinite && y.isFinite) ∧
        ((x * y).isNaN = false → signBit (x * y) = Bool.xor (signBit x) (signBit y))
    else
      toStandardFloat (x * y) =
        bsn_binary_overflow 53 1024 .RNE (Bool.xor (signBit x) (signBit y)) := by
  simp only [isFinite_eq, isNaN_eq, toReal, signBit, toStandardFloat, toBinary_mul]
  exact FloatSpec.IEEE754.BinarySingleNaN.Source.Bmult_correct mode.mode_NE
    (toBinary x) (toBinary y)

/-- Flocq's `Bdiv_correct` for native `Float` division. As in Flocq, the
premise is that the divisor is nonzero as a real number. -/
theorem div_correct (x y : Float) (hy : toReal y ≠ 0) :
    if FloatSpec.Core.Raux.Rlt_bool
        |FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp (-1074) 53) (round_mode .mode_NE)
          (toReal x / toReal y)|
        (FloatSpec.Core.Raux.bpow 2 1024) then
      toReal (x / y) =
          FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp (-1074) 53) (round_mode .mode_NE)
            (toReal x / toReal y) ∧
        (x / y).isFinite = x.isFinite ∧
        ((x / y).isNaN = false → signBit (x / y) = Bool.xor (signBit x) (signBit y))
    else
      toStandardFloat (x / y) =
        bsn_binary_overflow 53 1024 .RNE (Bool.xor (signBit x) (signBit y)) := by
  simp only [isFinite_eq, isNaN_eq, toReal, signBit, toStandardFloat, toBinary_div]
  exact FloatSpec.IEEE754.BinarySingleNaN.Source.Bdiv_correct mode.mode_NE
    (toBinary x) (toBinary y) hy

/-- Flocq's `Bsqrt_correct` for native `Float.sqrt`. Like Flocq's, it has no
premise: a square root never overflows. -/
theorem sqrt_correct (x : Float) :
    toReal x.sqrt =
        FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp (-1074) 53) (round_mode .mode_NE)
          (Real.sqrt (toReal x)) ∧
      x.sqrt.isFinite =
        (match toBinary x with
        | BinarySingleNaNFloat.B754_zero _ => true
        | BinarySingleNaNFloat.B754_finite false _ _ _ _ => true
        | _ => false) ∧
      (x.sqrt.isNaN = false → signBit x.sqrt = signBit x) := by
  simp only [isFinite_eq, isNaN_eq, toReal, signBit, toBinary_sqrt]
  obtain ⟨hvalue, hfinite, hsign⟩ :=
    FloatSpec.IEEE754.BinarySingleNaN.Source.Bsqrt_correct mode.mode_NE (toBinary x)
  refine ⟨hvalue, ?_, hsign⟩
  rw [hfinite]
  generalize toBinary x = z
  rcases z with _ | _ | _ | ⟨_ | _, _, _, _, _⟩ <;> rfl

/-! ### The no-overflow case -/

/-- A sufficient condition for Flocq's no-overflow hypothesis: an exact result
that is at most the largest finite binary64 value, `(2 ^ 53 - 1) * 2 ^ 971`, in
magnitude rounds to a value below `2 ^ 1024` in magnitude. -/
theorem round_abs_lt_of_abs_le {r : ℝ} (h : |r| ≤ (2 ^ 53 - 1) * 2 ^ (971 : ℤ)) :
    |FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp (-1074) 53) (round_mode .mode_NE) r| <
      2 ^ (1024 : ℤ) := by
  have hfmt : FloatSpec.Core.Generic_fmt.generic_format 2 (FLT_exp (-1074) 53)
      ((2 ^ 53 - 1) * 2 ^ (971 : ℤ)) := by
    apply FloatSpec.Core.FLT.generic_format_FLT
    refine ⟨⟨2 ^ 53 - 1, 971⟩, ?_, ?_, ?_⟩
    · norm_num [FloatSpec.Core.Defs.F2R]
    · decide
    · decide
  have hle := FloatSpec.Core.Generic_fmt.abs_round_le_generic 2 (FLT_exp (-1074) 53)
    (round_mode .mode_NE) hfmt h
  refine lt_of_le_of_lt hle ?_
  rw [show (1024 : ℤ) = 53 + 971 by norm_num, zpow_add₀ (two_ne_zero' ℝ)]
  exact mul_lt_mul_of_pos_right (by norm_num) (zpow_pos (by norm_num) _)

/-- Native `Float` addition is correctly rounded when it does not overflow. -/
theorem add_eq_round (x y : Float) (hx : x.isFinite = true) (hy : y.isFinite = true)
    (hno : |FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp (-1074) 53) (round_mode .mode_NE)
      (toReal x + toReal y)| < 2 ^ (1024 : ℤ)) :
    toReal (x + y) =
        FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp (-1074) 53) (round_mode .mode_NE)
          (toReal x + toReal y) ∧
      (x + y).isFinite = true := by
  have h := add_correct x y hx hy
  rw [ite_eq_left (rlt_bool_bpow_of_lt hno)] at h
  exact ⟨h.1, h.2.1⟩

/-- Native `Float` subtraction is correctly rounded when it does not overflow. -/
theorem sub_eq_round (x y : Float) (hx : x.isFinite = true) (hy : y.isFinite = true)
    (hno : |FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp (-1074) 53) (round_mode .mode_NE)
      (toReal x - toReal y)| < 2 ^ (1024 : ℤ)) :
    toReal (x - y) =
        FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp (-1074) 53) (round_mode .mode_NE)
          (toReal x - toReal y) ∧
      (x - y).isFinite = true := by
  have h := sub_correct x y hx hy
  rw [ite_eq_left (rlt_bool_bpow_of_lt hno)] at h
  exact ⟨h.1, h.2.1⟩

/-- Native `Float` multiplication is correctly rounded when it does not
overflow. -/
theorem mul_eq_round (x y : Float)
    (hno : |FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp (-1074) 53) (round_mode .mode_NE)
      (toReal x * toReal y)| < 2 ^ (1024 : ℤ)) :
    toReal (x * y) =
        FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp (-1074) 53) (round_mode .mode_NE)
          (toReal x * toReal y) ∧
      (x * y).isFinite = (x.isFinite && y.isFinite) := by
  have h := mul_correct x y
  rw [ite_eq_left (rlt_bool_bpow_of_lt hno)] at h
  exact ⟨h.1, h.2.1⟩

/-- Native `Float` division by a nonzero value is correctly rounded when it does
not overflow. -/
theorem div_eq_round (x y : Float) (hy : toReal y ≠ 0)
    (hno : |FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp (-1074) 53) (round_mode .mode_NE)
      (toReal x / toReal y)| < 2 ^ (1024 : ℤ)) :
    toReal (x / y) =
        FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp (-1074) 53) (round_mode .mode_NE)
          (toReal x / toReal y) ∧
      (x / y).isFinite = x.isFinite := by
  have h := div_correct x y hy
  rw [ite_eq_left (rlt_bool_bpow_of_lt hno)] at h
  exact ⟨h.1, h.2.1⟩

/-- Native `Float.sqrt` is correctly rounded. -/
theorem sqrt_eq_round (x : Float) :
    toReal x.sqrt =
      FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp (-1074) 53) (round_mode .mode_NE)
        (Real.sqrt (toReal x)) :=
  (sqrt_correct x).1

/-- The square root of a finite, nonnegative native `Float` (including `-0`) is
finite. -/
theorem sqrt_isFinite_of_nonneg (x : Float) (hx : x.isFinite = true) (h0 : 0 ≤ toReal x) :
    x.sqrt.isFinite = true := by
  rw [(sqrt_correct x).2.1]
  rw [isFinite_eq] at hx
  unfold toReal at h0
  generalize toBinary x = z at hx h0
  cases z with
  | B754_zero s => rfl
  | B754_infinity s => simp [BinarySingleNaN.is_finite, binarySingleNaNFloatToB754,
      BSN_is_finite] at hx
  | B754_nan => simp [BinarySingleNaN.is_finite, binarySingleNaNFloatToB754,
      BSN_is_finite] at hx
  | B754_finite s m e hm hb =>
      cases s
      · rfl
      · exfalso
        have hneg : (-(m : ℝ)) * (2 : ℝ) ^ e < 0 :=
          mul_neg_of_neg_of_pos (by exact_mod_cast Int.neg_neg_of_pos (by exact_mod_cast hm))
            (zpow_pos (by norm_num) _)
        simp [BinarySingleNaN.B2R, binarySingleNaNFloatToB754, B754_to_R] at h0
        linarith

/-! ### The standard model -/

/-- Flocq's `error_N_FLT` for binary64 round-to-nearest-even: at radix 2,
`emin = -1074` and precision 53, `|ε| ≤ 1/2 * 2 ^ (1 - 53) = 2 ^ (-53)` and
`|η| ≤ 1/2 * 2 ^ (-1074) = 2 ^ (-1075)`. -/
theorem round_standard_model (r : ℝ) :
    ∃ ε η : ℝ, |ε| ≤ 2 ^ (-53 : ℤ) ∧ |η| ≤ 2 ^ (-1075 : ℤ) ∧ ε * η = 0 ∧
      FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp (-1074) 53) (round_mode .mode_NE) r =
        r * (1 + ε) + η := by
  obtain ⟨ε, η, hε, hη, hεη, h⟩ :=
    error_N_FLT 2 (-1074) 53 (by norm_num) (by norm_num) (fun t : Int => !(decide (2 ∣ t))) r
  refine ⟨ε, η, ?_, ?_, hεη, h⟩
  · calc |ε| ≤ _ := hε
      _ = 2 ^ (-53 : ℤ) := by rw [half_mul_two_zpow]; norm_num
  · calc |η| ≤ _ := hη
      _ = 2 ^ (-1075 : ℤ) := by rw [half_mul_two_zpow]; norm_num

/-- The standard model with underflow for native `Float` addition. -/
theorem add_standard_model (x y : Float) (hx : x.isFinite = true) (hy : y.isFinite = true)
    (hno : |FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp (-1074) 53) (round_mode .mode_NE)
      (toReal x + toReal y)| < 2 ^ (1024 : ℤ)) :
    ∃ ε η : ℝ, |ε| ≤ 2 ^ (-53 : ℤ) ∧ |η| ≤ 2 ^ (-1075 : ℤ) ∧ ε * η = 0 ∧
      toReal (x + y) = (toReal x + toReal y) * (1 + ε) + η := by
  rw [(add_eq_round x y hx hy hno).1]
  exact round_standard_model _

/-- The standard model with underflow for native `Float` subtraction. -/
theorem sub_standard_model (x y : Float) (hx : x.isFinite = true) (hy : y.isFinite = true)
    (hno : |FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp (-1074) 53) (round_mode .mode_NE)
      (toReal x - toReal y)| < 2 ^ (1024 : ℤ)) :
    ∃ ε η : ℝ, |ε| ≤ 2 ^ (-53 : ℤ) ∧ |η| ≤ 2 ^ (-1075 : ℤ) ∧ ε * η = 0 ∧
      toReal (x - y) = (toReal x - toReal y) * (1 + ε) + η := by
  rw [(sub_eq_round x y hx hy hno).1]
  exact round_standard_model _

/-- The standard model with underflow for native `Float` multiplication. -/
theorem mul_standard_model (x y : Float)
    (hno : |FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp (-1074) 53) (round_mode .mode_NE)
      (toReal x * toReal y)| < 2 ^ (1024 : ℤ)) :
    ∃ ε η : ℝ, |ε| ≤ 2 ^ (-53 : ℤ) ∧ |η| ≤ 2 ^ (-1075 : ℤ) ∧ ε * η = 0 ∧
      toReal (x * y) = (toReal x * toReal y) * (1 + ε) + η := by
  rw [(mul_eq_round x y hno).1]
  exact round_standard_model _

/-- The standard model with underflow for native `Float` division. -/
theorem div_standard_model (x y : Float) (hy : toReal y ≠ 0)
    (hno : |FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp (-1074) 53) (round_mode .mode_NE)
      (toReal x / toReal y)| < 2 ^ (1024 : ℤ)) :
    ∃ ε η : ℝ, |ε| ≤ 2 ^ (-53 : ℤ) ∧ |η| ≤ 2 ^ (-1075 : ℤ) ∧ ε * η = 0 ∧
      toReal (x / y) = (toReal x / toReal y) * (1 + ε) + η := by
  rw [(div_eq_round x y hy hno).1]
  exact round_standard_model _

/-- The standard model with underflow for native `Float.sqrt`. -/
theorem sqrt_standard_model (x : Float) :
    ∃ ε η : ℝ, |ε| ≤ 2 ^ (-53 : ℤ) ∧ |η| ≤ 2 ^ (-1075 : ℤ) ∧ ε * η = 0 ∧
      toReal x.sqrt = Real.sqrt (toReal x) * (1 + ε) + η := by
  rw [sqrt_eq_round]
  exact round_standard_model _

end FloatSpec.IEEE754.NativeFloat

/-! ## binary32: `Float32` -/

namespace FloatSpec.IEEE754.NativeFloat32

open FloatSpec.IEEE754.NativeFloat (half_mul_two_zpow rlt_bool_bpow_of_lt)

-- Flocq's binary32 section hypotheses, kept local as in `PrimFloat.lean`.
local instance : Prec_gt_0 (24 : Int) := ⟨by norm_num⟩
local instance : Prec_lt_emax (24 : Int) 128 := ⟨by norm_num⟩

/-! ### Reading a native `Float32` as a Flocq binary32 value -/

/-- The Flocq binary32 value of a native `Float32`, in Flocq's single-NaN carrier
`BinarySingleNaNFloat 24 128`. It decodes the IEEE fields of `x.toModel` with
`Native.standardFloatOfModel32` and attaches the binary32 validity proof. -/
def toBinary (x : Float32) : BinarySingleNaNFloat 24 128 :=
  standardFloatToBinarySingleNaNFloat (Native.standardFloatOfModel32 x.toModel)
    (Native.validStandardFloatOfModel32 x.toModel)

/-- Encode a Flocq binary32 value as a native `Float32`; the inverse of
`toBinary`. -/
def ofBinary (z : BinarySingleNaNFloat 24 128) : Float32 :=
  Float32.ofModel (Native.model32OfBinarySingleNaNFloat z)

/-- The real number a native `Float32` denotes: Flocq's `B2R` of `toBinary x`.
As in Flocq, infinities and NaN are sent to `0`. -/
noncomputable def toReal (x : Float32) : ℝ :=
  BinarySingleNaN.B2R (toBinary x)

/-- Flocq's `Bsign` of `toBinary x`. It is the IEEE sign bit of a zero, an
infinity or a finite value. NaN has no sign in Flocq's single-NaN model, and
there it is `false`. -/
def signBit (x : Float32) : Bool :=
  BinarySingleNaN.Bsign (toBinary x)

/-- Flocq's `StandardFloat` view of a native `Float32`, `B2SF (toBinary x)`. It
equals `Native.standardFloatOfModel32 x.toModel` (`toStandardFloat_eq`). -/
def toStandardFloat (x : Float32) : StandardFloat :=
  BinarySingleNaN.B2SF (toBinary x)

theorem ext_toModel {x y : Float32} (h : x.toModel = y.toModel) : x = y := by
  cases x
  cases y
  cases h
  rfl

@[simp] theorem toModel_ofBinary (z : BinarySingleNaNFloat 24 128) :
    (ofBinary z).toModel = Native.model32OfBinarySingleNaNFloat z :=
  rfl

@[simp] theorem model32OfBinarySingleNaNFloat_toBinary (x : Float32) :
    Native.model32OfBinarySingleNaNFloat (toBinary x) = x.toModel := by
  rw [toBinary, Native.model32OfBinarySingleNaNFloat_standardFloatToBinarySingleNaNFloat,
    Native.model32OfStandardFloat_standardFloatOfModel32]

@[simp] theorem ofBinary_toBinary (x : Float32) : ofBinary (toBinary x) = x :=
  ext_toModel (model32OfBinarySingleNaNFloat_toBinary x)

theorem toStandardFloat_eq (x : Float32) :
    toStandardFloat x = Native.standardFloatOfModel32 x.toModel :=
  binarySingleNaNFloatToStandardFloat_standardFloatToBinarySingleNaNFloat _ _

@[simp] theorem toBinary_ofBinary (z : BinarySingleNaNFloat 24 128) :
    toBinary (ofBinary z) = z := by
  apply BinarySingleNaN.B2SF_inj
  change toStandardFloat (ofBinary z) = _
  rw [toStandardFloat_eq, toModel_ofBinary,
    Native.model32OfBinarySingleNaNFloat_eq_model32OfStandardFloat,
    Native.standardFloatOfModel32_model32OfStandardFloat _
      (validBinarySingleNaNStandardFloat_binarySingleNaNFloatToStandardFloat z)]

/-- Native binary32 floats and Flocq's single-NaN binary32 floats are in
bijection. -/
def binaryEquiv : Float32 ≃ BinarySingleNaNFloat 24 128 where
  toFun := toBinary
  invFun := ofBinary
  left_inv := ofBinary_toBinary
  right_inv := toBinary_ofBinary

theorem toBinary_injective : Function.Injective toBinary :=
  binaryEquiv.injective

theorem toBinary_eq_iff {x : Float32} {z : BinarySingleNaNFloat 24 128} :
    toBinary x = z ↔ x = ofBinary z :=
  ⟨fun h => by rw [← h, ofBinary_toBinary], fun h => by rw [h, toBinary_ofBinary]⟩

/-- `toReal` through Flocq's `SF2R` of the decoded `StandardFloat`. -/
theorem toReal_eq_SF2R (x : Float32) : toReal x = SF2R 2 (toStandardFloat x) :=
  (BinarySingleNaN.SF2R_B2SF (toBinary x)).symm

theorem isFinite_eq (x : Float32) :
    x.isFinite = BinarySingleNaN.is_finite (toBinary x) := by
  change x.toModel.isFinite = _
  rw [← model32OfBinarySingleNaNFloat_toBinary x,
    Native.model32OfBinarySingleNaNFloat_eq_model32OfStandardFloat,
    Native.model32OfStandardFloat_isFinite _
      (validBinarySingleNaNStandardFloat_binarySingleNaNFloatToStandardFloat _)]
  exact BinarySingleNaN.is_finite_SF_B2SF _

theorem isNaN_eq (x : Float32) :
    x.isNaN = BinarySingleNaN.is_nan (toBinary x) := by
  change x.toModel.isNaN = _
  rw [← model32OfBinarySingleNaNFloat_toBinary x,
    Native.model32OfBinarySingleNaNFloat_eq_model32OfStandardFloat,
    Native.model32OfStandardFloat_isNaN _
      (validBinarySingleNaNStandardFloat_binarySingleNaNFloatToStandardFloat _)]
  exact BinarySingleNaN.is_nan_SF_B2SF _

/-! ### Native operations are Flocq's round-to-nearest-even operations -/

theorem toBinary_add (x y : Float32) :
    toBinary (x + y) =
      FloatSpec.IEEE754.BinarySingleNaN.Source.Bplus mode.mode_NE
        (toBinary x) (toBinary y) := by
  rw [toBinary_eq_iff]
  apply ext_toModel
  rw [toModel_ofBinary]
  change Float32.Model.add x.toModel y.toModel = _
  rw [← model32OfBinarySingleNaNFloat_toBinary x, ← model32OfBinarySingleNaNFloat_toBinary y]
  exact (LeanFloat.model32OfBinarySingleNaNFloat_Bplus_RNE _ _).symm

theorem toBinary_sub (x y : Float32) :
    toBinary (x - y) =
      FloatSpec.IEEE754.BinarySingleNaN.Source.Bminus mode.mode_NE
        (toBinary x) (toBinary y) := by
  rw [toBinary_eq_iff]
  apply ext_toModel
  rw [toModel_ofBinary]
  change Float32.Model.sub x.toModel y.toModel = _
  rw [← model32OfBinarySingleNaNFloat_toBinary x, ← model32OfBinarySingleNaNFloat_toBinary y]
  exact (LeanFloat.model32OfBinarySingleNaNFloat_Bminus_RNE _ _).symm

theorem toBinary_mul (x y : Float32) :
    toBinary (x * y) =
      FloatSpec.IEEE754.BinarySingleNaN.Source.Bmult mode.mode_NE
        (toBinary x) (toBinary y) := by
  rw [toBinary_eq_iff]
  apply ext_toModel
  rw [toModel_ofBinary]
  change Float32.Model.mul x.toModel y.toModel = _
  rw [← model32OfBinarySingleNaNFloat_toBinary x, ← model32OfBinarySingleNaNFloat_toBinary y]
  exact (LeanFloat.model32OfBinarySingleNaNFloat_Bmult_RNE _ _).symm

theorem toBinary_div (x y : Float32) :
    toBinary (x / y) =
      FloatSpec.IEEE754.BinarySingleNaN.Source.Bdiv mode.mode_NE
        (toBinary x) (toBinary y) := by
  rw [toBinary_eq_iff]
  apply ext_toModel
  rw [toModel_ofBinary]
  change Float32.Model.div x.toModel y.toModel = _
  rw [← model32OfBinarySingleNaNFloat_toBinary x, ← model32OfBinarySingleNaNFloat_toBinary y]
  exact (LeanFloat.model32OfBinarySingleNaNFloat_Bdiv_RNE _ _).symm

theorem toBinary_sqrt (x : Float32) :
    toBinary x.sqrt =
      FloatSpec.IEEE754.BinarySingleNaN.Source.Bsqrt mode.mode_NE (toBinary x) := by
  rw [toBinary_eq_iff]
  apply ext_toModel
  rw [toModel_ofBinary]
  change Float32.Model.sqrt x.toModel = _
  rw [← model32OfBinarySingleNaNFloat_toBinary x]
  exact (LeanFloat.model32OfBinarySingleNaNFloat_Bsqrt_RNE _).symm

/-! ### Flocq's correctness theorems for the native operators

Each statement is the corresponding Flocq theorem at `prec = 24`,
`emax = 128` and mode `mode_NE`, read through `toBinary`. Flocq's exponent
function `FLT_exp (3 - emax - prec) prec` is written `FLT_exp (-149) 24`. -/

/-- Flocq's `Bplus_correct` for native `Float32` addition. -/
theorem add_correct (x y : Float32) (hx : x.isFinite = true) (hy : y.isFinite = true) :
    if FloatSpec.Core.Raux.Rlt_bool
        |FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp (-149) 24) (round_mode .mode_NE)
          (toReal x + toReal y)|
        (FloatSpec.Core.Raux.bpow 2 128) then
      toReal (x + y) =
          FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp (-149) 24) (round_mode .mode_NE)
            (toReal x + toReal y) ∧
        (x + y).isFinite = true ∧
        signBit (x + y) =
          binaryPlusResultSign .RNE (signBit x) (signBit y) (toReal x + toReal y)
    else
      toStandardFloat (x + y) = bsn_binary_overflow 24 128 .RNE (signBit x) ∧
        signBit x = signBit y := by
  rw [isFinite_eq] at hx hy
  simp only [isFinite_eq, toReal, signBit, toStandardFloat, toBinary_add]
  exact FloatSpec.IEEE754.BinarySingleNaN.Source.Bplus_correct mode.mode_NE
    (toBinary x) (toBinary y) hx hy

/-- Flocq's `Bminus_correct` for native `Float32` subtraction. -/
theorem sub_correct (x y : Float32) (hx : x.isFinite = true) (hy : y.isFinite = true) :
    if FloatSpec.Core.Raux.Rlt_bool
        |FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp (-149) 24) (round_mode .mode_NE)
          (toReal x - toReal y)|
        (FloatSpec.Core.Raux.bpow 2 128) then
      toReal (x - y) =
          FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp (-149) 24) (round_mode .mode_NE)
            (toReal x - toReal y) ∧
        (x - y).isFinite = true ∧
        signBit (x - y) =
          binaryMinusResultSign .RNE (signBit x) (signBit y) (toReal x - toReal y)
    else
      toStandardFloat (x - y) = bsn_binary_overflow 24 128 .RNE (signBit x) ∧
        signBit x = !(signBit y) := by
  rw [isFinite_eq] at hx hy
  simp only [isFinite_eq, toReal, signBit, toStandardFloat, toBinary_sub]
  exact FloatSpec.IEEE754.BinarySingleNaN.Source.Bminus_correct mode.mode_NE
    (toBinary x) (toBinary y) hx hy

/-- Flocq's `Bmult_correct` for native `Float32` multiplication. Like Flocq's, it
has no finiteness premise. -/
theorem mul_correct (x y : Float32) :
    if FloatSpec.Core.Raux.Rlt_bool
        |FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp (-149) 24) (round_mode .mode_NE)
          (toReal x * toReal y)|
        (FloatSpec.Core.Raux.bpow 2 128) then
      toReal (x * y) =
          FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp (-149) 24) (round_mode .mode_NE)
            (toReal x * toReal y) ∧
        (x * y).isFinite = (x.isFinite && y.isFinite) ∧
        ((x * y).isNaN = false → signBit (x * y) = Bool.xor (signBit x) (signBit y))
    else
      toStandardFloat (x * y) =
        bsn_binary_overflow 24 128 .RNE (Bool.xor (signBit x) (signBit y)) := by
  simp only [isFinite_eq, isNaN_eq, toReal, signBit, toStandardFloat, toBinary_mul]
  exact FloatSpec.IEEE754.BinarySingleNaN.Source.Bmult_correct mode.mode_NE
    (toBinary x) (toBinary y)

/-- Flocq's `Bdiv_correct` for native `Float32` division. As in Flocq, the
premise is that the divisor is nonzero as a real number. -/
theorem div_correct (x y : Float32) (hy : toReal y ≠ 0) :
    if FloatSpec.Core.Raux.Rlt_bool
        |FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp (-149) 24) (round_mode .mode_NE)
          (toReal x / toReal y)|
        (FloatSpec.Core.Raux.bpow 2 128) then
      toReal (x / y) =
          FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp (-149) 24) (round_mode .mode_NE)
            (toReal x / toReal y) ∧
        (x / y).isFinite = x.isFinite ∧
        ((x / y).isNaN = false → signBit (x / y) = Bool.xor (signBit x) (signBit y))
    else
      toStandardFloat (x / y) =
        bsn_binary_overflow 24 128 .RNE (Bool.xor (signBit x) (signBit y)) := by
  simp only [isFinite_eq, isNaN_eq, toReal, signBit, toStandardFloat, toBinary_div]
  exact FloatSpec.IEEE754.BinarySingleNaN.Source.Bdiv_correct mode.mode_NE
    (toBinary x) (toBinary y) hy

/-- Flocq's `Bsqrt_correct` for native `Float32.sqrt`. Like Flocq's, it has no
premise: a square root never overflows. -/
theorem sqrt_correct (x : Float32) :
    toReal x.sqrt =
        FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp (-149) 24) (round_mode .mode_NE)
          (Real.sqrt (toReal x)) ∧
      x.sqrt.isFinite =
        (match toBinary x with
        | BinarySingleNaNFloat.B754_zero _ => true
        | BinarySingleNaNFloat.B754_finite false _ _ _ _ => true
        | _ => false) ∧
      (x.sqrt.isNaN = false → signBit x.sqrt = signBit x) := by
  simp only [isFinite_eq, isNaN_eq, toReal, signBit, toBinary_sqrt]
  obtain ⟨hvalue, hfinite, hsign⟩ :=
    FloatSpec.IEEE754.BinarySingleNaN.Source.Bsqrt_correct mode.mode_NE (toBinary x)
  refine ⟨hvalue, ?_, hsign⟩
  rw [hfinite]
  generalize toBinary x = z
  rcases z with _ | _ | _ | ⟨_ | _, _, _, _, _⟩ <;> rfl

/-! ### The no-overflow case -/

/-- A sufficient condition for Flocq's no-overflow hypothesis: an exact result
that is at most the largest finite binary32 value, `(2 ^ 24 - 1) * 2 ^ 104`, in
magnitude rounds to a value below `2 ^ 128` in magnitude. -/
theorem round_abs_lt_of_abs_le {r : ℝ} (h : |r| ≤ (2 ^ 24 - 1) * 2 ^ (104 : ℤ)) :
    |FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp (-149) 24) (round_mode .mode_NE) r| <
      2 ^ (128 : ℤ) := by
  have hfmt : FloatSpec.Core.Generic_fmt.generic_format 2 (FLT_exp (-149) 24)
      ((2 ^ 24 - 1) * 2 ^ (104 : ℤ)) := by
    apply FloatSpec.Core.FLT.generic_format_FLT
    refine ⟨⟨2 ^ 24 - 1, 104⟩, ?_, ?_, ?_⟩
    · norm_num [FloatSpec.Core.Defs.F2R]
    · decide
    · decide
  have hle := FloatSpec.Core.Generic_fmt.abs_round_le_generic 2 (FLT_exp (-149) 24)
    (round_mode .mode_NE) hfmt h
  refine lt_of_le_of_lt hle ?_
  rw [show (128 : ℤ) = 24 + 104 by norm_num, zpow_add₀ (two_ne_zero' ℝ)]
  exact mul_lt_mul_of_pos_right (by norm_num) (zpow_pos (by norm_num) _)

/-- Native `Float32` addition is correctly rounded when it does not overflow. -/
theorem add_eq_round (x y : Float32) (hx : x.isFinite = true) (hy : y.isFinite = true)
    (hno : |FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp (-149) 24) (round_mode .mode_NE)
      (toReal x + toReal y)| < 2 ^ (128 : ℤ)) :
    toReal (x + y) =
        FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp (-149) 24) (round_mode .mode_NE)
          (toReal x + toReal y) ∧
      (x + y).isFinite = true := by
  have h := add_correct x y hx hy
  rw [ite_eq_left (rlt_bool_bpow_of_lt hno)] at h
  exact ⟨h.1, h.2.1⟩

/-- Native `Float32` subtraction is correctly rounded when it does not overflow. -/
theorem sub_eq_round (x y : Float32) (hx : x.isFinite = true) (hy : y.isFinite = true)
    (hno : |FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp (-149) 24) (round_mode .mode_NE)
      (toReal x - toReal y)| < 2 ^ (128 : ℤ)) :
    toReal (x - y) =
        FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp (-149) 24) (round_mode .mode_NE)
          (toReal x - toReal y) ∧
      (x - y).isFinite = true := by
  have h := sub_correct x y hx hy
  rw [ite_eq_left (rlt_bool_bpow_of_lt hno)] at h
  exact ⟨h.1, h.2.1⟩

/-- Native `Float32` multiplication is correctly rounded when it does not
overflow. -/
theorem mul_eq_round (x y : Float32)
    (hno : |FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp (-149) 24) (round_mode .mode_NE)
      (toReal x * toReal y)| < 2 ^ (128 : ℤ)) :
    toReal (x * y) =
        FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp (-149) 24) (round_mode .mode_NE)
          (toReal x * toReal y) ∧
      (x * y).isFinite = (x.isFinite && y.isFinite) := by
  have h := mul_correct x y
  rw [ite_eq_left (rlt_bool_bpow_of_lt hno)] at h
  exact ⟨h.1, h.2.1⟩

/-- Native `Float32` division by a nonzero value is correctly rounded when it does
not overflow. -/
theorem div_eq_round (x y : Float32) (hy : toReal y ≠ 0)
    (hno : |FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp (-149) 24) (round_mode .mode_NE)
      (toReal x / toReal y)| < 2 ^ (128 : ℤ)) :
    toReal (x / y) =
        FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp (-149) 24) (round_mode .mode_NE)
          (toReal x / toReal y) ∧
      (x / y).isFinite = x.isFinite := by
  have h := div_correct x y hy
  rw [ite_eq_left (rlt_bool_bpow_of_lt hno)] at h
  exact ⟨h.1, h.2.1⟩

/-- Native `Float32.sqrt` is correctly rounded. -/
theorem sqrt_eq_round (x : Float32) :
    toReal x.sqrt =
      FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp (-149) 24) (round_mode .mode_NE)
        (Real.sqrt (toReal x)) :=
  (sqrt_correct x).1

/-- The square root of a finite, nonnegative native `Float32` (including `-0`) is
finite. -/
theorem sqrt_isFinite_of_nonneg (x : Float32) (hx : x.isFinite = true) (h0 : 0 ≤ toReal x) :
    x.sqrt.isFinite = true := by
  rw [(sqrt_correct x).2.1]
  rw [isFinite_eq] at hx
  unfold toReal at h0
  generalize toBinary x = z at hx h0
  cases z with
  | B754_zero s => rfl
  | B754_infinity s => simp [BinarySingleNaN.is_finite, binarySingleNaNFloatToB754,
      BSN_is_finite] at hx
  | B754_nan => simp [BinarySingleNaN.is_finite, binarySingleNaNFloatToB754,
      BSN_is_finite] at hx
  | B754_finite s m e hm hb =>
      cases s
      · rfl
      · exfalso
        have hneg : (-(m : ℝ)) * (2 : ℝ) ^ e < 0 :=
          mul_neg_of_neg_of_pos (by exact_mod_cast Int.neg_neg_of_pos (by exact_mod_cast hm))
            (zpow_pos (by norm_num) _)
        simp [BinarySingleNaN.B2R, binarySingleNaNFloatToB754, B754_to_R] at h0
        linarith

/-! ### The standard model -/

/-- Flocq's `error_N_FLT` for binary32 round-to-nearest-even: at radix 2,
`emin = -149` and precision 24, `|ε| ≤ 1/2 * 2 ^ (1 - 24) = 2 ^ (-24)` and
`|η| ≤ 1/2 * 2 ^ (-149) = 2 ^ (-150)`. -/
theorem round_standard_model (r : ℝ) :
    ∃ ε η : ℝ, |ε| ≤ 2 ^ (-24 : ℤ) ∧ |η| ≤ 2 ^ (-150 : ℤ) ∧ ε * η = 0 ∧
      FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp (-149) 24) (round_mode .mode_NE) r =
        r * (1 + ε) + η := by
  obtain ⟨ε, η, hε, hη, hεη, h⟩ :=
    error_N_FLT 2 (-149) 24 (by norm_num) (by norm_num) (fun t : Int => !(decide (2 ∣ t))) r
  refine ⟨ε, η, ?_, ?_, hεη, h⟩
  · calc |ε| ≤ _ := hε
      _ = 2 ^ (-24 : ℤ) := by rw [half_mul_two_zpow]; norm_num
  · calc |η| ≤ _ := hη
      _ = 2 ^ (-150 : ℤ) := by rw [half_mul_two_zpow]; norm_num

/-- The standard model with underflow for native `Float32` addition. -/
theorem add_standard_model (x y : Float32) (hx : x.isFinite = true) (hy : y.isFinite = true)
    (hno : |FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp (-149) 24) (round_mode .mode_NE)
      (toReal x + toReal y)| < 2 ^ (128 : ℤ)) :
    ∃ ε η : ℝ, |ε| ≤ 2 ^ (-24 : ℤ) ∧ |η| ≤ 2 ^ (-150 : ℤ) ∧ ε * η = 0 ∧
      toReal (x + y) = (toReal x + toReal y) * (1 + ε) + η := by
  rw [(add_eq_round x y hx hy hno).1]
  exact round_standard_model _

/-- The standard model with underflow for native `Float32` subtraction. -/
theorem sub_standard_model (x y : Float32) (hx : x.isFinite = true) (hy : y.isFinite = true)
    (hno : |FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp (-149) 24) (round_mode .mode_NE)
      (toReal x - toReal y)| < 2 ^ (128 : ℤ)) :
    ∃ ε η : ℝ, |ε| ≤ 2 ^ (-24 : ℤ) ∧ |η| ≤ 2 ^ (-150 : ℤ) ∧ ε * η = 0 ∧
      toReal (x - y) = (toReal x - toReal y) * (1 + ε) + η := by
  rw [(sub_eq_round x y hx hy hno).1]
  exact round_standard_model _

/-- The standard model with underflow for native `Float32` multiplication. -/
theorem mul_standard_model (x y : Float32)
    (hno : |FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp (-149) 24) (round_mode .mode_NE)
      (toReal x * toReal y)| < 2 ^ (128 : ℤ)) :
    ∃ ε η : ℝ, |ε| ≤ 2 ^ (-24 : ℤ) ∧ |η| ≤ 2 ^ (-150 : ℤ) ∧ ε * η = 0 ∧
      toReal (x * y) = (toReal x * toReal y) * (1 + ε) + η := by
  rw [(mul_eq_round x y hno).1]
  exact round_standard_model _

/-- The standard model with underflow for native `Float32` division. -/
theorem div_standard_model (x y : Float32) (hy : toReal y ≠ 0)
    (hno : |FloatSpec.Core.Generic_fmt.roundR 2 (FLT_exp (-149) 24) (round_mode .mode_NE)
      (toReal x / toReal y)| < 2 ^ (128 : ℤ)) :
    ∃ ε η : ℝ, |ε| ≤ 2 ^ (-24 : ℤ) ∧ |η| ≤ 2 ^ (-150 : ℤ) ∧ ε * η = 0 ∧
      toReal (x / y) = (toReal x / toReal y) * (1 + ε) + η := by
  rw [(div_eq_round x y hy hno).1]
  exact round_standard_model _

/-- The standard model with underflow for native `Float32.sqrt`. -/
theorem sqrt_standard_model (x : Float32) :
    ∃ ε η : ℝ, |ε| ≤ 2 ^ (-24 : ℤ) ∧ |η| ≤ 2 ^ (-150 : ℤ) ∧ ε * η = 0 ∧
      toReal x.sqrt = Real.sqrt (toReal x) * (1 + ε) + η := by
  rw [sqrt_eq_round]
  exact round_standard_model _

end FloatSpec.IEEE754.NativeFloat32
