/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import FloatSpec.src.IEEE754.Binary
import FloatSpec.src.IEEE754.Bits
import Mathlib.Basic.Real.Basic

/-!
# Pure-Lean IEEE-754 Binary64 Decoder

A pure-Lean decoder from `UInt64` bit patterns to `ℝ`, using FloatSpec's
`bits_to_binary` and `B2R` infrastructure, with verified zero, one, and
semantic-negation results below. This replaces the opaque
`Float.ofBits` path used in `FPRBridge.toReal` with a pure-Lean definition
that the kernel can reason about. It also proves, for every `UInt64` bit
pattern, that XOR with the sign-bit mask decodes to `Bopp` of the decoded
value, preserving NaN payloads and signed zeros.

## Main Definitions

- `Binary64.ofBits`: decode a `UInt64` into `Binary754 53 1023`
- `Binary64.toReal`: decode a `UInt64` into `ℝ`

## Main Results

- `Binary64.toReal_zero`: the all-zeros pattern decodes to `0`
- `Binary64.toReal_one`: the pattern `0x3FF0000000000000` decodes to `1`
- `Binary64.ofBits_flipSign`: sign-bit XOR decodes to `Bopp` on all bit patterns
- `Binary64.negated_toReal`: decoded `Bopp` negation negates the real value
-/

open FloatSpec.Core.Defs

section

namespace Binary64

instance : Prec_gt_0 (53 : Int) := ⟨by grind⟩
instance : Prec_lt_emax (53 : Int) (1023 : Int) := ⟨by grind⟩

/-- Decode a `UInt64` bit pattern into a `Binary754 53 1023` (binary64 format). -/
def ofBits (w : UInt64) : Binary754 53 1023 :=
  bits_to_binary 53 1023 (w.toNat : Int)

/-- Decode a `UInt64` bit pattern into `ℝ` via the IEEE-754 binary64 format.
Non-finite bit patterns (infinities, NaNs) map to `0`. -/
noncomputable def toReal (w : UInt64) : ℝ := B2R (ofBits w)

/-! ### Constants -/

/-- The sign bit mask for binary64: bit 63. -/
def signBitMask : UInt64 := 0x8000000000000000

/-- The bit pattern for IEEE-754 binary64 `+1.0`: biased exponent 1023, zero mantissa. -/
def oneBits : UInt64 := 0x3FF0000000000000

/-! ### Zero decoding -/

/-- The all-zeros `UInt64` decodes to the `+0` float. -/
theorem ofBits_zero_val : (ofBits 0).val = FullFloat.F754_zero false := by
  decide

/-- The all-zeros `UInt64` decodes to `0 : ℝ`. -/
theorem toReal_zero : toReal 0 = 0 := by
  simp [toReal, B2R, ofBits_zero_val, FF2R]

/-! ### One decoding -/

/-- The `0x3FF0000000000000` pattern decodes to a finite float with
mantissa `2^52` and exponent `-52`, representing `1.0`. -/
theorem ofBits_one_val :
    (ofBits oneBits).val =
      FullFloat.F754_finite false (2 ^ 52) (-52) := by
  decide

/-- The `0x3FF0000000000000` pattern decodes to `1 : ℝ`. -/
theorem toReal_one : toReal oneBits = 1 := by
  simp [toReal, B2R, ofBits_one_val, FF2R, _root_.F2R]
  norm_num

/-! ### Negation -/

/-- Flip the sign bit of a `UInt64` to negate the IEEE-754 value.

This is the executable bit operation. `ofBits_flipSign` below proves that this
raw `UInt64` XOR is `Bopp` on the decoded binary64 value for every bit
pattern. -/
def flipSign (w : UInt64) : UInt64 := w ^^^ signBitMask

/-- Semantic negation of a decoded binary64 value. -/
def negated (w : UInt64) : Binary754 53 1023 :=
  FF2B (prec:=53) (emax:=1023) (Bopp (ofBits w).val)

/-! ### Sign-bit XOR is decoded negation -/

/-- The binary64 case split of `bits_to_binary`, taken from its three raw
fields: sign `s`, 52-bit mantissa field `m` and 11-bit exponent field `e`. -/
private def decodeFields (s : Bool) (m e : Int) : Binary754 53 1023 :=
  if e = 2 ^ 11 - 1 then
    if m = 0 then FF2B (FullFloat.F754_infinity s)
    else FF2B (FullFloat.F754_nan s m.toNat)
  else if e = 0 then
    if m = 0 then FF2B (FullFloat.F754_zero s)
    else FF2B (FullFloat.F754_finite s m.toNat ((1 - 1023) - 52))
  else FF2B (FullFloat.F754_finite s (2 ^ 52 + m).toNat ((e - 1023) - 52))

/-- `ofBits` depends on the bit pattern only through `split_bits 52 11`. -/
private theorem ofBits_eq_decodeFields (w : UInt64) :
    ofBits w = decodeFields (decide ((2 : Int) ^ 52 * 2 ^ 11 ≤ (w.toNat : Int)))
      ((w.toNat : Int) % 2 ^ 52) (((w.toNat : Int) / 2 ^ 52) % 2 ^ 11) := by
  have hmw : mant_width 53 = 52 := by decide
  have hew : exp_width 1023 = 11 := by decide
  have hlt : (w.toNat : Int) < 2 ^ 64 := by
    have := w.toNat_lt
    omega
  have hmod : (w.toNat : Int) % 2 ^ (52 + 11 + 1) = w.toNat :=
    Int.emod_eq_of_lt (by omega) (by simpa using hlt)
  unfold ofBits bits_to_binary
  simp only [hmw, hew, hmod, split_bits, decodeFields]
  rfl

/-- `Bopp` changes only the sign argument of every decoded constructor, keeping
NaN payloads, mantissas and exponents. -/
private theorem FF2B_Bopp_decodeFields (s : Bool) (m e : Int) :
    FF2B (prec := 53) (emax := 1023) (Bopp (decodeFields s m e).val) =
      decodeFields (!s) m e := by
  unfold decodeFields
  split_ifs <;> rfl

private theorem toNat_flipSign (w : UInt64) :
    (flipSign w).toNat = w.toNat ^^^ 2 ^ 63 := by
  rw [flipSign, UInt64.toNat_xor]
  rfl

/-- XOR with bit 63 leaves the 52-bit mantissa field unchanged. -/
private theorem xor_sign_mantissa (n : Nat) :
    (n ^^^ 2 ^ 63) % 2 ^ 52 = n % 2 ^ 52 := by
  rw [Nat.xor_mod_two_pow]
  have h : (2 : Nat) ^ 63 % 2 ^ 52 = 0 := by decide
  rw [h, Nat.xor_zero]

/-- XOR with bit 63 leaves the 11-bit exponent field unchanged. -/
private theorem xor_sign_exponent (n : Nat) :
    ((n ^^^ 2 ^ 63) / 2 ^ 52) % 2 ^ 11 = (n / 2 ^ 52) % 2 ^ 11 := by
  rw [Nat.xor_div_two_pow, Nat.xor_mod_two_pow]
  have h : (2 : Nat) ^ 63 / 2 ^ 52 % 2 ^ 11 = 0 := by decide
  rw [h, Nat.xor_zero]

/-- XOR with bit 63 flips the sign field of a 64-bit pattern. -/
private theorem xor_sign_sign (n : Nat) (hn : n < 2 ^ 64) :
    2 ^ 63 ≤ (n ^^^ 2 ^ 63) ↔ ¬ 2 ^ 63 ≤ n := by
  have hdiv : (n ^^^ 2 ^ 63) / 2 ^ 63 = n / 2 ^ 63 ^^^ 1 := by
    rw [Nat.xor_div_two_pow, Nat.div_self (by positivity)]
  have hlt : n ^^^ 2 ^ 63 < 2 ^ 64 := Nat.xor_lt_two_pow hn (by decide)
  have hq : n / 2 ^ 63 = 0 ∨ n / 2 ^ 63 = 1 := by omega
  rcases hq with hq | hq
  · rw [hq] at hdiv
    have h : (0 : Nat) ^^^ 1 = 1 := by decide
    omega
  · rw [hq] at hdiv
    have h : (1 : Nat) ^^^ 1 = 0 := by decide
    omega

/-- All-bit-pattern correspondence between sign-bit XOR and decoded negation.
XOR with `signBitMask` flips the sign field and keeps the exponent and
mantissa fields, so every decoded constructor (zero, subnormal, normal,
infinity and NaN with its payload) has its sign negated exactly as `Bopp`
does; real-value negation alone could not establish this. -/
theorem ofBits_flipSign (w : UInt64) : ofBits (flipSign w) = negated w := by
  have hn := w.toNat_lt
  rw [negated, ofBits_eq_decodeFields, ofBits_eq_decodeFields,
    FF2B_Bopp_decodeFields, toNat_flipSign]
  have hs := xor_sign_sign w.toNat (by simpa using hn)
  have hm := xor_sign_mantissa w.toNat
  have he := xor_sign_exponent w.toNat
  congr 1
  · rw [← decide_not]
    exact decide_eq_decide.mpr (by omega)
  · omega
  · omega

/-- Decoder-level semantic negation via FloatSpec's verified `Bopp`.

Combined with `ofBits_flipSign`, this shows that flipping the raw sign bit
negates the decoded real value. -/
theorem negated_toReal (w : UInt64) : B2R (negated w) = -toReal w := by
  change FF2R 2 (Bopp (ofBits w).val) = -FF2R 2 (ofBits w).val
  exact B2R_Bopp_compat (ofBits w).val

end Binary64

end
