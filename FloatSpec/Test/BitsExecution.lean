import FloatSpec.src.IEEE754.Bits

/-! Direct execution of the port's source-shaped bit decoders, without using
Lean's built-in float model as an input adapter. NaN signs/payloads are retained. -/

namespace FloatSpec.Test.BitsExecution

private def boolean (b : Bool) : Int := if b then 1 else 0

/-- Serialize the exact constructor, sign, positive payload, and exponent. -/
def full : full_float → List Int
  | .F754_zero s => [0, boolean s, 0, 0]
  | .F754_infinity s => [1, boolean s, 0, 0]
  | .F754_nan s payload => [2, boolean s, FloatSpec.Core.Zaux.Zpos payload, 0]
  | .F754_finite s mantissa exponent =>
      [3, boolean s, FloatSpec.Core.Zaux.Zpos mantissa, exponent]

/-- Observe binary32 decoding, re-encoding, raw field splitting, and validity. -/
def observation32 (bits : Int) : List Int :=
  let x := b32_of_bits bits
  let fields := split_bits 23 8 bits
  let raw := binaryFloatToFullFloat x
  full raw ++ [bits_of_b32 x, boolean fields.1, fields.2.1, fields.2.2,
    boolean (valid_binary (prec := 24) (emax := 128) (full_float.toFullFloat raw))]

/-- Observe binary64 decoding, re-encoding, raw field splitting, and validity. -/
def observation64 (bits : Int) : List Int :=
  let x := b64_of_bits bits
  let fields := split_bits 52 11 bits
  let raw := binaryFloatToFullFloat x
  full raw ++ [bits_of_b64 x, boolean fields.1, fields.2.1, fields.2.2,
    boolean (valid_binary (prec := 53) (emax := 1024) (full_float.toFullFloat raw))]

set_option maxRecDepth 10000

-- The old unary converter exhausted the recursion limit on this ordinary value.
example : bits_of_b64 (b64_of_bits 0x3ff0000000000000) = 0x3ff0000000000000 :=
  by decide +kernel

-- No canonicalization: signaling NaN sign and payload survive the bit decoder.
example : observation64 0xfff0000000000001 =
    [2, 1, 1, 0, 0xfff0000000000001, 1, 1, 2047, 1] := by decide +kernel

example : observation32 0x3f800000 =
    [3, 0, 8388608, -23, 0x3f800000, 0, 0, 127, 1] := by decide +kernel

/-- A compiled-only independent roundtrip grid. The theorem examples above use
kernel reduction; this check additionally rejects missing executable code. -/
def checkRoundtrips : IO Unit := do
  let mut state : UInt64 := 526913
  for _ in [:10000] do
    state := state * 6364136223846793005 + 1442695040888963407
    let word64 : Int := state.toNat
    let word32 : Int := state.toUInt32.toNat
    unless bits_of_b64 (b64_of_bits word64) == word64 do
      throw (IO.userError s!"binary64 roundtrip failed: {word64}")
    unless bits_of_b32 (b32_of_bits word32) == word32 do
      throw (IO.userError s!"binary32 roundtrip failed: {word32}")

#eval checkRoundtrips

end FloatSpec.Test.BitsExecution
