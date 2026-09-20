import FloatSpec.src.IEEE754.Bits

/-! Integer-only model adapters. The source bit decoder preserves NaN sign and
payload; Lean's logical model deliberately canonicalizes them. -/

namespace FloatSpec.Test.NativeModelAdapters

open FloatSpec.IEEE754.Native

/-- Five actual source/model-adapter paths at binary32 width. -/
def observe32 (bits : Int) : List Int :=
  let source := b32_of_bits bits
  let model := Float32.Model.ofBits (UInt32.ofInt bits)
  let decoded := binary32OfModel model
  [bits_of_b32 source, (model32OfBinary source).toBits.toNat,
    bits_of_b32 decoded, (model32OfBinary decoded).toBits.toNat,
    bits_of_b32 (binary32OfModel (model32OfBinary source))]

/-- Five actual source/model-adapter paths at binary64 width. -/
def observe64 (bits : Int) : List Int :=
  let source := b64_of_bits bits
  let model := Float.Model.ofBits (UInt64.ofInt bits)
  let decoded := binary64OfModel model
  [bits_of_b64 source, (model64OfBinary source).toBits.toNat,
    bits_of_b64 decoded, (model64OfBinary decoded).toBits.toNat,
    bits_of_b64 (binary64OfModel (model64OfBinary source))]

/-- Independent arithmetic NaN classification for an already bounded word. -/
def canonical (mantissaBits exponentBits : Nat) (word : Int) : Int :=
  let fraction := word % (2 ^ mantissaBits : Int)
  let exponent := (word / (2 ^ mantissaBits : Int)) % (2 ^ exponentBits : Int)
  if exponent = 2 ^ exponentBits - 1 ∧ fraction ≠ 0 then
      ((2 ^ exponentBits : Int) - 1) * 2 ^ mantissaBits + 2 ^ (mantissaBits - 1)
    else word

/-- The source total integer decoder uses a sign threshold, whereas UInt
conversion wraps. The two routes agree on bounded words, not all integers. -/
def expected (width mantissaBits exponentBits : Nat) (bits : Int) : List Int :=
  let signWeight : Int := 2 ^ (width - 1)
  let sourceWord := bits % signWeight + if signWeight ≤ bits then signWeight else 0
  let wrappedWord := bits % (2 ^ width : Int)
  let sourceModel := canonical mantissaBits exponentBits sourceWord
  let wrappedModel := canonical mantissaBits exponentBits wrappedWord
  [sourceWord, sourceModel, wrappedModel, wrappedModel, sourceModel]

private def words32 : List Int :=
  [0, 0x80000000, 1, 0x007fffff, 0x00800000, 0x3f800000,
    0x7f7fffff, 0x7f800000, 0xff800000, 0x7f800001, 0xff800001,
    0x7fc00000, 0xffffffff, -1, 0x100000001, -0x80000000]

private def words64 : List Int :=
  [0, 0x8000000000000000, 1, 0x000fffffffffffff, 0x0010000000000000,
    0x3ff0000000000000, 0x7fefffffffffffff, 0x7ff0000000000000,
    0xfff0000000000000, 0x7ff0000000000001, 0xfff0000000000001,
    0x7ff8000000000000, 0xffffffffffffffff, -1, 0x10000000000000001,
    -0x8000000000000000]

/-- Thirty-two boundary/wrapping inputs, with five paths each, checked by the kernel. -/
theorem boundary_cases :
    (words32.all (fun bits => observe32 bits == expected 32 23 8 bits) &&
      words64.all (fun bits => observe64 bits == expected 64 52 11 bits)) = true := by
  decide +kernel

/-- A signed payload survives the raw source decoder but not the logical model. -/
theorem signed_nan_distinction :
    observe64 0xfff0000000000001 =
      [0xfff0000000000001, 0x7ff8000000000000, 0x7ff8000000000000,
        0x7ff8000000000000, 0x7ff8000000000000] := by
  decide +kernel

/-- Wider-than-word integer decoding and machine wrapping disagree at a finite value. -/
theorem wider_integer_distinction :
    observe32 0x100000001 = [0x80000001, 0x80000001, 1, 1, 0x80000001] := by
  decide +kernel

/-- Negative out-of-range input separates positive source zero from wrapped negative zero. -/
theorem negative_integer_distinction :
    observe64 (-0x8000000000000000) =
      [0, 0, 0x8000000000000000, 0x8000000000000000, 0] := by
  decide +kernel

private def check (width : Nat) (bits : Int) (actual expectedRow : List Int) : IO Unit := do
  unless actual == expectedRow do
    throw (IO.userError s!"model adapter mismatch; seed=854033; width={width}; bits={bits}; actual={actual}; expected={expectedRow}")

/-- Execute both widths, including signed and wider-than-word integers. -/
def runChecks : IO Unit := do
  for bits in words32 do
    check 32 bits (observe32 bits) (expected 32 23 8 bits)
  for bits in words64 do
    check 64 bits (observe64 bits) (expected 64 52 11 bits)
  let mut state : UInt64 := 854033
  for _ in [:10000] do
    state := state * 6364136223846793005 + 1442695040888963407
    let bits : Int := state.toNat
    for word in [bits, -bits, bits + 2 ^ 80] do
      check 32 word (observe32 word) (expected 32 23 8 word)
      check 64 word (observe64 word) (expected 64 52 11 word)
  IO.println "Model adapters: 60,032 inputs / 300,160 path observations passed; seed=854033"

#eval runChecks
#print axioms boundary_cases
#print axioms signed_nan_distinction
#print axioms wider_integer_distinction
#print axioms negative_integer_distinction

end FloatSpec.Test.NativeModelAdapters
