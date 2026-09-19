import FloatSpec.src.IEEE754.Bits

/-! Compiled nearest-even arithmetic on the source-shaped carriers, checked
against native binary32/binary64. The source operations are integer algorithms;
only the independent oracle uses runtime floating point. NaNs are explicitly
quotiented here, unlike the exact-payload Rocq bridge. -/

namespace FloatSpec.Test.NativeSourceArithmetic

private def native32 (x : Float32) : Int :=
  if x.isNaN then 0x7fc00000 else x.toBits.toNat

private def native64 (x : Float) : Int :=
  if x.isNaN then 0x7ff8000000000000 else x.toBits.toNat

private def model32 (x : binary32) : Int :=
  if Binary.is_nan x then 0x7fc00000 else bits_of_b32 x

private def model64 (x : binary64) : Int :=
  if Binary.is_nan x then 0x7ff8000000000000 else bits_of_b64 x

/-- Source results and native expected results for add/subtract/multiply/divide
and square root of the left input. Every column must agree. -/
def observations32 (left right : UInt32) : List Int × List Int :=
  let x := b32_of_bits left.toNat
  let y := b32_of_bits right.toNat
  let a := Float32.ofBits left
  let b := Float32.ofBits right
  ([model32 (b32_plus .RNE x y), model32 (b32_minus .RNE x y),
    model32 (b32_mult .RNE x y), model32 (b32_div .RNE x y), model32 (b32_sqrt .RNE x)],
   [native32 (a + b), native32 (a - b), native32 (a * b), native32 (a / b), native32 a.sqrt])

/-- The same five source/native comparisons for binary64. -/
def observations64 (left right : UInt64) : List Int × List Int :=
  let x := b64_of_bits left.toNat
  let y := b64_of_bits right.toNat
  let a := Float.ofBits left
  let b := Float.ofBits right
  ([model64 (b64_plus .RNE x y), model64 (b64_minus .RNE x y),
    model64 (b64_mult .RNE x y), model64 (b64_div .RNE x y), model64 (b64_sqrt .RNE x)],
   [native64 (a + b), native64 (a - b), native64 (a * b), native64 (a / b), native64 a.sqrt])

private def check (width : Nat) (left right : Nat) (rows : List Int × List Int) : IO Unit := do
  unless rows.1 == rows.2 do
    -- This exact triple can be replayed by ieee_modes_bridge.py. Third operand
    -- zero is irrelevant to the five operations checked by this native grid.
    throw (IO.userError s!"source/native arithmetic mismatch; seed=489231; \
      replay=[{width},0,{left},{right},0]; source={rows.1}; native={rows.2}")

/-- Run 100,100 arithmetic comparisons on boundary and seeded input pairs. This is
finite native execution, not a proof of a compiler or hardware specification. -/
def checkNativeArithmetic : IO Unit := do
  for (left, right) in ([
      (0, 0), (0x80000000, 0), (1, 0), (0x00800000, 0x3f000000),
      (0x7f7fffff, 0x40000000), (0x7f800000, 0), (0xff800000, 0x7f800000),
      (0xff800001, 0x3f800000), (0xbf800000, 0x3f800000),
      (0x3f800000, 0x33800000)] : List (UInt32 × UInt32)) do
    check 32 left.toNat right.toNat (observations32 left right)
  for (left, right) in ([
      (0, 0), (0x8000000000000000, 0), (1, 0), (0x0010000000000000, 0x3fe0000000000000),
      (0x7fefffffffffffff, 0x4000000000000000), (0x7ff0000000000000, 0),
      (0xfff0000000000000, 0x7ff0000000000000), (0xfff0000000000001, 0x3ff0000000000000),
      (0xbff0000000000000, 0x3ff0000000000000),
      (0x3ff0000000000000, 0x3ca0000000000000)] : List (UInt64 × UInt64)) do
    check 64 left.toNat right.toNat (observations64 left right)
  let mut state : UInt64 := 489231
  for _ in [:10000] do
    state := state * 6364136223846793005 + 1442695040888963407
    let left := state
    state := state * 6364136223846793005 + 1442695040888963407
    let right := state
    check 64 left.toNat right.toNat (observations64 left right)
    check 32 left.toUInt32.toNat right.toUInt32.toNat
      (observations32 left.toUInt32 right.toUInt32)

#eval checkNativeArithmetic

end FloatSpec.Test.NativeSourceArithmetic
