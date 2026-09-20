import FloatSpec.src.IEEE754.Bits
import FloatSpec.src.IEEE754.BinarySingleNaNSourceFacade

/-! Compiled nearest-even arithmetic on the source-shaped carriers, checked
through the direct and source-mode SingleNaN APIs against native binary32/binary64. The source operations are integer algorithms;
only the independent oracle uses runtime floating point. NaNs are explicitly
quotiented here, unlike the exact-payload Rocq bridge. -/

namespace FloatSpec.Test.NativeSingleNaNArithmetic

private instance : Prec_gt_0 (24 : Int) := ⟨by decide⟩
private instance : Prec_lt_emax (24 : Int) (128 : Int) := ⟨by decide⟩
private instance : Prec_gt_0 (53 : Int) := ⟨by decide⟩
private instance : Prec_lt_emax (53 : Int) (1024 : Int) := ⟨by decide⟩

private def native32 (x : Float32) : Int :=
  if x.isNaN then 0x7fc00000 else x.toBits.toNat

private def native64 (x : Float) : Int :=
  if x.isNaN then 0x7ff8000000000000 else x.toBits.toNat

private def model32 (x : BinarySingleNaN.binary_float 24 128) : Int :=
  if h : Binary.is_nan_BSN x = true then 0x7fc00000
  else bits_of_b32 (Binary.BSN2B' x (Bool.eq_false_of_not_eq_true h))

private def model64 (x : BinarySingleNaN.binary_float 53 1024) : Int :=
  if h : Binary.is_nan_BSN x = true then 0x7ff8000000000000
  else bits_of_b64 (Binary.BSN2B' x (Bool.eq_false_of_not_eq_true h))

/-- Direct/source-mode SingleNaN results and native expectations for addition,
subtraction, multiplication, division, and square root. Every column must agree. -/
def observations32 (left right : UInt32) : List Int × List Int :=
  let x := Binary.B2BSN (b32_of_bits left.toNat)
  let y := Binary.B2BSN (b32_of_bits right.toNat)
  let a := Float32.ofBits left
  let b := Float32.ofBits right
  ([model32 (BinarySingleNaN.Bplus .RNE x y), model32 (BinarySingleNaN.Bminus .RNE x y),
    model32 (BinarySingleNaN.Bmult .RNE x y), model32 (BinarySingleNaN.Bdiv .RNE x y), model32 (BinarySingleNaN.Bsqrt .RNE x)] ++
   [model32 (FloatSpec.IEEE754.BinarySingleNaN.Source.Bplus .mode_NE x y),
    model32 (FloatSpec.IEEE754.BinarySingleNaN.Source.Bminus .mode_NE x y),
    model32 (FloatSpec.IEEE754.BinarySingleNaN.Source.Bmult .mode_NE x y),
    model32 (FloatSpec.IEEE754.BinarySingleNaN.Source.Bdiv .mode_NE x y),
    model32 (FloatSpec.IEEE754.BinarySingleNaN.Source.Bsqrt .mode_NE x)],
   [native32 (a + b), native32 (a - b), native32 (a * b), native32 (a / b), native32 a.sqrt] ++
   [native32 (a + b), native32 (a - b), native32 (a * b), native32 (a / b), native32 a.sqrt])

/-- The same ten public-API/native comparisons for binary64. -/
def observations64 (left right : UInt64) : List Int × List Int :=
  let x := Binary.B2BSN (b64_of_bits left.toNat)
  let y := Binary.B2BSN (b64_of_bits right.toNat)
  let a := Float.ofBits left
  let b := Float.ofBits right
  ([model64 (BinarySingleNaN.Bplus .RNE x y), model64 (BinarySingleNaN.Bminus .RNE x y),
    model64 (BinarySingleNaN.Bmult .RNE x y), model64 (BinarySingleNaN.Bdiv .RNE x y), model64 (BinarySingleNaN.Bsqrt .RNE x)] ++
   [model64 (FloatSpec.IEEE754.BinarySingleNaN.Source.Bplus .mode_NE x y),
    model64 (FloatSpec.IEEE754.BinarySingleNaN.Source.Bminus .mode_NE x y),
    model64 (FloatSpec.IEEE754.BinarySingleNaN.Source.Bmult .mode_NE x y),
    model64 (FloatSpec.IEEE754.BinarySingleNaN.Source.Bdiv .mode_NE x y),
    model64 (FloatSpec.IEEE754.BinarySingleNaN.Source.Bsqrt .mode_NE x)],
   [native64 (a + b), native64 (a - b), native64 (a * b), native64 (a / b), native64 a.sqrt] ++
   [native64 (a + b), native64 (a - b), native64 (a * b), native64 (a / b), native64 a.sqrt])

private def check (width : Nat) (left right : Nat) (rows : List Int × List Int) : IO Unit := do
  unless rows.1 == rows.2 do
    -- Reproduce the exact SingleNaN observations by calling observations32 or
    -- observations64 with these words. The same bit inputs can be given to
    -- ieee_modes_bridge.py to compare the full-payload baseline with Rocq.
    throw (IO.userError s!"source/native arithmetic mismatch; seed=831557; \
      replay=[{width},0,{left},{right},0]; source={rows.1}; native={rows.2}")

/-- Run 200,200 arithmetic comparisons on boundary and seeded input pairs. This is
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
  let mut state : UInt64 := 831557
  for _ in [:10000] do
    state := state * 6364136223846793005 + 1442695040888963407
    let left := state
    state := state * 6364136223846793005 + 1442695040888963407
    let right := state
    check 64 left.toNat right.toNat (observations64 left right)
    check 32 left.toUInt32.toNat right.toUInt32.toNat
      (observations32 left.toUInt32 right.toUInt32)

#eval do
  checkNativeArithmetic
  IO.println "PASS: 200,200 native comparisons through both SingleNaN APIs; seed 831557."

end FloatSpec.Test.NativeSingleNaNArithmetic
