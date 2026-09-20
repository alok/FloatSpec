import FloatSpec.src.IEEE754.Bits

/-! Execute the source-shaped comparisons and adjacent-value APIs. The pure
laws do not use native floating point; a separate compiled check compares the
port with actual Float/Float32 runtime comparisons. Neither is a universal
source-equivalence proof. -/

namespace FloatSpec.Test.BitOrderExecution

private def lessEqual (c : Option Ordering) : Bool := c == some .lt || c == some .eq

private def laws (xy yx xx predX xSucc : Option Ordering) (nan : Bool) : Bool :=
  xx == (if nan then none else some .eq) &&
    xy == yx.map Ordering.swap && (nan || (lessEqual predX && lessEqual xSucc))

/-- Reflexivity/unorderedness, reversal, and predecessor/successor order. -/
def laws32 (left right : UInt32) : Bool :=
  letI : Prec_gt_0 24 := ⟨by decide⟩
  letI : Prec_lt_emax 24 128 := ⟨by decide⟩
  let x := b32_of_bits left.toNat
  let y := b32_of_bits right.toNat
  bits_of_b32 (Binary.Bpred x) == bits_of_b32 (b32_pred x) &&
  bits_of_b32 (Binary.Bsucc x) == bits_of_b32 (b32_succ x) &&
  laws (b32_compare x y) (b32_compare y x) (b32_compare x x)
    (b32_compare (Binary.Bpred x) x) (b32_compare x (Binary.Bsucc x)) (Binary.is_nan x)

/-- The same pure ordering laws for binary64. -/
def laws64 (left right : UInt64) : Bool :=
  letI : Prec_gt_0 53 := ⟨by decide⟩
  letI : Prec_lt_emax 53 1024 := ⟨by decide⟩
  let x := b64_of_bits left.toNat
  let y := b64_of_bits right.toNat
  bits_of_b64 (Binary.Bpred x) == bits_of_b64 (b64_pred x) &&
  bits_of_b64 (Binary.Bsucc x) == bits_of_b64 (b64_succ x) &&
  laws (b64_compare x y) (b64_compare y x) (b64_compare x x)
    (b64_compare (Binary.Bpred x) x) (b64_compare x (Binary.Bsucc x)) (Binary.is_nan x)

private def nextWord (state : UInt64) : UInt64 :=
  state * 6364136223846793005 + 1442695040888963407

/-- Execute 2,000 independent ordering-law checks, paired with the Rocq grid. -/
def checkPureOrder : IO Unit := do
  let mut state : UInt64 := 388312
  for _ in [:1000] do
    let left := nextWord state
    let right := nextWord left
    state := right
    unless laws64 left right && laws32 left.toUInt32 right.toUInt32 do
      throw (IO.userError s!"ordering law failure at inputs {left}, {right}")

private def native64 (left right : UInt64) : Option Ordering :=
  let x := Float.ofBits left
  let y := Float.ofBits right
  if x.isNaN || y.isNaN then none
  else if x < y then some .lt else if x == y then some .eq else some .gt

private def native32 (left right : UInt32) : Option Ordering :=
  let x := Float32.ofBits left
  let y := Float32.ofBits right
  if x.isNaN || y.isNaN then none
  else if x < y then some .lt else if x == y then some .eq else some .gt

/-- Compare the actual port APIs with 200,000 native comparisons. This uses
runtime primitives as an additional oracle, not as a proof of their semantics. -/
def checkNativeOrder : IO Unit := do
  let mut state : UInt64 := 388312
  for _ in [:100000] do
    let left := nextWord state
    let right := nextWord left
    state := right
    unless b64_compare (b64_of_bits left.toNat) (b64_of_bits right.toNat) ==
        native64 left right do
      throw (IO.userError s!"native binary64 comparison disagreement: {left}, {right}")
    unless b32_compare (b32_of_bits left.toUInt32.toNat) (b32_of_bits right.toUInt32.toNat) ==
        native32 left.toUInt32 right.toUInt32 do
      throw (IO.userError s!"native binary32 comparison disagreement: {left.toUInt32}, {right.toUInt32}")

set_option maxRecDepth 10000

/-- Kernel regressions retain signed-zero equality, ordinary ordering, unordered
signaling NaNs, and the signed zero reached from a negative minimum subnormal. -/
theorem orderBoundaryRegressions :
    (b32_compare (b32_of_bits 0) (b32_of_bits 0x80000000),
     b64_compare (b64_of_bits 0x3ff0000000000000) (b64_of_bits 0x4000000000000000),
     b32_compare (b32_of_bits 0xff800001) (b32_of_bits 0),
     bits_of_b64 (b64_succ (b64_of_bits 0x8000000000000001))) =
    (some .eq, some .lt, none, 0x8000000000000000) := by decide +kernel

/-- Generic source comparisons retain their four outcomes even when there is
no positive-precision or precision-below-emax instance. -/
theorem genericComparisonBoundaryRegressions :
    (Binary.Bcompare (prec := 0) (emax := -1) (.B754_zero true) (.B754_zero false),
     BinarySingleNaN.Bcompare (prec := 0) (emax := -1) .B754_nan (.B754_zero false),
     BinarySingleNaN.Bcompare (prec := 1) (emax := 1) (.B754_infinity true) (.B754_zero false),
     Binary.Bcompare (b64_of_bits 0xc000000000000000) (b64_of_bits 0xbff0000000000000)) =
    (some .eq, none, some .lt, some .lt) := by decide +kernel

/-- The generic integer algorithms retain signed-zero and overflow boundaries,
including exact signaling-NaN payloads. These are kernel checks, not FFI calls. -/
theorem genericNeighborBoundaryRegressions :
    (letI : Prec_gt_0 24 := ⟨by decide⟩;
     letI : Prec_lt_emax 24 128 := ⟨by decide⟩;
     [bits_of_b32 (Binary.Bsucc (b32_of_bits 0x80000001)),
      bits_of_b32 (Binary.Bpred (b32_of_bits 0)),
      bits_of_b32 (Binary.Bsucc (b32_of_bits 0x7f7fffff)),
      bits_of_b32 (Binary.Bulp (b32_of_bits 0xff800001)),
      bits_of_b32 (Binary.Bulp (b32_of_bits 0x3f800000))]) =
    [0x80000000, 0x80000001, 0x7f800000, 0xff800001, 0x34000000] := by
  decide +kernel

#eval checkPureOrder
#eval checkNativeOrder

end FloatSpec.Test.BitOrderExecution
