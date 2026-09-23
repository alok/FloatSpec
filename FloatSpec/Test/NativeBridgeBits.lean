import FloatSpec.src.IEEE754.PrimFloat

namespace FloatSpec.Test.NativeBridgeBits

open FaithfulPrimFloat.PrimitiveFloat

example : nextUpBits 0 = 1 := by decide
example : nextUpBits 0x8000000000000000 = 1 := by decide
example : nextUpBits 0x7ff0000000000000 = 0x7ff0000000000000 := by decide
example : nextUpBits 0xfff0000000000000 = 0xffefffffffffffff := by decide
example : nextUpBits 0x7ff8000000000001 = 0x7ff8000000000001 := by decide

example : nextDownBits 0 = 0x8000000000000001 := by decide
example : nextDownBits 0x8000000000000000 = 0x8000000000000001 := by decide
example : nextDownBits 0xfff0000000000000 = 0xfff0000000000000 := by decide
example : nextDownBits 0x7ff0000000000000 = 0x7fefffffffffffff := by decide
example : nextDownBits 0xfff8000000000001 = 0xfff8000000000001 := by decide

-- Kernel-evaluated `frexpBits` regressions: signed zero, subnormal extremes,
-- the smallest normal, one, the largest finite value, infinity, and NaN.
example : frexpBits 0 = (0, 0) := by decide
example : frexpBits 0x8000000000000000 = (0x8000000000000000, 0) := by decide
example : frexpBits 1 = (0x3fe0000000000000, -1073) := by decide
example : frexpBits 0x800fffffffffffff = (0xbfeffffffffffffe, -1022) := by decide
example : frexpBits 0x0010000000000000 = (0x3fe0000000000000, -1021) := by decide
example : frexpBits 0x3ff0000000000000 = (0x3fe0000000000000, 1) := by decide
example : frexpBits 0x7fefffffffffffff = (0x3fefffffffffffff, 1024) := by decide
example : frexpBits 0xfff0000000000000 = (0xfff0000000000000, 0) := by decide
example : frexpBits 0x7ff8000000000001 = (0x7ff8000000000001, 0) := by decide

end FloatSpec.Test.NativeBridgeBits
