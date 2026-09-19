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

end FloatSpec.Test.NativeBridgeBits
