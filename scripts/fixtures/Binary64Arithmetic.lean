import FloatSpec.src.IEEE754.Bits

/-! Binary64 arithmetic executes the computable `Binary` operations, which round
through the integer pipeline and overflow as Flocq does. The expected answers
are literal IEEE-754 bit patterns: `1 + 2` is `3`, and the largest finite
binary64 times two overflows to `+∞` in round-to-nearest, both through the
`b64_*` wrappers and through `Binary.Bmult` directly. -/

namespace Binary64Arithmetic

private instance : Prec_gt_0 (53 : Int) := ⟨by decide⟩
private instance : Prec_lt_emax (53 : Int) (1024 : Int) := ⟨by decide⟩

private def one : binary64 := b64_of_bits 0x3FF0000000000000
private def two : binary64 := b64_of_bits 0x4000000000000000
private def maxFinite : binary64 := b64_of_bits 0x7FEFFFFFFFFFFFFF

private def rows : List Int :=
  [bits_of_b64 (b64_plus .RNE one two),
   bits_of_b64 (b64_mult .RNE maxFinite two),
   bits_of_b64 (Binary.Bmult binop_nan_pl64 .RNE Binary.Bmax_float two),
   bits_of_b64 Binary.Bmax_float]

private def expected : List Int :=
  [0x4008000000000000, 0x7FF0000000000000, 0x7FF0000000000000, 0x7FEFFFFFFFFFFFFF]

example : rows = expected := by decide +kernel

private def check : IO Unit := do
  unless decide (rows = expected) do throw (IO.userError "binary64 arithmetic mismatch")
  IO.println "PASS: four binary64 sum and overflow boundaries (compiled and kernel-checked)."

#eval check

end Binary64Arithmetic
