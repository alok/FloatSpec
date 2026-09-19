import FloatSpec.src.Core.SimprocRaux

namespace FloatSpec.Test.SimprocRaux

open FloatSpec.Core.Raux

/-! Exercise the real-valued branch that the `reduceZtruncNeg` simproc was
written for.  Merely compiling the simproc definition does not typecheck the
expression it constructs for a successful match. -/

example (x : ℝ) : Ztrunc (-x) = -Ztrunc x := by
  simp only [reduceZtruncNeg]

end FloatSpec.Test.SimprocRaux
