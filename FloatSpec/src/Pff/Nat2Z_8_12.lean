-- Mirror of Coq file: flocq/src/Pff/Nat2Z_8_12.v
-- Provides Nat → Int compatibility lemma for division.

import FloatSpec.src.Core
import FloatSpec.src.Compat
open FloatSpec.Core

namespace FloatSpec.Pff.Nat2Z

/-- Coq lemma {lit}`Nat2Z.inj_div`:
    {lit}`Z.of_nat (n / m) = (Z.of_nat n / Z.of_nat m)`

    The cast of a natural quotient is the integer quotient of the casts.

-/
theorem inj_div (n m : Nat) :
    ((n / m : Nat) : Int) = (n : Int) / (m : Int) :=
  Int.natCast_div n m

end FloatSpec.Pff.Nat2Z
