module
import Lean
set_option warning.simp.varHead false
@[simp] public axiom inlineAssumption (n : Nat) : n = 0
public axiom publicAssumption : False
