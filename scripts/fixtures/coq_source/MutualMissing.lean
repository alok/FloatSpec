import FloatSpec.Linter.CoqSourceLinter
set_option linter.coqSource true
set_option warningAsError true

namespace MutualProbe
mutual
@[flocq_local "Classified first member must not hide later members"]
def covered (n : Nat) : Nat := n
-- EXPECT: MutualProbe.uncovered
def uncovered (n : Nat) : Nat := n + 1
end
end MutualProbe
