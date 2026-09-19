import FloatSpec.Linter.CoqSourceLinter
set_option linter.coqSource true
set_option warningAsError true

namespace ClassificationProbe
mutual
@[flocq_local "First mutual member"]
def firstMember (n : Nat) : Nat := n
@[flocq_local "Second mutual member"]
def secondMember (n : Nat) : Nat := n + 1
end
@[flocq_local "Namespaced helper"]
def Nested.covered : Nat := 1
@[flocq_local "Root-qualified helper"]
def _root_.coveredAtRoot : Nat := 1
@[flocq_local "Classified abbreviation"]
abbrev aliasAtNamespace := firstMember
private def privateHelper : Nat := 1
end ClassificationProbe
