import FloatSpec.Linter.CoqSourceLinter
set_option linter.coqSource true
set_option warningAsError true

mutual
private def privateMember (n : Nat) : Nat := n
-- EXPECT: missingAfterPrivate
def missingAfterPrivate (n : Nat) : Nat := n + 1
end
