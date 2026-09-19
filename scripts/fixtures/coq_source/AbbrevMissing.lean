import FloatSpec.Linter.CoqSourceLinter
set_option linter.coqSource true
set_option warningAsError true

namespace AbbrevProbe
-- EXPECT: AbbrevProbe.missingAlias
abbrev missingAlias := Nat
end AbbrevProbe
