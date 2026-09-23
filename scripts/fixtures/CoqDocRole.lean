import FloatSpec.src.Core.Round_pred
import FloatSpec.src.IEEE754.BinarySingleNaN

/-! Accepted uses of the Flocq docstring extensions defined in `FloatSpecRoles`: the `{coq}` and
`{coq_file}` roles and the `coq` quote block, written the way a library docstring would write
them. Run with `lake env lean scripts/fixtures/CoqDocRole.lean`.

This file checks by elaborating. A citation that names no pinned anchor, or names several, is an
elaboration error, so every citation below must resolve; the fixture step also treats warnings as
errors, so no docstring here may draw a Verso suggestion or a `linter.flocqCitations` warning.
`scripts/validate_flocq_source_refs.py` compares the quote with the pinned Flocq source.

The exact hover text, the citation data stored in each docstring, and the error for each kind of
rejected citation are checked by `FloatSpec/Test/FlocqCitations.lean`. It elaborates rejected
citations inside a rollback, which this step does not allow, so it is a module of the compiled
test library. -/

namespace CoqDocRole

set_option doc.verso true in
/--
Cited by Lean name {coq}`FloatSpec.Core.Generic_fmt.round_0`, by Coq name
{coq}`Rnd_DN_pt_monotone`, by the Coq name {coq}`round_opp`, which two Lean ports share, and
from the file {coq_file}`Generic_fmt.v`.

```coq round_0
Theorem round_0 :
  round 0 = 0%R.
```
-/
def cited : Unit := ()

/-- A Markdown docstring may mention `{coq}`, `{coq_file}` and ``{coq}`x` `` as code, and a
Lean block may contain the role, without a citation warning:

```lean
{coq}`inside_another_block`
```
-/
def markdownMentions : Unit := ()

end CoqDocRole

-- A citation resolves in the current scope: at the root, `Bcompare` names two anchored Coq
-- declarations and is ambiguous (an error there), but inside `BinarySingleNaN` it is the
-- anchored `BinarySingleNaN.Bcompare`, and inside `Binary` the anchored `Binary.Bcompare`.
namespace BinarySingleNaN

set_option doc.verso true in
/-- Cites {coq}`Bcompare`, here {lit}`src/IEEE754/BinarySingleNaN.v` line 559. -/
private def citesSingleNaNBcompare : Unit := ()

end BinarySingleNaN

namespace Binary

set_option doc.verso true in
/-- Cites {coq}`Bcompare`, here {lit}`src/IEEE754/Binary.v` line 773. -/
private def citesBinaryBcompare : Unit := ()

end Binary
