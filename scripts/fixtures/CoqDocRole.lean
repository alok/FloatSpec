import FloatSpec.src.Core.Round_pred
import FloatSpec.src.IEEE754.BinarySingleNaN

/-! Regressions for the Flocq docstring extensions defined in `FloatSpecRoles`: the `{coq}` and
`{coq_file}` roles, the `coq` quote block, and the Markdown citation linter.
Run with `lake env lean scripts/fixtures/CoqDocRole.lean`.

Citations that must be rejected are elaborated one command at a time by `probe`, which returns
the messages they produce and then restores the environment, so this file itself elaborates
without errors or warnings. Their docstring text is built inside string literals, so no line of
this file opens a `coq` block that `scripts/validate_flocq_source_refs.py` would try to check. -/

open Lean Elab Command

namespace CoqDocRole

/-- A file at the pinned Flocq commit, spelled out independently of the implementation. -/
def pinned (path : String) : String :=
  "https://gitlab.inria.fr/flocq/flocq/-/blob/7aab8f55bceec0cfafc3b3bc0e77e0dbb5a70c5f/" ++ path

/--
Elaborates `input`, a single command, in the current scope as `lean` would, linters included.
Returns the messages it logs, as `severity: text` (with `lint` for the Flocq citation linter), and
the constants its info trees record; then restores the environment and message log.
-/
def probe (input : String) : CommandElabM (Array String × Array Name) := do
  let stx ← match Parser.runParserCategory (← getEnv) `command input "<probe>" with
    | .ok stx => pure stx
    | .error e => throwError "the probe does not parse: {e}"
  let saved ← get
  try
    modify fun s => { s with messages := {}, infoState := { enabled := true } }
    withReader (fun ctx => { ctx with fileName := "<probe>", fileMap := FileMap.ofString input }) do
      elabCommand stx
      runLinters stx
    let messages ← (← get).messages.toList.toArray.mapM fun m => do
      -- A lint is a warning, or an error when warnings are errors; report it as `lint` either way.
      let kind := if m.data.hasTag (· == `linter.flocqCitations) then "lint" else
        match m.severity with | .error => "error" | .warning => "warning" | .information => "info"
      return s!"{kind}: {← m.data.toString}"
    let consts := (← get).infoState.trees.foldl (init := #[]) fun acc tree =>
      tree.foldInfo (init := acc) fun _ info acc => match info with
        | .ofTermInfo ti => if let .const n _ := ti.expr then acc.push n else acc
        | _ => acc
    return (messages, consts)
  finally
    set saved

/-- Fails unless elaborating `input` logs exactly `expected`. -/
def expectMessages (input : String) (expected : Array String) : CommandElabM Unit := do
  let (messages, _) ← probe input
  unless messages == expected do
    throwError m!"{input}{indentD m!"logged"}{indentD (toString (repr messages))}\
      {indentD m!"instead of"}{indentD (toString (repr expected))}"

/-- A Verso docstring on a throwaway declaration. -/
def versoDoc (doc : String) : String :=
  "set_option doc.verso true in\n/--\n" ++ doc ++ "\n-/\ndef probed : Unit := ()"

/-! ## Citations that resolve -/

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

-- The hover text, exactly. (No expected-message docstring can hold it: GitLab URLs contain `-/`.)
run_cmd do
  let some doc ← findDocString? (← getEnv) ``cited | throwError "`cited` lost its docstring"
  let expected := s!"Cited by Lean name [`round_0`]({pinned "src/Core/Generic_fmt.v#L763"}), \
    by Coq name\n[`Rnd_DN_pt_monotone`]({pinned "src/Core/Round_pred.v#L103"}), by the Coq \
    name [`round_opp`]({pinned "src/Core/Generic_fmt.v#L852"}), which two Lean ports share, \
    and\nfrom the file [`src/Core/Generic_fmt.v`]({pinned "src/Core/Generic_fmt.v"}).\n\n\
    Flocq [`round_0`]({pinned "src/Core/Generic_fmt.v#L763"}) in `src/Core/Generic_fmt.v`:\n\n```coq\n\
    Theorem round_0 :\n  round 0 = 0%R.\n```"
  unless doc == expected do
    throwError m!"the hover changed:{indentD doc}\nexpected:{indentD expected}"

-- Those links are the anchors' own URLs, as recorded by `@[flocq_source]`.
run_cmd do
  let env ← getEnv
  for (declName, path) in [(``FloatSpec.Core.Generic_fmt.round_0, "src/Core/Generic_fmt.v#L763"),
      (``FloatSpec.Core.Round_pred.Rnd_DN_pt_monotone, "src/Core/Round_pred.v#L103"),
      (``FloatSpec.Core.Generic_fmt.round_opp, "src/Core/Generic_fmt.v#L852"),
      (``FloatSpec.Core.Generic_fmt.roundR_opp, "src/Core/Generic_fmt.v#L852")] do
    let url := (FloatSpec.Linter.CoqSource.sourceRef? env declName).map
      FloatSpec.Linter.CoqSource.sourceUrl
    unless url == some (pinned path) do
      throwError m!"`{declName}` is anchored at {url}, not {pinned path}"

/-- The recorded anchor of a citation or quote: Coq name, path, line, and sorted Lean ports. -/
def summary (a : FloatSpec.Roles.FlocqAnchor) : String × String × Nat × List Name :=
  (a.coqName, a.path, a.line, (a.leanNames.qsort Name.quickLt).toList)

-- Tools recover each citation and quote, with the Lean ports that chose it, from the docstring
-- data. `round_opp` is one target whose two Lean ports are both recorded.
run_cmd do
  let some (.inr doc) ← findInternalDocString? (← getEnv) ``cited
    | throwError "`cited` has no Verso docstring"
  let citations := (FloatSpec.Roles.docData FloatSpec.Roles.FlocqAnchor doc).map summary
  let expected := #[
    ("round_0", "src/Core/Generic_fmt.v", 763, [``FloatSpec.Core.Generic_fmt.round_0]),
    ("Rnd_DN_pt_monotone", "src/Core/Round_pred.v", 103,
      [``FloatSpec.Core.Round_pred.Rnd_DN_pt_monotone]),
    ("round_opp", "src/Core/Generic_fmt.v", 852,
      ([``FloatSpec.Core.Generic_fmt.roundR_opp, ``FloatSpec.Core.Generic_fmt.round_opp].toArray.qsort
        Name.quickLt).toList)]
  unless citations == expected do
    throwError m!"recorded citations {repr citations} differ from {repr expected}"
  let quotes := FloatSpec.Roles.docData FloatSpec.Roles.FlocqQuote doc
  -- The quote records the line of its fence, where the validator looks for it.
  let lines := (← IO.FS.readFile (← getFileName)).splitOn "\n"
  let some fence := (lines.findIdx? (· == "```coq round_0")).map (· + 1)
    | throwError "no quote fence in this file"
  let #[quote] := quotes | throwError m!"expected one quote, found {quotes.size}"
  unless summary quote.anchor == ("round_0", "src/Core/Generic_fmt.v", 763,
      [``FloatSpec.Core.Generic_fmt.round_0]) && quote.cited == "round_0" &&
      quote.code == "Theorem round_0 :\n  round 0 = 0%R.\n" && quote.leanLine == fence do
    throwError m!"recorded quote {repr (summary quote.anchor)} {quote.cited} at \
      {quote.leanLine}:{indentD quote.code}"
  -- A reader that does not know `FlocqQuote` falls back to the block's content: the linked
  -- header, then the quoted source as a code block.
  let fallback : Array (Array (Doc.Block ElabInline ElabBlock)) := doc.text.filterMap fun
    | .other (.custom val) content =>
      if (val.get? FloatSpec.Roles.FlocqQuote).isSome then some content else none
    | _ => none
  match fallback with
  | #[#[Doc.Block.para header, Doc.Block.code source]] =>
    unless source == quote.code && header.size == 5 do
      throwError m!"the quote block's fallback content changed:{indentD source}"
  | _ => throwError "the quote block's fallback content is not a header and a code block"

end CoqDocRole

-- Resolution follows the current namespace: `Bcompare` names two Coq declarations, but inside
-- `BinarySingleNaN` it is the Lean `BinarySingleNaN.Bcompare`, and inside `Binary`
-- `Binary.Bcompare`.
namespace BinarySingleNaN
run_cmd do
  let (messages, consts) ← CoqDocRole.probe (CoqDocRole.versoDoc "{coq}`Bcompare`")
  unless messages.isEmpty && consts.contains ``BinarySingleNaN.Bcompare do
    throwError m!"{messages} {consts}"
end BinarySingleNaN

namespace Binary
run_cmd do
  let (messages, consts) ← CoqDocRole.probe (CoqDocRole.versoDoc "{coq}`Bcompare`")
  unless messages.isEmpty && consts.contains ``Binary.Bcompare do
    throwError m!"{messages} {consts}"
end Binary

namespace CoqDocRole

-- A citation or quote with one Lean port records it for hover and go-to-definition; `round_opp`,
-- with two ports, records neither.
run_cmd do
  let (messages, consts) ← probe (versoDoc ("{coq}`Rnd_DN_pt_monotone` {coq}`round_opp`\n\n" ++
    "```coq round_0\nTheorem round_0 :\n  round 0 = 0%R.\n```"))
  unless messages.isEmpty do throwError m!"{messages}"
  for c in [``FloatSpec.Core.Round_pred.Rnd_DN_pt_monotone, ``FloatSpec.Core.Generic_fmt.round_0] do
    unless consts.contains c do throwError m!"no hover information for `{c}` in {consts}"
  for c in [``FloatSpec.Core.Generic_fmt.round_opp, ``FloatSpec.Core.Generic_fmt.roundR_opp] do
    if consts.contains c then throwError m!"`round_opp` should not pick the port `{c}`"

/-! ## Citations that must not elaborate -/

run_cmd do
  expectMessages (versoDoc "{coq}`Rnd_DN_pt_monotnoe`") #[
    "error: No pinned Flocq anchor matches `Rnd_DN_pt_monotnoe`. Cite a Lean declaration that \
    carries `@[flocq_source]`, or a Coq name that exactly one anchor declares.\n\
    \n\
    Hint: Cite a nearby anchor:\n  \
    • {coq}`Rnd_DN_pt_monoto̲no̵e`\n  \
    • {coq}`Rnd_D̵N_pt_monoto̲no̵e`"]

-- The root `Bcompare` is an unanchored Lean declaration, and two anchored Coq declarations
-- are named `Bcompare`.
run_cmd do
  expectMessages (versoDoc "{coq}`Bcompare`") #[
    "error: `Bcompare` resolves to the Lean declaration `Bcompare`, which has no \
    `@[flocq_source]` anchor, but it is also the Coq name of\n  \
    src/IEEE754/Binary.v:773 `Bcompare` (Lean: Binary.Bcompare)\n  \
    src/IEEE754/BinarySingleNaN.v:559 `Bcompare` (Lean: BinarySingleNaN.Bcompare)\n\
    Cite the anchored Lean port to say which one you mean.\n\
    \n\
    Hint: Cite the anchored port instead:\n  \
    • {coq}`Bi̲n̲a̲r̲y̲.̲B̲compare`\n  \
    • {coq}`Bi̲n̲a̲r̲y̲S̲i̲n̲g̲l̲e̲N̲a̲N̲.̲B̲compare`"]

run_cmd do
  expectMessages (versoDoc "{coq}`Nat.add`") #[
    "error: `Nat.add` is the Lean declaration `Nat.add`, which has no `@[flocq_source]` anchor, \
    and no anchored Coq declaration is named `Nat.add`. Cite an anchored declaration, or anchor \
    this one with `@[flocq_source \"src/…/File.v\" LINE \"coq_name\"]` if it ports Flocq."]

run_cmd do
  expectMessages (versoDoc "{coq}`validB754`") #[
    "error: `validB754` is the Lean declaration `validB754` (a Lean-only `@[flocq_local]` \
    declaration: Propositional validity adapter for the raw B754 compatibility carrier), which \
    has no `@[flocq_source]` anchor, and no anchored Coq declaration is named `validB754`. Cite \
    an anchored declaration."]

-- The Lean `SF2B'` at the root is a Lean-only helper; the Coq `SF2B'` is ported by
-- `BinarySingleNaN.SF2B'`. The bare name could mean either, so it is rejected.
run_cmd do
  expectMessages (versoDoc "{coq}`SF2B'`") #[
    "error: `SF2B'` resolves to the Lean declaration `SF2B'` (a Lean-only `@[flocq_local]` \
    declaration: raw B754 view of SF2B'; faithful port is BinarySingleNaN.SF2B'), which has no \
    `@[flocq_source]` anchor, but it is also the Coq name of\n  \
    src/IEEE754/BinarySingleNaN.v:73 `SF2B'` (Lean: BinarySingleNaN.SF2B')\n\
    Cite the anchored Lean port to say which one you mean.\n\
    \n\
    Hint: Cite the anchored port instead:\n  \
    {̵c̵o̵q̵}̵`̵S̵F̵2̵B̵'̵`̵{̲c̲o̲q̲}̲`̲B̲i̲n̲a̲r̲y̲S̲i̲n̲g̲l̲e̲N̲a̲N̲.̲S̲F̲2̲B̲'̲`̲"]

namespace Shadow
/-- An unanchored Lean declaration that shares a Coq name. -/
def round_0 : Nat := 0

run_cmd do
  expectMessages (versoDoc "{coq}`round_0`") #[
    "error: `round_0` resolves to the Lean declaration `CoqDocRole.Shadow.round_0`, which has no \
    `@[flocq_source]` anchor, but it is also the Coq name of\n  \
    src/Core/Generic_fmt.v:763 `round_0` (Lean: FloatSpec.Core.Generic_fmt.round_0)\n\
    Cite the anchored Lean port to say which one you mean.\n\
    \n\
    Hint: Cite the anchored port instead:\n  \
    {̵c̵o̵q̵}̵`̵r̵o̵u̵n̵d̵_̵0̵`̵{̲c̲o̲q̲}̲`̲F̲l̲o̲a̲t̲S̲p̲e̲c̲.̲C̲o̲r̲e̲.̲G̲e̲n̲e̲r̲i̲c̲_̲f̲m̲t̲.̲r̲o̲u̲n̲d̲_̲0̲`̲"]

-- A docstring can cite its own anchored declaration while that declaration is still being
-- elaborated, even with the unanchored `Shadow.round_0` in scope.
namespace Inner
run_cmd do
  let (messages, _) ← probe ("set_option doc.verso true in\n/-- {coq}`round_0` -/\n" ++
    "@[flocq_source \"src/Core/Generic_fmt.v\" 763 \"round_0\"]\ntheorem round_0 : True := trivial")
  unless messages.isEmpty do throwError m!"{messages}"
end Inner
end Shadow

run_cmd do
  expectMessages (versoDoc "{coq_file}`Generic_fmt.vv`") #[
    "error: `Generic_fmt.vv` is not a Rocq source file of Flocq at the pinned commit \
    7aab8f55bceec0cfafc3b3bc0e77e0dbb5a70c5f.\n\
    \n\
    Hint: Use a pinned Flocq file:\n  \
    {̵c̵o̵q̵_̵f̵i̵l̵e̵}̵`̵G̵e̵n̵e̵r̵i̵c̵_̵f̵m̵t̵.̵v̵v̵`̵{̲c̲o̲q̲_̲f̲i̲l̲e̲}̲`̲s̲r̲c̲/̲C̲o̲r̲e̲/̲G̲e̲n̲e̲r̲i̲c̲_̲f̲m̲t̲.̲v̲`̲"]

-- A quote's first line must declare the anchored name, as the anchored line does.
run_cmd do
  expectMessages (versoDoc "```coq round_0\nLemma round_0_misquoted : True.\n```") #[
    "error: A Flocq quote must begin at its anchored line src/Core/Generic_fmt.v:763, which \
    declares `round_0` (for example `Theorem round_0 :`), but this quote begins with\n  \
    Lemma round_0_misquoted : True."]

run_cmd do
  expectMessages (versoDoc
    "```coq round_0\n(* round_0 *) Theorem round_0 :\n  round 0 = 0%R.\n```") #[
    "error: A Flocq quote must begin at its anchored line src/Core/Generic_fmt.v:763, which \
    declares `round_0` (for example `Theorem round_0 :`), but this quote begins with\n  \
    (* round_0 *) Theorem round_0 :"]

run_cmd do
  expectMessages (versoDoc "```coq\nTheorem round_0 :\n  round 0 = 0%R.\n```") #[
    "error: Missing positional argument `flocqAnchor`"]

-- In a Markdown docstring the same syntax would be unchecked literal text. The linter flags
-- the role applied to code, and a `coq` fence even inside a list item, but not the role's name
-- written as code.
run_cmd do
  expectMessages ("/-- A Markdown {coq}`round_0` and `{coq}` as code. -/\n" ++
      "def markdown : Unit := ()") #[
    "lint: This Markdown docstring uses the `{coq}` role, which only a Verso docstring \
    checks: here it is literal text, and a misspelled or unanchored citation goes unnoticed. \
    Turn on Verso docstrings for it with `set_option doc.verso true in` (then each citation must \
    name a pinned anchor), or write the name as plain code.\n\
    \n\
    Hint: Check the citations in a Verso docstring:\n  \
    [apply] set_option doc.verso true in\n  \
    /--\n\
    \n\
    Note: This linter can be disabled with `set_option linter.flocqCitations false`"]

run_cmd do
  expectMessages ("/--\n* ``` coq round_0\n  Theorem round_0 :\n  ```\n-/\n" ++
      "def markdownQuote : Unit := ()") #[
    "lint: This Markdown docstring uses a `coq` quote block, which only a Verso docstring \
    checks: here it is literal text, and a misspelled or unanchored citation goes unnoticed. \
    Turn on Verso docstrings for it with `set_option doc.verso true in` (then each citation must \
    name a pinned anchor), or write the name as plain code.\n\
    \n\
    Hint: Check the citations in a Verso docstring:\n  \
    [apply] set_option doc.verso true in\n  \
    /--\n\
    \n\
    Note: This linter can be disabled with `set_option linter.flocqCitations false`"]

run_cmd do
  expectMessages ("/-- Mentions `{coq}`, `{coq_file}` and ``{coq}`x` `` only as code.\n\n" ++
      "```lean\n{coq}`inside_another_block`\n```\n-/\ndef markdownMentions : Unit := ()") #[]

end CoqDocRole
