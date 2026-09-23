import FloatSpec.src.Core.Round_pred
import FloatSpec.src.IEEE754.BinarySingleNaN

/-! Regressions for the Flocq docstring extensions defined in `FloatSpecRoles`:
the `{coq}` and `{coq_file}` roles and the `coq` quote block.
Run with `lake env lean scripts/fixtures/CoqDocRole.lean`. -/

open Lean Elab Command

namespace CoqDocRole

/-! ## Citations that resolve -/

set_option doc.verso true in
/--
Cited by Lean name {coq}`FloatSpec.Core.Generic_fmt.round_0`, by Coq name
{coq}`Rnd_DN_pt_monotone`, and by a Coq name that two Lean ports share, {coq}`B2R_inj`, from
the file {coq_file}`Generic_fmt.v`.

```coq round_0
Theorem round_0 :
  round 0 = 0%R.
```
-/
def cited : Unit := ()

/-- A file at the pinned Flocq commit, spelled out independently of the implementation. -/
def pinned (path : String) : String :=
  "https://gitlab.inria.fr/flocq/flocq/-/blob/7aab8f55bceec0cfafc3b3bc0e77e0dbb5a70c5f/" ++ path

-- The hover text, exactly. (A `#guard_msgs` docstring cannot hold it: GitLab URLs contain `-/`.)
run_cmd do
  let some doc ← findDocString? (← getEnv) ``cited | throwError "`cited` lost its docstring"
  let expected := s!"Cited by Lean name [`round_0`]({pinned "src/Core/Generic_fmt.v#L763"}), \
    by Coq name\n[`Rnd_DN_pt_monotone`]({pinned "src/Core/Round_pred.v#L103"}), and by a Coq \
    name that two Lean ports share, [`B2R_inj`]({pinned "src/IEEE754/Binary.v#L392"}), from\n\
    the file [`src/Core/Generic_fmt.v`]({pinned "src/Core/Generic_fmt.v"}).\n\n\
    Flocq [`round_0`]({pinned "src/Core/Generic_fmt.v#L763"}) in `src/Core/Generic_fmt.v`:\n\n\
    ```coq\nTheorem round_0 :\n  round 0 = 0%R.\n```"
  unless doc == expected do
    throwError m!"the hover changed:{indentD doc}\nexpected:{indentD expected}"

-- Those links are the anchors' own URLs, as recorded by `@[flocq_source]`.
run_cmd do
  let env ← getEnv
  for (declName, path) in [(``FloatSpec.Core.Generic_fmt.round_0, "src/Core/Generic_fmt.v#L763"),
      (``FloatSpec.Core.Round_pred.Rnd_DN_pt_monotone, "src/Core/Round_pred.v#L103"),
      (``B2R_inj, "src/IEEE754/Binary.v#L392")] do
    let url := (FloatSpec.Linter.CoqSource.sourceRef? env declName).map
      FloatSpec.Linter.CoqSource.sourceUrl
    unless url == some (pinned path) do
      throwError m!"`{declName}` is anchored at {url}, not {pinned path}"

/-- Every Flocq anchor recorded as structured data in a Verso docstring, in document order. -/
partial def recordedAnchors (doc : VersoDocString) : Array (String × String × Nat) :=
  let rec inl : Doc.Inline ElabInline → Array (String × String × Nat)
    | .other (.custom val) content =>
      let here := match val.get? FloatSpec.Roles.FlocqAnchor with
        | some a => #[(a.coqName, a.path, a.line)]
        | none => #[]
      here ++ content.flatMap inl
    | .other _ content | .concat content | .emph content | .bold content | .link content _
    | .footnote _ content => content.flatMap inl
    | _ => #[]
  let rec blk : Doc.Block ElabInline ElabBlock → Array (String × String × Nat)
    | .other (.custom val) content =>
      let here := match val.get? FloatSpec.Roles.FlocqQuote with
        | some q => #[(q.anchor.coqName, q.anchor.path, q.anchor.line)]
        | none => #[]
      here ++ content.flatMap blk
    | .para content => content.flatMap inl
    | .other _ content | .concat content | .blockquote content => content.flatMap blk
    | .ul items | .ol _ items => items.flatMap (·.contents.flatMap blk)
    | .dl items => items.flatMap fun item => item.term.flatMap inl ++ item.desc.flatMap blk
    | .code _ => #[]
  doc.text.flatMap blk

-- Tools can recover each citation, and the quote, without parsing Markdown.
run_cmd do
  let some (.inr doc) ← findInternalDocString? (← getEnv) ``cited
    | throwError "`cited` has no Verso docstring"
  let found := recordedAnchors doc
  let expected := #[("round_0", "src/Core/Generic_fmt.v", 763),
    ("Rnd_DN_pt_monotone", "src/Core/Round_pred.v", 103), ("B2R_inj", "src/IEEE754/Binary.v", 392),
    ("round_0", "src/Core/Generic_fmt.v", 763)]
  unless found == expected do
    throwError m!"recorded anchors {repr found} differ from {repr expected}"

/-! ## Citations that must not elaborate -/

/--
error: No pinned Flocq anchor matches `Rnd_DN_pt_monotnoe`. Cite a Lean declaration that carries `@[flocq_source]`, or a Coq name that exactly one anchor declares.

Hint: Cite a nearby anchor:
  • {coq}`Rnd_DN_pt_monoto̲no̵e`
  • {coq}`Rnd_D̵N_pt_monoto̲no̵e`
-/
#guard_msgs in
set_option doc.verso true in
/-- {coq}`Rnd_DN_pt_monotnoe` -/
def misspelled : Unit := ()

/--
error: `Bcompare` names 2 different pinned Flocq declarations:
  src/IEEE754/Binary.v:773 `Bcompare` (Lean: Binary.Bcompare)
  src/IEEE754/BinarySingleNaN.v:559 `Bcompare` (Lean: BinarySingleNaN.Bcompare)
Cite one of their Lean declarations to choose.

Hint: Cite the Lean declaration instead:
  • {coq}`Bi̲n̲a̲r̲y̲.̲B̲compare`
  • {coq}`Bi̲n̲a̲r̲y̲S̲i̲n̲g̲l̲e̲N̲a̲N̲.̲B̲compare`
-/
#guard_msgs in
set_option doc.verso true in
/-- {coq}`Bcompare` -/
def ambiguous : Unit := ()

/--
error: `Nat.add` is the Lean declaration `Nat.add`, which has no `@[flocq_source]` anchor, and no anchored Coq declaration is named `Nat.add`. Cite an anchored declaration, or anchor this one with `@[flocq_source "src/…/File.v" LINE "coq_name"]` if it ports Flocq.
-/
#guard_msgs in
set_option doc.verso true in
/-- {coq}`Nat.add` -/
def unanchored : Unit := ()

/--
error: `Generic_fmt.vv` is not a Rocq source file of Flocq at the pinned commit 7aab8f55bceec0cfafc3b3bc0e77e0dbb5a70c5f.

Hint: Use a pinned Flocq file:
  {̵c̵o̵q̵_̵f̵i̵l̵e̵}̵`̵G̵e̵n̵e̵r̵i̵c̵_̵f̵m̵t̵.̵v̵v̵`̵{̲c̲o̲q̲_̲f̲i̲l̲e̲}̲`̲s̲r̲c̲/̲C̲o̲r̲e̲/̲G̲e̲n̲e̲r̲i̲c̲_̲f̲m̲t̲.̲v̲`̲
-/
#guard_msgs in
set_option doc.verso true in
/-- {coq_file}`Generic_fmt.vv` -/
def missingFile : Unit := ()

/--
error: A Flocq quote must begin at its anchored line src/Core/Generic_fmt.v:763, which declares `round_0`, but this quote begins with
  Lemma round_0_misquoted : True.
-/
#guard_msgs in
set_option doc.verso true in
/--
```coq round_0
Lemma round_0_misquoted : True.
```
-/
def misquoted : Unit := ()

/--
error: Missing positional argument `flocqAnchor`
-/
#guard_msgs in
set_option doc.verso true in
/--
```coq
Theorem round_0 :
  round 0 = 0%R.
```
-/
def unanchoredQuote : Unit := ()

end CoqDocRole
