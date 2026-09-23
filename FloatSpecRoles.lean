module

public meta import Lean
public meta import Lean.Data.EditDistance
public meta import FloatSpec.Linter.CoqSourceLinter

/-!
# Flocq citations in Verso docstrings

These docstring extensions use Lean's built-in Verso docstrings, so a file (or a single
declaration) opts in with `set_option doc.verso true`. The project default stays `false`.

* The role `coq` takes one code element naming either a Lean declaration that carries
  `@[flocq_source "src/…/File.v" LINE "coq_name"]` or a Coq name that exactly one anchored
  Coq declaration has. It renders the Coq name as inline code linked to that line at the
  pinned Flocq commit, and records the anchor as structured docstring data.
* The role `coq_file` takes a Flocq source path such as `src/Core/Generic_fmt.v`, or a unique
  suffix such as `Generic_fmt.v`, and links the whole file at the pinned commit.
* A code block whose info string is `coq` followed by an anchor name quotes that declaration's
  Rocq source, beginning at its anchored line. `scripts/validate_flocq_source_refs.py` checks
  every such quote verbatim against the pinned checkout.

Unknown, unanchored, and ambiguous citations are elaboration errors that name the candidates
and suggest replacements; nothing silently degrades to plain text.
-/

open Lean Elab Term Doc
open scoped Lean.Doc.Syntax
open FloatSpec.Linter.CoqSource

public meta section

namespace FloatSpec.Roles

/-- A pinned Flocq declaration cited from a docstring. It is stored in the docstring as
custom data, so tools can recover every citation structurally. -/
structure FlocqAnchor where
  /-- The Coq declaration's name. -/
  coqName : String
  /-- The Flocq source file, relative to the Flocq repository root. -/
  path : String
  /-- The 1-based line that declares `coqName` in `path`. -/
  line : Nat
  /-- The Lean declarations that selected this anchor. -/
  leanNames : Array Name
  deriving TypeName

/-- The pinned GitLab URL of an anchor's line. -/
def FlocqAnchor.url (anchor : FlocqAnchor) : String :=
  sourceUrl { declName := .anonymous, path := anchor.path, line := anchor.line,
              coqName := anchor.coqName }

/-- A quotation of the Flocq source that begins at an anchored line. -/
structure FlocqQuote where
  /-- The quoted declaration. -/
  anchor : FlocqAnchor
  /-- The quoted Rocq source text. -/
  code : String
  deriving TypeName

/-- The outcome of resolving the text of a Flocq citation. -/
inductive Resolution where
  /-- Exactly one Coq declaration. -/
  | found (anchor : FlocqAnchor)
  /-- Several distinct Coq declarations. -/
  | ambiguous (anchors : Array FlocqAnchor)
  /-- Lean declarations without an anchor, and no Coq declaration of that name. -/
  | unanchored (declNames : Array Name)
  /-- Neither a Lean declaration nor an anchored Coq name. -/
  | unknown

/-- Groups source references by the Coq declaration they point at, in source order. -/
def groupTargets (refs : Array SourceRef) : Array FlocqAnchor := Id.run do
  let mut out : Array FlocqAnchor := #[]
  let mut index : Std.HashMap (String × Nat × String) Nat := {}
  for ref in refs do
    match index[(ref.path, ref.line, ref.coqName)]? with
    | some i =>
      out := out.modify i fun a =>
        if a.leanNames.contains ref.declName then a
        else { a with leanNames := a.leanNames.push ref.declName }
    | none =>
      index := index.insert (ref.path, ref.line, ref.coqName) out.size
      out := out.push { coqName := ref.coqName, path := ref.path, line := ref.line,
                        leanNames := #[ref.declName] }
  return out.qsort fun a b => a.path < b.path || (a.path == b.path && a.line < b.line)

/--
Resolves citation text against the pinned anchors visible in `env`.

A Lean declaration name (resolved like an identifier in the current scope) takes precedence.
Otherwise the text is a Coq name, which must be declared by exactly one anchored Coq
declaration. Several Lean ports of one Coq declaration are one target, not an ambiguity.
-/
def resolveAnchor (env : Environment) (opts : Options) (currNamespace : Name)
    (openDecls : List OpenDecl) (text : String) : Resolution := Id.run do
  let refs := sourceExt.getState env
  let leanName := text.toName
  let leanCandidates : Array Name :=
    if leanName.isAnonymous then #[]
    else (ResolveName.resolveGlobalName env opts currNamespace openDecls leanName).toArray.filterMap
      fun (n, fields) => if fields.isEmpty && env.contains n then some n else none
  let anchored := refs.filter fun ref => leanCandidates.contains ref.declName
  let targets := groupTargets (if anchored.isEmpty then refs.filter (·.coqName == text) else anchored)
  if h : targets.size = 1 then
    return .found targets[0]
  else if targets.isEmpty then
    return if leanCandidates.isEmpty then .unknown else .unanchored leanCandidates
  else
    return .ambiguous targets

/-- Close spellings of anchored citations, using a Lean name whenever the Coq name is ambiguous. -/
def nearMisses (env : Environment) (text : String) (limit : Nat := 4) : Array String := Id.run do
  let targets := groupTargets (sourceExt.getState env)
  let mut counts : Std.HashMap String Nat := {}
  for target in targets do
    counts := counts.insert target.coqName (counts.getD target.coqName 0 + 1)
  let cutoff := if text.length < 5 then 1 else if text.length < 8 then 2 else 3
  let mut scored : Array (Nat × String) := #[]
  for target in targets do
    if let some d := EditDistance.levenshtein text target.coqName cutoff then
      if counts.getD target.coqName 0 == 1 then
        scored := scored.push (d, target.coqName)
      else
        for n in target.leanNames do scored := scored.push (d, n.toString)
  let sorted := scored.qsort fun a b => a.1 < b.1 || (a.1 == b.1 && a.2 < b.2)
  let mut out : Array String := #[]
  for (_, s) in sorted do
    if out.size < limit && !out.contains s then out := out.push s
  return out

/-- Identifier-like tokens of a line of Rocq source. -/
def identTokens (line : String) : Array String := Id.run do
  let mut tokens : Array String := #[]
  let mut current := ""
  for c in line.toList do
    if c.isAlphanum || c == '_' || c == '\'' then
      current := current.push c
    else if !current.isEmpty then
      tokens := tokens.push current
      current := ""
  if !current.isEmpty then tokens := tokens.push current
  return tokens

/-- The single code element given to a role. -/
def codeArg (xs : TSyntaxArray `inline) : DocM StrLit := do
  let mut codes : Array StrLit := #[]
  for stx in xs do
    match stx with
    | `(inline|code($s)) => codes := codes.push s
    | `(inline|$s:str) =>
      unless s.getString.all (·.isWhitespace) do
        throwErrorAt stx "Expected a single code element, such as `round_0` in backticks"
    | other => throwErrorAt other "Expected a single code element, such as `round_0` in backticks"
  if h : codes.size = 1 then return codes[0]
  else throwError "Expected exactly one code element, such as `round_0` in backticks"

/-- One line describing a candidate anchor in an error message. -/
def describe (anchor : FlocqAnchor) : MessageData :=
  m!"{anchor.path}:{anchor.line} `{anchor.coqName}` \
    (Lean: {", ".intercalate (anchor.leanNames.toList.map toString)})"

/-- Suggest replacements for the citation at `ref`, if there are any. -/
def replacements (ref : Syntax) (title : MessageData) (spellings : Array String)
    (render : String → String) : DocM MessageData := do
  if spellings.isEmpty then return m!""
  let suggestions : Array Meta.Hint.Suggestion :=
    spellings.map fun s => { suggestion := .string (render s) }
  MessageData.hint title suggestions (ref? := some ref)

/--
Resolves citation text or throws an actionable error at `ref`. `render` turns a suggested
spelling into replacement text for `ref`.
-/
def resolveOrThrow (text : String) (ref : Syntax) (render : String → String) :
    DocM FlocqAnchor := do
  let env ← getEnv
  match resolveAnchor env (← getOptions) (← getCurrNamespace) (← getOpenDecls) text with
  | .found anchor => return anchor
  | .ambiguous anchors =>
    let mut spellings : Array String := #[]
    for anchor in anchors do
      for n in anchor.leanNames do
        spellings := spellings.push (← unresolveNameGlobal n).toString
    let hint ← replacements ref m!"Cite the Lean declaration instead:" spellings render
    throwErrorAt ref m!"`{text}` names {anchors.size} different pinned Flocq declarations:\
      {indentD (MessageData.joinSep (anchors.toList.map describe) Format.line)}\n\
      Cite one of their Lean declarations to choose.{hint}"
  | .unanchored declNames =>
    let hint ← replacements ref m!"Cite an anchored declaration:" (nearMisses env text) render
    throwErrorAt ref m!"`{text}` is the Lean declaration `{declNames[0]!}`, which has no \
      `@[flocq_source]` anchor, and no anchored Coq declaration is named `{text}`. \
      Cite an anchored declaration, or anchor this one with \
      `@[flocq_source \"src/…/File.v\" LINE \"coq_name\"]` if it ports Flocq.{hint}"
  | .unknown =>
    let hint ← replacements ref m!"Cite a nearby anchor:" (nearMisses env text) render
    throwErrorAt ref m!"No pinned Flocq anchor matches `{text}`. Cite a Lean declaration that \
      carries `@[flocq_source]`, or a Coq name that exactly one anchor declares.{hint}"

/-- The line introducing a Flocq quote: the linked Coq name and its source file. -/
def quoteHeader (anchor : FlocqAnchor) : Array (Inline ElabInline) :=
  #[.text "Flocq ", .link #[.code anchor.coqName] anchor.url, .text " in ", .code anchor.path,
    .text ":"]

/-- Markdown for a Flocq quote: a link to the anchor, then the Rocq source. -/
@[doc_block_md]
def FlocqQuote.toMarkdown : BlockMdRendererOf FlocqQuote := fun goI _goB quote _content => do
  let anchor := quote.anchor
  let header ← goI (.concat (quoteHeader anchor))
  let body := (quote.code.splitOn "\n").toArray
  let body := if body.back? == some "" then body.pop else body
  return header ++ #["", "```coq"] ++ body ++ #["```"]

end FloatSpec.Roles

open FloatSpec.Roles

/--
Cites a pinned Flocq declaration: `{coq}` followed by a code element with a Lean declaration
carrying `@[flocq_source]` (such as `FloatSpec.Core.Generic_fmt.round_0`) or a Coq name
declared by exactly one anchor (such as `Rnd_DN_pt_monotone`). Renders the Coq name linked to
its line at the pinned commit. Unknown, unanchored, and ambiguous names are errors.
-/
@[doc_role]
def coq (xs : TSyntaxArray `inline) : DocM (Inline ElabInline) := do
  let code ← codeArg xs
  let text := code.getString.trimAscii.toString
  let anchor ← resolveOrThrow text (← getRef) fun s => "{coq}`" ++ s ++ "`"
  if let #[declName] := anchor.leanNames then addConstInfo code declName
  return .custom anchor #[.link #[.code anchor.coqName] anchor.url]

/--
Links a whole Flocq source file at the pinned commit: `{coq_file}` followed by a code element with
a path such as `src/Core/Generic_fmt.v`, or a unique suffix such as `Generic_fmt.v`.
-/
@[doc_role]
def coq_file (xs : TSyntaxArray `inline) : DocM (Inline ElabInline) := do
  let code ← codeArg xs
  let text := code.getString.trimAscii.toString
  let found := flocqSourceFiles.filter fun path => path == text || path.endsWith ("/" ++ text)
  if h : found.size = 1 then
    return .link #[.code found[0]] (sourceFileUrl found[0])
  let cutoff := if text.length < 8 then 2 else 3
  let near := flocqSourceFiles.filter fun path =>
    (EditDistance.levenshtein text path cutoff).isSome ||
      (EditDistance.levenshtein text ((path.splitOn "/").getLast!) cutoff).isSome
  let hint ← replacements (← getRef) m!"Use a pinned Flocq file:" (if found.isEmpty then near else found)
    fun s => "{coq_file}`" ++ s ++ "`"
  if found.isEmpty then
    throwErrorAt code m!"`{text}` is not a Rocq source file of Flocq at the pinned commit \
      {flocqCommit}.{hint}"
  else
    throwErrorAt code m!"`{text}` matches {found.size} Flocq source files; give the full path.{hint}"

/--
Quotes the Rocq source of a pinned Flocq declaration. The info string is `coq` followed by
the same anchor name the `{coq}` role accepts, and the quote must begin at the anchored
line. `scripts/validate_flocq_source_refs.py` checks each quote verbatim against the pinned
checkout.
-/
@[doc_code_block coq]
def coqQuote (flocqAnchor : Ident) (code : StrLit) : DocM (Block ElabInline ElabBlock) := do
  let text := flocqAnchor.getId.toString (escape := false)
  let anchor ← resolveOrThrow text flocqAnchor id
  let source := code.getString
  let firstLine := (source.splitOn "\n").headD ""
  unless (identTokens firstLine).contains anchor.coqName do
    throwErrorAt code m!"A Flocq quote must begin at its anchored line \
      {anchor.path}:{anchor.line}, which declares `{anchor.coqName}`, but this quote begins with\
      {indentD firstLine}"
  if let #[declName] := anchor.leanNames then addConstInfo flocqAnchor declName
  return .custom ({ anchor, code := source } : FlocqQuote) #[
    .para (quoteHeader anchor), .code source]

end
