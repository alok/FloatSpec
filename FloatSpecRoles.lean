module

public meta import Lean
public meta import Lean.Data.EditDistance
public meta import FloatSpec.Linter.CoqSourceLinter

/-!
# Flocq citations in Verso docstrings

These docstring extensions use Lean's built-in Verso docstrings, so a file (or a single
declaration) opts in with `set_option doc.verso true`. The project default stays `false`, and the
`linter.flocqCitations` linter (in `FloatSpec.Linter.CoqSourceLinter`) rejects this syntax in a
Markdown docstring, where it would render as unchecked literal text.

* The role `coq` takes one code element naming either a Lean declaration that carries
  `@[flocq_source "src/…/File.v" LINE "coq_name"]` or a Coq name that exactly one anchored
  Coq declaration has. It renders the Coq name as inline code linked to that line at the
  pinned Flocq commit, and records the anchor as structured docstring data.
* The role `coq_file` takes a Flocq source path such as `src/Core/Generic_fmt.v`, or a unique
  suffix such as `Generic_fmt.v`, and links the whole file at the pinned commit.
* A code block whose info string is `coq` followed by an anchor name quotes that declaration's
  Rocq source. Its first line must declare the anchored name, as the anchored line does. The
  quote, with the anchor it resolved to, is stored in the docstring, and
  `scripts/validate_flocq_source_refs.py` reads that compiled data back and checks it verbatim
  against the pinned checkout: from the anchored line through the end of the declaration's first
  sentence, unless a final line `...` marks the quote as shortened.

Unknown, unanchored, ambiguous and shadowed citations are elaboration errors that name the
candidates and suggest replacements; nothing silently degrades to plain text.
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
  /-- The anchor name as written after `coq` in the block's info string. -/
  cited : String
  /-- The 1-based line of the Lean source that opens the block, or `0` if it has no position. -/
  leanLine : Nat
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
  /-- Lean declarations without an anchor in scope, and also anchored Coq declarations with that
  name: the citation could mean either. -/
  | shadowed (declNames : Array Name) (anchors : Array FlocqAnchor)
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

The text is first read as a Lean declaration name, resolved like an identifier in the current
scope (a docstring is elaborated after its own declaration is added, so it can cite itself). The
anchored declarations it resolves to decide the target. Only when it resolves to no anchored Lean
declaration is the text read as a Coq name, which must be declared by exactly one anchored Coq
declaration; several Lean ports of one Coq declaration are one target, not an ambiguity. If the
text also resolves to an unanchored Lean declaration, the citation is `shadowed`, and the author
must name the port by its Lean name.
-/
def resolveAnchor (env : Environment) (opts : Options) (currNamespace : Name)
    (openDecls : List OpenDecl) (text : String) : Resolution := Id.run do
  let refs := sourceExt.getState env
  let leanName := text.toName
  let leanCandidates : Array Name :=
    if leanName.isAnonymous then #[]
    else (ResolveName.resolveGlobalName env opts currNamespace openDecls leanName).toArray.filterMap
      fun (n, fields) => if fields.isEmpty && env.contains n then some n else none
  let anchored := refs.filter (leanCandidates.contains ·.declName)
  if !anchored.isEmpty then
    let targets := groupTargets anchored
    if h : targets.size = 1 then return .found targets[0]
    return .ambiguous targets
  let targets := groupTargets (refs.filter (·.coqName == text))
  if !leanCandidates.isEmpty then
    return if targets.isEmpty then .unanchored leanCandidates else .shadowed leanCandidates targets
  if h : targets.size = 1 then
    return .found targets[0]
  else if targets.isEmpty then
    return .unknown
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

/-- The shortest Lean spellings, in the current scope, of the ports of `anchors`. -/
def portSpellings (anchors : Array FlocqAnchor) : DocM (Array String) := do
  let mut spellings : Array String := #[]
  for anchor in anchors do
    for n in anchor.leanNames do
      let s := (← unresolveNameGlobal n).toString
      unless spellings.contains s do spellings := spellings.push s
  return spellings

/-- `declName`, with the reason it is Lean-only if it carries `@[flocq_local]`. -/
def describeLean (env : Environment) (declName : Name) : MessageData :=
  match localRef? env declName with
  | some ref => m!"`{declName}` (a Lean-only `@[flocq_local]` declaration: {ref.reason})"
  | none => m!"`{declName}`"

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
    let hint ← replacements ref m!"Cite the Lean declaration instead:" (← portSpellings anchors)
      render
    throwErrorAt ref m!"`{text}` names {anchors.size} different pinned Flocq declarations:\
      {indentD (MessageData.joinSep (anchors.toList.map describe) Format.line)}\n\
      Cite one of their Lean declarations to choose.{hint}"
  | .shadowed declNames anchors =>
    let hint ← replacements ref m!"Cite the anchored port instead:" (← portSpellings anchors)
      render
    throwErrorAt ref m!"`{text}` resolves to the Lean declaration {describeLean env declNames[0]!}, \
      which has no `@[flocq_source]` anchor, but it is also the Coq name of\
      {indentD (MessageData.joinSep (anchors.toList.map describe) Format.line)}\n\
      Cite the anchored Lean port to say which one you mean.{hint}"
  | .unanchored declNames =>
    let hint ← replacements ref m!"Cite an anchored declaration:" (nearMisses env text) render
    let fix := if (localRef? env declNames[0]!).isSome then m!""
      else m!", or anchor this one with `@[flocq_source \"src/…/File.v\" LINE \"coq_name\"]` \
        if it ports Flocq"
    throwErrorAt ref m!"`{text}` is the Lean declaration {describeLean env declNames[0]!}, which \
      has no `@[flocq_source]` anchor, and no anchored Coq declaration is named `{text}`. \
      Cite an anchored declaration{fix}.{hint}"
  | .unknown =>
    let hint ← replacements ref m!"Cite a nearby anchor:" (nearMisses env text) render
    throwErrorAt ref m!"No pinned Flocq anchor matches `{text}`. Cite a Lean declaration that \
      carries `@[flocq_source]`, or a Coq name that exactly one anchor declares.{hint}"

/-- Vernacular modifiers that may precede the keyword on an anchored line. Keep in sync with
`COQ_DECL` in `scripts/validate_flocq_source_refs.py`. -/
def vernacularModifiers : List String :=
  ["Local", "Global", "Program", "Polymorphic", "Monomorphic"]

/-- Vernacular keywords that introduce an anchored declaration. Keep in sync with `COQ_DECL` in
`scripts/validate_flocq_source_refs.py`. -/
def vernacularKeywords : List String :=
  ["Definition", "Fixpoint", "CoFixpoint", "Lemma", "Theorem", "Inductive", "CoInductive",
   "Record", "Class", "Axiom", "Parameter", "Notation"]

/-- Does `line` declare `name` the way an anchored line does: optional modifiers, a vernacular
keyword, then `name` as a whole identifier? A leading comment or any other text fails. -/
def declaresName (line name : String) : Bool := Id.run do
  let isIdentChar (c : Char) := c.isAlphanum || c == '_' || c == '\''
  let mut rest := line.toList.dropWhile Char.isWhitespace
  repeat
    let word := rest.takeWhile (!·.isWhitespace)
    let after := rest.drop word.length
    let wordStr := String.ofList word
    if vernacularModifiers.contains wordStr && after.any Char.isWhitespace then
      rest := after.dropWhile Char.isWhitespace
    else if vernacularKeywords.contains wordStr && !after.isEmpty then
      let target := after.dropWhile Char.isWhitespace
      return target.take name.length == name.toList &&
        !((target.drop name.length).headD ' ' |> isIdentChar)
    else
      return false
  return false

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

/-! ## Reading citations back -/

/-- The custom inline data of type `α` in `inline`, in document order. -/
partial def inlineData (α : Type) [TypeName α] : Doc.Inline ElabInline → Array α
  | .other (.custom val) content =>
    (match val.get? α with | some a => #[a] | none => #[]) ++ content.flatMap (inlineData α)
  | .other _ content | .concat content | .emph content | .bold content | .link content _
  | .footnote _ content => content.flatMap (inlineData α)
  | _ => #[]

/-- The custom data of type `α` in `block`, inline or block, in document order. -/
partial def blockData (α : Type) [TypeName α] : Doc.Block ElabInline ElabBlock → Array α
  | .other (.custom val) content =>
    (match val.get? α with | some a => #[a] | none => #[]) ++ content.flatMap (blockData α)
  | .para content => content.flatMap (inlineData α)
  | .other _ content | .concat content | .blockquote content => content.flatMap (blockData α)
  | .ul items | .ol _ items => items.flatMap (·.contents.flatMap (blockData α))
  | .dl items => items.flatMap fun item =>
    item.term.flatMap (inlineData α) ++ item.desc.flatMap (blockData α)
  | .code _ => #[]

/-- The custom data of type `α` in a document part and its subparts. -/
partial def partData (α : Type) [TypeName α] {p : Type} :
    Doc.Part ElabInline ElabBlock p → Array α
  | part => part.title.flatMap (inlineData α) ++ part.content.flatMap (blockData α) ++
      part.subParts.flatMap (partData α)

/-- The custom data of type `α` in a Verso docstring, in document order. -/
def docData (α : Type) [TypeName α] (doc : VersoDocString) : Array α :=
  doc.text.flatMap (blockData α) ++ doc.subsections.flatMap (partData α)

/-- The custom data of type `α` in a snippet of Verso module docs. -/
def snippetData (α : Type) [TypeName α] (snippet : VersoModuleDocs.Snippet) : Array α :=
  snippet.text.flatMap (blockData α) ++ snippet.sections.flatMap (partData α ·.2.2)

/-- A compiled quote as JSON, for `scripts/validate_flocq_source_refs.py`. -/
def FlocqQuote.json (quote : FlocqQuote) : Json :=
  Json.mkObj [("lean_line", toJson quote.leanLine), ("cited", toJson quote.cited),
    ("coq_name", toJson quote.anchor.coqName), ("path", toJson quote.anchor.path),
    ("line", toJson quote.anchor.line),
    ("lean_names", toJson (quote.anchor.leanNames.map toString)), ("code", toJson quote.code)]

/-- The Flocq quotes in the docstrings of an imported module. -/
def moduleQuotes (env : Environment) (moduleName : Name) : Array FlocqQuote := Id.run do
  let some idx := env.getModuleIdx? moduleName | return #[]
  let decls := versoDocStringExt.getModuleEntries (level := .server) env idx
  let snippets := (getVersoModuleDoc? env moduleName).getD #[]
  return decls.flatMap (docData FlocqQuote ·.2) ++ snippets.flatMap (snippetData FlocqQuote)

/-- The Flocq quotes in the docstrings elaborated so far in the main module. -/
def mainModuleQuotes (env : Environment) : Array FlocqQuote := Id.run do
  let names := env.constants.foldStage2 (fun names n _ => names.push n) (#[] : Array Name)
  let mut quotes := #[]
  for n in names do
    if let some doc := versoDocStringExt.find? (level := .server) env n then
      quotes := quotes ++ docData FlocqQuote doc
  for snippet in (getMainVersoModuleDocs env).snippets do
    quotes := quotes ++ snippetData FlocqQuote snippet
  return quotes.qsort (·.leanLine < ·.leanLine)

/-- Prints the main module's Flocq quotes as one line, `FLOCQ_QUOTES` then a JSON array.
`scripts/validate_flocq_source_refs.py` appends `run_cmd` of this to a copy of a Lean file that
is not part of the library, to read that file's compiled quotes. -/
def printMainModuleQuotes : Command.CommandElabM Unit := do
  let quotes := mainModuleQuotes (← getEnv)
  IO.println ("FLOCQ_QUOTES " ++ (Json.arr (quotes.map FlocqQuote.json)).compress)

end FloatSpec.Roles

open FloatSpec.Roles

/--
Cites a pinned Flocq declaration: `{coq}` followed by a code element with a Lean declaration
carrying `@[flocq_source]` (such as `FloatSpec.Core.Generic_fmt.round_0`) or a Coq name
declared by exactly one anchor (such as `Rnd_DN_pt_monotone`). Renders the Coq name linked to
its line at the pinned commit. Unknown, unanchored, ambiguous and shadowed names are errors.
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
the same anchor name the `{coq}` role accepts, and the quote's first line must declare the
anchored name, as the anchored line does (`Theorem round_0 :`, say). The quote and its resolved
anchor are stored in the docstring; `scripts/validate_flocq_source_refs.py` reads them back and
checks the quote verbatim against the pinned checkout, through the end of the declaration's first
sentence unless a final line `...` marks it as shortened.
-/
@[doc_code_block coq]
def coqQuote (flocqAnchor : Ident) (code : StrLit) : DocM (Block ElabInline ElabBlock) := do
  let text := flocqAnchor.getId.toString (escape := false)
  let anchor ← resolveOrThrow text flocqAnchor id
  let source := code.getString
  let firstLine := (source.splitOn "\n").headD ""
  unless declaresName firstLine anchor.coqName do
    throwErrorAt code m!"A Flocq quote must begin at its anchored line \
      {anchor.path}:{anchor.line}, which declares `{anchor.coqName}` (for example \
      `Theorem {anchor.coqName} :`), but this quote begins with{indentD firstLine}"
  if let #[declName] := anchor.leanNames then addConstInfo flocqAnchor declName
  let fileMap ← getFileMap
  let leanLine := match flocqAnchor.raw.getPos? with
    | some pos => (fileMap.toPosition pos).line
    | none => 0
  return .custom ({ anchor, cited := text, leanLine, code := source } : FlocqQuote) #[
    .para (quoteHeader anchor), .code source]

end
