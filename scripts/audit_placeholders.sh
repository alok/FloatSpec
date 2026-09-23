#!/usr/bin/env bash
set -euo pipefail

usage() {
  cat <<'USAGE'
Usage: scripts/audit_placeholders.sh [--json] [--diff] [--fail-on-findings] [PATH...]

Scan Lean and Rocq sources for placeholder hazards: sorry/admit/axiom, True
placeholders, placeholder comments, identity/constant stubs, and common
semantic-weakening markers.

Lean sources are also scanned for trust escapes that the compiled trust scan
cannot see in an `example` or an uncompiled fixture: native evaluation
(`native_decide`, native `decide` configurations, `bv_decide`, `ofReduceBool`),
`sorryAx` and sorry-producing tactics, options and meta calls, kernel bypasses,
every `warningAsError` and `#guard_msgs` use (scripts/check_proof_debts.py
approves the reviewed ones line by line), `#exit`, and syntax the comment
stripper cannot follow (notation tokens containing comment markers, new
interpolated-string syntax).  Rocq (`.v`) sources are scanned for `Admitted`,
`Admit`, `admit`, axioms, parameters and `Declare` commands, context
declarations outside a Section, `native_compute`, and disabled kernel checks.

Patterns see comment-stripped code, except that the unambiguous trust-escape
names (scope `raw` in the pattern table) are rejected in comments and strings
too.  This is a line-oriented text gate, not a parser: it matches single-line
spellings of the escapes it lists, and multi-token escapes are matched by a
token that must appear on some line.

Options:
  --json    Emit JSON instead of text.
  --diff    Scan only added lines in the current git diff.
  --fail-on-findings  Exit nonzero when any finding is reported.
  -h,--help Show this help.

If no PATH is supplied, FloatSpec/ is scanned.
USAGE
}

json=false
diff_only=false
fail_on_findings=false
paths=()

while [[ $# -gt 0 ]]; do
  case "$1" in
    --json)
      json=true
      shift
      ;;
    --diff)
      diff_only=true
      shift
      ;;
    --fail-on-findings)
      fail_on_findings=true
      shift
      ;;
    -h|--help)
      usage
      exit 0
      ;;
    *)
      paths+=("$1")
      shift
      ;;
  esac
done

for tool in rg python3; do
  if ! command -v "$tool" >/dev/null 2>&1; then
    echo "audit scanner prerequisite missing: $tool" >&2
    exit 2
  fi
done

# ripgrep distinguishes no matches (1) from search/tool failures (>1).
# Never turn an unreadable source or failed tool into an empty successful scan.
rg_or_empty() {
  local status
  if rg "$@"; then
    return 0
  else
    status=$?
    if [[ "$status" -eq 1 ]]; then return 0; fi
    echo "audit scanner ripgrep failed (status $status)" >&2
    return "$status"
  fi
}

if [[ ${#paths[@]} -eq 0 ]]; then
  paths=(FloatSpec)
fi

work_dir="$(mktemp -d)"
trap 'rm -rf "$work_dir"' EXIT
pattern_file="$work_dir/patterns.tsv"
scan_file="$work_dir/scan.txt"

# Columns: language (lean for .lean files, rocq for .v files), scope, kind,
# regex.  Scope `code` matches comment-stripped code; `trust` also matches the
# code as lexed with interpolated strings, so neither reading of a `{` inside a
# string can hide code; `raw` also matches the unstripped source line.  A kind
# may have several rows and is reported once per source line.  Each regex must
# mean the same thing to ripgrep (text mode) and Python (JSON mode).
cat >"$pattern_file" <<'PATTERNS'
lean	trust	sorry	^\s*sorry\b|\bsorry\b
lean	trust	axiom	(^|[\s\]])((public|private|protected|noncomputable|unsafe|meta)\s+)*axiom\b
lean	raw	axiom	^\s*(@\[[^\n]*\]\s*)*((public|private|protected|noncomputable|unsafe|meta)\s+)*axiom\b|\baxiomDecl\b
lean	trust	opaque	^\s*(@\[[^\n]*\]\s*)*((public|private|protected|noncomputable|unsafe|meta)\s+)*opaque\b
lean	trust	extern	@\[[^\n]*\bextern\b
lean	trust	unsafe_declaration	^\s*(@\[[^\n]*\]\s*)*((public|private|protected|noncomputable|meta)\s+)*unsafe\s+(nonrec\s+)?(def|theorem|lemma|instance)\b
lean	trust	implemented_by	\bimplemented_by\b
lean	raw	native_decide	\bnative_decide\b
lean	raw	native_config	\+native\b|(^|[({,⟨]|\bwith\b)\s*native\s*(:=|$)|\b(DecideConfig|nativeDecide|evalNativeDecide|evalDecideCore)\b
lean	trust	config_term	\bconfig\s*:=\s*($|[^{\s])
lean	raw	bv_decide	\bbv_(decide|check)\b
lean	raw	compiler_trust	\b(ofReduceBool|ofReduceNat|reduceBool|reduceNat|trustCompiler|nativeEqTrue)\b
lean	raw	sorry_ax	\bsorryAx\b
lean	raw	sorry_meta	\b(mkSorry|mkLabeledSorry|mkSyntheticSorry|mkSyntheticSorryFor|exceptionToSorry|admitGoal)\b
lean	raw	sorry_option	\b(proofAsSorry|byAsSorry|terminalTacticsAsSorry)\b
lean	raw	kernel_bypass	\bskipKernelTC\b|\baddDeclWithoutChecking\b
lean	raw	warning_as_error	\bwarningAsError\b
lean	raw	guard_msgs	#guard_msgs\b
lean	raw	exit_command	#exit\b
lean	trust	sorry_tactic	\bstop\b\s*($|[A-Za-z_«({·.])|\bapply\?|\bimpossible\s*([+-][\w«]|\(\s*[\w.«»]+\s*:=|\bby\b)|^\s*impossible\s*$|\b(plausible|slim_check)\b
lean	trust	lexer_syntax	\b(notation\w*|infix[lr]?|prefix|postfix|syntax|macro|elab|binder_predicate)\b.*"[^"]*[^\s"](--|/-)|\binterpolatedStr\b
lean	trust	admit	^\s*admit\b|\badmit\b
lean	code	true_definition	:\s*Prop\s*:=\s*True\b|:\s*True\s*:=\s*True\.intro\b
lean	code	true_relation	fun\s+(_|[A-Za-z][A-Za-z0-9_']*)\s+(_|[A-Za-z][A-Za-z0-9_']*)\s*=>\s*True\b
lean	code	decide_true	decide\s*(\(\s*)?True(\s*\))?
lean	code	obvious_decide_true	decide\s*\(\s*\(?\s*0\s*:\s*ℝ\s*\)?\s*≤\s*0\s*\)
lean	code	placeholder_text	placeholder|stub|fake|dummy|temporar|TODO|FIXME|mode is ignored|mode.*ignored|always returns|constant.*placeholder
lean	code	conclusion_as_hypothesis	conclusion.*hypothesis|postcondition.*precondition|assum.*conclusion
lean	code	identity_hint	identity/no-op|no-op placeholder|returns the input|return the input
lean	code	public_true_theorem	theorem\s+[A-Za-z0-9_'.]+\b.*:\s*True\b
rocq	raw	rocq_admitted	\bAdmitted\b|\bAdmit\b
rocq	trust	rocq_admit	\badmit\b
rocq	trust	rocq_axiom	\b(Axioms?|Parameters?|Conjectures?|Declare)\b
rocq	trust	rocq_hypothesis	\b(Variables?|Hypothesis|Hypotheses|Context)\b|[",]\s*-\s*(all|default|vernacular|declaration-outside-section|context-outside-section)\b
rocq	raw	rocq_native_compute	\b(native_compute|native_cast_no_check)\b
rocq	raw	rocq_kernel_bypass	\bChecking\b|\bbypass_check\b
rocq	trust	lexer_syntax	\b(Notation|Infix)\b.*"[^"]*[^\s"]\(\*
PATTERNS

if "$diff_only"; then
  # Pin the patch format against user configuration (prefixes, color).
  git diff --unified=0 --no-color --no-ext-diff --src-prefix=a/ --dst-prefix=b/ -- "${paths[@]}" |
    awk '
      /^diff --git / {
        file=$4
        sub(/^b\//, "", file)
      }
      /^\+\+\+ b\// {
        file=$2
        sub(/^b\//, "", file)
      }
      /^@@ / {
        if (match($0, /\+[0-9]+/)) line=substr($0, RSTART+1, RLENGTH-1); else line=0
        next
      }
      /^\+/ && $0 !~ /^\+\+\+/ {
        text=substr($0, 2)
        if (file ~ /\.(lean|v)$/) {
          printf "%s:%d:%s\n", file, line, text
        }
        line++
        next
      }
    ' >"$scan_file"
else
  # Search every byte of every Lean/Rocq file Lake or coqc could compile:
  # binary (NUL-containing), hidden, ignored and symlinked ones included.
  rg_or_empty -n -H --text --encoding none --follow --hidden --no-ignore --sort path \
    --glob '*.lean' --glob '*.v' '.*' "${paths[@]}" >"$scan_file"
fi

# Heuristically lex each source line, omitting comments: Lean line and nested
# block comments, and Rocq nested `(* *)` comments. This is not a Lean or Rocq
# parser or a complete environment-level trust audit. Keeping the original path
# and line number makes findings stable while preventing words such as
# "temporarily" or "admit" in audit explanations from becoming trust failures.
# String contents are retained because placeholder code can occur in generated
# declarations, but comment delimiters inside strings, Lean character literals,
# raw strings and «escaped» identifiers are ignored (an escaped identifier is
# emitted without its guillemets).  Lexer state carries across the lines of one
# file and resets at a new file or a diff-hunk gap, so an unclosed comment can
# never hide another file's code.
#
# Rocq `Variable`/`Hypothesis`/`Context` declarations inside a Section are
# discharged when the Section ends, so they are blanked there.  Outside every
# Section they are axioms and stay visible to `rocq_hypothesis`.
#
# Outside --diff mode, every Lean/Rocq file under the scanned paths must appear
# in the scan with all of its lines; anything else is a scanner failure.
#
# Output: for each language, line-aligned views `code` (plain strings), `alt`
# (interpolated strings; blank where equal to code), `raw` (the source line;
# blank where equal to code) and `loc` (scan order and path:line), consumed
# identically by both output modes.
python3 - "$scan_file" "$work_dir" "$diff_only" "${paths[@]}" <<'PY'
import os
import re
import sys

source, work_dir, diff_only = sys.argv[1:4]
diff_only = diff_only == "true"
roots = sys.argv[4:]


def fail(message):
    print(f"audit scanner {message}", file=sys.stderr)
    sys.exit(2)


ROCQ_TOKEN = re.compile(
    r"\b(Section|End|Module|Variables?|Hypothesis|Hypotheses|Context)\b")
ROCQ_NAME = re.compile(r"\s+(?:Type\s+)?(?:(?:Import|Export)\s+)?([A-Za-z_][A-Za-z0-9_']*)")
CHAR_LITERAL = re.compile(r"'(?:\\(?:x[0-9a-fA-F]{2}|u[0-9a-fA-F]{4}|[\\\"'rnt])|[^\\'])'")
RAW_STRING_START = re.compile(r'r(#*)"')
LEAN_CODE_STOP = re.compile(r'--|/-|[«"\'{}]|r#*"')
LEAN_STRING_STOP = re.compile(r'[\\"{]')
LEAN_COMMENT_STOP = re.compile(r"/-|-/")


def is_id_rest(ch):
    """Lean's `isIdRest`: ASCII alphanumerics, `_'!?`, letter-likes, subscripts."""
    if not ch:
        return False
    o = ord(ch)
    return ((ch.isascii() and ch.isalnum()) or ch in "_'!?"
            or (0x3B1 <= o <= 0x3C9 and o != 0x3BB)
            or (0x391 <= o <= 0x3A9 and o not in (0x3A0, 0x3A3))
            or 0x3CA <= o <= 0x3FB or 0x1F00 <= o <= 0x1FFE or 0x2100 <= o <= 0x214F
            or 0x1D49C <= o <= 0x1D59F or (0xC0 <= o <= 0xFF and o not in (0xD7, 0xF7))
            or 0x100 <= o <= 0x17F or 0x2080 <= o <= 0x209C or 0x1D62 <= o <= 0x1D6A
            or o == 0x2C7C)


def in_identifier(text, i):
    """Whether position i continues an identifier or name literal (Lean)."""
    j = i
    while j > 0 and is_id_rest(text[j - 1]):
        j -= 1
    if j < i:
        return not text[j].isdigit()  # identifiers never start with a digit
    prev = text[i - 1] if i else ""
    return prev == "`" or (prev == "." and i > 1 and (is_id_rest(text[i - 2]) or text[i - 2] == "»"))


class Lexer:
    def __init__(self, path, interpolation=False):
        self.rocq = path.endswith(".v")
        self.interpolation = interpolation
        self.block_depth = 0
        self.mode = "code"  # code, string, raw (Lean raw string) or ident («...»)
        self.raw_close = ""
        self.string_interpolated = False
        self.frames = []  # brace depth inside each open `{` interpolation
        self.last = ""  # last non-space code character, for interpolation
        self.comment_string = False
        self.scopes = []  # open Rocq (kind, name) scopes

    def strip_lean(self, text):
        out = []
        i = 0
        while i < len(text):
            if self.block_depth:
                stop = LEAN_COMMENT_STOP.search(text, i)
                if not stop:
                    break
                self.block_depth += 1 if stop.group() == "/-" else -1
                i = stop.end()
            elif self.mode == "ident":  # «escaped identifier», emitted without guillemets
                end = text.find("»", i)
                out.append(text[i:] if end < 0 else text[i:end])
                if end < 0:
                    break
                self.mode, self.last, i = "code", "»", end + 1
            elif self.mode == "raw":  # r#"raw string"#: no escapes
                end = text.find(self.raw_close, i)
                if end < 0:
                    out.append(text[i:])
                    break
                out.append(text[i:end + len(self.raw_close)])
                self.mode, self.last, i = "code", '"', end + len(self.raw_close)
            elif self.mode == "string":
                stop = LEAN_STRING_STOP.search(text, i)
                if not stop:
                    out.append(text[i:])
                    break
                out.append(text[i:stop.end()])
                i = stop.end()
                if stop.group() == "\\":
                    out.append(text[i:i + 1])  # the escaped character, if on this line
                    i += 1
                elif stop.group() == '"':
                    self.mode, self.last = "code", '"'
                elif self.string_interpolated:  # `{` opens an interpolated term
                    self.frames.append(0)
                    self.mode, self.last = "code", "{"
            else:
                stop = LEAN_CODE_STOP.search(text, i)
                chunk = text[i:stop.start() if stop else len(text)]
                out.append(chunk)
                if chunk.strip():
                    self.last = chunk.rstrip()[-1]
                if not stop:
                    break
                token, i = stop.group(), stop.start()
                if token == "--":
                    break
                if token == "/-":
                    self.block_depth, i = 1, i + 2
                elif token == "«":
                    self.mode, i = "ident", i + 1
                elif token == '"':
                    # View `alt` reads a string as interpolated after an
                    # identifier, keyword, `!`, `]` or `)`: the prefixes of
                    # Lean's `s!`, `throwError`, `trace[c]` and `throwErrorAt
                    # (e)`.  Other interpolating syntax is `lexer_syntax`.
                    self.string_interpolated = self.interpolation and (
                        is_id_rest(self.last) or self.last in "!»])")
                    out.append(token)
                    self.mode, i = "string", i + 1
                elif token[0] in "'r":  # a character or raw string literal, or an identifier
                    literal = None
                    if not in_identifier(text, i) and not text.startswith("''", i):
                        literal = (CHAR_LITERAL if token == "'" else RAW_STRING_START).match(text, i)
                    if literal is None:
                        out.append(token[0])
                        self.last, i = token[0], i + 1
                    else:
                        out.append(literal.group())
                        self.last, i = literal.group()[-1], literal.end()
                        if token[0] == "r":
                            self.mode, self.raw_close = "raw", '"' + literal.group(1)
                else:  # a brace, which matters only inside an interpolated term
                    out.append(token)
                    self.last, i = token, i + 1
                    if self.frames and token == "}" and not self.frames[-1]:
                        self.frames.pop()
                        self.mode, self.string_interpolated = "string", True
                    elif self.frames:
                        self.frames[-1] += 1 if token == "{" else -1
        return "".join(out)

    def strip_rocq(self, text):
        out = []
        bare = []  # `out` with string contents blanked, for Section tracking
        i = 0
        while i < len(text):
            ch = text[i]
            if self.block_depth:
                # Rocq lexes strings inside comments: `"*)"` does not close one.
                if self.comment_string:
                    self.comment_string = ch != '"'
                    i += 1
                elif text.startswith("(*", i):
                    self.block_depth += 1
                    i += 2
                elif text.startswith("*)", i):
                    self.block_depth -= 1
                    i += 2
                else:
                    self.comment_string = ch == '"'
                    i += 1
                continue
            if self.mode == "string":
                # A doubled quote closes and immediately reopens the string.
                out.append(ch)
                bare.append(" ")
                self.mode = "code" if ch == '"' else "string"
                i += 1
            elif ch == '"':
                self.mode = "string"
                out.append(ch)
                bare.append(" ")
                i += 1
            elif text.startswith("(*", i):
                self.block_depth = 1
                i += 2
            else:
                out.append(ch)
                bare.append(ch)
                i += 1
        return self.mask_section_context("".join(out), "".join(bare))

    def mask_section_context(self, code, bare):
        masked = list(code)
        for match in ROCQ_TOKEN.finditer(bare):
            word = match.group(1)
            name = ROCQ_NAME.match(bare, match.end())
            if word == "Section" and name:
                self.scopes.append(("section", name.group(1)))
            elif word == "Module" and name and not bare[:match.start()].rstrip().endswith("Declare"):
                if ":=" not in bare[name.end():]:
                    self.scopes.append(("module", name.group(1)))
            elif word == "End" and name:
                names = [scope_name for _, scope_name in self.scopes]
                if name.group(1) in names:
                    del self.scopes[len(names) - 1 - names[::-1].index(name.group(1)):]
            elif word not in ("Section", "Module", "End"):
                if any(kind == "section" for kind, _ in self.scopes):
                    masked[match.start():match.end()] = " " * (match.end() - match.start())
        return "".join(masked)


def expected_files():
    """Every file ripgrep must have scanned, found independently of ripgrep."""
    found = set()

    def walk(directory, ancestors):
        real = os.path.realpath(directory)
        if real in ancestors:
            return
        for entry in os.scandir(directory):
            if entry.is_dir():  # follows symlinks, like `rg --follow`
                walk(entry.path, ancestors | {real})
            elif entry.name.endswith((".lean", ".v")):
                found.add(entry.path)

    for root in roots:
        if os.path.isdir(root):
            walk(root, frozenset())
        else:
            found.add(root)
    return found


def line_count(path):
    try:
        with open(path, "rb") as f:
            data = f.read()
    except OSError as error:
        fail(f"cannot read {path}: {error}")
    return data.count(b"\n") + (1 if data and not data.endswith(b"\n") else 0)


outputs = {
    (language, view): open(f"{work_dir}/{language}.{view}", "w", encoding="utf-8")
    for language in ("lean", "rocq") for view in ("code", "alt", "raw", "loc")
}
lexers = None
previous = (None, None)
scanned = {}
with open(source, encoding="utf-8", errors="replace", newline="\n") as src:
    for seq, raw in enumerate(src):
        raw = raw[:-1] if raw.endswith("\n") else raw
        parts = raw.split(":", 2)
        if len(parts) != 3 or not parts[1].isdigit():
            fail(f"could not parse scan line {seq + 1}: {raw[:200]!r}")
        path, line, text = parts
        number = int(line)
        if previous[0] == path and previous[1] + 1 != number and not diff_only:
            fail(f"skipped lines of {path} before line {number}")
        if lexers is None or previous != (path, number - 1):
            lexers = (Lexer(path), Lexer(path, interpolation=True))
        previous = (path, number)
        scanned[path] = scanned.get(path, 0) + 1
        text = text.replace("\0", " ")  # a NUL would make ripgrep treat a view as binary
        if lexers[0].rocq:
            language = "rocq"
            code = alt = lexers[0].strip_rocq(text)
        else:
            language = "lean"
            code = lexers[0].strip_lean(text)
            alt = lexers[1].strip_lean(text)
        outputs[(language, "code")].write(f"{code}\n")
        outputs[(language, "alt")].write(f"{alt if alt != code else ''}\n")
        outputs[(language, "raw")].write(f"{text if text != code else ''}\n")
        outputs[(language, "loc")].write(f"{seq}\t{path}:{line}\n")
for output in outputs.values():
    output.close()

if not diff_only:
    problems = []
    expected = expected_files()
    for path in sorted(expected | scanned.keys()):
        want = line_count(path) if path in expected else 0
        if scanned.get(path, 0) != want:
            problems.append(f"{path}: scanned {scanned.get(path, 0)} of {want} lines")
    if problems:
        fail("did not read every source line:\n  " + "\n  ".join(problems[:20]))
PY

case_insensitive() {
  [[ "$1" == "placeholder_text" || "$1" == "identity_hint" || "$1" == "conclusion_as_hypothesis" ]]
}

if "$json"; then
  python3 - "$pattern_file" "$work_dir" "$fail_on_findings" <<'PY'
import json
import re
import sys

pattern_file, work_dir, fail = sys.argv[1:4]
VIEWS = {"code": ("code",), "trust": ("code", "alt"), "raw": ("code", "alt", "raw")}
rows = []
with open(pattern_file, encoding="utf-8") as f:
    for raw in f:
        raw = raw.rstrip("\n")
        if not raw:
            continue
        language, scope, name, pattern = raw.split("\t", 3)
        if name in {"placeholder_text", "identity_hint", "conclusion_as_hypothesis"}:
            pattern = f"(?i:{pattern})"
        rows.append((language, VIEWS[scope], name, pattern))
kinds = list(dict.fromkeys(name for _, _, name, _ in rows))
# One combined search per view skips the many lines that match nothing.
prefilter = {
    (language, view): re.compile("|".join(
        f"(?:{pattern})" for row_language, row_views, _, pattern in rows
        if row_language == language and view in row_views) or "(?!)")
    for language in ("lean", "rocq") for view in ("code", "alt", "raw")
}
rows = [(language, views, name, re.compile(pattern)) for language, views, name, pattern in rows]

found = []
for language in ("lean", "rocq"):
    views = {}
    for view in ("code", "alt", "raw", "loc"):
        with open(f"{work_dir}/{language}.{view}", encoding="utf-8", newline="\n") as f:
            views[view] = f.read().split("\n")[:-1]
    for index, location in enumerate(views["loc"]):
        seq, location = location.split("\t", 1)
        path, line = location.rsplit(":", 1)
        texts = {view: views[view][index] for view in ("code", "alt", "raw")}
        if not any(texts[view].strip() and prefilter[language, view].search(texts[view])
                   for view in texts):
            continue
        reported = set()
        for row_language, row_views, name, regex in rows:
            if row_language != language or name in reported:
                continue
            for view in row_views:
                text = texts[view]
                if text.strip() and regex.search(text):
                    reported.add(name)
                    found.append((int(seq), kinds.index(name), {
                        "kind": name,
                        "path": path,
                        "line": int(line),
                        "text": text.strip(),
                    }))
                    break

found.sort(key=lambda item: item[:2])
findings = [finding for _, _, finding in found]
counts = {name: 0 for name in kinds}
for finding in findings:
    counts[finding["kind"]] += 1
print(json.dumps({"counts": counts, "findings": findings}, indent=2, sort_keys=True))
if fail == "true" and findings:
    raise SystemExit(1)
PY
else
  any=false
  while IFS= read -r name; do
    hits=""
    while IFS=$'\t' read -r language scope row_name pattern; do
      [[ "$row_name" == "$name" ]] || continue
      rg_flags=(-n --text)
      if case_insensitive "$name"; then
        rg_flags+=(-i)
      fi
      case "$scope" in
        code) views=(code) ;;
        trust) views=(code alt) ;;
        *) views=(code alt raw) ;;
      esac
      for view in "${views[@]}"; do
        view_hits="$(rg_or_empty "${rg_flags[@]}" -e "$pattern" "$work_dir/$language.$view")"
        if [[ -n "$view_hits" ]]; then
          hits+="$(printf '%s\n' "$view_hits" | sed "s/^/$language:/")"$'\n'
        fi
      done
    done <"$pattern_file"
    matches=""
    if [[ -n "$hits" ]]; then
      # Replace each view's line number with the source path:line, reporting a
      # source line once and skipping blank view lines, as the JSON mode does.
      matches="$(printf '%s' "$hits" | awk -v lean="$work_dir/lean.loc" -v rocq="$work_dir/rocq.loc" '
        FILENAME == lean || FILENAME == rocq {
          language = FILENAME == lean ? "lean" : "rocq"
          tab = index($0, "\t")
          seq[language, FNR] = substr($0, 1, tab - 1)
          location[language, FNR] = substr($0, tab + 1)
          next
        }
        {
          language = $0
          sub(/:.*/, "", language)
          rest = substr($0, length(language) + 2)
          n = rest
          sub(/:.*/, "", n)
          text = substr(rest, length(n) + 2)
          if (text ~ /^[[:space:]]*$/ || seen[language, n]++) next
          printf "%s\t%s:%s\n", seq[language, n], location[language, n], text
        }
      ' "$work_dir/lean.loc" "$work_dir/rocq.loc" - | sort -n -k1,1 | cut -f2-)"
    fi
    count="$(printf '%s\n' "$matches" | sed '/^$/d' | wc -l | tr -d ' ')"
    printf '%s: %s\n' "$name" "$count"
    if [[ "$count" != "0" ]]; then
      any=true
      printf '%s\n' "$matches" | sed 's/^/  /'
    fi
  done < <(awk -F'\t' '!seen[$3]++ { print $3 }' "$pattern_file")
  if ! "$any"; then
    echo "No placeholder-pattern findings."
  fi
  if "$fail_on_findings" && "$any"; then
    exit 1
  fi
fi
