#!/usr/bin/env python3
"""Check elaborated Lean flocq_source anchors against the pinned Flocq checkout.

The default builds/imports FloatSpec and reads its persistent source metadata.
--lean-dir is a legacy textual heuristic, not a compiler-backed coverage gate.

With compiled metadata it also checks the Flocq file list behind the `{coq_file}`
docstring role, and every `coq` docstring quote as Lean compiled it: against the
exact anchor its rendered link names, verbatim (up to trailing whitespace) from the
anchored line to the end of a Rocq sentence. Every line of a Lean file that opens a
`coq` fence must have compiled to such a quote, and no Lean line may carry the location
comment of an unchecked Flocq quote, `(* Flocq src/...`, so no Flocq quote escapes the check.
"""

from __future__ import annotations

import argparse
import json
import re
from pathlib import Path
import tempfile

from flocq_bridge import ROOT, run, verify_reference


SOURCE_REF = re.compile(
    r'@\[flocq_source\s+"(?P<path>src/[^"\n]+\.v)"\s+'
    r'(?P<line>[1-9][0-9]*)\s+"(?P<name>[^"\n]+)"\]'
)
COQ_DECL = re.compile(
    r"^\s*(?:(?:Local|Global|Program|Polymorphic|Monomorphic)\s+)*"
    r"(?:Definition|Fixpoint|CoFixpoint|Lemma|Theorem|Inductive|CoInductive|"
    r"Record|Class|Axiom|Parameter|Notation)\s+(?P<name>[A-Za-z_][A-Za-z_0-9']*)(?![A-Za-z_0-9'])"
)


# A line opening a fenced code block whose info string starts with the word `coq`, after any
# blockquote or list markers: the form every `coq` quote block takes in a docstring (see
# FloatSpecRoles.lean). It deliberately over-approximates what Lean's docstring parser accepts, so
# that no quote-like block escapes the check below.
QUOTE_FENCE = re.compile(
    r"^[ \t]*(?:(?:>|[*+-](?=[ \t])|[0-9]+[.)](?=[ \t]))[ \t]*)*(?:`{3,}|~{3,})[ \t]*coq"
    r"(?![A-Za-z0-9_'])", re.MULTILINE)
# A line that begins, after any blockquote or list markers, with the location comment of a Flocq
# quote, `(* Flocq src/...`: the form an unchecked quote of Flocq took in a plain block. A Flocq
# quote must be a `coq` block, which starts at the anchored declaration instead.
FLOCQ_LOCATION = re.compile(
    r"^[ \t]*(?:(?:>|[*+-](?=[ \t])|[0-9]+[.)](?=[ \t]))[ \t]*)*\(\*[ \t]*Flocq[ \t]+src/",
    re.MULTILINE)
# The line `run_cmd FloatSpec.Roles.printMainModuleQuotes` prints; see FloatSpecRoles.lean.
QUOTES_MARKER = "FLOCQ_QUOTES "


def tracked_rocq_sources(flocq_dir: Path) -> list[str]:
    """Rocq sources in the tree of the checkout's commit. `./configure` also generates an
    untracked `src/Version.v`, which has no pinned URL and so is not a citable file."""
    listed = run(["git", "-C", str(flocq_dir), "ls-tree", "-r", "--name-only", "HEAD", "--", "src"])
    return sorted(path for path in listed.splitlines() if path.endswith(".v"))


def validate_source_files(source_files: list[str], tracked: list[str]) -> list[str]:
    """The `{coq_file}` role's list must be exactly the pinned commit's Rocq sources."""
    if sorted(source_files) == sorted(tracked) and len(set(source_files)) == len(source_files):
        return []
    return [f"flocqSourceFiles differs from the pinned Rocq sources: "
            f"missing {sorted(set(tracked) - set(source_files))}, "
            f"extra {sorted(set(source_files) - set(tracked))}"]


def lean_files(root: Path) -> list[Path]:
    """Lean sources of this repository, excluding build output and dependencies."""
    return sorted(path for path in root.rglob("*.lean")
                  if not {".lake", "Deps", ".git"} & set(path.relative_to(root).parts))


def quote_fence_lines(text: str) -> list[int]:
    """The 1-based lines of `text` that open a `coq` fenced block."""
    return [text.count("\n", 0, match.start()) + 1 for match in QUOTE_FENCE.finditer(text)]


def flocq_location_lines(text: str) -> list[int]:
    """The 1-based lines of `text` that begin with a Flocq location comment, `(* Flocq src/...`."""
    return [text.count("\n", 0, match.start()) + 1 for match in FLOCQ_LOCATION.finditer(text)]


def module_file(module: str, root: Path = ROOT) -> Path:
    """The source file of a library module."""
    return root / (module.replace(".", "/") + ".lean")


def standalone_quotes(path: Path) -> list[dict]:
    """The compiled `coq` quotes of a Lean file outside the library, such as a fixture.

    Elaborates a copy of the file with a final command that prints the quotes its docstrings
    stored, each with the anchor Lean resolved and the line of its fence.
    """
    with tempfile.TemporaryDirectory(prefix="flocq-quotes-") as directory:
        copy = Path(directory) / path.name
        copy.write_text(path.read_text(encoding="utf-8") +
                        "\n\nrun_cmd FloatSpec.Roles.printMainModuleQuotes\n", encoding="utf-8")
        output = run(["lake", "env", "lean", "-DElab.async=false", str(copy)], timeout=3600)
    printed = [line for line in output.splitlines() if line.startswith(QUOTES_MARKER)]
    if len(printed) != 1:
        raise ValueError(f"{path}: expected one {QUOTES_MARKER.strip()} line, got {len(printed)}")
    return json.loads(printed[0].removeprefix(QUOTES_MARKER))


def ends_sentence(line: str) -> bool:
    """Does this line of Rocq source end a sentence (a vernacular command)?"""
    stripped = line.rstrip()
    return stripped.endswith(".") and not stripped.endswith("..")


def check_quote(quote: dict, source: list[str]) -> str | None:
    """Why a compiled quote misstates the pinned source it links to, if it does.

    The quote must reproduce `source` verbatim from the anchored line, and end where a Rocq
    sentence ends, so it cannot silently drop the rest of a statement. A final line `...`
    marks a quote as deliberately shortened; the lines before it must still be verbatim.
    Trailing whitespace on each line, and the quote's final newline, are not compared.
    """
    where = f"{quote['path']}:{quote['line']}"
    body = [line.rstrip() for line in quote["code"].removesuffix("\n").split("\n")]
    shortened = len(body) > 1 and body[-1].strip() == "..."
    if shortened:
        body = body[:-1]
    start = quote["line"] - 1
    pinned = [line.rstrip() for line in source[start:start + len(body)]]
    if body != pinned:
        return (f"is not verbatim {where}; the pinned source reads:\n  " +
                "\n  ".join(pinned or ["<nothing: the file is missing or shorter>"]))
    if not shortened and not ends_sentence(body[-1]):
        end = next((i for i in range(start + len(body), len(source)) if ends_sentence(source[i])),
                   None)
        until = f"through line {end + 1}" if end is not None else "to the end of the sentence"
        return (f"stops inside the Rocq sentence that begins at {where}; quote it {until}, "
                f"or end the quote with a line `...` to mark it shortened")
    return None


def validate_quotes(files: list[Path], compiled: dict[Path, list[dict]], references: list[dict],
                    flocq_dir: Path, root: Path = ROOT) -> tuple[list[str], int]:
    """Check every `coq` quote as Lean compiled it, and that every fence in `files` compiled.

    `compiled` maps a file to the quotes its docstrings stored. Each quote carries the anchor
    Lean resolved, so it is compared with exactly the source its rendered link points at.
    Returns the failures and the number of verified quotes.
    """
    failures: list[str] = []
    checked = 0
    anchors = {(ref["path"], ref["line"], ref["name"]) for ref in references}
    sources: dict[str, list[str]] = {}
    for file in files:
        where_file = file.relative_to(root) if file.is_relative_to(root) else file
        text = file.read_text(encoding="utf-8")
        for line in flocq_location_lines(text):
            failures.append(
                f"{where_file}:{line}: a `(* Flocq src/...` location line marks an unchecked "
                f"quote of Flocq. Quote Flocq in a ```coq ANCHOR block of a Verso docstring, "
                f"which starts at the anchored declaration, so the validator checks it (if the "
                f"Lean port has no anchor, add `@[flocq_source \"src/...v\" LINE \"name\"]`). "
                f"Plain blocks are for the Rocq core library, located by `(* Rocq V9.1.0 ...`.")
        fences = set(quote_fence_lines(text))
        quotes = compiled.get(file, [])
        stored = {quote["lean_line"] for quote in quotes}
        for line in sorted(fences - stored):
            failures.append(
                f"{where_file}:{line}: this ```coq block is not a compiled Flocq quote, so "
                f"nothing checks it. Quotes are elaborated only in Verso docstrings: put "
                f"`set_option doc.verso true in` before the declaration (and rebuild). A test of "
                f"a rejected quote must build the block inside a string.")
        for line in sorted(stored - fences):
            failures.append(f"{where_file}:{line}: a compiled Flocq quote has no ```coq fence "
                            f"on this line; the build is stale")
        for quote in quotes:
            where = f"{where_file}:{quote['lean_line']}: ```coq {quote['cited']}"
            if (quote["path"], quote["line"], quote["coq_name"]) not in anchors:
                failures.append(f"{where} resolved to {quote['path']}:{quote['line']}, "
                                f"which is not a compiled anchor")
                continue
            if quote["path"] not in sources:
                coq_file = flocq_dir / quote["path"]
                sources[quote["path"]] = (coq_file.read_text(encoding="utf-8").splitlines()
                                          if coq_file.is_file() else [])
            problem = check_quote(quote, sources[quote["path"]])
            if problem:
                failures.append(f"{where} {problem}")
            else:
                checked += 1
    return failures, checked


def compiled_quotes(files: list[Path], manifest: dict,
                    root: Path = ROOT) -> tuple[dict[Path, list[dict]], list[str]]:
    """The compiled quotes of `files`: the library's from `manifest`, and any other file's
    that opens a `coq` fence by elaborating it. Returns them with any export failures."""
    library = {module_file(module, root) for module in manifest["quote_modules"]}
    compiled: dict[Path, list[dict]] = {}
    for quote in manifest["quotes"]:
        compiled.setdefault(module_file(quote["module"], root), []).append(quote)
    failures: list[str] = []
    for file in files:
        if file in library or not quote_fence_lines(file.read_text(encoding="utf-8")):
            continue
        try:
            compiled[file] = standalone_quotes(file)
        except (RuntimeError, ValueError) as error:
            failures.append(f"{file.relative_to(root)}: could not read its compiled quotes "
                            f"(does it import FloatSpecRoles?): {error}")
    return compiled, failures


def validate_references(references: list[dict], flocq_dir: Path) -> list[str]:
    failures: list[str] = []
    for ref in references:
        origin = ref.get("lean_name", "unknown Lean declaration")
        path, line_no, name = ref.get("path"), ref.get("line"), ref.get("name")
        if (not isinstance(path, str) or not path.startswith("src/") or
                not path.endswith(".v") or ".." in Path(path).parts or
                type(line_no) is not int or line_no <= 0 or not isinstance(name, str) or not name):
            failures.append(f"{origin}: malformed source reference")
            continue
        coq_file = flocq_dir / path
        if not coq_file.is_file():
            failures.append(f"{origin}: missing Flocq source {coq_file}")
            continue
        lines = coq_file.read_text(encoding="utf-8").splitlines()
        if line_no > len(lines):
            failures.append(f"{origin}: {path}:{line_no} is beyond EOF")
            continue
        declaration = COQ_DECL.match(lines[line_no - 1])
        if declaration is None or declaration.group("name") != name:
            failures.append(f"{origin}: {path}:{line_no} does not declare "
                            f"{name!r}: {lines[line_no - 1]!r}")
    if not references:
        failures.append("no flocq_source annotations found")
    return failures


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("flocq_dir", type=Path, help="checkout at the pinned Flocq commit")
    inputs = parser.add_mutually_exclusive_group()
    inputs.add_argument("--lean-dir", type=Path, help="legacy textual scan, not compiler coverage")
    inputs.add_argument("--manifest", type=Path, help="previously exported compiler metadata JSON")
    args = parser.parse_args()
    pin = verify_reference(args.flocq_dir.resolve())
    if args.lean_dir:
        references = [{"lean_name": str(path), "path": match["path"],
                       "line": int(match["line"]), "name": match["name"]}
                      for path in sorted(args.lean_dir.rglob("*.lean"))
                      for match in SOURCE_REF.finditer(path.read_text(encoding="utf-8"))]
        method = "legacy textual heuristic"
    else:
        if args.manifest:
            manifest = json.loads(args.manifest.read_text())
            method = "supplied compiled metadata (freshness not checked)"
        else:
            run(["lake", "build", "FloatSpec"], timeout=600)
            manifest = json.loads(run(["lake", "env", "lean", str(ROOT / "scripts/ExportFlocqSources.lean")]))
            method = "fresh compiled metadata"
        if manifest["flocq_commit"] != pin:
            raise ValueError("Lean source-link commit differs from the repository Flocq gitlink")
        references = manifest["references"]
    failures = validate_references(references, args.flocq_dir)
    extra = ""
    if not args.lean_dir:
        if "source_files" in manifest:
            failures += validate_source_files(manifest["source_files"],
                                              tracked_rocq_sources(args.flocq_dir))
        elif not args.manifest:
            failures.append("compiled metadata lacks the {coq_file} source-file list")
        if "quotes" in manifest:
            files = lean_files(ROOT)
            compiled, export_failures = compiled_quotes(files, manifest)
            quote_failures, quotes = validate_quotes(files, compiled, references, args.flocq_dir)
            failures += export_failures + quote_failures
            extra = f" and {quotes} verbatim `coq` docstring quotes"
        elif not args.manifest:
            failures.append("compiled metadata lacks the docstring quotes")
        else:
            extra = " (the supplied metadata has no docstring quotes; quotes not checked)"
    if failures:
        for failure in failures:
            print(failure)
        return 1
    print(f"Validated {len(references)} pinned Flocq source anchors{extra} ({method}) "
          f"against {args.flocq_dir}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
