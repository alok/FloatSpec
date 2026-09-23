#!/usr/bin/env python3
"""Check elaborated Lean flocq_source anchors against the pinned Flocq checkout.

The default builds/imports FloatSpec and reads its persistent source metadata.
--lean-dir is a legacy textual heuristic, not a compiler-backed coverage gate.

With compiled metadata it also checks the Flocq file list behind the `{coq_file}`
docstring role, and that every `coq` quote block in a Lean file reproduces the
pinned source verbatim, starting at its anchored line.
"""

from __future__ import annotations

import argparse
import json
import re
from pathlib import Path

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


# A docstring code block quoting Flocq: ```coq ANCHOR ... ``` (see FloatSpecRoles.lean).
QUOTE = re.compile(
    r"^(?P<indent>[ \t]*)(?P<fence>`{3,})coq(?:[ \t]+(?P<anchor>[^\s`]+))?[ \t]*\n"
    r"(?P<body>.*?)^(?P=indent)(?P=fence)[ \t]*$", re.MULTILINE | re.DOTALL)
QUOTE_OPENER = re.compile(r"^[ \t]*`{3,}coq(?:[ \t]+[^\s`]+)?[ \t]*$", re.MULTILINE)
# A doc comment that `#guard_msgs` expects to be rejected, possibly under `set_option ... in`.
EXPECTED_FAILURE = re.compile(r"#guard_msgs[^\n]*\bin\s*(?:set_option[^\n]*\bin\s*)*/--$")


def tracked_rocq_sources(flocq_dir: Path) -> list[str]:
    """Rocq sources committed at the checkout's commit. `./configure` also generates an
    untracked `src/Version.v`, which has no pinned URL and so is not a citable file."""
    listed = run(["git", "-C", str(flocq_dir), "ls-files", "--", "src"])
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


def validate_quotes(files: list[Path], references: list[dict], flocq_dir: Path,
                    root: Path = ROOT) -> tuple[list[str], int]:
    """Check each `coq` quote block against the pinned source at its anchor.

    An anchor names a Lean declaration (full or namespace suffix) or a Coq name, as the
    Lean role does; the quote must equal the source lines starting at one such anchor.
    Blocks inside a doc comment that `#guard_msgs` expects to fail are skipped.
    Returns the failures and the number of verified quotes.
    """
    failures: list[str] = []
    checked = 0
    sources: dict[str, list[str]] = {}
    for file in files:
        text = file.read_text(encoding="utf-8")
        where_file = file.relative_to(root) if file.is_relative_to(root) else file
        blocks = list(QUOTE.finditer(text))
        if len(blocks) != len(QUOTE_OPENER.findall(text)):
            failures.append(f"{where_file}: a ```coq block is unterminated or malformed")
        for block in blocks:
            where = f"{where_file}:{text.count(chr(10), 0, block.start()) + 1}"
            opener = text.rfind("/--", 0, block.start())
            if opener >= 0 and EXPECTED_FAILURE.search(text[max(0, opener - 400):opener + 3]):
                continue
            anchor = block["anchor"]
            if not anchor:
                failures.append(f"{where}: ```coq quote names no Flocq anchor")
                continue
            indent = block["indent"]
            body = block["body"].removesuffix("\n").split("\n")
            quote = [line.removeprefix(indent).rstrip() for line in body]
            targets = sorted({(ref["path"], ref["line"]) for ref in references
                              if anchor in (ref["name"], ref["lean_name"])
                              or ref["lean_name"].endswith("." + anchor)})
            if not targets:
                failures.append(f"{where}: ```coq {anchor} names no compiled Flocq anchor")
                continue
            for path in {path for path, _ in targets} - sources.keys():
                coq_file = flocq_dir / path
                sources[path] = (coq_file.read_text(encoding="utf-8").splitlines()
                                 if coq_file.is_file() else [])
            pinned = {(path, line_no): [line.rstrip() for line in
                                        sources[path][line_no - 1:line_no - 1 + len(quote)]]
                      for path, line_no in targets}
            if quote in pinned.values():
                checked += 1
            else:
                path, line_no = targets[0]
                failures.append(f"{where}: ```coq {anchor} is not verbatim {path}:{line_no}; "
                                f"the pinned source reads:\n  " + "\n  ".join(pinned[targets[0]]))
    return failures, checked


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
        quote_failures, quotes = validate_quotes(lean_files(ROOT), references, args.flocq_dir)
        failures += quote_failures
        extra = f" and {quotes} verbatim `coq` docstring quotes"
    if failures:
        for failure in failures:
            print(failure)
        return 1
    print(f"Validated {len(references)} pinned Flocq source anchors{extra} ({method}) "
          f"against {args.flocq_dir}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
