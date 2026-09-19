#!/usr/bin/env python3
"""Check elaborated Lean flocq_source anchors against the pinned Flocq checkout.

The default builds/imports FloatSpec and reads its persistent source metadata.
--lean-dir is a legacy textual heuristic, not a compiler-backed coverage gate.
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
    r"Record|Class|Axiom|Parameter)\s+(?P<name>[A-Za-z_][A-Za-z_0-9']*)\b"
)


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
    if failures:
        for failure in failures:
            print(failure)
        return 1
    print(f"Validated {len(references)} pinned Flocq source anchors ({method}) against {args.flocq_dir}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
