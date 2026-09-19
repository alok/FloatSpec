#!/usr/bin/env python3
"""Check every Lean flocq_source anchor against an exact Flocq checkout."""

from __future__ import annotations

import argparse
import re
from pathlib import Path


SOURCE_REF = re.compile(
    r'@\[flocq_source\s+"(?P<path>src/[^"\n]+\.v)"\s+'
    r'(?P<line>[1-9][0-9]*)\s+"(?P<name>[^"\n]+)"\]'
)
COQ_DECL = re.compile(
    r"^\s*(?:(?:Local|Global|Program|Polymorphic|Monomorphic)\s+)*"
    r"(?:Definition|Fixpoint|CoFixpoint|Lemma|Theorem|Inductive|CoInductive|"
    r"Record|Class|Axiom|Parameter)\s+(?P<name>[A-Za-z_][A-Za-z_0-9']*)\b"
)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("flocq_dir", type=Path, help="checkout at the pinned Flocq commit")
    parser.add_argument(
        "--lean-dir", type=Path, default=Path("FloatSpec/src"), help="Lean source tree"
    )
    args = parser.parse_args()

    failures: list[str] = []
    count = 0
    for lean_file in sorted(args.lean_dir.rglob("*.lean")):
        for match in SOURCE_REF.finditer(lean_file.read_text(encoding="utf-8")):
            count += 1
            rel_path = Path(match.group("path"))
            if ".." in rel_path.parts:
                failures.append(f"{lean_file}: source path escapes src/: {rel_path}")
                continue
            coq_file = args.flocq_dir / rel_path
            if not coq_file.is_file():
                failures.append(f"{lean_file}: missing Flocq source {coq_file}")
                continue
            lines = coq_file.read_text(encoding="utf-8").splitlines()
            line_no = int(match.group("line"))
            if line_no > len(lines):
                failures.append(f"{lean_file}: {rel_path}:{line_no} is beyond EOF")
                continue
            declaration = COQ_DECL.match(lines[line_no - 1])
            if declaration is None or declaration.group("name") != match.group("name"):
                failures.append(
                    f"{lean_file}: {rel_path}:{line_no} does not declare "
                    f"{match.group('name')!r}: {lines[line_no - 1]!r}"
                )

    if count == 0:
        failures.append("no flocq_source annotations found")
    if failures:
        for failure in failures:
            print(failure)
        return 1
    print(f"Validated {count} pinned Flocq source anchors against {args.flocq_dir}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
