#!/usr/bin/env python3
"""Fail on new trust hazards while allowing only named, reviewed proof debts."""

import json
import re
import subprocess
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parent.parent
MANIFEST = ROOT / "FloatSpec/docs/proof_debts.json"
MARKER = re.compile(r"\bsorry\s*--\s*FLOCQ-DEBT:\s*([a-z0-9_]+)\s*$")
THEOREM = re.compile(r"\btheorem\s+([A-Za-z0-9_']+)")


def main() -> int:
    expected_list = json.loads(MANIFEST.read_text(encoding="utf-8"))
    expected = {item["id"]: item for item in expected_list}
    if len(expected) != len(expected_list):
        raise ValueError("duplicate proof-debt id in manifest")

    result = subprocess.run(
        [str(ROOT / "scripts/audit_placeholders.sh"), "--json", "FloatSpec"],
        cwd=ROOT,
        check=True,
        capture_output=True,
        text=True,
    )
    findings = json.loads(result.stdout)["findings"]
    errors = []
    seen = set()
    for finding in findings:
        if finding["kind"] != "sorry":
            errors.append(f"unexpected {finding['kind']}: {finding['path']}:{finding['line']}")
            continue
        path = finding["path"]
        line = finding["line"]
        source_lines = (ROOT / path).read_text(encoding="utf-8").splitlines()
        if line is None or not 1 <= line <= len(source_lines):
            errors.append(f"invalid sorry location: {path}:{line}")
            continue
        match = MARKER.search(source_lines[line - 1])
        if not match:
            errors.append(f"unnamed sorry: {path}:{line}")
            continue
        debt_id = match.group(1)
        item = expected.get(debt_id)
        if item is None or item["path"] != path or debt_id in seen:
            errors.append(f"unapproved or duplicate debt {debt_id}: {path}:{line}")
            continue
        nearby = "\n".join(source_lines[max(0, line - 12) : line])
        theorem_names = THEOREM.findall(nearby)
        if not theorem_names or theorem_names[-1] != item["theorem"]:
            errors.append(f"debt {debt_id} is not in theorem {item['theorem']}")
            continue
        seen.add(debt_id)

    for debt_id in expected.keys() - seen:
        errors.append(f"manifest debt missing from sources: {debt_id}")
    if errors:
        print("\n".join(errors), file=sys.stderr)
        return 1
    print(f"Trust scan passed with {len(seen)} named, unproved proof obligations.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
