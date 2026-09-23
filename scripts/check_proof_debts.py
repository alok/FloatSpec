#!/usr/bin/env python3
"""Fail on new trust hazards while allowing only named, reviewed proof debts.

The scan covers every Lean and Rocq source in the repository that Lake or coqc
could compile: lakefile.lean (whose leanOptions enable warningAsError), the
root modules, FloatSpec/, and scripts/ (the standalone fixtures, which run
outside Lake and outside the compiled trust scan, and the Lean audit tools).
Only the vendored Flocq reference (Deps/), the local Rocq switch (_opam/) and
hidden tool state (.lake/, .git/, ...) are excluded.  Every scanner finding is
an error except:

- `sorry -- FLOCQ-DEBT: <id>` inside the theorem the manifest names for <id>;
- `set_option warningAsError false in` scoping exactly one such theorem, so its
  approved `sorry` warning does not fail the build;
- `set_option warningAsError true` (with or without `in`), and the lakefile's
  single `⟨`warningAsError, true⟩` option, which must be present;
- `#guard_msgs in` guarding a `#` command (never a declaration, whose
  elaboration errors it could otherwise swallow while the declaration is added
  with `sorryAx`), with no expected message that mentions `sorry`;
- the scanner's own negative controls in scripts/fixtures/audit/, the
  constant names the compiled trust audit must refer to, and the kernel
  replayer's two `unsafe def`s (it frees each module's imports), at exactly
  their expected counts.
"""

import json
import re
import subprocess
import sys
from collections import Counter
from dataclasses import dataclass, field
from pathlib import Path


ROOT = Path(__file__).resolve().parent.parent
MANIFEST = ROOT / "FloatSpec/docs/proof_debts.json"
EXCLUDED = {"Deps", "_opam"}
SOURCE_SUFFIXES = (".lean", ".v")
MARKER = re.compile(r"\bsorry\s*--\s*FLOCQ-DEBT:\s*([a-z0-9_]+)\s*$")
THEOREM = re.compile(r"\btheorem\s+([A-Za-z0-9_']+)")
DISABLE_WARNING_AS_ERROR = "set_option warningAsError false in"
ENABLE_WARNING_AS_ERROR = {"set_option warningAsError true", "set_option warningAsError true in"}
LAKEFILE_WARNING_AS_ERROR = "⟨`warningAsError, true⟩"
GUARD_MSGS = "#guard_msgs in"
# A `set_option ... in` scopes the next command: the first declaration header.
DECLARATION = re.compile(
    r"^\s*(?:@\[[^\n]*\]\s*)*"
    r"(?:(?:public|private|protected|noncomputable|unsafe|partial|nonrec|meta)\s+)*"
    r"(theorem|lemma|def|example|instance|abbrev|opaque|axiom|structure|inductive|class)\b"
    r"\s*([A-Za-z0-9_'.]*)")
EXPECTED_REFERENCES = Counter({
    # scripts/test_audit_placeholders.sh compiles these files and requires the
    # scanner to reject them; nothing imports them.
    ("scripts/fixtures/audit/AttributedAxioms.lean", "axiom"): 2,
    ("scripts/fixtures/audit/Extern.lean", "extern"): 1,
    ("scripts/fixtures/audit/Extern.lean", "opaque"): 1,
    # The compiled trust audit looks for `sorryAx` by name.
    ("scripts/AuditCompiledTrust.lean", "sorry_ax"): 3,
    # Freeing a replayed module's imported regions is unsafe; the replayer
    # only runs as a script and adds no declaration anything imports.
    ("scripts/KernelReplay.lean", "unsafe_declaration"): 2,
})


def scan_paths(root: Path) -> list[str]:
    """Top-level files and directories holding Lean or Rocq sources."""
    paths = []
    for entry in sorted(root.iterdir()):
        if entry.name.startswith(".") or entry.name in EXCLUDED:
            continue
        if entry.is_dir():
            if any(path.suffix in SOURCE_SUFFIXES for path in entry.rglob("*")):
                paths.append(entry.name)
        elif entry.suffix in SOURCE_SUFFIXES:
            paths.append(entry.name)
    return paths


def scoped_theorem(source_lines: list[str], line: int) -> str | None:
    """Name of the theorem a `set_option ... in` at `line` scopes, if any."""
    for text in source_lines[line:]:
        match = DECLARATION.match(text)
        if match:
            return match.group(2) if match.group(1) == "theorem" else None
    return None


def approved_guard(source_lines: list[str], line: int) -> bool:
    """Whether the `#guard_msgs` at `line` guards a `#` command and expects no `sorry`."""
    if source_lines[line - 1].strip() != GUARD_MSGS:
        return False
    guarded = next((text.strip() for text in source_lines[line:] if text.strip()), "")
    if not guarded.startswith("#"):
        return False
    expected = []
    index = line - 2
    if index >= 0 and source_lines[index].rstrip().endswith("-/"):
        while index >= 0:
            expected.append(source_lines[index])
            if "/--" in source_lines[index]:
                break
            index -= 1
    text = "\n".join(expected).lower()
    return "sorry" not in text and "declaration uses" not in text


@dataclass
class Review:
    """The gate's verdict on each scanner finding, before the whole-tree checks."""
    errors: list[str] = field(default_factory=list)
    # (kind, path, line) of every finding the gate accepts.
    approved: set[tuple[str, str, int]] = field(default_factory=set)
    seen: set[str] = field(default_factory=set)  # manifest debt ids found in place
    references: Counter[tuple[str, str]] = field(default_factory=Counter)
    lakefile_enables: int = 0


def review(findings: list[dict], expected: dict[str, dict]) -> Review:
    """Approve or reject each finding; scripts/status_report.sh reuses the approvals."""
    result = Review()
    sources: dict[str, list[str]] = {}
    debt_theorems = set()
    suppressions: list[tuple[str, int]] = []
    for finding in findings:
        kind = finding["kind"]
        path = finding["path"]
        line = finding["line"]
        if (path, kind) in EXPECTED_REFERENCES:
            result.references[(path, kind)] += 1
            result.approved.add((kind, path, line))
            continue
        if path not in sources:
            sources[path] = (ROOT / path).read_text(encoding="utf-8", errors="replace").splitlines()
        source_lines = sources[path]
        if not isinstance(line, int) or not 1 <= line <= len(source_lines):
            result.errors.append(f"invalid {kind} location: {path}:{line}")
            continue
        text = source_lines[line - 1].strip()
        if kind == "warning_as_error":
            if text in ENABLE_WARNING_AS_ERROR:
                result.approved.add((kind, path, line))
                continue
            if path == "lakefile.lean" and text.rstrip(",") == LAKEFILE_WARNING_AS_ERROR:
                result.lakefile_enables += 1
                result.approved.add((kind, path, line))
                continue
            suppressions.append((path, line))
            continue
        if kind == "guard_msgs":
            if approved_guard(source_lines, line):
                result.approved.add((kind, path, line))
            else:
                result.errors.append(f"unapproved #guard_msgs: {path}:{line}")
            continue
        if kind != "sorry":
            result.errors.append(f"unexpected {kind}: {path}:{line}")
            continue
        match = MARKER.search(source_lines[line - 1])
        if not match:
            result.errors.append(f"unnamed sorry: {path}:{line}")
            continue
        debt_id = match.group(1)
        item = expected.get(debt_id)
        if item is None or item["path"] != path or debt_id in result.seen:
            result.errors.append(f"unapproved or duplicate debt {debt_id}: {path}:{line}")
            continue
        nearby = "\n".join(source_lines[max(0, line - 12) : line])
        theorem_names = THEOREM.findall(nearby)
        if not theorem_names or theorem_names[-1] != item["theorem"]:
            result.errors.append(f"debt {debt_id} is not in theorem {item['theorem']}")
            continue
        result.seen.add(debt_id)
        result.approved.add((kind, path, line))
        debt_theorems.add((path, item["theorem"]))

    scoped = set()
    for path, line in suppressions:
        source_lines = sources[path]
        target = (path, scoped_theorem(source_lines, line))
        if (source_lines[line - 1].strip() != DISABLE_WARNING_AS_ERROR
                or target not in debt_theorems or target in scoped):
            result.errors.append(f"unapproved warningAsError: {path}:{line}")
            continue
        scoped.add(target)
        result.approved.add(("warning_as_error", path, line))
    return result


def load_manifest() -> dict[str, dict]:
    expected_list = json.loads(MANIFEST.read_text(encoding="utf-8"))
    expected = {item["id"]: item for item in expected_list}
    if len(expected) != len(expected_list):
        raise ValueError("duplicate proof-debt id in manifest")
    return expected


def main() -> int:
    expected = load_manifest()
    paths = scan_paths(ROOT)
    result = subprocess.run(
        [str(ROOT / "scripts/audit_placeholders.sh"), "--json", *paths],
        cwd=ROOT,
        check=True,
        capture_output=True,
        text=True,
    )
    verdict = review(json.loads(result.stdout)["findings"], expected)
    errors = verdict.errors
    if verdict.lakefile_enables != 1:
        errors.append(f"lakefile.lean enables warningAsError {verdict.lakefile_enables} times, expected 1")
    for (path, kind), count in EXPECTED_REFERENCES.items():
        if verdict.references[(path, kind)] != count:
            errors.append(f"expected reference {path} has {verdict.references[(path, kind)]} {kind} "
                          f"findings, expected {count}")
    for debt_id in expected.keys() - verdict.seen:
        errors.append(f"manifest debt missing from sources: {debt_id}")
    if errors:
        print("\n".join(errors), file=sys.stderr)
        return 1
    print(f"Trust scan passed with {len(verdict.seen)} named, unproved proof obligations "
          f"across {', '.join(paths)}.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
