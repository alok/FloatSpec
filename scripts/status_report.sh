#!/usr/bin/env bash
set -euo pipefail

usage() {
  cat <<'USAGE'
Usage: scripts/status_report.sh [--json|--markdown] [--write]

Generate FloatSpec proof-pipeline status from the current workspace.

Options:
  --json      Print JSON only.
  --markdown  Print Markdown only.
  --write     Write FloatSpec/docs/status.json and FloatSpec/docs/status.md.
  -h,--help   Show this help.

Default output is Markdown.
USAGE
}

format="markdown"
write=false

while [[ $# -gt 0 ]]; do
  case "$1" in
    --json)
      format="json"
      shift
      ;;
    --markdown)
      format="markdown"
      shift
      ;;
    --write)
      write=true
      shift
      ;;
    -h|--help)
      usage
      exit 0
      ;;
    *)
      echo "unknown argument: $1" >&2
      usage >&2
      exit 2
      ;;
  esac
done

json_tmp="$(mktemp)"
md_tmp="$(mktemp)"
audit_tmp="$(mktemp)"
trap 'rm -f "$json_tmp" "$md_tmp" "$audit_tmp"' EXIT

scripts/audit_placeholders.sh --json FloatSpec >"$audit_tmp"

python3 - "$audit_tmp" "$json_tmp" "$md_tmp" <<'PY'
import json
import pathlib
import subprocess
import sys
from collections import defaultdict

audit_path, json_path, md_path = sys.argv[1:4]
root = pathlib.Path("FloatSpec")
families = ["Core", "Calc", "Prop", "Pff", "IEEE754", "ErrorBound", "Other"]

with open(audit_path, encoding="utf-8") as f:
    audit = json.load(f)
# Every use of these is flagged, and scripts/check_proof_debts.py approves the
# reviewed ones line by line; they are not placeholders.
REVIEWED_USES = {"guard_msgs", "warning_as_error"}

lean_files = sorted(root.rglob("*.lean"))

def family(path: pathlib.Path) -> str:
    text = str(path)
    for fam in families[:-1]:
        if text == f"FloatSpec/src/{fam}.lean" or text.startswith(f"FloatSpec/src/{fam}/"):
            return fam
    return "Other"

by_module = {
    fam: {
        "lean_files": 0,
        "sorry": 0,
        "axiom": 0,
        "admit": 0,
        "placeholder": 0,
    }
    for fam in families
}

for path in lean_files:
    by_module[family(path)]["lean_files"] += 1

for finding in audit["findings"]:
    path = pathlib.Path(finding["path"])
    fam = family(path)
    kind = finding["kind"]
    if kind in ("sorry", "axiom", "admit"):
        by_module[fam][kind] += 1
    elif kind not in REVIEWED_USES:
        by_module[fam]["placeholder"] += 1

status = {
    "lean_files": len(lean_files),
    "sorry_count": audit["counts"].get("sorry", 0),
    "axiom_count": audit["counts"].get("axiom", 0),
    "admit_count": audit["counts"].get("admit", 0),
    "placeholder_semantics_count": sum(
        count
        for kind, count in audit["counts"].items()
        if kind not in {"sorry", "axiom", "admit"} | REVIEWED_USES
    ),
    "spec_weakened_count": audit["counts"].get("conclusion_as_hypothesis", 0),
    "by_module": by_module,
}

with open(json_path, "w", encoding="utf-8") as f:
    json.dump(status, f, indent=2, sort_keys=True)
    f.write("\n")

lines = [
    "# FloatSpec Generated Status",
    "",
    "Generated from the current workspace by `scripts/status_report.sh`.",
    "",
    "## Summary",
    "",
    f"- Lean files: {status['lean_files']}",
    f"- `sorry`: {status['sorry_count']}",
    f"- `axiom`: {status['axiom_count']}",
    f"- `admit`: {status['admit_count']}",
    f"- Placeholder/weakening findings: {status['placeholder_semantics_count']}",
    f"- Conclusion-as-hypothesis findings: {status['spec_weakened_count']}",
    "",
    "## By Module",
    "",
    "| Module | Lean files | sorry | axiom | admit | placeholder findings |",
    "|---|---:|---:|---:|---:|---:|",
]
for fam in families:
    data = by_module[fam]
    lines.append(
        f"| {fam} | {data['lean_files']} | {data['sorry']} | {data['axiom']} | "
        f"{data['admit']} | {data['placeholder']} |"
    )

lines.extend([
    "",
    "## Interpretation",
    "",
    "The default build covers the unified FloatSpec target. Any future placeholder finding is a merge blocker, not a separate build tier.",
    "",
    "These are textual heuristics, not a semantic audit. Zero placeholder findings does not establish faithful Flocq correspondence or absence of unreviewed mistakes. Use the compiled trust audit for proof dependencies and SOURCE_CONTRACT_REVIEW.md for the reviewed source-contract boundary.",
])

with open(md_path, "w", encoding="utf-8") as f:
    f.write("\n".join(lines))
    f.write("\n")
PY

if "$write"; then
  cp "$json_tmp" FloatSpec/docs/status.json
  cp "$md_tmp" FloatSpec/docs/status.md
fi

case "$format" in
  json)
    cat "$json_tmp"
    ;;
  markdown)
    cat "$md_tmp"
    ;;
esac
