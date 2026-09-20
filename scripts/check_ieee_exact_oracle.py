#!/usr/bin/env python3
"""Independently check retained IEEE bridge observations, without rerunning them.

Usage: uv run scripts/check_ieee_exact_oracle.py --profile modes /path/report.json
The reported source hash belongs to that saved execution, not today's checkout.
"""

import argparse
import json
from pathlib import Path

from flocq_bridge import parse_result
import ieee_exact_oracle as oracle
import ieee_modes_bridge
import native_arithmetic_bridge


def check_report(report_path, profile):
    report_path = Path(report_path).resolve()
    report = json.loads(report_path.read_text())
    folder = report_path.parent
    if profile == "native":
        paths = ("native", "model", "compiled_model", "rocq")
        columns = native_arithmetic_bridge.COLUMNS
        expected = oracle.native_columns
        validate = native_arithmetic_bridge.validate_case
    elif profile == "modes":
        paths = ("lean", "compiled", "rocq")
        columns = ieee_modes_bridge.COLUMNS
        expected = oracle.mode_columns
        validate = ieee_modes_bridge.validate_case
    else:
        raise ValueError("profile must be native or modes")
    cases = [validate(case) for case in json.loads((folder / "cases.json").read_text())]
    if (not cases or report.get("status") != "passed"
            or any(report.get(key) != len(cases) for key in
                   ("cases", "compared_cases", "bootstrapped_lean_cases"))
            or report.get("columns") != list(columns)):
        raise ValueError("need a completed, nonempty report with matching columns and counts")
    batches = sorted(folder.glob("batch_*"))
    if not batches or batches[0].name != "batch_000000":
        raise ValueError("complete saved batches beginning at zero are required")
    assertions, mismatches = 0, []
    for index, batch in enumerate(batches):
        offset = int(batch.name.split("_")[1])
        end = int(batches[index + 1].name.split("_")[1]) if index + 1 < len(batches) else len(cases)
        if not 0 <= offset < end <= len(cases):
            raise ValueError("invalid saved batch offsets")
        inputs = cases[offset:end]
        observations = {
            path: parse_result((batch / f"{path}.out").read_text(),
                               "rocq" if path == "rocq" else "lean", len(inputs))
            for path in paths
        }
        failures, count = oracle.compare_columns(inputs, observations, columns, expected)
        assertions += count
        mismatches.extend(failures)
    return {"status": "mismatch" if mismatches else "passed",
            "method": "Independent exact oracle over saved observations; not a fresh execution",
            "input_report": str(report_path), "profile": profile, "cases": len(cases),
            "lean_source_sha256": report["lean_source_sha256"],
            "reference": report["reference"], "oracle_assertions": assertions,
            "mismatches": mismatches}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--profile", choices=("native", "modes"), required=True)
    parser.add_argument("report", type=Path)
    args = parser.parse_args()
    result = check_report(args.report, args.profile)
    print(json.dumps(result, indent=2))
    if result["mismatches"]:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
