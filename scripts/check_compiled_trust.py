#!/usr/bin/env python3
"""Audit elaborated source declarations and transitive axiom dependencies.

The textual gate still enforces named source markers. This complementary gate
reads actual Lean declarations, requiring direct and propagated sorry dependence
to match the manifest, and rejects project axioms, unsafe declarations, runtime
overrides, and nonstandard axiom dependencies. This is not a semantics audit of
the standard library or the compiler/FFI.
"""

import argparse
import json
from pathlib import Path

from flocq_bridge import ROOT, lean_source_fingerprint, require_lean_source_snapshot, run


def validate(report: dict, debts: list[dict], expected_modules: set[str]) -> list[str]:
    failures = []
    names = [debt["lean_name"] for debt in debts]
    if len(names) != len(set(names)):
        failures.append("duplicate compiled declaration in proof-debt manifest")
    if type(report["project_declarations"]) is not int or report["project_declarations"] <= 0:
        failures.append("empty or invalid compiled declaration count")
    if set(report["source_modules"]) != expected_modules:
        failures.append("compiled source module coverage differs from source files: " +
                        str(sorted(set(report["source_modules"]) ^ expected_modules)))
    for field in ("project_axioms", "unsafe_declarations", "runtime_overrides",
                  "unexpected_axiom_dependencies"):
        if report[field]:
            failures.append(f"{field}: {report[field]}")
    for field in ("direct_sorry", "transitive_sorry"):
        actual = report[field]
        if len(actual) != len(set(actual)) or set(actual) != set(names):
            failures.append(f"{field} differs from manifest: {actual}")
    return failures


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--skip-build", action="store_true",
                        help="inspect existing artifacts; caller must already have built current sources")
    parser.add_argument("--output", type=Path, help="save the observed compiler report")
    args = parser.parse_args()
    snapshot = lean_source_fingerprint()
    if not args.skip_build:
        run(["lake", "build", "FloatSpec", "FloatSpec.src.IEEE754.ComputableCompare"], timeout=600)
    report = json.loads(run(["lake", "env", "lean", str(ROOT / "scripts/AuditCompiledTrust.lean")],
                            timeout=600))
    require_lean_source_snapshot(snapshot)
    report["lean_source_sha256"] = snapshot
    report["fresh_build"] = not args.skip_build
    if args.output:
        args.output.write_text(json.dumps(report, indent=2) + "\n")
    debts = json.loads((ROOT / "FloatSpec/docs/proof_debts.json").read_text())
    modules = {".".join(path.relative_to(ROOT).with_suffix("").parts)
               for path in (ROOT / "FloatSpec/src").rglob("*.lean")}
    failures = validate(report, debts, modules)
    if failures:
        raise SystemExit("\n".join(failures))
    print(f"Compiled trust audit passed: {report['project_declarations']} source declarations, "
          f"{len(modules)} modules, {len(debts)} manifest-only direct/transitive proof debts.")


if __name__ == "__main__":
    main()
