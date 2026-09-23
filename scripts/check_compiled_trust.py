#!/usr/bin/env python3
"""Audit elaborated source declarations and transitive axiom dependencies.

The textual gate still enforces named source markers. This complementary gate
reads actual Lean declarations, requiring source direct and propagated sorry
dependence to match the manifest (or no debt at all in test scope), and rejects
project axioms, unsafe declarations, runtime
overrides, and nonstandard axiom dependencies. It then replays every module of
the scope through the kernel (scripts/KernelReplay.lean), because a metaprogram
can add a declaration the kernel never checked and the axiom report cannot see
that. This is not a semantics audit of the standard library or the
compiler/FFI.
"""

import argparse
import json
from pathlib import Path
import re
import tempfile

from flocq_bridge import ROOT, lean_source_fingerprint, require_lean_source_snapshot, run


def audit_source(scope: str, modules: set[str]) -> str:
    """Reuse the compiled inspection for source or independently imported tests."""
    source = (ROOT / 'scripts/AuditCompiledTrust.lean').read_text()
    if scope == 'source':
        return source
    if scope != 'tests':
        raise ValueError('unknown compiled trust scope')
    # Both the declaration filter and module-coverage filter must change.
    marker = '"FloatSpec.src."'
    if source.count(marker) != 2:
        raise ValueError('compiled audit template changed; review test-scope filters')
    source = source.replace(marker, '"FloatSpec.Test."')
    return ''.join(f'import {name}\n' for name in sorted(modules)) + source


REPLAYED = re.compile(r'replayed (\S+) (\d+)')


def kernel_replay(targets: list[str]) -> dict[str, int]:
    """Replay each module (or .olean path) through the kernel; declarations per target.

    Any kernel rejection makes KernelReplay exit nonzero with a message on
    stderr, which `run` turns into an error.
    """
    output = run(['lake', 'env', 'lean', '--run', str(ROOT / 'scripts/KernelReplay.lean'), *targets],
                 timeout=1800)
    counts: dict[str, int] = {}
    for line in output.splitlines():
        match = REPLAYED.fullmatch(line)
        if match is None or match[1] in counts:
            raise RuntimeError(f'unexpected kernel replay output: {line!r}')
        counts[match[1]] = int(match[2])
    return counts


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
    replayed = report.get("kernel_replay", {})
    if set(replayed) != expected_modules:
        failures.append("kernel replay coverage differs from source files: " +
                        str(sorted(set(replayed) ^ expected_modules)))
    if not sum(replayed.values()):
        failures.append("kernel replay checked no declarations")
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
    parser.add_argument('--scope', choices=('source', 'tests'), default='source',
                        help='tests imports every FloatSpec/Test module and permits no proof debt')
    args = parser.parse_args()
    snapshot = lean_source_fingerprint()
    directory = ROOT / ('FloatSpec/src' if args.scope == 'source' else 'FloatSpec/Test')
    modules = {'.'.join(path.relative_to(ROOT).with_suffix('').parts)
               for path in directory.rglob('*.lean')}
    if not args.skip_build:
        targets = (['FloatSpec', 'FloatSpec.src.IEEE754.ComputableCompare']
                   if args.scope == 'source' else ['FloatSpecTests'])
        run(['lake', 'build', *targets], timeout=600)
    with tempfile.TemporaryDirectory(prefix='floatspec-compiled-trust-') as temporary:
        path = Path(temporary) / 'TrustInspection.lean'
        path.write_text(audit_source(args.scope, modules))
        report = json.loads(run(['lake', 'env', 'lean', str(path)], timeout=600))
    report['kernel_replay'] = kernel_replay(sorted(modules))
    require_lean_source_snapshot(snapshot)
    report["lean_source_sha256"] = snapshot
    report["fresh_build"] = not args.skip_build
    report['scope'] = args.scope
    if args.output:
        args.output.write_text(json.dumps(report, indent=2) + "\n")
    debts = (json.loads((ROOT / 'FloatSpec/docs/proof_debts.json').read_text())
             if args.scope == 'source' else [])
    failures = validate(report, debts, modules)
    if failures:
        raise SystemExit("\n".join(failures))
    print(f"Compiled trust audit passed: {report['project_declarations']} {args.scope} declarations, "
          f"{len(modules)} modules, {sum(report['kernel_replay'].values())} declarations "
          f"replayed through the kernel, {len(debts)} manifest-only direct/transitive proof debts.")


if __name__ == "__main__":
    main()
