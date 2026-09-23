#!/usr/bin/env python3
"""Run the hosted live conformance suite; missing tools and skipped tests fail.

Individual test modules remain usable for Lean-only development. This entry
point is different: it requires a clean built reference at the repository pin,
sets the reference before importing any skip-decorated tests, and rejects even
one skip or expected failure. It never treats an empty suite, an empty required
module, an interrupted run, or a timeout as a pass.
"""

import argparse
import json
import os
from pathlib import Path
import sys
import time
import unittest

from flocq_bridge import (configured_coqc, lean_source_fingerprint,
                          require_lean_source_snapshot, run, verify_reference)


# Every scripts/test_*.py module gated on FLOCQ_AUDIT_DIR, in either this tuple
# or EXCLUDED_MODULES; test_ci_coverage.py enforces the partition.
LIVE_MODULES = (
    'test_flocq_bridge', 'test_native_ieee_bridge',
    'test_native_arithmetic_bridge', 'test_ieee_modes_bridge',
    'test_ieee_scale_bridge', 'test_ieee_integer_bridge',
    'test_ieee_exact_oracle', 'test_round_pred_contracts',
    'test_round_ne_point_contracts', 'test_ulp_nearest_contracts',
    'test_ulp_choice_contracts', 'test_zaux_prelude_bridge',
    'test_zaux_power_contracts', 'test_zaux_division_contracts',
    'test_pff_bridge', 'test_pff_basic_contracts', 'test_pff_aux_bridge',
    'test_pff_statement_contracts',
    'test_pff_integer_bridge', 'test_pff_rounding_contracts',
    'test_lpo_contracts', 'test_double_rounding_contracts',
    'test_remainder_contracts', 'test_remainder_bridge',
    'test_model_adapter_bridge', 'test_flocq_exemplars', 'test_flocqsmith',
)

# Live modules that hosted CI cannot run, each with its measured reason. Empty:
# every live module runs. An entry here must say where the module runs instead.
EXCLUDED_MODULES: dict[str, str] = {}


class _CountingResult(unittest.TextTestResult):
    """Remember every started test so each required module is accounted for."""

    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs)
        self.started: list[str] = []

    def startTest(self, test):
        self.started.append(test.id())
        super().startTest(test)


def run_required_suite(suite, *, modules=(), stream=sys.stderr):
    """A successful unittest exit alone is insufficient: skips and expected
    failures are failures, and so is a required module that contributes no tests."""
    result = unittest.TextTestRunner(
        verbosity=2, stream=stream, resultclass=_CountingResult).run(suite)
    module_tests = {module: sum(test.startswith(module + '.') for test in result.started)
                    for module in modules}
    empty_modules = [module for module, count in module_tests.items() if count == 0]
    passed = (result.wasSuccessful() and result.testsRun > 0 and not result.skipped
              and not result.expectedFailures and not empty_modules)
    return {
        'status': 'passed' if passed else 'failed',
        'tests_run': result.testsRun,
        'module_tests': module_tests,
        'empty_modules': empty_modules,
        'failures': [str(test) for test, _ in result.failures],
        'errors': [str(test) for test, _ in result.errors],
        'skipped': [(str(test), reason) for test, reason in result.skipped],
        'expected_failures': [str(test) for test, _ in result.expectedFailures],
        'unexpected_successes': [str(test) for test in result.unexpectedSuccesses],
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--flocq-dir', required=True, type=Path)
    parser.add_argument('--output', required=True, type=Path)
    args = parser.parse_args()
    if args.output.exists():
        parser.error('output report already exists; do not overwrite previous evidence')
    args.output.parent.mkdir(parents=True, exist_ok=True)
    report = {'status': 'running', 'modules': list(LIVE_MODULES)}
    args.output.write_text(json.dumps(report, indent=2) + '\n')
    started = time.monotonic()
    try:
        reference = args.flocq_dir.resolve()
        report['reference'] = verify_reference(reference)
        coqc = configured_coqc(reference)
        report['rocq_version'] = run([coqc, '--version']).strip()
        report['lean_version'] = run(['lake', 'env', 'lean', '--version']).strip()
        report['lean_source_sha256'] = lean_source_fingerprint()
        # Evaluate skipUnless decorators only after establishing the live reference.
        os.environ['FLOCQ_AUDIT_DIR'] = str(reference)
        suite = unittest.defaultTestLoader.loadTestsFromNames(LIVE_MODULES)
        report.update(run_required_suite(suite, modules=LIVE_MODULES))
        require_lean_source_snapshot(report['lean_source_sha256'])
    except BaseException as error:
        report.update(status='error', error=f'{type(error).__name__}: {error}')
        raise
    finally:
        report['elapsed_seconds'] = round(time.monotonic() - started, 3)
        args.output.write_text(json.dumps(report, indent=2) + '\n')
    if report['status'] != 'passed':
        raise SystemExit('Required Rocq suite failed (a skip or expected failure also fails); see '
                         + str(args.output))
    print(f"Required Rocq suite passed: {report['tests_run']} tests, zero skips; {args.output}")


if __name__ == '__main__':
    main()
