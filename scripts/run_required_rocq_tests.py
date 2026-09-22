#!/usr/bin/env python3
"""Run the hosted live conformance suite; missing tools and skipped tests fail.

Individual test modules remain usable for Lean-only development. This entry
point is different: it requires a clean built reference at the repository pin,
sets the reference before importing any skip-decorated tests, and rejects even
one skip. It never treats an empty suite, interrupted run, or timeout as a pass.
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


LIVE_MODULES = (
    'test_flocq_bridge', 'test_native_ieee_bridge',
    'test_native_arithmetic_bridge', 'test_ieee_modes_bridge',
    'test_ieee_scale_bridge', 'test_ieee_integer_bridge',
    'test_round_pred_contracts', 'test_round_ne_point_contracts',
    'test_ulp_nearest_contracts', 'test_ulp_choice_contracts',
    'test_zaux_prelude_bridge', 'test_zaux_power_contracts',
    'test_zaux_division_contracts', 'test_pff_basic_contracts',
    'test_pff_integer_bridge', 'test_remainder_contracts',
)


def run_required_suite(suite, *, stream=sys.stderr):
    """A successful unittest exit alone is insufficient: skips are failures."""
    result = unittest.TextTestRunner(verbosity=2, stream=stream).run(suite)
    passed = result.wasSuccessful() and result.testsRun > 0 and not result.skipped
    return {
        'status': 'passed' if passed else 'failed',
        'tests_run': result.testsRun,
        'failures': [str(test) for test, _ in result.failures],
        'errors': [str(test) for test, _ in result.errors],
        'skipped': [(str(test), reason) for test, reason in result.skipped],
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
        report.update(run_required_suite(suite))
        require_lean_source_snapshot(report['lean_source_sha256'])
    except BaseException as error:
        report.update(status='error', error=f'{type(error).__name__}: {error}')
        raise
    finally:
        report['elapsed_seconds'] = round(time.monotonic() - started, 3)
        args.output.write_text(json.dumps(report, indent=2) + '\n')
    if report['status'] != 'passed':
        raise SystemExit('Required Rocq suite failed (including any skipped tests); see ' + str(args.output))
    print(f"Required Rocq suite passed: {report['tests_run']} tests, zero skips; {args.output}")


if __name__ == '__main__':
    main()
