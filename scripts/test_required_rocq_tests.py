"""Mutation controls for the required suite's fail-closed result policy."""

import io
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

from run_required_rocq_tests import run_required_suite


class RequiredSuiteTests(unittest.TestCase):
    def check_case(self, body):
        suite = unittest.TestSuite([unittest.FunctionTestCase(body)])
        return run_required_suite(suite, stream=io.StringIO())

    def test_positive_control(self):
        self.assertEqual(self.check_case(lambda: None)['status'], 'passed')

    def test_empty_is_not_success(self):
        report = run_required_suite(unittest.TestSuite(), stream=io.StringIO())
        self.assertEqual(report['status'], 'failed')

    def test_skip_is_not_success(self):
        def skipped():
            raise unittest.SkipTest('reference is unavailable')
        report = self.check_case(skipped)
        self.assertEqual(report['status'], 'failed')
        self.assertEqual(len(report['skipped']), 1)

    def test_failure_is_not_success(self):
        def failed():
            raise AssertionError('mutation detected')
        report = self.check_case(failed)
        self.assertEqual(report['status'], 'failed')
        self.assertEqual(len(report['failures']), 1)

    def test_error_or_timeout_is_not_success(self):
        def timed_out():
            raise TimeoutError('not a passing run')
        report = self.check_case(timed_out)
        self.assertEqual(report['status'], 'failed')
        self.assertEqual(len(report['errors']), 1)

    def test_interruption_propagates(self):
        def interrupted():
            raise KeyboardInterrupt()
        with self.assertRaises(KeyboardInterrupt):
            self.check_case(interrupted)

    def test_missing_reference_is_error_not_skipped_suite(self):
        with tempfile.TemporaryDirectory(prefix='floatspec-required-missing-') as directory:
            report = Path(directory) / 'result.json'
            process = subprocess.run(
                [sys.executable, str(Path(__file__).with_name('run_required_rocq_tests.py')),
                 '--flocq-dir', str(Path(directory) / 'missing'), '--output', str(report)],
                capture_output=True, text=True, timeout=30)
            self.assertNotEqual(process.returncode, 0)
            observed = json.loads(report.read_text())
            self.assertEqual(observed['status'], 'error')
            self.assertNotIn('tests_run', observed)

    def test_previous_evidence_is_not_overwritten(self):
        with tempfile.TemporaryDirectory(prefix='floatspec-required-existing-') as directory:
            report = Path(directory) / 'result.json'
            report.write_text('previous evidence\n')
            process = subprocess.run(
                [sys.executable, str(Path(__file__).with_name('run_required_rocq_tests.py')),
                 '--flocq-dir', directory, '--output', str(report)],
                capture_output=True, text=True, timeout=30)
            self.assertNotEqual(process.returncode, 0)
            self.assertEqual(report.read_text(), 'previous evidence\n')


if __name__ == '__main__':
    unittest.main()
