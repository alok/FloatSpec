"""Harness regressions; set FLOCQ_AUDIT_DIR to include live prover/mutation tests."""

import contextlib
import io
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import time
import unittest
from unittest.mock import patch

import flocq_bridge as bridge


class RunnerTests(unittest.TestCase):
    def test_success_exit_code_and_stderr(self):
        self.assertEqual(bridge.run([sys.executable, '-c', 'print("ok")']), 'ok\n')
        with self.assertRaisesRegex(RuntimeError, 'command failed \\(7\\)'):
            bridge.run([sys.executable, '-c', 'raise SystemExit(7)'])
        with self.assertRaisesRegex(RuntimeError, 'unexpected stderr'):
            bridge.run([sys.executable, '-c', 'import sys; print("warning",file=sys.stderr)'])

    @unittest.skipUnless(os.name == "posix", "process-group cleanup is a POSIX contract")
    def test_timeout_stops_descendants(self):
        with tempfile.TemporaryDirectory() as directory:
            marker = Path(directory) / 'orphan-ran'
            child = f'import time,pathlib; time.sleep(1.5); pathlib.Path({str(marker)!r}).touch()'
            parent = f'import subprocess,sys,time; subprocess.Popen([sys.executable,"-c",{child!r}]); print("ready",flush=True); time.sleep(10)'
            with self.assertRaises(subprocess.TimeoutExpired) as caught:
                bridge.run([sys.executable, '-c', parent], timeout=1.0)
            self.assertIn(b'ready', caught.exception.output)
            time.sleep(1.8)
            self.assertFalse(marker.exists(), 'descendant survived the runner timeout')

    def test_interrupt_stops_process_group_and_is_reraised(self):
        original = subprocess.Popen.communicate
        interrupted = set()
        def interrupt_once(process, *args, **kwargs):
            if process.pid not in interrupted:
                interrupted.add(process.pid)
                raise KeyboardInterrupt()
            return original(process, *args, **kwargs)
        with patch.object(subprocess.Popen, 'communicate', interrupt_once), self.assertRaises(KeyboardInterrupt):
            bridge.run([sys.executable, '-c', 'import time; time.sleep(10)'])
        self.assertEqual(len(interrupted), 1)


class BatchTests(unittest.TestCase):
    def test_heavy_family_limits_and_smaller_requests(self):
        for family in bridge.BATCH_LIMITS:
            case = getattr(bridge, family + '_corpus')(844763, 0)[0]
            cases = [case] * 61
            batches = list(bridge.case_batches(cases, 200))
            self.assertEqual([offset for offset, _ in batches], [0, 25, 50])
            self.assertEqual([len(batch) for _, batch in batches], [25, 25, 11])
            self.assertEqual([len(batch) for _, batch in bridge.case_batches(cases, 10)],
                             [10, 10, 10, 10, 10, 10, 1])

    def test_order_duplicates_family_boundaries_and_offsets(self):
        light = bridge.Case('power', (2, 3))
        heavy = bridge.prim_arithmetic_corpus(844763, 0)[0]
        cases = [light] * 201 + [heavy] * 26 + [light, heavy, light]
        batches = list(bridge.case_batches(cases, 200))
        self.assertEqual([len(batch) for _, batch in batches], [200, 1, 25, 1, 1, 1, 1])
        self.assertEqual([case for _, batch in batches for case in batch], cases)
        offset = 0
        for actual, batch in batches:
            self.assertEqual(actual, offset)
            self.assertEqual(len({case.op for case in batch}), 1)
            offset += len(batch)
        self.assertEqual(offset, len(cases))

    def test_empty_and_invalid_request(self):
        self.assertEqual(list(bridge.case_batches([], 200)), [])
        for size in (0, -1):
            with self.assertRaisesRegex(ValueError, 'positive'):
                list(bridge.case_batches([], size))

    def test_mixed_light_families_share_batches(self):
        cases = [bridge.Case('power', (2, 3)), bridge.Case('div_eucl', (-7, 3))] * 103
        batches = list(bridge.case_batches(cases, 200))
        self.assertEqual([offset for offset, _ in batches], [0, 200])
        self.assertEqual([len(batch) for _, batch in batches], [200, 6])
        self.assertEqual([case for _, batch in batches for case in batch], cases)
        self.assertTrue(all(len({case.op for case in batch}) == 2 for _, batch in batches))

    def test_full_corpus_order_offsets_and_caps(self):
        cases = bridge.corpus(848933, 100)
        batches = list(bridge.case_batches(cases, 200))
        self.assertEqual(len(cases), 48614)
        self.assertEqual(len(batches), 378)
        self.assertEqual([case for _, batch in batches for case in batch], cases)
        offset = 0
        for actual, batch in batches:
            self.assertEqual(actual, offset)
            heavy_limit = bridge.BATCH_LIMITS.get(batch[0].op)
            self.assertLessEqual(len(batch), heavy_limit or 200)
            if heavy_limit is None:
                self.assertTrue(all(case.op not in bridge.BATCH_LIMITS for case in batch))
            else:
                self.assertEqual(len({case.op for case in batch}), 1)
            offset += len(batch)
        self.assertEqual(offset, len(cases))

    def check_driver(self, fail_batch=None, cases=None):
        if cases is None:
            cases = bridge.prim_arithmetic_corpus(844763, 0)[:61]
        with tempfile.TemporaryDirectory() as directory:
            folder = Path(directory)
            replay = folder / 'replay.json'
            replay.write_text(json.dumps([{'op': c.op, 'args': c.args} for c in cases]))
            output = folder / 'out'
            argv = ['bridge', '--flocq-dir', directory, '--coqc', 'coqc',
                    '--replay', str(replay), '--output', str(output),
                    '--batch-size', '200', '--skip-build']
            observed, bootstrapped = [], []
            def execute(batch, *_):
                if len(observed) == fail_batch:
                    raise subprocess.TimeoutExpired(['lean'], 120)
                observed.append(batch)
                return {name: [[0] * bridge.WIDTHS[c.op] for c in batch]
                        for name in ('lean', 'compiled', 'rocq')}
            def bootstrap(batch, *_):
                bootstrapped.append(batch)
            with (patch('sys.argv', argv),
                  patch.object(bridge, 'verify_reference', return_value='pinned'),
                  patch.object(bridge, 'run', return_value='metadata'),
                  patch.object(bridge, 'lean_source_fingerprint', return_value='snapshot'),
                  patch.object(bridge, 'execute', side_effect=execute),
                  patch.object(bridge, 'bootstrap_lean', side_effect=bootstrap),
                  contextlib.redirect_stdout(io.StringIO())):
                if fail_batch is None:
                    bridge.main()
                else:
                    with self.assertRaises(subprocess.TimeoutExpired):
                        bridge.main()
            report = json.loads((output / 'report.json').read_text())
            self.assertEqual(report['requested_batch_size'], 200)
            self.assertEqual(report['batch_size_limits'], bridge.BATCH_LIMITS)
            self.assertEqual(len(json.loads((output / 'cases.json').read_text())), len(cases))
            self.assertEqual(report['batch_policy'],
                             'ordered mixed-light and homogeneous capped-heavy')
            # Each observation key and the kernel count carry their honest path name.
            self.assertEqual({key: label.split(':')[0] for key, label in report['execution_paths'].items()},
                             {'rocq': 'rocq-vm', 'lean': 'lean-meta', 'compiled': 'lean-ir',
                              'bootstrapped_lean_cases': 'lean-kernel'})
            self.assertIn('bootstrapped_lean_cases', report)
            self.assertEqual(observed, bootstrapped)
            return report, observed, cases

    def test_driver_uses_cap_and_keeps_all_cases(self):
        report, batches, cases = self.check_driver()
        self.assertEqual(report['status'], 'passed')
        self.assertEqual([len(batch) for batch in batches], [25, 25, 11])
        self.assertEqual([case for batch in batches for case in batch], cases)
        for count in ('compared_cases', 'compiled_cases', 'bootstrapped_lean_cases'):
            self.assertEqual(report[count], 61)

    def test_later_batch_timeout_is_error_not_partial_pass(self):
        report, batches, _ = self.check_driver(fail_batch=1)
        self.assertEqual(report['status'], 'error')
        self.assertIn('TimeoutExpired', report['error'])
        self.assertEqual(len(batches), 1)
        for count in ('compared_cases', 'compiled_cases', 'bootstrapped_lean_cases'):
            self.assertEqual(report[count], 25)

    def test_one_mismatch_keeps_kernel_coverage_for_the_rest_of_its_batch(self):
        # Offline control: a planted lean-meta mismatch at case 30 (the second
        # batch) and a lean-ir-only mismatch at case 3. Both fail the run; only
        # case 30 leaves the lean-kernel file, and every batch says so.
        cases = [bridge.Case('power', (2, n)) for n in range(40)]
        planted = {30: ('lean', 'compiled'), 3: ('compiled',)}
        with tempfile.TemporaryDirectory() as directory:
            folder = Path(directory)
            replay = folder / 'replay.json'
            replay.write_text(json.dumps([{'op': c.op, 'args': c.args} for c in cases]))
            output = folder / 'out'
            argv = ['bridge', '--flocq-dir', directory, '--coqc', 'coqc', '--replay', str(replay),
                    '--output', str(output), '--batch-size', '25', '--skip-build']
            offsets, kernel = [0, 25], []

            def execute(batch, *_):
                offset = offsets.pop(0)
                rows = {name: [[offset + index] for index in range(len(batch))]
                        for name in ('lean', 'compiled', 'rocq')}
                for index, paths in planted.items():
                    for path in paths:
                        if offset <= index < offset + len(batch):
                            rows[path][index - offset] = [-1]
                return rows

            def bootstrap(batch, expected, _folder):
                kernel.extend(zip(batch, expected, strict=True))

            with (patch('sys.argv', argv),
                  patch.object(bridge, 'verify_reference', return_value='pinned'),
                  patch.object(bridge, 'run', return_value='metadata'),
                  patch.object(bridge, 'lean_source_fingerprint', return_value='snapshot'),
                  patch.object(bridge, 'execute', side_effect=execute),
                  patch.object(bridge, 'bootstrap_lean', side_effect=bootstrap),
                  contextlib.redirect_stdout(io.StringIO()),
                  self.assertRaisesRegex(SystemExit, '2 mismatches')):
                bridge.main()
            report = json.loads((output / 'report.json').read_text())
        self.assertEqual(report['status'], 'mismatch')
        self.assertEqual([(m['index'], m['paths']) for m in report['mismatches']],
                         [(3, ['compiled']), (30, ['lean', 'compiled'])])
        self.assertEqual(kernel, [(case, [index]) for index, case in enumerate(cases) if index != 30])
        self.assertEqual(report['bootstrapped_lean_cases'], 39)
        self.assertEqual(report['batches'], [
            {'offset': 0, 'cases': 25, 'mismatched_cases': 1, 'kernel_checked_cases': 25,
             'not_kernel_checked': []},
            {'offset': 25, 'cases': 15, 'mismatched_cases': 1, 'kernel_checked_cases': 14,
             'not_kernel_checked': [30]}])

    def test_driver_batches_mixed_light_families(self):
        cases = [bridge.Case('power', (2, 3)), bridge.Case('div_eucl', (-7, 3))] * 103
        report, batches, replay = self.check_driver(cases=cases)
        self.assertEqual(report['status'], 'passed')
        self.assertEqual([len(batch) for batch in batches], [200, 6])
        self.assertEqual([case for batch in batches for case in batch], replay)
        for count in ('compared_cases', 'compiled_cases', 'bootstrapped_lean_cases'):
            self.assertEqual(report[count], len(cases))


class ParserTests(unittest.TestCase):

    def test_primitive_execution_domains_and_replayable_corpora(self):
        for family, width in (('prim_arithmetic', 70), ('prim_helpers', 68), ('prim_round', 16)):
            generate = getattr(bridge, family + '_corpus')
            cases = generate(844763, 3)
            self.assertEqual(cases, generate(844763, 3))
            self.assertNotEqual(cases, generate(844769, 3))
            self.assertEqual(len(cases), len(set(cases)))
            self.assertEqual({case.args[0] for case in cases}, set(range(5)))
            self.assertEqual(bridge.WIDTHS[family], width)
        for family, args in (
            ('prim_arithmetic', (5, 3, 0, 1, 0, 3, 0, 1, 0)),
            ('prim_arithmetic', (0, 4, 0, 1, 0, 3, 0, 1, 0)),
            ('prim_arithmetic', (0, 3, 0, 1, 0, 3, 2, 1, 0)),
            ('prim_arithmetic', (0, 3, 0, 1, 0, 3, 0, 0, 0)),
            ('prim_helpers', (0, 3, 0, 1, 0, 0, -1)),
            ('prim_helpers', (0, 3, 0, 1, 0, 0, 1 << 63)),
            ('prim_helpers', (0, 3, 0, -1, 0, 0, 0)),
            ('prim_round', (0, 2, -1, 0, 0, 1)),
            ('prim_round', (0, 0, -1, 0, 4, 1)),
            ('prim_round', (0, 0, -1, 0, 0, 0))):
            with self.subTest(family=family, args=args), self.assertRaises(ValueError):
                bridge.Case(family, args)
    def test_primitive_conversion_domain_wrapping_and_seed(self):
        cases = bridge.prim_conversion_corpus(843751, 7)
        self.assertEqual(cases, bridge.prim_conversion_corpus(843751, 7))
        self.assertNotEqual(cases, bridge.prim_conversion_corpus(843752, 7))
        self.assertEqual(len(cases), len(set(cases)))
        for args in ((3, 0, 3, -1), (3, 1, 1 << 63, 0),
                     (3, 0, (1 << 63) + 1, 0), (3, 0, (1 << 53) + 5, -1077)):
            self.assertIn(bridge.Case('prim_conversion', args), cases)
        for args in ((4, 0, 1, 0), (3, 2, 1, 0), (3, 0, 0, 0), (3, 0, -1, 0)):
            with self.assertRaises(ValueError):
                bridge.Case('prim_conversion', args)
        self.assertEqual(bridge.WIDTHS['prim_conversion'], 14)
        replay = Path(__file__).parent / 'fixtures/PrimitiveConversionReplay.json'
        self.assertEqual(len(json.loads(replay.read_text())), 4)
        self.assertTrue(all(bridge.Case(row['op'], tuple(row['args'])) in cases
                            for row in json.loads(replay.read_text())))

    def test_primitive_comparison_raw_domain_and_replay(self):
        cases = bridge.prim_comparison_corpus(841709, 5)
        self.assertEqual(cases, bridge.prim_comparison_corpus(841709, 5))
        self.assertNotEqual(cases, bridge.prim_comparison_corpus(841710, 5))
        self.assertEqual(len(cases), len(set(cases)))
        for args in ((3, 0, 3, -1, 3, 0, 6, -2),
                     (3, 1, 1, -1000000, 3, 0, 1, 1000000),
                     (0, 0, 1, 0, 0, 1, 1, 0)):
            self.assertIn(bridge.Case('prim_comparison', args), cases)
        for position, value in ((0, 4), (1, 2), (2, 0), (4, -1), (5, -1), (6, -2)):
            args = [3, 0, 3, -1, 3, 0, 6, -2]
            args[position] = value
            with self.assertRaises(ValueError):
                bridge.Case('prim_comparison', tuple(args))
        self.assertEqual(bridge.WIDTHS['prim_comparison'], 26)

    def test_normalization_domains_and_replayable_boundaries(self):
        cases = bridge.normalize_corpus(840691, 3)
        self.assertEqual(cases, bridge.normalize_corpus(840691, 3))
        self.assertNotEqual(cases, bridge.normalize_corpus(840692, 3))
        self.assertEqual(len(cases), len(set(cases)))
        self.assertEqual({c.args[2] for c in cases}, set(range(5)))
        for args in ((3, 4, 0, -9, -3, 0), (3, 4, 4, 0, 0, 1),
                     (53, 1024, 3, 1, -1075, 0), (1, 2, 0, 1, 2, 1)):
            self.assertIn(bridge.Case('normalize', args), cases)
        for position, bad in ((0, 0), (0, 4), (1, 3), (2, 5), (5, 2)):
            args = [3, 4, 0, -9, -3, 0]
            args[position] = bad
            with self.assertRaises(ValueError):
                bridge.Case('normalize', tuple(args))
        self.assertEqual(bridge.WIDTHS['normalize'], 12)
        self.assertEqual(bridge.WIDTHS['ieee_round'], 21)

    def test_frexp_corpus_uses_its_actual_source_domain(self):
        cases = bridge.single_frexp_corpus(836641, 3)
        self.assertEqual(cases, bridge.single_frexp_corpus(836641, 3))
        self.assertNotEqual(cases, bridge.single_frexp_corpus(836642, 3))
        self.assertEqual(len(cases), len(set(cases)))
        self.assertIn(bridge.Case('single_frexp', (8, 2, 3, 0, 1, -7)), cases)
        self.assertIn(bridge.Case('single_frexp', (8, 3, 3, 1, 1, -8)), cases)
        self.assertIn(bridge.Case('single_frexp', (1, -3, 0, 1, 1, 0)), cases)
        for position, value in ((0, 0), (0, -1), (2, 4), (3, 2), (4, 0)):
            args = [8, 2, 3, 0, 1, -7]
            args[position] = value
            with self.assertRaises(ValueError):
                bridge.Case('single_frexp', tuple(args))
        self.assertEqual(bridge.WIDTHS['single_frexp'], 11)

    def test_single_helpers_corpus_and_domains(self):
        cases = bridge.single_helpers_corpus(834619, 3)
        self.assertEqual(cases, bridge.single_helpers_corpus(834619, 3))
        self.assertNotEqual(cases, bridge.single_helpers_corpus(834620, 3))
        self.assertEqual(len(cases), len(set(cases)))
        self.assertEqual({c.args[0] for c in cases}, {1, 2, 3, 4, 8, 24, 53})
        self.assertEqual({c.args[2] for c in cases}, set(range(5)))
        self.assertEqual(bridge.WIDTHS['single_helpers'], 46)
        self.assertIn(bridge.Case('single_helpers', (1, 2, 0, 3, 0, 1, 0, 0, 1)), cases)
        for position, value in ((0, 0), (0, 4), (1, 3), (2, 5), (3, 4), (4, 2), (5, 0)):
            args = [3, 4, 0, 3, 0, 4, -2, 1, 9]
            args[position] = value
            with self.assertRaises(ValueError):
                bridge.Case('single_helpers', tuple(args))

    def test_raw_overflow_accepts_source_total_domain(self):
        cases = bridge.corpus(827419, 0)
        for args in ((-3, -4, 1, 0), (0, 1, 1, 1), (3, 3, 4, 0)):
            self.assertIn(bridge.Case('overflow', args), cases)
        self.assertEqual(bridge.WIDTHS['overflow'], 21)

    def test_saved_raw_overflow_counterexamples_remain_replayable(self):
        path = Path(__file__).parent / 'fixtures/RawOverflowReplay.json'
        cases = [bridge.Case(row['op'], tuple(row['args']))
                 for row in json.loads(path.read_text())]
        self.assertEqual(len(cases), 87)
        self.assertEqual(len(set(cases)), 87)
        self.assertTrue(all(case.op == 'overflow' and case.args[0] <= 0 for case in cases))

    def test_saved_raw_round_counterexamples_remain_replayable(self):
        path = Path(__file__).parent / 'fixtures/RawIEEERoundingReplay.json'
        cases = [bridge.Case(row['op'], tuple(row['args']))
                 for row in json.loads(path.read_text())]
        self.assertEqual(len(cases), 197)
        self.assertEqual(len(set(cases)), 197)
        self.assertTrue(all(case.op == 'ieee_round' and case.args[4] < 0 for case in cases))
        self.assertIn(bridge.Case('ieee_round', (3, 4, 4, 1, -7, -6, 0, 10)), cases)

    def test_raw_ieee_round_corpus_and_carrier_validation(self):
        cases = bridge.ieee_round_corpus(49241, 4)
        self.assertEqual(cases, bridge.ieee_round_corpus(49241, 4))
        self.assertNotEqual(cases, bridge.ieee_round_corpus(49242, 4))
        self.assertIn(bridge.Case('ieee_round', (-1, 1, 0, 0, -1, 0, 0, 1)), cases)
        self.assertIn(bridge.Case('ieee_round', (3, 3, 4, 1, 8, -3, 2, 8)), cases)
        for position, bad in ((2, 5), (3, 2), (6, 4), (7, 0), (7, -1)):
            args = [3, 4, 0, 0, -1, 0, 0, 1]
            args[position] = bad
            with self.assertRaises(ValueError):
                bridge.Case('ieee_round', tuple(args))

    def test_small_format_corpus_and_preconditions(self):
        cases = bridge.small_ieee_corpus(491731, 1)
        self.assertEqual(cases, bridge.small_ieee_corpus(491731, 1))
        self.assertNotEqual(cases, bridge.small_ieee_corpus(491732, 1))
        self.assertEqual({c.args[0] for c in cases}, {2, 3, 4, 8})
        self.assertEqual({c.args[2] for c in cases}, set(range(5)))
        for args in ((1, 4, 0), (3, 3, 0), (3, 4, 5)):
            with self.assertRaises(ValueError):
                bridge.Case('small_ieee', (*args, *(0, 0, 1, 0)*3))
        for operand in ((4, 0, 1, 0), (0, 2, 1, 0), (3, 0, 0, 0)):
            with self.assertRaises(ValueError):
                bridge.Case('small_ieee', (3, 4, 0, *operand, *(0, 0, 1, 0)*2))

    def test_source_snapshot_changes_with_inputs_not_documentation(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            for name in ("FloatSpec.lean", "lakefile.lean", "lean-toolchain", "lake-manifest.json"):
                (root / name).write_text(name)
            (root / "FloatSpec").mkdir()
            source = root / "FloatSpec/Test.lean"
            source.write_text("def x := 1")
            before = bridge.lean_source_fingerprint(root)
            (root / "FloatSpec/guide.md").write_text("A reading guide")
            self.assertEqual(before, bridge.lean_source_fingerprint(root))
            source.write_text("def x := 2")
            self.assertNotEqual(before, bridge.lean_source_fingerprint(root))
        with patch.object(bridge, "lean_source_fingerprint", return_value="changed"):
            with self.assertRaisesRegex(RuntimeError, "changed during verification"):
                bridge.require_lean_source_snapshot("original")

    def test_signed_lean_constructors(self):
        self.assertEqual(bridge.parse_result("[[Int.ofNat 0, Int.negSucc 2]]", "lean", 1), [[0, -3]])

    def test_wrapped_maximum_binary64_integer(self):
        # Lean wraps the 309-digit truncation result after its constructor.
        largest = ((1 << 53) - 1) << 971
        output = f"[[Int.ofNat\n  {largest}, Int.negSucc\n  {largest - 1}]]"
        self.assertEqual(bridge.parse_result(output, "lean", 1), [[largest, -largest]])

    def test_rocq_signed_output(self):
        self.assertEqual(bridge.parse_result(" = [[0; -3]]\n : list (list Z)", "rocq", 1), [[0, -3]])

    def test_reject_truncated_and_non_numeric_output(self):
        for value in ("[[0], ⋯]", "[[0], ...]", "[[sorry]]", "error: no file", "[]", "[[True]]"):
            with self.subTest(value=value), self.assertRaises(ValueError):
                bridge.parse_result(value, "lean", 1)

    def test_reject_wrong_result_count(self):
        with self.assertRaises(ValueError):
            bridge.parse_result("[[0], [1]]", "lean", 1)

    def test_reject_empty_rows(self):
        with self.assertRaises(ValueError):
            bridge.parse_result("[[]]", "lean", 1)

    def test_all_paths_and_columns_are_checked(self):
        for op in bridge.OPS:
            case = next(case for case in bridge.corpus(17, 0) if case.op == op)
            width = bridge.WIDTHS[op]
            for path in ("lean", "compiled"):
                for column in range(width):
                    observations = {name: [[0] * width] for name in ("lean", "compiled", "rocq")}
                    observations[path][0][column] = 1
                    self.assertEqual(bridge.compare([case], observations)[0]["paths"], [path])
        with self.assertRaises(ValueError):
            bridge.compare([bridge.Case("power", (2, 1))], {"lean": [[2]], "rocq": [[2]]})
        with self.assertRaises(ValueError):
            bridge.compare([bridge.Case("power", (2, 1))],
                           {name: [[2, 3]] for name in ("lean", "compiled", "rocq")})

    def test_seed_replay_and_api_coverage(self):
        first = bridge.corpus(17, 10)
        self.assertEqual(first, bridge.corpus(17, 10))
        self.assertNotEqual(first, bridge.corpus(18, 10))
        self.assertEqual({case.op for case in first}, set(bridge.OPS))
        self.assertIn(bridge.Case("div_eucl", (7, 0)), first)
        self.assertIn(bridge.Case("power", (2, -1)), first)
        self.assertIn(bridge.Case("div_eucl", (7, -3)), first)
        self.assertIn(bridge.Case("bits64", (-1,)), first)
        self.assertIn(bridge.Case("bits32", (1 << 32,)), first)
        self.assertIn(bridge.Case("bit_fields", (-3, -2, 1, -3, -2, -1)), first)
        self.assertIn(bridge.Case("validity", (3, 4, 0, 1, 0)), first)
        self.assertIn(bridge.Case("validity", (3, 4, 0, 4, -2)), first)
        self.assertIn(bridge.Case("validity", (-1, 1, 1, 1, -5)), first)
        self.assertIn(bridge.Case("nearby", (-1, 4, 0, 0, 1, 0)), first)
        self.assertIn(bridge.Case("nearby", (53, 54, 4, 1, 1, -55)), first)
        self.assertIn(bridge.Case("neighbors", (3, 4, 3, 0, 4, -4)), first)
        self.assertIn(bridge.Case("neighbors", (1, 2, 0, 1, 1, 0)), first)
        self.assertIn(bridge.Case("comparison", (0, 1, 0, 0, 1, 0, 0, 1, 1, 0)), first)
        self.assertIn(bridge.Case("comparison", (3, 4, 3, 0, 4, -4, 3, 1, 4, -4)), first)

    def test_replay_input_validation(self):
        for op, args in (("no_such_function", ()), ("power", (2,)),
                         ("power", (2, "sorry")), ("power", (2, True)),
                         ("location", (4, 2, -1)), ("round", (2, 0, 1)),
                         ("sqrt", (1, 4, 0, 0)), ("overflow", (3, 4, 5, 0)),
                         ("overflow", (3, 4, 0, 2)),
                         ("bit_fields", (0, 0, 2, 0, 0, 0)),
                         ("validity", (3, 4, 0, 0, 0)),
                         ("validity", (3, 4, 2, 1, 0)),
                         ("nearby", (3, 4, 5, 0, 1, 0)),
                         ("nearby", (3, 4, 0, 2, 1, 0)),
                         ("nearby", (3, 4, 0, 0, 0, 0)),
                         ("neighbors", (0, 4, 0, 0, 1, 0)),
                         ("neighbors", (3, 3, 0, 0, 1, 0)),
                         ("neighbors", (3, 4, 4, 0, 1, 0)),
                         ("neighbors", (3, 4, 0, 2, 1, 0)),
                         ("neighbors", (3, 4, 3, 0, 0, 0)),
                         ("comparison", (3, 4, 4, 0, 1, 0, 0, 0, 1, 0)),
                         ("comparison", (3, 4, 0, 2, 1, 0, 0, 0, 1, 0)),
                         ("comparison", (3, 4, 0, 0, 1, 0, 3, 0, 0, 0))):
            with self.subTest(op=op, args=args), self.assertRaises(ValueError):
                bridge.Case(op, args)


@unittest.skipUnless(os.environ.get("FLOCQ_AUDIT_DIR"), "live test requires FLOCQ_AUDIT_DIR")
class LiveTests(unittest.TestCase):

    def test_mixed_light_families_and_bootstrap(self):
        counts, cases = {}, []
        for case in bridge.corpus(848933, 0):
            if case.op not in bridge.BATCH_LIMITS and counts.get(case.op, 0) < 3:
                cases.append(case)
                counts[case.op] = counts.get(case.op, 0) + 1
        self.assertEqual(len(counts), 29)
        self.assertEqual(len(cases), 87)
        batches = list(bridge.case_batches(cases, 200))
        self.assertEqual(len(batches), 1)
        self.assertEqual(batches[0], (0, cases))
        flocq = Path(os.environ['FLOCQ_AUDIT_DIR']).resolve()
        with tempfile.TemporaryDirectory(prefix='floatspec-mixed-light-live-') as directory:
            folder = Path(directory)
            rows = bridge.execute(cases, flocq, bridge.configured_coqc(flocq), folder)
            self.assertEqual(bridge.compare(cases, rows), [])
            bridge.bootstrap_lean(cases, rows['rocq'], folder)

    def test_primitive_execution_literal_columns(self):
        flocq = Path(os.environ['FLOCQ_AUDIT_DIR']).resolve()
        one = [3, 0, 4503599627370496, -52]
        two = [3, 0, 4503599627370496, -51]
        zero = [0, 0, 0, 0]
        half = [3, 0, 4503599627370496, -53]
        ulp = [3, 0, 4503599627370496, -104]
        up = [3, 0, 4503599627370497, -52]
        down = [3, 0, 9007199254740991, -53]
        cases = [
            bridge.Case('prim_arithmetic', (0, *one, *one)),
            bridge.Case('prim_helpers', (0, *one, 1, 2102)),
            bridge.Case('prim_round', (0, 0, 1, 0, 0, 1))]
        expected = [
            one + one + two + [1, 1] + one + one + one + two + zero +
                one + one + two + zero + one + one + one + two + zero,
            [1] + two + [3, 0, 4622346883170304, -41] + two + two + two +
                ulp + up + down + two + half + [1] + half + [2102] +
                two + ulp + up + down + half + [1],
            [3, 0, 1, 0] + one + one + one]
        with tempfile.TemporaryDirectory(prefix='floatspec-primitive-execution-literal-') as directory:
            folder = Path(directory)
            rows = bridge.execute(cases, flocq, bridge.configured_coqc(flocq), folder)
            self.assertEqual(bridge.compare(cases, rows), [])
            self.assertEqual(rows['rocq'], expected)
            bridge.bootstrap_lean(cases, expected, folder)

    def test_primitive_execution_independent_mutations(self):
        flocq = Path(os.environ['FLOCQ_AUDIT_DIR']).resolve()
        one = (3, 0, 4503599627370496, -52)
        arithmetic = bridge.Case('prim_arithmetic', (0, *one, *one))
        helpers = bridge.Case('prim_helpers', (0, *one, 1, 2102))
        rounding = bridge.Case('prim_round', (0, 0, 1, 0, 0, 1))
        original = bridge.expressions
        # Every executable API/instance has its own mutation; the three
        # decomposition exponent projections are additionally checked alone.
        changes = [
            (arithmetic, "SFmul raw_x raw_y", "SFadd raw_x raw_y", 0, 4),
            (arithmetic, "SFdiv raw_x raw_y", "SFadd raw_x raw_y", 4, 8),
            (arithmetic, "SFadd raw_x raw_y", "SFmul raw_x raw_y", 8, 12),
            (arithmetic, "FaithfulPrimFloat.mul prim_x prim_y", "FaithfulPrimFloat.add prim_x prim_y", 14, 18),
            (arithmetic, "FaithfulPrimFloat.div prim_x prim_y", "FaithfulPrimFloat.add prim_x prim_y", 18, 22),
            (arithmetic, "FaithfulPrimFloat.sqrt prim_x", "FaithfulPrimFloat.add prim_x prim_y", 22, 26),
            (arithmetic, "FaithfulPrimFloat.add prim_x prim_y", "FaithfulPrimFloat.mul prim_x prim_y", 26, 30),
            (arithmetic, "FaithfulPrimFloat.sub prim_x prim_y", "FaithfulPrimFloat.add prim_x prim_y", 30, 34),
            (arithmetic, "(prim_x * prim_y)", "(prim_x + prim_y)", 34, 38),
            (arithmetic, "(prim_x / prim_y)", "(prim_x + prim_y)", 38, 42),
            (arithmetic, "(prim_x + prim_y)", "(prim_x * prim_y)", 42, 46),
            (arithmetic, "(prim_x - prim_y)", "(prim_x + prim_y)", 46, 50),
            (arithmetic, "Bmult .RNE x y", "Bplus .RNE x y", 50, 54),
            (arithmetic, "Bdiv .RNE x y", "Bplus .RNE x y", 54, 58),
            (arithmetic, "Bsqrt .RNE x", "Bplus .RNE x y", 58, 62),
            (arithmetic, "Bplus .RNE x y", "Bmult .RNE x y", 62, 66),
            (arithmetic, "Bminus .RNE x y", "Bplus .RNE x y", 66, 70),
            (helpers, "SFldexp raw (1)", "SFldexp raw (0)", 1, 5),
            (helpers, "FaithfulPrimFloat.of_uint63 u", "FaithfulPrimFloat.two", 5, 9),
            (helpers, "FaithfulPrimFloat.ldexp prim (1)", "prim", 9, 13),
            (helpers, "FaithfulPrimFloat.Z.ldexp prim (1)", "prim", 13, 17),
            (helpers, "FaithfulPrimFloat.ldshiftexp prim u", "prim", 17, 21),
            (helpers, "FaithfulPrimFloat.ulp prim", "FaithfulPrimFloat.two", 21, 25),
            (helpers, "FaithfulPrimFloat.next_up prim", "prim", 25, 29),
            (helpers, "FaithfulPrimFloat.next_down prim", "prim", 29, 33),
            (helpers, "FaithfulPrimFloat.two", "prim", 33, 37),
            (helpers, "FaithfulPrimFloat.Z.frexp prim", "(prim, (0 : Int))", 37, 42),
            (helpers, "FaithfulPrimFloat.frshiftexp prim", "(prim, u)", 42, 47),
            (helpers, "FaithfulPrimFloat.Bldexp .RNE x (1)", "x", 47, 51),
            (helpers, "FaithfulPrimFloat.Bulp' x", "x", 51, 55),
            (helpers, "FaithfulPrimFloat.Bsucc x", "x", 55, 59),
            (helpers, "FaithfulPrimFloat.Bpred x", "x", 59, 63),
            (helpers, "FaithfulPrimFloat.Bfrexp x", "(x, (0 : Int))", 63, 68),
            (helpers, " ++ [f.2]", " ++ [f.2 + 1]", 41, 42),
            (helpers, "Uint63.to_Z fs.2]", "Uint63.to_Z fs.2 + 1]", 46, 47),
            (helpers, " ++ [fb.2]", " ++ [fb.2 + 1]", 67, 68),
            (rounding, "binary_round_aux false (1) (0)", "binary_round_aux true (1) (0)", 0, 4),
            (rounding, "binary_round false (binaryPositiveOfNat 1", "binary_round true (binaryPositiveOfNat 1", 4, 8),
            (rounding, "binary_normalize (1) (0)", "binary_normalize (-1) (0)", 8, 12),
            (rounding, "binary_normalize_bsn .RNE (1)", "binary_normalize_bsn .RNE (-1)", 12, 16),
        ]
        self.assertEqual(len(changes), 40)
        for case, before, after, start, end in changes:
            def mutation(current):
                lean, rocq = original(current)
                self.assertEqual(lean.count(before), 1)
                return lean.replace(before, after), rocq
            with (self.subTest(mutation=before),
                  tempfile.TemporaryDirectory(prefix='floatspec-primitive-execution-mutation-') as directory,
                  patch.object(bridge, 'expressions', mutation)):
                rows = bridge.execute([case], flocq, bridge.configured_coqc(flocq), Path(directory))
                self.assertEqual(bridge.compare([case], rows)[0]['paths'], ['lean', 'compiled'])
                for path in ('lean', 'compiled'):
                    self.assertNotEqual(rows[path][0][start:end], rows['rocq'][0][start:end])
                    self.assertEqual(rows[path][0][:start], rows['rocq'][0][:start])
                    self.assertEqual(rows[path][0][end:], rows['rocq'][0][end:])

    def test_primitive_execution_fixture_rejects_noncomputable_client(self):
        source = (Path(__file__).parent / 'fixtures/PrimitiveExecution.lean').read_text()
        before = 'private def check_mul : StandardFloat'
        self.assertEqual(source.count(before), 1)
        with tempfile.TemporaryDirectory(prefix='floatspec-primitive-execution-marker-') as directory:
            path = Path(directory) / 'PrimitiveExecutionMutation.lean'
            path.write_text(source.replace(before, 'private noncomputable def check_mul : StandardFloat'))
            with self.assertRaisesRegex(RuntimeError, 'dependsOnNoncomputable'):
                bridge.run(['lake', 'env', 'lean', str(path)])
    def test_total_primitive_conversion_replays_and_valid_controls(self):
        flocq = Path(os.environ['FLOCQ_AUDIT_DIR']).resolve()
        data = json.loads((Path(__file__).parent / 'fixtures/PrimitiveConversionReplay.json').read_text())
        cases = [bridge.Case(row['op'], tuple(row['args'])) for row in data]
        cases += [bridge.Case('prim_conversion', args) for args in
                  ((3, 0, 1 << 52, -52), (0, 1, 1, 0), (1, 1, 1, 0),
                   (2, 0, 1, 0), (3, 1, 1, -1074), (3, 1, 1 << 63, 0))]
        values = [[3, 0, 6755399441055744, -52], [0, 0, 0, 0],
                  [3, 0, 1 << 52, -52], [3, 0, 1 << 50, -1074],
                  [3, 0, 1 << 52, -52], [0, 1, 0, 0], [1, 1, 0, 0],
                  [2, 0, 0, 0], [3, 1, 1, -1074], [0, 1, 0, 0]]
        valid = [0, 0, 0, 0, 1, 1, 1, 1, 1, 0]
        expected = [[v] + value + value + [1] + (value if v else [2, 0, 0, 0])
                    for v, value in zip(valid, values, strict=True)]
        with tempfile.TemporaryDirectory(prefix='floatspec-primitive-conversion-') as directory:
            rows = bridge.execute(cases, flocq, bridge.configured_coqc(flocq), Path(directory))
            self.assertEqual(bridge.compare(cases, rows), [])
            self.assertEqual(rows['rocq'], expected)
            bridge.bootstrap_lean(cases, rows['rocq'], Path(directory))

    def test_primitive_conversion_rejects_validation_wrap_and_rounding_mutations(self):
        flocq = Path(os.environ['FLOCQ_AUDIT_DIR']).resolve()
        original = bridge.expressions
        instances = ('letI : Prec_gt_0 (53 : Int) := ⟨by decide⟩; '
                     'letI : Prec_lt_emax (53 : Int) (1024 : Int) := ⟨by decide⟩; ')
        mutations = [
            ('reject-instead-of-convert', (3, 0, 3, -1),
             "FaithfulPrimFloat.B2Prim (BinarySingleNaN.SF2B' (prec := 53) (emax := 1024) raw)"),
            ('skip-uint63-wrap', (3, 0, 1 << 63, 0),
             'FaithfulPrimFloat.B2Prim (Binary.BldexpSingle .RNE '
             '(Binary.B2BSN (Binary.binary_normalize (prec := 53) (emax := 1024) '
             '.RNE 9223372036854775808 0 false)) 0)'),
            ('collapse-two-roundings', (3, 0, (1 << 53) + 5, -1077),
             'FaithfulPrimFloat.B2Prim (Binary.B2BSN '
             '(Binary.binary_normalize (prec := 53) (emax := 1024) '
             '.RNE 9007199254740997 (-1077) false))')]
        for name, args, replacement in mutations:
            case = bridge.Case('prim_conversion', args)
            def mutate(case):
                lean, rocq = original(case)
                before = 'let converted := FaithfulPrimFloat.SF2Prim raw; '
                self.assertEqual(lean.count(before), 1)
                return instances + lean.replace(before, f'let converted := {replacement}; '), rocq
            with (self.subTest(mutation=name),
                  tempfile.TemporaryDirectory(prefix='floatspec-conversion-mutation-') as directory,
                  patch.object(bridge, 'expressions', mutate)):
                rows = bridge.execute([case], flocq, bridge.configured_coqc(flocq), Path(directory))
                self.assertEqual(bridge.compare([case], rows)[0]['paths'], ['lean', 'compiled'])
                for path in ('lean', 'compiled'):
                    self.assertNotEqual(rows[path][0][1:9], rows['rocq'][0][1:9])
                    self.assertEqual(rows[path][0][:1], rows['rocq'][0][:1])
                    self.assertEqual(rows[path][0][9:], rows['rocq'][0][9:])

    def test_primitive_comparison_raw_and_validated_boundaries(self):
        flocq = Path(os.environ['FLOCQ_AUDIT_DIR']).resolve()
        cases = [bridge.Case('prim_comparison', args) for args in
                 ((3, 0, 3, -1, 3, 0, 6, -2),
                  (3, 1, 3, -1, 3, 1, 6, -2),
                  (3, 0, 1, 1, 3, 0, 16, 0),
                  (3, 0, 4503599627370496, -52, 3, 0, 4503599627370496, -51),
                  (0, 0, 1, 0, 0, 1, 1, 0),
                  (2, 0, 1, 0, 0, 1, 1, 0))]
        expected = [
            [1, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0],
            [-1, 0, 1, 1, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0],
            [1, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0],
            [-1, 0, 1, 1, 1, 1, -1, 0, 1, 1, -1, 0, 1, 1],
            [0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1],
            [2, 0, 0, 0, 1, 1, 2, 0, 0, 0, 2, 0, 0, 0]]
        expected = [row + row[10:14] + row[6:10] + row[10:14] for row in expected]
        with tempfile.TemporaryDirectory(prefix='floatspec-prim-comparison-') as directory:
            folder = Path(directory)
            rows = bridge.execute(cases, flocq, bridge.configured_coqc(flocq), folder)
            self.assertEqual(bridge.compare(cases, rows), [])
            self.assertEqual(rows['rocq'], expected)
            bridge.bootstrap_lean(cases, rows['rocq'], folder)

    def test_primitive_comparison_every_api_is_independently_observed(self):
        flocq = Path(os.environ['FLOCQ_AUDIT_DIR']).resolve()
        original = bridge.expressions
        # Strictly ordered canonical finite values distinguish each boolean
        # from its negation and each ordering from its reversed operands.
        case = bridge.Case('prim_comparison',
                           (3, 0, 4503599627370496, -52, 3, 0, 4503599627370496, -51))
        mutations = []
        for prefix, operands, start in (('SF', 'raw_x raw_y', 0),
                                       ('', 'prim_x prim_y', 6), ('B', 'x y', 10)):
            name = prefix + 'compare'
            token = f'FaithfulPrimFloat.{name} {operands}'
            mutations.append((token, f'FaithfulPrimFloat.{name} ' +
                              ' '.join(reversed(operands.split())), start))
            for delta, suffix in enumerate(('eqb', 'ltb', 'leb'), start=1):
                token = f'boolean (FaithfulPrimFloat.{prefix + suffix} {operands})'
                mutations.append((token, f'boolean (! (FaithfulPrimFloat.{prefix + suffix} {operands}))',
                                  start + delta))
        value_api = 'FloatSpec.IEEE754.ComputableCompare'
        for prefix, operands, start in (('SF', 'canonical_x canonical_y', 14),
                                       ('', 'prim_x prim_y', 18), ('B', 'x y', 22)):
            name = prefix + 'compareC'
            token = f'{value_api}.{name} {operands}'
            mutations.append((token, f'{value_api}.{name} ' +
                              ' '.join(reversed(operands.split())), start))
            for delta, suffix in enumerate(('eqbC', 'ltbC', 'lebC'), start=1):
                token = f'boolean ({value_api}.{prefix + suffix} {operands})'
                mutations.append((token, f'boolean (! ({value_api}.{prefix + suffix} {operands}))',
                                  start + delta))
        self.assertEqual(len(mutations), 24)
        for before, after, column in mutations:
            def mutated(case):
                lean, rocq = original(case)
                self.assertEqual(lean.count(before), 1)
                return lean.replace(before, after), rocq
            with (self.subTest(column=column),
                  tempfile.TemporaryDirectory(prefix='floatspec-prim-comparison-mutation-') as directory,
                  patch.object(bridge, 'expressions', mutated)):
                rows = bridge.execute([case], flocq, bridge.configured_coqc(flocq), Path(directory))
                self.assertEqual(bridge.compare([case], rows)[0]['paths'], ['lean', 'compiled'])
                for path in ('lean', 'compiled'):
                    changed = [n for n, (a, b) in enumerate(zip(rows[path][0], rows['rocq'][0], strict=True))
                               if a != b]
                    self.assertEqual(changed, [column])

    def check_calc_mutation(self, operation, expression):
        source = (Path(__file__).parent / 'fixtures/CalcBrackets.lean').read_text()
        before = f'let (q, location) := {expression}'
        self.assertEqual(source.count(before), 1)
        mutations = {
            'quotient': f'let result := {expression}\n  let q := result.1 + 1\n  let location := result.2',
            'location': f'let result := {expression}\n  let q := result.1\n  let location := Location.loc_Exact',
        }
        for name, replacement in mutations.items():
            with self.subTest(operation=operation, mutation=name):
                with tempfile.TemporaryDirectory(prefix='floatspec-calc-law-mutation-') as directory:
                    path = Path(directory) / 'CalcBracketsMutation.lean'
                    path.write_text(source.replace(before, replacement))
                    with self.assertRaises(RuntimeError) as caught:
                        bridge.run(['lake', 'env', 'lean', str(path)])
                    self.assertRegex(str(caught.exception),
                        r'Tactic `decide` (proved that the proposition|failed for proposition)')
                    witness = ('divisionLaw 2 1 0 3 0 0 = true' if operation == 'division'
                               else 'sqrtLaw 2 2 0 0 = true')
                    self.assertIn(witness, str(caught.exception))
                    self.assertIn('independent Calc bracket law failed', str(caught.exception))

    def test_independent_division_brackets_reject_mutations(self):
        self.check_calc_mutation('division',
            'FloatSpec.Calc.Div.Fdiv_core beta m1 e1 m2 e2 target')

    def test_independent_sqrt_brackets_reject_mutations(self):
        self.check_calc_mutation('square-root',
            'FloatSpec.Calc.Sqrt.Fsqrt_core beta mantissa exponent target')

    def test_independent_frexp_laws_reject_exponent_mutation(self):
        source = (Path(__file__).parent / 'fixtures/FrexpLaws.lean').read_text()
        before = 'let f := BinarySingleNaN.Bfrexp x'
        self.assertEqual(source.count(before), 1)
        changed = source.replace(before,
            'let result := BinarySingleNaN.Bfrexp x\n  let f := (result.1, result.2 + 1)')
        with tempfile.TemporaryDirectory(prefix='floatspec-frexp-law-mutation-') as directory:
            path = Path(directory) / 'FrexpLawsMutation.lean'
            path.write_text(changed)
            with self.assertRaises(RuntimeError) as caught:
                bridge.run(['lake', 'env', 'lean', str(path)])
            # Both the closed kernel assertion and compiled #eval must reject it.
            self.assertIn('(kernel)', str(caught.exception))
            self.assertIn('independent frexp domain law failed', str(caught.exception))

    def test_frexp_without_precision_separation_and_literal_outputs(self):
        flocq = Path(os.environ['FLOCQ_AUDIT_DIR']).resolve()
        cases = [bridge.Case('single_frexp', args) for args in
                 ((8, 2, 3, 0, 1, -7), (8, 3, 3, 1, 1, -8),
                  (1, -3, 0, 1, 1, 0), (3, 3, 3, 0, 4, -2),
                  (8, 2, 3, 0, 1, -8))]
        with tempfile.TemporaryDirectory(prefix='floatspec-frexp-domain-') as directory:
            folder = Path(directory)
            rows = bridge.execute(cases, flocq, bridge.configured_coqc(flocq), folder)
            self.assertEqual(bridge.compare(cases, rows), [])
            self.assertEqual(rows['rocq'], [
                [1, 3, 0, 1, -7, 3, 0, 1, -7, 0, 1],
                [1, 3, 1, 1, -8, 3, 1, 128, -8, -7, 1],
                [1, 0, 1, 0, 0, 0, 1, 0, 0, 5, 1],
                [1, 3, 0, 4, -2, 3, 0, 4, -3, 1, 1],
                [0, 2, 0, 0, 0, 2, 0, 0, 0, -12, 1]])
            bridge.bootstrap_lean(cases, rows['rocq'], folder)

    def test_frexp_fraction_and_exponent_mutations_are_rejected(self):
        flocq = Path(os.environ['FLOCQ_AUDIT_DIR']).resolve()
        case = bridge.Case('single_frexp', (8, 3, 3, 0, 1, -8))
        original = bridge.expressions
        for before, after, start, end in (
            ('standard fraction ++', 'standard (binarySingleNaNFloatToStandardFloat x) ++', 5, 9),
            ('[f.2, boolean', '[f.2 + 1, boolean', 9, 10)):
            def mutation(case):
                lean, rocq = original(case)
                self.assertEqual(lean.count(before), 1)
                return lean.replace(before, after), rocq
            with (self.subTest(mutation=before),
                  tempfile.TemporaryDirectory(prefix='floatspec-frexp-domain-mutation-') as directory,
                  patch.object(bridge, 'expressions', mutation)):
                rows = bridge.execute([case], flocq, bridge.configured_coqc(flocq), Path(directory))
                self.assertEqual(bridge.compare([case], rows)[0]['paths'], ['lean', 'compiled'])
                for path in ('lean', 'compiled'):
                    self.assertNotEqual(rows[path][0][start:end], rows['rocq'][0][start:end])
                    self.assertEqual(rows[path][0][:start], rows['rocq'][0][:start])
                    self.assertEqual(rows[path][0][end:], rows['rocq'][0][end:])

    def test_raw_overflow_positive_fallback_and_all_exports(self):
        flocq = Path(os.environ['FLOCQ_AUDIT_DIR']).resolve()
        cases = [bridge.Case('overflow', args) for args in
                 ((0, 1, 1, 0), (-1, 1, 1, 1), (0, -4, 0, 1),
                  (3, 3, 1, 0), (3, 4, 1, 1))]
        with tempfile.TemporaryDirectory(prefix='floatspec-raw-overflow-') as directory:
            rows = bridge.execute(cases, flocq, bridge.configured_coqc(flocq), Path(directory))
            bridge.bootstrap_lean(cases, rows['rocq'], Path(directory))
        self.assertEqual(bridge.compare(cases, rows), [])
        for index, result, valid in ((0, [3, 0, 1, 1], 0), (1, [3, 1, 1, 2], 0),
                                      (2, [1, 1, 0, 0], 1), (3, [3, 0, 7, 0], 1),
                                      (4, [3, 1, 7, 1], 1)):
            self.assertEqual(rows['rocq'][index], result + [valid] + result * 4)

    def test_raw_overflow_each_mantissa_column_is_checked(self):
        flocq = Path(os.environ['FLOCQ_AUDIT_DIR']).resolve()
        original = bridge.expressions
        case = bridge.Case('overflow', (0, 1, 1, 0))
        for column in (2, 7, 11, 15, 19):
            def mutated(case):
                lean, rocq = original(case)
                return f'({lean}).set {column} 0', rocq
            with (self.subTest(column=column),
                  tempfile.TemporaryDirectory(prefix='floatspec-overflow-mutation-') as directory,
                  patch.object(bridge, 'expressions', mutated)):
                rows = bridge.execute([case], flocq, bridge.configured_coqc(flocq), Path(directory))
            failures = bridge.compare([case], rows)
            self.assertEqual(len(failures), 1)
            self.assertEqual(failures[0]['paths'], ['lean', 'compiled'])

    def test_single_helpers_public_boundaries(self):
        flocq = Path(os.environ['FLOCQ_AUDIT_DIR']).resolve()
        cases = [bridge.Case('single_helpers', (p, emax, mode, kind, sign, m, e, shift, norm))
                 for mode in range(5) for p, emax, kind, sign, m, e, shift, norm in
                 ((1, 2, 0, 1, 1, 0, 1, 0), (1, 2, 3, 0, 1, 0, 0, 1),
                  (3, 4, 3, 0, 4, -2, 1, 9), (3, 4, 3, 1, 1, -4, -1, -1),
                  (3, 4, 3, 0, 1, -5, 0, -1),
                  (24, 128, 3, 0, 1 << 23, -23, 129, 9),
                  (53, 1024, 3, 0, 1 << 52, -52, -1075, -9))]
        with tempfile.TemporaryDirectory(prefix='floatspec-single-helper-boundaries-') as directory:
            folder = Path(directory)
            results = bridge.execute(cases, flocq, bridge.configured_coqc(flocq), folder)
            self.assertEqual(bridge.compare(cases, results), [])
            self.assertEqual(results['rocq'][0][37], -5)
            self.assertEqual(results['rocq'][1][21:25], [3, 0, 1, 0])
            self.assertEqual(results['rocq'][1][37], 0)
            self.assertEqual(results['rocq'][4][0:5], [0, 2, 0, 0, 0])
            bridge.bootstrap_lean(cases, results['rocq'], folder)

    def test_single_helper_mutations_are_independently_rejected(self):
        flocq = Path(os.environ['FLOCQ_AUDIT_DIR']).resolve()
        case = bridge.Case('single_helpers', (3, 4, 0, 3, 0, 4, -2, 1, 9))
        original = bridge.expressions
        changes = [
            ('binary_normalize (prec := 3) (emax := 4) .RNE',
             'binary_normalize (prec := 3) (emax := 4) .RNA', 5, 9),
            ('BinarySingleNaN.Bldexp .RNE x (1)', 'BinarySingleNaN.Bldexp .RNE x (-1)', 17, 21),
            (' ++ [f.2]', ' ++ [f.2 + 1]', 37, 38),
            ("BinarySingleNaN.Bsucc' x", 'BinarySingleNaN.Bpred x', 33, 37),
            ('Binary.shr_fexp (prec := 3) (emax := 4) (9)',
             'Binary.shr_fexp (prec := 3) (emax := 4) (0)', 38, 42)]
        for before, after, start, end in changes:
            def mutation(case):
                lean, rocq = original(case)
                self.assertEqual(lean.count(before), 1)
                return lean.replace(before, after), rocq

            with (self.subTest(mutation=before),
                  tempfile.TemporaryDirectory(prefix='floatspec-single-helper-mutation-') as directory,
                  patch.object(bridge, 'expressions', mutation)):
                results = bridge.execute([case], flocq, bridge.configured_coqc(flocq), Path(directory))
                mismatch = bridge.compare([case], results)[0]
                self.assertEqual(mismatch['paths'], ['lean', 'compiled'])
                for path in ('lean', 'compiled'):
                    self.assertNotEqual(results[path][0][start:end], results['rocq'][0][start:end])
                    self.assertEqual(results[path][0][:start], results['rocq'][0][:start])
                    self.assertEqual(results[path][0][end:], results['rocq'][0][end:])

    def test_single_helper_large_exponents_reduce_completely(self):
        flocq = Path(os.environ['FLOCQ_AUDIT_DIR']).resolve()
        case = bridge.Case('single_helpers',
                           (53, 1024, 0, 3, 0, 1 << 52, -52, -2048, 1))
        # This real binary64 boundary previously stopped the full run at the
        # default reduction threshold. Diagnostics must remain a hard error;
        # raising a bounded test-only resource limit must produce full values.
        with (tempfile.TemporaryDirectory(prefix='floatspec-helper-threshold-') as directory,
              patch.object(bridge, 'LEAN_HEADER', bridge.LEAN_HEADER.replace(
                  'set_option exponentiation.threshold 5000\n', ''))):
            with self.assertRaisesRegex(ValueError, r'exponent \d+ exceeds the threshold 256'):
                bridge.execute([case], flocq, bridge.configured_coqc(flocq), Path(directory))
        with tempfile.TemporaryDirectory(prefix='floatspec-helper-large-exponents-') as directory:
            folder = Path(directory)
            results = bridge.execute([case], flocq, bridge.configured_coqc(flocq), folder)
            self.assertEqual(bridge.compare([case], results), [])
            self.assertEqual(results['rocq'][0][17:21], [0, 0, 0, 0])
            bridge.bootstrap_lean([case], results['rocq'], folder)

    def test_raw_ieee_round_boundaries_and_degenerate_parameters(self):
        flocq = Path(os.environ['FLOCQ_AUDIT_DIR']).resolve()
        cases = [bridge.Case('ieee_round', args) for args in
                 ((3, 4, 0, 0, 9, -3, 0, 9),
                  (3, 4, 4, 0, 9, -3, 0, 9),
                  (3, 4, 0, 1, 0, -4, 0, 1),
                  (3, 4, 0, 0, -1, -4, 0, 1),
                  (0, 1, 0, 0, 1, 0, 0, 1),
                  (-1, 1, 2, 1, -2, 0, 2, 1),
                  (3, 3, 0, 0, 4, -2, 0, 4),
                  (-1, 1, 1, 0, -2, 2, 0, 2),
                  (3, 4, 4, 1, -7, -6, 0, 10),
                  (3, 3, 1, 1, -2, -5, 1, 2))]
        with tempfile.TemporaryDirectory(prefix='floatspec-ieee-round-') as directory:
            rows = bridge.execute(cases, flocq, bridge.configured_coqc(flocq), Path(directory))
            bridge.bootstrap_lean(cases, rows['rocq'], Path(directory))
        self.assertEqual(bridge.compare(cases, rows), [])
        self.assertEqual(rows['rocq'][0], [3, 0, 4, -2] * 4 + [1, 3, 0, 4, -2])
        self.assertEqual(rows['rocq'][1], [3, 0, 5, -2] * 4 + [1, 3, 0, 5, -2])
        self.assertEqual(rows['rocq'][2][:8], [0, 1, 0, 0] * 2)
        self.assertEqual(rows['rocq'][3][:8], [2, 0, 0, 0, 2, 0, 1, 0])
        self.assertEqual(rows['rocq'][6], [3, 0, 4, -2] * 4 + [1, 3, 0, 4, -2])
        self.assertEqual(rows['rocq'][7][:8], [0, 0, 0, 0] * 2)
        self.assertEqual(rows['rocq'][8][:8], [0, 1, 0, 0] * 2)
        self.assertEqual(rows['rocq'][9][:8], [0, 1, 0, 0] * 2)

    def test_raw_ieee_round_mode_mutation_is_rejected(self):
        flocq = Path(os.environ['FLOCQ_AUDIT_DIR']).resolve()
        original = bridge.expressions
        def mutated(case):
            lean, rocq = original(case)
            self.assertIn('.RNE', lean)
            return lean.replace('.RNE', '.RNA'), rocq
        case = bridge.Case('ieee_round', (3, 4, 0, 0, 9, -3, 0, 9))
        with (tempfile.TemporaryDirectory(prefix='floatspec-ieee-round-mutation-') as directory,
              patch.object(bridge, 'expressions', mutated)):
            rows = bridge.execute([case], flocq, bridge.configured_coqc(flocq), Path(directory))
        failures = bridge.compare([case], rows)
        self.assertEqual(len(failures), 1)
        self.assertEqual(failures[0]['paths'], ['lean', 'compiled'])

    def test_normalization_three_exports_and_signed_zero(self):
        flocq = Path(os.environ['FLOCQ_AUDIT_DIR']).resolve()
        cases = [bridge.Case('normalize', args) for args in
                 ((3, 4, 0, -9, -3, 0), (3, 4, 4, -9, -3, 0),
                  (3, 4, 0, 0, 20, 1), (3, 4, 0, 1, -5, 0),
                  (3, 4, 3, 1, -5, 0), (3, 4, 0, 15, 0, 0),
                  (3, 4, 1, -15, 0, 0), (1, 2, 0, 1, 0, 0))]
        with tempfile.TemporaryDirectory(prefix='floatspec-normalization-') as directory:
            folder = Path(directory)
            rows = bridge.execute(cases, flocq, bridge.configured_coqc(flocq), folder)
            self.assertEqual(bridge.compare(cases, rows), [])
            expected = [[3, 1, 4, -2], [3, 1, 5, -2], [0, 1, 0, 0],
                        [0, 0, 0, 0], [3, 0, 1, -4], [1, 0, 0, 0],
                        [3, 1, 7, 1], [3, 0, 1, 0]]
            self.assertEqual(rows['rocq'], [row * 3 for row in expected])
            bridge.bootstrap_lean(cases, rows['rocq'], folder)

    def test_normalization_each_export_is_independently_observed(self):
        flocq = Path(os.environ['FLOCQ_AUDIT_DIR']).resolve()
        original = bridge.expressions
        case = bridge.Case('normalize', (3, 4, 0, -9, -3, 0))
        for namespace, start in (('Binary', 0), ('_root_', 4), ('BinarySingleNaN', 8)):
            before = f'{namespace}.binary_normalize (prec := 3) (emax := 4) .RNE'
            after = before.replace('.RNE', '.RNA')
            def mutated(case):
                lean, rocq = original(case)
                self.assertEqual(lean.count(before), 1)
                return lean.replace(before, after), rocq
            with (self.subTest(namespace=namespace),
                  tempfile.TemporaryDirectory(prefix='floatspec-normalization-mutation-') as directory,
                  patch.object(bridge, 'expressions', mutated)):
                rows = bridge.execute([case], flocq, bridge.configured_coqc(flocq), Path(directory))
                self.assertEqual(bridge.compare([case], rows)[0]['paths'], ['lean', 'compiled'])
                for path in ('lean', 'compiled'):
                    self.assertNotEqual(rows[path][0][start:start+4], rows['rocq'][0][start:start+4])
                    self.assertEqual(rows[path][0][:start], rows['rocq'][0][:start])
                    self.assertEqual(rows[path][0][start+4:], rows['rocq'][0][start+4:])

    def test_round_adapter_rejects_invalid_results_and_preserves_valid_nan(self):
        flocq = Path(os.environ['FLOCQ_AUDIT_DIR']).resolve()
        cases = [bridge.Case('ieee_round', args) for args in
                 ((3, 0, 1, 0, 1, 0, 0, 1), (3, 4, 0, 0, -1, -4, 0, 1),
                  (3, 4, 0, 1, 0, -4, 0, 1), (0, 1, 1, 0, 1, 0, 0, 1))]
        with tempfile.TemporaryDirectory(prefix='floatspec-round-adapter-') as directory:
            folder = Path(directory)
            rows = bridge.execute(cases, flocq, bridge.configured_coqc(flocq), folder)
            self.assertEqual(bridge.compare(cases, rows), [])
            self.assertEqual([row[16:] for row in rows['rocq']],
                             [[0, 2, 0, 0, 0], [1, 2, 0, 0, 0], [1, 0, 1, 0, 0],
                              [1, 0, 0, 0, 0]])
            bridge.bootstrap_lean(cases, rows['rocq'], folder)

    def test_round_adapter_columns_are_not_hidden_by_raw_rounding(self):
        flocq = Path(os.environ['FLOCQ_AUDIT_DIR']).resolve()
        original = bridge.expressions
        case = bridge.Case('ieee_round', (3, 4, 0, 0, 9, -3, 0, 9))
        for column in (16, 19):
            def mutated(case):
                lean, rocq = original(case)
                return f'({lean}).set {column} 0', rocq
            with (self.subTest(column=column),
                  tempfile.TemporaryDirectory(prefix='floatspec-round-adapter-mutation-') as directory,
                  patch.object(bridge, 'expressions', mutated)):
                rows = bridge.execute([case], flocq, bridge.configured_coqc(flocq), Path(directory))
                self.assertEqual(bridge.compare([case], rows)[0]['paths'], ['lean', 'compiled'])
                for path in ('lean', 'compiled'):
                    self.assertEqual(rows[path][0][:16], rows['rocq'][0][:16])
                    self.assertNotEqual(rows[path][0][16:], rows['rocq'][0][16:])

    def test_small_format_arithmetic_and_invalid_conversion(self):
        flocq = Path(os.environ['FLOCQ_AUDIT_DIR']).resolve()
        one, half, invalid = (3, 0, 4, -2), (3, 0, 4, -3), (3, 0, 1, 5)
        cases = [bridge.Case('small_ieee', (3, 4, mode, *one, *half, *invalid))
                 for mode in range(5)]
        with tempfile.TemporaryDirectory(prefix='floatspec-small-ieee-') as directory:
            rows = bridge.execute(cases, flocq, bridge.configured_coqc(flocq), Path(directory))
            bridge.bootstrap_lean(cases, rows['rocq'], Path(directory))
        self.assertEqual(bridge.compare(cases, rows), [])
        for row in rows['lean']:
            self.assertEqual(row[:3], [1, 1, 0])
            self.assertEqual(row[11:15], [2, 0, 0, 0])
            self.assertEqual(row[15:19], [3, 0, 6, -2])
            self.assertEqual(row[-4:], [2, 0, 0, 0])
            self.assertEqual(len(row), 87)
            self.assertEqual(row[15:39], row[39:63])
            self.assertEqual(row[15:39], row[63:87])

    def test_small_format_add_to_subtract_mutation_is_rejected(self):
        flocq = Path(os.environ['FLOCQ_AUDIT_DIR']).resolve()
        original = bridge.expressions
        one = (3, 0, 4, -2)
        case = bridge.Case('small_ieee', (3, 4, 0, *one, *one, *one))
        # Change one independently serialized public entry point at a time.
        for symbol, start in (('Binary.Bplus', 15), ('BinarySingleNaN.Bplus', 39),
                              ('FloatSpec.IEEE754.BinarySingleNaN.Source.Bplus', 63)):
            with self.subTest(symbol=symbol):
                def mutated(case):
                    lean, rocq = original(case)
                    token = f'({symbol} '
                    self.assertEqual(lean.count(token), 1)
                    return lean.replace(token, token.replace('Bplus', 'Bminus')), rocq
                with (tempfile.TemporaryDirectory(prefix='floatspec-small-ieee-mutation-') as directory,
                      patch.object(bridge, 'expressions', mutated)):
                    rows = bridge.execute([case], flocq, bridge.configured_coqc(flocq), Path(directory))
                failures = bridge.compare([case], rows)
                self.assertEqual(len(failures), 1)
                self.assertEqual(failures[0]['paths'], ['lean', 'compiled'])
                for path in ('lean', 'compiled'):
                    self.assertNotEqual(rows[path][0][start:start+4], rows['rocq'][0][start:start+4])
                    self.assertEqual(rows[path][0][:start], rows['rocq'][0][:start])
                    self.assertEqual(rows[path][0][start+4:], rows['rocq'][0][start+4:])

    def test_generic_comparison_observes_validity_and_degenerate_formats(self):
        flocq = Path(os.environ["FLOCQ_AUDIT_DIR"]).resolve()
        cases = [bridge.Case("comparison", args) for args in
                 ((3, 4, 3, 1, 4, -1, 3, 1, 4, -2),
                  (3, 4, 3, 0, 1, 0, 3, 0, 4, -2),
                  (0, -1, 0, 1, 1, 0, 0, 0, 1, 0),
                  (0, 1, 3, 0, 1, 0, 0, 0, 1, 0),
                  (1, 1, 1, 0, 1, 0, 1, 1, 1, 0))]
        with tempfile.TemporaryDirectory(prefix="floatspec-comparison-") as directory:
            rows = bridge.execute(cases, flocq, bridge.configured_coqc(flocq), Path(directory))
            bridge.bootstrap_lean(cases, rows["rocq"], Path(directory))
        self.assertEqual(bridge.compare(cases, rows), [])
        self.assertEqual([row[10] for row in rows["lean"]], [-1, 2, 0, 2, 1])
        self.assertEqual(rows["lean"][1][:6], [0, 1, 2, 0, 0, 0])
        self.assertEqual([row[-3:] for row in rows["lean"]],
                         [[0, 1, 1], [0, 0, 0], [1, 0, 1], [0, 0, 0], [0, 0, 0]])

    def test_boolean_comparison_special_values_and_finite_boundaries(self):
        flocq = Path(os.environ["FLOCQ_AUDIT_DIR"]).resolve()
        # Each expectation is [equal, strictly less, less-or-equal].
        # Constructor tags are zero=0, infinity=1, NaN=2, finite=3.
        examples = [
            ((0, 0, 1, 0), (0, 1, 1, 0), [1, 0, 1]),
            ((2, 0, 1, 0), (2, 0, 1, 0), [0, 0, 0]),
            ((2, 0, 1, 0), (0, 0, 1, 0), [0, 0, 0]),
            ((0, 0, 1, 0), (2, 0, 1, 0), [0, 0, 0]),
            ((1, 0, 1, 0), (1, 0, 1, 0), [1, 0, 1]),
            ((1, 1, 1, 0), (1, 1, 1, 0), [1, 0, 1]),
            ((1, 1, 1, 0), (1, 0, 1, 0), [0, 1, 1]),
            ((1, 0, 1, 0), (3, 0, 7, 1), [0, 0, 0]),
            ((3, 1, 7, 1), (3, 1, 1, -4), [0, 1, 1]),
            ((3, 0, 3, -4), (3, 0, 4, -4), [0, 1, 1]),
            ((3, 1, 3, -4), (3, 1, 4, -4), [0, 0, 0]),
            ((3, 0, 1, 0), (3, 0, 4, -2), [0, 0, 0]),
        ]
        cases = [bridge.Case("comparison", (3, 4, *x, *y)) for x, y, _ in examples]
        with tempfile.TemporaryDirectory(prefix="floatspec-boolean-comparison-") as directory:
            rows = bridge.execute(cases, flocq, bridge.configured_coqc(flocq), Path(directory))
            bridge.bootstrap_lean(cases, rows["rocq"], Path(directory))
        self.assertEqual(bridge.compare(cases, rows), [])
        self.assertEqual([row[-3:] for row in rows["rocq"]],
                         [expected for _, _, expected in examples])

    def test_boolean_comparison_mutations_are_rejected(self):
        flocq = Path(os.environ["FLOCQ_AUDIT_DIR"]).resolve()
        original = bridge.expressions
        mutations = [
            # Treating NaN as reflexively equal must fail on both Lean paths.
            ("BinarySingleNaN.Beqb x y", "true", (2, 0, 1, 0)),
            # Confusing <= with < must fail even on differently signed zeros.
            ("BinarySingleNaN.Bleb x y", "BinarySingleNaN.Bltb x y", (0, 1, 1, 0)),
        ]
        for old, new, operand in mutations:
            with self.subTest(mutation=old):
                def mutated(case):
                    lean, rocq = original(case)
                    self.assertIn(old, lean)
                    return lean.replace(old, new), rocq
                case = bridge.Case("comparison", (3, 4, *operand, 0, 0, 1, 0))
                with (tempfile.TemporaryDirectory(prefix="floatspec-boolean-mutation-") as directory,
                      patch.object(bridge, "expressions", mutated)):
                    rows = bridge.execute([case], flocq, bridge.configured_coqc(flocq), Path(directory))
                failures = bridge.compare([case], rows)
                self.assertEqual(len(failures), 1)
                self.assertEqual(failures[0]["paths"], ["lean", "compiled"])

    def test_generic_comparison_operand_swap_mutation_is_rejected(self):
        flocq = Path(os.environ["FLOCQ_AUDIT_DIR"]).resolve()
        original = bridge.expressions
        def mutated(case):
            lean, rocq = original(case)
            self.assertIn("BinarySingleNaN.Bcompare x y", lean)
            return lean.replace("BinarySingleNaN.Bcompare x y", "BinarySingleNaN.Bcompare y x"), rocq
        case = bridge.Case("comparison", (3, 4, 3, 0, 4, -2, 3, 0, 4, -1))
        with (tempfile.TemporaryDirectory(prefix="floatspec-comparison-mutation-") as directory,
              patch.object(bridge, "expressions", mutated)):
            rows = bridge.execute([case], flocq, bridge.configured_coqc(flocq), Path(directory))
        failures = bridge.compare([case], rows)
        self.assertEqual(len(failures), 1)
        self.assertEqual(failures[0]["paths"], ["lean", "compiled"])

    def test_generic_neighbors_preserve_boundaries_and_reject_invalid_carriers(self):
        flocq = Path(os.environ["FLOCQ_AUDIT_DIR"]).resolve()
        cases = [bridge.Case("neighbors", args) for args in
                 ((3, 4, 0, 1, 1, 0), (3, 4, 3, 0, 7, 1),
                  (3, 4, 3, 1, 1, -4), (3, 4, 3, 0, 1, 0))]
        with tempfile.TemporaryDirectory(prefix="floatspec-neighbors-") as directory:
            rows = bridge.execute(cases, flocq, bridge.configured_coqc(flocq), Path(directory))
            bridge.bootstrap_lean(cases, rows["rocq"], Path(directory))
        self.assertEqual(bridge.compare(cases, rows), [])
        self.assertEqual(rows["lean"][0], [1, 0, 1, 0, 0, 3, 0, 1, -4,
                                           3, 1, 1, -4, 3, 0, 1, -4])
        self.assertEqual(rows["lean"][1][5:9], [1, 0, 0, 0])
        self.assertEqual(rows["lean"][2][5:9], [0, 1, 0, 0])
        self.assertEqual(rows["lean"][3], [0] + [2, 0, 0, 0] * 4)

    def test_raw_nearby_modes_and_invalid_precision(self):
        flocq = Path(os.environ["FLOCQ_AUDIT_DIR"]).resolve()
        cases = [bridge.Case("nearby", (3, 4, mode, sign, 6, -2))
                 for mode in range(5) for sign in (0, 1)]
        cases.append(bridge.Case("nearby", (-1, 4, 0, 0, 1, 0)))
        with tempfile.TemporaryDirectory(prefix="floatspec-nearby-") as directory:
            folder = Path(directory)
            rows = bridge.execute(cases, flocq, bridge.configured_coqc(flocq), folder)
            self.assertEqual(bridge.compare(cases, rows), [])
            bridge.bootstrap_lean(cases, rows["rocq"], folder)
        self.assertEqual(rows["lean"][0], [2, 3, 0, 4, -1, 1, 1])
        self.assertEqual(rows["lean"][1], [2, 3, 1, 4, -1, 1, 1])
        self.assertEqual(rows["lean"][-1][-2:], [0, 0])

    def test_generic_successor_mutation_is_rejected(self):
        flocq = Path(os.environ["FLOCQ_AUDIT_DIR"]).resolve()
        original = bridge.expressions
        def mutated(case):
            lean, rocq = original(case)
            self.assertIn("BinarySingleNaN.Bsucc x", lean)
            return lean.replace("BinarySingleNaN.Bsucc x", "BinarySingleNaN.Bpred x"), rocq
        case = bridge.Case("neighbors", (3, 4, 0, 0, 1, 0))
        with (tempfile.TemporaryDirectory(prefix="floatspec-neighbor-mutation-") as directory,
              patch.object(bridge, "expressions", mutated)):
            rows = bridge.execute([case], flocq, bridge.configured_coqc(flocq), Path(directory))
        failures = bridge.compare([case], rows)
        self.assertEqual(len(failures), 1)
        self.assertEqual(failures[0]["paths"], ["lean", "compiled"])

    def test_raw_and_proof_carrying_validity_agree_with_source(self):
        flocq = Path(os.environ["FLOCQ_AUDIT_DIR"]).resolve()
        cases = [bridge.Case("validity", (3, 4, 0, 1, 0)),
                 bridge.Case("validity", (3, 4, 0, 4, -2)),
                 bridge.Case("validity", (3, 4, 1, 1, -4)),
                 bridge.Case("validity", (-1, 1, 0, 1, 0))]
        with tempfile.TemporaryDirectory(prefix="floatspec-validity-") as directory:
            observations = bridge.execute(cases, flocq, bridge.configured_coqc(flocq), Path(directory))
            bridge.bootstrap_lean(cases, observations["rocq"], Path(directory))
        self.assertEqual(bridge.compare(cases, observations), [])
        self.assertEqual(observations["lean"][0], [0, 0] + [2, 0, 0, 0] * 3 + [0])
        self.assertEqual(observations["lean"][1], [1, 1] + [3, 0, 4, -2] * 3 + [1])
        self.assertEqual(observations["lean"][2], [1, 1] + [3, 1, 1, -4] * 3 + [1])
        self.assertEqual(observations["lean"][3], [0, 0] + [2, 0, 0, 0] * 3 + [0])

    def test_always_true_validity_mutation_is_rejected(self):
        flocq = Path(os.environ["FLOCQ_AUDIT_DIR"]).resolve()
        original = bridge.expressions
        def mutated(case):
            lean, rocq = original(case)
            old = "boolean (valid_binary_SF (prec := (3)) (emax := (4)) x)"
            self.assertIn(old, lean)
            return lean.replace(old, "boolean true"), rocq
        case = bridge.Case("validity", (3, 4, 0, 1, 0))
        with (tempfile.TemporaryDirectory(prefix="floatspec-vacuous-validity-") as directory,
              patch.object(bridge, "expressions", mutated)):
            rows = bridge.execute([case], flocq, bridge.configured_coqc(flocq), Path(directory))
        failures = bridge.compare([case], rows)
        self.assertEqual(len(failures), 1)
        self.assertEqual(failures[0]["paths"], ["lean", "compiled"])
        self.assertEqual(rows["lean"][0][-1], 1)
        self.assertEqual(rows["rocq"][0][-1], 0)

    def test_range_only_conversion_mutation_is_rejected(self):
        original = bridge.expressions
        def mutated(case):
            lean, rocq = original(case)
            if case.op == "validity":
                # Restore the old bug: raw conversion accepts any in-range
                # finite representation without checking canonicality.
                lean = lean.replace("_root_.SF2B' (prec := (3)) (emax := (4)) x", "SF2B x")
            return lean, rocq
        with tempfile.TemporaryDirectory(prefix="floatspec-validity-mutation-") as directory:
            output, replay = Path(directory) / "output", Path(directory) / "cases.json"
            case = {"op": "validity", "args": [3, 4, 0, 1, 0]}
            replay.write_text(json.dumps([case]))
            argv = ["flocq_bridge", "--flocq-dir", os.environ["FLOCQ_AUDIT_DIR"],
                    "--skip-build", "--replay", str(replay), "--output", str(output)]
            with (patch("sys.argv", argv), patch.object(bridge, "expressions", mutated),
                  contextlib.redirect_stdout(io.StringIO()), self.assertRaises(SystemExit)):
                bridge.main()
            report = json.loads((output / "report.json").read_text())
            self.assertEqual(report["status"], "mismatch")
            self.assertEqual(report["mismatches"][0]["paths"], ["lean", "compiled"])
            self.assertEqual(json.loads((output / "replay.json").read_text()), [case])

    def test_concurrent_source_change_marks_run_error(self):
        with tempfile.TemporaryDirectory(prefix="floatspec-source-change-") as directory:
            output, replay = Path(directory) / "output", Path(directory) / "cases.json"
            replay.write_text('[{"op": "power", "args": [2, 0]}]')
            argv = ["flocq_bridge", "--flocq-dir", os.environ["FLOCQ_AUDIT_DIR"],
                    "--replay", str(replay), "--output", str(output)]
            with (patch("sys.argv", argv), patch.object(bridge, "lean_source_fingerprint",
                  side_effect=["original", "changed"]), contextlib.redirect_stdout(io.StringIO()),
                  self.assertRaisesRegex(RuntimeError, "changed during verification")):
                bridge.main()
            report = json.loads((output / "report.json").read_text())
            self.assertEqual(report["status"], "error")
            self.assertEqual(report["compared_cases"], 0)
            self.assertEqual(report["bootstrapped_lean_cases"], 0)

    def test_timeout_and_interrupt_are_errors_not_passes(self):
        for error in (subprocess.TimeoutExpired("lean", 0.1), KeyboardInterrupt()):
            with (self.subTest(error=type(error).__name__),
                  tempfile.TemporaryDirectory(prefix="floatspec-bridge-error-") as directory):
                output, replay = Path(directory) / "output", Path(directory) / "cases.json"
                replay.write_text('[{"op": "power", "args": [2, 0]}]')
                argv = ["flocq_bridge", "--flocq-dir", os.environ["FLOCQ_AUDIT_DIR"],
                        "--replay", str(replay), "--output", str(output)]
                with (patch("sys.argv", argv), patch.object(bridge, "execute", side_effect=error),
                      contextlib.redirect_stdout(io.StringIO()), self.assertRaises(type(error))):
                    bridge.main()
                report = json.loads((output / "report.json").read_text())
                self.assertEqual(report["status"], "error")
                self.assertEqual(report["compared_cases"], 0)
                self.assertEqual(report["bootstrapped_lean_cases"], 0)

    def test_all_adapters_execute(self):
        flocq = Path(os.environ["FLOCQ_AUDIT_DIR"]).resolve()
        cases = [bridge.Case("power", (2, -1)), bridge.Case("div_eucl", (7, -3)),
                 bridge.Case("location", (4, 2, 0)), bridge.Case("round", (1, 2, -3)),
                 bridge.Case("truncate", (2, -3, 0, 0, 1)),
                 bridge.Case("div", (2, 1, 0, 2, 0, 0)),
                 bridge.Case("plus", (2, 1, 0, 0, 1, 1)),
                 bridge.Case("sqrt", (2, -4, 0, 0)),
                 bridge.Case("formats", (-2, 3, 0)), bridge.Case("digits", (3, -9)),
                 bridge.Case("operations", (2, 1, 0, -2, -1)),
                 *[bridge.Case("format_calc", (3, 9, -1, 2, 1, -2, 3, fmt))
                   for fmt in range(4)], bridge.Case("overflow", (3, 4, 1, 0)),
                 bridge.Case("bits64", (0xfff0000000000001,)), bridge.Case("bits32", (-1,))]
        with tempfile.TemporaryDirectory(prefix="floatspec-bridge-test-") as directory:
            observations = bridge.execute(cases, flocq, bridge.configured_coqc(flocq), Path(directory))
        self.assertEqual(bridge.compare(cases, observations), [])
        lean = observations["lean"]
        self.assertEqual(lean[0], [0])
        self.assertEqual(lean[1], [-3, -2])
        self.assertEqual(lean[7], [0, 0])
        self.assertEqual(lean[-3], [3, 0, 7, 1, 1] + [3, 0, 7, 1] * 4)
        self.assertEqual(lean[-2], [2, 1, 1, 0, 0xfff0000000000001, 1, 1, 2047, 1])
        self.assertEqual(lean[-1], [2, 0, (1 << 23) - 1, 0, (1 << 31) - 1,
                                   0, (1 << 23) - 1, 255, 1])

    def test_negative_bit_widths_execute_without_natural_clamping(self):
        flocq = Path(os.environ["FLOCQ_AUDIT_DIR"]).resolve()
        cases = [bridge.Case("bit_fields", (-1, 2, 0, 0, -3, -3)),
                 bridge.Case("bit_fields", (2, -1, 1, 1, 0, -1))]
        with tempfile.TemporaryDirectory(prefix="floatspec-bit-fields-") as directory:
            observations = bridge.execute(cases, flocq, bridge.configured_coqc(flocq), Path(directory))
            bridge.bootstrap_lean(cases, observations["rocq"], Path(directory))
        self.assertEqual(bridge.compare(cases, observations), [])
        self.assertEqual(observations["lean"][0], [-2, 0, -3, 0, 0, -2, 0, -3])

    def test_fixed_width_order_and_exact_unary_operations(self):
        flocq = Path(os.environ["FLOCQ_AUDIT_DIR"]).resolve()
        cases = [bridge.Case("order32", (0x80000000, 0)),
                 bridge.Case("order32", (0xff800001, 0)),
                 bridge.Case("order64", (0x3ff0000000000000, 0x4000000000000000))]
        with tempfile.TemporaryDirectory(prefix="floatspec-bit-order-") as directory:
            observations = bridge.execute(cases, flocq, bridge.configured_coqc(flocq), Path(directory))
            bridge.bootstrap_lean(cases, observations["rocq"], Path(directory))
        self.assertEqual(bridge.compare(cases, observations), [])
        self.assertEqual(observations["lean"][0], [0x80000000, 0, 0, 0, 0, 0,
                                                 0x80000000, 0x80000001, 1, 0x80000001, 1, 1, 0, 0])
        self.assertEqual(observations["lean"][1], [0xff800001, 0, 2, 2] + [0xff800001] * 8 + [2, 2])
        self.assertEqual(observations["lean"][2], [0x3ff0000000000000, 0x4000000000000000,
                          -1, 1, 0xbff0000000000000, 0x3ff0000000000000,
                          0x3ff0000000000000, 0x3fefffffffffffff, 0x3ff0000000000001,
                          0x3fefffffffffffff, 0x3ff0000000000001, 0x3cb0000000000000, -1, -1])

    def test_nan_order_cannot_be_mutated_into_equality(self):
        original = bridge.expressions

        def mutated(case):
            lean, rocq = original(case)
            return lean.replace(".getD 2", ".getD 0"), rocq

        with tempfile.TemporaryDirectory(prefix="floatspec-order-mutation-") as directory:
            output, replay = Path(directory) / "output", Path(directory) / "cases.json"
            case = {"op": "order32", "args": [0xff800001, 0]}
            replay.write_text(json.dumps([case]))
            argv = ["flocq_bridge", "--flocq-dir", os.environ["FLOCQ_AUDIT_DIR"],
                    "--replay", str(replay), "--output", str(output)]
            with (patch("sys.argv", argv), patch.object(bridge, "expressions", mutated),
                  contextlib.redirect_stdout(io.StringIO()), self.assertRaises(SystemExit)):
                bridge.main()
            report = json.loads((output / "report.json").read_text())
            self.assertEqual(report["status"], "mismatch")
            self.assertEqual(report["mismatches"][0]["paths"], ["lean", "compiled"])
            self.assertEqual(report["bootstrapped_lean_cases"], 0)
            self.assertEqual(json.loads((output / "replay.json").read_text()), [case])

    def test_compiled_only_mutation_is_not_hidden_by_kernel_agreement(self):
        original = bridge.compiled_source

        def wrong_compiled(rows, instances):
            return original(rows, instances).replace("Zaux.Zpower (2) (1)", "Zaux.Zpower (3) (1)")

        with tempfile.TemporaryDirectory(prefix="floatspec-compiled-mutation-") as directory:
            output, replay = Path(directory) / "output", Path(directory) / "cases.json"
            replay.write_text('[{"op": "power", "args": [2, 1]}]')
            argv = ["flocq_bridge", "--flocq-dir", os.environ["FLOCQ_AUDIT_DIR"],
                    "--replay", str(replay), "--output", str(output)]
            with (patch("sys.argv", argv), patch.object(bridge, "compiled_source", wrong_compiled),
                  contextlib.redirect_stdout(io.StringIO()), self.assertRaises(SystemExit)):
                bridge.main()
            report = json.loads((output / "report.json").read_text())
            self.assertEqual(report["status"], "mismatch")
            self.assertEqual(report["mismatches"][0]["paths"], ["compiled"])
            self.assertEqual(report["bootstrapped_lean_cases"], 1)
            self.assertEqual(json.loads((output / "replay.json").read_text()),
                             [{"op": "power", "args": [2, 1]}])

    def test_one_mismatch_keeps_kernel_coverage_for_the_rest_of_its_batch(self):
        # Live control: plant the natAbs bug in the Lean input of one case only.
        # That case fails the run as a mismatch, and the real kernel still
        # checks the other three cases of its batch against Rocq.
        original = bridge.expressions
        planted = bridge.Case("power", (2, -1))

        def mutated(case):
            lean, rocq = original(case)
            return ("[Zaux.Zpower 2 (Int.natAbs (-1))]" if case == planted else lean), rocq

        cases = [{"op": "power", "args": [2, 3]}, {"op": "power", "args": [2, -1]},
                 {"op": "div_eucl", "args": [7, -3]}, {"op": "power", "args": [3, 2]}]
        with tempfile.TemporaryDirectory(prefix="floatspec-bridge-kernel-coverage-") as directory:
            output, replay = Path(directory) / "output", Path(directory) / "cases.json"
            replay.write_text(json.dumps(cases))
            argv = ["flocq_bridge", "--flocq-dir", os.environ["FLOCQ_AUDIT_DIR"], "--skip-build",
                    "--replay", str(replay), "--output", str(output)]
            with (patch("sys.argv", argv), patch.object(bridge, "expressions", mutated),
                  contextlib.redirect_stdout(io.StringIO()),
                  self.assertRaisesRegex(SystemExit, "1 mismatches")):
                bridge.main()
            report = json.loads((output / "report.json").read_text())
            regressions = (output / "batch_000000" / "OracleRegressions.lean").read_text()
            kernel_output = (output / "batch_000000" / "oracle_regressions.out").read_text()
        self.assertEqual(report["status"], "mismatch")
        self.assertEqual([(m["index"], m["paths"]) for m in report["mismatches"]],
                         [(1, ["lean", "compiled"])])
        self.assertEqual(report["batches"], [{"offset": 0, "cases": 4, "mismatched_cases": 1,
                                              "kernel_checked_cases": 3, "not_kernel_checked": [1]}])
        self.assertEqual(report["bootstrapped_lean_cases"], 3)
        self.assertEqual(regressions.count(":= by decide +kernel"), 3)
        for case in (cases[0], cases[2], cases[3]):
            self.assertIn(original(bridge.Case(case["op"], tuple(case["args"])))[0], regressions)
        self.assertNotIn("Int.natAbs", regressions)
        self.assertEqual(kernel_output.strip(), "")

    def test_real_mutation_exits_with_replay(self):
        # Reproduce the historical negative-exponent/natAbs bug only in the
        # generated Lean test input. Both real provers still execute.
        original = bridge.expressions

        def mutated(case):
            lean, rocq = original(case)
            if case == bridge.Case("power", (2, -1)):
                lean = "[Zaux.Zpower 2 (Int.natAbs (-1))]"
            return lean, rocq

        with tempfile.TemporaryDirectory(prefix="floatspec-bridge-mutation-") as directory:
            output = Path(directory) / "output"
            replay = Path(directory) / "cases.json"
            replay.write_text(json.dumps([{"op": "power", "args": [2, -1]}]))
            argv = ["flocq_bridge", "--flocq-dir", os.environ["FLOCQ_AUDIT_DIR"],
                    "--replay", str(replay), "--output", str(output)]
            with (patch("sys.argv", argv), patch.object(bridge, "expressions", mutated),
                  contextlib.redirect_stdout(io.StringIO()),
                  self.assertRaises(SystemExit) as exit_result):
                bridge.main()
            self.assertIn("1 mismatches", str(exit_result.exception))
            report = json.loads((output / "report.json").read_text())
            self.assertEqual(report["status"], "mismatch")
            self.assertEqual(report["mismatches"][0]["lean"], [2])
            self.assertEqual(report["mismatches"][0]["rocq"], [0])
            self.assertEqual(json.loads((output / "replay.json").read_text()),
                             [{"op": "power", "args": [2, -1]}])


if __name__ == "__main__":
    unittest.main()
