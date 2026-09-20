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


class ParserTests(unittest.TestCase):
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
                         ("sqrt", (1, 4, 0, 0)), ("overflow", (0, 4, 0, 0)),
                         ("overflow", (4, 4, 0, 0)), ("overflow", (3, 4, 5, 0)),
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
        self.assertEqual([row[-1] for row in rows["lean"]], [-1, 2, 0, 2, 1])
        self.assertEqual(rows["lean"][1][:6], [0, 1, 2, 0, 0, 0])

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
        self.assertEqual(lean[-3], [3, 0, 7, 1, 1])
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
