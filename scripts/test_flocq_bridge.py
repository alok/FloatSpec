"""Harness regressions; set FLOCQ_AUDIT_DIR to include live prover/mutation tests."""

import contextlib
import io
import json
import os
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest.mock import patch

import flocq_bridge as bridge


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

    def test_replay_input_validation(self):
        for op, args in (("no_such_function", ()), ("power", (2,)),
                         ("power", (2, "sorry")), ("power", (2, True)),
                         ("location", (4, 2, -1)), ("round", (2, 0, 1)),
                         ("sqrt", (1, 4, 0, 0)), ("overflow", (0, 4, 0, 0)),
                         ("overflow", (4, 4, 0, 0)), ("overflow", (3, 4, 5, 0)),
                         ("bit_fields", (0, 0, 2, 0, 0, 0))):
            with self.subTest(op=op, args=args), self.assertRaises(ValueError):
                bridge.Case(op, args)


@unittest.skipUnless(os.environ.get("FLOCQ_AUDIT_DIR"), "live test requires FLOCQ_AUDIT_DIR")
class LiveTests(unittest.TestCase):
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
                                                 0x80000000, 0x80000001, 1])
        self.assertEqual(observations["lean"][1], [0xff800001, 0, 2, 2] + [0xff800001] * 5)
        self.assertEqual(observations["lean"][2], [0x3ff0000000000000, 0x4000000000000000,
                          -1, 1, 0xbff0000000000000, 0x3ff0000000000000,
                          0x3ff0000000000000, 0x3fefffffffffffff, 0x3ff0000000000001])

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
