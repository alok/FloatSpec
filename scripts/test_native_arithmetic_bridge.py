"""Corpus, failure-path, and real mutation tests for the arithmetic bridge."""

import contextlib
import io
import json
import os
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest.mock import patch

import native_arithmetic_bridge as bridge


class CorpusTests(unittest.TestCase):
    def test_seed_boundaries_and_cancellation(self):
        cases = bridge.corpus(17, 10)
        self.assertEqual(cases, bridge.corpus(17, 10))
        self.assertNotEqual(cases, bridge.corpus(18, 10))
        for case in ((0, 1 << 63), (1, 0x3fe0000000000000),
                     (0x7fefffffffffffff, 0x4000000000000000),
                     (0x3ff0000000000000, 0x3ca0000000000000),
                     (0x3ff0000000000000, 0xbff0000000000000),
                     (0, 0x7ff0000000000000)):
            self.assertIn(case, cases)
        self.assertEqual(len(cases), len(set(cases)))

    def test_replay_validation(self):
        for case in ([], [1], [1, 2, 3], [1, -1], [1 << 64, 1], [True, 1], "12"):
            with self.subTest(case=case), self.assertRaises(ValueError):
                bridge.validate_case(case)

    def test_each_output_column_is_compared_on_each_path(self):
        for path in ("native", "model", "compiled_model"):
            for column, name in enumerate(bridge.COLUMNS):
                observations = {key: [[0] * 7] for key in ("native", "model", "compiled_model", "rocq")}
                observations[path][0][column] = 1
                mismatches = bridge.compare([(0, 0)], observations)
                self.assertEqual(len(mismatches), 1)
                self.assertEqual(mismatches[0]["path"], f"{path.replace('_', '-')}-versus-rocq")
                self.assertEqual(mismatches[0]["columns"], [name])

    def test_missing_compiled_path_is_rejected(self):
        with self.assertRaisesRegex(ValueError, "four execution paths"):
            bridge.compare([(0, 0)], {name: [[0] * 7] for name in ("native", "model", "rocq")})

    def test_missing_paths_and_columns_rejected(self):
        for observations in ({"native": [[0] * 7], "rocq": [[0] * 7]},
                             {name: [[0] * 6] for name in ("native", "model", "compiled_model", "rocq")},
                             {name: [] for name in ("native", "model", "compiled_model", "rocq")}):
            with self.assertRaises(ValueError):
                bridge.compare([(0, 0)], observations)


@unittest.skipUnless(os.environ.get("FLOCQ_AUDIT_DIR"), "live test requires FLOCQ_AUDIT_DIR")
class LiveTests(unittest.TestCase):
    def test_shared_operand_routing_bug_is_rejected_by_exact_oracle(self):
        original = bridge.execute

        def wrong_inputs(cases, flocq, coqc, folder):
            # All four real programs receive the same wrongly reordered input.
            return original([(right, left) for left, right in cases], flocq, coqc, folder)

        with tempfile.TemporaryDirectory(prefix="floatspec-shared-input-mutation-") as directory:
            output, replay = Path(directory) / "output", Path(directory) / "cases.json"
            case = [0x3ff0000000000000, 0x4000000000000000]
            replay.write_text(json.dumps([case]))
            argv = ["native_arithmetic_bridge", "--flocq-dir", os.environ["FLOCQ_AUDIT_DIR"],
                    "--replay", str(replay), "--output", str(output)]
            with (patch("sys.argv", argv), patch.object(bridge, "execute", wrong_inputs),
                  patch.object(bridge, "bootstrap_lean") as bootstrap,
                  contextlib.redirect_stdout(io.StringIO()), self.assertRaises(SystemExit)):
                bridge.main()
            report = json.loads((output / "report.json").read_text())
            self.assertEqual(report["status"], "mismatch")
            self.assertEqual(report["mismatches"], [])  # Pairwise agreement is not enough.
            self.assertEqual(len(report["oracle_mismatches"]), 4)
            self.assertGreater(report["oracle_assertions"], 0)
            self.assertEqual(report["bootstrapped_lean_cases"], 0)
            bootstrap.assert_not_called()
            for failure in report["oracle_mismatches"]:
                self.assertIn("left", failure["columns"])
                self.assertIn("sub", failure["columns"])
                self.assertIn("div", failure["columns"])
            self.assertEqual(json.loads((output / "replay.json").read_text()), [case])

    def test_arithmetic_paths_and_kernel_bootstrap(self):
        flocq = Path(os.environ["FLOCQ_AUDIT_DIR"]).resolve()
        cases = [(0x3ff0000000000000, 0x4000000000000000), (0, 1 << 63),
                 (1, 0x3fe0000000000000), (0x7ff0000000000000, 0)]
        with tempfile.TemporaryDirectory(prefix="floatspec-arithmetic-test-") as directory:
            folder = Path(directory)
            results = bridge.execute(cases, flocq, bridge.configured_coqc(flocq), folder)
            self.assertEqual(bridge.compare(cases, results), [])
            bridge.bootstrap_lean(cases, results["rocq"], folder)
        self.assertEqual(results["model"][0][2], 0x4008000000000000)
        self.assertEqual(results["model"][2][4], 0)  # half-min-subnormal ties to even

    def test_live_mutation_retains_replay(self):
        original = bridge.native_source

        def wrong_native(cases):
            # Swap operands, so subtraction and division are demonstrably wrong.
            return original(cases).replace("nativeObservation x y", "nativeObservation y x")

        with tempfile.TemporaryDirectory(prefix="floatspec-arithmetic-mutation-") as directory:
            output, replay = Path(directory) / "output", Path(directory) / "cases.json"
            case = [0x3ff0000000000000, 0x4000000000000000]
            replay.write_text(json.dumps([case]))
            argv = ["native_arithmetic_bridge", "--flocq-dir", os.environ["FLOCQ_AUDIT_DIR"],
                    "--replay", str(replay), "--output", str(output)]
            with (patch("sys.argv", argv), patch.object(bridge, "native_source", wrong_native),
                  contextlib.redirect_stdout(io.StringIO()), self.assertRaises(SystemExit)):
                bridge.main()
            report = json.loads((output / "report.json").read_text())
            self.assertEqual(report["status"], "mismatch")
            self.assertIn("sub", report["mismatches"][0]["columns"])
            self.assertIn("div", report["mismatches"][0]["columns"])
            self.assertEqual(report["bootstrapped_lean_cases"], 1)
            self.assertEqual(json.loads((output / "replay.json").read_text()), [case])

    def test_compiled_model_mutation_cannot_hide_behind_kernel_proofs(self):
        original = bridge.compiled_model_source

        def wrong_compiled(cases):
            return original(cases).replace("modelObservation x y", "modelObservation y x")

        with tempfile.TemporaryDirectory(prefix="floatspec-arithmetic-compiled-mutation-") as directory:
            output, replay = Path(directory) / "output", Path(directory) / "cases.json"
            case = [0x3ff0000000000000, 0x4000000000000000]
            replay.write_text(json.dumps([case]))
            argv = ["native_arithmetic_bridge", "--flocq-dir", os.environ["FLOCQ_AUDIT_DIR"],
                    "--replay", str(replay), "--output", str(output)]
            with (patch("sys.argv", argv),
                  patch.object(bridge, "compiled_model_source", wrong_compiled),
                  contextlib.redirect_stdout(io.StringIO()), self.assertRaises(SystemExit)):
                bridge.main()
            report = json.loads((output / "report.json").read_text())
            self.assertEqual(report["status"], "mismatch")
            self.assertEqual([row["path"] for row in report["mismatches"]],
                             ["compiled-model-versus-rocq"])
            self.assertIn("sub", report["mismatches"][0]["columns"])
            self.assertIn("div", report["mismatches"][0]["columns"])
            self.assertEqual(report["compiled_model_cases"], 1)
            self.assertEqual(report["bootstrapped_lean_cases"], 1)
            self.assertEqual(json.loads((output / "replay.json").read_text()), [case])

    def test_timeout_and_interrupt_are_errors_not_passes(self):
        for error in (subprocess.TimeoutExpired("lean", 0.1), KeyboardInterrupt()):
            with (self.subTest(error=type(error).__name__),
                  tempfile.TemporaryDirectory(prefix="floatspec-arithmetic-error-") as directory):
                output, replay = Path(directory) / "output", Path(directory) / "cases.json"
                replay.write_text("[[0, 0]]")
                argv = ["native_arithmetic_bridge", "--flocq-dir", os.environ["FLOCQ_AUDIT_DIR"],
                        "--replay", str(replay), "--output", str(output)]
                with (patch("sys.argv", argv), patch.object(bridge, "execute", side_effect=error),
                      contextlib.redirect_stdout(io.StringIO()), self.assertRaises(type(error))):
                    bridge.main()
                report = json.loads((output / "report.json").read_text())
                self.assertEqual(report["status"], "error")
                self.assertEqual(report["compared_cases"], 0)
                self.assertEqual(report["bootstrapped_lean_cases"], 0)


if __name__ == "__main__":
    unittest.main()
