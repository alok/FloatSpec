"""Validate the all-rounding-mode corpus and deliberately break its real adapter."""

import contextlib
import io
import json
import os
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest.mock import patch

import ieee_modes_bridge as bridge


class CorpusTests(unittest.TestCase):
    def test_all_paths_and_columns_are_required(self):
        case = (32, 0, 1, 2, 3)
        for path in ("lean", "compiled"):
            for offset, column in enumerate(bridge.COLUMNS):
                results = {name: [[0] * len(bridge.COLUMNS)] for name in ("lean", "compiled", "rocq")}
                results[path][0][offset] = 1
                mismatch = bridge.compare([case], results)[0]
                self.assertEqual(mismatch["paths"], [path])
                self.assertEqual(mismatch["columns"], [column])
        with self.assertRaises(ValueError):
            bridge.compare([case], {"lean": [[0] * len(bridge.COLUMNS)], "rocq": [[0] * len(bridge.COLUMNS)]})
        with self.assertRaises(ValueError):
            bridge.compare([case], {name: [[0] * (len(bridge.COLUMNS) - 1)] for name in ("lean", "compiled", "rocq")})

    def test_modes_formats_replay_and_nan_priority(self):
        cases = bridge.corpus(17, 2)
        self.assertEqual(cases, bridge.corpus(17, 2))
        self.assertNotEqual(cases, bridge.corpus(18, 2))
        self.assertEqual({case[:2] for case in cases}, {(w, m) for w in (32, 64) for m in range(5)})
        self.assertEqual(len(cases), len(set(cases)))
        self.assertIn((32, 3, 0x3f800000, 0x33800000, 0), cases)
        for case in cases:
            self.assertEqual(bridge.validate_case(case), case)
        for case in ([32, 5, 0, 0, 0], [16, 0, 0, 0, 0], [32, 0, 1 << 32, 0, 0],
                     [64, 0, -1, 0, 0], [32, 0, True, 0, 0], [], "case"):
            with self.assertRaises(ValueError):
                bridge.validate_case(case)

    def test_parameter_order_mode_mapping_and_no_nan_canonicalization(self):
        for width in (32, 64):
            for mode in range(5):
                case = (width, mode, 1, 2, 3)
                lean, rocq = bridge.expression(case, "lean"), bridge.expression(case, "rocq")
                self.assertIn(f"b{width}_fma {bridge.LEAN_MODES[mode]} x y z", lean)
                self.assertIn(f"b{width}_fma {bridge.COQ_MODES[mode]} x y z", rocq)
                self.assertIn(f"BinarySingleNaN.Bfma {bridge.LEAN_MODES[mode]} single_x single_y single_z", lean)
                self.assertIn(f"Source.Bfma .{bridge.COQ_MODES[mode]} single_x single_y single_z", lean)
                self.assertNotIn("canonical", lean + rocq)
        self.assertEqual(len(bridge.COLUMNS), 57)
        self.assertEqual(len(set(bridge.COLUMNS)), 57)
        with self.assertRaises(ValueError):
            bridge.expression((32, 0, 0, 0, 0), "other")


@unittest.skipUnless(os.environ.get("FLOCQ_AUDIT_DIR"), "live test requires FLOCQ_AUDIT_DIR")
class LiveTests(unittest.TestCase):
    def test_shared_wrong_mode_is_rejected_before_bootstrap(self):
        original = bridge.expression

        def wrong_mode(case, language):
            # Mutate the actual Lean and Rocq programs, including both SingleNaN routes.
            return original(case, language).replace(".RTP", ".RNE").replace("mode_UP", "mode_NE")

        with tempfile.TemporaryDirectory(prefix="floatspec-shared-mode-mutation-") as directory:
            output, replay = Path(directory) / "output", Path(directory) / "cases.json"
            case = [32, 3, 0x3f800000, 0x33800000, 0]
            replay.write_text(json.dumps([case]))
            argv = ["ieee_modes_bridge", "--flocq-dir", os.environ["FLOCQ_AUDIT_DIR"],
                    "--skip-build", "--replay", str(replay), "--output", str(output)]
            with (patch("sys.argv", argv), patch.object(bridge, "expression", wrong_mode),
                  patch.object(bridge, "bootstrap") as bootstrap,
                  contextlib.redirect_stdout(io.StringIO()), self.assertRaises(SystemExit)):
                bridge.main()
            report = json.loads((output / "report.json").read_text())
            self.assertEqual(report["status"], "mismatch")
            self.assertEqual(report["mismatches"], [])  # Every implementation agrees.
            self.assertEqual(len(report["oracle_mismatches"]), 3)
            self.assertGreater(report["oracle_assertions"], 0)
            self.assertEqual(report["bootstrapped_lean_cases"], 0)
            bootstrap.assert_not_called()
            for failure in report["oracle_mismatches"]:
                self.assertIn("add", failure["columns"])
                self.assertIn("single_add_mantissa", failure["columns"])
                self.assertIn("source_single_add_mantissa", failure["columns"])
            self.assertEqual(json.loads((output / "replay.json").read_text()), [case])

    def test_each_format_and_rounding_mode_executes_all_operations(self):
        flocq = Path(os.environ["FLOCQ_AUDIT_DIR"]).resolve()
        cases = [(width, mode, one, half_ulp, negative_one)
                 for width, one, half_ulp, negative_one in
                 ((32, 0x3f800000, 0x33800000, 0xbf800000),
                  (64, 0x3ff0000000000000, 0x3ca0000000000000, 0xbff0000000000000))
                 for mode in range(5)]
        with tempfile.TemporaryDirectory(prefix="floatspec-all-compiled-modes-") as directory:
            folder = Path(directory)
            results = bridge.execute(cases, flocq, bridge.configured_coqc(flocq), folder)
            self.assertEqual(bridge.compare(cases, results), [])
            bridge.bootstrap(cases, results["rocq"], folder)

    def test_actual_directed_rounding_and_kernel_regressions(self):
        flocq = Path(os.environ["FLOCQ_AUDIT_DIR"]).resolve()
        cases = [(32, 3, 0x3f800000, 0x33800000, 0), (32, 0, 0x3f800000, 0x33800000, 0),
                 (64, 0, 0x7ff0000000000001, 0xfff8000000000000, 0x7ff0000000000025)]
        with tempfile.TemporaryDirectory(prefix="floatspec-ieee-mode-test-") as directory:
            folder = Path(directory)
            results = bridge.execute(cases, flocq, bridge.configured_coqc(flocq), folder)
            self.assertEqual(results["lean"], results["rocq"])
            self.assertEqual(bridge.compare(cases, results), [])
            self.assertEqual(results["lean"][0][3], 0x3f800001)
            self.assertEqual(results["lean"][1][3], 0x3f800000)
            self.assertEqual(results["lean"][2][8], 0x7ff0000000000001)
            for start in (9, 33):
                self.assertEqual(results["lean"][0][start:start + 4], [3, 0, 8388609, -23])
                self.assertEqual(results["lean"][1][start:start + 4], [3, 0, 8388608, -23])
                for op in range(6):
                    offset = start + 4 * op
                    self.assertEqual(results["lean"][2][offset:offset + 4], [2, 0, 0, 0])
            bridge.bootstrap(cases, results["rocq"], folder)

    def test_single_nan_public_paths_are_independently_observed(self):
        flocq = Path(os.environ["FLOCQ_AUDIT_DIR"]).resolve()
        original = bridge.expression
        case = (32, 0, 0x3f800000, 0x3e800000, 0)
        for namespace, start in (("BinarySingleNaN", 9),
                                 ("FloatSpec.IEEE754.BinarySingleNaN.Source", 33)):
            def mutation(case, language):
                result = original(case, language)
                return (result.replace(f"{namespace}.Bplus ", f"{namespace}.Bminus ")
                        if language == "lean" else result)

            with (self.subTest(namespace=namespace),
                  tempfile.TemporaryDirectory(prefix="floatspec-single-mode-mutation-") as directory,
                  patch.object(bridge, "expression", mutation)):
                results = bridge.execute([case], flocq, bridge.configured_coqc(flocq), Path(directory))
                self.assertEqual(results["rocq"][0][start:start + 4], [3, 0, 10485760, -23])
                mismatch = bridge.compare([case], results)[0]
                self.assertEqual(mismatch["paths"], ["lean", "compiled"])
                self.assertTrue(mismatch["columns"])
                self.assertLessEqual(set(mismatch["columns"]), set(bridge.COLUMNS[start:start + 4]))
                for path in ("lean", "compiled"):
                    self.assertEqual(results[path][0][:start], results["rocq"][0][:start])
                    self.assertEqual(results[path][0][start + 4:], results["rocq"][0][start + 4:])

    def test_wrong_rounding_mode_fails_with_replay(self):
        original = bridge.expression

        def mutation(case, language):
            result = original(case, language)
            return result.replace(".RTP", ".RNE") if language == "lean" else result

        with tempfile.TemporaryDirectory(prefix="floatspec-ieee-mode-mutation-") as directory:
            output, replay = Path(directory) / "output", Path(directory) / "cases.json"
            case = [32, 3, 0x3f800000, 0x33800000, 0]
            replay.write_text(json.dumps([case]))
            argv = ["ieee_modes_bridge", "--flocq-dir", os.environ["FLOCQ_AUDIT_DIR"],
                    "--skip-build", "--replay", str(replay), "--output", str(output)]
            with (patch("sys.argv", argv), patch.object(bridge, "expression", mutation),
                  contextlib.redirect_stdout(io.StringIO()), self.assertRaises(SystemExit)):
                bridge.main()
            report = json.loads((output / "report.json").read_text())
            self.assertEqual(report["status"], "mismatch")
            self.assertIn("add", report["mismatches"][0]["columns"])
            self.assertEqual(report["bootstrapped_lean_cases"], 0)
            self.assertEqual(json.loads((output / "replay.json").read_text()), [case])

    def test_compiled_mode_mutation_and_explicit_compiler(self):
        original = bridge.compiled_source
        with tempfile.TemporaryDirectory(prefix="floatspec-compiled-mode-mutation-") as directory:
            output, replay = Path(directory) / "output", Path(directory) / "cases.json"
            case = [32, 3, 0x3f800000, 0x33800000, 0]
            replay.write_text(json.dumps([case]))
            coqc = bridge.configured_coqc(Path(os.environ["FLOCQ_AUDIT_DIR"]))
            argv = ["ieee_modes_bridge", "--flocq-dir", os.environ["FLOCQ_AUDIT_DIR"],
                    "--coqc", coqc, "--skip-build", "--replay", str(replay), "--output", str(output)]
            with (patch("sys.argv", argv), patch.object(bridge, "compiled_source",
                  side_effect=lambda cases: original(cases).replace(".RTP", ".RNE")),
                  contextlib.redirect_stdout(io.StringIO()), self.assertRaises(SystemExit)):
                bridge.main()
            report = json.loads((output / "report.json").read_text())
            self.assertEqual(report["status"], "mismatch")
            self.assertEqual(report["mismatches"][0]["paths"], ["compiled"])
            self.assertIn("add", report["mismatches"][0]["columns"])
            self.assertEqual(report["bootstrapped_lean_cases"], 1)
            self.assertEqual(json.loads((output / "replay.json").read_text()), [case])

    def test_errors_never_become_passes(self):
        for error in (subprocess.TimeoutExpired("lean", 0.1), KeyboardInterrupt()):
            with tempfile.TemporaryDirectory(prefix="floatspec-ieee-mode-error-") as directory:
                output, replay = Path(directory) / "output", Path(directory) / "cases.json"
                replay.write_text("[[32, 0, 0, 0, 0]]")
                argv = ["ieee_modes_bridge", "--flocq-dir", os.environ["FLOCQ_AUDIT_DIR"],
                        "--skip-build", "--replay", str(replay), "--output", str(output)]
                with (patch("sys.argv", argv), patch.object(bridge, "execute", side_effect=error),
                      contextlib.redirect_stdout(io.StringIO()), self.assertRaises(type(error))):
                    bridge.main()
                report = json.loads((output / "report.json").read_text())
                self.assertEqual(report["status"], "error")
                self.assertEqual(report["compared_cases"], 0)
                self.assertEqual(report["bootstrapped_lean_cases"], 0)


if __name__ == "__main__":
    unittest.main()
