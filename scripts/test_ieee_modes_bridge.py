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
                self.assertNotIn("canonical", lean + rocq)


@unittest.skipUnless(os.environ.get("FLOCQ_AUDIT_DIR"), "live test requires FLOCQ_AUDIT_DIR")
class LiveTests(unittest.TestCase):
    def test_actual_directed_rounding_and_kernel_regressions(self):
        flocq = Path(os.environ["FLOCQ_AUDIT_DIR"]).resolve()
        cases = [(32, 3, 0x3f800000, 0x33800000, 0), (32, 0, 0x3f800000, 0x33800000, 0),
                 (64, 0, 0x7ff0000000000001, 0xfff8000000000000, 0x7ff0000000000025)]
        with tempfile.TemporaryDirectory(prefix="floatspec-ieee-mode-test-") as directory:
            folder = Path(directory)
            results = bridge.execute(cases, flocq, bridge.configured_coqc(flocq), folder)
            self.assertEqual(results["lean"], results["rocq"])
            self.assertEqual(results["lean"][0][3], 0x3f800001)
            self.assertEqual(results["lean"][1][3], 0x3f800000)
            self.assertEqual(results["lean"][2][8], 0x7ff0000000000001)
            bridge.bootstrap(cases, results["rocq"], folder)

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
