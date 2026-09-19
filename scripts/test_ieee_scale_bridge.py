"""Exercise scale/decompose adapters, native contract scopes, and mutation failures."""

import contextlib
import io
import json
import os
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest.mock import patch

import ieee_scale_bridge as bridge


class CorpusTests(unittest.TestCase):
    def test_seed_modes_boundaries_and_input_validation(self):
        cases = bridge.corpus(17, 2)
        self.assertEqual(cases, bridge.corpus(17, 2))
        self.assertNotEqual(cases, bridge.corpus(18, 2))
        self.assertEqual({case[:2] for case in cases}, {(w, m) for w in (32, 64) for m in range(5)})
        self.assertIn((64, 0, 1, 2048), cases)
        self.assertIn((32, 3, 0x80000001, -150), cases)
        self.assertEqual(len(cases), len(set(cases)))
        for case in cases:
            self.assertEqual(bridge.validate_case(case), case)
        for case in ([], [32, 5, 0, 0], [16, 0, 0, 0], [64, 0, -1, 0],
                     [32, 0, 1 << 32, 0], [32, 0, 0, True]):
            with self.assertRaises(ValueError):
                bridge.validate_case(case)

    def test_all_source_paths_and_columns_are_required(self):
        case = (64, 0, 0x3ff0000000000000, 1)
        for path in ("lean", "compiled", "native"):
            for column in range(5):
                rows = {p: [[0] * 5] for p in ("lean", "compiled", "rocq", "native")}
                rows[path][0][column] = 1
                mismatches, _ = bridge.compare([case], rows)
                self.assertEqual(mismatches[0]["path"], path)
                self.assertEqual(mismatches[0]["columns"], [bridge.COLUMNS[column]])
        with self.assertRaises(ValueError):
            bridge.compare([case], {p: [[0] * 5] for p in ("lean", "rocq", "native")})
        with self.assertRaises(ValueError):
            bridge.compare([case], {p: [[0] * 4] for p in ("lean", "compiled", "rocq", "native")})
        for invalid in (-1, 1 << 64, True):
            rows = {p: [[0] * 5] for p in ("lean", "compiled", "rocq", "native")}
            rows["native"][0][0] = invalid
            with self.assertRaises(ValueError):
                bridge.compare([case], rows)

    def test_native_scope_is_explicit_and_does_not_mask_source_mismatch(self):
        case = (64, 3, 0, -1)
        rows = {p: [[0, 0, 0, -2101, 0]] for p in ("lean", "compiled", "rocq", "native")}
        rows["native"] = [[0, 1, 99, 0, 0]]
        mismatches, exceptions = bridge.compare([case], rows)
        self.assertEqual(mismatches, [])
        self.assertEqual(exceptions[0]["native_checked_columns"], ["input", "reconstructed"])
        rows["lean"][0][3] = 0
        self.assertEqual(bridge.compare([case], rows)[0][0]["path"], "lean")
        rows["lean"][0][3] = -2101
        rows["native"][0][4] = 1
        self.assertEqual(bridge.compare([case], rows)[0][0]["columns"], ["reconstructed"])

    def test_nan_quotient_applies_only_to_native(self):
        case = (32, 0, 0xff800001, 0)
        rows = {p: [[0xff800001] * 3 + [-280, 0xff800001]]
                for p in ("lean", "compiled", "rocq", "native")}
        rows["native"] = [[0x7fc00000] * 3 + [0, 0x7fc00000]]
        self.assertEqual(bridge.compare([case], rows)[0], [])
        rows["compiled"][0][1] = 0x7fc00000
        self.assertEqual(bridge.compare([case], rows)[0][0]["path"], "compiled")


@unittest.skipUnless(os.environ.get("FLOCQ_AUDIT_DIR"), "live tests require FLOCQ_AUDIT_DIR")
class LiveTests(unittest.TestCase):
    def test_every_format_and_mode_and_exceptional_class(self):
        flocq = Path(os.environ["FLOCQ_AUDIT_DIR"]).resolve()
        cases = [(width, mode, word, shift)
                 for width, sign, inf, shift in ((32, 1 << 31, 0x7f800000, -150),
                                                 (64, 1 << 63, 0x7ff0000000000000, -1075))
                 for mode in range(5) for word in (0, sign, 1, inf, sign | inf | 1)]
        with tempfile.TemporaryDirectory(prefix="floatspec-scale-test-") as directory:
            folder = Path(directory)
            rows = bridge.execute(cases, flocq, bridge.configured_coqc(flocq), folder)
            self.assertEqual(bridge.compare(cases, rows)[0], [])
            bridge.bootstrap(cases, rows["rocq"], folder)

    def test_wrong_scale_sign_and_native_shift_fail_with_replay(self):
        original, original_program = bridge.expression, bridge.program
        for path in ("lean", "compiled", "native"):
            def mutated(case, language):
                if language == path:
                    width, mode, word, shift = case
                    return original((width, mode, word, -shift), language)
                return original(case, language)
            def mutated_program(cases, execution_path):
                if path == "compiled" and execution_path == "compiled":
                    cases = [(width, mode, word, -shift) for width, mode, word, shift in cases]
                return original_program(cases, execution_path)
            with self.subTest(path=path), tempfile.TemporaryDirectory(prefix="floatspec-scale-mutation-") as directory:
                output, replay = Path(directory) / "output", Path(directory) / "cases.json"
                case = [64, 0, 0x3ff0000000000000, 1]
                replay.write_text(json.dumps([case]))
                argv = ["ieee_scale_bridge", "--flocq-dir", os.environ["FLOCQ_AUDIT_DIR"],
                        "--skip-build", "--replay", str(replay), "--output", str(output)]
                with (patch("sys.argv", argv), patch.object(bridge, "expression", mutated),
                      patch.object(bridge, "program", mutated_program),
                      contextlib.redirect_stdout(io.StringIO()), self.assertRaises(SystemExit)):
                    bridge.main()
                report = json.loads((output / "report.json").read_text())
                self.assertEqual(report["status"], "mismatch")
                self.assertEqual(report["bootstrapped_lean_cases"], int(path != "lean"))
                self.assertEqual({item["path"] for item in report["mismatches"]},
                                 {"lean", "compiled"} if path == "lean" else {path})
                self.assertEqual(json.loads((output / "replay.json").read_text()), [case])

    def test_timeout_interrupt_and_source_drift_are_errors(self):
        for error in (subprocess.TimeoutExpired("lean", 0.1), KeyboardInterrupt()):
            with self.subTest(error=type(error).__name__), tempfile.TemporaryDirectory() as directory:
                output, replay = Path(directory) / "output", Path(directory) / "cases.json"
                replay.write_text('[[32,0,0,0]]')
                argv = ["ieee_scale_bridge", "--flocq-dir", os.environ["FLOCQ_AUDIT_DIR"],
                        "--skip-build", "--replay", str(replay), "--output", str(output)]
                with (patch("sys.argv", argv), patch.object(bridge, "execute", side_effect=error),
                      contextlib.redirect_stdout(io.StringIO()), self.assertRaises(type(error))):
                    bridge.main()
                self.assertEqual(json.loads((output / "report.json").read_text())["status"], "error")
        with tempfile.TemporaryDirectory() as directory:
            output, replay = Path(directory) / "output", Path(directory) / "cases.json"
            replay.write_text('[[32,0,0,0]]')
            argv = ["ieee_scale_bridge", "--flocq-dir", os.environ["FLOCQ_AUDIT_DIR"],
                    "--skip-build", "--replay", str(replay), "--output", str(output)]
            with (patch("sys.argv", argv), patch.object(bridge, "require_lean_source_snapshot",
                  side_effect=RuntimeError("source changed")), contextlib.redirect_stdout(io.StringIO()),
                  self.assertRaisesRegex(RuntimeError, "source changed")):
                bridge.main()
            report = json.loads((output / "report.json").read_text())
            self.assertEqual(report["status"], "error")
            self.assertEqual(report["compared_cases"], 0)


if __name__ == "__main__":
    unittest.main()
