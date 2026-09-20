"""Integer-rounding coverage, explicit native scopes, and deliberate failures."""

import contextlib
import io
import json
import os
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest.mock import patch

import ieee_integer_bridge as bridge


class CorpusTests(unittest.TestCase):
    def test_seed_modes_boundaries_and_validation(self):
        cases = bridge.corpus(13, 2)
        self.assertEqual(cases, bridge.corpus(13, 2))
        self.assertNotEqual(cases, bridge.corpus(14, 2))
        self.assertEqual({case[:2] for case in cases}, {(w, m) for w in (32, 64) for m in range(5)})
        self.assertIn((64, 0, 0x3ff8000000000000), cases)
        self.assertIn((32, 4, 0xbf000000), cases)
        self.assertIn((64, 1, 0x43efffffffffffff), cases)
        self.assertIn((64, 1, 0x43f0000000000000), cases)
        self.assertEqual(len(cases), len(set(cases)))
        for case in cases:
            self.assertEqual(bridge.validate_case(case), case)
        for case in ([], [32, 5, 0], [16, 0, 0], [64, 0, -1], [32, 0, 1 << 32], [32, 0, True]):
            with self.assertRaises(ValueError):
                bridge.validate_case(case)

    def test_every_path_column_and_signed_integer_is_checked(self):
        case = (64, 4, 0xbff8000000000000)
        for path in ("lean", "compiled", "native"):
            for column in range(5):
                rows = {p: [[0] * 5] for p in ("lean", "compiled", "rocq", "native")}
                rows[path][0][column] = 1
                mismatch = bridge.compare([case], rows)[0]
                self.assertEqual(mismatch[0]["path"], path)
                self.assertEqual(mismatch[0]["columns"], [bridge.COLUMNS[column]])
        rows = {p: [[0, 0, -(1 << 150), 0, -(1 << 150)]] for p in ("lean", "compiled", "rocq", "native")}
        self.assertEqual(bridge.compare([case], rows)[0], [])
        for invalid in (-1, 1 << 64, True):
            rows = {p: [[0] * 5] for p in ("lean", "compiled", "rocq", "native")}
            rows["native"][0][0] = invalid
            with self.assertRaises(ValueError):
                bridge.compare([case], rows)
        with self.assertRaises(ValueError):
            bridge.compare([case], {p: [[0] * 5] for p in ("lean", "rocq", "native")})
        with self.assertRaises(ValueError):
            bridge.compare([case], {p: [[0] * 4] for p in ("lean", "compiled", "rocq", "native")})

    def test_native_precision_mode_and_conversion_domains_are_explicit(self):
        self.assertEqual(bridge.native_checked_columns([64, 0, 0x3ff0000000000000]), [0, 2, 4])
        self.assertEqual(bridge.native_checked_columns([64, 4, 0x43efffffffffffff]), list(range(5)))
        self.assertEqual(bridge.native_checked_columns([64, 4, 0x43f0000000000000]), [0, 1, 3])
        self.assertEqual(bridge.native_checked_columns([32, 0, 0x5f800000]), [0])
        self.assertEqual(bridge.native_checked_columns([32, 4, 0x7f800000]), [0, 1, 3])
        case = (64, 0, 0x43f0000000000000)
        rows = {p: [[case[2], 0, 1 << 64, 0, 1 << 64]] for p in ("lean", "compiled", "rocq", "native")}
        rows["native"][0][1:] = [1, 42, 1, 42]
        mismatches, exceptions = bridge.compare([case], rows)
        self.assertEqual(mismatches, [])
        self.assertEqual(exceptions[0]["native_checked_columns"], ["input"])
        rows["compiled"][0][2] = 42
        self.assertEqual(bridge.compare([case], rows)[0][0]["columns"], ["trunc"])

    def test_nan_quotient_is_not_used_between_source_paths(self):
        case = (32, 4, 0xff800001)
        rows = {p: [[case[2], case[2], 0, case[2], 0]] for p in ("lean", "compiled", "rocq", "native")}
        rows["native"][0] = [0x7fc00000, 0x7fc00000, 42, 0x7fc00000, 42]
        self.assertEqual(bridge.compare([case], rows)[0], [])
        rows["compiled"][0][1] = 0x7fc00000
        self.assertEqual(bridge.compare([case], rows)[0][0]["path"], "compiled")


@unittest.skipUnless(os.environ.get("FLOCQ_AUDIT_DIR"), "live tests require FLOCQ_AUDIT_DIR")
class LiveTests(unittest.TestCase):
    def test_independent_oracles_reject_wrong_rounding_mode(self):
        root = Path(__file__).resolve().parents[1]
        lean = (root / "scripts/fixtures/IntegerRounding.lean").read_text()
        rocq = (root / "scripts/fixtures/IntegerRounding.v").read_text()
        lean = lean.replace("let y := BinarySingleNaN.Bnearbyint mode x",
                            "let y := BinarySingleNaN.Bnearbyint .RNA x")
        grid = "example : cases.all (fun (mode, n) => check mode n) = true := by decide +kernel"
        # A single retained counterexample bounds the diagnostic cost of the
        # intentionally false kernel statement; the positive test checks all.
        kernel = lean.split("#eval do")[0].replace(grid,
            "example : check .RNE (-500) = true := by decide +kernel") + "end IntegerRounding\n"
        runtime = lean.replace(grid, "")
        rocq = rocq.replace("let y := @Bnearbyint 24 128 precision_below_max mode x",
                            "let y := @Bnearbyint 24 128 precision_below_max mode_NA x")
        flocq = Path(os.environ["FLOCQ_AUDIT_DIR"]).resolve()
        with tempfile.TemporaryDirectory(prefix="floatspec-integer-oracle-mutation-") as directory:
            folder = Path(directory)
            for name, source, message in (("Kernel", kernel, "is false"),
                                          ("Runtime", runtime, "numerator=-500")):
                path = folder / f"{name}.lean"
                path.write_text(source)
                with self.assertRaisesRegex(RuntimeError, message):
                    bridge.run(["lake", "env", "lean", str(path)])
            path = folder / "WrongMode.v"
            path.write_text(rocq)
            with self.assertRaisesRegex(RuntimeError, "Unable to unify"):
                bridge.run([bridge.configured_coqc(flocq), "-q", "-R", str(flocq / "src"),
                            "Flocq", str(path)])

    def test_all_modes_signs_and_exceptional_values(self):
        flocq = Path(os.environ["FLOCQ_AUDIT_DIR"]).resolve()
        cases = [(width, mode, sign | word)
                 for width, fraction, bias in ((32, 23, 127), (64, 52, 1023))
                 for mode in range(5) for sign in (0, 1 << (width - 1))
                 for word in (0, 1, (bias - 1) << fraction,
                              (bias << fraction) | (1 << (fraction - 1)),
                              (2 * bias + 1) << fraction, ((2 * bias + 1) << fraction) | 1)]
        with tempfile.TemporaryDirectory(prefix="floatspec-integer-test-") as directory:
            folder = Path(directory)
            rows = bridge.execute(cases, flocq, bridge.configured_coqc(flocq), folder)
            self.assertEqual(bridge.compare(cases, rows)[0], [])
            bridge.bootstrap(cases, rows["rocq"], folder)

    def test_wrong_mode_compiled_only_and_native_mutations_fail(self):
        original, original_program = bridge.expression, bridge.program
        for path in ("lean", "compiled", "native"):
            def mutated(case, language):
                if language == path:
                    width, _, word = case
                    return original((width, 1, word), language)
                return original(case, language)
            def mutated_program(cases, execution_path):
                if path == "compiled" and execution_path == "compiled":
                    cases = [(width, 1, word) for width, _, word in cases]
                return original_program(cases, execution_path)
            with self.subTest(path=path), tempfile.TemporaryDirectory(prefix="floatspec-integer-mutation-") as directory:
                output, replay = Path(directory) / "output", Path(directory) / "cases.json"
                case = [64, 4, 0x3ff8000000000000]
                replay.write_text(json.dumps([case]))
                argv = ["ieee_integer_bridge", "--flocq-dir", os.environ["FLOCQ_AUDIT_DIR"],
                        "--skip-build", "--replay", str(replay), "--output", str(output)]
                with (patch("sys.argv", argv), patch.object(bridge, "expression", mutated),
                      patch.object(bridge, "program", mutated_program),
                      contextlib.redirect_stdout(io.StringIO()), self.assertRaises(SystemExit)):
                    bridge.main()
                report = json.loads((output / "report.json").read_text())
                self.assertEqual(report["status"], "mismatch")
                self.assertEqual(report["bootstrapped_lean_cases"], int(path != "lean"))
                self.assertEqual({m["path"] for m in report["mismatches"]},
                                 {"lean", "compiled"} if path == "lean" else {path})
                self.assertEqual(json.loads((output / "replay.json").read_text()), [case])

    def test_timeout_interrupt_and_source_drift_are_errors(self):
        for target, error in (("execute", subprocess.TimeoutExpired("lean", 0.1)),
                              ("execute", KeyboardInterrupt()),
                              ("require_lean_source_snapshot", RuntimeError("source changed"))):
            with self.subTest(error=type(error).__name__), tempfile.TemporaryDirectory() as directory:
                output, replay = Path(directory) / "output", Path(directory) / "cases.json"
                replay.write_text('[[32,0,0]]')
                argv = ["ieee_integer_bridge", "--flocq-dir", os.environ["FLOCQ_AUDIT_DIR"],
                        "--skip-build", "--replay", str(replay), "--output", str(output)]
                with (patch("sys.argv", argv), patch.object(bridge, target, side_effect=error),
                      contextlib.redirect_stdout(io.StringIO()), self.assertRaises(type(error))):
                    bridge.main()
                report = json.loads((output / "report.json").read_text())
                self.assertEqual(report["status"], "error")
                self.assertEqual(report["compared_cases"], 0)


if __name__ == "__main__":
    unittest.main()

