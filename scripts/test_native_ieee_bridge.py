"""Four-path guards, including independent native and compiled-model mutations."""

import contextlib
import io
import json
import os
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

import native_ieee_bridge as bridge


class CorpusTests(unittest.TestCase):
    def test_seed_and_boundary_coverage(self):
        words = bridge.corpus(17, 20)
        self.assertEqual(words, bridge.corpus(17, 20))
        self.assertNotEqual(words, bridge.corpus(18, 20))
        self.assertEqual(set(map(bridge.category, words)),
                         {"normal", "subnormal", "zero", "infinity", "nan"})
        for word in (0, 1 << 63, 1, (1 << 52) - 1, 1 << 52, 0x7fefffffffffffff,
                     0x7ff0000000000000, 0xfff0000000000000,
                     0x7ff0000000000001, 0xfff8000000000000):
            self.assertIn(word, words)

    def test_replay_validation(self):
        for word in (-1, 1 << 64, True, "1", 1.0):
            with self.subTest(word=word), self.assertRaises(ValueError):
                bridge.validate_word(word)

    def test_frexp_exceptions_are_explicit_not_blindly_compared(self):
        native = [[0, 1, 0x8000000000000001, 0, 0]]
        model = [[0, 1, 0x8000000000000001, 0, -2101]]
        mismatches, exceptions = bridge.compare([0], {"native": native,
                                                     "model": model, "compiled_model": model, "rocq": model})
        self.assertEqual(mismatches, [])
        self.assertEqual(len(exceptions), 1)
        self.assertFalse(exceptions[0]["frexp_equality_asserted"])
        # The same native/model difference is a failure for a nonzero input.
        mismatches, _ = bridge.compare([1], {"native": native, "model": model, "compiled_model": model, "rocq": model})
        self.assertEqual(mismatches[0]["path"], "native-versus-rocq")

    def test_model_exceptions_still_must_match_rocq(self):
        left, right = [[0, 1, 2, 0, 0]], [[0, 1, 2, 0, -2101]]
        mismatches, _ = bridge.compare([0], {"native": left, "model": left, "compiled_model": right, "rocq": right})
        self.assertEqual(mismatches[0]["path"], "model-versus-rocq")

    def test_compiled_model_exceptions_still_must_match_rocq(self):
        native = [[0, 1, 2, 0, 0]]
        model = [[0, 1, 2, 0, -2101]]
        mismatches, exceptions = bridge.compare([0], {"native": native, "model": model,
            "compiled_model": native, "rocq": model})
        self.assertEqual([row["path"] for row in mismatches], ["compiled-model-versus-rocq"])
        self.assertFalse(exceptions[0]["frexp_equality_asserted"])

    def test_missing_compiled_path_is_not_a_three_path_pass(self):
        with self.assertRaisesRegex(ValueError, "four execution paths"):
            bridge.compare([1], {name: [[0] * 5] for name in ("native", "model", "rocq")})

    def test_all_paths_and_columns_required(self):
        for observations in ({"native": [[0] * 5], "rocq": [[0] * 5]},
                             {name: [[0] * 4] for name in ("native", "model", "compiled_model", "rocq")},
                             {name: [] for name in ("native", "model", "compiled_model", "rocq")}):
            with self.assertRaises(ValueError):
                bridge.compare([0], observations)


@unittest.skipUnless(os.environ.get("FLOCQ_AUDIT_DIR"), "live test requires FLOCQ_AUDIT_DIR")
class LiveTests(unittest.TestCase):
    def test_four_paths_execute_and_bootstrap(self):
        flocq = Path(os.environ["FLOCQ_AUDIT_DIR"]).resolve()
        words = [0, 1, 0x7ff0000000000000, 0xfff0000000000001]
        with tempfile.TemporaryDirectory(prefix="floatspec-native-test-") as directory:
            folder = Path(directory)
            results = bridge.execute(words, flocq, bridge.configured_coqc(flocq), folder)
            mismatches, exceptions = bridge.compare(words, results)
            self.assertEqual(mismatches, [])
            self.assertEqual(len(exceptions), 3)
            bridge.bootstrap_lean(words, results["rocq"], folder)
        self.assertEqual(results["native"][1], [1, 2, 0, 4602678819172646912, -1073])

    def test_live_native_mutation_exits_with_replay(self):
        original = bridge.native_source

        def wrong_native_path(words):
            # Deliberately replace successor by predecessor. The other three
            # implementations and the real native FFI still run unmodified.
            wrong = """def wrongObservation (word : UInt64) : List Int :=
  let x := Float.ofBits word
  let result := x.frExp
  [x.toModel.toBits.toNat,
   (FaithfulPrimFloat.PrimitiveFloat.nativeNextDown x).toModel.toBits.toNat,
   (FaithfulPrimFloat.PrimitiveFloat.nativeNextDown x).toModel.toBits.toNat,
   result.1.toModel.toBits.toNat, result.2]
"""
            return original(words).replace("def main", wrong + "def main").replace(
                ".map nativeObservation", ".map wrongObservation")

        with tempfile.TemporaryDirectory(prefix="floatspec-native-mutation-") as directory:
            output, replay = Path(directory) / "output", Path(directory) / "cases.json"
            replay.write_text("[1]\n")
            argv = ["native_ieee_bridge", "--flocq-dir", os.environ["FLOCQ_AUDIT_DIR"],
                    "--replay", str(replay), "--output", str(output)]
            with (patch("sys.argv", argv), patch.object(bridge, "native_source", wrong_native_path),
                  contextlib.redirect_stdout(io.StringIO()), self.assertRaises(SystemExit)):
                bridge.main()
            report = json.loads((output / "report.json").read_text())
            self.assertEqual(report["status"], "mismatch")
            self.assertEqual(report["mismatches"][0]["path"], "native-versus-rocq")
            self.assertEqual(report["bootstrapped_lean_cases"], 1)
            self.assertEqual(json.loads((output / "replay.json").read_text()), [1])

    def test_live_compiled_model_mutation_exits_with_replay(self):
        original = bridge.compiled_model_source

        def wrong_compiled_path(words):
            # Native, kernel, and Rocq observations stay correct. A passing
            # generated kernel proof must not hide a compiled-path mismatch.
            wrong = """def wrongObservation (word : UInt64) : List Int :=
  (modelObservation word).map (fun value => value + 1)
"""
            return original(words).replace("def main", wrong + "def main").replace(
                ".map modelObservation", ".map wrongObservation")

        with tempfile.TemporaryDirectory(prefix="floatspec-compiled-model-mutation-") as directory:
            output, replay = Path(directory) / "output", Path(directory) / "cases.json"
            replay.write_text("[1]\n")
            argv = ["native_ieee_bridge", "--flocq-dir", os.environ["FLOCQ_AUDIT_DIR"],
                    "--replay", str(replay), "--output", str(output)]
            with (patch("sys.argv", argv),
                  patch.object(bridge, "compiled_model_source", wrong_compiled_path),
                  contextlib.redirect_stdout(io.StringIO()), self.assertRaises(SystemExit)):
                bridge.main()
            report = json.loads((output / "report.json").read_text())
            self.assertEqual(report["status"], "mismatch")
            self.assertEqual([row["path"] for row in report["mismatches"]],
                             ["compiled-model-versus-rocq"])
            self.assertEqual(report["compiled_model_cases"], 1)
            self.assertEqual(report["bootstrapped_lean_cases"], 1)
            self.assertEqual(json.loads((output / "replay.json").read_text()), [1])


if __name__ == "__main__":
    unittest.main()
