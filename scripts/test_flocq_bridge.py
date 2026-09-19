"""Harness regressions; set FLOCQ_AUDIT_DIR to include live prover/mutation tests."""

import contextlib
import io
import json
import os
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

import flocq_bridge as bridge


class ParserTests(unittest.TestCase):
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

    def test_seed_replay_and_api_coverage(self):
        first = bridge.corpus(17, 10)
        self.assertEqual(first, bridge.corpus(17, 10))
        self.assertNotEqual(first, bridge.corpus(18, 10))
        self.assertEqual({case.op for case in first}, set(bridge.OPS))
        self.assertIn(bridge.Case("div_eucl", (7, 0)), first)
        self.assertIn(bridge.Case("power", (2, -1)), first)
        self.assertIn(bridge.Case("div_eucl", (7, -3)), first)

    def test_replay_input_validation(self):
        for op, args in (("no_such_function", ()), ("power", (2,)),
                         ("power", (2, "sorry")), ("power", (2, True)),
                         ("location", (4, 2, -1)), ("round", (2, 0, 1)),
                         ("sqrt", (1, 4, 0, 0)), ("overflow", (0, 4, 0, 0)),
                         ("overflow", (4, 4, 0, 0)), ("overflow", (3, 4, 5, 0))):
            with self.subTest(op=op, args=args), self.assertRaises(ValueError):
                bridge.Case(op, args)


@unittest.skipUnless(os.environ.get("FLOCQ_AUDIT_DIR"), "live test requires FLOCQ_AUDIT_DIR")
class LiveTests(unittest.TestCase):
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
                   for fmt in range(4)], bridge.Case("overflow", (3, 4, 1, 0))]
        with tempfile.TemporaryDirectory(prefix="floatspec-bridge-test-") as directory:
            lean, rocq = bridge.execute(cases, flocq, bridge.configured_coqc(flocq), Path(directory))
        self.assertEqual(lean, rocq)
        self.assertEqual(lean[0], [0])
        self.assertEqual(lean[1], [-3, -2])
        self.assertEqual(lean[7], [0, 0])
        self.assertEqual(lean[-1], [3, 0, 7, 1, 1])

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
