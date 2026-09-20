"""Independent expectations, complete observations and live shared-bug controls."""
import contextlib
import io
import json
import os
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

import flocq_bridge as core
import remainder_bridge as rem


class ProfileTests(unittest.TestCase):
    def test_complete_exhaustive_domain_and_preconditions(self):
        cases = rem.corpus(19, 0)
        self.assertEqual(len(cases), 12100)
        self.assertEqual(len(set(cases)), 12100)
        self.assertEqual(cases, rem.corpus(19, 0))
        self.assertNotEqual(cases, rem.corpus(20, 0))
        counts = [0, 0, 0, 0]
        for case in cases:
            row, qualified, exact = rem.expected(case)
            self.assertEqual(rem.independent_checks(case, row),
                             (qualified, not qualified and not exact))
            counts[0] += int(qualified)
            counts[1] += int(not qualified)
            counts[2] += int(not qualified and not exact)
            counts[3] += int(case.args[2] == 0)
        self.assertEqual(counts, [11582, 518, 380, 220])

    def test_boundaries(self):
        self.assertEqual(rem.expected(rem.Case(rem.OPERATION, (0, -1, 128)))[0],
                         [0, -1, 3, 1, 1, -4])
        self.assertEqual(rem.expected(rem.Case(rem.OPERATION, (3, 1, 128)))[0],
                         [1, -127, 3, 1, 4, 1])
        self.assertEqual(rem.expected(rem.Case(rem.OPERATION, (0, 0, 0)))[0],
                         [0, 0, 0, 0, 0, 0])
        self.assertEqual(rem.expected(rem.Case(rem.OPERATION, (1, -1, 2)))[0][0], -1)
        self.assertEqual(rem.expected(rem.Case(rem.OPERATION, (2, -1, 2)))[0][0], 0)

    def test_invalid_protocol_inputs(self):
        for args in ((4, 1, 2), (0, 225, 1), (0, 1), (True, 1, 2)):
            with self.assertRaises(ValueError):
                rem.Case(rem.OPERATION, args)
        with self.assertRaises(ValueError):
            rem.corpus(1, 1)

    def test_every_observation_and_shared_error_is_checked(self):
        case = rem.Case(rem.OPERATION, (3, 1, 128))
        row = rem.expected(case)[0]
        with rem.profile():
            self.assertEqual(core.compare([case], {p: [list(row)] for p in ("lean", "compiled", "rocq")}), [])
            for column in range(len(rem.COLUMNS)):
                bad = list(row)
                bad[column] += 1
                observations = {p: [bad if p == "compiled" else row]
                                for p in ("lean", "compiled", "rocq")}
                self.assertEqual(len(core.compare([case], observations)), 1)
                with self.assertRaisesRegex(AssertionError, "remainder oracle"):
                    core.compare([case], {p: [bad] for p in observations})

    def test_profile_restores_shared_runner_after_failure(self):
        before = vars(core).copy()
        with self.assertRaises(RuntimeError):
            with rem.profile():
                raise RuntimeError("deliberate")
        self.assertEqual([key for key, value in before.items() if getattr(core, key) is not value], [])


@unittest.skipUnless(os.environ.get("FLOCQ_AUDIT_DIR"), "live tests require FLOCQ_AUDIT_DIR")
class LiveTests(unittest.TestCase):
    def test_shared_wrong_programs_are_rejected_before_bootstrap(self):
        flocq = Path(os.environ["FLOCQ_AUDIT_DIR"]).resolve()
        mutations = (
            ((0, -1, 128), "numerator.tdiv denominator", "numerator.fdiv denominator",
             "Z.quot numerator denominator", "Z.div numerator denominator", "quotient"),
            ((3, 1, 128),
             "binary_round (prec := 3) (emax := 4) .RNE (value < 0) value.natAbs (-4)",
             "StandardFloat.S754_finite (value < 0) value.natAbs (-4)",
             "binary_round 3 4 mode_NE (Z.ltb value 0) (Z.to_pos (Z.abs value)) (-4)",
             "SpecFloat.S754_finite (Z.ltb value 0) (Z.to_pos (Z.abs value)) (-4)", "mantissa"),
        )
        for args, lean_old, lean_new, coq_old, coq_new, column in mutations:
            case = rem.Case(rem.OPERATION, args)
            with self.subTest(column=column), tempfile.TemporaryDirectory(prefix="floatspec-rem-shared-") as directory:
                root = Path(directory)
                baseline = root / "baseline"
                baseline.mkdir()
                with rem.profile():
                    rows = core.execute([case], flocq, core.configured_coqc(flocq), baseline)
                    self.assertEqual(core.compare([case], rows), [])
                replay, output = root / "cases.json", root / "out"
                replay.write_text(json.dumps([rem.asdict(case)]))
                self.assertEqual(rem.LEAN_HEADER.count(lean_old), 1)
                self.assertEqual(rem.COQ_HEADER.count(coq_old), 1)
                with (patch("sys.argv", ["remainder_bridge", "--flocq-dir", str(flocq),
                        "--skip-build", "--replay", str(replay), "--output", str(output)]),
                      patch.object(rem, "LEAN_HEADER", rem.LEAN_HEADER.replace(lean_old, lean_new)),
                      patch.object(rem, "COQ_HEADER", rem.COQ_HEADER.replace(coq_old, coq_new)),
                      patch.object(core, "bootstrap_lean") as bootstrap,
                      contextlib.redirect_stdout(io.StringIO()),
                      self.assertRaisesRegex(AssertionError, "remainder oracle " + column)):
                    rem.main()
                report = json.loads((output / "report.json").read_text())
                self.assertEqual(report["status"], "error")
                self.assertEqual(report["mismatches"], [])
                self.assertEqual(report["bootstrapped_lean_cases"], 0)
                self.assertEqual(report["profile"]["oracle_failure_case"],
                                 json.loads(json.dumps(rem.asdict(case))))
                self.assertEqual(json.loads((output / "cases.json").read_text()),
                                 json.loads(replay.read_text()))
                bootstrap.assert_not_called()


if __name__ == "__main__":
    unittest.main()
