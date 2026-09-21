"""Pff integer protocol checks, source execution and shared-bug mutation controls."""
import contextlib
import io
import json
import os
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest.mock import patch

import flocq_bridge as core
import pff_integer_bridge as pff


class ProfileTests(unittest.TestCase):
    def test_deterministic_boundary_corpus(self):
        cases = pff.corpus(863211, 30)
        self.assertEqual(len(cases), 822)
        self.assertEqual(cases, pff.corpus(863211, 30))
        self.assertNotEqual(cases, pff.corpus(863212, 30))
        self.assertEqual(sum(c.op == "pff_quotient" and c.args[1] == 0
                             for c in pff.corpus(863211, 0)), 11)
        self.assertTrue(any(abs(c.args[0]) > 2**64 for c in cases))

    def test_input_domains_reject_invalid_positive_and_option_values(self):
        for op, args in (("pff_pdiv", (0, 1)), ("pff_pdiv", (1, 0)),
                         ("pff_pdiv", (-1, 3)), ("pff_option", (-1,)),
                         ("pff_maxdiv", (2, 8, -1)),
                         ("pff_quotient", (True, 3)), ("pff_quotient", ("0", 1)),
                         ("pff_quotient", (1,)), ("invented", (1, 2))):
            with self.assertRaises(ValueError):
                pff.Case(op, args)

    def test_signed_zero_and_option_boundaries(self):
        for numerator, denominator, answer in ((-7,3,-2), (7,-3,-2), (-7,-3,2),
                                               (-7,0,0), (0,0,0)):
            self.assertEqual(pff.expected(pff.Case("pff_quotient", (numerator, denominator))), [answer])
        self.assertEqual(pff.expected(pff.Case("pff_pdiv", (1,3))), [0,0,0,0,1,1,1,1])
        self.assertEqual(pff.expected(pff.Case("pff_pdiv", (3,1))), [1,3,3,3,0,0,0,0])
        self.assertEqual(pff.expected(pff.Case("pff_option", (0,))), [0,0,0,0])

    def test_all_fields_and_shared_wrong_results_are_checked(self):
        for case in (pff.Case("pff_quotient", (-7,3)), pff.Case("pff_pdiv", (7,3)),
                     pff.Case("pff_option", (1,)), pff.Case("pff_divides", (6,3)),
                     pff.Case("pff_maxdiv", (2,8,4))):
            row = pff.expected(case)
            with pff.profile():
                self.assertEqual(core.compare([case], {p:[row] for p in ("lean","compiled","rocq")}), [])
                for column in range(len(row)):
                    bad = list(row)
                    bad[column] += 1
                    observations = {p:[bad if p == "compiled" else row]
                                    for p in ("lean","compiled","rocq")}
                    self.assertEqual(len(core.compare([case], observations)), 1)
                    with self.assertRaisesRegex(AssertionError, "Pff integer oracle"):
                        core.compare([case], {p:[bad] for p in observations})

    def test_profile_is_restored_after_exception(self):
        before = vars(core).copy()
        with self.assertRaises(RuntimeError):
            with pff.profile():
                raise RuntimeError("deliberate")
        self.assertEqual([key for key,value in before.items() if getattr(core,key) is not value], [])

    def test_random_inputs_are_batched_not_one_prover_per_case(self):
        cases = pff.corpus(863211, 300)
        with pff.profile():
            batches = list(core.case_batches(cases, 100))
        self.assertEqual([case for _, batch in batches for case in batch], cases)
        self.assertEqual(len(batches), 25)

    def test_driver_records_failures_never_passes_or_bootstraps(self):
        case = pff.Case("pff_quotient", (-7,3))
        for error in (subprocess.TimeoutExpired("lean", 0.1), KeyboardInterrupt(),
                      RuntimeError("deliberate source drift")):
            with tempfile.TemporaryDirectory() as directory:
                root = Path(directory)
                replay = root / "cases.json"
                replay.write_text(json.dumps([pff.asdict(case)]))
                with (patch("sys.argv", ["pff_integer_bridge", "--flocq-dir", str(root),
                        "--coqc", "mock-coqc", "--skip-build", "--replay", str(replay),
                        "--output", str(root/"out")]),
                      patch.object(core, "verify_reference", return_value="pin"),
                      patch.object(core, "run", return_value="metadata"),
                      patch.object(core, "lean_source_fingerprint", return_value="snapshot"),
                      patch.object(core, "execute", side_effect=error),
                      patch.object(core, "bootstrap_lean") as bootstrap,
                      contextlib.redirect_stdout(io.StringIO()), self.assertRaises(type(error))):
                    pff.main()
                report = json.loads((root/"out/report.json").read_text())
                self.assertEqual(report["status"], "error")
                self.assertEqual(report["bootstrapped_lean_cases"], 0)
                bootstrap.assert_not_called()


@unittest.skipUnless(os.environ.get("FLOCQ_AUDIT_DIR"), "live tests require FLOCQ_AUDIT_DIR")
class LiveTests(unittest.TestCase):
    def test_shared_wrong_programs_fail_independent_gate(self):
        flocq = Path(os.environ["FLOCQ_AUDIT_DIR"]).resolve()
        mutations = (
            (pff.Case("pff_quotient", (-7,3)), "Zquotient numerator denominator",
             "numerator.fdiv denominator", "Pff.Zquotient numerator denominator",
             "Z.div numerator denominator", "quotient"),
            (pff.Case("pff_pdiv", (7,3)), "optionFields result.1 ++ optionFields result.2",
             "optionFields result.2 ++ optionFields result.1",
             "optionFields (fst result) ++ optionFields (snd result)",
             "optionFields (snd result) ++ optionFields (fst result)", "quotient.payload"),
            (pff.Case("pff_option", (0,)), "| none => [0, 0]", "| none => [1, 0]",
             "| Pff.None => [0; 0]", "| Pff.None => [1; 0]", "tag"),
            (pff.Case("pff_divides", (6,3)), "@decide (Zdivides value divisor) (ZdividesP value divisor)",
             "@decide (Zdivides divisor value) (ZdividesP divisor value)", "Pff.ZdividesP value divisor",
             "Pff.ZdividesP divisor value", "divides"),
            (pff.Case("pff_maxdiv", (2,8,4)), "maxDiv radix value bound",
             "maxDiv radix value (bound - bound)", "Pff.maxDiv radix value (Z.to_nat bound)",
             "Pff.maxDiv radix value 0", "maxDiv"),
        )
        for case, lean_old, lean_new, coq_old, coq_new, column in mutations:
            with self.subTest(column=column), tempfile.TemporaryDirectory(prefix="floatspec-pff-integer-") as directory:
                root = Path(directory)
                baseline = root/"baseline"
                baseline.mkdir()
                with pff.profile():
                    rows = core.execute([case], flocq, core.configured_coqc(flocq), baseline)
                    self.assertEqual(core.compare([case], rows), [])
                    core.bootstrap_lean([case], rows["rocq"], baseline)
                replay, output = root/"cases.json", root/"out"
                replay.write_text(json.dumps([pff.asdict(case)]))
                self.assertEqual(pff.LEAN_HEADER.count(lean_old), 1)
                self.assertEqual(pff.COQ_HEADER.count(coq_old), 1)
                with (patch("sys.argv", ["pff_integer_bridge", "--flocq-dir", str(flocq),
                        "--skip-build", "--replay", str(replay), "--output", str(output)]),
                      patch.object(pff, "LEAN_HEADER", pff.LEAN_HEADER.replace(lean_old, lean_new)),
                      patch.object(pff, "COQ_HEADER", pff.COQ_HEADER.replace(coq_old, coq_new)),
                      patch.object(core, "bootstrap_lean") as bootstrap,
                      contextlib.redirect_stdout(io.StringIO()),
                      self.assertRaisesRegex(AssertionError, "Pff integer oracle " + column)):
                    pff.main()
                report = json.loads((output/"report.json").read_text())
                self.assertEqual(report["status"], "error")
                self.assertEqual(report["mismatches"], [])
                self.assertEqual(report["bootstrapped_lean_cases"], 0)
                self.assertEqual(report["profile"]["oracle_failure_case"],
                                 json.loads(json.dumps(pff.asdict(case))))
                self.assertEqual(json.loads((output/"cases.json").read_text()),
                                 json.loads(replay.read_text()))
                bootstrap.assert_not_called()


if __name__ == "__main__":
    unittest.main()
