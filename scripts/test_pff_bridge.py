"""Pff profile isolation, independent invariants, live execution and mutations."""
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
import pff_bridge as pff

CASE = pff.Case("pff_source", (3, 1, 0, -1, 1, 1, 10, 2, 8))
# Rocq/kernel/compiled observation retained from seed 850021, case 2115.
ROW = [1, 1, 3, -1, -2, 0, 4, 0, 3, -1, -1, 0, 1, 0, 3, 3, 3, 8,
       3, -10, 1, 1, 3, -1, 2, 0, 0, 0, 3, -1, 3, -1, 8, -2, 1, 1,
       1, 1, 1, 3, 3, -10, 0, 1, 2, 0, 0, 0, 4, -1, 8, -2, 0, 1, 1, 0]


def observations(row=ROW):
    return {name: [list(row)] for name in ("lean", "compiled", "rocq")}


class ProfileTests(unittest.TestCase):
    def test_layout_and_deterministic_inputs(self):
        self.assertEqual(len(pff.COLUMNS), 56)
        self.assertEqual(len(set(pff.COLUMNS)), 56)
        self.assertEqual(pff.corpus(850021, 300), pff.corpus(850021, 300))
        self.assertNotEqual(pff.corpus(850021, 3), pff.corpus(850022, 3))
        self.assertEqual(len(pff.corpus(850021, 300)), 3072)
        cases = pff.corpus(850021, 0)
        self.assertIn(CASE, cases)
        self.assertTrue({-3, -1, 0, 1, 2, 3, 10, 16} <= {case.args[0] for case in cases})
        self.assertTrue(any(case.args[7] == 0 for case in cases))
        self.assertTrue(any(case.args[2] < -case.args[6] for case in cases))
        self.assertTrue(any(abs(case.args[1]) >= case.args[8] + 1 for case in cases))

    def test_input_validation_rejects_injection_bool_and_negative_naturals(self):
        for operation in ("other", "", "pffObserve);"):
            with self.assertRaises(ValueError):
                pff.Case(operation, CASE.args)
        for args in ((), CASE.args[:-1], CASE.args + (0,)):
            with self.assertRaises(ValueError):
                pff.Case("pff_source", args)
        for index in range(9):
            for invalid in (True, "0", 1.5, None):
                args = list(CASE.args)
                args[index] = invalid
                with self.assertRaises(ValueError):
                    pff.Case("pff_source", tuple(args))
        for index in range(5, 9):
            args = list(CASE.args)
            args[index] = -1
            with self.assertRaises(ValueError):
                pff.Case("pff_source", tuple(args))

    def test_large_natural_transport_does_not_use_unary_literals(self):
        case = pff.Case("pff_source", (0, -7, -9, 11, -13, 32, 32, 256, 1024))
        lean, rocq = pff.expressions(case)
        self.assertIn("(1024)", lean)
        self.assertIn("(Z.to_nat (1024%Z))", rocq)
        self.assertIn("(-13%Z)", rocq)
        self.assertEqual(rocq.count("Z.to_nat"), 4)

    def test_profile_restores_every_override_even_after_exception(self):
        before = vars(core).copy()
        with self.assertRaisesRegex(RuntimeError, "deliberate"):
            with pff.profile():
                self.assertEqual(core.WIDTHS, {"pff_source": 56})
                raise RuntimeError("deliberate")
        changed = [name for name, value in before.items() if getattr(core, name) is not value]
        self.assertEqual(changed, [])

    def test_profile_batches_and_replay_preserve_all_inputs(self):
        cases = pff.corpus(850021, 300)
        replay = [pff.Case(row["op"], tuple(row["args"]))
                  for row in json.loads(json.dumps([pff.asdict(case) for case in cases]))]
        with pff.profile():
            batches = list(core.case_batches(replay, 200))
        self.assertEqual([c for _, batch in batches for c in batch], cases)
        self.assertEqual([offset for offset, _ in batches], list(range(0, 3072, 50)))
        self.assertEqual(len(batches[-1][1]), 22)

    def test_all_paths_and_columns_are_checked(self):
        with pff.profile():
            self.assertEqual(core.compare([CASE], observations()), [])
            for path in ("lean", "compiled"):
                for column in range(56):
                    rows = observations()
                    rows[path][0][column] += 1
                    mismatch = core.compare([CASE], rows)
                    self.assertEqual(len(mismatch), 1)
                    self.assertEqual(mismatch[0]["paths"], [path])
                    self.assertEqual(mismatch[0]["case"], pff.asdict(CASE))

    def test_targeted_samples_satisfy_every_neighbor_premise(self):
        cases = pff.valid_neighbor_corpus(859111, 1000)
        self.assertEqual(cases, pff.valid_neighbor_corpus(859111, 1000))
        self.assertNotEqual(cases, pff.valid_neighbor_corpus(859112, 1000))
        self.assertEqual(pff.valid_neighbor_corpus(859111, 0), [])
        self.assertEqual(len(cases), 1000)
        self.assertEqual({case.args[0] for case in cases}, {2, 3, 10, 16})
        self.assertTrue(any(case.args[1] == 0 for case in cases))
        self.assertTrue(any(case.args[1] < 0 for case in cases))
        self.assertTrue(any(case.args[1] > 0 for case in cases))
        self.assertTrue(any(case.args[2] == -case.args[6] for case in cases))
        self.assertTrue(any(case.args[2] > -case.args[6] for case in cases))
        for case in cases:
            radix, mantissa, exponent, _, _, _, bound_exp, precision, bound_pred = case.args
            self.assertGreaterEqual(radix, 2)
            self.assertGreater(precision, 0)
            self.assertEqual(bound_pred + 1, radix ** precision)
            self.assertLessEqual(bound_pred + 1, 4096)
            self.assertLess(abs(mantissa), bound_pred + 1)
            self.assertGreaterEqual(exponent, -bound_exp)
        self.assertEqual(pff.corpus(859111, 10)[-10:], pff.valid_neighbor_corpus(859111, 10))

    def test_missing_path_truncation_and_boolean_are_errors(self):
        with pff.profile():
            for path in ("lean", "compiled", "rocq"):
                rows = observations()
                del rows[path]
                with self.assertRaises(ValueError):
                    core.compare([CASE], rows)
                rows = observations()
                rows[path][0].pop()
                with self.assertRaises(ValueError):
                    core.compare([CASE], rows)
            bad = list(ROW)
            bad[0] = True
            with self.assertRaises(ValueError):
                core.compare([CASE], observations(bad))

    def test_independent_oracle_and_premise_gated_neighbor_checks(self):
        count, neighbors = pff.independent_checks(CASE, ROW)
        self.assertEqual(neighbors, 5)
        self.assertGreaterEqual(count, 20)
        # Compilers agreeing on the SAME wrong answer must still fail.
        for group in ("source.Fshift", "source.Fplus", "source.Fminus",
                      "source.Fnormalize", "source.Fopp", "source.Fabs",
                      "source.FNSucc", "source.FNPred", "source.FNeven"):
            bad = list(ROW)
            offset = pff.OFFSETS[group]
            bad[offset] += 100 if "FNeven" not in group else 1
            with pff.profile() as metadata:
                with self.assertRaises(AssertionError):
                    core.compare([CASE], observations(bad))
                self.assertEqual(metadata["oracle_failure_case"], pff.asdict(CASE))
                self.assertEqual(metadata["oracle_checked_cases"], 0)

    def driver(self, error=None, skip=False, row=ROW, oracle_error=False):
        with tempfile.TemporaryDirectory() as directory:
            folder = Path(directory)
            replay, output = folder / "cases.json", folder / "out"
            replay.write_text(json.dumps([pff.asdict(CASE)]))
            argv = ["pff_bridge", "--flocq-dir", directory, "--coqc", "coqc",
                    "--replay", str(replay), "--output", str(output)]
            if skip:
                argv.append("--skip-build")
            with (patch("sys.argv", argv),
                  patch.object(core, "verify_reference", return_value="pin"),
                  patch.object(core, "run", return_value="metadata") as run,
                  patch.object(core, "lean_source_fingerprint", return_value="snapshot"),
                  patch.object(core, "execute", side_effect=error,
                               return_value=observations(row)),
                  patch.object(core, "bootstrap_lean") as bootstrap,
                  contextlib.redirect_stdout(io.StringIO())):
                if oracle_error:
                    with self.assertRaises(AssertionError):
                        pff.main()
                elif error is None:
                    pff.main()
                else:
                    with self.assertRaises(type(error)):
                        pff.main()
            report = json.loads((output / "report.json").read_text())
            commands = [call.args[0] for call in run.call_args_list]
            return report, commands, bootstrap.call_count

    def test_driver_builds_profile_target_and_records_oracle_metadata(self):
        report, commands, bootstraps = self.driver()
        self.assertIn(["lake", "build", "FloatSpec.src.Pff.SourceFacade"], commands)
        self.assertEqual(report["status"], "passed")
        self.assertTrue(report["fresh_build"])
        self.assertEqual(report["profile"]["columns"], list(pff.COLUMNS))
        self.assertEqual(report["profile"]["legacy_normalized_radix"], 2)
        self.assertEqual(report["profile"]["oracle_checked_cases"], 1)
        self.assertEqual(report["profile"]["conditional_neighbor_assertions"], 5)
        self.assertEqual(report["bootstrapped_lean_cases"], 1)
        self.assertEqual(bootstraps, 1)

    def test_skip_build_is_explicit(self):
        report, commands, _ = self.driver(skip=True)
        self.assertFalse(report["fresh_build"])
        self.assertFalse(any(command[:2] == ["lake", "build"] for command in commands))

    def test_matching_wrong_results_retain_oracle_failure_input(self):
        wrong = list(ROW)
        wrong[pff.OFFSETS["source.Fplus"]] += 1
        report, _, bootstraps = self.driver(row=wrong, oracle_error=True)
        self.assertEqual(report["status"], "error")
        self.assertEqual(report["profile"]["oracle_failure_case"],
                         json.loads(json.dumps(pff.asdict(CASE))))
        self.assertEqual(report["profile"]["oracle_checked_cases"], 0)
        self.assertEqual(bootstraps, 0)

    def test_timeout_interrupt_and_other_failure_never_pass(self):
        for error in (subprocess.TimeoutExpired("lean", 0.1), KeyboardInterrupt(),
                      RuntimeError("deliberate source drift")):
            report, _, bootstraps = self.driver(error)
            self.assertEqual(report["status"], "error")
            self.assertIn(type(error).__name__, report["error"])
            self.assertEqual(report["compared_cases"], 0)
            self.assertEqual(report["profile"]["oracle_checked_cases"], 0)
            self.assertEqual(bootstraps, 0)


@unittest.skipUnless(os.environ.get("FLOCQ_AUDIT_DIR"), "live tests require FLOCQ_AUDIT_DIR")
class LiveTests(unittest.TestCase):
    def test_large_natural_and_invalid_domains_execute_all_three_paths(self):
        cases = [CASE,
                 pff.Case("pff_source", (0, -7, -9, 11, -13, 32, 32, 256, 1024)),
                 pff.Case("pff_source", (-3, -17, -7, 18, -8, 1, 2, 0, 0))]
        flocq = Path(os.environ["FLOCQ_AUDIT_DIR"]).resolve()
        with pff.profile() as metadata, tempfile.TemporaryDirectory(prefix="floatspec-pff-live-") as directory:
            folder = Path(directory)
            rows = core.execute(cases, flocq, core.configured_coqc(flocq), folder)
            self.assertEqual(rows["rocq"][0], ROW)
            self.assertEqual(core.compare(cases, rows), [])
            core.bootstrap_lean(cases, rows["rocq"], folder)
            self.assertEqual(metadata["oracle_checked_cases"], len(cases))

    def test_live_mutation_in_every_observation_column_is_detected(self):
        # Each input chooses one different corrupt column. Both actual Lean
        # execution paths are mutated; the pinned Rocq program is unchanged.
        header = pff.LEAN_HEADER.replace("def pffObserve (", "def pffObserveOriginal (")
        header += """
def pffObserve (radix mantissa exponent otherMantissa otherExponent : Int)
    (shift boundExponent precision boundMantissaPred : Nat) : List Int :=
  (pffObserveOriginal radix mantissa exponent otherMantissa otherExponent
    shift boundExponent precision boundMantissaPred).mapIdx fun index value =>
      if index == mantissa.toNat then value + 1 else value
"""
        cases = [pff.Case("pff_source", (3, column, 0, -1, 1, 1, 10, 2, 8))
                 for column in range(56)]
        flocq = Path(os.environ["FLOCQ_AUDIT_DIR"]).resolve()
        with (pff.profile(), patch.object(core, "LEAN_HEADER", header),
              tempfile.TemporaryDirectory(prefix="floatspec-pff-mutations-") as directory):
            rows = core.execute(cases, flocq, core.configured_coqc(flocq), Path(directory))
            mismatches = core.compare(cases, rows)
            self.assertEqual(len(mismatches), 56)
            for column, mismatch in enumerate(mismatches):
                self.assertEqual(mismatch["index"], column)
                self.assertEqual(mismatch["paths"], ["lean", "compiled"])
                for path in ("lean", "compiled"):
                    differences = [index for index, (left, right) in
                                   enumerate(zip(mismatch[path], mismatch["rocq"], strict=True))
                                   if left != right]
                    self.assertEqual(differences, [column])

    def test_wrong_bootstrap_expectation_is_rejected_by_lean(self):
        wrong = list(ROW)
        wrong[0] += 1
        with pff.profile(), tempfile.TemporaryDirectory(prefix="floatspec-pff-bootstrap-mutation-") as directory:
            with self.assertRaises(RuntimeError):
                core.bootstrap_lean([CASE], [wrong], Path(directory))

    def test_compiled_only_mutation_retains_mismatch_report_and_replay(self):
        original = core.compiled_source
        def mutated(rows, instances):
            source = original(rows, instances)
            return source.replace("def pffObserve (", "def pffObserveOriginal (").replace(
                "def main : IO Unit :=", """def pffObserve (radix mantissa exponent otherMantissa otherExponent : Int)
    (shift boundExponent precision boundMantissaPred : Nat) : List Int :=
  (pffObserveOriginal radix mantissa exponent otherMantissa otherExponent
    shift boundExponent precision boundMantissaPred).mapIdx fun index value =>
      if index == 48 then value + 1 else value
def main : IO Unit :=""")
        with tempfile.TemporaryDirectory(prefix="floatspec-pff-compiled-mutation-") as directory:
            folder = Path(directory)
            output, replay = folder / "out", folder / "cases.json"
            replay.write_text(json.dumps([pff.asdict(CASE)]))
            argv = ["pff_bridge", "--flocq-dir", os.environ["FLOCQ_AUDIT_DIR"],
                    "--skip-build", "--replay", str(replay), "--output", str(output)]
            with (patch("sys.argv", argv), patch.object(core, "compiled_source", mutated),
                  contextlib.redirect_stdout(io.StringIO()), self.assertRaises(SystemExit)):
                pff.main()
            report = json.loads((output / "report.json").read_text())
            self.assertEqual(report["status"], "mismatch")
            self.assertEqual(report["mismatches"][0]["paths"], ["compiled"])
            self.assertEqual(report["bootstrapped_lean_cases"], 1)
            self.assertEqual(json.loads((output / "replay.json").read_text()),
                             json.loads(replay.read_text()))


if __name__ == "__main__":
    unittest.main()
