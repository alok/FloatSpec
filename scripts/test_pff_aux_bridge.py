"""Source-bound profile tests, plus exact-rational local-helper mutation tests."""
import contextlib
import io
import json
import os
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

import flocq_bridge as core
import pff_aux_bridge as aux
import pff_bridge as pff

CASE = aux.Case("pff_bounds", (2, 3, -10, 1, 0, 3, -1))
ROW = [8, 10, 16777216, 149, 9007199254740992, 1074, 4, -2, 6, -2]


class ProfileTests(unittest.TestCase):
    def test_domains_seed_layout_and_replay(self):
        cases = aux.corpus(852017, 200)
        self.assertEqual(len(cases), 2216)
        self.assertEqual(cases, aux.corpus(852017, 200))
        self.assertNotEqual(cases, aux.corpus(852018, 200))
        self.assertEqual(len(aux.COLUMNS), 10)
        self.assertEqual(len(set(aux.COLUMNS)), 10)
        for args in ((1, *CASE.args[1:]), (-3, *CASE.args[1:]),
                     (2, True, *CASE.args[2:]), CASE.args[:-1]):
            with self.assertRaises(ValueError):
                aux.Case("pff_bounds", args)
        with self.assertRaises(ValueError):
            aux.Case("pff_source", CASE.args)
        self.assertTrue(any(case.args[1] < 0 for case in cases))
        self.assertTrue(any(case.args[2] > 0 for case in cases))
        self.assertEqual([aux.Case(row["op"], tuple(row["args"])) for row in
                          json.loads(json.dumps([aux.asdict(c) for c in cases]))], cases)

    def test_profiles_are_nested_and_restored_on_failure(self):
        before = vars(core).copy()
        with pff.profile():
            self.assertEqual(core.Case, pff.Case)
            with self.assertRaisesRegex(RuntimeError, "deliberate"):
                with aux.profile():
                    self.assertEqual(core.Case, aux.Case)
                    self.assertEqual(core.RADIX_OPS, {"pff_bounds"})
                    raise RuntimeError("deliberate")
            self.assertEqual(core.Case, pff.Case)
        self.assertEqual([name for name, value in before.items() if getattr(core, name) is not value], [])

    def test_all_columns_paths_and_independent_oracle(self):
        with aux.profile() as metadata:
            rows = {path: [list(ROW)] for path in ("lean", "compiled", "rocq")}
            self.assertEqual(core.compare([CASE], rows), [])
            self.assertEqual(metadata["oracle_checked_cases"], 1)
            self.assertEqual(metadata["oracle_assertions"], 6)
            for path in ("lean", "compiled"):
                for column in range(10):
                    changed = {name: [list(ROW)] for name in rows}
                    changed[path][0][column] += 1
                    self.assertEqual(core.compare([CASE], changed)[0]["paths"], [path])
            for column in range(10):
                changed = list(ROW)
                changed[column] += 1
                with self.assertRaises(AssertionError):
                    core.compare([CASE], {name: [list(changed)] for name in rows})
                self.assertEqual(metadata["oracle_failure_case"], aux.asdict(CASE))
            with self.assertRaises(ValueError):
                core.compare([CASE], {"lean": [ROW], "rocq": [ROW]})

    def test_batching_retains_order_and_caps(self):
        cases = aux.corpus(852017, 200)
        with aux.profile():
            batches = list(core.case_batches(cases, 200))
        self.assertEqual([case for _, batch in batches for case in batch], cases)
        self.assertEqual(len(batches), 45)
        self.assertEqual(len(batches[-1][1]), 16)


@unittest.skipUnless(os.environ.get("FLOCQ_AUDIT_DIR"), "live tests require FLOCQ_AUDIT_DIR")
class LiveTests(unittest.TestCase):
    def test_reference_boundary_controls_and_bootstrap(self):
        cases = [CASE, aux.Case("pff_bounds", (3, -3, 1074, -17, -1075, 0, 10)),
                 aux.Case("pff_bounds", (16, 53, -149, 1, 3, -1, -1))]
        flocq = Path(os.environ["FLOCQ_AUDIT_DIR"]).resolve()
        with aux.profile(), tempfile.TemporaryDirectory(prefix="floatspec-pff-aux-live-") as directory:
            rows = core.execute(cases, flocq, core.configured_coqc(flocq), Path(directory))
            self.assertEqual(rows["rocq"][0], ROW)
            self.assertEqual(core.compare(cases, rows), [])
            core.bootstrap_lean(cases, rows["rocq"], Path(directory))

    def test_every_live_column_mutation(self):
        header = aux.LEAN_HEADER.replace("def pffBoundsObserve (", "def pffBoundsObserveOriginal (")
        header += """
def pffBoundsObserve (radix : Int) [ValidRadix radix]
    (precision boundExponent mantissa exponent otherMantissa otherExponent : Int) : List Int :=
  (pffBoundsObserveOriginal radix precision boundExponent mantissa exponent
    otherMantissa otherExponent).mapIdx fun index value =>
      if index == mantissa.toNat then value + 1 else value
"""
        cases = [aux.Case("pff_bounds", (3, 2, -10, column, 0, -1, 1))
                 for column in range(10)]
        flocq = Path(os.environ["FLOCQ_AUDIT_DIR"]).resolve()
        with (aux.profile(), patch.object(core, "LEAN_HEADER", header),
              tempfile.TemporaryDirectory(prefix="floatspec-pff-aux-mutations-") as directory):
            rows = core.execute(cases, flocq, core.configured_coqc(flocq), Path(directory))
            mismatches = core.compare(cases, rows)
            self.assertEqual(len(mismatches), 10)
            for column, mismatch in enumerate(mismatches):
                self.assertEqual(mismatch["paths"], ["lean", "compiled"])
                for path in ("lean", "compiled"):
                    self.assertEqual([index for index, (left, right) in
                                      enumerate(zip(mismatch[path], mismatch["rocq"], strict=True))
                                      if left != right], [column])

    def test_exact_rational_lean_oracle_rejects_reversed_comparison(self):
        root = Path(__file__).resolve().parents[1]
        source = (root / "FloatSpec/Test/PffAuxExecution.lean").read_text()
        mutated = source.replace("pff_compare beta x y == comparison",
                                 "pff_compare beta x y == -comparison")
        self.assertNotEqual(source, mutated)
        kernel = mutated.split("#eval do")[0] + "\nend FloatSpec.Test.PffAuxExecution\n"
        runtime = mutated.replace(
            "theorem local_helpers_kernel : smallGrid 2 = true := by decide +kernel", "")
        runtime = runtime.replace("#print axioms local_helpers_kernel", "")
        with tempfile.TemporaryDirectory(prefix="floatspec-pff-aux-oracle-mutation-") as directory:
            for name, content, message in (("Kernel", kernel, "Tactic .decide. failed"),
                                            ("Runtime", runtime, "Pff auxiliary comparison failed")):
                path = Path(directory) / f"{name}.lean"
                path.write_text(content)
                with self.assertRaisesRegex(RuntimeError, message):
                    core.run(["lake", "env", "lean", str(path)])
            # Establish falsity positively as well: a failure diagnostic alone
            # does not distinguish a false claim from an evaluation failure.
            false_path = Path(directory) / "KernelFalseControl.lean"
            false_path.write_text(kernel.replace("smallGrid 2 = true", "smallGrid 2 = false"))
            core.run(["lake", "env", "lean", str(false_path)])

    def test_rocq_negative_precision_control_rejects_absolute_power_mutation(self):
        root = Path(__file__).resolve().parents[1]
        source = (root / "scripts/fixtures/PffAuxExecution.v").read_text()
        mutated = source.replace("make_bound radix2 (-3) (-10)", "make_bound radix2 3 (-10)")
        self.assertNotEqual(source, mutated)
        flocq = Path(os.environ["FLOCQ_AUDIT_DIR"]).resolve()
        with tempfile.TemporaryDirectory(prefix="floatspec-pff-bound-mutation-") as directory:
            path = Path(directory) / "WrongBound.v"
            path.write_text(mutated)
            with self.assertRaises(RuntimeError):
                core.run([core.configured_coqc(flocq), "-q", "-R", str(flocq / "src"), "Flocq", str(path)])


if __name__ == "__main__":
    unittest.main()
