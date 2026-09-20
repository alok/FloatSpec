"""Live controls for remainder type boundaries and finite representability checks."""

import os
from pathlib import Path
import tempfile
import unittest

import flocq_bridge as core


ROOT = Path(__file__).resolve().parents[1]


def mutated(source, old, new):
    if source.count(old) != 1:
        raise ValueError("mutation must select exactly one expression")
    return source.replace(old, new)


class LeanControls(unittest.TestCase):
    def reject(self, fixture, old, new):
        source = (ROOT / "scripts/fixtures" / (fixture + ".lean")).read_text()
        wrong = mutated(source, old, new)
        with tempfile.TemporaryDirectory(prefix="floatspec-rem-lean-") as directory:
            path = Path(directory) / "Control.lean"
            path.write_text(source)
            core.run(["lake", "env", "lean", str(path)])
            path.write_text(wrong)
            with self.assertRaisesRegex(RuntimeError, "Type mismatch|Tactic .decide. proved"):
                core.run(["lake", "env", "lean", str(path)])

    def test_contract_requires_small_quotient_premise(self):
        self.reject("RemainderContracts",
                    "    (|x / y| < (1 / 2 : Real) → rnd (x / y) = 0) →\n", "")

    def test_grid_cannot_ignore_source_premise(self):
        self.reject("RemainderGrid", "!sourcePremise x y q || roundedUnits remainder",
                    "roundedUnits remainder")

    def test_identity_rounder_cannot_fool_counterexample(self):
        self.reject("RemainderGrid", "if value = 0 then some 0", "if True then some value")


@unittest.skipUnless(os.environ.get("FLOCQ_AUDIT_DIR"), "live tests require FLOCQ_AUDIT_DIR")
class RocqControls(unittest.TestCase):
    def reject(self, fixture, old, new):
        source = (ROOT / "scripts/fixtures" / (fixture + ".v")).read_text()
        wrong = mutated(source, old, new)
        flocq = Path(os.environ["FLOCQ_AUDIT_DIR"]).resolve()
        with tempfile.TemporaryDirectory(prefix="floatspec-rem-rocq-") as directory:
            path = Path(directory) / "Control.v"
            command = [core.configured_coqc(flocq), "-q", "-R", str(flocq / "src"),
                       "Flocq", str(path)]
            path.write_text(source)
            core.run(command)
            path.write_text(wrong)
            with self.assertRaisesRegex(RuntimeError, "expected to have type|Unable to unify|Not a discriminable"):
                core.run(command)

    def test_contract_requires_small_quotient_premise(self):
        self.reject("RemainderContracts", "      (Rabs (x / y) < /2 -> rnd (x / y) = 0%Z) ->\n", "")

    def test_grid_cannot_ignore_source_premise(self):
        self.reject("RemainderGrid", "orb (negb (sourcePremise x y q)) (same (roundedUnits remainder) remainder)",
                    "same (roundedUnits remainder) remainder")

    def test_identity_rounder_cannot_fool_counterexample(self):
        self.reject("RemainderGrid", "if Z.eqb value 0 then Some 0", "if true then Some value")


if __name__ == "__main__":
    unittest.main()
