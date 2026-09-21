"""Live typed-client mutations for the unindexed Pff arithmetic contracts."""

import os
from pathlib import Path
import tempfile
import unittest

import flocq_bridge as core


ROOT = Path(__file__).resolve().parents[1]


class ArithmeticContracts(unittest.TestCase):
    def reject(self, language, old, new):
        source = (ROOT / "scripts/fixtures" / f"PffBasicSourceContracts.{language}").read_text()
        self.assertEqual(source.count(old), 1)
        with tempfile.TemporaryDirectory(prefix="floatspec-pff-contracts-") as directory:
            path = Path(directory) / f"Control.{language}"
            if language == "lean":
                command = ["lake", "env", "lean", str(path)]
                diagnostic = "Type mismatch"
            else:
                flocq = Path(os.environ["FLOCQ_AUDIT_DIR"]).resolve()
                command = [core.configured_coqc(flocq), "-q", "-R", str(flocq / "src"),
                           "Flocq", str(path)]
                diagnostic = "expected to have type"
            path.write_text(source)
            core.run(command)
            path.write_text(source.replace(old, new))
            with self.assertRaisesRegex(RuntimeError, diagnostic):
                core.run(command)

    def test_lean_absolute_value_requires_positive_radix(self):
        self.reject("lean", "Source.Fabs_correct : ∀ (radix : Int), 0 < radix →",
                    "Source.Fabs_correct : ∀ (radix : Int),")

    def test_lean_negation_cannot_be_identity(self):
        self.reject("lean", "Source.FtoR radix (Source.Fopp x) = -Source.FtoR radix x)",
                    "Source.FtoR radix (Source.Fopp x) = Source.FtoR radix x)")

    def test_lean_addition_requires_positive_radix(self):
        self.reject("lean", "Source.Fplus_correct : ∀ (radix : Int), 0 < radix →",
                    "Source.Fplus_correct : ∀ (radix : Int),")

    def test_lean_subtraction_is_not_addition(self):
        self.reject("lean", "Source.FtoR radix (Source.Fminus radix x y) = Source.FtoR radix x -",
                    "Source.FtoR radix (Source.Fminus radix x y) = Source.FtoR radix x +")

    @unittest.skipUnless(os.environ.get("FLOCQ_AUDIT_DIR"), "live tests require FLOCQ_AUDIT_DIR")
    def test_rocq_absolute_value_requires_positive_radix(self):
        self.reject("v", "Pff.Fabs_correct : forall radix : Z, 0 < radix ->",
                    "Pff.Fabs_correct : forall radix : Z,")

    @unittest.skipUnless(os.environ.get("FLOCQ_AUDIT_DIR"), "live tests require FLOCQ_AUDIT_DIR")
    def test_rocq_negation_cannot_be_identity(self):
        self.reject("v", "Pff.FtoR radix (Pff.Fopp x) = (- Pff.FtoR radix x)%R)",
                    "Pff.FtoR radix (Pff.Fopp x) = (Pff.FtoR radix x)%R)")

    @unittest.skipUnless(os.environ.get("FLOCQ_AUDIT_DIR"), "live tests require FLOCQ_AUDIT_DIR")
    def test_rocq_addition_requires_positive_radix(self):
        self.reject("v", "Pff.Fplus_correct : forall radix : Z, 0 < radix ->",
                    "Pff.Fplus_correct : forall radix : Z,")

    @unittest.skipUnless(os.environ.get("FLOCQ_AUDIT_DIR"), "live tests require FLOCQ_AUDIT_DIR")
    def test_rocq_subtraction_is_not_addition(self):
        self.reject("v", "Pff.FtoR radix (Pff.Fminus radix x y) = (Pff.FtoR radix x -",
                    "Pff.FtoR radix (Pff.Fminus radix x y) = (Pff.FtoR radix x +")


if __name__ == "__main__":
    unittest.main()
