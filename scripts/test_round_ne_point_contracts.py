"""Reject weakening the concrete nearest-even result or dropping its real premise."""

import os
from pathlib import Path
import tempfile
import unittest

import flocq_bridge as core


ROOT = Path(__file__).resolve().parents[1]


def replace_once(source, old, new):
    if source.count(old) != 1:
        raise ValueError("mutation must select exactly one expression")
    return source.replace(old, new)


class LeanControls(unittest.TestCase):
    def reject(self, old, new):
        source = (ROOT / "scripts/fixtures/RoundNEPointContracts.lean").read_text()
        wrong = replace_once(source, old, new)
        with tempfile.TemporaryDirectory(prefix="floatspec-ne-point-lean-") as directory:
            path = Path(directory) / "Control.lean"
            path.write_text(source)
            core.run(["lake", "env", "lean", str(path)])
            path.write_text(wrong)
            with self.assertRaisesRegex(RuntimeError, "Type mismatch|failed to synthesize"):
                core.run(["lake", "env", "lean", str(path)])

    def test_concrete_point_cannot_be_replaced_by_existence(self):
        self.reject("#check (round_NE_pt (beta := beta) (fexp := fexp) : ∀ x : Real,\n"
                    "  Rnd_NE_pt beta fexp x (roundR beta fexp (Znearest (fun t ↦ !decide (2 ∣ t))) x))",
                    "#check (round_NE_pt (beta := beta) (fexp := fexp) : ∀ x : Real,\n"
                    "  ∃ y : Real, Rnd_NE_pt beta fexp x y)")

    def test_existence_premise_cannot_be_dropped(self):
        self.reject("variable [Exists_NE beta fexp]", "-- Deliberately missing Exists_NE")


@unittest.skipUnless(os.environ.get("FLOCQ_AUDIT_DIR"), "live tests require FLOCQ_AUDIT_DIR")
class RocqControls(unittest.TestCase):
    def reject(self, old, new):
        source = (ROOT / "scripts/fixtures/RoundNEPointContracts.v").read_text()
        wrong = replace_once(source, old, new)
        flocq = Path(os.environ["FLOCQ_AUDIT_DIR"]).resolve()
        with tempfile.TemporaryDirectory(prefix="floatspec-ne-point-rocq-") as directory:
            path = Path(directory) / "Control.v"
            command = [core.configured_coqc(flocq), "-q", "-R", str(flocq / "src"),
                       "Flocq", str(path)]
            path.write_text(source)
            core.run(command)
            path.write_text(wrong)
            with self.assertRaisesRegex(RuntimeError, "expected to have type"):
                core.run(command)

    def test_concrete_point_cannot_be_replaced_by_existence(self):
        self.reject("    forall x : R, Rnd_NE_pt beta fexp x (round beta fexp ZnearestE x) :=",
                    "    forall x : R, exists y : R, Rnd_NE_pt beta fexp x y :=")

    def test_existence_premise_cannot_be_dropped(self):
        self.reject("Definition point_contract :\n"
                    "  forall (beta : radix) (fexp : Z -> Z), Valid_exp fexp -> Exists_NE beta fexp ->",
                    "Definition point_contract :\n"
                    "  forall (beta : radix) (fexp : Z -> Z), Valid_exp fexp ->")


if __name__ == "__main__":
    unittest.main()
