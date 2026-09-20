"""Live negative controls for the noncomputable real-rounding fixtures.

These run the two proof checkers, not native execution of mathematical reals.
Each control first checks the original fixture, rejects nearest-even replaced
by downward rounding, then positively checks the changed result of that mutant.
"""
import os
from pathlib import Path
import tempfile
import unittest

import flocq_bridge as core

ROOT = Path(__file__).resolve().parents[1]


class LeanControls(unittest.TestCase):
    def test_downward_mutation_has_a_different_positive_half_result(self):
        source = (ROOT / "FloatSpec/Test/PffRoundingSource.lean").read_text()
        source = source.split("/-- The even lower mantissa wins the negative halfway tie.")[0]
        source += "\nend FloatSpec.Test.PffRoundingSource\n"
        observed = "Source.RND_EvenClosest bound 3 2 r"
        self.assertEqual(source.count(observed), 1)
        wrong = source.replace(observed, "Source.RND_Min bound 3 2 r")
        expected = "[⟨1, 0⟩, ⟨2, 0⟩, ⟨2, 0⟩]"
        self.assertEqual(wrong.count(expected), 1)
        corrected = wrong.replace(expected, "[⟨1, 0⟩, ⟨2, 0⟩, ⟨1, 0⟩]")
        with tempfile.TemporaryDirectory(prefix="floatspec-pff-rounding-lean-control-") as directory:
            path = Path(directory) / "Control.lean"
            path.write_text(source)
            core.run(["lake", "env", "lean", str(path)])
            path.write_text(wrong)
            with self.assertRaisesRegex(RuntimeError, "unsolved goals"):
                core.run(["lake", "env", "lean", str(path)])
            path.write_text(corrected)
            core.run(["lake", "env", "lean", str(path)])


@unittest.skipUnless(os.environ.get("FLOCQ_AUDIT_DIR"), "live tests require FLOCQ_AUDIT_DIR")
class RocqControls(unittest.TestCase):
    def test_downward_mutation_has_a_different_positive_half_result(self):
        source = (ROOT / "scripts/fixtures/PffRoundingSource.v").read_text()
        source = source.split("Example negative_half :")[0]
        source += """
Example positive_half : row (3/2) =
  [Pff.Float 1 0; Pff.Float 2 0; Pff.Float 2 0].
Proof. rounding_literal. Qed.
"""
        observed = "Pff.RND_EvenClosest bound 3 2 r"
        self.assertEqual(source.count(observed), 1)
        wrong = source.replace(observed, "Pff.RND_Min bound 3 2 r")
        expected = "[Pff.Float 1 0; Pff.Float 2 0; Pff.Float 2 0]"
        self.assertEqual(wrong.count(expected), 1)
        corrected = wrong.replace(expected, "[Pff.Float 1 0; Pff.Float 2 0; Pff.Float 1 0]")
        flocq = Path(os.environ["FLOCQ_AUDIT_DIR"]).resolve()
        with tempfile.TemporaryDirectory(prefix="floatspec-pff-rounding-rocq-control-") as directory:
            path = Path(directory) / "Control.v"
            command = [core.configured_coqc(flocq), "-q", "-R", str(flocq / "src"), "Flocq", str(path)]
            path.write_text(source)
            core.run(command)
            path.write_text(wrong)
            with self.assertRaisesRegex(RuntimeError, "Unable to unify"):
                core.run(command)
            path.write_text(corrected)
            core.run(command)


if __name__ == "__main__":
    unittest.main()
