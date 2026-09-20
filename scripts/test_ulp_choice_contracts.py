"""Reject zero-spacing body drift and lost exponent-validity premises."""
import os
from pathlib import Path
import tempfile
import unittest

import flocq_bridge as core

ROOT = Path(__file__).resolve().parents[1]


class LeanControls(unittest.TestCase):
    def check_rejection(self, source, wrong, diagnostic):
        self.assertNotEqual(source, wrong)
        with tempfile.TemporaryDirectory(prefix="floatspec-ulp-lean-control-") as directory:
            path = Path(directory) / "Control.lean"
            path.write_text(source)
            core.run(["lake", "env", "lean", str(path)])
            path.write_text(wrong)
            with self.assertRaisesRegex(RuntimeError, diagnostic):
                core.run(["lake", "env", "lean", str(path)])

    def test_erased_zero_spacing_is_rejected(self):
        source = (ROOT / "FloatSpec/Test/UlpSourceChoice.lean").read_text()
        start = source.index("theorem ulp_body")
        stop = source.index("theorem pred_pos_body", start)
        section = source[start:stop]
        expected = "| some n => (beta : Real) ^ fexp n"
        self.assertEqual(section.count(expected), 1)
        wrong = source[:start] + section.replace(expected, "| some _ => 0") + source[stop:]
        self.check_rejection(source, wrong, "Type mismatch|Tactic.*rfl.*failed")

    def test_preservation_proof_requires_valid_exponent(self):
        source = (ROOT / "FloatSpec/Test/UlpSourceChoice.lean").read_text()
        start = source.index("theorem valid_exp_ulp_preserved")
        stop = source.index("theorem negligible_choice_contract", start)
        section = source[start:stop]
        expected = "[Valid_exp fexp]"
        self.assertEqual(section.count(expected), 1)
        wrong = source[:start] + section.replace(expected, "") + source[stop:]
        self.check_rejection(source, wrong,
                             "failed to synthesize[\\s\\S]*Valid_exp")


@unittest.skipUnless(os.environ.get("FLOCQ_AUDIT_DIR"), "live tests require FLOCQ_AUDIT_DIR")
class RocqControls(unittest.TestCase):
    def test_erased_zero_spacing_is_rejected(self):
        source = (ROOT / "scripts/fixtures/UlpSourceChoice.v").read_text()
        expected = "Some n => bpow beta (fexp n)"
        self.assertEqual(source.count(expected), 1)
        wrong = source.replace(expected, "Some _ => 0")
        flocq = Path(os.environ["FLOCQ_AUDIT_DIR"]).resolve()
        with tempfile.TemporaryDirectory(prefix="floatspec-ulp-rocq-control-") as directory:
            path = Path(directory) / "Control.v"
            command = [core.configured_coqc(flocq), "-q", "-R", str(flocq / "src"), "Flocq", str(path)]
            path.write_text(source)
            core.run(command)
            path.write_text(wrong)
            with self.assertRaisesRegex(RuntimeError, "Unable to unify"):
                core.run(command)


if __name__ == "__main__":
    unittest.main()
