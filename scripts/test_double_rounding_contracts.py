"""Deliberate body/premise drift must break the paired double-rounding guards."""
import os
from pathlib import Path
import tempfile
import unittest

import flocq_bridge as core

ROOT = Path(__file__).resolve().parents[1]


class LeanControls(unittest.TestCase):
    def check_rejection(self, source, mutated, diagnostic):
        self.assertNotEqual(source, mutated)
        with tempfile.TemporaryDirectory(prefix="floatspec-double-contract-lean-") as directory:
            path = Path(directory) / "Control.lean"
            path.write_text(source)
            core.run(["lake", "env", "lean", str(path)])
            path.write_text(mutated)
            with self.assertRaisesRegex(RuntimeError, diagnostic):
                core.run(["lake", "env", "lean", str(path)])

    def test_radix_four_hypothesis_off_by_one_is_rejected(self):
        source = (ROOT / "FloatSpec/Test/DoubleRoundingContracts.lean").read_text()
        start = source.index("theorem sqrt_ge4_hyp_contract")
        stop = source.index("theorem div_hyp_contract", start)
        section = source[start:stop]
        expected = "fexp2 ex + ex ≤ 2 * fexp1 ex - 1"
        self.assertEqual(section.count(expected), 1)
        wrong = section.replace(expected, "fexp2 ex + ex ≤ 2 * fexp1 ex - 2")
        self.check_rejection(source, source[:start] + wrong + source[stop:], "Type mismatch|type mismatch")

    def test_unavailable_extra_valid_exp_premises_are_rejected(self):
        source = (ROOT / "FloatSpec/Test/DoubleRoundingContracts.lean").read_text()
        expected = "round_round_mult_aux beta fexp1 fexp2 ValidRadix.valid h x y hx hy"
        self.assertEqual(source.count(expected), 1)
        wrong = source.replace(expected,
            "round_round_mult_aux_from_valid_exp_payload beta fexp1 fexp2 ValidRadix.valid h x y hx hy")
        self.check_rejection(source, wrong, "failed to synthesize[\\s\\S]*Valid_exp")


@unittest.skipUnless(os.environ.get("FLOCQ_AUDIT_DIR"), "live tests require FLOCQ_AUDIT_DIR")
class RocqControls(unittest.TestCase):
    def test_radix_four_hypothesis_off_by_one_is_rejected(self):
        source = (ROOT / "scripts/fixtures/DoubleRoundingContracts.v").read_text()
        start = source.index("Example sqrt_ge4_hyp_contract")
        stop = source.index("Example div_hyp_contract", start)
        section = source[start:stop]
        expected = "fexp2 ex + ex <= 2 * fexp1 ex - 1"
        self.assertEqual(section.count(expected), 1)
        wrong = source[:start] + section.replace(expected,
            "fexp2 ex + ex <= 2 * fexp1 ex - 2") + source[stop:]
        flocq = Path(os.environ["FLOCQ_AUDIT_DIR"]).resolve()
        with tempfile.TemporaryDirectory(prefix="floatspec-double-contract-rocq-") as directory:
            path = Path(directory) / "Control.v"
            command = [core.configured_coqc(flocq), "-q", "-R", str(flocq / "src"), "Flocq", str(path)]
            path.write_text(source)
            core.run(command)
            path.write_text(wrong)
            with self.assertRaisesRegex(RuntimeError, "Unable to unify"):
                core.run(command)


if __name__ == "__main__":
    unittest.main()
