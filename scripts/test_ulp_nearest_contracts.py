"""Reject choice-erased nearest contracts and a deliberately wrong tie policy."""

import os
from pathlib import Path
import tempfile
import unittest

import flocq_bridge as core


ROOT = Path(__file__).resolve().parents[1]


def replace_section(source, start, stop, expected, replacement):
    begin, end = source.index(start), source.index(stop, source.index(start))
    section = source[begin:end]
    if section.count(expected) != 1:
        raise ValueError("mutation must identify exactly one selected expression")
    return source[:begin] + section.replace(expected, replacement) + source[end:]


class LeanControls(unittest.TestCase):
    def reject(self, wrong):
        source = (ROOT / "scripts/fixtures/UlpNearestChoiceContracts.lean").read_text()
        self.assertNotEqual(source, wrong)
        with tempfile.TemporaryDirectory(prefix="floatspec-nearest-lean-mutation-") as directory:
            path = Path(directory) / "Control.lean"
            path.write_text(source)
            core.run(["lake", "env", "lean", str(path)])
            path.write_text(wrong)
            with self.assertRaisesRegex(RuntimeError, "Type mismatch|unsolved goals"):
                core.run(["lake", "env", "lean", str(path)])

    def test_second_choice_cannot_be_erased_from_contract(self):
        source = (ROOT / "scripts/fixtures/UlpNearestChoiceContracts.lean").read_text()
        self.reject(replace_section(source, "theorem nearest_choices_agree_away_from_ties",
            "#print axioms nearest_choices_agree_away_from_ties",
            "= roundR beta fexp (Znearest choice₂) x :=",
            "= roundR beta fexp (Znearest choice₁) x :="))

    def test_wrong_midpoint_policy_is_rejected(self):
        source = (ROOT / "scripts/fixtures/UlpNearestChoiceContracts.lean").read_text()
        self.reject(replace_section(source, "theorem tie_choices_differ",
            "#print axioms tie_choices_differ",
            "Znearest (fun _ => true)", "Znearest (fun _ => false)"))


@unittest.skipUnless(os.environ.get("FLOCQ_AUDIT_DIR"), "live tests require FLOCQ_AUDIT_DIR")
class RocqControls(unittest.TestCase):
    def reject(self, wrong):
        source = (ROOT / "scripts/fixtures/UlpNearestChoiceContracts.v").read_text()
        self.assertNotEqual(source, wrong)
        flocq = Path(os.environ["FLOCQ_AUDIT_DIR"]).resolve()
        with tempfile.TemporaryDirectory(prefix="floatspec-nearest-rocq-mutation-") as directory:
            path = Path(directory) / "Control.v"
            command = [core.configured_coqc(flocq), "-q", "-R", str(flocq / "src"), "Flocq", str(path)]
            path.write_text(source)
            core.run(command)
            path.write_text(wrong)
            with self.assertRaisesRegex(RuntimeError, "expected to have type|not a valid ring equation"):
                core.run(command)

    def test_second_choice_cannot_be_erased_from_contract(self):
        source = (ROOT / "scripts/fixtures/UlpNearestChoiceContracts.v").read_text()
        self.reject(replace_section(source, "Definition round_N_eq_ties_client",
            "Print Assumptions round_N_eq_ties_client",
            "= round beta fexp (Znearest c2) x :=",
            "= round beta fexp (Znearest c1) x :="))

    def test_wrong_midpoint_policy_is_rejected(self):
        source = (ROOT / "scripts/fixtures/UlpNearestChoiceContracts.v").read_text()
        self.reject(replace_section(source, "Example tie_choices_differ",
            "Print Assumptions tie_choices_differ",
            "Znearest (fun _ => true)", "Znearest (fun _ => false)"))


if __name__ == "__main__":
    unittest.main()
