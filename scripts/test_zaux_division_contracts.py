"""Reject silent changes in division mode, sign premises and signed boundaries."""

import os
from pathlib import Path
import tempfile
import unittest

import flocq_bridge as core


ROOT = Path(__file__).resolve().parents[1]
MUTATIONS = {
    "lean": [
        ("∀ a b : Int, a.tmod b = a - a.tdiv b * b", "∀ a b : Int, a % b = a - a.tdiv b * b"),
        ("∀ a b c : Int, 0 ≤ a * b →", "∀ a b c : Int,"),
        ("(7 : Int) / (-3) = -2", "(7 : Int) / (-3) = -3"),
    ],
    "v": [
        ("Z.rem a b = a - Z.quot a b * b :=", "Z.modulo a b = a - Z.quot a b * b :="),
        ("forall a b c, 0 <= a*b ->", "forall a b c,"),
        ("7 / (-3) = -3", "7 / (-3) = -2"),
    ],
}


class DivisionContracts(unittest.TestCase):
    def check_mutations(self, language):
        source = (ROOT / "scripts/fixtures" / f"ZauxDivisionContracts.{language}").read_text()
        with tempfile.TemporaryDirectory(prefix="floatspec-division-contracts-") as directory:
            path = Path(directory) / f"Control.{language}"
            if language == "lean":
                command = ["lake", "env", "lean", str(path)]
                diagnostic = r"[Tt]ype mismatch|Tactic `decide` proved that the proposition"
            else:
                flocq = Path(os.environ["FLOCQ_AUDIT_DIR"]).resolve()
                command = [core.configured_coqc(flocq), "-q", "-R", str(flocq / "src"),
                           "Flocq", str(path)]
                diagnostic = r"expected to have type|Attempt to save an incomplete proof"
            path.write_text(source)
            core.run(command)
            for old, new in MUTATIONS[language]:
                with self.subTest(old=old):
                    self.assertEqual(source.count(old), 1)
                    path.write_text(source.replace(old, new))
                    with self.assertRaisesRegex(RuntimeError, diagnostic):
                        core.run(command)

    def test_lean_source_domains_and_modes(self):
        self.check_mutations("lean")

    @unittest.skipUnless(os.environ.get("FLOCQ_AUDIT_DIR"), "requires pinned built Rocq")
    def test_rocq_source_domains_and_modes(self):
        self.check_mutations("v")


if __name__ == "__main__":
    unittest.main()
