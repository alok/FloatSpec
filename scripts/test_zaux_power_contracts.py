"""Paired typed clients reject weakened integer-power/radix contracts."""

import os
from pathlib import Path
import tempfile
import unittest

import flocq_bridge as core


ROOT = Path(__file__).resolve().parents[1]
MUTATIONS = {
    "lean": [
        ("e₁ e₂ : Int), 0 ≤ e₂ → e₁ < e₂ →", "e₁ e₂ : Int), e₁ < e₂ →"),
        ("n k₁ k₂ : Int, 0 ≤ k₁ → 0 ≤ k₂ →", "n k₁ k₂ : Int, 0 ≤ k₂ →"),
        ("(h : decide (2 ≤ value) = true)", "(h : decide (0 ≤ value) = true)"),
        ("Zpower 2 (-2) = 0 ∧", "Zpower 2 (-2) = 4 ∧"),
    ],
    "v": [
        ("e1 e2, 0 <= e2 -> e1 < e2 ->", "e1 e2, e1 < e2 ->"),
        ("n k1 k2, 0 <= k1 -> 0 <= k2 ->", "n k1 k2, 0 <= k2 ->"),
        ("forall value, Z.leb 2 value = true", "forall value, Z.leb 0 value = true"),
        ("Zpower 2 (-2) = 0 /\\", "Zpower 2 (-2) = 4 /\\"),
    ],
}


class PowerContracts(unittest.TestCase):
    def check_mutations(self, language):
        source = (ROOT / "scripts/fixtures" / f"ZauxPowerRadixContracts.{language}").read_text()
        with tempfile.TemporaryDirectory(prefix="floatspec-power-contracts-") as directory:
            path = Path(directory) / f"Control.{language}"
            if language == "lean":
                command = ["lake", "env", "lean", str(path)]
            else:
                flocq = Path(os.environ["FLOCQ_AUDIT_DIR"]).resolve()
                command = [core.configured_coqc(flocq), "-q", "-R", str(flocq / "src"),
                           "Flocq", str(path)]
            path.write_text(source)
            core.run(command)
            for old, new in MUTATIONS[language]:
                with self.subTest(old=old):
                    self.assertEqual(source.count(old), 1)
                    path.write_text(source.replace(old, new))
                    # Baseline compiles first. A theorem type mismatch or false
                    # kernel goal must fail; timeout/import errors are not passes.
                    diagnostic = (r"[Tt]ype mismatch|Tactic `decide` proved that the proposition"
                                  if language == "lean" else
                                  r"expected to have type|Attempt to save an incomplete proof")
                    with self.assertRaisesRegex(RuntimeError, diagnostic):
                        core.run(command)

    def test_lean_premises_and_counterexamples(self):
        self.check_mutations("lean")

    @unittest.skipUnless(os.environ.get("FLOCQ_AUDIT_DIR"), "live tests require FLOCQ_AUDIT_DIR")
    def test_rocq_premises_and_counterexamples(self):
        self.check_mutations("v")


if __name__ == "__main__":
    unittest.main()
