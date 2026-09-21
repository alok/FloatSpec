"""Exact source clients must reject weakened rounding premises in either prover."""

import os
from pathlib import Path
import tempfile
import unittest

import flocq_bridge as core


ROOT = Path(__file__).resolve().parents[1]
MUTATIONS = {
    "lean": [
        ("x < y → f ≤ g :=", "x ≤ y → f ≤ g :="),
        ("∀ F, F 0 → round_pred_monotone (Rnd_ZR_pt F)",
         "∀ F, round_pred_monotone (Rnd_ZR_pt F)"),
        ("Rnd_UP_pt F x u → x - d ≠ u - x →", "Rnd_UP_pt F x u →"),
        ("Rnd_DN_pt F x f → F x → f = x :=", "Rnd_DN_pt F x f → f = x :="),
    ],
    "v": [
        ("x < y -> f <= g :=", "x <= y -> f <= g :="),
        ("forall F, F 0 -> round_pred_monotone (Rnd_ZR_pt F)",
         "forall F, round_pred_monotone (Rnd_ZR_pt F)"),
        ("Rnd_UP_pt F x u -> x - d <> u - x ->", "Rnd_UP_pt F x u ->"),
        ("Rnd_DN_pt F x f -> F x -> f = x :=", "Rnd_DN_pt F x f -> f = x :="),
    ],
}


class RoundPredContracts(unittest.TestCase):
    def check_mutations(self, language):
        source = (ROOT / "scripts/fixtures" / f"RoundPredSourceContracts.{language}").read_text()
        with tempfile.TemporaryDirectory(prefix="floatspec-round-pred-contracts-") as directory:
            path = Path(directory) / f"Control.{language}"
            if language == "lean":
                command = ["lake", "env", "lean", str(path)]
                diagnostic = r"[Tt]ype mismatch"
            else:
                flocq = Path(os.environ["FLOCQ_AUDIT_DIR"]).resolve()
                command = [core.configured_coqc(flocq), "-q", "-R", str(flocq / "src"),
                           "Flocq", str(path)]
                diagnostic = r"expected to have type"
            # Establish a valid control first. A missing compiler/import is an
            # error, not successful rejection of a mutant.
            path.write_text(source)
            core.run(command)
            for old, new in MUTATIONS[language]:
                with self.subTest(old=old):
                    self.assertEqual(source.count(old), 1)
                    path.write_text(source.replace(old, new))
                    with self.assertRaisesRegex(RuntimeError, diagnostic):
                        core.run(command)

    def test_lean_exact_rounding_contracts(self):
        self.check_mutations("lean")

    @unittest.skipUnless(os.environ.get("FLOCQ_AUDIT_DIR"), "requires pinned built Rocq")
    def test_rocq_exact_rounding_contracts(self):
        self.check_mutations("v")


if __name__ == "__main__":
    unittest.main()
