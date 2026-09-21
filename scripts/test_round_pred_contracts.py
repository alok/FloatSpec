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

TIE_MUTATIONS = {
    "lean": [
        ("∀ F P, Rnd_NG_pt_unique_prop F P → ∀ x f g,", "∀ F P x f g,"),
        ("∀ F, F 0 → ∀ x f g, Rnd_NA_pt", "∀ F x f g, Rnd_NA_pt"),
        ("∀ F, F 0 → ∀ x f g, Rnd_N0_pt", "∀ F x f g, Rnd_N0_pt"),
        ("∀ F1 F2 a b, F1 a →", "∀ F1 F2 a b,"),
        ("round_pred_total (Rnd_NG_pt F P) := satisfies_any_imp_NG",
         "round_pred (Rnd_NG_pt F P) := satisfies_any_imp_NG"),
        ("Rnd_NA_pt F x f ↔ Rnd_NG_pt F (fun x f ↦ |x| ≤ |f|)",
         "Rnd_NA_pt F x f ↔ Rnd_NG_pt F (fun x f ↦ |f| ≤ |x|)"),
    ],
    "v": [
        ("Rnd_NG_pt_unique_prop F P -> forall x f g,", "forall x f g,"),
        ("forall F, F 0 -> forall x f g,\n  Rnd_NA_pt", "forall F x f g,\n  Rnd_NA_pt"),
        ("forall F, F 0 -> forall x f g,\n  Rnd_N0_pt", "forall F x f g,\n  Rnd_N0_pt"),
        ("F1 a -> (forall x, a <= x <= b", "(forall x, a <= x <= b"),
        ("round_pred_total (Rnd_NG_pt F P) := satisfies_any_imp_NG",
         "round_pred (Rnd_NG_pt F P) := satisfies_any_imp_NG"),
        ("Rnd_NA_pt F x f <-> Rnd_NG_pt F (fun x f => Rabs x <= Rabs f)",
         "Rnd_NA_pt F x f <-> Rnd_NG_pt F (fun x f => Rabs f <= Rabs x)"),
    ],
}


class RoundPredContracts(unittest.TestCase):
    def check_mutations(self, language, fixture="RoundPredSourceContracts", mutations=MUTATIONS):
        source = (ROOT / "scripts/fixtures" / f"{fixture}.{language}").read_text()
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
            for old, new in mutations[language]:
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

    def test_lean_tie_and_totality_contracts(self):
        self.check_mutations("lean", "RoundPredTieContracts", TIE_MUTATIONS)

    @unittest.skipUnless(os.environ.get("FLOCQ_AUDIT_DIR"), "requires pinned built Rocq")
    def test_rocq_tie_and_totality_contracts(self):
        self.check_mutations("v", "RoundPredTieContracts", TIE_MUTATIONS)


if __name__ == "__main__":
    unittest.main()
