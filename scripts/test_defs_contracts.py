"""Reject silent changes to Flocq's basic definitions: float values and rounding relations."""

import os
from pathlib import Path
import tempfile
import unittest

import flocq_bridge as core


ROOT = Path(__file__).resolve().parents[1]
MUTATIONS = {
    "lean": [
        ("F2R f = (f.Fnum : ℝ) * bpow beta f.Fexp := rfl", "F2R f = (f.Fnum : ℝ) * bpow beta (-f.Fexp) := rfl"),
        ("round_pred P = (round_pred_total P ∧ round_pred_monotone P) := rfl",
         "round_pred P = (round_pred_total P ∨ round_pred_monotone P) := rfl"),
        ("P x f → P y g → x ≤ y → f ≤ g := rfl", "P x f → P y g → x ≤ y → g ≤ f := rfl"),
        ("(F f ∧ f ≤ x ∧ ∀ g, F g → g ≤ x → g ≤ f) := rfl", "(F f ∧ f ≤ x ∧ ∀ g, F g → g ≤ x → f ≤ g) := rfl"),
        ("((0 ≤ x → Rnd_DN_pt F x f) ∧ (x ≤ 0 → Rnd_UP_pt F x f)) := rfl",
         "((0 ≤ x → Rnd_UP_pt F x f) ∧ (x ≤ 0 → Rnd_DN_pt F x f)) := rfl"),
        ("(F f ∧ ∀ g, F g → |f - x| ≤ |g - x|) := rfl", "(F f ∧ ∀ g, F g → |f - x| < |g - x|) := rfl"),
        ("(P x f ∨ ∀ f2, Rnd_N_pt F x f2 → f2 = f)) := rfl", "(P x f ∧ ∀ f2, Rnd_N_pt F x f2 → f2 = f)) := rfl"),
        ("Rnd_N_pt F x f2 → |f2| ≤ |f|) := rfl", "Rnd_N_pt F x f2 → |f| ≤ |f2|) := rfl"),
    ],
    "v": [
        ("F2R f = IZR (Fnum f) * bpow beta (Fexp f)", "F2R f = IZR (Fnum f) * bpow beta (- Fexp f)"),
        ("round_pred P = (round_pred_total P /\\ round_pred_monotone P)",
         "round_pred P = (round_pred_total P \\/ round_pred_monotone P)"),
        ("P x f -> P y g -> x <= y -> f <= g", "P x f -> P y g -> x <= y -> g <= f"),
        ("(F f /\\ f <= x /\\ forall g, F g -> g <= x -> g <= f)", "(F f /\\ f <= x /\\ forall g, F g -> g <= x -> f <= g)"),
        ("((0 <= x -> Rnd_DN_pt F x f) /\\ (x <= 0 -> Rnd_UP_pt F x f))",
         "((0 <= x -> Rnd_UP_pt F x f) /\\ (x <= 0 -> Rnd_DN_pt F x f))"),
        ("(F f /\\ forall g, F g -> Rabs (f - x) <= Rabs (g - x))", "(F f /\\ forall g, F g -> Rabs (f - x) < Rabs (g - x))"),
        ("(P x f \\/ forall f2, Rnd_N_pt F x f2 -> f2 = f)", "(P x f /\\ forall f2, Rnd_N_pt F x f2 -> f2 = f)"),
        ("Rnd_N_pt F x f2 -> Rabs f2 <= Rabs f)", "Rnd_N_pt F x f2 -> Rabs f <= Rabs f2)"),
    ],
}


class DefsContracts(unittest.TestCase):
    def check_mutations(self, language):
        source = (ROOT / "scripts/fixtures" / f"DefsContracts.{language}").read_text()
        with tempfile.TemporaryDirectory(prefix="floatspec-defs-") as directory:
            path = Path(directory) / f"Control.{language}"
            if language == "lean":
                command = ["lake", "env", "lean", str(path)]
                diagnostic = r"[Tt]ype mismatch"
            else:
                flocq = Path(os.environ["FLOCQ_AUDIT_DIR"]).resolve()
                command = [core.configured_coqc(flocq), "-q", "-R", str(flocq / "src"),
                           "Flocq", str(path)]
                diagnostic = r"expected to have type|Unable to unify"
            path.write_text(source)
            core.run(command)
            for old, new in MUTATIONS[language]:
                with self.subTest(old=old):
                    self.assertEqual(source.count(old), 1)
                    path.write_text(source.replace(old, new))
                    with self.assertRaisesRegex(RuntimeError, diagnostic):
                        core.run(command)

    def test_lean_definitions(self):
        self.check_mutations("lean")

    @unittest.skipUnless(os.environ.get("FLOCQ_AUDIT_DIR"), "requires pinned built Rocq")
    def test_rocq_definitions(self):
        self.check_mutations("v")


if __name__ == "__main__":
    unittest.main()
