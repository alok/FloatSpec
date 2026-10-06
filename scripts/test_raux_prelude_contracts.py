"""Reject silent changes to the premises and directions of Raux's real-number prelude."""

import os
from pathlib import Path
import tempfile
import unittest

import flocq_bridge as core


ROOT = Path(__file__).resolve().parents[1]
MUTATIONS = {
    "lean": [
        ("∀ x y : ℝ, 0 ≤ y → y ≤ 2 * x → |x - y| ≤ x", "∀ x y : ℝ, y ≤ 2 * x → |x - y| ≤ x"),
        ("∀ r1 r2 r3 r4 : ℝ, 0 ≤ r1 → 0 ≤ r3 →", "∀ r1 r2 r3 r4 : ℝ, 0 ≤ r3 →"),
        ("∀ r1 r2 r3 : ℝ, r1 ≠ 0 → r2 ≠ r3 →", "∀ r1 r2 r3 : ℝ, r2 ≠ r3 →"),
        ("∀ r r1 r2 : ℝ, 0 ≤ r → min r1 r2 * r", "∀ r r1 r2 : ℝ, min r1 r2 * r"),
        ("∀ x y : ℝ, 0 < x → x < y → y⁻¹ < x⁻¹", "∀ x y : ℝ, x < y → y⁻¹ < x⁻¹"),
        ("∀ x : ℝ, x ≤ 0 → Real.sqrt x = 0", "∀ x : ℝ, 0 ≤ x → Real.sqrt x = 0"),
        ("∀ x y : ℝ, -y < x ∧ x < y → |x| < y", "∀ x y : ℝ, -y ≤ x ∧ x ≤ y → |x| < y"),
        ("∀ m n : Int, (m : ℝ) ≠ n → m ≠ n", "∀ m n : Int, m ≠ n → (m : ℝ) ≠ n"),
    ],
    "v": [
        ("forall x y, 0 <= y -> y <= 2 * x -> Rabs (x - y) <= x :=",
         "forall x y, y <= 2 * x -> Rabs (x - y) <= x :="),
        ("forall r1 r2 r3 r4, 0 <= r1 -> 0 <= r3 ->", "forall r1 r2 r3 r4, 0 <= r3 ->"),
        ("forall r1 r2 r3, r1 <> 0 -> r2 <> r3 ->", "forall r1 r2 r3, r2 <> r3 ->"),
        ("forall r r1 r2, 0 <= r -> Rmin r1 r2 * r", "forall r r1 r2, Rmin r1 r2 * r"),
        ("forall x y, 0 < x -> x < y -> / y < / x :=", "forall x y, x < y -> / y < / x :="),
        ("forall x, x <= 0 -> sqrt x = 0", "forall x, 0 <= x -> sqrt x = 0"),
        ("forall x y, - y < x < y -> Rabs x < y", "forall x y, - y <= x <= y -> Rabs x < y"),
        ("forall m n, IZR m <> IZR n -> m <> n", "forall m n, m <> n -> IZR m <> IZR n"),
    ],
}


class RauxPreludeContracts(unittest.TestCase):
    def check_mutations(self, language):
        source = (ROOT / "scripts/fixtures" / f"RauxPreludeContracts.{language}").read_text()
        with tempfile.TemporaryDirectory(prefix="floatspec-raux-prelude-") as directory:
            path = Path(directory) / f"Control.{language}"
            if language == "lean":
                command = ["lake", "env", "lean", str(path)]
                diagnostic = r"[Tt]ype mismatch"
            else:
                flocq = Path(os.environ["FLOCQ_AUDIT_DIR"]).resolve()
                command = [core.configured_coqc(flocq), "-q", "-R", str(flocq / "src"),
                           "Flocq", str(path)]
                diagnostic = r"expected to have type"
            path.write_text(source)
            core.run(command)
            for old, new in MUTATIONS[language]:
                with self.subTest(old=old):
                    self.assertEqual(source.count(old), 1)
                    path.write_text(source.replace(old, new))
                    with self.assertRaisesRegex(RuntimeError, diagnostic):
                        core.run(command)

    def test_lean_premises_and_directions(self):
        self.check_mutations("lean")

    @unittest.skipUnless(os.environ.get("FLOCQ_AUDIT_DIR"), "requires pinned built Rocq")
    def test_rocq_premises_and_directions(self):
        self.check_mutations("v")


if __name__ == "__main__":
    unittest.main()
