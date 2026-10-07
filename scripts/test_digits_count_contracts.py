"""Reject silent changes to Digits.v's digit-count laws: bounds, offsets and premises."""

import os
from pathlib import Path
import tempfile
import unittest

import flocq_bridge as core


ROOT = Path(__file__).resolve().parents[1]
MUTATIONS = {
    "lean": [
        ("|n| < Zpower beta (Zdigits beta n) := Zdigits_correct",
         "|n| < Zpower beta (Zdigits beta n - 1) := Zdigits_correct"),
        ("Zdigits beta |n| = Zdigits beta n := Zdigits_abs", "Zdigits beta |n| = Zdigits beta n + 1 := Zdigits_abs"),
        ("∀ beta n : Int, n ≠ 0 → 0 < Zdigits beta n", "∀ beta n : Int, 0 < Zdigits beta n"),
        ("Zdigits beta (m * Zpower beta e) = Zdigits beta m + e",
         "Zdigits beta (m * Zpower beta e) = Zdigits beta m * e"),
        ("Zdigits beta (Zpower beta e) = e + 1", "Zdigits beta (Zpower beta e) = e"),
        ("∀ beta x y : Int, 0 ≤ x → x ≤ y → 1 < beta →", "∀ beta x y : Int, x ≤ y → 1 < beta →"),
        ("Zdigits beta x + Zdigits beta y - 1 ≤ Zdigits beta (x * y)",
         "Zdigits beta x + Zdigits beta y ≤ Zdigits beta (x * y)"),
        ("((digits2_Pnat m + 1 : Nat) : Int) = Zdigits 2 (Zpos m)",
         "((digits2_Pnat m : Nat) : Int) = Zdigits 2 (Zpos m)"),
    ],
    "v": [
        ("Z.abs n < Zpower beta (Zdigits beta n) := Zdigits_correct",
         "Z.abs n < Zpower beta (Zdigits beta n - 1) := Zdigits_correct"),
        ("Zdigits beta (Z.abs n) = Zdigits beta n := Zdigits_abs",
         "Zdigits beta (Z.abs n) = Zdigits beta n + 1 := Zdigits_abs"),
        ("forall (beta : radix) n, n <> Z0 -> 0 < Zdigits beta n", "forall (beta : radix) n, 0 < Zdigits beta n"),
        ("Zdigits beta (m * Zpower beta e) = Zdigits beta m + e",
         "Zdigits beta (m * Zpower beta e) = Zdigits beta m * e"),
        ("Zdigits beta (Zpower beta e) = e + 1", "Zdigits beta (Zpower beta e) = e"),
        ("forall (beta : radix) x y, 0 <= x -> x <= y ->", "forall (beta : radix) x y, x <= y ->"),
        ("Zdigits beta x + Zdigits beta y - 1 <= Zdigits beta (x * y)",
         "Zdigits beta x + Zdigits beta y <= Zdigits beta (x * y)"),
        ("Z.of_nat (S (digits2_Pnat m)) = Zdigits radix2 (Zpos m)",
         "Z.of_nat (digits2_Pnat m) = Zdigits radix2 (Zpos m)"),
    ],
}


class DigitsCountContracts(unittest.TestCase):
    def check_mutations(self, language):
        source = (ROOT / "scripts/fixtures" / f"DigitsCountContracts.{language}").read_text()
        with tempfile.TemporaryDirectory(prefix="floatspec-digits-count-") as directory:
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

    def test_lean_count_laws(self):
        self.check_mutations("lean")

    @unittest.skipUnless(os.environ.get("FLOCQ_AUDIT_DIR"), "requires pinned built Rocq")
    def test_rocq_count_laws(self):
        self.check_mutations("v")


if __name__ == "__main__":
    unittest.main()
