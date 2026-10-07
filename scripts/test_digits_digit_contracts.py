"""Reject silent changes to Digits.v's digit, scale and slice laws: indices, signs and premises."""

import os
from pathlib import Path
import tempfile
import unittest

import flocq_bridge as core


ROOT = Path(__file__).resolve().parents[1]
MUTATIONS = {
    "lean": [
        ("Zpos n < (2 : Int) ^ (digits2_Pnat n + 1)", "Zpos n < (2 : Int) ^ (digits2_Pnat n)"),
        ("Zdigit beta (-n) k = -Zdigit beta n k := Zdigit_opp", "Zdigit beta (-n) k = Zdigit beta n k := Zdigit_opp"),
        ("k < k' → 1 < beta →", "k ≤ k' → 1 < beta →"),
        ("Zdigit beta (n * Zpower beta k') k = Zdigit beta n (k - k')",
         "Zdigit beta (n * Zpower beta k') k = Zdigit beta n (k + k')"),
        ("Zsum_digit beta (Zdigit beta n) k = Int.tmod n (Zpower beta k)",
         "Zsum_digit beta (Zdigit beta n) k = Int.tdiv n (Zpower beta k)"),
        ("Zdigit beta (Zscale beta n k) k' = Zdigit beta n (k' - k)",
         "Zdigit beta (Zscale beta n k) k' = Zdigit beta n (k' + k)"),
        ("Zdigit beta n (k1 + k) := Zdigit_slice", "Zdigit beta n k := Zdigit_slice"),
        ("(min (k2 - k1') k2')", "(max (k2 - k1') k2')"),
    ],
    "v": [
        ("Zpos n < Zpower_nat 2 (S (digits2_Pnat n))", "Zpos n < Zpower_nat 2 (digits2_Pnat n)"),
        ("Zdigit beta (- n) k = - Zdigit beta n k", "Zdigit beta (- n) k = Zdigit beta n k"),
        ("forall (beta : radix) n k k', k < k' ->", "forall (beta : radix) n k k', k <= k' ->"),
        ("Zdigit beta (n * Zpower beta k') k = Zdigit beta n (k - k')",
         "Zdigit beta (n * Zpower beta k') k = Zdigit beta n (k + k')"),
        ("Zsum_digit beta (Zdigit beta n) k = Z.rem n", "Zsum_digit beta (Zdigit beta n) k = Z.quot n"),
        ("Zdigit beta (Zscale beta n k) k' = Zdigit beta n (k' - k)",
         "Zdigit beta (Zscale beta n k) k' = Zdigit beta n (k' + k)"),
        ("Zdigit beta n (k1 + k) := Zdigit_slice", "Zdigit beta n k := Zdigit_slice"),
        ("(Z.min (k2 - k1') k2')", "(Z.max (k2 - k1') k2')"),
    ],
}


class DigitsDigitContracts(unittest.TestCase):
    def check_mutations(self, language):
        source = (ROOT / "scripts/fixtures" / f"DigitsDigitContracts.{language}").read_text()
        with tempfile.TemporaryDirectory(prefix="floatspec-digits-digit-") as directory:
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

    def test_lean_digit_laws(self):
        self.check_mutations("lean")

    @unittest.skipUnless(os.environ.get("FLOCQ_AUDIT_DIR"), "requires pinned built Rocq")
    def test_rocq_digit_laws(self):
        self.check_mutations("v")


if __name__ == "__main__":
    unittest.main()
