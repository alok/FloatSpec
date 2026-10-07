"""Reject silent changes to Raux's radix powers: premises, monotonicity, inverses and shapes."""

import os
from pathlib import Path
import tempfile
import unittest

import flocq_bridge as core


ROOT = Path(__file__).resolve().parents[1]
MUTATIONS = {
    "lean": [
        ("∀ beta e1 e2 : Int, 1 < beta → e1 ≤ e2 → bpow beta e1 ≤ bpow beta e2",
         "∀ beta e1 e2 : Int, e1 ≤ e2 → bpow beta e1 ≤ bpow beta e2"),
        ("1 < beta → e1 < e2 → bpow beta e1 < bpow beta e2", "1 < beta → e1 ≤ e2 → bpow beta e1 < bpow beta e2"),
        ("bpow beta (-e) = (bpow beta e)⁻¹ := bpow_opp", "bpow beta (-e) = -bpow beta e := bpow_opp"),
        ("bpow beta (e + 1) = (beta : ℝ) * bpow beta e", "bpow beta (e + 1) = bpow beta e + 1"),
        ("bpow beta (e1 + e2) = bpow beta e1 * bpow beta e2", "bpow beta (e1 + e2) = bpow beta e1 + bpow beta e2"),
        ("Real.sqrt (bpow beta (2 * e)) = bpow beta e", "Real.sqrt (bpow beta (2 * e)) = bpow beta (2 * e)"),
        ("bpow beta (e / 2) ≤ Real.sqrt (bpow beta e)", "Real.sqrt (bpow beta e) ≤ bpow beta (e / 2)"),
        ("Real.exp ((e : ℝ) * Real.log (beta : ℝ)) := bpow_exp", "Real.exp ((e : ℝ) + Real.log (beta : ℝ)) := bpow_exp"),
    ],
    "v": [
        ("forall (r : radix) e1 e2, (e1 <= e2)%Z -> bpow r e1 <= bpow r e2",
         "forall (r : radix) e1 e2, (e2 <= e1)%Z -> bpow r e1 <= bpow r e2"),
        ("(e1 < e2)%Z -> bpow r e1 < bpow r e2 := bpow_lt", "(e1 <= e2)%Z -> bpow r e1 < bpow r e2 := bpow_lt"),
        ("bpow r (- e) = / bpow r e := bpow_opp", "bpow r (- e) = - bpow r e := bpow_opp"),
        ("bpow r (e + 1) = IZR r * bpow r e", "bpow r (e + 1) = bpow r e + 1"),
        ("bpow r (e1 + e2) = bpow r e1 * bpow r e2", "bpow r (e1 + e2) = bpow r e1 + bpow r e2"),
        ("sqrt (bpow r (2 * e)) = bpow r e", "sqrt (bpow r (2 * e)) = bpow r (2 * e)"),
        ("bpow r (e / 2) <= sqrt (bpow r e)", "sqrt (bpow r e) <= bpow r (e / 2)"),
        ("exp (IZR e * ln (IZR r)) := bpow_exp", "exp (IZR e + ln (IZR r)) := bpow_exp"),
    ],
}


class RauxPowContracts(unittest.TestCase):
    def check_mutations(self, language):
        source = (ROOT / "scripts/fixtures" / f"RauxPowContracts.{language}").read_text()
        with tempfile.TemporaryDirectory(prefix="floatspec-raux-pow-") as directory:
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

    def test_lean_radix_powers(self):
        self.check_mutations("lean")

    @unittest.skipUnless(os.environ.get("FLOCQ_AUDIT_DIR"), "requires pinned built Rocq")
    def test_rocq_radix_powers(self):
        self.check_mutations("v")


if __name__ == "__main__":
    unittest.main()
