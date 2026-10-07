"""Reject silent changes to Raux's magnitude: its witness, bounds, premises and shapes."""

import os
from pathlib import Path
import tempfile
import unittest

import flocq_bridge as core


ROOT = Path(__file__).resolve().parents[1]
MUTATIONS = {
    "lean": [
        ("mag beta x = Zfloor (Real.log |x| / Real.log (beta : ℝ)) + 1 := rfl",
         "mag beta x = Zceil (Real.log |x| / Real.log (beta : ℝ)) + 1 := rfl"),
        ("bpow beta (e - 1) ≤ |x| ∧ |x| < bpow beta e → mag beta x = e := mag_unique",
         "bpow beta (e - 1) ≤ |x| ∧ |x| ≤ bpow beta e → mag beta x = e := mag_unique"),
        ("1 < beta → 0 < x → x ≤ y → mag beta x ≤ mag beta y := mag_le",
         "1 < beta → x ≤ y → mag beta x ≤ mag beta y := mag_le"),
        ("mag beta (bpow beta e) = e + 1 := mag_bpow", "mag beta (bpow beta e) = e := mag_bpow"),
        ("mag beta x + mag beta y - 1 ≤ mag beta (x * y) ∧ mag beta (x * y) ≤ mag beta x + mag beta y",
         "mag beta (x * y) ≤ mag beta x + mag beta y ∧ mag beta x + mag beta y - 1 ≤ mag beta (x * y)"),
        ("(mag beta x + 1) / 2 := mag_sqrt", "mag beta x / 2 := mag_sqrt"),
        ("1 < beta → x ≠ 0 → bpow beta (mag beta x - 1) ≤ |x|", "1 < beta → bpow beta (mag beta x - 1) ≤ |x|"),
        ("1 < beta → x ≠ 0 →\n    mag beta (x * bpow beta e)", "1 < beta →\n    mag beta (x * bpow beta e)"),
    ],
    "v": [
        ("Rabs x < bpow r (mag r x) := bpow_mag_gt", "Rabs x <= bpow r (mag r x - 1) := bpow_mag_gt"),
        ("bpow r (e - 1) <= Rabs x < bpow r e -> mag r x = e :> Z := mag_unique",
         "bpow r (e - 1) <= Rabs x <= bpow r e -> mag r x = e :> Z := mag_unique"),
        ("forall (r : radix) x y, 0 < x -> x <= y -> (mag r x <= mag r y)%Z := mag_le",
         "forall (r : radix) x y, x <= y -> (mag r x <= mag r y)%Z := mag_le"),
        ("mag r (bpow r e) = (e + 1)%Z :> Z := mag_bpow", "mag r (bpow r e) = e :> Z := mag_bpow"),
        ("(mag r x + mag r y - 1 <= mag r (x * y) <= mag r x + mag r y)%Z := mag_mult",
         "(mag r x + mag r y <= mag r (x * y) <= mag r x + mag r y)%Z := mag_mult"),
        ("Z.div2 (mag r x + 1) :> Z", "Z.div2 (mag r x) :> Z"),
        ("forall (r : radix) x, x <> 0 -> bpow r (mag r x - 1) <= Rabs x := bpow_mag_le",
         "forall (r : radix) x, bpow r (mag r x - 1) <= Rabs x := bpow_mag_le"),
        ("forall (r : radix) x e, x <> 0 ->\n  mag r (x * bpow r e)", "forall (r : radix) x e,\n  mag r (x * bpow r e)"),
    ],
}


class RauxMagContracts(unittest.TestCase):
    def check_mutations(self, language):
        source = (ROOT / "scripts/fixtures" / f"RauxMagContracts.{language}").read_text()
        with tempfile.TemporaryDirectory(prefix="floatspec-raux-mag-") as directory:
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

    def test_lean_magnitude(self):
        self.check_mutations("lean")

    @unittest.skipUnless(os.environ.get("FLOCQ_AUDIT_DIR"), "requires pinned built Rocq")
    def test_rocq_magnitude(self):
        self.check_mutations("v")


if __name__ == "__main__":
    unittest.main()
