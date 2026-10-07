"""Reject silent changes to Float_prop.v's laws: directions, signs, exponents and premises."""

import os
from pathlib import Path
import tempfile
import unittest

import flocq_bridge as core


ROOT = Path(__file__).resolve().parents[1]
MUTATIONS = {
    "lean": [
        ("Ord.compare m1 m2 := Rcompare_F2R", "Ord.compare m2 m1 := Rcompare_F2R"),
        ("F2R (FlocqFloat.mk |m| e : FlocqFloat beta) = |F2R (FlocqFloat.mk m e : FlocqFloat beta)| := F2R_Zabs",
         "F2R (FlocqFloat.mk |m| e : FlocqFloat beta) = F2R (FlocqFloat.mk m e : FlocqFloat beta) := F2R_Zabs"),
        ("F2R (FlocqFloat.mk (-m) e : FlocqFloat beta) = -F2R (FlocqFloat.mk m e : FlocqFloat beta) := F2R_Zopp",
         "F2R (FlocqFloat.mk (-m) e : FlocqFloat beta) = F2R (FlocqFloat.mk m e : FlocqFloat beta) := F2R_Zopp"),
        ("0 ≤ F2R (FlocqFloat.mk m e : FlocqFloat beta) → 0 ≤ m := ge_0_F2R",
         "0 ≤ F2R (FlocqFloat.mk m e : FlocqFloat beta) → 0 < m := ge_0_F2R"),
        ("F2R (FlocqFloat.mk (m + 1) e1 : FlocqFloat beta) ≤ bpow beta e2 := F2R_p1_le_bpow",
         "F2R (FlocqFloat.mk (m + 1) e1 : FlocqFloat beta) < bpow beta e2 := F2R_p1_le_bpow"),
        ("F2R (FlocqFloat.mk (m * Zpower beta (e - e')) e' : FlocqFloat beta) := F2R_change_exp",
         "F2R (FlocqFloat.mk (m * Zpower beta (e' - e)) e' : FlocqFloat beta) := F2R_change_exp"),
        ("mag beta (F2R (FlocqFloat.mk m e : FlocqFloat beta)) = Zdigits beta m + e := mag_F2R_Zdigits",
         "mag beta (F2R (FlocqFloat.mk m e : FlocqFloat beta)) = Zdigits beta m := mag_F2R_Zdigits"),
        ("e2 < e1 ∧ e1 + mag beta (m1 : ℝ) = e2 + mag beta (m2 : ℝ)",
         "e2 < e1 ∧ e1 + mag beta (m2 : ℝ) = e2 + mag beta (m1 : ℝ)"),
    ],
    "v": [
        ("= Z.compare m1 m2 := Rcompare_F2R", "= Z.compare m2 m1 := Rcompare_F2R"),
        ("F2R (Float beta (Z.abs m) e) = Rabs (F2R (Float beta m e))", "F2R (Float beta (Z.abs m) e) = F2R (Float beta m e)"),
        ("F2R (Float beta (Z.opp m) e) = Ropp (F2R (Float beta m e))", "F2R (Float beta (Z.opp m) e) = F2R (Float beta m e)"),
        ("0 <= F2R (Float beta m e) -> (0 <= m)%Z := ge_0_F2R", "0 <= F2R (Float beta m e) -> (0 < m)%Z := ge_0_F2R"),
        ("F2R (Float beta (m + 1) e1) <= bpow beta e2", "F2R (Float beta (m + 1) e1) < bpow beta e2"),
        ("F2R (Float beta (m * Zpower beta (e - e')) e') := F2R_change_exp",
         "F2R (Float beta (m * Zpower beta (e' - e)) e') := F2R_change_exp"),
        ("(mag beta (F2R (Float beta m e)) = Zdigits beta m + e :> Z)%Z := mag_F2R_Zdigits",
         "(mag beta (F2R (Float beta m e)) = Zdigits beta m :> Z)%Z := mag_F2R_Zdigits"),
        ("(e1 + mag beta (IZR m1) = e2 + mag beta (IZR m2))%Z", "(e1 + mag beta (IZR m2) = e2 + mag beta (IZR m1))%Z"),
    ],
}


class FloatPropContracts(unittest.TestCase):
    def check_mutations(self, language):
        source = (ROOT / "scripts/fixtures" / f"FloatPropContracts.{language}").read_text()
        with tempfile.TemporaryDirectory(prefix="floatspec-float-prop-") as directory:
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

    def test_lean_float_laws(self):
        self.check_mutations("lean")

    @unittest.skipUnless(os.environ.get("FLOCQ_AUDIT_DIR"), "requires pinned built Rocq")
    def test_rocq_float_laws(self):
        self.check_mutations("v")


if __name__ == "__main__":
    unittest.main()
