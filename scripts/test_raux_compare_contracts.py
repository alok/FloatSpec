"""Reject silent changes to Raux's comparison encoding, bodies, premises and names."""

import os
from pathlib import Path
import tempfile
import unittest

import flocq_bridge as core


ROOT = Path(__file__).resolve().parents[1]
MUTATIONS = {
    "lean": [
        ("∀ x y : ℝ, y < x → Rle_bool_prop x y false", "∀ x y : ℝ, y ≤ x → Rle_bool_prop x y false"),
        ("∀ x y : ℝ, y ≤ x → Rlt_bool_prop x y false", "∀ x y : ℝ, y < x → Rlt_bool_prop x y false"),
        ("Rle_bool x y = match Rcompare x y with | .gt => false | _ => true := rfl",
         "Rle_bool x y = match Rcompare x y with | .lt => false | _ => true := rfl"),
        ("Rcompare x y = (Rcompare y x).swap := Rcompare_sym", "Rcompare x y = Rcompare y x := Rcompare_sym"),
        ("∀ z x y : ℝ, 0 < z → Rcompare (x * z)", "∀ z x y : ℝ, Rcompare (x * z)"),
        ("Rcompare (x : ℝ) (y : ℝ) = compare x y", "Rcompare (x : ℝ) (y : ℝ) = compare y x"),
        ("| .lt => x | .eq => x | .gt => y := Rmin_compare", "| .lt => y | .eq => x | .gt => y := Rmin_compare"),
        ("(!Rle_bool x y) = Rlt_bool y x := negb_Rlt_bool", "(!Rle_bool x y) = Rlt_bool y x := negb_Rle_bool"),
    ],
    "v": [
        ("forall x y, y < x -> Rle_bool_prop x y false", "forall x y, y <= x -> Rle_bool_prop x y false"),
        ("forall x y, y <= x -> Rlt_bool_prop x y false", "forall x y, y < x -> Rlt_bool_prop x y false"),
        ("Rle_bool x y = match Rcompare x y with Gt => false | _ => true end",
         "Rle_bool x y = match Rcompare x y with Lt => false | _ => true end"),
        ("Rcompare x y = CompOpp (Rcompare y x) := Rcompare_sym", "Rcompare x y = Rcompare y x := Rcompare_sym"),
        ("forall z x y, 0 < z -> Rcompare (x * z)", "forall z x y, Rcompare (x * z)"),
        ("Rcompare (IZR x) (IZR y) = Z.compare x y", "Rcompare (IZR x) (IZR y) = Z.compare y x"),
        ("Lt => x | Eq => x | Gt => y end := Rmin_compare", "Lt => y | Eq => x | Gt => y end := Rmin_compare"),
        ("negb (Rle_bool x y) = Rlt_bool y x := negb_Rlt_bool", "negb (Rle_bool x y) = Rlt_bool y x := negb_Rle_bool"),
    ],
}


class RauxCompareContracts(unittest.TestCase):
    def check_mutations(self, language):
        source = (ROOT / "scripts/fixtures" / f"RauxCompareContracts.{language}").read_text()
        with tempfile.TemporaryDirectory(prefix="floatspec-raux-compare-") as directory:
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

    def test_lean_encoding_and_names(self):
        self.check_mutations("lean")

    @unittest.skipUnless(os.environ.get("FLOCQ_AUDIT_DIR"), "requires pinned built Rocq")
    def test_rocq_encoding_and_names(self):
        self.check_mutations("v")


if __name__ == "__main__":
    unittest.main()
