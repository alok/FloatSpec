"""Reject silent changes to Raux's Boolean equality laws and conditional negation of reals."""

import os
from pathlib import Path
import tempfile
import unittest

import flocq_bridge as core


ROOT = Path(__file__).resolve().parents[1]
MUTATIONS = {
    "lean": [
        ("a = !b → (a == b) = false := eqb_false", "a = b → (a == b) = false := eqb_false"),
        ("cond_Ropp b m = if b then -m else m := rfl", "cond_Ropp b m = if b then m else -m := rfl"),
        ("0 < x → Rlt_bool (cond_Ropp sx x) 0 = sx", "0 ≤ x → Rlt_bool (cond_Ropp sx x) 0 = sx"),
        ("cond_Ropp (Rlt_bool m 0) m = |m| := cond_Ropp_Rlt_bool",
         "cond_Ropp (Rlt_bool 0 m) m = |m| := cond_Ropp_Rlt_bool"),
        ("cond_Ropp b (x * y) = cond_Ropp b x * y", "cond_Ropp b (x * y) = cond_Ropp b x * cond_Ropp b y"),
        ("cond_Ropp b (x + y) = cond_Ropp b x + cond_Ropp b y", "cond_Ropp b (x + y) = cond_Ropp b x + y"),
        ("((FloatSpec.Core.Zaux.cond_Zopp b m : Int) : ℝ) = cond_Ropp b (m : ℝ)",
         "((FloatSpec.Core.Zaux.cond_Zopp b m : Int) : ℝ) = cond_Ropp (!b) (m : ℝ)"),
        ("cond_Ropp b x = cond_Ropp b y → x = y := cond_Ropp_inj",
         "cond_Ropp b x = cond_Ropp (!b) y → x = y := cond_Ropp_inj"),
    ],
    "v": [
        ("x = negb y -> Bool.eqb x y = false := eqb_false", "x = y -> Bool.eqb x y = false := eqb_false"),
        ("cond_Ropp b m = if b then - m else m := fun b m => eq_refl",
         "cond_Ropp b m = if b then m else - m := fun b m => eq_refl"),
        ("0 < x -> Rlt_bool (cond_Ropp sx x) 0 = sx", "0 <= x -> Rlt_bool (cond_Ropp sx x) 0 = sx"),
        ("cond_Ropp (Rlt_bool m 0) m = Rabs m := cond_Ropp_Rlt_bool",
         "cond_Ropp (Rlt_bool 0 m) m = Rabs m := cond_Ropp_Rlt_bool"),
        ("cond_Ropp b (x * y) = cond_Ropp b x * y", "cond_Ropp b (x * y) = cond_Ropp b x * cond_Ropp b y"),
        ("cond_Ropp b (x + y) = cond_Ropp b x + cond_Ropp b y", "cond_Ropp b (x + y) = cond_Ropp b x + y"),
        ("IZR (cond_Zopp b m) = cond_Ropp b (IZR m)", "IZR (cond_Zopp b m) = cond_Ropp (negb b) (IZR m)"),
        ("cond_Ropp b x = cond_Ropp b y -> x = y := cond_Ropp_inj",
         "cond_Ropp b x = cond_Ropp (negb b) y -> x = y := cond_Ropp_inj"),
    ],
}


class RauxCondOppContracts(unittest.TestCase):
    def check_mutations(self, language):
        source = (ROOT / "scripts/fixtures" / f"RauxCondOppContracts.{language}").read_text()
        with tempfile.TemporaryDirectory(prefix="floatspec-raux-cond-opp-") as directory:
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

    def test_lean_conditional_negation(self):
        self.check_mutations("lean")

    @unittest.skipUnless(os.environ.get("FLOCQ_AUDIT_DIR"), "requires pinned built Rocq")
    def test_rocq_conditional_negation(self):
        self.check_mutations("v")


if __name__ == "__main__":
    unittest.main()
