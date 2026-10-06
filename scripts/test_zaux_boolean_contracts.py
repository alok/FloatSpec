"""Reject silent changes to the Boolean comparison graphs, their strictness and orientation."""

import os
from pathlib import Path
import tempfile
import unittest

import flocq_bridge as core


ROOT = Path(__file__).resolve().parents[1]
MUTATIONS = {
    "lean": [
        ("∀ x y : Int, y < x → Zle_bool_prop x y false", "∀ x y : Int, y ≤ x → Zle_bool_prop x y false"),
        ("∀ x y : Int, y ≤ x → Zlt_bool_prop x y false", "∀ x y : Int, y < x → Zlt_bool_prop x y false"),
        ("(x ≠ y → P false) → ∀ b, Zeq_bool_prop x y b → P b",
         "(x = y → P false) → ∀ b, Zeq_bool_prop x y b → P b"),
        ("Zeq_bool (-x) y = Zeq_bool x (-y) := Zeq_bool_opp", "Zeq_bool (-x) y = Zeq_bool x y := Zeq_bool_opp"),
        ("Zle_bool (-x) y = Zle_bool (-y) x := Zle_bool_opp_l",
         "Zle_bool (-x) y = Zle_bool x (-y) := Zle_bool_opp_l"),
        ("Zle_bool x (-y) = Zle_bool y (-x) := Zle_bool_opp_r",
         "Zle_bool x (-y) = Zle_bool (-x) y := Zle_bool_opp_r"),
        ("(!Zle_bool x y) = Zlt_bool y x := negb_Zle_bool", "(!Zle_bool x y) = Zlt_bool x y := negb_Zle_bool"),
        ("∀ x y : Int, y < x → compare x y = .gt", "∀ x y : Int, x < y → compare x y = .gt"),
    ],
    "v": [
        ("forall x y, y < x -> Zle_bool_prop x y false", "forall x y, y <= x -> Zle_bool_prop x y false"),
        ("forall x y, y <= x -> Zlt_bool_prop x y false", "forall x y, y < x -> Zlt_bool_prop x y false"),
        ("(x <> y -> P false) -> forall b, Zeq_bool_prop x y b -> P b :=\n  Zeq_bool_prop_ind.",
         "(x = y -> P false) -> forall b, Zeq_bool_prop x y b -> P b :=\n  Zeq_bool_prop_ind."),
        ("Z.eqb (- x) y = Z.eqb x (- y) := Zeq_bool_opp.", "Z.eqb (- x) y = Z.eqb x y := Zeq_bool_opp."),
        ("Z.leb (- x) y = Z.leb (- y) x := Zle_bool_opp_l", "Z.leb (- x) y = Z.leb x (- y) := Zle_bool_opp_l"),
        ("Z.leb x (- y) = Z.leb y (- x) := Zle_bool_opp_r", "Z.leb x (- y) = Z.leb (- x) y := Zle_bool_opp_r"),
        ("negb (Z.leb x y) = Z.ltb y x := negb_Zle_bool", "negb (Z.leb x y) = Z.ltb x y := negb_Zle_bool"),
        ("forall x y, y < x -> Z.compare x y = Gt", "forall x y, x < y -> Z.compare x y = Gt"),
    ],
}


class BooleanContracts(unittest.TestCase):
    def check_mutations(self, language):
        source = (ROOT / "scripts/fixtures" / f"ZauxBooleanContracts.{language}").read_text()
        with tempfile.TemporaryDirectory(prefix="floatspec-boolean-contracts-") as directory:
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

    def test_lean_graphs_and_orientation(self):
        self.check_mutations("lean")

    @unittest.skipUnless(os.environ.get("FLOCQ_AUDIT_DIR"), "requires pinned built Rocq")
    def test_rocq_graphs_and_orientation(self):
        self.check_mutations("v")


if __name__ == "__main__":
    unittest.main()
