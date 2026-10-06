"""Reject silent changes to Zaux's sign helpers, fast algorithms and their source recursion."""

import os
from pathlib import Path
import tempfile
import unittest

import flocq_bridge as core


ROOT = Path(__file__).resolve().parents[1]
MUTATIONS = {
    "lean": [
        ("cond_Zopp (Zlt_bool m 0) m = |m| := cond_Zopp_Zlt_bool",
         "cond_Zopp (Zlt_bool 0 m) m = |m| := cond_Zopp_Zlt_bool"),
        ("Zeq_bool (cond_Zopp s m) n = Zeq_bool m (cond_Zopp s n) := Zeq_bool_cond_Zopp",
         "Zeq_bool (cond_Zopp s m) n = Zeq_bool m n := Zeq_bool_cond_Zopp"),
        ("cond_Zopp (!x) y = -cond_Zopp x y", "cond_Zopp (!x) y = cond_Zopp x y"),
        ("Zfast_pow_pos v (.xO e) = Zfast_pow_pos v e ^ 2 := rfl",
         "Zfast_pow_pos v (.xO e) = v * Zfast_pow_pos v e ^ 2 := rfl"),
        ("(let (q, r) := Zpos_div_eucl_aux1 a b; (q, 2 * r)) := rfl",
         "(let (q, r) := Zpos_div_eucl_aux1 a b; (q, 2 * r + 1)) := rfl"),
        ("Zfast_div_eucl a b = Z_div_eucl a b := Zfast_div_eucl_correct",
         "Zfast_div_eucl a b = (a / b, a % b) := Zfast_div_eucl_correct"),
        ("Zfast_div_eucl 7 0 = (0, 7)", "Zfast_div_eucl 7 0 = (0, 0)"),
        ("iter_nat f (n + 1) x = iter_nat f n (f x) := rfl",
         "iter_nat f (n + 1) x = f (iter_nat f n x) := rfl"),
    ],
    "v": [
        ("cond_Zopp (Z.ltb m 0) m = Z.abs m := cond_Zopp_Zlt_bool",
         "cond_Zopp (Z.ltb 0 m) m = Z.abs m := cond_Zopp_Zlt_bool"),
        ("Z.eqb (cond_Zopp s m) n = Z.eqb m (cond_Zopp s n) := Zeq_bool_cond_Zopp",
         "Z.eqb (cond_Zopp s m) n = Z.eqb m n := Zeq_bool_cond_Zopp"),
        ("cond_Zopp (negb x) y = - cond_Zopp x y", "cond_Zopp (negb x) y = cond_Zopp x y"),
        ("Zfast_pow_pos v (xO e) = Z.square (Zfast_pow_pos v e) := fun v e => eq_refl",
         "Zfast_pow_pos v (xO e) = v * Z.square (Zfast_pow_pos v e) := fun v e => eq_refl"),
        ("let (q, r) := Zpos_div_eucl_aux1 a b in (q, 2 * r) :=",
         "let (q, r) := Zpos_div_eucl_aux1 a b in (q, 2 * r + 1) :="),
        ("Zfast_div_eucl a b = Z.div_eucl a b := Zfast_div_eucl_correct",
         "Zfast_div_eucl a b = (Z.quot a b, Z.rem a b) := Zfast_div_eucl_correct"),
        ("Zfast_div_eucl 7 0 = (0, 7)", "Zfast_div_eucl 7 0 = (0, 0)"),
        ("iter_nat f (S n) x = iter_nat f n (f x) := fun A f n x => eq_refl",
         "iter_nat f (S n) x = f (iter_nat f n x) := fun A f n x => eq_refl"),
    ],
}


class AlgorithmContracts(unittest.TestCase):
    def check_mutations(self, language):
        source = (ROOT / "scripts/fixtures" / f"ZauxAlgorithmContracts.{language}").read_text()
        with tempfile.TemporaryDirectory(prefix="floatspec-algorithm-contracts-") as directory:
            path = Path(directory) / f"Control.{language}"
            if language == "lean":
                command = ["lake", "env", "lean", str(path)]
                diagnostic = r"[Tt]ype mismatch|Tactic `decide` proved that the proposition"
            else:
                flocq = Path(os.environ["FLOCQ_AUDIT_DIR"]).resolve()
                command = [core.configured_coqc(flocq), "-q", "-R", str(flocq / "src"),
                           "Flocq", str(path)]
                diagnostic = r"expected to have type|Unable to unify|Attempt to save an incomplete proof"
            path.write_text(source)
            core.run(command)
            for old, new in MUTATIONS[language]:
                with self.subTest(old=old):
                    self.assertEqual(source.count(old), 1)
                    path.write_text(source.replace(old, new))
                    with self.assertRaisesRegex(RuntimeError, diagnostic):
                        core.run(command)

    def test_lean_algorithms_and_recursion(self):
        self.check_mutations("lean")

    @unittest.skipUnless(os.environ.get("FLOCQ_AUDIT_DIR"), "requires pinned built Rocq")
    def test_rocq_algorithms_and_recursion(self):
        self.check_mutations("v")


if __name__ == "__main__":
    unittest.main()
