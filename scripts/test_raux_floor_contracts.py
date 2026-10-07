"""Reject silent changes to Raux's integer rounding bodies, intervals, premises and modes."""

import os
from pathlib import Path
import tempfile
import unittest

import flocq_bridge as core


ROOT = Path(__file__).resolve().parents[1]
MUTATIONS = {
    "lean": [
        ("Zceil x = -Zfloor (-x) := rfl", "Zceil x = Zfloor (-x) := rfl"),
        ("Ztrunc x = if Rlt_bool x 0 then Zceil x else Zfloor x := rfl",
         "Ztrunc x = if Rlt_bool x 0 then Zfloor x else Zceil x := rfl"),
        ("x < ((n + 1 : Int) : ℝ) → Zfloor x = n", "x ≤ ((n + 1 : Int) : ℝ) → Zfloor x = n"),
        ("∀ x : ℝ, 0 ≤ x → Ztrunc x = Zfloor x", "∀ x : ℝ, x ≤ 0 → Ztrunc x = Zfloor x"),
        ("∀ x : ℝ, ((Zfloor x : Int) : ℝ) ≠ x → Zceil x = Zfloor x + 1",
         "∀ x : ℝ, Zceil x = Zfloor x + 1"),
        ("= Int.fdiv x y := Zfloor_div", "= Int.tdiv x y := Zfloor_div"),
        ("= Int.tdiv x y := Ztrunc_div", "= x / y := Ztrunc_div"),
        ("((Zceil x : Int) : ℝ) < x + 1 := Zceil_lb", "((Zceil x : Int) : ℝ) < x := Zceil_lb"),
    ],
    "v": [
        ("Zceil x = (- Zfloor (- x))%Z := fun x => eq_refl", "Zceil x = Zfloor (- x) := fun x => eq_refl"),
        ("Ztrunc x = if Rlt_bool x 0 then Zceil x else Zfloor x := fun x => eq_refl",
         "Ztrunc x = if Rlt_bool x 0 then Zfloor x else Zceil x := fun x => eq_refl"),
        ("IZR n <= x < IZR (n + 1) -> Zfloor x = n", "IZR n <= x <= IZR (n + 1) -> Zfloor x = n"),
        ("forall x, 0 <= x -> Ztrunc x = Zfloor x", "forall x, x <= 0 -> Ztrunc x = Zfloor x"),
        ("forall x, IZR (Zfloor x) <> x -> Zceil x = (Zfloor x + 1)%Z",
         "forall x, Zceil x = (Zfloor x + 1)%Z"),
        ("Zfloor (IZR x / IZR y) = (x / y)%Z := Zfloor_div", "Zfloor (IZR x / IZR y) = Z.quot x y := Zfloor_div"),
        ("Ztrunc (IZR x / IZR y) = Z.quot x y := Ztrunc_div", "Ztrunc (IZR x / IZR y) = (x / y)%Z := Ztrunc_div"),
        ("IZR (Zceil x) < x + 1 := Zceil_lb", "IZR (Zceil x) < x := Zceil_lb"),
    ],
}


class RauxFloorContracts(unittest.TestCase):
    def check_mutations(self, language):
        source = (ROOT / "scripts/fixtures" / f"RauxFloorContracts.{language}").read_text()
        with tempfile.TemporaryDirectory(prefix="floatspec-raux-floor-") as directory:
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

    def test_lean_bodies_and_premises(self):
        self.check_mutations("lean")

    @unittest.skipUnless(os.environ.get("FLOCQ_AUDIT_DIR"), "requires pinned built Rocq")
    def test_rocq_bodies_and_premises(self):
        self.check_mutations("v")


if __name__ == "__main__":
    unittest.main()
