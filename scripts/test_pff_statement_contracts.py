"""Live typed-client mutations for reviewed `Pff.lean` statement shapes.

`scripts/fixtures/PffStatementContracts.{lean,v}` ascribe the Lean and Rocq
statements of representative Pff theorems.  Each control first checks the
unchanged fixture, then plants a mutation that a faithful port must reject:
an extra premise, a swapped premise order, a specialized rounding mode, or a
weakened conclusion.
"""

import os
from pathlib import Path
import tempfile
import unittest

import flocq_bridge as core


ROOT = Path(__file__).resolve().parents[1]


class StatementContracts(unittest.TestCase):
    def reject(self, language, old, new):
        source = (ROOT / "scripts/fixtures" / f"PffStatementContracts.{language}").read_text()
        self.assertEqual(source.count(old), 1)
        with tempfile.TemporaryDirectory(prefix="floatspec-pff-statements-") as directory:
            path = Path(directory) / f"Control.{language}"
            if language == "lean":
                command = ["lake", "env", "lean", str(path)]
                diagnostic = "Type mismatch"
            else:
                flocq = Path(os.environ["FLOCQ_AUDIT_DIR"]).resolve()
                command = [core.configured_coqc(flocq), "-q", "-R", str(flocq / "src"),
                           "Flocq", str(path)]
                diagnostic = "expected to have type"
            path.write_text(source)
            core.run(command)
            path.write_text(source.replace(old, new))
            with self.assertRaisesRegex(RuntimeError, diagnostic):
                core.run(command)

    def test_lean_implyclosest_has_no_upper_bound_premise(self):
        self.reject("lean", "    -b.dExp ≤ e → |z - _root_.F2R f| ≤ (radix : ℝ) ^ e / 2 →",
                    "    -b.dExp ≤ e → z ≤ (radix : ℝ) ^ (e + (precision : Int)) →\n"
                    "    |z - _root_.F2R f| ≤ (radix : ℝ) ^ e / 2 →")

    def test_lean_fnormalunique_keeps_source_premise_order(self):
        self.reject("lean", "∀ p q : FlocqFloat beta, Fnormal radix b p → Fnormal radix b q →\n"
                            "      _root_.F2R p = _root_.F2R q → p = q)",
                    "∀ p q : FlocqFloat beta, _root_.F2R p = _root_.F2R q →\n"
                    "      Fnormal radix b p → Fnormal radix b q → p = q)")

    def test_lean_errorboundedmult_is_not_closest_only(self):
        self.reject("lean", "  ∀ P : ℝ → FlocqFloat beta → Prop, RoundedModeP bo P →\n"
                            "  ∀ p q f : FlocqFloat beta, Fbounded bo p → Fbounded bo q →\n"
                            "    -bo.dExp ≤ p.Fexp + q.Fexp → P (_root_.F2R p * _root_.F2R q) f →",
                    "  ∀ p q f : FlocqFloat beta, Fbounded bo p → Fbounded bo q →\n"
                    "    -bo.dExp ≤ p.Fexp + q.Fexp →\n"
                    "    Closest bo (radix : ℝ) (_root_.F2R p * _root_.F2R q) f →")

    def test_lean_discri3_has_no_extra_boundedness(self):
        self.reject("lean", "    Fbounded bo p → Fbounded bo q → 0 ≤ _root_.F2R b * _root_.F2R b' →",
                    "    Fbounded bo p → Fbounded bo q → Fbounded bo t →\n"
                    "    0 ≤ _root_.F2R b * _root_.F2R b' →")

    def test_lean_eqexpless_needs_only_left_boundedness(self):
        self.reject("lean", "  Fbounded b p → _root_.F2R p = _root_.F2R q →\n    ∃ r",
                    "  Fbounded b p → Fbounded b q → _root_.F2R p = _root_.F2R q →\n    ∃ r")

    @unittest.skipUnless(os.environ.get("FLOCQ_AUDIT_DIR"), "live tests require FLOCQ_AUDIT_DIR")
    def test_rocq_implyclosest_has_no_upper_bound_premise(self):
        self.reject("v", "  - dExp b <= e ->\n  (Rabs (z - FtoR radix f) <= powerRZ radix e / 2)%R ->",
                    "  - dExp b <= e -> (z <= powerRZ radix (e + p))%R ->\n"
                    "  (Rabs (z - FtoR radix f) <= powerRZ radix e / 2)%R ->")

    @unittest.skipUnless(os.environ.get("FLOCQ_AUDIT_DIR"), "live tests require FLOCQ_AUDIT_DIR")
    def test_rocq_fnormalunique_keeps_source_premise_order(self):
        self.reject("v", "  forall p q : float, Fnormal radix b p -> Fnormal radix b q ->\n"
                         "  FtoR radix p = FtoR radix q -> p = q).",
                    "  forall p q : float, FtoR radix p = FtoR radix q ->\n"
                    "  Fnormal radix b p -> Fnormal radix b q -> p = q).")

    @unittest.skipUnless(os.environ.get("FLOCQ_AUDIT_DIR"), "live tests require FLOCQ_AUDIT_DIR")
    def test_rocq_errorboundedmult_is_not_closest_only(self):
        self.reject("v", "  forall P : R -> float -> Prop, RoundedModeP b radix P ->\n"
                         "  forall p q f : float, Fbounded b p -> Fbounded b q ->\n"
                         "  - dExp b <= Fexp p + Fexp q ->\n"
                         "  P (FtoR radix p * FtoR radix q)%R f ->",
                    "  forall p q f : float, Fbounded b p -> Fbounded b q ->\n"
                    "  - dExp b <= Fexp p + Fexp q ->\n"
                    "  Closest b radix (FtoR radix p * FtoR radix q)%R f ->")

    @unittest.skipUnless(os.environ.get("FLOCQ_AUDIT_DIR"), "live tests require FLOCQ_AUDIT_DIR")
    def test_rocq_discri3_has_no_extra_boundedness(self):
        self.reject("v", "  forall a b b' c p q t dp dq s d : float, Fbounded bo p -> Fbounded bo q ->",
                    "  forall a b b' c p q t dp dq s d : float, Fbounded bo p -> Fbounded bo q ->\n"
                    "  Fbounded bo t ->")

    @unittest.skipUnless(os.environ.get("FLOCQ_AUDIT_DIR"), "live tests require FLOCQ_AUDIT_DIR")
    def test_rocq_eqexpless_needs_only_left_boundedness(self):
        self.reject("v", "  forall (b : Fbound) (p q : float), Fbounded b p -> FtoR radix p = FtoR radix q ->",
                    "  forall (b : Fbound) (p q : float), Fbounded b p -> Fbounded b q ->\n"
                    "  FtoR radix p = FtoR radix q ->")


if __name__ == "__main__":
    unittest.main()
