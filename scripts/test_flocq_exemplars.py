"""Exemplar lane: paired Rocq/Lean fixtures, exact oracles and drift controls.

Offline tests check the fixture inventory, provenance headers and the exact
oracles. Live tests need FLOCQ_AUDIT_DIR (a built reference at the pin):
they compile each pair, require identical rows, and require every oracle to
hold on both sides.
"""

from fractions import Fraction
import os
from pathlib import Path
import re
import tempfile
import unittest

import flocq_exemplars as lane

FIXTURE_SUFFIXES = {".v", ".lean"}


def fixture_paths():
    return sorted(path for path in lane.FIXTURES.iterdir() if path.suffix in FIXTURE_SUFFIXES)


class InventoryTests(unittest.TestCase):
    def test_every_module_has_both_sides_and_a_readme_entry(self):
        readme = (lane.FIXTURES / "README.md").read_text()
        expected = {*lane.SHARED, *lane.EXEMPLARS}
        self.assertEqual({path.stem for path in fixture_paths()}, expected)
        for name in expected:
            for suffix in FIXTURE_SUFFIXES:
                self.assertTrue((lane.FIXTURES / f"{name}{suffix}").is_file(), name + suffix)
            self.assertTrue(re.search(rf"\| `{name}` \|", readme), f"README.md has no table row for {name}")

    def test_non_verbatim_fixtures_state_their_provenance(self):
        for path in fixture_paths():
            if path.name in lane.UPSTREAM_VERBATIM:
                continue
            header = path.read_text()[:2500]
            with self.subTest(path.name):
                self.assertTrue(header.startswith("(*") or header.startswith("/-"))
                # Every fixture names the pinned upstream commit it follows.
                self.assertTrue(any(commit[:8] in header for commit in lane.UPSTREAM_COMMITS.values()))
                self.assertRegex(header, r"(?i)upstream|provenance|not upstream")

    def test_exemplar_row_shapes_are_declared(self):
        for exemplar in lane.EXEMPLARS.values():
            self.assertGreater(exemplar.rows, 0)
            self.assertGreater(exemplar.width, 0)


class ExactRoundingTests(unittest.TestCase):
    def test_magnitude_brackets_the_value(self):
        for beta, x, e in ((2, Fraction(1), 1), (2, Fraction(1, 2), 0), (10, Fraction(999), 3),
                           (10, Fraction(1000), 4), (3, Fraction(1, 9), -1),
                           (2, Fraction(1, 2**1074), -1073)):
            self.assertEqual(lane.mag_rational(beta, x), e)
            self.assertLessEqual(Fraction(beta) ** (e - 1), x)
            self.assertLess(x, Fraction(beta) ** e)

    def test_modes_on_ties_and_signs(self):
        p3 = lane.flx(3)
        cases = [("NE", 9, 8), ("NE", 11, 12), ("NA", 9, 10), ("NA", -9, -10), ("DN", -9, -10),
                 ("UP", -9, -8), ("ZR", -9, -8), ("ZR", 9, 8), (("N", lambda f: True), 9, 10),
                 (("N", lambda f: False), -9, -10)]
        for mode, x, expected in cases:
            with self.subTest(mode=mode, x=x):
                self.assertEqual(lane.round_rational(2, p3, mode, Fraction(x)), expected)

    def test_square_roots_round_from_the_exact_value(self):
        self.assertEqual(lane.round_sqrt(2, lane.flx(3), "NE", Fraction(2)), Fraction(3, 2))
        self.assertEqual(lane.round_sqrt(10, lane.flx(2), "DN", Fraction(2)), Fraction(14, 10))
        self.assertEqual(lane.round_sqrt(10, lane.flx(2), "UP", Fraction(2)), Fraction(15, 10))
        self.assertEqual(lane.round_sqrt(5, lane.flx(3), "NE", Fraction(49)), 7)
        self.assertEqual(lane.round_sqrt(2, lane.flx(3), "NE", Fraction(-4)), 0)


def expected_compute_grid_row(beta, fk, ck, mx, ex, my, ey):
    """Build a row from the oracle's own answers (in lowest terms)."""
    def float_of(x):
        exponent = 0
        while x.denominator != 1:
            x, exponent = x * beta, exponent - 1
        return [x.numerator, exponent]
    fexp, mode = lane.COMPUTE_GRID_FEXPS[fk], lane.CHOICE_MODES[ck]
    x, y = lane.value(beta, mx, ex), lane.value(beta, my, ey)
    return [beta, fk, ck, mx, ex, my, ey,
            *float_of(lane.round_rational(beta, fexp, mode, x + y)),
            *float_of(lane.round_rational(beta, fexp, mode, x * y)),
            *(float_of(lane.round_rational(beta, fexp, mode, x / y)) if y else [0, 0]),
            *float_of(lane.round_sqrt(beta, fexp, mode, x))]


class OracleControlTests(unittest.TestCase):
    def test_compute_grid_oracle_accepts_exact_rows_and_rejects_perturbations(self):
        rows = [expected_compute_grid_row(beta, fk, ck, 23, -1, -5, 2)
                for beta in (2, 3, 10) for fk in range(4) for ck in range(5)]
        report = lane.oracle_compute_grid(rows)
        self.assertEqual(report.violations, [])
        self.assertEqual(report.holds, 4 * len(rows))
        for column in range(7, 15, 2):
            mutated = [row[:] for row in rows]
            mutated[5][column] += 1
            with self.subTest(column=column):
                self.assertEqual(len(lane.oracle_compute_grid(mutated).violations), 1)

    def test_a_zero_divisor_is_a_false_premise_not_a_pass(self):
        report = lane.oracle_compute_grid([expected_compute_grid_row(2, 0, 3, 1, 0, 0, 0)])
        self.assertEqual((report.premise_false, report.holds, report.violations), (1, 3, []))

    def test_cody_waite_oracle_bounds_have_teeth(self):
        # x = 0: k = t = 0, p = 1/4, q = 1/2, r = 1/2, Zfloor k = 0, cw_exp 0 = 1.
        row = [0, 0, 0, 0, 0, 0, 1, -2, 1, -1, 1, -1, 0, 1, 0]
        self.assertEqual(lane.oracle_cody_waite([row]).violations, [])
        too_far = row[:13] + [2**50 + 1, -50]            # relative error 2^-50 > 2^-51
        wide_t = row[:4] + [356, -10] + row[6:]          # |t| > 355/1024
        wrong_floor = row[:12] + [1] + row[13:]
        for label, mutated in (("exp", too_far), ("t", wide_t), ("floor", wrong_floor)):
            with self.subTest(label):
                self.assertEqual(len(lane.oracle_cody_waite([mutated]).violations), 1)
        outside = [1000, 0, *row[2:]]
        self.assertEqual(lane.oracle_cody_waite([outside]).premise_false, 2)

    def test_division_oracle_checks_frcpa_spec_before_the_quotient(self):
        exact = [6, 1, 0, 1, 0, 6, 0, 1, -17, 6, 0, 6]
        self.assertEqual(lane.oracle_division_u16([exact]).holds, 1)
        self.assertEqual(len(lane.oracle_division_u16([exact[:11] + [5]]).violations), 1)
        # y0 = 1/2 for b = 1 breaks frcpa_spec: a wrong quotient is then a control break.
        control = lane.oracle_division_u16([[6, 1, 3, 1, -1, 3, 0, 1, -1, 4, 0, 4]])
        self.assertEqual((control.premise_false, control.control_breaks, control.violations),
                         (1, 1, []))

    def test_a_missing_control_break_fails_the_oracle_verdict(self):
        exemplar = lane.Exemplar("Probe", rows=1, width=1,
                                 oracle=lambda rows: lane.OracleReport(holds=1),
                                 needs_control_break=True)
        result = lane.judge(exemplar, {"rocq": [[0]], "lean": [[0]]})
        self.assertEqual(result["verdict"], "match")
        self.assertEqual(result["oracle_rocq"]["verdict"], "violated")

    def test_a_single_differing_row_is_a_mismatch(self):
        exemplar = lane.Exemplar("Probe", rows=2, width=1,
                                 oracle=lambda rows: lane.OracleReport(holds=1))
        result = lane.judge(exemplar, {"rocq": [[0], [1]], "lean": [[0], [2]]})
        self.assertEqual(result["verdict"], "mismatch")
        self.assertEqual(result["differing_rows"], [1])


@unittest.skipUnless(os.environ.get("FLOCQ_AUDIT_DIR"), "live tests require FLOCQ_AUDIT_DIR")
class LiveExemplarTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.flocq = Path(os.environ["FLOCQ_AUDIT_DIR"]).resolve()
        cls.scratch = tempfile.TemporaryDirectory(prefix="floatspec-exemplars-test-")
        cls.workspace = lane.Workspace(cls.flocq, Path(cls.scratch.name))
        cls.workspace.build_shared()

    @classmethod
    def tearDownClass(cls):
        cls.scratch.cleanup()

    def check(self, name):
        exemplar = lane.EXEMPLARS[name]
        result = lane.judge(exemplar, self.workspace.observe(exemplar))
        self.assertEqual(result["verdict"], "match", result)
        for side in ("rocq", "lean"):
            self.assertEqual(result[f"oracle_{side}"]["verdict"], "holds", result)
        return result

    def test_verbatim_upstream_files_have_not_drifted(self):
        lane.check_upstream_verbatim(self.flocq)

    def test_compute_grid(self):
        self.check("ComputeGrid")

    def test_cody_waite(self):
        self.check("CodyWaite")

    def test_division_u16(self):
        result = self.check("DivisionU16")
        self.assertGreater(result["oracle_rocq"]["control_breaks"], 0)

    def mutant(self, name, side, old, new):
        """Run a copy of an exemplar with one side textually mutated."""
        exemplar = lane.EXEMPLARS[name]
        mutant = lane.Exemplar(f"{name}Mutant", exemplar.rows, exemplar.width, exemplar.oracle,
                               exemplar.needs_control_break, exemplar.timeout)
        for suffix, folder in ((".v", self.workspace.rocq), (".lean", self.workspace.lean)):
            source = (folder / f"{name}{suffix}").read_text()
            if (suffix == ".v") == (side == "rocq"):
                self.assertEqual(source.count(old), 1, f"mutation anchor {old!r} must be unique")
                source = source.replace(old, new)
            source = re.sub(rf"\b{name}\b", mutant.name, source)
            (folder / f"{mutant.name}{suffix}").write_text(source)
        return lane.judge(mutant, self.workspace.observe(mutant))

    def test_lean_side_choice_drift_is_a_mismatch_and_an_oracle_violation(self):
        result = self.mutant("ComputeGrid", "lean", "  | 3 => rnd_NE\n", "  | 3 => rnd_NA\n")
        self.assertEqual(result["verdict"], "mismatch")
        self.assertEqual(result["oracle_rocq"]["verdict"], "holds")
        self.assertEqual(result["oracle_lean"]["verdict"], "violated")


if __name__ == "__main__":
    unittest.main()
