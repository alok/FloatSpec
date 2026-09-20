"""Test grid selection by exhaustive enumeration in a six-bit toy format."""

from fractions import Fraction
import json
import os
from pathlib import Path
import tempfile
import unittest

import ieee_exact_oracle as oracle


@unittest.skipUnless(os.environ.get("FLOCQ_AUDIT_DIR"), "live test requires FLOCQ_AUDIT_DIR")
class LiveOracleTests(unittest.TestCase):
    def test_all_modes_formats_and_kernel_proofs(self):
        import ieee_modes_bridge as bridge
        flocq = Path(os.environ["FLOCQ_AUDIT_DIR"])
        cases = []
        for width, one, two, half, half_ulp, maximum in (
                (32, 0x3f800000, 0x40000000, 0x3f000000, 0x33800000, 0x7f7fffff),
                (64, 0x3ff0000000000000, 0x4000000000000000, 0x3fe0000000000000,
                 0x3ca0000000000000, 0x7fefffffffffffff)):
            sign = 1 << (width - 1)
            for mode in range(5):
                cases += [(width, mode, one, half_ulp, sign | one),
                          (width, mode, 1, half, sign),
                          (width, mode, maximum, two, sign | maximum),
                          (width, mode, sign, sign, 0)]
        with tempfile.TemporaryDirectory(prefix="floatspec-exact-modes-") as directory:
            folder = Path(directory)
            results = bridge.execute(cases, flocq, bridge.configured_coqc(flocq), folder)
            self.assertEqual(bridge.compare(cases, results), [])
            failures, assertions = oracle.compare_columns(cases, results, bridge.COLUMNS, oracle.mode_columns)
            self.assertEqual(failures, [])
            self.assertEqual(assertions, 6570)
            bridge.bootstrap(cases, results["rocq"], folder)

    def test_native_compiled_kernel_rocq_and_proofs(self):
        import native_arithmetic_bridge as bridge
        flocq = Path(os.environ["FLOCQ_AUDIT_DIR"])
        cases = [(0x3ff0000000000000, 0x4000000000000000),
                 (0x3ff0000000000000, 0xbff0000000000000),
                 (0x7fefffffffffffff, 0x4000000000000000),
                 (1, 0x3fe0000000000000), (0x8000000000000001, 0x3fe0000000000000),
                 (0x8000000000000000, 0), (0x7ff0000000000001, 0xfff0000000000000)]
        with tempfile.TemporaryDirectory(prefix="floatspec-exact-native-") as directory:
            folder = Path(directory)
            results = bridge.execute(cases, flocq, bridge.configured_coqc(flocq), folder)
            self.assertEqual(bridge.compare(cases, results), [])
            failures, assertions = oracle.compare_columns(cases, results, bridge.COLUMNS, oracle.native_columns)
            self.assertEqual(failures, [])
            self.assertEqual(assertions, 168)
            bridge.bootstrap_lean(cases, results["rocq"], folder)


class SavedReportTests(unittest.TestCase):
    @staticmethod
    def fixture(folder):
        import native_arithmetic_bridge
        columns = native_arithmetic_bridge.COLUMNS
        report = {"status": "passed", "cases": 1, "compared_cases": 1,
                  "bootstrapped_lean_cases": 1, "columns": list(columns),
                  "lean_source_sha256": "historical-source", "reference": "historical-pin"}
        path = folder / "report.json"
        path.write_text(json.dumps(report))
        (folder / "cases.json").write_text("[[0, 0]]")
        batch = folder / "batch_000000"
        batch.mkdir()
        for name in ("native", "model", "compiled_model"):
            (batch / f"{name}.out").write_text("[[0, 0, 0, 0, 0, 0, 0]]")
        (batch / "rocq.out").write_text("= [[0; 0; 0; 0; 0; 0; 0]] : list (list Z)")
        return path, report

    def test_saved_report_and_correlated_corruption(self):
        import check_ieee_exact_oracle as checker
        with tempfile.TemporaryDirectory() as directory:
            folder = Path(directory)
            path, _ = self.fixture(folder)
            result = checker.check_report(path, "native")
            self.assertEqual(result["status"], "passed")
            self.assertEqual(result["oracle_assertions"], 24)  # 0/0 is explicitly excluded
            self.assertEqual(result["lean_source_sha256"], "historical-source")
            for name in ("native", "model", "compiled_model", "rocq"):
                output = folder / "batch_000000" / f"{name}.out"
                output.write_text(output.read_text().replace("[[0", "[[1"))
            result = checker.check_report(path, "native")
            self.assertEqual(result["status"], "mismatch")
            self.assertEqual(len(result["mismatches"]), 4)

    def test_incomplete_report_or_missing_output_is_not_a_pass(self):
        import check_ieee_exact_oracle as checker
        with tempfile.TemporaryDirectory() as directory:
            folder = Path(directory)
            path, report = self.fixture(folder)
            for key, value in (("status", "running"), ("compared_cases", 0),
                               ("bootstrapped_lean_cases", 0), ("columns", [])):
                path.write_text(json.dumps({**report, key: value}))
                with self.assertRaises(ValueError):
                    checker.check_report(path, "native")
            path.write_text(json.dumps(report))
            (folder / "batch_000000" / "rocq.out").unlink()
            with self.assertRaises(FileNotFoundError):
                checker.check_report(path, "native")


class ExactOracleTests(unittest.TestCase):
    def test_known_decode_boundaries(self):
        for width, one, minimum, maximum, inf in (
                (32, 0x3f800000, Fraction(1, 2**149), (2 - Fraction(1, 2**23)) * 2**127, 0x7f800000),
                (64, 0x3ff0000000000000, Fraction(1, 2**1074), (2 - Fraction(1, 2**52)) * 2**1023, 0x7ff0000000000000)):
            fmt = oracle.FORMATS[width]
            self.assertEqual(oracle.decode(fmt, one), 1)
            self.assertEqual(oracle.decode(fmt, 1), minimum)
            self.assertEqual(oracle.decode(fmt, inf - 1), maximum)
            self.assertEqual(oracle.decode(fmt, one | fmt.sign_bit), -1)
            self.assertIsNone(oracle.decode(fmt, inf))
            self.assertIsNone(oracle.decode(fmt, inf + 1))

    def test_exact_magnitudes(self):
        for exponent in range(-1100, 1101, 7):
            power = oracle.power_two(exponent)
            self.assertEqual(oracle.floor_log_two(power), exponent)
            self.assertEqual(oracle.floor_log_two(power * Fraction(3, 4)), exponent - 1)
            self.assertEqual(oracle.floor_log_two(power * Fraction(5, 4)), exponent)

    @staticmethod
    def enumerated(fmt):
        # Enumerate values directly from a subnormal grid and normal binades.
        values = [Fraction(m, 16) for m in range(4)]
        values += [Fraction(m) * oracle.power_two(e)
                   for e in range(-4, 2) for m in range(4, 8)]
        values.append(Fraction(16))  # conceptual first overflowing grid point
        assert len(values) == fmt.infinity + 1
        return values

    @staticmethod
    def choose(points, value, mode, negative=False, square=False):
        # Exhaustive ordered search, independent of magnitude and grid scaling.
        coordinates = [point * point for point in points] if square else points
        lower = max(index for index, point in enumerate(coordinates) if point <= value)
        if coordinates[lower] == value:
            return lower
        upper = lower + 1
        if mode in (0, 4):
            midpoint = (points[lower] + points[upper]) / 2
            threshold = midpoint * midpoint if square else midpoint
            return upper if value > threshold or (value == threshold and (mode == 4 or lower % 2)) else lower
        return upper if (mode == 2 and negative) or (mode == 3 and not negative) else lower

    def test_rational_rounding_against_exhaustive_grid(self):
        fmt = oracle.Format(2, 3)
        points = self.enumerated(fmt)
        inputs = {Fraction(n, 64) for n in range(1025)}
        inputs |= {(a + b) / 2 for a, b in zip(points, points[1:])}
        for mode in range(5):
            for magnitude in inputs:
                for negative in (False, True):
                    word = self.choose(points, magnitude, mode, negative)
                    if word == fmt.infinity and mode not in (0, 4) and not (
                            (mode == 2 and negative) or (mode == 3 and not negative)):
                        word -= 1
                    word |= fmt.sign_bit if negative else 0
                    actual = oracle.round_rational(fmt, mode, -magnitude if negative else magnitude, negative)
                    self.assertEqual(actual, word, (mode, magnitude, negative))

    def test_square_root_against_exhaustive_squared_grid(self):
        fmt = oracle.Format(2, 3)
        points = self.enumerated(fmt)
        inputs = {Fraction(n, 16) for n in range(4097)}
        inputs |= {((a + b) / 2) ** 2 for a, b in zip(points, points[1:])}
        inputs |= {a * a for a in points}
        for mode in range(5):
            for value in inputs:
                expected = self.choose(points, value, mode, square=True)
                if expected == fmt.infinity and mode in (1, 2):
                    expected -= 1
                self.assertEqual(oracle.round_sqrt(fmt, mode, value), expected, (mode, value))

    def test_binary32_ties_subnormal_and_overflow(self):
        fmt = oracle.FORMATS[32]
        half_ulp = Fraction(1, 2**24)
        self.assertEqual([oracle.round_rational(fmt, mode, 1 + half_ulp) for mode in range(5)],
                         [0x3f800000, 0x3f800000, 0x3f800000, 0x3f800001, 0x3f800001])
        self.assertEqual([oracle.round_rational(fmt, mode, Fraction(1, 2**150)) for mode in range(5)],
                         [0, 0, 0, 1, 1])
        self.assertEqual([oracle.round_rational(fmt, mode, Fraction(2**200)) for mode in range(5)],
                         [0x7f800000, 0x7f7fffff, 0x7f7fffff, 0x7f800000, 0x7f800000])

    def test_signed_zero_policies_and_fused_rounding(self):
        for mode in range(5):
            cancel = 0x80000000 if mode == 2 else 0
            self.assertEqual(oracle.expected_operations(32, mode, 0x3f800000, 0xbf800000)["add"], cancel)
            self.assertEqual(oracle.expected_operations(32, mode, 0x80000000, 0x80000000)["add"], 0x80000000)
            self.assertEqual(oracle.expected_operations(32, mode, 0x80000000, 0x3f800000)["mul"], 0x80000000)
            self.assertEqual(oracle.expected_operations(32, mode, 0x80000000, 0)["sqrt_left"], 0x80000000)
        # Exact (1+2^-23)(1-2^-23)-1 = -2^-46; one rounding, not two.
        result = oracle.expected_operations(32, 0, 0x3f800001, 0x3f7ffffe, 0xbf800000)
        self.assertEqual(result["fma"], 0xa8800000)

    def test_excluded_inputs_are_explicit(self):
        self.assertEqual(oracle.expected_operations(32, 0, 0x7f800001, 0x7f800000), {})
        self.assertNotIn("div", oracle.expected_operations(32, 0, 0x3f800000, 0))
        self.assertNotIn("sqrt_left", oracle.expected_operations(32, 0, 0xbf800000, 0x3f800000))

    def test_all_paths_agreeing_on_wrong_rounding_is_rejected(self):
        case = (32, 3, 0x3f800000, 0x33800000, 0)
        expected = oracle.mode_columns(case)
        columns = tuple(expected)
        row = list(expected.values())
        results = {path: [row.copy()] for path in ("lean", "compiled", "rocq")}
        failures, assertions = oracle.compare_columns([case], results, columns, oracle.mode_columns)
        self.assertEqual(failures, [])
        self.assertEqual(assertions, 3 * len(expected))
        for path in results:
            results[path][0][columns.index("add")] = 0x3f800000  # wrong nearest-even answer
        failures, _ = oracle.compare_columns([case], results, columns, oracle.mode_columns)
        self.assertEqual(len(failures), 3)
        self.assertTrue(all(failure["columns"] == ["add"] for failure in failures))

    def test_common_input_corruption_is_rejected(self):
        case = (0x3ff0000000000000, 0x4000000000000000)
        expected = oracle.native_columns(case)
        columns = tuple(expected)
        row = list(expected.values())
        row[columns.index("left")] = 0
        observations = {path: [row.copy()] for path in ("native", "model", "compiled_model", "rocq")}
        failures, _ = oracle.compare_columns([case], observations, columns, oracle.native_columns)
        self.assertEqual(len(failures), 4)
        self.assertTrue(all(failure["columns"] == ["left"] for failure in failures))

    def test_incomplete_or_unobserved_columns_are_errors(self):
        for observations, columns in (({}, ("left",)), ({"lean": []}, ("left",)),
                                      ({"lean": [[1]]}, ("left",)),
                                      ({"lean": [[1, 2]]}, ("left", "left"))):
            with self.assertRaises(ValueError):
                oracle.compare_columns([(0, 0)], observations, columns, oracle.native_columns)


if __name__ == "__main__":
    unittest.main()
