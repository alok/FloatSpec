"""Check model/source policy boundaries and deliberately corrupt every route."""
import json
import os
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

import flocq_bridge as core
import model_adapter_bridge as adapter

CASE = adapter.Case("model_adapters", (32, 0x100000001))
ROW = [0x80000001, 0x80000001, 1, 1, 0x80000001]


class ProfileTests(unittest.TestCase):
    def test_domains_seed_and_replay(self):
        cases = adapter.corpus(854033, 500)
        self.assertEqual(len(cases), 1140)
        self.assertEqual(cases, adapter.corpus(854033, 500))
        self.assertNotEqual(cases, adapter.corpus(854034, 500))
        self.assertEqual(len(set(adapter.COLUMNS)), 5)
        for args in ((16, 1), (True, 0), (32, True), (32,), (64, 1, 2)):
            with self.assertRaises(ValueError):
                adapter.Case("model_adapters", args)
        with self.assertRaises(ValueError):
            adapter.Case("bits32", (32, 1))
        self.assertEqual([adapter.Case(row["op"], tuple(row["args"])) for row in
                          json.loads(json.dumps([adapter.asdict(c) for c in cases]))], cases)
        self.assertTrue(any(case.args[1] < 0 for case in cases))
        self.assertTrue(any(case.args[1] >= 2 ** case.args[0] for case in cases))

    def test_exact_policy_counterexamples(self):
        self.assertEqual(adapter.expected(CASE), ROW)
        negative_zero = adapter.Case("model_adapters", (64, -(1 << 63)))
        self.assertEqual(adapter.expected(negative_zero), [0, 0, 1 << 63, 1 << 63, 0])
        signed_nan = adapter.Case("model_adapters", (64, 0xfff0000000000001))
        self.assertEqual(adapter.expected(signed_nan),
                         [0xfff0000000000001] + [0x7ff8000000000000] * 4)
        with self.assertRaises(AssertionError):
            adapter.independent_checks(CASE, [1] * 5)
        with self.assertRaises(ValueError):
            adapter.independent_checks(CASE, [True] * 5)

    def test_every_column_path_and_matching_wrong_oracle(self):
        with adapter.profile() as metadata:
            rows = {path: [list(ROW)] for path in ("lean", "compiled", "rocq")}
            self.assertEqual(core.compare([CASE], rows), [])
            self.assertEqual(metadata["oracle_assertions"], 5)
            self.assertEqual(metadata["out_of_range_cases"], 1)
            self.assertEqual(metadata["distinct_route_cases"], 1)
            self.assertFalse(metadata["native_float_ffi"])
            for path in ("lean", "compiled"):
                for column in range(5):
                    changed = {name: [list(ROW)] for name in rows}
                    changed[path][0][column] += 1
                    self.assertEqual(core.compare([CASE], changed)[0]["paths"], [path])
            for column in range(5):
                changed = list(ROW)
                changed[column] += 1
                with self.assertRaises(AssertionError):
                    core.compare([CASE], {name: [list(changed)] for name in rows})
                self.assertEqual(metadata["oracle_failure_case"], adapter.asdict(CASE))

    def test_profile_restores_bindings_on_exception(self):
        before = vars(core).copy()
        with self.assertRaisesRegex(RuntimeError, "deliberate"):
            with adapter.profile():
                self.assertEqual(core.Case, adapter.Case)
                raise RuntimeError("deliberate")
        self.assertEqual([key for key, value in before.items() if getattr(core, key) is not value], [])


@unittest.skipUnless(os.environ.get("FLOCQ_AUDIT_DIR"), "live tests require FLOCQ_AUDIT_DIR")
class LiveTests(unittest.TestCase):
    def test_policy_boundaries_and_bootstrap(self):
        cases = [CASE, adapter.Case("model_adapters", (64, -(1 << 63))),
                 adapter.Case("model_adapters", (64, 0xfff0000000000001))]
        flocq = Path(os.environ["FLOCQ_AUDIT_DIR"]).resolve()
        with adapter.profile(), tempfile.TemporaryDirectory(prefix="floatspec-model-adapter-live-") as directory:
            rows = core.execute(cases, flocq, core.configured_coqc(flocq), Path(directory))
            self.assertEqual(rows["rocq"][0], ROW)
            self.assertEqual(core.compare(cases, rows), [])
            core.bootstrap_lean(cases, rows["rocq"], Path(directory))

    def test_every_live_column_in_both_widths(self):
        header = adapter.LEAN_HEADER
        for width in (32, 64):
            header = header.replace(f"def modelAdapterObserve{width} :=",
                                    f"def originalObserve{width} :=")
            header += f"""
def modelAdapterObserve{width} (bits : Int) : List Int :=
  (originalObserve{width} bits).mapIdx fun index value =>
    if index == bits.toNat then value + 1 else value
"""
        cases = [adapter.Case("model_adapters", (width, column))
                 for width in (32, 64) for column in range(5)]
        flocq = Path(os.environ["FLOCQ_AUDIT_DIR"]).resolve()
        with (adapter.profile(), patch.object(core, "LEAN_HEADER", header),
              tempfile.TemporaryDirectory(prefix="floatspec-model-adapter-mutations-") as directory):
            rows = core.execute(cases, flocq, core.configured_coqc(flocq), Path(directory))
            mismatches = core.compare(cases, rows)
            self.assertEqual(len(mismatches), 10)
            for case, mismatch in zip(cases, mismatches, strict=True):
                self.assertEqual(mismatch["paths"], ["lean", "compiled"])
                for path in ("lean", "compiled"):
                    self.assertEqual([index for index, (left, right) in
                                      enumerate(zip(mismatch[path], mismatch["rocq"], strict=True))
                                      if left != right], [case.args[1]])

    def test_kernel_rejects_wrong_wrapping_expectation(self):
        with adapter.profile(), tempfile.TemporaryDirectory(prefix="floatspec-model-adapter-bootstrap-control-") as directory:
            with self.assertRaisesRegex(RuntimeError, "is false"):
                core.bootstrap_lean([CASE], [[1] * 5], Path(directory))
            core.bootstrap_lean([CASE], [ROW], Path(directory))


if __name__ == "__main__":
    unittest.main()
