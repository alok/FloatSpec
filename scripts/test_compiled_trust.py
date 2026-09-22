"""Positive controls for the compiled trust gate, including opaque proof debt."""

import json
from pathlib import Path
import tempfile
import unittest

import check_compiled_trust as checker
from flocq_bridge import ROOT, run


class CompiledTrustTests(unittest.TestCase):
    def test_test_scope_imports_all_modules_and_checks_both_filters(self):
        source = checker.audit_source('tests', {'FloatSpec.Test.Zed', 'FloatSpec.Test.First'})
        self.assertTrue(source.startswith('import FloatSpec.Test.First\nimport FloatSpec.Test.Zed\n'))
        self.assertEqual(source.count('"FloatSpec.Test."'), 2)
        self.assertNotIn('"FloatSpec.src."', source)
        with self.assertRaises(ValueError):
            checker.audit_source('unrecognized', set())

    def clean_report(self):
        return {"project_declarations": 1, "source_modules": ["FloatSpec.src.Example"],
                "project_axioms": [], "unsafe_declarations": [], "runtime_overrides": [],
                "direct_sorry": ["Example.pending"], "transitive_sorry": ["Example.pending"],
                "unexpected_axiom_dependencies": []}

    def test_strict_manifest_module_and_hazard_validation(self):
        debts = [{"lean_name": "Example.pending"}]
        modules = {"FloatSpec.src.Example"}
        self.assertEqual(checker.validate(self.clean_report(), debts, modules), [])
        for field, value in (("project_declarations", 0), ("source_modules", []),
                             ("project_axioms", ["bad"]), ("unsafe_declarations", ["bad"]),
                             ("runtime_overrides", ["bad"]), ("direct_sorry", []),
                             ("transitive_sorry", ["Example.pending", "Example.wrapper"]),
                             ("unexpected_axiom_dependencies", [{"axioms": ["bad"]}])):
            with self.subTest(field=field):
                report = self.clean_report()
                report[field] = value
                self.assertTrue(checker.validate(report, debts, modules))
        self.assertTrue(checker.validate(self.clean_report(), debts * 2, modules))

    def test_actual_theorem_opaque_and_transitive_dependencies(self):
        fixture = """
namespace AuditFixture
axiom bad : True
theorem throughBad : True := bad
theorem pending : True := by sorry
opaque opaquePending : Nat := by sorry
theorem throughPending : True := pending
theorem nativeProof : (1 : Nat) + 1 = 2 := by native_decide
unsafe def runtimeValue : Nat := 0
@[implemented_by runtimeValue] def overridden : Nat := 1
@[extern "audit_fixture_foreign"] opaque foreignValue : Nat := 0
end AuditFixture
"""
        source = (ROOT / "scripts/AuditCompiledTrust.lean").read_text()
        source = source.replace("open Lean Elab Command", fixture + "\nopen Lean Elab Command")
        source = source.replace('if origin.toString.startsWith "FloatSpec.src." then',
                                'if name.toString.startsWith "AuditFixture." then')
        with tempfile.TemporaryDirectory(prefix="floatspec-compiled-trust-") as directory:
            path = Path(directory) / "TrustFixture.lean"
            path.write_text(source)
            output = run(["lake", "env", "lean", str(path)], timeout=120)
        # Intentional sorry/unused-variable warnings can arrive after run_cmd's
        # JSON because Lean elaboration is asynchronous. Require one JSON row.
        reports = [line for line in output.splitlines() if line.startswith("{")]
        self.assertEqual(len(reports), 1, output)
        report = json.loads(reports[0])
        self.assertIn("AuditFixture.bad", report["project_axioms"])
        self.assertTrue(any(name.startswith("AuditFixture.nativeProof.")
                            for name in report["project_axioms"]))
        self.assertIn("AuditFixture.runtimeValue", report["unsafe_declarations"])
        self.assertEqual(report["runtime_overrides"],
                         ["AuditFixture.foreignValue", "AuditFixture.overridden"])
        self.assertEqual(report["direct_sorry"],
                         ["AuditFixture.opaquePending", "AuditFixture.pending"])
        self.assertEqual(report["transitive_sorry"],
                         ["AuditFixture.opaquePending", "AuditFixture.pending", "AuditFixture.throughPending"])
        self.assertIn({"declaration": "AuditFixture.throughBad", "axioms": ["AuditFixture.bad"]},
                      report["unexpected_axiom_dependencies"])
        self.assertTrue(any(row["declaration"] == "AuditFixture.nativeProof"
                            for row in report["unexpected_axiom_dependencies"]))
        self.assertTrue(checker.validate(report, [], set(report["source_modules"])))


if __name__ == "__main__":
    unittest.main()
