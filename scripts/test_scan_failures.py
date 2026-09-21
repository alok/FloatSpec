"""Audit tools must distinguish a clean scan from an unavailable/failed search."""

import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest


ROOT = Path(__file__).resolve().parents[1]


class ScanFailures(unittest.TestCase):
    def run_script(self, script, *args, path=None):
        env = os.environ.copy()
        if path is not None:
            env["PATH"] = path
        return subprocess.run(["/bin/bash", str(ROOT / "scripts" / script), *args],
                              cwd=ROOT, env=env, text=True, capture_output=True, timeout=30)

    def test_missing_ripgrep_is_not_a_clean_scan(self):
        with tempfile.TemporaryDirectory() as empty_path:
            for script in ("audit_placeholders.sh", "test_unused_mvcgen.sh"):
                with self.subTest(script=script):
                    result = self.run_script(script, path=empty_path)
                    self.assertEqual(result.returncode, 2)
                    self.assertIn("prerequisite missing: rg", result.stderr)
                    self.assertNotIn("passed", result.stdout)

    def test_missing_input_is_an_error_in_both_output_modes(self):
        with tempfile.TemporaryDirectory() as directory:
            missing = str(Path(directory) / "NotPresent.lean")
            for args in ([], ["--json"]):
                with self.subTest(args=args):
                    result = self.run_script("audit_placeholders.sh", *args, missing)
                    self.assertEqual(result.returncode, 2)
                    self.assertIn("ripgrep failed", result.stderr)
                    self.assertNotIn("findings", result.stdout)

    def test_search_errors_are_not_treated_as_no_matches(self):
        for code in (2, 127):
            with tempfile.TemporaryDirectory() as directory:
                stub = Path(directory) / "rg"
                stub.write_text(f"#!/bin/sh\nexit {code}\n")
                stub.chmod(0o755)
                path = directory + os.pathsep + os.environ["PATH"]
                for script in ("audit_placeholders.sh", "test_unused_mvcgen.sh"):
                    with self.subTest(script=script, code=code):
                        result = self.run_script(script, path=path)
                        self.assertEqual(result.returncode, code)
                        self.assertIn(f"ripgrep failed (status {code})", result.stderr)

    def test_text_pattern_search_errors_are_not_swallowed(self):
        real_rg = shutil.which("rg")
        self.assertIsNotNone(real_rg)
        with tempfile.TemporaryDirectory() as directory:
            stub = Path(directory) / "rg"
            # Permit source collection, fail the subsequent text-pattern query.
            stub.write_text('#!/bin/sh\nif [ "$2" = "-H" ]; then\n'
                            '  exec "$REAL_RG" "$@"\nfi\nexit 2\n')
            stub.chmod(0o755)
            env = dict(os.environ, REAL_RG=real_rg,
                       PATH=directory + os.pathsep + os.environ["PATH"])
            result = subprocess.run(["/bin/bash", str(ROOT / "scripts/audit_placeholders.sh"),
                                     str(ROOT / "scripts/fixtures/audit/Extern.lean")],
                                    cwd=ROOT, env=env, text=True, capture_output=True, timeout=30)
            self.assertEqual(result.returncode, 2)
            self.assertIn("ripgrep failed", result.stderr)
            self.assertNotIn("No placeholder-pattern findings", result.stdout)

    def test_empty_and_clean_inputs_still_pass(self):
        with tempfile.TemporaryDirectory() as directory:
            for args in ([], ["--json"]):
                result = self.run_script("audit_placeholders.sh", *args, directory)
                self.assertEqual(result.returncode, 0, result.stderr)
            path = Path(directory) / "Clean.lean"
            path.write_text("def clean : Nat := 42\n")
            result = self.run_script("audit_placeholders.sh", "--json", "--fail-on-findings", str(path))
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertIn('"findings": []', result.stdout)


if __name__ == "__main__":
    unittest.main()
