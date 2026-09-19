"""Compiler metadata regressions for source anchors, including old text-scan bypasses."""

import json
from pathlib import Path
import tempfile
import unittest

from flocq_bridge import ROOT, run
import validate_flocq_source_refs as validator


class ReferenceTests(unittest.TestCase):
    def test_apostrophes_are_part_of_the_declaration_name(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "src").mkdir()
            (root / "src/Probe.v").write_text("Definition SF2B' x := x.\n")
            reference = {"lean_name": "probe", "path": "src/Probe.v", "line": 1, "name": "SF2B'"}
            self.assertEqual(validator.validate_references([reference], root), [])
            self.assertTrue(validator.validate_references([{**reference, "name": "SF2B"}], root))

    def test_paths_lines_and_names(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "src").mkdir()
            (root / "src/Probe.v").write_text("Definition valid := 1.\n")
            good = {"lean_name": "probe", "path": "src/Probe.v", "line": 1, "name": "valid"}
            self.assertEqual(validator.validate_references([good], root), [])
            for change in ({"path": "src/../outside.v"}, {"path": "/src/Probe.v"},
                           {"line": 0}, {"line": True}, {"line": 2},
                           {"name": "wrong"}, {"path": "src/Missing.v"}):
                with self.subTest(change=change):
                    self.assertTrue(validator.validate_references([{**good, **change}], root))
            self.assertTrue(validator.validate_references([], root))

    def test_compiler_sees_combined_and_post_declaration_attributes_not_comments(self):
        exporter = (ROOT / "scripts/ExportFlocqSources.lean").read_text()
        fixture = '''
-- @[flocq_source "src/Commented.v" 1 "not_a_definition"]
@[inline, flocq_source "src/Probe.v" 1 "valid"]
def combinedSourceProbe : Nat := 1
def laterSourceProbe : Nat := 2
attribute [flocq_source "src/Missing.v" 1 "absent"] laterSourceProbe
'''
        with tempfile.TemporaryDirectory(prefix="floatspec-source-metadata-") as directory:
            root = Path(directory)
            path = root / "Probe.lean"
            path.write_text(exporter.replace("open Lean Elab Command", fixture + "\nopen Lean Elab Command"))
            manifest = json.loads(run(["lake", "env", "lean", str(path)]))
            refs = [ref for ref in manifest["references"]
                    if ref["lean_name"] in ("combinedSourceProbe", "laterSourceProbe")]
            self.assertEqual(len(refs), 2)
            self.assertFalse(any(ref["name"] == "not_a_definition" for ref in manifest["references"]))
            # The old regular expression sees only the commented-out annotation,
            # missing both actual source links in this valid Lean fixture.
            self.assertEqual([match["name"] for match in validator.SOURCE_REF.finditer(fixture)],
                             ["not_a_definition"])
            (root / "src").mkdir()
            (root / "src/Probe.v").write_text("Definition valid := 1.\n")
            failures = validator.validate_references(refs, root)
            self.assertEqual(len(failures), 1)
            self.assertIn("laterSourceProbe: missing Flocq source", failures[0])


if __name__ == "__main__":
    unittest.main()
