"""Compiler metadata regressions for source anchors, including old text-scan bypasses."""

import json
from pathlib import Path
import tempfile
import unittest

from flocq_bridge import ROOT, run
import validate_flocq_source_refs as validator


class ReferenceTests(unittest.TestCase):
    def test_imported_simple_notation_alias_is_a_real_source_anchor(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "src").mkdir()
            (root / "src/Probe.v").write_text(
                "Notation iter_pos := SpecFloat.iter_pos (only parsing).\n")
            ref = {"lean_name": "probe", "path": "src/Probe.v", "line": 1, "name": "iter_pos"}
            self.assertEqual(validator.validate_references([ref], root), [])
            self.assertTrue(validator.validate_references([{**ref, "name": "iter"}], root))

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



class QuoteTests(unittest.TestCase):
    """`coq` docstring quotes must reproduce the pinned source from the anchored line."""

    REFS = [{"lean_name": "Ns.probeLemma", "path": "src/Probe.v", "line": 2, "name": "probe_lemma"}]
    SOURCE = "(* header *)\nTheorem probe_lemma :\n  forall x : nat, x = x.\nProof. auto. Qed.\n"
    QUOTE = "```coq {anchor}\nTheorem probe_lemma :\n  forall x : nat, x = x.\n```\n"

    def check(self, lean_text: str) -> tuple[list[str], int]:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "src").mkdir()
            (root / "src/Probe.v").write_text(self.SOURCE)
            lean = root / "Probe.lean"
            lean.write_text(lean_text)
            return validator.validate_quotes([lean], self.REFS, root, root)

    def test_verbatim_quote_by_coq_lean_and_suffix_name(self):
        for anchor in ("probe_lemma", "Ns.probeLemma", "probeLemma"):
            with self.subTest(anchor=anchor):
                text = "/--\nDoc.\n\n" + self.QUOTE.format(anchor=anchor) + "-/\ndef x := 1\n"
                self.assertEqual(self.check(text), ([], 1))

    def test_indented_quote_is_compared_after_removing_the_fence_indent(self):
        quote = "".join("  " + line + "\n" for line in
                        self.QUOTE.format(anchor="probe_lemma").splitlines())
        self.assertEqual(self.check("/--\n" + quote + "-/\n"), ([], 1))

    def test_drift_unknown_and_missing_anchors_fail(self):
        cases = {
            "not verbatim": self.QUOTE.format(anchor="probe_lemma").replace("x = x", "x = 0"),
            "names no compiled Flocq anchor": self.QUOTE.format(anchor="probe_lemmas"),
            "names no Flocq anchor": self.QUOTE.format(anchor="").replace("coq \n", "coq\n"),
            "unterminated": "```coq probe_lemma\nTheorem probe_lemma :\n",
        }
        for message, block in cases.items():
            with self.subTest(message=message):
                failures, checked = self.check("/--\n" + block + "-/\n")
                self.assertEqual(checked, 0)
                self.assertTrue(any(message in failure for failure in failures), failures)

    def test_quotes_that_guard_msgs_expects_to_fail_are_skipped(self):
        bad = self.QUOTE.format(anchor="probe_lemma").replace("x = x", "x = 0")
        text = ("/--\nerror: expected\n-/\n#guard_msgs in\nset_option doc.verso true in\n/--\n" +
                bad + "-/\ndef x := 1\n")
        self.assertEqual(self.check(text), ([], 0))
        # The same block outside `#guard_msgs` is checked, and fails.
        self.assertTrue(self.check("set_option doc.verso true in\n/--\n" + bad + "-/\n")[0])

    def test_source_file_list_must_match_the_tracked_sources(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "src/Core").mkdir(parents=True)
            (root / "src/Core/A.v").write_text("")
            (root / "src/B.v").write_text("")
            (root / "src/README").write_text("")
            run(["git", "-C", str(root), "init", "--quiet"])
            run(["git", "-C", str(root), "add", "src"])
            # Generated by configure after checkout; not part of the pinned commit.
            (root / "src/Version.v").write_text("")
            tracked = validator.tracked_rocq_sources(root)
            self.assertEqual(tracked, ["src/B.v", "src/Core/A.v"])
            self.assertEqual(validator.validate_source_files(["src/B.v", "src/Core/A.v"], tracked), [])
            for files in (["src/B.v"], ["src/B.v", "src/Core/A.v", "src/Version.v"],
                          ["src/B.v", "src/B.v", "src/Core/A.v"]):
                with self.subTest(files=files):
                    self.assertTrue(validator.validate_source_files(files, tracked))

    def test_every_repository_quote_block_parses(self):
        # An opener the quote pattern cannot parse would escape the verbatim check.
        for path in validator.lean_files(ROOT):
            text = path.read_text(encoding="utf-8")
            self.assertEqual(len(list(validator.QUOTE.finditer(text))),
                             len(validator.QUOTE_OPENER.findall(text)), path)


if __name__ == "__main__":
    unittest.main()
