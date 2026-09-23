"""Compiler metadata regressions for source anchors, including old text-scan bypasses."""

import json
from pathlib import Path
import re
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
    """`coq` docstring quotes are checked as Lean compiled them, against the anchor Lean chose."""

    SOURCE = ("(* header *)\nTheorem probe_lemma :\n  forall x : nat, x = x.\nProof. auto. Qed.\n"
              "Definition other := 1.\n")
    REFS = [{"lean_name": "Ns.probeLemma", "path": "src/Probe.v", "line": 2, "name": "probe_lemma"},
            {"lean_name": "Other.probeLemma", "path": "src/Other.v", "line": 1,
             "name": "probe_lemma"}]
    BODY = "Theorem probe_lemma :\n  forall x : nat, x = x.\n"

    @staticmethod
    def quote(code: str, lean_line: int = 3, path: str = "src/Probe.v", line: int = 2) -> dict:
        return {"lean_line": lean_line, "cited": "probe_lemma", "coq_name": "probe_lemma",
                "path": path, "line": line, "lean_names": ["Ns.probeLemma"], "code": code}

    def check(self, lean_text: str, quotes: list[dict]) -> tuple[list[str], int]:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "src").mkdir()
            (root / "src/Probe.v").write_text(self.SOURCE)
            (root / "src/Other.v").write_text("Theorem probe_lemma :\n  forall y : nat, y = y.\n")
            lean = root / "Probe.lean"
            lean.write_text(lean_text)
            return validator.validate_quotes([lean], {lean: quotes}, self.REFS, root, root)

    def doc(self, fence: str = "```coq probe_lemma") -> str:
        return "/--\nDoc.\n" + fence + "\n" + self.BODY + "```\n-/\ndef x := 1\n"

    def test_verbatim_quote_at_its_fence_passes(self):
        self.assertEqual(self.check(self.doc(), [self.quote(self.BODY)]), ([], 1))

    def test_quote_is_compared_with_the_anchor_lean_chose(self):
        # Two Coq files declare `probe_lemma`. The compiled quote names the file its link points
        # at; text copied from the other file fails even though it matches an anchor of that name.
        other = "Theorem probe_lemma :\n  forall y : nat, y = y.\n"
        failures, checked = self.check(self.doc(), [self.quote(other)])
        self.assertEqual(checked, 0)
        self.assertIn("is not verbatim src/Probe.v:2", failures[0])
        self.assertEqual(self.check(self.doc(), [self.quote(other, path="src/Other.v", line=1)]),
                         ([], 1))

    def test_drift_truncation_and_foreign_anchors_fail(self):
        cases = {
            "is not verbatim": self.quote(self.BODY.replace("x = x", "x = 0")),
            "stops inside the Rocq sentence": self.quote("Theorem probe_lemma :\n"),
            "not a compiled anchor": self.quote(self.BODY, line=3),
        }
        for message, quote in cases.items():
            with self.subTest(message=message):
                failures, checked = self.check(self.doc(), [quote])
                self.assertEqual(checked, 0)
                self.assertTrue(any(message in failure for failure in failures), failures)
        failures, _ = self.check(self.doc(), [])
        self.assertIn("not a compiled Flocq quote", failures[0])
        failures, _ = self.check(self.doc(), [self.quote(self.BODY, lean_line=4)])
        self.assertTrue(any("the build is stale" in failure for failure in failures), failures)

    def test_marked_shortening_and_whole_proofs_are_verbatim_quotes(self):
        shortened = "Theorem probe_lemma :\n...\n"
        through_qed = self.BODY + "Proof. auto. Qed.\n"
        for code in (shortened, through_qed):
            with self.subTest(code=code):
                self.assertEqual(self.check(self.doc(), [self.quote(code)]), ([], 1))

    def test_every_quote_like_fence_is_found(self):
        for fence in ("```coq probe_lemma", "``` coq probe_lemma", "* ```coq probe_lemma",
                      "  - ```coq probe_lemma", "> ```coq probe_lemma", "1. ```coq probe_lemma",
                      "~~~coq probe_lemma", "````coq", "```coq"):
            with self.subTest(fence=fence):
                self.assertEqual(validator.quote_fence_lines(self.doc(fence)), [3])
        for text in ('  return header ++ #["", "```coq"]', "```coqc", "```lean", "text ```coq x"):
            with self.subTest(text=text):
                self.assertEqual(validator.quote_fence_lines(text), [])

    def test_plain_blocks_may_not_quote_flocq(self):
        # A `(* Flocq src/...` location line marks an unchecked quote of Flocq, wherever it sits
        # in a plain block. A Rocq core library quote, located by `(* Rocq ...`, stays allowed.
        rocq = ("```\n(* Rocq V9.1.0 theories/Corelib/Floats/SpecFloat.v:36-37 *)\n"
                "  Definition emin := 1.\n")
        flocq = "(* Flocq src/Probe.v:2-3 (7aab8f55) *)\n" + self.BODY
        for block, line in (("```\n" + flocq + "```\n", 4), (rocq + flocq + "```\n", 6),
                            ("> ~~~\n> (* Flocq src/Probe.v:2-3 *)\n> ~~~\n", 4),
                            ("* ```\n  (*Flocq src/Probe.v:2 *)\n  ```\n", 4)):
            with self.subTest(block=block):
                failures, checked = self.check("/--\nDoc.\n" + block + "-/\ndef x := 1\n", [])
                self.assertEqual(checked, 0)
                self.assertEqual(len(failures), 1, failures)
                self.assertIn(f"Probe.lean:{line}: a `(* Flocq src/...` location line",
                              failures[0])
        self.assertEqual(self.check("/--\nDoc.\n" + rocq + "```\n-/\ndef x := 1\n", []), ([], 0))
        # Naming the form in prose, or in a string, is not a quote.
        for text in ("  a `(* Flocq src/...` line\n", 'text "(* Flocq src/X.v *)"\n',
                     "(* Flocq's src/X.v *)\n"):
            with self.subTest(text=text):
                self.assertEqual(validator.flocq_location_lines(text), [])

    def test_lean_and_python_accept_the_same_declaration_keywords(self):
        roles = (ROOT / "FloatSpecRoles.lean").read_text()
        def lean_list(name: str) -> list[str]:
            body = re.search(name + r" : List String :=\s*\[(.*?)\]", roles, re.S)
            assert body, name
            return re.findall(r'"([^"]+)"', body.group(1))
        pattern = validator.COQ_DECL.pattern
        modifiers = re.search(r"\(\?:\(\?:([A-Za-z|]+)\)", pattern).group(1).split("|")
        keywords = re.search(r"\(\?:(Definition[A-Za-z|]+)\)", pattern.replace('"', "").replace(
            "\n", "")).group(1).split("|")
        self.assertEqual(lean_list("vernacularModifiers"), modifiers)
        self.assertEqual(lean_list("vernacularKeywords"), keywords)

    def test_compiled_quotes_follow_the_namespace_that_resolved_them(self):
        # `Bcompare` is declared in two Flocq files. Lean resolves the anchor through the current
        # namespace, and the exported quote records the file it chose, which the validator uses.
        probe = """import FloatSpec

namespace BinarySingleNaN
set_option doc.verso true in
/--
```coq Bcompare
Definition Bcompare (f1 f2 : binary_float) : option comparison :=
```
-/
def quotedHere : Unit := ()
end BinarySingleNaN

namespace Binary
set_option doc.verso true in
/--
```coq Bcompare
Definition Bcompare (f1 f2 : binary_float) : option comparison :=
```
-/
def quotedHere : Unit := ()
end Binary
"""
        with tempfile.TemporaryDirectory(prefix="floatspec-quote-probe-") as directory:
            path = Path(directory) / "QuoteProbe.lean"
            path.write_text(probe)
            quotes = validator.standalone_quotes(path)
        self.assertEqual([(q["lean_line"], q["path"], q["line"], q["lean_names"]) for q in quotes],
                         [(6, "src/IEEE754/BinarySingleNaN.v", 559, ["BinarySingleNaN.Bcompare"]),
                          (16, "src/IEEE754/Binary.v", 773, ["Binary.Bcompare"])])

    def test_source_file_list_must_match_the_committed_sources(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "src/Core").mkdir(parents=True)
            (root / "src/Core/A.v").write_text("")
            (root / "src/B.v").write_text("")
            (root / "src/README").write_text("")
            run(["git", "-C", str(root), "init", "--quiet"])
            run(["git", "-C", str(root), "add", "src"])
            run(["git", "-C", str(root), "-c", "user.name=probe", "-c", "user.email=probe@invalid",
                 "commit", "--quiet", "-m", "pin"])
            # Generated by configure after checkout, or staged but not committed: neither is in
            # the pinned tree.
            (root / "src/Version.v").write_text("")
            (root / "src/Staged.v").write_text("")
            run(["git", "-C", str(root), "add", "src/Staged.v"])
            tracked = validator.tracked_rocq_sources(root)
            self.assertEqual(tracked, ["src/B.v", "src/Core/A.v"])
            self.assertEqual(validator.validate_source_files(["src/B.v", "src/Core/A.v"], tracked), [])
            for files in (["src/B.v"], ["src/B.v", "src/Core/A.v", "src/Version.v"],
                          ["src/B.v", "src/B.v", "src/Core/A.v"]):
                with self.subTest(files=files):
                    self.assertTrue(validator.validate_source_files(files, tracked))


if __name__ == "__main__":
    unittest.main()
