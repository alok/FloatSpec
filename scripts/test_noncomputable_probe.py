"""Checks for the report-only noncomputable probe: scripts/noncomputable_probe.py
and its Lean template scripts/NoncomputableProbe.lean.

The live test compiles a module in which every declaration has a known verdict
and runs the real probe on it. The other tests check tag attribution, the
census shape, the summaries and the self-check without running Lean."""

import os
from pathlib import Path
import re
import tempfile
import unittest
from unittest.mock import patch

import noncomputable_probe as probe
from flocq_bridge import ROOT, run

SAMPLE = '''namespace NcProbeSample

/-- Removable on its own. -/
noncomputable def alone : Nat := 1

/-- Removable only together with `alone`. -/
noncomputable def jointly : Nat := alone + 1

/-- Needs `Classical.choice`. -/
noncomputable def chosen : Nat := Classical.choice ⟨0⟩

/-- Needs `chosen`. -/
noncomputable def viaChosen : Nat := chosen + 1

/-- Private, so its name has a `_private` prefix. -/
private noncomputable def hidden : Nat := Classical.choice ⟨1⟩

/-- Needs `hidden`. -/
@[reducible] noncomputable def viaHidden : Nat := hidden + 1

/-- Its auxiliary `outer.go` is tagged too. -/
noncomputable def outer : Nat := go 1
where
  /-- Needs `chosen`. -/
  go (n : Nat) : Nat := n + chosen

/-- A Prop-valued class. -/
class Good : Prop where
  ok : True

/-- A theorem, since `Good` is a `Prop`: the code generator never compiles it. -/
noncomputable instance goodInst : Good := ⟨trivial⟩

/-- Its kernel body uses `Nat.brecOn`, which the code generator cannot compile. -/
noncomputable def recursiveTagged : Nat → Nat
  | 0 => 0
  | n + 1 => recursiveTagged n + 1

/-- Blocked only by a candidate the probe cannot decide. -/
noncomputable def viaRecursive : Nat := recursiveTagged 3

/-- A computable control. -/
def control (n : Nat) : Nat := n + 1

/-- A computable recursive control, compiled from its `_unsafe_rec`. -/
def recursive : Nat → Nat
  | 0 => 0
  | n + 1 => recursive n + 1

noncomputable section

/-- Not noncomputable by its own modifiers: the section tags it. -/
def sectionTagged : Nat := chosen

/-- Compiles, so the section leaves it untagged. -/
def sectionComputable : Nat := 3

end

end NcProbeSample
'''
# name: (kind, status, joint_only, root_cause, source)
EXPECTED = {
    'NcProbeSample.alone': ('def', 'removable', False, '', 'explicit'),
    'NcProbeSample.jointly': ('def', 'removable', True, '', 'explicit'),
    'NcProbeSample.chosen': ('def', 'necessary', False, 'Classical.choice', 'explicit'),
    'NcProbeSample.viaChosen': ('def', 'necessary', False, 'Classical.choice', 'explicit'),
    '_private.NcProbeSample.0.NcProbeSample.hidden':
        ('def', 'necessary', False, 'Classical.choice', 'explicit'),
    'NcProbeSample.viaHidden': ('def', 'necessary', False, 'Classical.choice', 'explicit'),
    'NcProbeSample.outer': ('def', 'necessary', False, 'Classical.choice', 'explicit'),
    'NcProbeSample.outer.go': ('def', 'necessary', False, 'Classical.choice', 'inherited'),
    'NcProbeSample.goodInst': ('instance', 'removable', False, '', 'explicit'),
    'NcProbeSample.recursiveTagged': ('def', 'inconclusive', False, '', 'explicit'),
    'NcProbeSample.viaRecursive': ('def', 'inconclusive', False, '', 'explicit'),
    'NcProbeSample.sectionTagged':
        ('def', 'necessary', False, 'Classical.choice', 'noncomputable-section'),
}


def report(*candidates: dict, failed: tuple = (), compiled: int = 1,
           modules: tuple = ('M',), version: str = '4.34.0') -> dict:
    return {'lean_version': version, 'modules': list(modules), 'candidates': list(candidates),
            'controls': {'compiled': compiled, 'failed': list(failed), 'recursive_not_copied': []}}


def candidate(name: str, status: str, module: str = 'M', line: int = 1, alone: bool = True,
              root: str = '', theorem: bool = False) -> dict:
    return {'name': name, 'module': module, 'start': [line, 0], 'selection': [line, 18],
            'kind': 'def', 'theorem': theorem, 'status': status, 'removable_alone': alone,
            'blame': root, 'root_cause': root, 'result_type': 'Nat', 'error': ''}


class LiveProbeTests(unittest.TestCase):
    """The real probe, through the kernel and code generator, on SAMPLE."""

    @classmethod
    def setUpClass(cls):
        cls.directory = tempfile.TemporaryDirectory(prefix='floatspec-noncomputable-sample-')
        root = Path(cls.directory.name)
        source = root / 'NcProbeSample.lean'
        source.write_text(SAMPLE)
        run(['lake', 'env', 'lean', '-DwarningAsError=true', '-R', str(root),
             '-o', str(root / 'NcProbeSample.olean'), str(source)], timeout=600)
        with patch.dict(os.environ, {'LEAN_PATH': str(root)}):
            cls.report = probe.probe(['NcProbeSample'], ['NcProbeSample'], timeout=600)
        cls.rows = {row.name: row for row in probe.rows(cls.report, root)}

    @classmethod
    def tearDownClass(cls):
        cls.directory.cleanup()

    def test_every_verdict(self):
        self.assertEqual(set(self.rows), set(EXPECTED), 'exactly the tagged declarations')
        for name, expected in EXPECTED.items():
            row = self.rows[name]
            with self.subTest(name=name):
                self.assertEqual((row.kind, row.status, row.joint_only, row.root_cause, row.source),
                                 expected)
                self.assertEqual(row.file, 'NcProbeSample.lean')

    def test_details(self):
        items = {item['name']: item for item in self.report['candidates']}
        self.assertTrue(items['NcProbeSample.goodInst']['theorem'])
        self.assertTrue(items['NcProbeSample.alone']['removable_alone'])
        # The blame names the original, even for a private constant.
        self.assertEqual(items['NcProbeSample.viaHidden']['blame'],
                         '_private.NcProbeSample.0.NcProbeSample.hidden')
        self.assertEqual(items['NcProbeSample.viaRecursive']['blame'], 'NcProbeSample.recursiveTagged')
        self.assertIn('brecOn', items['NcProbeSample.recursiveTagged']['error'])
        # A declaration's line is where its docstring starts, as in the census.
        self.assertEqual(self.rows['NcProbeSample.alone'].line, 3)
        self.assertEqual(self.report['modules'], ['NcProbeSample'])
        self.assertEqual(self.report['controls'], {
            'compiled': 2, 'failed': [], 'recursive_not_copied': ['NcProbeSample.recursive']})
        self.assertEqual(probe.self_check(self.report, ['NcProbeSample']), [])


class TemplateTests(unittest.TestCase):
    def test_no_kernel_bypass(self):
        # Copies must reach the kernel; scripts/audit_placeholders.sh names these escapes.
        source = probe.PROBE.read_text()
        self.assertIsNone(re.search(r'\bskipKernelTC\b|\baddDecl(WithoutChecking|Core)\b|\bdoCheck\b',
                                    source))
        self.assertIn('addDecl decl', source)

    def test_source_imports_modules_and_sets_projects(self):
        source = probe.probe_source(['A.B', 'C'], ['A', 'C'])
        self.assertTrue(source.startswith('import A.B\nimport C\nimport Lean\n'))
        self.assertIn('def projects : Array Name := #[`A, `C]\n', source)
        self.assertNotIn(probe.PROJECTS_LINE, source)
        with patch.object(probe, 'PROBE', Path(os.devnull)), self.assertRaises(ValueError):
            probe.probe_source(['A'], ['A'])

    def test_probe_output_is_one_json_document(self):
        with patch.object(probe, 'run', return_value='warning: x\n{}\n'), \
                self.assertRaises(RuntimeError):
            probe.probe(['A'], ['A'], timeout=1)
        with patch.object(probe, 'run', return_value='{"modules": ["A"]}\n'):
            self.assertEqual(probe.probe(['A'], ['A'], timeout=1), {'modules': ['A']})

    def test_project_modules_cover_every_file(self):
        modules = probe.project_modules()
        self.assertEqual(modules, sorted(set(modules)))
        self.assertIn('FloatSpec', modules)
        self.assertIn('FloatSpec.src.Core.Raux', modules)
        self.assertIn('FloatSpec.Test.ZauxSource', modules)
        for module in modules:
            with self.subTest(module=module):
                self.assertTrue((ROOT / probe.module_file(module)).is_file())


class AttributionTests(unittest.TestCase):
    def test_strip_comments_keeps_positions(self):
        text = ('/-- noncomputable /- nested -/ still -/ def a := "x -- y" -- noncomputable\n'
                "def b := '\"' /- noncomputable -/\ndef c' := 1\n")
        stripped = probe.strip_comments(text)
        self.assertEqual(len(stripped), len(text))
        self.assertEqual([len(line) for line in stripped.split('\n')],
                         [len(line) for line in text.split('\n')])
        self.assertNotIn('noncomputable', stripped)
        self.assertNotIn('"', stripped)
        self.assertIn("def c' := 1", stripped)
        self.assertEqual(stripped.count('def'), 3)

    def test_tag_source(self):
        code = probe.strip_comments(
            '/-- Not noncomputable. -/\n'            # 1
            'def a := 1\n'                           # 2
            '@[simp] private noncomputable def b := 1\n'  # 3
            'noncomputable section\n'                # 4
            'namespace N\n'                          # 5
            'def c := 1\n'                           # 6
            'end N\n'                                # 7
            'def d := 1\n'                           # 8
            'end\n'                                  # 9
            'def e := 1\n')                          # 10
        self.assertEqual(probe.tag_source(code, [1, 0], [2, 4]), 'inherited')
        self.assertEqual(probe.tag_source(code, [3, 0], [3, 34]), 'explicit')
        self.assertEqual(probe.tag_source(code, [6, 0], [6, 4]), 'noncomputable-section')
        self.assertEqual(probe.tag_source(code, [8, 0], [8, 4]), 'noncomputable-section')
        self.assertEqual(probe.tag_source(code, [10, 0], [10, 4]), 'inherited')
        self.assertEqual(probe.tag_source(code, None, None), 'inherited')

    def test_open_sections(self):
        code = 'noncomputable section A\nsection\nmutual\nend\nend\nend A\n'
        self.assertEqual([probe.open_noncomputable_sections(code, line) for line in range(1, 8)],
                         [0, 1, 1, 1, 1, 1, 0])


class ReportTests(unittest.TestCase):
    def setUp(self):
        self.directory = tempfile.TemporaryDirectory()
        self.addCleanup(self.directory.cleanup)
        self.root = Path(self.directory.name)
        (self.root / 'M.lean').write_text('noncomputable def a := 1\nnoncomputable def b := 1\n'
                                          'noncomputable def c := 1\n')

    def test_rows_and_tsv(self):
        table = probe.rows(report(candidate('c', 'necessary', line=3, root='Real.sqrt'),
                                  candidate('a', 'removable', alone=False),
                                  candidate('b', 'inconclusive', line=2, alone=False)), self.root)
        self.assertEqual([row.name for row in table], ['a', 'b', 'c'])
        self.assertEqual([row.joint_only for row in table], [True, False, False])
        self.assertEqual(table[0].tsv(), 'M.lean:1\ta\tdef\tremovable\ttrue\t\tNat\texplicit')
        spaced = probe.Row('F.lean', 1, 'n', 'def', 'necessary', False, 'r', 'A\t→\nB', 'explicit')
        self.assertEqual(spaced.tsv().split('\t'),
                         ['F.lean:1', 'n', 'def', 'necessary', 'false', 'r', 'A → B', 'explicit'])
        with self.assertRaises(ValueError):
            probe.rows(report(candidate('a', 'maybe')), self.root)

    def test_summary_and_baseline(self):
        data = report(candidate('a', 'removable'), candidate('b', 'removable', line=2, theorem=True),
                      candidate('c', 'necessary', line=3, root='Real.sqrt'))
        table = probe.rows(data, self.root)
        summary = probe.summarize(table, data)
        self.assertEqual(summary['totals'], {'tagged': 3, 'removable': 2, 'necessary': 1,
                                             'inconclusive': 0, 'joint_only': 0})
        self.assertEqual(summary['root_causes'], {'Real.sqrt': 1})
        self.assertEqual(summary['theorems'], 1)
        census = self.root / 'census.tsv'
        census.write_text('\t'.join(probe.COLUMNS) + '\n'
                          'M.lean:1\ta\tdef\tremovable\tfalse\t\tNat\texplicit\n'
                          'M.lean:2\tb\tdef\tnecessary\tfalse\tReal.sqrt\tNat\texplicit\n'
                          'N.lean:4\td\tdef\tremovable\tfalse\t\tNat\texplicit\n')
        change = probe.compare(table, probe.read_census(census))
        self.assertEqual(change['new_removable'], ['b'])
        self.assertEqual(change['per_file'], {
            'M.lean': {'tagged_before': 2, 'removable_before': 1, 'tagged': 3, 'removable': 2},
            'N.lean': {'tagged_before': 1, 'removable_before': 1, 'tagged': 0, 'removable': 0}})
        text = probe.render(summary, table, [], ['M.lean', 'Z.lean'], change)
        self.assertIn('     0         0         0            0  Z.lean', text)
        self.assertIn('newly removable: 1\n  b', text)
        census.write_text('file\tname\n')
        with self.assertRaises(ValueError):
            probe.read_census(census)

    def test_self_check(self):
        self.assertEqual(probe.self_check(report(), ['M']), [])
        problems = probe.self_check(report(failed=({'name': 'f', 'error': 'boom'},), compiled=0),
                                    ['M', 'N'])
        self.assertEqual(problems, ['the probe did not load N',
                                    'control f did not compile as a copy: boom',
                                    'no control compiled; the probe checked nothing'])
        self.assertEqual(probe.self_check(report(version='4.35.0'), ['M']), [
            'the probe is pinned to Lean 4.34.x; review scripts/NoncomputableProbe.lean '
            'against Lean 4.35.0'])


if __name__ == '__main__':
    unittest.main()
