"""Fail closed when hosted CI would leave an existing check unrun.

CI discovers fixtures by glob and runs every live module listed by
run_required_rocq_tests. These controls keep that coverage complete and
unconditional: a new live test module, test script, fixture, replay or local
conformance command cannot land unrun; a fixture that defines `main` cannot be
merely elaborated; a test module CI invokes must run all of its tests; and no
trigger filter, `if:` condition or shell construct can switch a required
command off or swallow its failure. This module runs in CI's first step after
checkout, whose log the evidence step requires. The workflow and the local
driver are read with strict parsers for the YAML and bash subsets they use, so
an unfamiliar construct fails here instead of being misread.
"""

import ast
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import textwrap
import unittest

from run_required_rocq_tests import EXCLUDED_MODULES, LIVE_MODULES

ROOT = Path(__file__).resolve().parent.parent
SCRIPTS = ROOT / 'scripts'
FIXTURES = SCRIPTS / 'fixtures'
CI = ROOT / '.github/workflows/ci.yml'
CONFORMANCE = SCRIPTS / 'test_flocq_conformance.sh'
REFERENCE = 'FLOCQ_AUDIT_DIR'
THIS = Path(__file__).resolve()

# Test entry points CI does not invoke by name, and why each is not a gap.
NOT_INVOKED_BY_CI = {
    'test_flocq_conformance.sh':
        'local all-in-one driver; ConformanceDriverTests accounts for each of its commands',
}
# Random corpora the local driver runs and hosted CI does not yet. CI runs each
# bridge's boundary and mutation cases through its live test module, and the
# flocq_bridge.py grid at --samples 5. Local times: 2026-09-22, --skip-build,
# under heavy machine load.
LOCAL_CORPORA = {
    'flocq_bridge.py': '--samples 100 grid: about 35,600 cases, about 130 min',
    'native_ieee_bridge.py': 'random binary32/binary64 corpus; always rebuilds Lean',
    'native_arithmetic_bridge.py': 'random arithmetic corpus; always rebuilds Lean',
    'ieee_modes_bridge.py': '470 cases, 998 s',
    'ieee_scale_bridge.py': '2,360 cases, 616 s',
    'ieee_integer_bridge.py': '1,460 cases, 340 s',
    'pff_bridge.py': '2,672 cases, 608 s',
    'pff_aux_bridge.py': '2,116 cases, 302 s',
    'pff_integer_bridge.py': '1,172 cases, 119 s',
    'zaux_prelude_bridge.py': '1,244 cases, 120 s',
    'remainder_bridge.py': '12,100 cases, 550 s',
    'model_adapter_bridge.py': '740 cases, 243 s',
}
# Modules outside the required runner that may still skip, and why.
ALLOWED_SKIPS = {
    'test_required_rocq_tests': 'controls skip and expect failure to prove the runner rejects both',
}
# The only step conditions: saving a fresh cache, and uploading evidence of a failed run.
ALLOWED_CONDITIONS = {
    ('actions/cache/save@v4', "steps.rocq-cache.outputs.cache-hit != 'true'"),
    ('actions/upload-artifact@v4', 'always()'),
}
SKIP = re.compile(r'\bskip(?:If|Unless)?\s*\(|\.skipTest\s*\(|\bSkipTest\b|\bexpectedFailure\b')
MAIN = re.compile(r'^(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|unsafe|partial|noncomputable)\s+)*'
                  r'def\s+main\b', re.M)
# Under `bash -eo pipefail`, these are the ways a command's failure is lost or
# skipped. A command negated with `!` never trips errexit, whatever its result;
# an `if !`, `while !` or `until !` condition is exempt, like any condition.
SWALLOWS = re.compile(r'&&|\|\|(?! status=\$\?$)|(?<![>&])&(?![>&])|<<|\w\s*\(\)|continue-on-error'
                      r'|(?:^|[;|({]|\b(?:then|do|else))\s*'
                      r'(?:(?:exit|return|set|shopt|trap|eval|source|function)\b|!(?=\s))', re.M)
INVOCATION = r'(?:opam exec --switch=floatspec-rocq -- )?(?:python3 )?scripts/'
# A test script invocation and its arguments, up to any output redirection.
TEST_INVOCATION = re.compile(rf'{INVOCATION}(test_\w+\.(?:py|sh))((?:\s+[^\s|>]+)*?)(?:\s+2>&1)?(?:\s*\|.*)?')

# Steps pinned command for command; `{executables}` is derived from the fixtures.
LEAN_GATE = (r"rg -n 'warningAsError|#guard_msgs|#exit|\baxiom\b|implemented_by|\bextern\b"
             r"|native_decide|decide\s*\+native|native\s*:=\s*true|ofReduceBool|skipKernelTC"
             r"|addDecl(WithoutChecking|Core)|doCheck|setEnv|modifyEnv|run_(cmd|elab|meta)"
             r"|sorryAx|drop\s+(all|error|warning)' scripts/fixtures/*.lean || status=$?")
ROCQ_GATE = (r"rg -n '\b(Admitted|Admit|admit|Abort|Axioms?|Parameters?|Conjectures?|Declare)\b"
             r"|native_compute|native_cast_no_check|Unset (Guard|Positivity|Universe) Checking"
             r"|bypass_check' scripts/fixtures/*.v || status=$?")
PINNED_STEPS = {
    'Check that CI runs every check': [
        'python3 scripts/test_ci_coverage.py -v 2>&1 | tee "$FLOCQ_CI_OUTPUT/ci-coverage.log"',
    ],
    'Run every Lean regression fixture': [
        'status=0', LEAN_GATE, 'test "$status" -eq 1',
        "executable_fixtures='{executables}'",
        'oleans="$(mktemp -d)"',
        'for path in scripts/fixtures/*.lean; do',
        'fixture="$(basename "$path" .lean)"',
        'echo "== $fixture"',
        'if [[ "$executable_fixtures" == *" $fixture "* ]]; then',
        'lake env lean -DwarningAsError=true -o "$oleans/$fixture.olean" --run "$path"',
        'else',
        'lake env lean -DwarningAsError=true -o "$oleans/$fixture.olean" "$path"',
        'fi',
        'done 2>&1 | tee "$FLOCQ_CI_OUTPUT/lean-fixtures.log"',
        'lake env lean --run scripts/KernelReplay.lean "$oleans"/*.olean 2>&1 '
        '| tee -a "$FLOCQ_CI_OUTPUT/lean-fixtures.log"',
        'lake exe floatspec_demo 2>&1 | tee -a "$FLOCQ_CI_OUTPUT/lean-fixtures.log"',
    ],
    'Run pure Rocq regressions': [
        'mkdir -p "$FLOCQ_CI_OUTPUT/rocq"',
        'status=0', ROCQ_GATE, 'test "$status" -eq 1',
        "opam exec --switch=floatspec-rocq -- bash -euo pipefail -c ' "
        'for path in scripts/fixtures/*.v; do fixture="$(basename "$path" .v)" '
        'echo "== $fixture" coqc -q -R Deps/flocq/src Flocq \\ '
        '-o "$FLOCQ_CI_OUTPUT/rocq/$fixture.vo" "$path" done '
        '\' 2>&1 | tee "$FLOCQ_CI_OUTPUT/rocq.log"',
    ],
    'Run required live Lean and Rocq mutation tests (no skips)': [
        'opam exec --switch=floatspec-rocq -- python3 scripts/run_required_rocq_tests.py '
        '--flocq-dir Deps/flocq --output "$FLOCQ_CI_OUTPUT/required-tests.json" '
        '2>&1 | tee "$FLOCQ_CI_OUTPUT/required-tests.log"',
    ],
    'Execute the differential bridge and kernel regressions': [
        'opam exec --switch=floatspec-rocq -- python3 scripts/flocq_bridge.py '
        '--flocq-dir Deps/flocq --seed 865509 --samples 5 --batch-size 100 '
        '--operations power,div_eucl,location,round,truncate,div,plus,sqrt,formats,digits,'
        'operations,bits32,bits64 --skip-build --output "$FLOCQ_CI_OUTPUT/bridge" '
        '2>&1 | tee "$FLOCQ_CI_OUTPUT/bridge.log"',
        'for replay in RawIEEERoundingReplay RawOverflowReplay PrimitiveComparisonReplay '
        'PrimitiveConversionReplay; do',
        'opam exec --switch=floatspec-rocq -- python3 scripts/flocq_bridge.py '
        '--flocq-dir Deps/flocq --replay "scripts/fixtures/$replay.json" '
        '--skip-build --output "$FLOCQ_CI_OUTPUT/$replay" 2>&1 | tee "$FLOCQ_CI_OUTPUT/$replay.log"',
        'done',
        'opam exec --switch=floatspec-rocq -- python3 scripts/pff_bridge.py '
        '--flocq-dir Deps/flocq --replay scripts/fixtures/PffSignLawsReplay.json '
        '--skip-build --output "$FLOCQ_CI_OUTPUT/PffSignLawsReplay" '
        '2>&1 | tee "$FLOCQ_CI_OUTPUT/PffSignLawsReplay.log"',
        'opam exec --switch=floatspec-rocq -- python3 scripts/pff_integer_bridge.py '
        '--flocq-dir Deps/flocq --replay scripts/fixtures/PffIntegerReplay.json '
        '--skip-build --output "$FLOCQ_CI_OUTPUT/PffIntegerReplay" '
        '2>&1 | tee "$FLOCQ_CI_OUTPUT/PffIntegerReplay.log"',
    ],
    'Require complete cross-check evidence': [
        'missing=()',
        'if [[ "$(tail -n 1 "$FLOCQ_CI_OUTPUT/ci-coverage.log" 2>/dev/null)" != OK ]]; then',
        'missing+=("passing ci-coverage.log")',
        'fi',
        'for evidence in reference-build.log lean-fixtures.log rocq.log '
        'required-tests.json bridge/report.json; do',
        'if [[ ! -s "$FLOCQ_CI_OUTPUT/$evidence" ]]; then missing+=("$evidence"); fi',
        'done',
        'for path in scripts/fixtures/*.v; do',
        'evidence="rocq/$(basename "$path" .v).vo"',
        'if [[ ! -s "$FLOCQ_CI_OUTPUT/$evidence" ]]; then missing+=("$evidence"); fi',
        'done',
        'for path in scripts/fixtures/*.json; do',
        'evidence="$(basename "$path" .json)/report.json"',
        'if [[ ! -s "$FLOCQ_CI_OUTPUT/$evidence" ]]; then missing+=("$evidence"); fi',
        'done',
        'for evidence in "${missing[@]}"; do',
        'echo "::error::missing cross-check evidence $evidence"',
        'done',
        'test "${#missing[@]}" -eq 0',
    ],
    'Verify generated status is current': [
        'scripts/status_report.sh --write',
        'git diff --exit-code -- FloatSpec/docs/status.json FloatSpec/docs/status.md',
    ],
}

# Import every test module without the reference; report those unittest marks skipped.
SKIP_PROBE = '''
import json, sys, unittest

def cases(suite):
    for item in suite:
        if isinstance(item, unittest.TestSuite):
            yield from cases(item)
        else:
            yield item

marked = []
for name in sys.argv[1:]:
    for case in cases(unittest.defaultTestLoader.loadTestsFromName(name)):
        method = getattr(case, case._testMethodName, None)
        if getattr(type(case), "__unittest_skip__", False) or getattr(method, "__unittest_skip__", False):
            marked.append(name)
            break
print(json.dumps(marked))
'''


def load_yaml(text: str):
    """Parse block mappings, block sequences of mappings, plain scalars and `|` scalars.

    Anything else (flow collections, scalar sequence items, quoted keys,
    anchors, folded scalars, tabs, duplicate keys) raises ValueError rather
    than being guessed at.
    """
    lines, pos = text.splitlines(), 0

    def indent_here() -> int:
        nonlocal pos
        while pos < len(lines) and (not lines[pos].strip() or lines[pos].lstrip().startswith('#')):
            pos += 1
        return len(lines[pos]) - len(lines[pos].lstrip(' ')) if pos < len(lines) else -1

    def block(level: int):
        nonlocal pos
        if lines[pos][level:].startswith('- '):
            items = []
            while indent_here() == level and lines[pos][level:].startswith('- '):
                lines[pos] = lines[pos][:level] + '  ' + lines[pos][level + 2:]
                items.append(block(level + 2))
            return items
        mapping = {}
        while indent_here() == level and not lines[pos][level:].startswith('- '):
            entry = re.fullmatch(r'([A-Za-z_][\w-]*):(?: +([^\s&*!|>{\["\'#%@`].*|\|))?',
                                 lines[pos][level:])
            if entry is None or entry[1] in mapping or '\t' in lines[pos]:
                raise ValueError(f'unsupported YAML at line {pos + 1}: {lines[pos]!r}')
            key, value = entry[1], entry[2]
            pos += 1
            if value == '|':
                body = []
                while pos < len(lines) and (not lines[pos].strip()
                                            or len(lines[pos]) - len(lines[pos].lstrip(' ')) > level):
                    body.append(lines[pos])
                    pos += 1
                value = textwrap.dedent('\n'.join(body)).strip('\n') + '\n'
            elif value is None:
                child = indent_here()
                value = block(child) if child > level else None
            mapping[key] = value
        return mapping

    document = block(indent_here())
    if indent_here() != -1:
        raise ValueError(f'unsupported YAML indentation at line {pos + 1}: {lines[pos]!r}')
    return document


def shell_commands(script: str) -> list[tuple[int, str]]:
    """Split bash into logical commands, each with the control-flow depth around it.

    Comments are dropped; continuations, multi-line quotes and parentheses join
    lines. Depth counts enclosing if/for/while/until/case/select and brace
    groups, so a command inside any of them is not top level.
    """
    commands, depth, text, skeleton, quote, parens = [], 0, '', '', None, 0
    for line in script.splitlines():
        index, continued = 0, False
        while index < len(line):
            char = line[index]
            if quote:
                text += char
                if char == '\\' and quote == '"':
                    text += line[index + 1:index + 2]
                    index += 1
                elif char == quote:
                    quote = None
                    skeleton += 'Q'
            elif char == '\\' and index == len(line) - 1:
                continued = True
            elif char == '#' and (index == 0 or line[index - 1] in ' \t;|&('):
                break
            else:
                if char == '\\':
                    text += char
                    index += 1
                    char = line[index]
                elif char in '\'"':
                    quote = char
                elif char == '(':
                    parens += 1
                elif char == ')':
                    parens -= 1
                if parens < 0:
                    raise ValueError(f'unbalanced parenthesis in {line!r}')
                text += char
                skeleton += char if quote is None else ''
            index += 1
        if continued or quote or parens:
            text += ' ' if continued else '\n'
            skeleton += ' '
            continue
        if text.strip():
            commands.append((depth, text.strip()))
            for segment in re.split(r'[;&|]', skeleton):
                words = segment.split()
                while words and words[0] in ('then', 'do', 'else', 'elif', '!'):
                    words = words[1:]
                if words and words[0] in ('if', 'for', 'while', 'until', 'case', 'select'):
                    depth += 1
                elif words and words[0] in ('fi', 'done', 'esac'):
                    depth -= 1
                depth += words.count('{') - words.count('}')
            if depth < 0:
                raise ValueError(f'unbalanced control flow at {text.strip()!r}')
        text, skeleton = '', ''
    if quote or parens or depth or text:
        raise ValueError('unterminated quote, parenthesis or control structure')
    return commands


def normalized(command: str) -> str:
    return ' '.join(command.split())


def workflow() -> dict:
    return load_yaml(CI.read_text())


def steps() -> list[dict]:
    return [step for job in workflow()['jobs'].values() for step in job['steps']]


def top_level_commands() -> list[str]:
    return [command for step in steps() if 'run' in step
            for depth, command in shell_commands(step['run']) if depth == 0]


def invokes(commands: list[str], script: str) -> bool:
    """A top-level command runs the script itself, not an echo or comment naming it."""
    return any(re.match(rf'{INVOCATION}{re.escape(script)}(?=\s|$)', command) and ';' not in command
               for command in commands)


def lean_action_targets() -> list[str]:
    actions = [step for step in steps() if step.get('uses', '').startswith('leanprover/lean-action@')]
    return actions[0]['with']['build-args'].split() if len(actions) == 1 else []


def test_modules() -> list[Path]:
    return sorted(path for path in SCRIPTS.glob('test_*.py') if path.resolve() != THIS)


def skipped_without_reference() -> set[str]:
    env = {key: value for key, value in os.environ.items() if key != REFERENCE}
    process = subprocess.run(
        [sys.executable, '-c', SKIP_PROBE, *(path.stem for path in test_modules())],
        cwd=SCRIPTS, env=env, capture_output=True, text=True, timeout=120, check=True)
    return set(json.loads(process.stdout))


def runs_every_test(path: Path) -> bool:
    """The module ends by running unittest's main program, which runs every test."""
    last = ast.parse(path.read_text()).body[-1]
    return (isinstance(last, ast.If) and not last.orelse
            and ast.unparse(last.test) == "__name__ == '__main__'"
            and [ast.unparse(node) for node in last.body] == ['unittest.main()'])


def executable_fixtures() -> set[str]:
    return {path.stem for path in FIXTURES.glob('*.lean') if MAIN.search(path.read_text())}


def ci_test_modules(commands: list[str]) -> list[Path]:
    """Test scripts CI runs: those it invokes by name, and, when it invokes the
    required runner, every live module that runner loads. This policy module is
    left out: the gates it pins name fixture globs without running them."""
    paths = [path for path in sorted(SCRIPTS.glob('test_*'))
             if invokes(commands, path.name) and path.resolve() != THIS]
    if invokes(commands, 'run_required_rocq_tests.py'):
        paths += [SCRIPTS / f'{module}.py' for module in LIVE_MODULES]
    return paths


def consumes(text: str, path: Path) -> bool:
    """A test names a nested fixture by a glob over its folder, by its own path,
    or in a `for name in ...` list whose body names fixtures/<folder>/$name."""
    folder = re.escape(path.parent.relative_to(FIXTURES).as_posix())
    listed = (rf'for (\w+) in ([\w ]+); do\n(?:[^\n]*\n){{0,2}}?[^\n]*'
              rf'fixtures/{folder}/\$\1{re.escape(path.suffix)}')
    return (re.search(rf'fixtures/{folder}/(?:\*|{re.escape(path.stem)})'
                      rf'{re.escape(path.suffix)}(?![\w.])', text) is not None
            or any(path.stem in names.split() for _, names in re.findall(listed, text)))


class LiveModuleTests(unittest.TestCase):
    def test_live_modules_partition_the_reference_gated_modules(self):
        gated = {path.stem for path in test_modules() if REFERENCE in path.read_text()}
        live, excluded = set(LIVE_MODULES), set(EXCLUDED_MODULES)
        self.assertEqual(len(live), len(LIVE_MODULES), 'a live module is listed twice')
        self.assertFalse(live & excluded, 'a module is both required and excluded')
        self.assertEqual(live | excluded, gated,
                         'add each reference-gated module to LIVE_MODULES (or justify an exclusion)')
        for module, reason in EXCLUDED_MODULES.items():
            self.assertTrue(reason.strip(), f'{module} is excluded without a reason')

    def test_every_statically_skipped_module_is_required(self):
        # Catches gates that reach the reference through a helper, not by name.
        missing = skipped_without_reference() - set(LIVE_MODULES) - set(EXCLUDED_MODULES)
        self.assertEqual(missing, set(), 'these modules skip without the reference but never '
                                         'run in the required no-skip suite')

    def test_modules_outside_the_required_runner_cannot_skip(self):
        # Plain `python3 scripts/test_*.py` counts a skip as success.
        for path in test_modules():
            if path.stem in (*LIVE_MODULES, *EXCLUDED_MODULES, *ALLOWED_SKIPS):
                continue
            with self.subTest(module=path.stem):
                self.assertIsNone(SKIP.search(path.read_text()),
                                  'run this module through run_required_rocq_tests instead')

    def test_live_modules_never_expect_failure(self):
        for module in LIVE_MODULES:
            with self.subTest(module=module):
                self.assertNotIn('expectedFailure', (SCRIPTS / f'{module}.py').read_text())

    def test_tests_are_defined_unconditionally(self):
        # A class or test method defined only when a tool is present (or a
        # load_tests filter) drops tests silently, like an unmarked skip.
        control = (ast.If, ast.Try, ast.For, ast.While, ast.With, ast.Match)
        for path in [*test_modules(), THIS]:
            tree = ast.parse(path.read_text())
            hidden = [node.name for block in tree.body if isinstance(block, control)
                      for node in ast.walk(block) if isinstance(node, ast.ClassDef)]
            hidden += [node.name for cls in tree.body if isinstance(cls, ast.ClassDef)
                       for block in cls.body if isinstance(block, control)
                       for node in ast.walk(block)
                       if isinstance(node, ast.FunctionDef) and node.name.startswith('test')]
            hidden += [node.name for node in ast.walk(tree)
                       if isinstance(node, ast.FunctionDef) and node.name == 'load_tests']
            with self.subTest(module=path.stem):
                self.assertEqual(hidden, [])

    def test_every_bridge_is_exercised(self):
        commands = top_level_commands()
        for path in sorted(set(SCRIPTS.glob('*_bridge.py')) - set(SCRIPTS.glob('test_*'))):
            imported = rf'^(?:import {path.stem}\b|from {path.stem} import\b)'
            with self.subTest(bridge=path.name):
                self.assertTrue(invokes(commands, path.name) or any(
                    re.search(imported, (SCRIPTS / f'{module}.py').read_text(), re.M)
                    for module in LIVE_MODULES), 'run this bridge in CI or from a live test module')


class ParserTests(unittest.TestCase):
    def test_yaml_subset(self):
        parsed = load_yaml('a:\n  b: c  # kept\n  d:\n    - e: f\n      g: |\n        x\n\n'
                           '        # y\n    - h:\n')
        self.assertEqual(parsed, {'a': {'b': 'c  # kept',
                                        'd': [{'e': 'f', 'g': 'x\n\n# y\n'}, {'h': None}]}})
        for unsupported in ('a: [b]\n', 'a: &x b\n', 'a: >\n  b\n', 'a: b\na: c\n', '"a": b\n',
                            'a:\n  b: c\n d: e\n'):
            with self.subTest(yaml=unsupported), self.assertRaises(ValueError):
                load_yaml(unsupported)

    def test_shell_depth(self):
        script = ('a # b\nif c; then\n  d "x # y" \\\n    e\nfi\nf \'g\nh\' | i\n'
                  'for j in k; do l; done\nm && { n; }\n{\no\n}\n')
        self.assertEqual([(depth, normalized(command)) for depth, command in shell_commands(script)], [
            (0, 'a'), (0, 'if c; then'), (1, 'd "x # y" e'), (1, 'fi'), (0, "f 'g h' | i"),
            (0, 'for j in k; do l; done'), (0, 'm && { n; }'), (0, '{'), (1, 'o'), (1, '}')])
        self.assertEqual(shell_commands('f() {\n  g\n}\n'), [(0, 'f() {'), (1, 'g'), (1, '}')])
        for unsupported in ('if a; then\n', "a 'b\n", 'a )\n', 'fi\n', 'f() {\n'):
            with self.subTest(shell=unsupported), self.assertRaises(ValueError):
                shell_commands(unsupported)

    def test_swallowed_failures(self):
        for command in ('! python3 scripts/check_proof_debts.py', 'a; ! b', 'if c; then ! d; fi',
                        'for e in f; do ! g; done', '( ! h )', 'i | ! j', 'k || true', 'l && m',
                        'n &', 'set +e', 'trap x ERR', 'o || status=$?; p'):
            with self.subTest(swallows=command):
                self.assertIsNotNone(SWALLOWS.search(command))
        for command in ('if ! opam switch list --short | rg -x x; then', 'while ! a; do b; done',
                        'if [[ ! -s "$x" ]]; then y+=("$x"); fi', "rg -n '!x|y' z || status=$?",
                        'a 2>&1 | tee b', 'test "$status" -eq 1'):
            with self.subTest(keeps=command):
                self.assertIsNone(SWALLOWS.search(command))

    def test_fixture_consumption(self):
        readme, lean = FIXTURES / 'x/README.md', FIXTURES / 'x/A.lean'
        for text in ('glob("scripts/fixtures/x/*.lean")', 'fixtures/x/A.lean', 'p = "fixtures/x/A.lean"\n',
                     'for name in B A; do\n  lean "fixtures/x/$name.lean"\ndone\n'):
            with self.subTest(consumes=text):
                self.assertTrue(consumes(text, lean))
        for text in ('fixtures/x/*.v', 'fixtures/y/*.lean', 'fixtures/x/', 'fixtures/x/AB.lean',
                     'fixtures/x/A.lean.orig', 'fixtures/x/B.lean', 'x/A.lean',
                     'for name in B; do\n  lean "fixtures/x/$name.lean"\ndone\n'):
            with self.subTest(ignores=text):
                self.assertFalse(consumes(text, lean))
        self.assertTrue(consumes('FIXTURES / "fixtures/x/README.md"', readme))
        self.assertFalse(consumes('fixtures/x/*.lean', readme))

    def test_test_invocations(self):
        for command, expected in (('python3 scripts/test_a.py -v', ('test_a.py', ' -v')),
                                  ('python3 scripts/test_a.py -v 2>&1 | tee "$x/y.log"',
                                   ('test_a.py', ' -v')),
                                  ('python3 scripts/test_a.py -k b', ('test_a.py', ' -k b')),
                                  ('scripts/test_b.sh', ('test_b.sh', '')),
                                  ('opam exec --switch=floatspec-rocq -- python3 scripts/test_c.py',
                                   ('test_c.py', ''))):
            with self.subTest(command=command):
                self.assertEqual(TEST_INVOCATION.fullmatch(command).groups(), expected)


class WorkflowShapeTests(unittest.TestCase):
    def test_every_event_runs_every_job(self):
        document = workflow()
        self.assertEqual(set(document), {'name', 'on', 'permissions', 'jobs'})
        self.assertEqual(document['on'], {'push': None, 'pull_request': None},
                         'trigger filters (paths, branches, types) would skip CI for some changes')
        for name, job in document['jobs'].items():
            with self.subTest(job=name):
                self.assertLessEqual(set(job), {'runs-on', 'timeout-minutes', 'needs', 'steps'})

    def test_steps_are_unconditional(self):
        for step in steps():
            with self.subTest(step=step.get('name', step.get('uses'))):
                self.assertLessEqual(set(step), {'name', 'id', 'uses', 'with', 'run', 'shell', 'if'})
                self.assertEqual(('uses' in step) + ('run' in step), 1)
                if 'if' in step:
                    self.assertIn((step.get('uses'), step['if']), ALLOWED_CONDITIONS)
                if 'run' in step:
                    # An explicit bash shell is `bash -eo pipefail`; the default lacks pipefail.
                    self.assertEqual(step.get('shell'), 'bash')

    def test_no_command_failure_is_swallowed(self):
        self.assertNotIn('continue-on-error', CI.read_text())
        for step in steps():
            for _, command in shell_commands(step.get('run', '')):
                with self.subTest(step=step.get('name'), command=command):
                    self.assertIsNone(SWALLOWS.search(command))


class WorkflowTests(unittest.TestCase):
    def setUp(self):
        self.commands = top_level_commands()

    def step_commands(self, name: str) -> list[str]:
        [step] = [step for step in steps() if step.get('name') == name]
        return [normalized(command) for _, command in shell_commands(step['run'])]

    def test_every_test_script_runs(self):
        self.assertTrue(invokes(self.commands, 'run_required_rocq_tests.py'))
        for path in [*test_modules(), THIS, *sorted(SCRIPTS.glob('test_*.sh'))]:
            with self.subTest(script=path.name):
                if path.stem in (*LIVE_MODULES, *EXCLUDED_MODULES):
                    continue
                if path.name in NOT_INVOKED_BY_CI:
                    self.assertFalse(invokes(self.commands, path.name), 'stale exception')
                    continue
                self.assertTrue(invokes(self.commands, path.name),
                                f'run scripts/{path.name} as a top-level command in ci.yml')
        for name in NOT_INVOKED_BY_CI:
            self.assertTrue((SCRIPTS / name).is_file(), f'stale exception {name}')

    def test_invoked_tests_run_every_test(self):
        # `python3 scripts/test_x.py` runs nothing without a unittest.main()
        # block, and a `-k` or test-name argument runs only a subset.
        invoked = set()
        for command in self.commands:
            match = TEST_INVOCATION.fullmatch(command)
            if match is None:
                continue
            script, arguments = match.groups()
            invoked.add(script)
            with self.subTest(command=command):
                self.assertEqual(arguments.split(), ['-v'] if script.endswith('.py') else [])
                if script.endswith('.py'):
                    self.assertTrue(runs_every_test(SCRIPTS / script),
                                    f'end scripts/{script} with if __name__ == "__main__": unittest.main()')
        self.assertIn(THIS.name, invoked)
        self.assertTrue(runs_every_test(THIS))

    def test_coverage_check_runs_first(self):
        # Right after checkout, before the long build, and in a step of its own.
        names = [step.get('name', step.get('uses')) for step in steps()]
        self.assertEqual(names[names.index('actions/checkout@v4') + 1], 'Check that CI runs every check')

    def test_pinned_steps(self):
        # Every Lean fixture runs with warnings as errors, every Rocq fixture
        # compiles against the pin, and every piece of evidence is required.
        executables = ' ' + ' '.join(sorted(executable_fixtures())) + ' '
        for name, expected in PINNED_STEPS.items():
            with self.subTest(step=name):
                self.assertEqual(self.step_commands(name),
                                 [normalized(command.replace('{executables}', executables))
                                  for command in expected])
        self.assertIn('GuidedDemo', executable_fixtures())  # positive control for MAIN
        self.assertIn('floatspec_demo', lean_action_targets())
        self.assertEqual(sorted(FIXTURES.rglob('*.v')), sorted(FIXTURES.glob('*.v')),
                         'the CI glob does not reach Rocq fixtures in subdirectories')

    def test_fixture_gates_reject_admissions(self):
        probes = {  # gate: (lines it must reject, lines it must accept)
            LEAN_GATE: (['axiom cheat : False', '/-- error: x -/ #guard_msgs in', '#exit',
                         '@[implemented_by f] def g', '@[extern "c"] opaque h', 'by native_decide',
                         'by decide +native', 'set_option warningAsError false',
                         'Lean.ofReduceBool', 'debug.skipKernelTC', 'sorryAx',
                         'env.addDeclCore 0 0 decl none', '(doCheck := false)',
                         '@Kernel.Environment.addDeclWithoutChecking', 'setEnv env',
                         'modifyEnv (·.addExtraName n)', 'run_cmd do', 'run_elab pure ()',
                         'run_meta pure ()'],
                        ['#print axioms t', 'theorem t : 1 = 1 := by decide']),
            ROCQ_GATE: (['Admitted.', 'Admit Obligations.', 'admit.', 'Abort.', 'Axiom a : False.',
                         'Parameter p : nat.', 'Conjecture c : False.', 'Declare Instance b : B.',
                         'native_compute.', 'Unset Guard Checking.', 'bypass_check'],
                        ['Print Assumptions t.', 'Proof. vm_compute. reflexivity. Qed.']),
        }
        for gate, (bad, good) in probes.items():
            pattern, glob = re.fullmatch(r"rg -n '(.*)' (\S+) \|\| status=\$\?", gate).groups()
            for line in bad:
                with self.subTest(gate=glob, rejects=line):
                    self.assertRegex(line, pattern)
            for line in good:
                with self.subTest(gate=glob, accepts=line):
                    self.assertNotRegex(line, pattern)
            for path in FIXTURES.glob(glob.removeprefix('scripts/fixtures/')):
                with self.subTest(fixture=path.name):
                    self.assertIsNone(re.search(pattern, path.read_text()))

    def test_every_replay_fixture_is_replayed(self):
        # A replay runs as a top-level bridge command, or as the sole command of
        # a top-level `for replay in ...` loop.
        replayed = set()
        replay = rf'{INVOCATION}\w+\.py [^;]*--replay '
        for step in steps():
            commands = [(depth, normalized(command))
                        for depth, command in shell_commands(step.get('run', ''))]
            for index, (depth, command) in enumerate(commands):
                single = re.match(replay + r'scripts/fixtures/([\w-]+)\.json ', command)
                loop = re.fullmatch(r'for replay in ([\w ]+); do', command)
                body = commands[index + 1:index + 3]
                if depth == 0 and single:
                    replayed.add(single[1])
                if (depth == 0 and loop and [level for level, _ in body] == [1, 1]
                        and re.match(replay + r'"scripts/fixtures/\$replay\.json" ', body[0][1])
                        and body[1][1] == 'done'):
                    replayed.update(loop[1].split())
        self.assertEqual(replayed, {path.stem for path in FIXTURES.glob('*.json')})
        self.assertEqual(sorted(FIXTURES.rglob('*.json')), sorted(FIXTURES.glob('*.json')))

    def test_subdirectory_fixtures_are_consumed_by_ci_tests(self):
        # No CI glob reaches a nested fixture, so a test CI runs must name it.
        texts = [path.read_text() for path in ci_test_modules(self.commands)]
        nested = [path for path in FIXTURES.rglob('*')
                  if path.is_file() and path.parent != FIXTURES]
        self.assertTrue(nested)
        for path in nested:
            with self.subTest(fixture=path.relative_to(FIXTURES).as_posix()):
                self.assertTrue(any(consumes(text, path) for text in texts))

    def test_live_modules_count_as_ci_tests(self):
        # CI runs every live module through the required runner, which rejects a
        # skip or an empty module, so a live module consumes fixtures as surely
        # as a test CI invokes by name. Without the runner, none is a consumer.
        live = {SCRIPTS / f'{module}.py' for module in LIVE_MODULES}
        self.assertTrue(invokes(self.commands, 'run_required_rocq_tests.py'))
        self.assertLessEqual(live, set(ci_test_modules(self.commands)))
        without_runner = [command for command in self.commands
                          if not re.match(rf'{INVOCATION}run_required_rocq_tests\.py', command)]
        self.assertFalse(live & set(ci_test_modules(without_runner)))

    def test_evidence_upload_fails_closed(self):
        [upload] = [step for step in steps()
                    if step.get('uses', '').startswith('actions/upload-artifact@')]
        self.assertEqual(upload['with']['if-no-files-found'], 'error')
        self.assertEqual(steps()[0].get('run', '').count('FLOCQ_CI_OUTPUT='), 1,
                         'set the evidence path before checkout can fail')


class ConformanceDriverTests(unittest.TestCase):
    """The local all-in-one driver runs no check that CI does not also run,
    except the random corpora listed, with reasons, in LOCAL_CORPORA."""

    def setUp(self):
        text = CONFORMANCE.read_text()
        heredoc = r'''cat >"\$scratch/([\w.]+)" <<'(\w+)'\n(.*?\n)\2\n'''
        found = re.findall(heredoc, text, re.S)
        self.heredocs = {name: body for name, _, body in found}
        self.unrecognized_heredocs = text.count('<<') - len(found)
        self.commands = [command for _, command in
                         shell_commands(re.sub(heredoc, r'cat >"$scratch/\1"\n', text, flags=re.S))]
        self.ci = top_level_commands()

    def test_inline_sources_are_fixtures_ci_compiles(self):
        self.assertEqual(self.unrecognized_heredocs, 0,
                         'write inline sources as cat >"$scratch/NAME" <<\'TAG\'')
        for name, body in self.heredocs.items():
            with self.subTest(source=name):
                self.assertTrue((FIXTURES / name).is_file(), f'add scripts/fixtures/{name}')
                self.assertEqual((FIXTURES / name).read_text(), body,
                                 f'keep scripts/fixtures/{name} identical to the inline source')
        for command in self.commands:
            for name in re.findall(r'"\$scratch/([\w.]+\.v)"', command):
                with self.subTest(command=command):
                    self.assertIn(name, self.heredocs)

    def test_fixture_loops_match_ci(self):
        # A green local run should predict a green CI run: the same globs, the
        # same warnings-as-errors flag, and the same fixtures executed.
        executables = ' ' + ' '.join(sorted(executable_fixtures())) + ' '
        commands = [normalized(command) for command in self.commands]
        for expected in (f"executable_fixtures='{executables}'",
                         'fixture_oleans="$(mktemp -d "$scratch/oleans.XXXXXX")"',
                         'for path in "$repo_root"/scripts/fixtures/*.lean; do',
                         'run_lake env lean -DwarningAsError=true -o "$fixture_oleans/$fixture.olean" '
                         '--run "$path"',
                         'run_lake env lean -DwarningAsError=true -o "$fixture_oleans/$fixture.olean" '
                         '"$path"',
                         'run_lake env lean --run "$repo_root/scripts/KernelReplay.lean" '
                         '"$fixture_oleans"/*.olean',
                         'for path in "$repo_root"/scripts/fixtures/*.v; do',
                         '"$coqc_bin" -q -R "$flocq_dir/src" Flocq -o "$scratch/$fixture.vo" "$path"'):
            with self.subTest(command=expected):
                self.assertIn(normalized(expected), commands)
        for command in commands:
            if re.search(r'\blake env lean\b', command) and 'scripts/fixtures/' in command:
                with self.subTest(command=command):
                    self.assertIn('-DwarningAsError=true', command)

    def test_every_driver_command_is_hosted_or_accounted(self):
        known = {'set', 'trap', 'if', 'else', 'fi', 'for', 'done', 'git', 'rm', 'echo', 'exit',
                 'cat', '}', 'cleanup()', 'run_lake()', 'uv', 'python3', 'run_lake', 'lake', 'elan',
                 '"$coqc_bin"'}
        assignments = r'^(?:\w+=(?:"[^"]*"|\'[^\']*\'|[^\s"\']+)*(?:\s+|$))+'
        scripts = set()
        for command in self.commands:
            words = re.sub(assignments, '', command).split()
            with self.subTest(command=command):
                self.assertTrue(not words or words[0] in known or words[0].startswith('('),
                                'account for this new kind of driver command here')
                for subcommand in re.findall(r'(?:\brun_|\b)lake\s+(\S+)', command):
                    self.assertIn(subcommand, {'build', 'env', 'exe', '"$@"'})
                for executable in re.findall(r'(?:\brun_|\b)lake exe (\S+)', command):
                    self.assertIn(f'lake exe {executable}',
                                  [' '.join(ci.split()[:3]) for ci in self.ci])
                for module in re.findall(r'FloatSpec[/.]Test[/.](\w+)', command):
                    self.assertTrue((ROOT / f'FloatSpec/Test/{module}.lean').is_file())
                    self.assertIn('FloatSpecTests', lean_action_targets())
            scripts.update(re.findall(r'scripts/([\w-]+\.(?:py|sh))\b', command))
        for script in sorted(scripts):
            with self.subTest(script=script):
                self.assertTrue(Path(script).stem in (*LIVE_MODULES, *EXCLUDED_MODULES)
                                or invokes(self.ci, script) or script in LOCAL_CORPORA,
                                f'run scripts/{script} in ci.yml or justify it in LOCAL_CORPORA')
        for script, reason in LOCAL_CORPORA.items():
            with self.subTest(corpus=script):
                self.assertTrue(reason.strip())
                self.assertTrue(any(f'scripts/{script}' in command and '--samples' in command
                                    for command in self.commands), 'stale corpus entry')


if __name__ == '__main__':
    unittest.main()
