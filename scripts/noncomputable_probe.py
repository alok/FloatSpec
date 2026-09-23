#!/usr/bin/env python3
"""Report which `noncomputable` declarations the code generator really needs.

Lean never warns about an unneeded `noncomputable`. This runs
scripts/NoncomputableProbe.lean, which copies every tagged FloatSpec constant
(references to other tagged constants redirected to their copies), sends each
copy through the kernel with an ordinary `addDecl`, and asks the real code
generator to compile it, in dependency order. Each tagged declaration gets one
status:

- removable: the keyword can be deleted. `joint_only` marks one that compiles
  only once other removable keywords in the same change are deleted too. A
  tagged theorem is removable: the code generator never compiles theorems.
- necessary: the code generator needs a constant it cannot compile;
  `root_cause` names it after following the chain through other candidates.
- inconclusive: the probe could not decide (the kernel rejected the copy, the
  code generator failed for another reason, such as a recursive definition's
  kernel body, or only such a candidate blocks it).

`--output DIR` writes the report in the shape of the 2026-09-22 census:
`census.tsv` (`file:line`, name, kind, status, joint_only, root_cause,
result_type, source) and `report.json` with per-file counts. `source` says
where the tag comes from: `explicit` (the declaration's own `noncomputable`
modifier), `noncomputable-section` (an enclosing `noncomputable section` tagged
it after compilation failed), or `inherited` (neither, such as a `where`
auxiliary). `--only FILE` narrows the printed table to the files a change
touches, and `--baseline CENSUS` compares with an earlier census.tsv and lists
the declarations that became removable.

Report-only: removable and inconclusive declarations never fail the run. It
exits 1 only when the probe cannot vouch for itself: it runs on another Lean
than 4.34, it did not load a FloatSpec module, or the copy of a computable
(non-recursive) control definition does not compile.
"""

from __future__ import annotations

import argparse
from collections import Counter
from dataclasses import dataclass
import json
from pathlib import Path
import re
import sys
import tempfile

from flocq_bridge import ROOT, lean_source_fingerprint, require_lean_source_snapshot, run

PROBE = ROOT / 'scripts/NoncomputableProbe.lean'
BUILD_TARGETS = ['FloatSpec.Test', 'FloatSpecTests', 'floatspec']
COLUMNS = ['file:line', 'name', 'kind', 'status', 'joint_only', 'root_cause', 'result_type', 'source']
STATUSES = ('removable', 'necessary', 'inconclusive')
# The probe reads Lean compiler internals (see its docstring); review it before
# trusting it on another toolchain.
PINNED_LEAN = '4.34.'


@dataclass(frozen=True)
class Row:
    """One tagged declaration, as the census reports it."""
    file: str
    line: int
    name: str
    kind: str
    status: str
    joint_only: bool
    root_cause: str
    result_type: str
    source: str

    def tsv(self) -> str:
        fields = [f'{self.file}:{self.line}', self.name, self.kind, self.status,
                  str(self.joint_only).lower(), self.root_cause, self.result_type, self.source]
        return '\t'.join(' '.join(field.split()) for field in fields)


def project_modules(root: Path = ROOT) -> list[str]:
    """Every FloatSpec module: the root module and each file under FloatSpec/."""
    modules = ['.'.join(path.relative_to(root).with_suffix('').parts)
               for path in (root / 'FloatSpec').rglob('*.lean')]
    return sorted({'FloatSpec', *modules})


def module_file(module: str) -> str:
    return '/'.join(module.split('.')) + '.lean'


def strip_comments(text: str) -> str:
    """Blank out Lean comments (nested block comments included) and string
    literals, keeping every other character and every newline in place."""
    out, index, depth, length = [], 0, 0, len(text)
    while index < length:
        char, pair = text[index], text[index:index + 2]
        if depth:
            if pair == '/-':
                depth, step = depth + 1, 2
            elif pair == '-/':
                depth, step = depth - 1, 2
            else:
                step = 1
            out.append(''.join(c if c == '\n' else ' ' for c in text[index:index + step]))
            index += step
        elif pair == '/-':
            depth = 1
            out.append('  ')
            index += 2
        elif pair == '--':
            end = text.find('\n', index)
            end = length if end < 0 else end
            out.append(' ' * (end - index))
            index = end
        elif char == '"':
            end = index + 1
            while end < length and text[end] != '"':
                end += 2 if text[end] == '\\' else 1
            end = min(end + 1, length)
            out.append(''.join(c if c == '\n' else ' ' for c in text[index:end]))
            index = end
        elif char == "'" and (index == 0 or not (text[index - 1].isalnum() or text[index - 1] in "_'!?.")):
            literal = re.match(r"'(?:\\.[^']*|[^'\\\n])'", text[index:])
            if literal:
                out.append(' ' * len(literal[0]))
                index += len(literal[0])
            else:
                out.append(char)
                index += 1
        else:
            out.append(char)
            index += 1
    return ''.join(out)


SCOPE = re.compile(r'^[ \t]*(?:(noncomputable)[ \t]+)?(section|namespace|mutual|end)\b')


def open_noncomputable_sections(code: str, line: int) -> int:
    """How many `noncomputable section`s are open just before 1-based `line`
    of comment-stripped `code`. `end` closes the innermost section, namespace
    or `mutual` block."""
    stack: list[bool] = []
    for text in code.split('\n')[:line - 1]:
        match = SCOPE.match(text)
        if match is None:
            continue
        if match[2] == 'end':
            if stack:
                stack.pop()
        else:
            stack.append(match[2] == 'section' and match[1] is not None)
    return sum(stack)


def offset(lines: list[str], position: list[int]) -> int:
    """Character offset of a Lean (1-based line, codepoint column) position."""
    line, column = position
    return sum(len(text) + 1 for text in lines[:line - 1]) + column


def tag_source(code: str, start: list[int] | None, selection: list[int] | None) -> str:
    """Where a declaration's `noncomputable` tag comes from; `code` is the
    comment-stripped file. The modifiers lie between the declaration's start
    and its name."""
    if start is None or selection is None:
        return 'inherited'
    lines = code.split('\n')
    if re.search(r'\bnoncomputable\b', code[offset(lines, start):offset(lines, selection)]):
        return 'explicit'
    if open_noncomputable_sections(code, start[0]):
        return 'noncomputable-section'
    return 'inherited'


def rows(report: dict, source_root: Path = ROOT) -> list[Row]:
    """Census rows for the probe's candidates, in file and line order."""
    code: dict[str, str] = {}
    result = []
    for item in report['candidates']:
        if item['status'] not in STATUSES:
            raise ValueError(f'unknown probe status {item["status"]!r} for {item["name"]}')
        path = module_file(item['module'])
        if path not in code:
            source = source_root / path
            code[path] = strip_comments(source.read_text()) if source.is_file() else ''
        start = item['start']
        result.append(Row(
            file=path, line=start[0] if start else 0, name=item['name'], kind=item['kind'],
            status=item['status'],
            joint_only=item['status'] == 'removable' and not item['removable_alone'],
            root_cause=item['root_cause'], result_type=item['result_type'],
            source=tag_source(code[path], start, item['selection']) if code[path] else 'inherited'))
    return sorted(result, key=lambda row: (row.file, row.line, row.name))


def self_check(report: dict, modules: list[str]) -> list[str]:
    """Why the probe cannot vouch for its report: another toolchain than the one
    it was written against, a module it did not load, or a computable definition
    whose copy did not compile (the method fails on that shape, so its verdicts
    on that shape cannot be trusted)."""
    problems = [] if report['lean_version'].startswith(PINNED_LEAN) else [
        f'the probe is pinned to Lean {PINNED_LEAN}x; review scripts/NoncomputableProbe.lean '
        f'against Lean {report["lean_version"]}']
    problems += [f'the probe did not load {module}'
                 for module in sorted(set(modules) - set(report['modules']))]
    problems += [f'control {item["name"]} did not compile as a copy: {item["error"]}'
                 for item in report['controls']['failed']]
    if not report['controls']['compiled']:
        problems.append('no control compiled; the probe checked nothing')
    return problems


def read_census(path: Path) -> dict[str, tuple[str, str]]:
    """(file, status) of each declaration in a census.tsv from an earlier run."""
    lines = path.read_text().splitlines()
    if not lines or lines[0].split('\t') != COLUMNS:
        raise ValueError(f'{path} is not a noncomputable census: expected columns {COLUMNS}')
    census = {}
    for line in lines[1:]:
        fields = line.split('\t')
        census[fields[1]] = (fields[0].rsplit(':', 1)[0], fields[3])
    return census


def compare(table: list[Row], baseline: dict[str, tuple[str, str]]) -> dict:
    """Change against a baseline census: counts per file, and the declarations
    that are removable now but were not (a batch must never add one)."""
    per_file: dict[str, list[int]] = {}
    for path, status in baseline.values():
        counts = per_file.setdefault(path, [0, 0, 0, 0])
        counts[0] += 1
        counts[1] += status == 'removable'
    for row in table:
        counts = per_file.setdefault(row.file, [0, 0, 0, 0])
        counts[2] += 1
        counts[3] += row.status == 'removable'
    return {
        'per_file': {path: dict(zip(('tagged_before', 'removable_before', 'tagged', 'removable'),
                                    counts))
                     for path, counts in sorted(per_file.items()) if counts[:2] != counts[2:]},
        'new_removable': [row.name for row in table if row.status == 'removable'
                          and baseline.get(row.name, ('', ''))[1] != 'removable'],
    }


def summarize(table: list[Row], report: dict) -> dict:
    per_file: dict[str, Counter] = {}
    for row in table:
        counts = per_file.setdefault(row.file, Counter())
        counts['tagged'] += 1
        counts[row.status] += 1
        counts['joint_only'] += row.joint_only
    totals = Counter()
    for counts in per_file.values():
        totals.update(counts)
    return {
        'totals': {key: totals[key] for key in ('tagged', *STATUSES, 'joint_only')},
        'per_file': {path: {key: counts[key] for key in ('tagged', *STATUSES, 'joint_only')}
                     for path, counts in sorted(per_file.items())},
        'sources': dict(sorted(Counter(row.source for row in table).items())),
        'root_causes': dict(Counter(row.root_cause for row in table
                                    if row.status == 'necessary').most_common()),
        'theorems': sum(item['theorem'] for item in report['candidates']),
        'controls': {'compiled': report['controls']['compiled'],
                     'failed': len(report['controls']['failed']),
                     'recursive_not_copied': len(report['controls']['recursive_not_copied'])},
    }


PROJECTS_LINE = 'def projects : Array Name := #[`FloatSpec]\n'


def probe_source(modules: list[str], projects: list[str]) -> str:
    """The probe template, importing `modules` and examining `projects`."""
    source = PROBE.read_text()
    if source.count(PROJECTS_LINE) != 1:
        raise ValueError('probe template changed; review its projects line')
    source = source.replace(PROJECTS_LINE, 'def projects : Array Name := #[' +
                            ', '.join(f'`{project}' for project in projects) + ']\n')
    return ''.join(f'import {module}\n' for module in modules) + source


def probe(modules: list[str], projects: list[str], timeout: int) -> dict:
    """Run the Lean probe; its stdout must be exactly one JSON document."""
    with tempfile.TemporaryDirectory(prefix='floatspec-noncomputable-probe-') as temporary:
        path = Path(temporary) / 'NoncomputableProbeRun.lean'
        path.write_text(probe_source(modules, projects))
        output = run(['lake', 'env', 'lean', str(path)], timeout=timeout)
    lines = output.splitlines()
    if len(lines) != 1:
        raise RuntimeError(f'the probe printed {len(lines)} lines, expected one JSON document:\n'
                           f'{output[:4000]}')
    return json.loads(lines[0])


def render(summary: dict, table: list[Row], problems: list[str], only: list[str],
           change: dict | None = None) -> str:
    totals = summary['totals']
    controls = summary['controls']
    lines = [f'noncomputable probe: {totals["tagged"]} tagged; {totals["removable"]} removable '
             f'({totals["joint_only"]} only jointly, {summary["theorems"]} theorems), '
             f'{totals["necessary"]} necessary, {totals["inconclusive"]} inconclusive',
             f'controls: {controls["compiled"]} compiled, {controls["failed"]} failed, '
             f'{controls["recursive_not_copied"]} recursive not copied',
             'tagged removable necessary inconclusive  file']
    empty = dict.fromkeys(('tagged', *STATUSES), 0)
    for path in (sorted(only) if only else summary['per_file']):
        counts = summary['per_file'].get(path, empty)
        lines.append(f'{counts["tagged"]:6} {counts["removable"]:9} {counts["necessary"]:9} '
                     f'{counts["inconclusive"]:12}  {path}')
    lines.append('necessary, by root cause:')
    lines += [f'{count:6}  {cause}' for cause, count in summary['root_causes'].items()]
    inconclusive = [row for row in table if row.status == 'inconclusive'
                    and (not only or row.file in only)]
    if inconclusive:
        lines.append('inconclusive:')
        lines += [f'  {row.file}:{row.line} {row.name}' for row in inconclusive]
    if change is not None:
        lines.append('against the baseline (tagged, removable): before -> now')
        lines += [f'  {counts["tagged_before"]}, {counts["removable_before"]} -> '
                  f'{counts["tagged"]}, {counts["removable"]}  {path}'
                  for path, counts in change['per_file'].items() if not only or path in only]
        lines.append(f'newly removable: {len(change["new_removable"])}')
        lines += [f'  {name}' for name in change['new_removable']]
    lines += [f'error: {problem}' for problem in problems]
    return '\n'.join(lines)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument('--skip-build', action='store_true',
                        help='probe existing build outputs; the caller must have built current sources')
    parser.add_argument('--output', type=Path,
                        help='directory for census.tsv and report.json')
    parser.add_argument('--only', action='append', default=[], metavar='FILE',
                        help='limit the printed per-file table to FILE, a path such as '
                             'FloatSpec/src/Core/Raux.lean (repeatable)')
    parser.add_argument('--baseline', type=Path, metavar='CENSUS',
                        help='census.tsv of an earlier run: print per-file changes and the '
                             'declarations that became removable')
    parser.add_argument('--timeout', type=int, default=7200, help='seconds for the Lean probe')
    args = parser.parse_args(argv)
    for path in args.only:
        if not (ROOT / path).is_file():
            parser.error(f'--only {path}: no such file under {ROOT}')
    baseline = read_census(args.baseline) if args.baseline else None
    snapshot = lean_source_fingerprint()
    if not args.skip_build:
        run(['lake', 'build', *BUILD_TARGETS], timeout=7200)
    modules = project_modules()
    report = probe(modules, ['FloatSpec'], args.timeout)
    require_lean_source_snapshot(snapshot)
    table = rows(report)
    summary = summarize(table, report)
    problems = self_check(report, modules)
    change = compare(table, baseline) if baseline is not None else None
    if args.output:
        args.output.mkdir(parents=True, exist_ok=True)
        (args.output / 'census.tsv').write_text(
            '\n'.join(['\t'.join(COLUMNS), *(row.tsv() for row in table)]) + '\n')
        (args.output / 'report.json').write_text(json.dumps({
            'lean_source_sha256': snapshot, 'fresh_build': not args.skip_build,
            'lean_version': report['lean_version'], 'modules': sorted(report['modules']),
            **summary,
            'inconclusive': [{key: item[key] for key in ('name', 'module', 'blame', 'error')}
                             for item in report['candidates'] if item['status'] == 'inconclusive'],
            'recursive_controls': report['controls']['recursive_not_copied'],
            'control_failures': report['controls']['failed'],
            'baseline': change, 'problems': problems}, indent=2) + '\n')
    print(render(summary, table, problems, args.only, change))
    return 1 if problems else 0


if __name__ == '__main__':
    sys.exit(main())
