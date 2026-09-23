"""Batch emission, execution and per-case attribution (FLOCQSMITH.md §6).

One batch is one Rocq file (``rocq-vm``) and three Lean files (``lean-meta``:
``#reduce``; ``lean-ir``: ``lean --run``; ``lean-kernel``: ``decide
+kernel`` against the Rocq values). Every case is attributed its own outcome
on every path: Rocq cases are delimited by ``FSCASE`` markers, Lean messages
are attributed by the source line range the emitter recorded, and the
interpreter brackets each case with ``FSBEGIN`` on stderr and ``FSOUT`` on
stdout (``panic!`` does not abort, so stderr text inside a case is a failure).

Raw streams are kept next to the generated files; :func:`judge_batch` is a
pure function of them, which is what makes offline ``verify`` possible.
"""

from __future__ import annotations

from concurrent.futures import ThreadPoolExecutor
from dataclasses import dataclass, field
import ast
import hashlib
import json
from pathlib import Path
import re

from .ir import Program, signature
from .mutants import preamble_for
from .process import ProcResult, run_capture
from .render import LeanVariant, lean_file, lean_term, rocq_file, rocq_term
from .verdict import CLONE_PATHS, Outcome, Verdict, judge, meta_ir_disagreement


@dataclass(frozen=True)
class Subject:
    """One (program, Lean variant) pair; the Rocq side depends only on the program."""

    case_id: str
    program: Program
    variant: LeanVariant

    @property
    def program_sha(self) -> str:
        return self.program.sha256()


@dataclass(frozen=True)
class Toolchain:
    flocq: Path
    coqc: str
    rocq_timeout: float = 600.0
    rocq_case_timeout: int = 60
    lean_timeout: float = 900.0
    heartbeats: int = 40_000_000


@dataclass
class BatchResult:
    folder: Path
    subjects: list[Subject]
    rocq: dict[str, Outcome]
    paths: dict[str, dict[str, Outcome]]
    verdicts: dict[str, list[Verdict]]
    disagreements: list[str]
    processes: dict[str, list[dict[str, object]]] = field(default_factory=dict)


# -- Rocq --------------------------------------------------------------------

ROCQ_MARK = re.compile(r"^FSCASE (\S+)\s*$")


def parse_rocq(stdout: str, stderr: str, returncode: int | None, timed_out: bool,
               labels: list[str]) -> dict[str, Outcome]:
    """Per-case outcomes from one coqc run over ``labels`` (in file order).

    Per-case timeouts are handled inside the file by the Ltac wrapper. Any
    file-level failure (nonzero exit, stderr text, process timeout) means a
    generated term did not type-check or the reference misbehaved; the whole
    batch then fails closed as ``harness-error`` naming the last marker (§6.1).
    """
    if stderr.strip() or timed_out or returncode != 0:
        marks = [m[1] for m in (ROCQ_MARK.match(line) for line in stdout.splitlines()) if m]
        detail = ("process timeout" if timed_out else f"coqc exit {returncode}") + \
            (f"; last marker {marks[-1]}" if marks else "; no marker") + \
            (f"; stderr: {stderr.strip()[:400]}" if stderr.strip() else f"; stdout tail: {stdout[-400:]}")
        return {label: Outcome("harness", detail=detail) for label in labels}
    return _rocq_partial(stdout, labels, "missing marker")


def _rocq_partial(stdout: str, labels: list[str], failure: str) -> dict[str, Outcome]:
    blocks: dict[str, list[str]] = {}
    order: list[str] = []
    current: str | None = None
    for line in stdout.splitlines():
        mark = ROCQ_MARK.match(line)
        if mark:
            current = mark[1]
            if current in blocks:
                current = None  # duplicate marker: leave the case unresolved
                continue
            blocks[current] = []
            order.append(current)
        elif current is not None:
            blocks[current].append(line)
    outcomes: dict[str, Outcome] = {}
    for label in labels:
        lines = blocks.get(label)
        if lines is None:
            outcomes[label] = Outcome("harness", detail=f"no Rocq marker for {label}: {failure}")
            continue
        text = "\n".join(lines).strip()
        if text == "TIMEOUT":
            outcomes[label] = Outcome("infra", stage="timeout", detail="Rocq per-case timeout")
            continue
        if not text.startswith("OK"):
            outcomes[label] = Outcome("harness", detail=f"unexpected Rocq output: {text[:300]}; {failure}")
            continue
        body = text[2:].strip()
        values = _int_list(body.replace(";", ","))
        if values is None:
            outcomes[label] = Outcome("harness", detail=f"unparseable Rocq value: {body[:300]}")
        else:
            outcomes[label] = Outcome("ok", document=tuple(values))
    # A case whose marker printed but whose command aborted the file is the
    # last marker with no OK/TIMEOUT line; it was already classified above.
    return outcomes


def _int_list(text: str) -> list[int] | None:
    text = text.strip()
    if not re.fullmatch(r"\[[\s,\-0-9]*\]", text):
        return None
    value = ast.literal_eval(text)
    if not isinstance(value, list) or not all(type(n) is int for n in value):
        return None
    return value


# -- Lean messages -----------------------------------------------------------

@dataclass(frozen=True)
class Message:
    line: int
    severity: str
    kind: str
    data: str


def parse_messages(stdout: str) -> tuple[list[Message], list[str]]:
    """JSON messages from ``lean --json``, plus every non-JSON stdout line."""
    messages, other = [], []
    for line in stdout.splitlines():
        if line.startswith("{"):
            try:
                row = json.loads(line)
                messages.append(Message(int(row["pos"]["line"]), str(row["severity"]), str(row.get("kind", "")),
                                        str(row.get("data", ""))))
                continue
            except (ValueError, KeyError, TypeError):
                pass
        if line.strip():
            other.append(line)
    return messages, other


def _named_kind(kind: str) -> str:
    """``lean.synthInstanceFailed._namedError`` -> ``synthInstanceFailed``."""
    parts = [p for p in kind.split(".") if p and p not in ("lean", "_namedError")]
    return ".".join(parts) or kind


def classify_error(message: Message, path: str) -> Outcome:
    """Map one error message to an outcome by its typed kind (§7: no free text)."""
    kind = message.kind
    if kind == "runtime.maxHeartbeats":
        return Outcome("infra", stage="heartbeats", detail=message.data[:300])
    if kind == "runtime.maxRecDepth":
        return Outcome("infra", stage="max-recdepth", detail=message.data[:300])
    if kind == "lean.dependsOnNoncomputable._namedError":
        return Outcome("infra", stage="noncomputable", detail=message.data[:300])
    if kind.startswith("lean.") and kind.endswith("._namedError"):
        return Outcome("infra", stage=f"lean-elab:{_named_kind(kind)}", detail=message.data[:300])
    return Outcome("harness", detail=f"unclassified Lean error ({kind}): {message.data[:300]}")


# ``decide +kernel`` rejection texts, pinned to Lean v4.34.0 (tested). When the
# kernel rejects the proof, Lean diagnoses with elaborator reduction: it says
# "proved that the proposition ... is false" only if *Meta* can evaluate the
# instance, and "failed for proposition ... did not reduce" otherwise. Neither
# text is a kernel verdict, so a rejection is re-checked with the negated
# statement: the kernel proving ``¬ (prog = expected)`` is the mismatch.
DECIDE_REJECTION_PREFIXES = ("Tactic `decide` proved that the proposition",
                             "Tactic `decide` failed for proposition")


def is_decide_rejection(message: Message) -> bool:
    return message.kind == "[anonymous]" and message.data.startswith(DECIDE_REJECTION_PREFIXES)


def attribute(messages: list[Message], ranges: dict[str, tuple[int, int]]) -> tuple[dict[str, list[Message]], list[Message]]:
    by_case: dict[str, list[Message]] = {label: [] for label in ranges}
    stray: list[Message] = []
    for message in messages:
        owner = next((label for label, (start, end) in ranges.items() if start <= message.line <= end), None)
        (by_case[owner] if owner is not None else stray).append(message)
    return by_case, stray


def parse_meta(result: ProcResult, ranges: dict[str, tuple[int, int]]) -> dict[str, Outcome]:
    messages, other = parse_messages(result.stdout)
    by_case, stray = attribute(messages, ranges)
    global_failure = _global_failure(result, stray, other)
    outcomes: dict[str, Outcome] = {}
    for label, own in by_case.items():
        if global_failure is not None:
            outcomes[label] = global_failure
            continue
        errors = [m for m in own if m.severity == "error"]
        infos = [m for m in own if m.severity == "information"]
        if errors:
            # Decided by the first error before any information output (§6.2 hazard).
            outcomes[label] = classify_error(errors[0], "lean-meta")
        elif not own:
            outcomes[label] = (Outcome("infra", stage="timeout", detail="no output before the process timeout")
                               if result.timed_out else
                               Outcome("infra", stage="process-crash", detail=f"exit {result.returncode}")
                               if result.returncode not in (0, 1) else
                               Outcome("harness", detail="no #reduce output"))
        elif len(infos) != 1 or len(own) != 1:
            outcomes[label] = Outcome("harness", detail=f"expected one information message, got {len(own)}")
        else:
            values = _lean_int_list(infos[0].data)
            outcomes[label] = (Outcome("ok", document=tuple(values)) if values is not None else
                               Outcome("infra", stage="meta-stuck", detail=infos[0].data[:300]))
    return outcomes


def _global_failure(result: ProcResult, stray: list[Message], other: list[str]) -> Outcome | None:
    if any(m.severity == "error" for m in stray) or other:
        detail = "; ".join(m.data[:200] for m in stray)[:600] or "; ".join(other)[:600]
        return Outcome("harness", detail=f"message outside any case: {detail}")
    if result.stderr.strip() and not result.timed_out and result.returncode in (0, 1):
        return Outcome("harness", detail=f"unexpected Lean stderr: {result.stderr[:400]}")
    return None


def _lean_int_list(text: str) -> list[int] | None:
    text = re.sub(r"Int\.ofNat\s+(\d+)", r"\1", text)
    text = re.sub(r"Int\.negSucc\s+(\d+)", lambda m: str(-int(m[1]) - 1), text)
    return _int_list(text)


REJECTED = "rejected"


def parse_kernel(result: ProcResult, ranges: dict[str, tuple[int, int]]) -> dict[str, Outcome | str]:
    """Per-case kernel acceptance: ``Outcome("kernel-true")`` if the statement was
    accepted, :data:`REJECTED` if ``decide`` rejected it, else an infra/harness outcome."""
    messages, other = parse_messages(result.stdout)
    by_case, stray = attribute(messages, ranges)
    global_failure = _global_failure(result, stray, other)
    outcomes: dict[str, Outcome | str] = {}
    for label, own in by_case.items():
        errors = [m for m in own if m.severity == "error"]
        if global_failure is not None:
            outcomes[label] = global_failure
        elif errors:
            outcomes[label] = REJECTED if is_decide_rejection(errors[0]) else classify_error(errors[0], "lean-kernel")
        elif result.timed_out:
            # A successful example prints nothing, so a killed process leaves
            # every case without an error unresolved: never a match.
            outcomes[label] = Outcome("infra", stage="timeout", detail="kernel process timed out")
        elif result.returncode not in (0, 1):
            outcomes[label] = Outcome("infra", stage="process-crash", detail=f"exit {result.returncode}")
        elif own:
            outcomes[label] = Outcome("harness", detail=f"unexpected kernel message: {own[0].data[:300]}")
        else:
            outcomes[label] = Outcome("kernel-true")
    return outcomes


def combine_kernel(first: dict[str, Outcome | str], second: dict[str, Outcome | str]) -> dict[str, Outcome]:
    """Pass 1 checks ``prog = expected``; pass 2 checks ``¬ (prog = expected)`` for pass-1 rejections."""
    out: dict[str, Outcome] = {}
    for label, verdict in first.items():
        if verdict != REJECTED:
            assert isinstance(verdict, Outcome)
            out[label] = verdict
            continue
        negated = second.get(label)
        if negated is None:
            out[label] = Outcome("harness", detail="kernel rejection was not re-checked")
        elif negated == REJECTED:
            out[label] = Outcome("infra", stage="kernel-stuck",
                                 detail="decide +kernel rejected both the equation and its negation")
        elif isinstance(negated, Outcome) and negated.status == "kernel-true":
            out[label] = Outcome("kernel-false", detail="kernel proved the negation")
        else:
            assert isinstance(negated, Outcome)
            out[label] = negated
    return out


# -- lean --run ----------------------------------------------------------------

def parse_ir(result: ProcResult, labels: list[str], def_ranges: dict[str, tuple[int, int]]
             ) -> tuple[dict[str, Outcome], list[str]]:
    """Outcomes for cases that ran or failed to compile, and the labels never started."""
    messages, other = parse_messages(result.stdout)
    errors = [m for m in messages if m.severity == "error"]
    outcomes: dict[str, Outcome] = {}
    if errors:
        by_case, stray = attribute(errors, def_ranges)
        for label, own in by_case.items():
            if own:
                outcome = classify_error(own[0], "lean-ir")
                outcomes[label] = outcome
        if not outcomes:
            detail = "; ".join(m.data[:200] for m in stray)[:600]
            return {label: Outcome("harness", detail=f"IR compile failure outside cases: {detail}")
                    for label in labels}, []
        # main did not run; the compilable remainder is re-emitted once.
        return outcomes, [label for label in labels if label not in outcomes]
    outputs: dict[str, list[int] | None] = {}
    for line in other:
        mark = re.match(r"^FSOUT (\S+) (.*)$", line)
        if mark is None:
            return {label: Outcome("harness", detail=f"unexpected IR stdout: {line[:300]}") for label in labels}, []
        outputs[mark[1]] = _int_list(mark[2])
    begun: list[str] = []
    stderr_by_case: dict[str, list[str]] = {}
    current: str | None = None
    preamble: list[str] = []
    for line in result.stderr.splitlines():
        mark = re.match(r"^FSBEGIN (\S+)\s*$", line)
        if mark:
            current = mark[1]
            begun.append(current)
            stderr_by_case[current] = []
        elif current is not None:
            stderr_by_case[current].append(line)
        elif line.strip():
            preamble.append(line)
    if preamble:
        return {label: Outcome("harness", detail=f"IR stderr before any case: {preamble[0][:300]}")
                for label in labels}, []
    unstarted = []
    for label in labels:
        if label in outputs:
            values = outputs[label]
            if stderr_by_case.get(label) and any(s.strip() for s in stderr_by_case[label]):
                outcomes[label] = Outcome("infra", stage="ir-panic", detail="\n".join(stderr_by_case[label])[:300])
            elif values is None:
                outcomes[label] = Outcome("harness", detail="unparseable IR output")
            else:
                outcomes[label] = Outcome("ok", document=tuple(values))
        elif label in begun:
            outcomes[label] = (Outcome("infra", stage="timeout", detail="IR process timed out") if result.timed_out else
                               Outcome("infra", stage="ir-crash",
                                       detail=f"exit {result.returncode}: " + "\n".join(stderr_by_case.get(label, []))[-300:]))
        else:
            unstarted.append(label)
    return outcomes, unstarted


# -- emission ------------------------------------------------------------------

@dataclass
class _LeanFile:
    text: str
    ranges: dict[str, tuple[int, int]]


def _commands(entries: list[tuple[str, list[str]]], preamble: str, ir_main: list[str] | None = None) -> _LeanFile:
    """Lay out commands and record each case's inclusive line range (1-based)."""
    head = lean_file(preamble, [], ir_main=None)
    head_lines = head.count("\n") - 1  # lean_file ends with "end Bridge\n"; commands go before it
    ranges: dict[str, tuple[int, int]] = {}
    commands: list[str] = []
    line = head_lines + (1 if ir_main is not None else 0)
    for label, lines in entries:
        start = line + 1
        commands.extend(text + "\n" for text in lines)
        line += len(lines)
        ranges[label] = (start, line)
    text = lean_file(preamble, commands, ir_main=ir_main)
    return _LeanFile(text, ranges)


def meta_file(subjects: list[Subject], heartbeats: int, preamble: str) -> _LeanFile:
    entries = [(s.case_id, [f"-- FSCASE {s.case_id}", f"set_option maxHeartbeats {heartbeats} in",
                            f"#reduce ({lean_term(s.program, s.variant)} : List Int)"]) for s in subjects]
    return _commands(entries, preamble)


def ir_file(subjects: list[Subject], preamble: str) -> _LeanFile:
    entries = [(s.case_id, [f"-- FSCASE {s.case_id}", f"def fsCase{k} (_ : Unit) : List Int :=",
                            f"  {lean_term(s.program, s.variant)}"]) for k, s in enumerate(subjects)]
    main = [f"  fsEmit \"{s.case_id}\" fsCase{k}\n" for k, s in enumerate(subjects)]
    return _commands(entries, preamble, ir_main=main)


def kernel_file(subjects: list[Subject], expected: dict[str, tuple[int, ...]], heartbeats: int,
                preamble: str, negated: bool = False) -> _LeanFile:
    entries = []
    for s in subjects:
        values = "[" + ", ".join(str(n) for n in expected[s.case_id]) + "]"
        statement = f"({lean_term(s.program, s.variant)} : List Int) = {values}"
        if negated:
            statement = f"¬ ({statement})"
        entries.append((s.case_id, [f"-- FSCASE {s.case_id}", f"set_option maxHeartbeats {heartbeats} in",
                                    f"example : {statement} := by decide +kernel"]))
    return _commands(entries, preamble)


def sha256_file(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


# -- execution -----------------------------------------------------------------

def _lean(path: Path, run: bool = False) -> list[str]:
    return ["lake", "env", "lean", "--json", *(["--run"] if run else []), str(path)]


def _save(folder: Path, name: str, result: ProcResult) -> dict[str, object]:
    (folder / f"{name}.stdout").write_text(result.stdout)
    (folder / f"{name}.stderr").write_text(result.stderr)
    row = result.to_json()
    row["name"] = name
    return row


def execute_batch(subjects: list[Subject], folder: Path, tools: Toolchain,
                  paths: tuple[str, ...] = CLONE_PATHS) -> BatchResult:
    """Run every path for every subject and judge each (case, path) pair."""
    folder.mkdir(parents=True, exist_ok=False)
    labels = sorted({s.case_id for s in subjects})
    if len(labels) != len(subjects):
        raise ValueError("case ids must be unique within a batch")
    programs: dict[str, Program] = {}
    for s in subjects:
        programs.setdefault(s.program_sha, s.program)
    rocq_labels = list(programs)
    (folder / "Case.v").write_text(rocq_file([(sha[:16], rocq_term(p)) for sha, p in programs.items()],
                                             tools.rocq_case_timeout))
    preamble = preamble_for([s.variant for s in subjects])
    processes: dict[str, list[dict[str, object]]] = {}
    lean_outcomes: dict[str, dict[str, Outcome]] = {}

    def rocq() -> dict[str, Outcome]:
        result = run_capture([tools.coqc, "-q", "-R", str(tools.flocq / "src"), "Flocq", str(folder / "Case.v")],
                             tools.rocq_timeout)
        processes["rocq-vm"] = [_save(folder, "rocq", result)]
        by_short = parse_rocq(result.stdout, result.stderr, result.returncode, result.timed_out,
                              [sha[:16] for sha in rocq_labels])
        return {sha: by_short[sha[:16]] for sha in rocq_labels}

    def meta() -> dict[str, Outcome]:
        lean = meta_file(subjects, tools.heartbeats, preamble)
        (folder / "Meta.lean").write_text(lean.text)
        (folder / "Meta.ranges.json").write_text(json.dumps(lean.ranges, indent=1) + "\n")
        result = run_capture(_lean(folder / "Meta.lean"), tools.lean_timeout)
        processes["lean-meta"] = [_save(folder, "meta", result)]
        return parse_meta(result, lean.ranges)

    def ir() -> dict[str, Outcome]:
        pending = list(subjects)
        outcomes: dict[str, Outcome] = {}
        runs: list[dict[str, object]] = []
        attempt = 0
        while pending:
            name = "IR" if attempt == 0 else f"IR.{attempt}"
            lean = ir_file(pending, preamble)
            (folder / f"{name}.lean").write_text(lean.text)
            (folder / f"{name}.ranges.json").write_text(json.dumps(lean.ranges, indent=1) + "\n")
            result = run_capture(_lean(folder / f"{name}.lean", run=True), tools.lean_timeout)
            runs.append(_save(folder, name.lower(), result))
            got, unstarted = parse_ir(result, [s.case_id for s in pending], lean.ranges)
            outcomes.update(got)
            # Each re-emission removes at least one case, so this terminates;
            # no case is ever executed twice (§6.3).
            if len(unstarted) == len(pending):
                for label in unstarted:
                    outcomes[label] = Outcome("harness", detail="IR process made no progress")
                break
            pending = [s for s in pending if s.case_id in set(unstarted)]
            attempt += 1
        processes["lean-ir"] = runs
        return outcomes

    jobs = {"rocq-vm": rocq}
    if "lean-meta" in paths:
        jobs["lean-meta"] = meta
    if "lean-ir" in paths:
        jobs["lean-ir"] = ir
    with ThreadPoolExecutor(max_workers=2) as pool:
        futures = {name: pool.submit(job) for name, job in jobs.items()}
        results = {name: future.result() for name, future in futures.items()}
    rocq_outcomes: dict[str, Outcome] = results.pop("rocq-vm")
    lean_outcomes.update(results)

    if "lean-kernel" in paths:
        expected = {s.case_id: rocq_outcomes[s.program_sha].document for s in subjects
                    if rocq_outcomes[s.program_sha].status == "ok" and _decodes(s.program, rocq_outcomes[s.program_sha])}
        runnable = [s for s in subjects if s.case_id in expected]
        kernel: dict[str, Outcome] = {s.case_id: Outcome("not-run", detail="reference did not produce a valid value")
                                      for s in subjects if s.case_id not in expected}
        if runnable:
            lean = kernel_file(runnable, expected, tools.heartbeats, preamble)  # type: ignore[arg-type]
            (folder / "Kernel.lean").write_text(lean.text)
            (folder / "Kernel.ranges.json").write_text(json.dumps(lean.ranges, indent=1) + "\n")
            result = run_capture(_lean(folder / "Kernel.lean"), tools.lean_timeout)
            runs = [_save(folder, "kernel", result)]
            first = parse_kernel(result, lean.ranges)
            rejected = [s for s in runnable if first[s.case_id] == REJECTED]
            second: dict[str, Outcome | str] = {}
            if rejected:
                lean = kernel_file(rejected, expected, tools.heartbeats, preamble, negated=True)  # type: ignore[arg-type]
                (folder / "KernelNeg.lean").write_text(lean.text)
                (folder / "KernelNeg.ranges.json").write_text(json.dumps(lean.ranges, indent=1) + "\n")
                result = run_capture(_lean(folder / "KernelNeg.lean"), tools.lean_timeout)
                runs.append(_save(folder, "kernelneg", result))
                second = parse_kernel(result, lean.ranges)
            processes["lean-kernel"] = runs
            kernel.update(combine_kernel(first, second))
        lean_outcomes["lean-kernel"] = kernel

    batch = judge_batch(folder, subjects, rocq_outcomes, lean_outcomes, paths)
    batch.processes = processes
    write_batch_record(batch)
    return batch


def _decodes(program: Program, outcome: Outcome) -> bool:
    from .observe import DecodeError, decode
    try:
        decode(signature(program), outcome.document or ())
        return True
    except DecodeError:
        return False


def judge_batch(folder: Path, subjects: list[Subject], rocq: dict[str, Outcome],
                lean: dict[str, dict[str, Outcome]], paths: tuple[str, ...]) -> BatchResult:
    verdicts: dict[str, list[Verdict]] = {}
    disagreements: list[str] = []
    for s in subjects:
        sig = signature(s.program)
        reference = rocq[s.program_sha]
        rows = []
        for path in paths:
            clone = lean[path].get(s.case_id, Outcome("harness", detail=f"{path}: no outcome recorded"))
            if path == "lean-kernel" and clone.status == "not-run" and reference.status == "ok":
                clone = Outcome("harness", detail="kernel not run although the reference produced a value")
            rows.append(judge(sig, path, reference, clone))
        verdicts[s.case_id] = rows
        if "lean-meta" in paths and "lean-ir" in paths and meta_ir_disagreement(
                sig, lean["lean-meta"][s.case_id], lean["lean-ir"][s.case_id]):
            disagreements.append(s.case_id)
    return BatchResult(folder, subjects, rocq, lean, verdicts, disagreements)


def write_batch_record(batch: BatchResult) -> None:
    files = sorted(p for p in batch.folder.iterdir() if p.is_file() and p.name != "batch.json"
                   and not p.name.startswith(".") and p.suffix not in (".vo", ".vok", ".vos", ".glob", ".aux"))
    record = {
        "subjects": [{"case_id": s.case_id, "program_sha256": s.program_sha, "variant": s.variant.name}
                     for s in batch.subjects],
        "processes": batch.processes,
        "rocq": {sha: o.to_json() for sha, o in batch.rocq.items()},
        "lean": {path: {label: o.to_json() for label, o in rows.items()} for path, rows in batch.paths.items()},
        "verdicts": {label: [v.to_json() for v in rows] for label, rows in batch.verdicts.items()},
        "meta_ir_disagreements": batch.disagreements,
        "files": {p.name: sha256_file(p) for p in files},
    }
    (batch.folder / "batch.json").write_text(json.dumps(record, indent=1) + "\n")
