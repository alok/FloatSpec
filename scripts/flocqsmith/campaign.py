"""Campaigns, positive controls, replay, shrinking and offline verification.

A campaign generates ``n`` programs from a seed, runs each on every path
(plus every exposed positive-control variant when requested), and publishes a
report whose verdicts can be recomputed offline (§7, §8.2):

- evidence is built in ``<out>.staging/`` and published by an atomic rename;
- every generated file, raw stream and case record is digested in
  ``manifest.json``; ``complete.json`` is written last and binds the report
  digest to the manifest digest;
- the reference (gitlink pin, clean ``src``), ``coqc`` and ``lean`` are
  identified by digest and version, and a dirty worktree is refused unless
  ``allow_dirty`` is set (its status is recorded either way);
- the Lean source fingerprint must not change during the run.
"""

from __future__ import annotations

from collections import Counter
from dataclasses import dataclass, field, replace
import hashlib
import json
import os
from pathlib import Path
import time

import flocq_bridge as fb

from . import SCHEMA_CASE, SCHEMA_REPORT
from .choose import Chooser, Draw, ReplayError
from .cost import pack
from .generate import GenConfig, generate, program_seed
from .harness import (BatchResult, Subject, Toolchain, combine_kernel, execute_batch, judge_batch, parse_ir,
                      parse_kernel, parse_meta, parse_rocq, sha256_file)
from .ir import Program, check_program, ops_used, signature, size
from .mutants import CONTROL_BY_NAME, CONTROLS, exposed
from .numeric import numeric_tags, structural_tags
from .observe import DecodeError, Observed, decode
from .process import ProcResult
from .render import BASELINE, LeanVariant, lean_term, rocq_term, sha256
from .shrink import Target, shrink
from .verdict import CLONE_PATHS, Outcome, Verdict

PACKAGE = Path(__file__).resolve().parent
INFRA = ("reference-infra-failure", "clone-infra-failure", "both-infra-failure")


def generator_rev() -> str:
    digest = hashlib.sha256()
    for path in sorted(PACKAGE.glob("*.py")):
        digest.update(path.name.encode() + b"\0" + path.read_bytes() + b"\0")
    digest.update(fb.LEAN_HEADER.encode() + fb.COQ_HEADER.encode())
    return digest.hexdigest()


# -- case records (§8.1) -------------------------------------------------------

@dataclass
class CaseRecord:
    id: str
    program: Program
    lean_sha256: str
    rocq_sha256: str
    cost_ms: float
    generator_rev: str
    seed: int | None = None
    index: int | None = None
    config: GenConfig | None = None
    draws: list[Draw] | None = None
    origin: str = "generated"

    def to_json(self) -> dict[str, object]:
        row: dict[str, object] = {
            "schema": SCHEMA_CASE, "id": self.id, "origin": self.origin, "generator_rev": self.generator_rev,
            "seed": self.seed, "index": self.index, "config": self.config.to_json() if self.config else None,
            "draws": [d.to_json() for d in self.draws] if self.draws is not None else None,
            "ir": self.program.to_json(), "observation_signature": signature(self.program),
            "lean_sha256": self.lean_sha256, "rocq_sha256": self.rocq_sha256, "cost_ms": round(self.cost_ms, 3),
            "size": size(self.program), "ops": ops_used(self.program),
            "tags": dict(sorted(structural_tags(self.program).items())),
        }
        return row


def new_case(seed: int, index: int, config: GenConfig) -> CaseRecord:
    chooser = Chooser(seed=program_seed(seed, index))
    result = generate(chooser, config)
    return CaseRecord(f"s{seed}-{index:06d}", result.program, sha256(lean_term(result.program)),
                      sha256(rocq_term(result.program)), result.cost_ms, generator_rev(), seed, index, config,
                      list(chooser.draws))


def load_case(row: dict[str, object], from_ir: bool = False) -> CaseRecord:
    """Replay a record: from its draw tape when it has one (unless ``from_ir``),
    else from its IR.

    Either way both renderings are regenerated and must hash to the recorded
    digests; otherwise :class:`ReplayError` (kind ``rendering``) is raised. A
    tape needs a compatible generator; the IR only a compatible renderer.
    """
    if row.get("schema") != SCHEMA_CASE:
        raise ReplayError("rendering", "not a flocqsmith case record")
    config = GenConfig.from_json(row["config"]) if row.get("config") else None  # type: ignore[arg-type]
    draws_row = row.get("draws")
    if draws_row is not None and not from_ir:
        if config is None:
            raise ReplayError("rendering", "a tape needs its generator config")
        draws = [Draw.from_json(d) for d in draws_row]  # type: ignore[union-attr]
        chooser = Chooser(tape=draws)
        result = generate(chooser, config)
        program, cost = result.program, result.cost_ms
        recorded = Program.from_json(row["ir"])
        if recorded != program:
            raise ReplayError("rendering", "tape regenerates a different IR than the record")
    else:
        draws = None
        program = Program.from_json(row["ir"])
        cost = float(row.get("cost_ms", 100.0))  # type: ignore[arg-type]
    lean, rocq = sha256(lean_term(program)), sha256(rocq_term(program))
    if lean != row.get("lean_sha256") or rocq != row.get("rocq_sha256"):
        raise ReplayError("rendering", "regenerated renderings do not match the recorded digests")
    return CaseRecord(str(row["id"]), program, lean, rocq, cost, str(row.get("generator_rev", "")),
                      row.get("seed"), row.get("index"), config, draws,  # type: ignore[arg-type]
                      str(row.get("origin", "generated")))


def case_from_program(case_id: str, program: Program, origin: str, cost_ms: float = 100.0) -> CaseRecord:
    check_program(program)
    return CaseRecord(case_id, program, sha256(lean_term(program)), sha256(rocq_term(program)), cost_ms,
                      generator_rev(), origin=origin)


# -- identities and integrity (§8.2) -------------------------------------------

def identities(flocq: Path, coqc: str, allow_dirty: bool) -> dict[str, object]:
    pin = fb.verify_reference(flocq)
    status = fb.run(["git", "status", "--porcelain"]).strip()
    if status and not allow_dirty:
        raise SystemExit("refusing a dirty worktree (pass --allow-dirty to record and proceed):\n" + status)
    prefix = fb.run(["lake", "env", "lean", "--print-prefix"]).strip()
    lean_binary = Path(prefix) / "bin" / "lean"
    return {
        "reference": {"flocq_commit": pin, "flocq_src": str(flocq / "src")},
        "coqc": {"path": coqc, "sha256": sha256_file(Path(coqc)), "version": fb.run([coqc, "--version"]).strip()},
        "lean": {"path": str(lean_binary), "sha256": sha256_file(lean_binary),
                 "version": fb.run(["lake", "env", "lean", "--version"]).strip()},
        "lean_source_sha256": fb.lean_source_fingerprint(),
        "head": fb.run(["git", "rev-parse", "HEAD"]).strip(),
        "dirty": bool(status),
        "dirty_status": status.splitlines() if status else [],
        "dirty_diff_sha256": (hashlib.sha256(fb.run(["git", "diff", "HEAD"]).encode()).hexdigest()
                              if status else None),
        "generator_rev": generator_rev(),
    }


def _staging(out: Path) -> Path:
    if out.exists() and (not out.is_dir() or any(out.iterdir())):
        raise SystemExit(f"output {out} exists and is not empty; previous evidence is not overwritten")
    staging = out.with_name(out.name + ".staging")
    if staging.exists():
        raise SystemExit(f"stale staging directory {staging}; inspect and remove it first")
    staging.mkdir(parents=True)
    return staging


def _publish(staging: Path, out: Path, report: dict[str, object]) -> None:
    report_path = staging / "report.json"
    report_path.write_text(json.dumps(report, indent=1, sort_keys=False) + "\n")
    manifest = {str(p.relative_to(staging)): sha256_file(p) for p in sorted(staging.rglob("*"))
                if p.is_file() and p.name not in ("manifest.json", "complete.json")}
    manifest_path = staging / "manifest.json"
    manifest_path.write_text(json.dumps(manifest, indent=1) + "\n")
    (staging / "complete.json").write_text(json.dumps({
        "report_sha256": sha256_file(report_path), "manifest_sha256": sha256_file(manifest_path),
        "files": len(manifest)}, indent=1) + "\n")
    if out.exists():
        out.rmdir()
    os.replace(staging, out)


# -- running subjects ------------------------------------------------------------

@dataclass
class Options:
    flocq: Path
    out: Path
    seed: int = 17
    n: int = 50
    config: GenConfig = field(default_factory=GenConfig)
    controls: tuple[str, ...] = ()
    paths: tuple[str, ...] = CLONE_PATHS
    allow_dirty: bool = False
    capacity_ms: float = 25_000.0
    max_batch: int = 48
    tools: Toolchain | None = None
    focus_controls: bool = False


def case_config(opts: Options, index: int) -> GenConfig:
    """With ``focus_controls``, program ``i`` targets planted control ``i mod k``:
    that control's ops are always in its swarm, and each of its relational
    corners is emitted once (operands and modes are still drawn)."""
    planted = [CONTROL_BY_NAME[name] for name in opts.controls if CONTROL_BY_NAME[name].ops]
    if not opts.focus_controls or not planted:
        return opts.config
    control = planted[index % len(planted)]
    return replace(opts.config, swarm_include=control.ops,
                   force_forms=opts.config.force_forms + tuple(f"corner:{c}" for c in control.corners))


def toolchain(flocq: Path) -> Toolchain:
    return Toolchain(flocq, fb.configured_coqc(flocq))


def _subjects(cases: list[CaseRecord], controls: tuple[str, ...]) -> list[tuple[Subject, float]]:
    out: list[tuple[Subject, float]] = []
    for case in cases:
        out.append((Subject(case.id, case.program, BASELINE), case.cost_ms))
        for name in controls:
            control = CONTROL_BY_NAME[name]
            if exposed(control, case.program):
                out.append((Subject(f"{case.id}~{name}", case.program, control.variant), case.cost_ms))
    return out


def run_subjects(subjects: list[tuple[Subject, float]], folder: Path, tools: Toolchain, paths: tuple[str, ...],
                 capacity_ms: float, max_batch: int, log: bool = True) -> list[BatchResult]:
    batches: list[BatchResult] = []
    groups = pack([cost for _, cost in subjects], capacity_ms, max_batch)
    for number, group in enumerate(groups):
        started = time.monotonic()
        batch = execute_batch([subjects[i][0] for i in group], folder / f"batch_{number:03d}", tools, paths)
        batches.append(batch)
        if log:
            counts = Counter(v.verdict for rows in batch.verdicts.values() for v in rows)
            print(f"batch {number + 1}/{len(groups)}: {len(group)} subjects in "
                  f"{time.monotonic() - started:.1f}s; {dict(counts)}", flush=True)
    return batches


# -- aggregation -----------------------------------------------------------------

def _reference_values(program: Program, outcome: Outcome) -> tuple[Observed, ...] | None:
    if outcome.status != "ok" or outcome.document is None:
        return None
    try:
        return decode(signature(program), outcome.document)
    except DecodeError:
        return None


def summarize(cases: list[CaseRecord], batches: list[BatchResult], controls: tuple[str, ...],
              paths: tuple[str, ...]) -> dict[str, object]:
    verdicts: dict[str, list[Verdict]] = {}
    rocq: dict[str, Outcome] = {}
    disagreements: list[str] = []
    for batch in batches:
        verdicts.update(batch.verdicts)
        rocq.update(batch.rocq)
        disagreements.extend(batch.disagreements)
    histogram = {path: Counter() for path in paths}  # type: dict[str, Counter[str]]
    stages: Counter[str] = Counter()
    mismatches, infra, harness = [], [], []
    structural: Counter[str] = Counter()
    numeric: Counter[str] = Counter()
    judged = {path: 0 for path in paths}
    for case in cases:
        structural.update(structural_tags(case.program))
        values = _reference_values(case.program, rocq.get(case.program.sha256(), Outcome("not-run")))
        if values is not None:
            numeric.update(numeric_tags(case.program, values))
        for v in verdicts.get(case.id, []):
            histogram[v.path][v.verdict] += 1
            if v.verdict in ("match", "observation-mismatch"):
                judged[v.path] += 1
            if v.stage:
                stages[f"{v.path}:{v.stage}"] += 1
            row = {"case": case.id, **v.to_json()}
            if v.verdict == "observation-mismatch":
                mismatches.append(row)
            elif v.verdict in INFRA:
                infra.append(row)
            elif v.verdict == "harness-error":
                harness.append(row)
    control_rows: dict[str, dict[str, object]] = {}
    for name in controls:
        exposed_ids = [c.id for c in cases if f"{c.id}~{name}" in verdicts]
        detected, first, per_path, non_mismatch = 0, None, Counter(), Counter()  # type: ignore[var-annotated]
        for position, case_id in enumerate(exposed_ids, start=1):
            rows = verdicts[f"{case_id}~{name}"]
            hit = [v for v in rows if v.verdict == "observation-mismatch"]
            for v in rows:
                if v.verdict == "observation-mismatch":
                    per_path[v.path] += 1
                elif v.verdict != "match":
                    non_mismatch[f"{v.path}:{v.verdict}"] += 1
            if hit:
                detected += 1
                if first is None:
                    first = position
        control = CONTROL_BY_NAME[name]
        control_rows[name] = {
            "family": control.family, "description": control.description, "ops": list(control.ops),
            "generated": len(cases), "exposed": len(exposed_ids), "detected": detected,
            "detection_rate": round(detected / len(exposed_ids), 4) if exposed_ids else None,
            "cases_to_first_detection": first, "detected_by_path": dict(per_path),
            "non_mismatch_verdicts": dict(non_mismatch),
            "ok": bool(exposed_ids) and detected > 0 and not non_mismatch,
        }
    return {
        "generated": len(cases), "judged": judged, "excluded": {path: 0 for path in paths},
        "verdicts": {path: dict(counts) for path, counts in histogram.items()},
        "infra_stages": dict(stages), "mismatches": mismatches, "infra": infra, "harness_errors": harness,
        "meta_ir_disagreements": [d for d in disagreements if "~" not in d],
        "controls": control_rows,
        "structural_tags": dict(sorted(structural.items())), "numeric_tags": dict(sorted(numeric.items())),
    }


def status_of(summary: dict[str, object]) -> str:
    if summary["harness_errors"]:
        return "harness-error"
    if summary["mismatches"] or summary["meta_ir_disagreements"]:
        return "mismatch"
    controls = summary["controls"]
    assert isinstance(controls, dict)
    if any(not row["ok"] for row in controls.values()):
        return "controls-failed"
    if summary["infra"]:
        return "infra-failure"
    return "passed"


def run_campaign(opts: Options) -> dict[str, object]:
    for name in opts.controls:
        if name not in CONTROL_BY_NAME:
            raise SystemExit(f"unknown control {name}; known: {', '.join(CONTROL_BY_NAME)}")
    tools = opts.tools or toolchain(opts.flocq)
    ident = identities(opts.flocq, tools.coqc, opts.allow_dirty)
    staging = _staging(opts.out)
    started = time.monotonic()
    cases = [new_case(opts.seed, index, case_config(opts, index)) for index in range(opts.n)]
    (staging / "cases").mkdir()
    for case in cases:
        (staging / "cases" / f"{case.id}.json").write_text(json.dumps(case.to_json(), indent=1) + "\n")
    subjects = _subjects(cases, opts.controls)
    print(f"flocqsmith: seed={opts.seed} n={opts.n} subjects={len(subjects)} controls={list(opts.controls)} "
          f"staging={staging}", flush=True)
    batches = run_subjects(subjects, staging / "batches", tools, opts.paths, opts.capacity_ms, opts.max_batch)
    fb.require_lean_source_snapshot(str(ident["lean_source_sha256"]))
    summary = summarize(cases, batches, opts.controls, opts.paths)
    report: dict[str, object] = {
        "schema": SCHEMA_REPORT, "status": status_of(summary), "kind": "campaign",
        "identities": ident, "seed": opts.seed, "n": opts.n, "config": opts.config.to_json(),
        "paths": list(opts.paths), "reference_path": "rocq-vm", "nan_policy": "exact",
        "controls_requested": list(opts.controls),
        "corpus": ("control-focused: program i has the ops of planted control i mod k in its swarm and "
                   "emits that control's relational corners once" if opts.focus_controls and opts.controls
                   else "unfocused"),
        "batches": [{"folder": str(b.folder.relative_to(staging)), "subjects": len(b.subjects)} for b in batches],
        "elapsed_seconds": round(time.monotonic() - started, 3),
        **summary,
        "statement": "Finite differential testing of generated BinarySingleNaN programs: every observed binding "
                     "of each Lean path compared with pinned Rocq vm_compute. Not a proof of equivalence.",
    }
    _publish(staging, opts.out, report)
    return report


# -- replay ------------------------------------------------------------------------

def replay(record_path: Path, flocq: Path, out: Path, controls: tuple[str, ...] = (),
           paths: tuple[str, ...] = CLONE_PATHS, allow_dirty: bool = False,
           from_ir: bool = False) -> dict[str, object]:
    case = load_case(json.loads(record_path.read_text()), from_ir)
    tools = toolchain(flocq)
    ident = identities(flocq, tools.coqc, allow_dirty)
    staging = _staging(out)
    (staging / "cases").mkdir()
    (staging / "cases" / f"{case.id}.json").write_text(json.dumps(case.to_json(), indent=1) + "\n")
    subjects = [(Subject(case.id, case.program, BASELINE), case.cost_ms)]
    subjects += [(Subject(f"{case.id}~{name}", case.program, CONTROL_BY_NAME[name].variant), case.cost_ms)
                 for name in controls]
    batches = run_subjects(subjects, staging / "batches", tools, paths, 1e12, len(subjects))
    summary = summarize([case], batches, tuple(controls), paths)
    report = {"schema": SCHEMA_REPORT, "status": status_of(summary), "kind": "replay", "identities": ident,
              "record": str(record_path), "paths": list(paths), **summary}
    _publish(staging, out, report)
    return report


# -- shrinking ------------------------------------------------------------------

def shrink_case(record_path: Path, flocq: Path, out: Path, control: str | None, path: str,
                allow_dirty: bool = False, from_ir: bool = False) -> dict[str, object]:
    """Shrink one diverging case under a (possibly planted) Lean variant."""
    case = load_case(json.loads(record_path.read_text()), from_ir)
    variant = CONTROL_BY_NAME[control].variant if control else BASELINE
    tools = toolchain(flocq)
    ident = identities(flocq, tools.coqc, allow_dirty)
    staging = _staging(out)
    counter = [0]

    def run(programs: list[Program]) -> list[tuple[Verdict | None, tuple[Observed, ...] | None]]:
        folder = staging / "rounds" / f"round_{counter[0]:03d}"
        counter[0] += 1
        subjects = [Subject(f"shrink{k}", p, variant) for k, p in enumerate(programs)]
        batch = execute_batch(subjects, folder, tools, (path,))
        return [(next((v for v in batch.verdicts[s.case_id] if v.path == path), None),
                  _reference_values(s.program, batch.rocq[s.program_sha])) for s in subjects]

    (initial, reference), = run([case.program])
    if initial is None or initial.verdict != "observation-mismatch" or reference is None:
        report = {"schema": SCHEMA_REPORT, "kind": "shrink", "status": "nothing-to-shrink", "identities": ident,
                  "initial": initial.to_json() if initial else None}
        _publish(staging, out, report)
        return report
    divergence = initial.divergence or {}
    target = Target(path, "observation-mismatch", str(divergence.get("op")))
    result = shrink(case.program, reference, str(divergence.get("id")), target, run)
    (final, _), = run([result.program])
    shrunk = case_from_program(f"{case.id}.min", result.program, origin=f"shrink:{case.id}")
    (staging / "minimized.json").write_text(json.dumps(shrunk.to_json(), indent=1) + "\n")
    (staging / "minimized.lean.txt").write_text(lean_term(result.program, variant) + "\n")
    (staging / "minimized.v.txt").write_text(rocq_term(result.program) + "\n")
    report = {
        "schema": SCHEMA_REPORT, "kind": "shrink", "identities": ident, "record": str(record_path),
        "control": control, "target": target.to_json(), "initial": initial.to_json(),
        "final": final.to_json() if final else None,
        "status": "preserved" if target.holds(final) else "lost",
        "statements_before": len(case.program.stmts), "statements_after": len(result.program.stmts),
        "size_before": size(case.program), "size_after": size(result.program),
        "rounds": result.rounds, "steps": result.steps,
    }
    _publish(staging, out, report)
    return report


# -- offline verification (§8.2) ---------------------------------------------------

def _proc(folder: Path, name: str, meta: dict[str, object]) -> ProcResult:
    return ProcResult(tuple(meta.get("command", [])), (folder / f"{name}.stdout").read_text(),  # type: ignore[arg-type]
                      (folder / f"{name}.stderr").read_text(), meta.get("returncode"),  # type: ignore[arg-type]
                      bool(meta.get("timed_out")), float(meta.get("seconds", 0.0)))  # type: ignore[arg-type]


def verify(out: Path) -> dict[str, object]:
    """Recheck digests and recompute every verdict from the retained raw streams."""
    problems: list[str] = []
    complete = json.loads((out / "complete.json").read_text())
    if sha256_file(out / "report.json") != complete["report_sha256"]:
        problems.append("report.json digest differs from complete.json")
    if sha256_file(out / "manifest.json") != complete["manifest_sha256"]:
        problems.append("manifest.json digest differs from complete.json")
    manifest = json.loads((out / "manifest.json").read_text())
    for rel, digest in manifest.items():
        path = out / rel
        if not path.is_file() or sha256_file(path) != digest:
            problems.append(f"digest mismatch: {rel}")
    report = json.loads((out / "report.json").read_text())
    # Programs come from the recorded IR (not the tape), so verification does
    # not depend on the generator revision; the renderings must still hash
    # to the recorded digests.
    cases: dict[str, CaseRecord] = {}
    for record_path in sorted((out / "cases").glob("*.json")):
        row = json.loads(record_path.read_text())
        program = Program.from_json(row["ir"])
        if sha256(lean_term(program)) != row["lean_sha256"] or sha256(rocq_term(program)) != row["rocq_sha256"]:
            problems.append(f"{record_path.name}: renderings differ from the recorded digests")
        cases[row["id"]] = case_from_program(row["id"], program, origin="verify")
    rejudged = 0
    for batch_record in sorted((out / "batches").glob("batch_*/batch.json")):
        folder = batch_record.parent
        record = json.loads(batch_record.read_text())
        subjects = []
        for row in record["subjects"]:
            base = row["case_id"].split("~")[0]
            variant: LeanVariant = BASELINE if row["variant"] == "baseline" else CONTROL_BY_NAME[row["variant"]].variant
            subjects.append(Subject(row["case_id"], cases[base].program, variant))
        procs = record["processes"]
        rocq_run = _proc(folder, "rocq", procs["rocq-vm"][0])
        shas = list(record["rocq"])
        by_short = parse_rocq(rocq_run.stdout, rocq_run.stderr, rocq_run.returncode, rocq_run.timed_out,
                              [s[:16] for s in shas])
        rocq = {s: by_short[s[:16]] for s in shas}
        lean: dict[str, dict[str, Outcome]] = {}
        paths = tuple(p for p in CLONE_PATHS if p in record["lean"])
        if "lean-meta" in paths:
            ranges = {k: tuple(v) for k, v in json.loads((folder / "Meta.ranges.json").read_text()).items()}
            lean["lean-meta"] = parse_meta(_proc(folder, "meta", procs["lean-meta"][0]), ranges)  # type: ignore[arg-type]
        if "lean-ir" in paths:
            outcomes: dict[str, Outcome] = {}
            for attempt, meta in enumerate(procs["lean-ir"]):
                name = "IR" if attempt == 0 else f"IR.{attempt}"
                ranges = {k: tuple(v) for k, v in json.loads((folder / f"{name}.ranges.json").read_text()).items()}
                got, unstarted = parse_ir(_proc(folder, name.lower(), meta), list(ranges), ranges)  # type: ignore[arg-type]
                outcomes.update(got)
                if attempt == len(procs["lean-ir"]) - 1:
                    for label in unstarted:
                        outcomes[label] = Outcome("harness", detail="IR process made no progress")
            lean["lean-ir"] = outcomes
        if "lean-kernel" in paths:
            kernel = {k: Outcome.from_json(v) for k, v in record["lean"]["lean-kernel"].items()
                      if v["status"] == "not-run"}
            if "lean-kernel" in procs:
                passes = []
                for name, meta in zip(("Kernel", "KernelNeg"), procs["lean-kernel"]):
                    ranges = {k: tuple(v) for k, v in json.loads((folder / f"{name}.ranges.json").read_text()).items()}
                    passes.append(parse_kernel(_proc(folder, name.lower(), meta), ranges))  # type: ignore[arg-type]
                kernel.update(combine_kernel(passes[0], passes[1] if len(passes) > 1 else {}))
            lean["lean-kernel"] = kernel
        again = judge_batch(folder, subjects, rocq, lean, paths)
        for label, rows in again.verdicts.items():
            rejudged += 1
            if [v.to_json() for v in rows] != record["verdicts"][label]:
                problems.append(f"{folder.name}/{label}: re-judged verdicts differ")
    return {"status": "verified" if not problems else "failed", "rejudged_subjects": rejudged,
            "problems": problems, "report_status": report.get("status")}


def all_control_names() -> tuple[str, ...]:
    return tuple(c.name for c in CONTROLS)
