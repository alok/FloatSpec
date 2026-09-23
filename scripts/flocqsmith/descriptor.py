"""Pre-registered campaigns: a committed descriptor, lanes, and one aggregate report.

A *campaign descriptor* (``flocqsmith-campaign-descriptor-v1``) fixes, before
anything runs, every lane (seed, N, format weights, sizes, budget, kind), the
coverage the campaign must reach, the shrink policy and whether the exemplar
lane runs. It must be committed and unmodified when the campaign starts; the
report binds its sha256 and git blob, so a result cannot be re-labelled after
the fact by editing the plan.

``run_descriptor`` then, in order and never more than one lane at a time
(each lane already caps itself at two prover processes):

1. runs every lane with :func:`~flocqsmith.campaign.run_campaign`, each
   publishing its own staged, manifested evidence directory;
2. re-judges every lane offline with :func:`~flocqsmith.campaign.verify`;
3. measures coverage (formats, ops, op families per format, forms, modes,
   corners) over cases *judged on every path*: an infrastructure failure
   never counts as coverage, and every requested cell that stays empty is a
   named gap;
4. clusters every disagreement (a baseline ``observation-mismatch`` on any
   path, or a ``lean-meta``/``lean-ir`` disagreement) by root signature, and
   infrastructure failures separately by ``(path, verdict, stage)``;
5. shrinks disagreements with :func:`~flocqsmith.campaign.shrink_case`
   (up to ``max_per_cluster`` per cluster) and collects the minimized records;
6. runs the exemplar lane test when asked, recording its exit status and
   test counts (a skipped live test is not a pass);
7. writes ``campaign.json`` and ``complete.json`` and publishes the whole
   directory by one atomic rename.

The campaign status is ``passed`` only if every lane passed (controls lanes:
every control detected with an all-match baseline), every lane verified,
coverage has no gap, no disagreement or infrastructure failure occurred and
the exemplar lane (if requested) passed. Anything else names its reasons.

``check_campaign_record`` rechecks a committed report offline against its
descriptor, re-deriving that status from the report's own fields.
"""

from __future__ import annotations

from collections import Counter, defaultdict
from dataclasses import dataclass
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import time

import flocq_bridge as fb

from . import SCHEMA_CASE
from .campaign import (INFRA, Options, _publish, all_control_names, identities, run_campaign, sha256_file,
                       shrink_case, toolchain, verify)
from .formats import DEFAULT_FORMAT_WEIGHTS, FORMATS
from .generate import CORNERS, FORMS, GenConfig
from .ir import Program, Stmt, iter_bindings
from .numeric import structural_tags
from .table import MODE_NAMES, OPS
from .verdict import CLONE_PATHS

SCHEMA_DESCRIPTOR = "flocqsmith-campaign-descriptor-v1"
SCHEMA_CAMPAIGN = "flocqsmith-campaign-report-v1"
ROOT = Path(__file__).resolve().parents[2]

# Op families of the BinarySingleNaN capability profile (FLOCQSMITH.md §12).
# They must partition the signature table exactly; ``check_families`` fails
# closed if a table row is added without a family.
FAMILIES: dict[str, tuple[str, ...]] = {
    "add-sub-fma": ("Bplus", "Bminus", "Bfma"),
    "mult": ("Bmult",),
    "div-sqrt": ("Bdiv", "Bsqrt"),
    "sign-erase": ("Bopp", "Babs", "erase"),
    "succ-pred-ulp": ("Bsucc", "Bpred", "Bulp", "Bsucc'", "Bpred_pos'", "Bulp'"),
    "scale": ("Bldexp", "Bfrexp.1", "Bfrexp.2"),
    "integer-rounding": ("Bnearbyint", "Btrunc"),
    "constants": ("Bone", "Bmax_float"),
    "construct-round": ("binary_normalize", "SF2B'", "B2SF", "binary_round"),
    "compare": ("Beqb", "Bltb", "Bleb", "Bcompare"),
    "classify": ("Bsign", "is_nan", "is_finite", "is_finite_strict", "Bfma_szero", "Bnormfr_mantissa"),
}
FAMILY_OF = {op: family for family, ops in FAMILIES.items() for op in ops}
FIELDS = {"BSN": ("class", "sign", "mantissa", "exponent"), "SF": ("class", "sign", "mantissa", "exponent")}


def check_families() -> None:
    table = [row.name for row in OPS]
    listed = [op for ops in FAMILIES.values() for op in ops]
    if sorted(table) != sorted(listed) or len(set(listed)) != len(listed):
        raise AssertionError(f"op families do not partition the table: missing {sorted(set(table) - set(listed))}, "
                             f"extra {sorted(set(listed) - set(table))}")


# -- the descriptor ----------------------------------------------------------------

@dataclass(frozen=True)
class Lane:
    name: str
    kind: str
    seed: int
    n: int
    config: GenConfig
    controls: tuple[str, ...]


def _lane(row: dict[str, object]) -> Lane:
    allowed = {"name", "kind", "seed", "n", "formats", "min_size", "max_size", "budget_ms", "controls", "purpose"}
    if set(row) - allowed:
        raise ValueError(f"lane has unknown fields {sorted(set(row) - allowed)}")
    name, kind = str(row["name"]), str(row["kind"])
    if not re.fullmatch(r"[a-z0-9][a-z0-9-]*", name):
        raise ValueError(f"lane name {name!r} must be lowercase kebab-case")
    if kind not in ("run", "controls"):
        raise ValueError(f"lane {name}: kind must be run or controls")
    formats = row.get("formats")
    weights = tuple(DEFAULT_FORMAT_WEIGHTS.items()) if formats is None else \
        tuple((str(k), int(v)) for k, v in dict(formats).items())  # type: ignore[call-overload]
    config = GenConfig(weights, int(row.get("min_size", 4)), int(row.get("max_size", 12)),  # type: ignore[call-overload]
                       float(row.get("budget_ms", 3000.0)))  # type: ignore[arg-type]
    controls_row = row.get("controls")
    if kind == "controls":
        controls = all_control_names() if controls_row in (None, "all") else tuple(controls_row)  # type: ignore[arg-type]
    elif controls_row:
        raise ValueError(f"lane {name}: only controls lanes take controls")
    else:
        controls = ()
    return Lane(name, kind, int(row["seed"]), int(row["n"]), config, controls)  # type: ignore[call-overload]


def load_descriptor(path: Path) -> tuple[dict[str, object], list[Lane]]:
    row = json.loads(path.read_text())
    if row.get("schema") != SCHEMA_DESCRIPTOR:
        raise ValueError(f"{path}: not a {SCHEMA_DESCRIPTOR}")
    lanes = [_lane(lane) for lane in row["lanes"]]
    names = [lane.name for lane in lanes]
    if len(set(names)) != len(names):
        raise ValueError("lane names must be unique")
    seeds = [lane.seed for lane in lanes]
    if len(set(seeds)) != len(seeds):
        raise ValueError("lane seeds must be distinct, so no program is judged twice under two lane names")
    paths = tuple(row.get("paths", CLONE_PATHS))  # type: ignore[arg-type]
    if not set(paths) <= set(CLONE_PATHS):
        raise ValueError(f"unknown paths {paths}")
    return row, lanes


def descriptor_is_committed(path: Path) -> tuple[bool, str]:
    """The descriptor must be tracked and identical to HEAD's copy."""
    rel = os.path.relpath(path, ROOT)
    tracked = subprocess.run(["git", "ls-files", "--error-unmatch", rel], cwd=ROOT, capture_output=True)
    if tracked.returncode != 0:
        return False, f"{rel} is not tracked by git"
    changed = subprocess.run(["git", "diff", "--quiet", "HEAD", "--", rel], cwd=ROOT)
    if changed.returncode != 0:
        return False, f"{rel} differs from HEAD"
    return True, subprocess.run(["git", "rev-parse", f"HEAD:{rel}"], cwd=ROOT, capture_output=True,
                                text=True, check=True).stdout.strip()


# -- reading lane evidence -----------------------------------------------------------

def _cases(lane_dir: Path) -> dict[str, dict[str, object]]:
    out: dict[str, dict[str, object]] = {}
    for path in sorted((lane_dir / "cases").glob("*.json")):
        row = json.loads(path.read_text())
        if row.get("schema") != SCHEMA_CASE:
            raise ValueError(f"{path}: not a case record")
        out[str(row["id"])] = row
    return out


def _verdicts(lane_dir: Path) -> dict[str, list[dict[str, object]]]:
    """Baseline verdict rows per case id, read from the retained batch records."""
    out: dict[str, list[dict[str, object]]] = {}
    for record in sorted((lane_dir / "batches").glob("batch_*/batch.json")):
        for label, rows in json.loads(record.read_text())["verdicts"].items():
            if "~" not in label:
                out[label] = rows
    return out


def _stmt(program: Program, binding: str) -> Stmt | None:
    for s in iter_bindings(program.stmts):
        if s.id == binding or (s.kind == "fold" and binding in s.fold_ids()):
            return s
    return None


# -- coverage --------------------------------------------------------------------------

def coverage(lanes: list[tuple[Lane, Path]], paths: tuple[str, ...]) -> dict[str, object]:
    """Structural coverage over cases judged (match or mismatch) on every path."""
    generated = judged_all = 0
    counts: dict[str, Counter[str]] = {k: Counter() for k in ("formats", "ops", "forms", "modes", "corners")}
    fmt_family: dict[str, Counter[str]] = {name: Counter() for name in FORMATS}
    fmt_op: dict[str, Counter[str]] = {name: Counter() for name in FORMATS}
    for _, lane_dir in lanes:
        verdicts = _verdicts(lane_dir)
        for case_id, row in _cases(lane_dir).items():
            generated += 1
            rows = {str(v["path"]): str(v["verdict"]) for v in verdicts.get(case_id, [])}
            if not all(rows.get(p) in ("match", "observation-mismatch") for p in paths):
                continue
            judged_all += 1
            program = Program.from_json(row["ir"])
            tags = structural_tags(program)
            fmt = program.fmt.name
            counts["formats"][fmt] += 1
            for tag, k in tags.items():
                kind, _, value = tag.partition(":")
                if kind == "op":
                    counts["ops"][value] += k
                    fmt_op[fmt][value] += k
                    fmt_family[fmt][FAMILY_OF[value]] += k
                elif kind == "form":
                    counts["forms"]["fold" if value.startswith("fold_") else value] += k
                elif kind == "mode":
                    counts["modes"][value] += k
                elif kind == "corner":
                    counts["corners"][value] += k
            # Plain op statements are not tagged as a form; count them so every
            # form in the grammar has a cell.
            if any(s.kind == "op" for s in iter_bindings(program.stmts)):
                counts["forms"]["op"] += 1
            if any(s.corner is not None for s in iter_bindings(program.stmts)):
                counts["forms"]["corner"] += 1
    required = {
        "formats": list(FORMATS), "ops": [row.name for row in OPS], "forms": list(FORMS),
        "modes": list(MODE_NAMES), "corners": list(CORNERS),
    }
    gaps: list[str] = [f"{kind}:{name}" for kind, names in required.items() for name in names
                       if counts[kind][name] == 0]
    gaps += [f"format-family:{fmt}/{family}" for fmt in FORMATS for family in FAMILIES
             if fmt_family[fmt][family] == 0]
    format_op_empty = [f"{fmt}/{op}" for fmt in FORMATS for op in required["ops"] if fmt_op[fmt][op] == 0]
    return {
        "basis": "cases whose every requested path returned match or observation-mismatch",
        "generated": generated, "judged_on_every_path": judged_all,
        **{kind: dict(sorted(c.items())) for kind, c in counts.items()},
        "format_family": {fmt: dict(sorted(c.items())) for fmt, c in fmt_family.items()},
        "gaps": gaps,
        "format_op_cells": len(FORMATS) * len(required["ops"]),
        "format_op_empty": format_op_empty,
    }


# -- clustering --------------------------------------------------------------------------

def _root_signature(program: Program, rows: dict[str, dict[str, object]], disagree: bool) -> dict[str, object]:
    mismatched = sorted(p for p, v in rows.items() if v["verdict"] == "observation-mismatch")
    divergence = next((rows[p].get("divergence") for p in ("lean-meta", "lean-ir")
                       if p in rows and rows[p].get("divergence")), None)
    if not isinstance(divergence, dict):
        return {"kind": "kernel-only" if mismatched == ["lean-kernel"] else "no-divergence",
                "paths": mismatched, "format": program.fmt.name, "meta_ir_disagreement": disagree}
    stmt = _stmt(program, str(divergence["id"]))
    ref, got = list(divergence["reference"]), list(divergence["clone"])  # type: ignore[call-overload]
    names = FIELDS.get(str(divergence["type"]), tuple(f"v{k}" for k in range(len(ref))))
    fields = [names[k] if k < len(names) else f"v{k}" for k in range(len(ref)) if ref[k] != got[k]]
    return {"kind": "divergence", "op": divergence["op"], "type": divergence["type"], "fields": fields,
            "mode": MODE_NAMES[stmt.mode] if stmt is not None and stmt.mode is not None else None,
            "format": program.fmt.name, "paths": mismatched, "meta_ir_disagreement": disagree}


def _signature_key(sig: dict[str, object]) -> str:
    if sig["kind"] != "divergence":
        return f"{sig['kind']}|{sig['format']}|{'+'.join(sig['paths'])}"  # type: ignore[arg-type]
    return (f"{sig['op']}|{sig['type']}|{','.join(sig['fields'])}|{sig['mode']}|{sig['format']}|"  # type: ignore[arg-type]
            f"{'+'.join(sig['paths'])}")  # type: ignore[arg-type]


def cluster(lanes: list[tuple[Lane, Path]]) -> tuple[list[dict[str, object]], list[dict[str, object]]]:
    """Disagreement clusters by root signature; infrastructure clusters by (path, verdict, stage)."""
    groups: dict[str, dict[str, object]] = {}
    infra: dict[tuple[str, str, str], list[str]] = defaultdict(list)
    for lane, lane_dir in lanes:
        report = json.loads((lane_dir / "report.json").read_text())
        disagreeing = set(report.get("meta_ir_disagreements", []))
        verdicts = _verdicts(lane_dir)
        cases = _cases(lane_dir)
        for case_id, rows_list in sorted(verdicts.items()):
            rows = {str(v["path"]): v for v in rows_list}
            for v in rows_list:
                if v["verdict"] in INFRA or v["verdict"] == "harness-error":
                    infra[(str(v["path"]), str(v["verdict"]), str(v.get("stage")))].append(f"{lane.name}/{case_id}")
            mismatch = any(v["verdict"] == "observation-mismatch" for v in rows_list)
            if not mismatch and case_id not in disagreeing:
                continue
            program = Program.from_json(cases[case_id]["ir"])
            sig = _root_signature(program, rows, case_id in disagreeing)
            key = _signature_key(sig)
            group = groups.setdefault(key, {"key": key, "signature": sig, "members": []})
            group["members"].append({"lane": lane.name, "case": case_id,  # type: ignore[union-attr]
                                     "record": str((lane_dir / "cases" / f"{case_id}.json").relative_to(
                                         lane_dir.parent.parent)),
                                     "verdicts": {p: r["verdict"] for p, r in rows.items()}})
    clusters = sorted(groups.values(), key=lambda g: (-len(g["members"]), str(g["key"])))  # type: ignore[arg-type]
    for index, group in enumerate(clusters):
        group["id"] = f"c{index:02d}"
        group["count"] = len(group["members"])  # type: ignore[arg-type]
    infra_rows = [{"path": p, "verdict": v, "stage": s, "count": len(ids), "cases": ids}
                  for (p, v, s), ids in sorted(infra.items())]
    return clusters, infra_rows


# -- the exemplar lane ---------------------------------------------------------------------

def run_exemplar_lane(flocq: Path, folder: Path, timeout: float) -> dict[str, object]:
    folder.mkdir(parents=True)
    env = dict(os.environ, FLOCQ_AUDIT_DIR=str(flocq))
    command = ["uv", "run", "scripts/test_flocq_exemplars.py", "-v"]
    started = time.monotonic()
    try:
        done = subprocess.run(command, cwd=ROOT, env=env, capture_output=True, text=True, timeout=timeout)
        returncode, stdout, stderr, timed_out = done.returncode, done.stdout, done.stderr, False
    except subprocess.TimeoutExpired as expired:
        returncode, timed_out = None, True
        stdout = expired.stdout.decode() if isinstance(expired.stdout, bytes) else (expired.stdout or "")
        stderr = expired.stderr.decode() if isinstance(expired.stderr, bytes) else (expired.stderr or "")
    (folder / "exemplars.stdout").write_text(stdout)
    (folder / "exemplars.stderr").write_text(stderr)
    text = stdout + stderr
    ran = re.search(r"^Ran (\d+) tests? in ([\d.]+)s", text, re.M)
    skipped = re.search(r"skipped=(\d+)", text)
    failures = re.search(r"failures=(\d+)", text)
    errors = re.search(r"errors=(\d+)", text)
    ok_line = re.search(r"^OK\b", text, re.M) is not None
    per_test = Counter(m.group(1) for m in re.finditer(r" \.\.\. (ok|FAIL|ERROR|skipped)", text))
    result = {
        "command": command, "returncode": returncode, "timed_out": timed_out,
        "seconds": round(time.monotonic() - started, 3), "tests": int(ran.group(1)) if ran else None,
        "skipped": int(skipped.group(1)) if skipped else 0, "failures": int(failures.group(1)) if failures else 0,
        "errors": int(errors.group(1)) if errors else 0, "per_test": dict(per_test),
    }
    result["status"] = ("passed" if returncode == 0 and ok_line and not timed_out and ran and not result["skipped"]
                        else "failed")
    return result


# -- the campaign verdict -----------------------------------------------------------------------

def campaign_reasons(lane_rows: list[dict[str, object]], covered: dict[str, object],
                     clusters: list[dict[str, object]], infra_clusters: list[dict[str, object]],
                     exemplar: dict[str, object] | None) -> list[str]:
    """Why a campaign failed; empty exactly when it passed (module docstring)."""
    reasons: list[str] = []
    for lane_row in lane_rows:
        wanted = "controls-ok" if lane_row["kind"] == "controls" else "passed"
        if lane_row["status"] != wanted:
            reasons.append(f"lane {lane_row['name']}: {lane_row['status']}")
        if lane_row["verify"]["status"] != "verified":  # type: ignore[index]
            reasons.append(f"lane {lane_row['name']}: offline verify {lane_row['verify']['status']}")  # type: ignore[index]
    if covered["gaps"]:
        reasons.append(f"coverage gaps: {len(covered['gaps'])}")  # type: ignore[arg-type]
    if clusters:
        reasons.append(f"disagreement clusters: {len(clusters)}")
    if infra_clusters:
        reasons.append(f"infrastructure clusters: {len(infra_clusters)}")
    if exemplar is not None and exemplar["status"] != "passed":
        reasons.append("exemplar lane failed")
    return reasons


def verdict_totals(lane_rows: list[dict[str, object]], paths: tuple[str, ...]) -> dict[str, dict[str, int]]:
    totals: dict[str, Counter[str]] = {p: Counter() for p in paths}
    for lane_row in lane_rows:
        verdicts = lane_row["verdicts"]
        assert isinstance(verdicts, dict)
        for p, counts in verdicts.items():
            totals[p].update(counts)
    return {p: dict(sorted(c.items())) for p, c in totals.items()}


def git_blob(data: bytes) -> str:
    """The id git gives a file with these bytes, computed without a repository."""
    return hashlib.sha1(b"blob %d\0" % len(data) + data).hexdigest()


def check_campaign_record(report: dict[str, object], descriptor: Path) -> list[str]:
    """Offline: a committed campaign report against its pre-registered descriptor.

    The raw prover streams are not committed, so this cannot re-judge a case;
    ``verify-campaign`` does that on a retained output directory. It checks what
    a committed record supports on its own: the report binds these exact
    descriptor bytes (sha256 and git blob, wherever the file now lives), its
    lanes are the pre-registered ones, its totals are the sums of its lanes,
    and its status and reasons follow from its recorded lane, coverage,
    cluster and exemplar results by the rule the runner applies. An empty
    list means the record is consistent.
    """
    problems: list[str] = []
    data = descriptor.read_bytes()
    row, lanes = load_descriptor(descriptor)
    if report.get("schema") != SCHEMA_CAMPAIGN:
        problems.append(f"schema is {report.get('schema')!r}, not {SCHEMA_CAMPAIGN}")
    bound = report.get("descriptor")
    if not isinstance(bound, dict) or bound.get("sha256") != hashlib.sha256(data).hexdigest():
        problems.append(f"the report does not bind {descriptor.name} (sha256 differs)")
    elif not bound.get("committed") or bound.get("git_blob") != git_blob(data):
        problems.append(f"{descriptor.name} was not committed when the campaign ran, or its blob differs")
    if report.get("id") != row.get("id"):
        problems.append(f"campaign id {report.get('id')!r} is not the descriptor's {row.get('id')!r}")
    paths: tuple[str, ...] = tuple(row.get("paths", CLONE_PATHS))  # type: ignore[arg-type]
    if report.get("paths") != list(paths):
        problems.append("paths differ from the descriptor's")
    lane_rows = report.get("lanes")
    if not isinstance(lane_rows, list):
        return problems + ["the report has no lane list"]
    planned = [[lane.name, lane.kind, lane.seed, lane.n, json.loads(json.dumps(lane.config.to_json()))]
               for lane in lanes]
    recorded = [[r.get("name"), r.get("kind"), r.get("seed"), r.get("n"), r.get("config")] for r in lane_rows]
    if recorded != planned:
        problems.append("lanes (name, kind, seed, n, config) differ from the pre-registered lanes")
    if report.get("programs") != sum(lane.n for lane in lanes):
        problems.append("program count is not the sum of the pre-registered lane sizes")
    if report.get("verdict_totals") != verdict_totals(lane_rows, paths):
        problems.append("verdict totals are not the sums of the lane verdicts")
    if bool(row.get("exemplar_lane")) != (report.get("exemplar_lane") is not None):
        problems.append("the exemplar lane ran although not requested, or was requested and did not run")
    reasons = campaign_reasons(lane_rows, report["coverage"], report["clusters"],  # type: ignore[arg-type]
                               report["infra_clusters"], report["exemplar_lane"])  # type: ignore[arg-type]
    if reasons != report.get("reasons"):
        problems.append(f"recorded reasons {report.get('reasons')} are not the re-derived {reasons}")
    if report.get("status") != ("passed" if not reasons else "failed"):
        problems.append(f"status {report.get('status')!r} does not follow from the re-derived reasons")
    return problems


# -- the campaign ------------------------------------------------------------------------------

def run_descriptor(descriptor: Path, flocq: Path, out: Path, allow_dirty: bool = False) -> dict[str, object]:
    check_families()
    row, lanes = load_descriptor(descriptor)
    committed, blob = descriptor_is_committed(descriptor)
    if not committed and not allow_dirty:
        raise SystemExit(f"refusing an uncommitted descriptor: {blob}")
    paths = tuple(row.get("paths", CLONE_PATHS))  # type: ignore[arg-type]
    if out.exists() and (not out.is_dir() or any(out.iterdir())):
        raise SystemExit(f"output {out} exists and is not empty")
    staging = out.with_name(out.name + ".staging")
    if staging.exists():
        raise SystemExit(f"stale staging directory {staging}")
    staging.mkdir(parents=True)
    tools = toolchain(flocq)
    ident = identities(flocq, tools.coqc, allow_dirty)
    expected_pin = str(row.get("reference", {}).get("flocq_commit", ""))  # type: ignore[union-attr]
    pin = str(ident["reference"]["flocq_commit"])  # type: ignore[index]
    if expected_pin and not pin.startswith(expected_pin):
        raise SystemExit(f"reference pin {pin} is not the descriptor's {expected_pin}")
    started = time.monotonic()
    lane_dirs: list[tuple[Lane, Path]] = []
    lane_rows: list[dict[str, object]] = []
    for lane in lanes:
        lane_dir = staging / "lanes" / lane.name
        lane_dir.parent.mkdir(exist_ok=True)
        print(f"== lane {lane.name}: kind={lane.kind} seed={lane.seed} n={lane.n}", flush=True)
        report = run_campaign(Options(flocq, lane_dir, lane.seed, lane.n, lane.config, lane.controls, paths,
                                      allow_dirty, tools=tools, focus_controls=lane.kind == "controls"))
        checked = verify(lane_dir)
        if lane.kind == "controls":
            controls_ok = all(r["ok"] for r in report["controls"].values())  # type: ignore[union-attr]
            baseline_ok = not report["mismatches"] and not report["harness_errors"] and not report["infra"]
            lane_status = "controls-ok" if controls_ok and baseline_ok else "controls-failed"
        else:
            lane_status = str(report["status"])
        lane_dirs.append((lane, lane_dir))
        lane_rows.append({
            "name": lane.name, "kind": lane.kind, "seed": lane.seed, "n": lane.n, "config": lane.config.to_json(),
            "status": lane_status, "report_status": report["status"], "verify": checked,
            "report_sha256": sha256_file(lane_dir / "report.json"),
            "complete_sha256": sha256_file(lane_dir / "complete.json"),
            "judged": report["judged"], "verdicts": report["verdicts"], "infra_stages": report["infra_stages"],
            "mismatches": len(report["mismatches"]), "infra": len(report["infra"]),  # type: ignore[arg-type]
            "harness_errors": len(report["harness_errors"]),  # type: ignore[arg-type]
            "meta_ir_disagreements": report["meta_ir_disagreements"],
            "controls": {name: {k: r[k] for k in ("exposed", "detected", "detection_rate", "detected_by_path",
                                                  "non_mismatch_verdicts", "ok")}
                         for name, r in report["controls"].items()},  # type: ignore[union-attr]
            "numeric_tags": report["numeric_tags"], "elapsed_seconds": report["elapsed_seconds"],
        })
    covered = coverage(lane_dirs, paths)
    clusters, infra_clusters = cluster(lane_dirs)
    shrink_policy = dict(row.get("shrink", {}))  # type: ignore[call-overload]
    per_cluster = int(shrink_policy.get("max_per_cluster", 3))
    shrinks: list[dict[str, object]] = []
    for group in clusters:
        sig = group["signature"]
        for member in group["members"][:per_cluster]:  # type: ignore[index]
            verdicts = member["verdicts"]
            path = next((p for p in ("lean-meta", "lean-ir") if verdicts.get(p) == "observation-mismatch"), None)
            entry: dict[str, object] = {"cluster": group["id"], "lane": member["lane"], "case": member["case"]}
            if path is None:
                entry.update(status="not-shrinkable",
                             reason="only lean-kernel diverged; the shrinker judges lean-meta or lean-ir")
            else:
                folder = staging / "shrink" / f"{group['id']}-{member['case']}"
                folder.parent.mkdir(exist_ok=True)
                result = shrink_case(staging / str(member["record"]), flocq, folder, None, path, allow_dirty)
                entry.update(status=result["status"], path=path, folder=str(folder.relative_to(staging)),
                             statements_before=result.get("statements_before"),
                             statements_after=result.get("statements_after"), rounds=result.get("rounds"))
            shrinks.append(entry)
        del sig
    exemplar = None
    if row.get("exemplar_lane"):
        exemplar = run_exemplar_lane(flocq, staging / "exemplars", float(row.get("exemplar_timeout_s", 3600)))
    fb.require_lean_source_snapshot(str(ident["lean_source_sha256"]))
    reasons = campaign_reasons(lane_rows, covered, clusters, infra_clusters, exemplar)
    report = {
        "schema": SCHEMA_CAMPAIGN, "id": row.get("id"), "status": "passed" if not reasons else "failed",
        "reasons": reasons,
        "descriptor": {"path": os.path.relpath(descriptor, ROOT), "sha256": sha256_file(descriptor),
                       "git_blob": blob if committed else None, "committed": committed},
        "identities": ident, "paths": list(paths),
        "programs": sum(lane.n for lane in lanes),
        "verdict_totals": verdict_totals(lane_rows, paths),
        "lanes": lane_rows, "coverage": covered, "clusters": clusters, "infra_clusters": infra_clusters,
        "shrinks": shrinks, "exemplar_lane": exemplar,
        "elapsed_seconds": round(time.monotonic() - started, 3),
        "statement": "Finite differential testing: every observed binding of generated BinarySingleNaN programs "
                     "on lean-meta, lean-ir and lean-kernel against pinned Rocq vm_compute. Infrastructure "
                     "failures are never matches and are reported separately. Not a proof of equivalence.",
    }
    report_path = staging / "campaign.json"
    report_path.write_text(json.dumps(report, indent=1) + "\n")
    lanes_complete = {name: sha256_file(staging / "lanes" / name / "complete.json") for name in
                      (lane.name for lane in lanes)}
    (staging / "complete.json").write_text(json.dumps({
        "campaign_sha256": sha256_file(report_path), "lanes_complete_sha256": lanes_complete}, indent=1) + "\n")
    if out.exists():
        out.rmdir()
    os.replace(staging, out)
    return report


def verify_campaign(out: Path) -> dict[str, object]:
    """Offline: the campaign report digest, and every lane's own offline verify."""
    problems: list[str] = []
    complete = json.loads((out / "complete.json").read_text())
    if sha256_file(out / "campaign.json") != complete["campaign_sha256"]:
        problems.append("campaign.json digest differs from complete.json")
    lanes: dict[str, object] = {}
    for name, digest in complete["lanes_complete_sha256"].items():
        lane_dir = out / "lanes" / name
        if sha256_file(lane_dir / "complete.json") != digest:
            problems.append(f"lane {name}: complete.json digest differs")
        result = verify(lane_dir)
        lanes[name] = result["status"]
        problems += [f"lane {name}: {p}" for p in result["problems"]]  # type: ignore[union-attr]
    return {"status": "verified" if not problems else "failed", "lanes": lanes, "problems": problems}


if __name__ == "__main__":  # pragma: no cover
    sys.exit("use scripts/run_flocqsmith.py campaign")
