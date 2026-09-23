"""Command line: ``run``, ``controls``, ``replay``, ``shrink``, ``verify`` (FLOCQSMITH.md §15).

Examples (from the repository root)::

    uv run scripts/run_flocqsmith.py run --flocq-dir "$FLOCQ_AUDIT_DIR" --seed 17 -n 50 --out DIR
    uv run scripts/run_flocqsmith.py controls --flocq-dir "$FLOCQ_AUDIT_DIR" --seed 5 -n 40 --out DIR
    uv run scripts/run_flocqsmith.py replay DIR/cases/s17-000042.json --flocq-dir "$FLOCQ_AUDIT_DIR" --out DIR2
    uv run scripts/run_flocqsmith.py shrink CASE.json --control fma_double_rounding --flocq-dir ... --out DIR3
    uv run scripts/run_flocqsmith.py verify DIR
    uv run scripts/run_flocqsmith.py campaign DESCRIPTOR.json --flocq-dir "$FLOCQ_AUDIT_DIR" --out DIR4
    uv run scripts/run_flocqsmith.py verify-campaign DIR4

Exit status is 0 only for ``passed`` (run, replay, campaign), ``controls-ok``
(controls), ``preserved`` (shrink) and ``verified`` (verify, verify-campaign).
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path
import sys

from .campaign import Options, all_control_names, replay, run_campaign, shrink_case, verify
from .descriptor import run_descriptor, verify_campaign
from .formats import DEFAULT_FORMAT_WEIGHTS, FORMATS
from .generate import GenConfig
from .verdict import CLONE_PATHS


def _formats(text: str | None) -> tuple[tuple[str, int], ...]:
    if not text:
        return tuple(DEFAULT_FORMAT_WEIGHTS.items())
    weights = []
    for item in text.split(","):
        name, _, weight = item.partition("=")
        if name not in FORMATS:
            raise SystemExit(f"unknown format {name}; known: {', '.join(FORMATS)}")
        weights.append((name, int(weight or 1)))
    return tuple(weights)


def _paths(text: str | None) -> tuple[str, ...]:
    if not text:
        return CLONE_PATHS
    paths = tuple(text.split(","))
    if not set(paths) <= set(CLONE_PATHS):
        raise SystemExit(f"unknown paths; known: {', '.join(CLONE_PATHS)}")
    return paths


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(prog="flocqsmith", description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = parser.add_subparsers(dest="command", required=True)
    for name in ("run", "controls"):
        p = sub.add_parser(name)
        p.add_argument("--flocq-dir", type=Path, required=True)
        p.add_argument("--out", type=Path, required=True)
        p.add_argument("--seed", type=int, default=17)
        p.add_argument("-n", type=int, default=50)
        p.add_argument("--formats", help="comma list name=weight (default: all, weighted)")
        p.add_argument("--min-size", type=int, default=4)
        p.add_argument("--max-size", type=int, default=12)
        p.add_argument("--budget-ms", type=float, default=3000.0)
        p.add_argument("--paths", help="comma list of lean-meta,lean-ir,lean-kernel")
        p.add_argument("--controls", help="comma list of control names (controls: default all)")
        p.add_argument("--allow-dirty", action="store_true")
        p.add_argument("--capacity-ms", type=float, default=25_000.0)
        p.add_argument("--max-batch", type=int, default=48)
    p = sub.add_parser("replay")
    p.add_argument("record", type=Path)
    p.add_argument("--flocq-dir", type=Path, required=True)
    p.add_argument("--out", type=Path, required=True)
    p.add_argument("--controls", help="also replay under these controls")
    p.add_argument("--paths")
    p.add_argument("--allow-dirty", action="store_true")
    p.add_argument("--from-ir", action="store_true", help="replay the recorded IR instead of the draw tape")
    p = sub.add_parser("shrink")
    p.add_argument("record", type=Path)
    p.add_argument("--flocq-dir", type=Path, required=True)
    p.add_argument("--out", type=Path, required=True)
    p.add_argument("--control", help="planted control to shrink under (default: the unmutated port)")
    p.add_argument("--path", default="lean-meta", choices=("lean-meta", "lean-ir"))
    p.add_argument("--allow-dirty", action="store_true")
    p.add_argument("--from-ir", action="store_true", help="load the recorded IR instead of the draw tape")
    p = sub.add_parser("verify")
    p.add_argument("out", type=Path)
    p = sub.add_parser("campaign", help="run a committed campaign descriptor (lanes, coverage, clusters, shrinks)")
    p.add_argument("descriptor", type=Path)
    p.add_argument("--flocq-dir", type=Path, required=True)
    p.add_argument("--out", type=Path, required=True)
    p.add_argument("--allow-dirty", action="store_true")
    p = sub.add_parser("verify-campaign")
    p.add_argument("out", type=Path)
    args = parser.parse_args(argv)

    if args.command in ("run", "controls"):
        controls: tuple[str, ...]
        if args.controls:
            controls = tuple(args.controls.split(","))
        else:
            controls = all_control_names() if args.command == "controls" else ()
        config = GenConfig(format_weights=_formats(args.formats), min_size=args.min_size, max_size=args.max_size,
                           budget_ms=args.budget_ms)
        report = run_campaign(Options(args.flocq_dir.resolve(), args.out.resolve(), args.seed, args.n, config,
                                      controls, _paths(args.paths), args.allow_dirty, args.capacity_ms,
                                      args.max_batch, focus_controls=args.command == "controls"))
        print(json.dumps({k: report[k] for k in ("status", "generated", "judged", "verdicts", "infra_stages",
                                                 "meta_ir_disagreements", "elapsed_seconds")}, indent=1))
        if report["controls"]:
            for name, row in report["controls"].items():  # type: ignore[union-attr]
                print(f"control {name}: exposed {row['exposed']}, detected {row['detected']} "
                      f"(rate {row['detection_rate']}), first at {row['cases_to_first_detection']}, "
                      f"by path {row['detected_by_path']}, other {row['non_mismatch_verdicts']}")
        if args.command == "controls":
            controls_ok = all(row["ok"] for row in report["controls"].values())  # type: ignore[union-attr]
            baseline_ok = not report["mismatches"] and not report["harness_errors"] and not report["infra"]
            return 0 if controls_ok and baseline_ok else 1
        return 0 if report["status"] == "passed" else 1
    if args.command == "replay":
        report = replay(args.record.resolve(), args.flocq_dir.resolve(), args.out.resolve(),
                        tuple(args.controls.split(",")) if args.controls else (), _paths(args.paths),
                        args.allow_dirty, args.from_ir)
        print(json.dumps({k: report[k] for k in ("status", "verdicts", "mismatches")}, indent=1))
        return 0 if report["status"] == "passed" else 1
    if args.command == "shrink":
        report = shrink_case(args.record.resolve(), args.flocq_dir.resolve(), args.out.resolve(), args.control,
                             args.path, args.allow_dirty, args.from_ir)
        print(json.dumps({k: report.get(k) for k in ("status", "target", "statements_before", "statements_after",
                                                     "rounds", "final")}, indent=1))
        return 0 if report["status"] == "preserved" else 1
    if args.command == "verify":
        result = verify(args.out.resolve())
        print(json.dumps(result, indent=1))
        return 0 if result["status"] == "verified" else 1
    if args.command == "campaign":
        report = run_descriptor(args.descriptor.resolve(), args.flocq_dir.resolve(), args.out.resolve(),
                                args.allow_dirty)
        print(json.dumps({k: report[k] for k in ("status", "reasons", "programs", "verdict_totals",
                                                 "elapsed_seconds")}, indent=1))
        return 0 if report["status"] == "passed" else 1
    if args.command == "verify-campaign":
        result = verify_campaign(args.out.resolve())
        print(json.dumps(result, indent=1))
        return 0 if result["status"] == "verified" else 1
    return 2


if __name__ == "__main__":
    sys.exit(main())
