#!/usr/bin/env python3
"""Execute binary64 arithmetic in native Lean, compiled/kernel models, and Rocq.

Round-to-nearest-even; NaNs are canonicalized, signed zeros are not. Every model
result agreeing with pinned Rocq becomes a kernel-checked Lean regression.
"""

from __future__ import annotations

import argparse
from collections import Counter
from concurrent.futures import ThreadPoolExecutor
import json
from pathlib import Path
import random
import tempfile
import time

from flocq_bridge import (ROOT, configured_coqc, lean_source_fingerprint, parse_result,
                          require_lean_source_snapshot, run, verify_reference)
from native_ieee_bridge import category, validate_word


LEAN_HEADER = """import FloatSpec.Test.NativeArithmetic
open FloatSpec.Test.NativeArithmetic
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option exponentiation.threshold 5000
set_option pp.maxSteps 200000
set_option pp.deepTerms true
"""
COQ_HEADER = ROOT / "scripts/fixtures/NativeArithmetic.v"
COLUMNS = ("left", "right", "add", "sub", "mul", "div", "sqrt_left")


def validate_case(case: list[int] | tuple[int, int]) -> tuple[int, int]:
    if type(case) not in (list, tuple) or len(case) != 2:
        raise ValueError("case must be a pair of uint64 bit patterns")
    return validate_word(case[0]), validate_word(case[1])


def corpus(seed: int, samples: int) -> list[tuple[int, int]]:
    boundaries = [0, 1, 2, 0x000fffffffffffff, 0x0010000000000000,
                  0x3ca0000000000000, 0x3fe0000000000000, 0x3fefffffffffffff,
                  0x3ff0000000000000, 0x3ff0000000000001, 0x4000000000000000,
                  0x4008000000000000, 0x7fefffffffffffff, 0x7ff0000000000000,
                  0x7ff0000000000001, 0x7ff8000000000001]
    words = [word | sign for sign in (0, 1 << 63) for word in boundaries]
    # The Cartesian grid exercises every exceptional pair, half-ULP ties,
    # overflow/underflow, and both signs of the smallest finite values.
    pairs = [(left, right) for left in words for right in words]
    rng = random.Random(seed)
    for _ in range(samples):
        left, right = rng.getrandbits(64), rng.getrandbits(64)
        pairs.extend(((left, right), (left, left), (left, left ^ (1 << 63)),
                      (left, left ^ 1)))
    return list(dict.fromkeys(pairs))


def native_source(cases: list[tuple[int, int]]) -> str:
    pairs = ", ".join(f"({left}, {right})" for left, right in cases)
    return (LEAN_HEADER + "def main : IO Unit :=\n  IO.println (([" + pairs +
            "] : List (UInt64 × UInt64)).map fun (x, y) => nativeObservation x y)\n")


def compiled_model_source(cases: list[tuple[int, int]]) -> str:
    pairs = ", ".join(f"({left}, {right})" for left, right in cases)
    return (LEAN_HEADER + "def main : IO Unit :=\n  IO.println (([" + pairs +
            "] : List (UInt64 × UInt64)).map fun (x, y) => modelObservation x y)\n")


def execute(cases: list[tuple[int, int]], flocq: Path, coqc: str,
            folder: Path) -> dict[str, list[list[int]]]:
    paths = {name: folder / filename for name, filename in
             (("native", "Native.lean"), ("model", "Model.lean"),
              ("compiled_model", "CompiledModel.lean"), ("rocq", "Arithmetic.v"))}
    paths["native"].write_text(native_source(cases))
    paths["compiled_model"].write_text(compiled_model_source(cases))
    paths["model"].write_text(LEAN_HEADER + "#reduce ([" + ", ".join(
        f"modelObservation {left} {right}" for left, right in cases) + "] : List (List Int))\n")
    paths["rocq"].write_text(COQ_HEADER.read_text() + "\nEval vm_compute in [" + "; ".join(
        f"observation {left} {right}" for left, right in cases) + "].\n")
    commands = {"native": ["lake", "env", "lean", "--run", str(paths["native"])],
                "model": ["lake", "env", "lean", str(paths["model"])],
                "compiled_model": ["lake", "env", "lean", "--run", str(paths["compiled_model"])],
                "rocq": [coqc, "-q", "-R", str(flocq / "src"), "Flocq", str(paths["rocq"])]}

    def observe(name: str) -> list[list[int]]:
        output = run(commands[name])
        (folder / f"{name}.out").write_text(output)
        rows = parse_result(output, "rocq" if name == "rocq" else "lean", len(cases))
        if any(len(row) != len(COLUMNS) for row in rows):
            raise ValueError(f"{name}: expected all seven observation columns")
        return rows

    with ThreadPoolExecutor(max_workers=4) as pool:
        futures = {name: pool.submit(observe, name) for name in commands}
        return {name: future.result() for name, future in futures.items()}


def compare(cases: list[tuple[int, int]], observations: dict[str, list[list[int]]]) -> list:
    if set(observations) != {"native", "model", "compiled_model", "rocq"}:
        raise ValueError("all four execution paths are required")
    if any(len(rows) != len(cases) or any(len(row) != len(COLUMNS) for row in rows)
           for rows in observations.values()):
        raise ValueError("incomplete observations")
    mismatches = []
    for index, case in enumerate(cases):
        for path in ("native", "model", "compiled_model"):
            actual, expected = observations[path][index], observations["rocq"][index]
            if actual != expected:
                mismatches.append({"case": case, "hex": [f"0x{word:016x}" for word in case],
                                   "path": f"{path.replace('_', '-')}-versus-rocq", "actual": actual,
                                   "expected": expected, "columns": [name for name, a, b in
                                   zip(COLUMNS, actual, expected, strict=True) if a != b]})
    return mismatches


def bootstrap_lean(cases: list[tuple[int, int]], expected: list[list[int]], folder: Path) -> None:
    path = folder / "OracleRegressions.lean"
    statements = [f"example : modelObservation {left} {right} = {json.dumps(row)} "
                  ":= by decide +kernel" for (left, right), row in zip(cases, expected, strict=True)]
    path.write_text(LEAN_HEADER + "\n".join(statements) + "\n")
    output = run(["lake", "env", "lean", str(path)])
    (folder / "oracle_regressions.out").write_text(output)
    if output.strip():
        raise ValueError(f"unexpected Lean regression diagnostics: {output[:500]}")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--flocq-dir", type=Path, required=True)
    parser.add_argument("--coqc")
    parser.add_argument("--seed", type=int, default=20260919)
    parser.add_argument("--samples", type=int, default=100)
    parser.add_argument("--batch-size", type=int, default=20)
    parser.add_argument("--output", type=Path)
    parser.add_argument("--replay", type=Path, help="JSON array of pairs of uint64 bit patterns")
    args = parser.parse_args()
    if args.samples < 0 or args.batch_size < 1:
        parser.error("samples must be nonnegative and batch-size positive")
    flocq = args.flocq_dir.resolve()
    pin, coqc = verify_reference(flocq), args.coqc or configured_coqc(flocq)
    cases = ([validate_case(case) for case in json.loads(args.replay.read_text())]
             if args.replay else corpus(args.seed, args.samples))
    if not cases:
        parser.error("empty corpus is not a successful test")
    output = (args.output or Path(tempfile.mkdtemp(prefix="floatspec-native-arithmetic-"))).resolve()
    output.mkdir(parents=True, exist_ok=True)
    if any(output.iterdir()):
        parser.error("output directory must be empty; previous evidence is not overwritten")
    (output / "cases.json").write_text(json.dumps(cases, indent=2) + "\n")
    report = {"seed": args.seed, "reference": pin, "cases": len(cases), "status": "running",
              "lean_source_sha256": lean_source_fingerprint(),
              "operand_categories": dict(Counter(category(word) for case in cases for word in case)),
              "lean_head": run(["git", "rev-parse", "HEAD"]).strip(),
              "worktree_status": run(["git", "status", "--porcelain"]).strip(),
              "lean_version": run(["lake", "env", "lean", "--version"]).strip(),
              "rocq_version": run([coqc, "--version"]).strip(), "host": run(["uname", "-sm"]).strip(),
              "method": "Native FFI execution, compiled Lean model, Lean kernel reduction, Rocq vm_compute",
              "rounding": "nearest, ties to even", "columns": COLUMNS,
              "nan_observation": "single canonical NaN; payload identity not claimed",
              "compared_cases": 0, "compiled_model_cases": 0, "bootstrapped_lean_cases": 0, "mismatches": []}
    report_path = output / "report.json"

    def save() -> None:
        report_path.write_text(json.dumps(report, indent=2) + "\n")
        if report["mismatches"]:
            replay = list(dict.fromkeys(tuple(row["case"]) for row in report["mismatches"]))
            (output / "replay.json").write_text(json.dumps(replay, indent=2) + "\n")

    save()
    print(f"Executing {len(cases)} arithmetic pairs; seed={args.seed}; artifacts={output}", flush=True)
    started = time.monotonic()
    try:
        build = run(["lake", "build", "FloatSpec.Test.NativeArithmetic"], timeout=600)
        (output / "lean_build.out").write_text(build)
        require_lean_source_snapshot(report["lean_source_sha256"])
        for offset in range(0, len(cases), args.batch_size):
            batch = cases[offset:offset + args.batch_size]
            folder = output / f"batch_{offset:06d}"
            folder.mkdir()
            observations = execute(batch, flocq, coqc, folder)
            report["mismatches"].extend(compare(batch, observations))
            report["compared_cases"] += len(batch)
            report["compiled_model_cases"] += len(batch)
            save()
            if observations["model"] == observations["rocq"]:
                bootstrap_lean(batch, observations["rocq"], folder)
                report["bootstrapped_lean_cases"] += len(batch)
                save()
            print(f"{report['compared_cases']}/{len(cases)}; "
                  f"mismatches={len(report['mismatches'])}", flush=True)
            require_lean_source_snapshot(report["lean_source_sha256"])
        report["status"] = "mismatch" if report["mismatches"] else "passed"
    except BaseException as error:
        report["status"], report["error"] = "error", f"{type(error).__name__}: {error}"
        raise
    finally:
        report["elapsed_seconds"] = round(time.monotonic() - started, 3)
        save()
    if report["mismatches"]:
        raise SystemExit(f"{len(report['mismatches'])} mismatches; see {report_path}")
    print(f"PASS: {len(cases)} four-path arithmetic pairs; see {report_path}")


if __name__ == "__main__":
    main()
