#!/usr/bin/env python3
"""Cross-test source IEEE arithmetic in every rounding mode, retaining NaN payloads.

This compares the port's own bit decoders/operations with pinned Rocq. It does
not claim native hardware execution of directed rounding. Inputs and complete
generated prover programs are retained, with per-case kernel regression proofs.
"""

import argparse
from collections import Counter
from concurrent.futures import ThreadPoolExecutor
import json
from pathlib import Path
import random
import tempfile
import time

from flocq_bridge import (configured_coqc, lean_source_fingerprint, parse_result,
                          require_lean_source_snapshot, run, verify_reference)


LEAN_MODES = (".RNE", ".RTZ", ".RTN", ".RTP", ".RNA")
COQ_MODES = ("mode_NE", "mode_ZR", "mode_DN", "mode_UP", "mode_NA")
COLUMNS = ("left", "right", "third", "add", "sub", "mul", "div", "sqrt_left", "fma")
LEAN_HEADER = """import FloatSpec.src.IEEE754.Bits
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option exponentiation.threshold 5000
set_option pp.maxSteps 200000
set_option pp.deepTerms true
"""
COQ_HEADER = """From Stdlib Require Import ZArith List.
From Flocq Require Import IEEE754.Bits IEEE754.Binary IEEE754.BinarySingleNaN.
Import ListNotations.
Open Scope Z_scope.
"""


def validate_case(case):
    if not isinstance(case, (list, tuple)) or len(case) != 5 or any(type(n) is not int for n in case):
        raise ValueError("case must be [width, mode, left, right, third] integers")
    width, mode, *words = case
    if width not in (32, 64) or mode not in range(5) or any(not 0 <= word < 1 << width for word in words):
        raise ValueError("width must be 32/64, mode 0..4, and all inputs valid unsigned words")
    return tuple(case)


def corpus(seed, samples):
    rng, cases = random.Random(seed), []
    for width, fraction, bias in ((32, 23, 127), (64, 52, 1023)):
        sign = 1 << (width - 1)
        one, two, half = bias << fraction, (bias + 1) << fraction, (bias - 1) << fraction
        inf, max_finite = ((2 * bias + 1) << fraction), ((2 * bias + 1) << fraction) - 1
        half_ulp = (bias - fraction - 1) << fraction
        min_normal = 1 << fraction
        nan1, nan2, nan3 = inf | 1, sign | inf | (1 << (fraction - 1)), inf | 37
        triples = [(one, two, sign | one), (one, half_ulp, 0), (one, half_ulp + 1, 0),
                   (1, half, 0), (sign | 1, half, sign), (max_finite, two, sign | max_finite),
                   (one + 1, one - 1, sign | one), (min_normal, half, 1),
                   (min_normal - 1, one + 1, 1), (max_finite, max_finite, sign | max_finite),
                   (0, 0, 0), (sign, 0, sign), (one, sign | one, sign),
                   (one, 0, one), (0, inf, one), (inf, 0, one),
                   (inf, sign | inf, one), (sign | inf, inf, sign | inf),
                   (inf, two, sign | inf), (sign | one, two, one),
                   (nan1, one, two), (one, nan2, two), (one, two, nan3),
                   (nan1, nan2, nan3), (nan2, nan1, nan3), (0, inf, nan3),
                   (nan1, inf, 0), (inf, nan2, 0), (sign, one, 0)]
        for mode in range(5):
            cases.extend((width, mode, *triple) for triple in triples)
            for _ in range(samples):
                cases.append((width, mode, *(rng.getrandbits(width) for _ in range(3))))
    return list(dict.fromkeys(cases))


def expression(case, language):
    width, mode, left, right, third = case
    mode_name = (LEAN_MODES if language == "lean" else COQ_MODES)[mode]
    prefix, separator = ("", ", ") if language == "lean" else ("Bits.", "; ")
    let = (lambda n, v: f"let {n} := {v}; ") if language == "lean" else (lambda n, v: f"let {n} := {v} in ")
    result = "".join(let(name, f"{prefix}b{width}_of_bits {word}")
                     for name, word in zip(("x", "y", "z"), (left, right, third), strict=True))
    values = ["x", "y", "z"]
    values += [f"{prefix}b{width}_{op} {mode_name} x y" for op in ("plus", "minus", "mult", "div")]
    values += [f"{prefix}b{width}_sqrt {mode_name} x", f"{prefix}b{width}_fma {mode_name} x y z"]
    return result + "[" + separator.join(f"{prefix}bits_of_b{width} ({value})" for value in values) + "]"


def execute(cases, flocq, coqc, folder):
    lean, rocq = folder / "Modes.lean", folder / "Modes.v"
    lean.write_text(LEAN_HEADER + "#reduce ([\n" + ",\n".join(expression(c, "lean") for c in cases) +
                    "\n] : List (List Int))\n")
    rocq.write_text(COQ_HEADER + "Eval vm_compute in [\n" + ";\n".join(expression(c, "rocq") for c in cases) + "\n].\n")
    commands = {"lean": ["lake", "env", "lean", str(lean)],
                "rocq": [coqc, "-q", "-R", str(flocq / "src"), "Flocq", str(rocq)]}

    def observe(name):
        output = run(commands[name], timeout=180)
        (folder / f"{name}.out").write_text(output)
        rows = parse_result(output, name, len(cases))
        if any(len(row) != len(COLUMNS) for row in rows):
            raise ValueError(f"{name}: incomplete IEEE observation columns")
        return rows

    with ThreadPoolExecutor(max_workers=2) as pool:
        futures = {name: pool.submit(observe, name) for name in commands}
        return {name: future.result() for name, future in futures.items()}


def bootstrap(cases, rows, folder):
    path = folder / "OracleRegressions.lean"
    path.write_text(LEAN_HEADER + "\n".join(
        f"example : ({expression(case, 'lean')} : List Int) = {json.dumps(row)} := by decide +kernel"
        for case, row in zip(cases, rows, strict=True)) + "\n")
    output = run(["lake", "env", "lean", str(path)], timeout=180)
    (folder / "oracle_regressions.out").write_text(output)
    if output.strip():
        raise ValueError(f"unexpected kernel regression diagnostics: {output[:500]}")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--flocq-dir", type=Path, required=True)
    parser.add_argument("--seed", type=int, default=923451)
    parser.add_argument("--samples", type=int, default=10, help="random triples per mode and format")
    parser.add_argument("--batch-size", type=int, default=10)
    parser.add_argument("--replay", type=Path)
    parser.add_argument("--output", type=Path)
    parser.add_argument("--skip-build", action="store_true", help="caller must have built current Bits sources")
    args = parser.parse_args()
    if args.samples < 0 or args.batch_size < 1:
        parser.error("samples must be nonnegative and batch-size positive")
    cases = ([validate_case(c) for c in json.loads(args.replay.read_text())]
             if args.replay else corpus(args.seed, args.samples))
    if not cases:
        parser.error("an empty corpus is not a pass")
    flocq = args.flocq_dir.resolve()
    pin, coqc = verify_reference(flocq), configured_coqc(flocq)
    output = (args.output or Path(tempfile.mkdtemp(prefix="floatspec-ieee-modes-"))).resolve()
    output.mkdir(parents=True, exist_ok=True)
    if any(output.iterdir()):
        parser.error("output directory must be empty")
    (output / "cases.json").write_text(json.dumps(cases, indent=2) + "\n")
    report = {"seed": args.seed, "reference": pin, "lean_source_sha256": lean_source_fingerprint(),
              "lean_head": run(["git", "rev-parse", "HEAD"]).strip(), "cases": len(cases),
              "worktree_status": run(["git", "status", "--porcelain"]).strip(),
              "lean_version": run(["lake", "env", "lean", "--version"]).strip(),
              "rocq_version": run([coqc, "--version"]).strip(), "host": run(["uname", "-sm"]).strip(),
              "method": "Lean kernel reduction versus pinned Rocq, all 5 rounding modes, exact NaN payloads",
              "groups": dict(Counter(f"binary{c[0]}:{LEAN_MODES[c[1]]}" for c in cases)),
              "fresh_build": not args.skip_build, "status": "running", "compared_cases": 0,
              "bootstrapped_lean_cases": 0, "mismatches": []}

    def save():
        (output / "report.json").write_text(json.dumps(report, indent=2) + "\n")
        if report["mismatches"]:
            (output / "replay.json").write_text(json.dumps([m["case"] for m in report["mismatches"]], indent=2) + "\n")

    save()
    print(f"Executing {len(cases)} IEEE mode cases; artifacts={output}", flush=True)
    started = time.monotonic()
    try:
        if not args.skip_build:
            (output / "lean_build.out").write_text(run(["lake", "build", "FloatSpec.src.IEEE754.Bits"], timeout=600))
        require_lean_source_snapshot(report["lean_source_sha256"])
        for offset in range(0, len(cases), args.batch_size):
            batch = cases[offset:offset + args.batch_size]
            folder = output / f"batch_{offset:06d}"
            folder.mkdir()
            results = execute(batch, flocq, coqc, folder)
            for case, lean, rocq in zip(batch, results["lean"], results["rocq"], strict=True):
                if lean != rocq:
                    report["mismatches"].append({"case": case, "lean": lean, "rocq": rocq,
                        "columns": [name for name, a, b in zip(COLUMNS, lean, rocq, strict=True) if a != b]})
            report["compared_cases"] += len(batch)
            save()
            if results["lean"] == results["rocq"]:
                bootstrap(batch, results["rocq"], folder)
                report["bootstrapped_lean_cases"] += len(batch)
            require_lean_source_snapshot(report["lean_source_sha256"])
            save()
            print(f"{report['compared_cases']}/{len(cases)}; mismatches={len(report['mismatches'])}", flush=True)
        report["status"] = "mismatch" if report["mismatches"] else "passed"
    except BaseException as error:
        report["status"], report["error"] = "error", f"{type(error).__name__}: {error}"
        raise
    finally:
        report["elapsed_seconds"] = round(time.monotonic() - started, 3)
        save()
    if report["mismatches"]:
        raise SystemExit(f"IEEE mode mismatches; see {output / 'report.json'}")
    print(f"PASS: {len(cases)} IEEE mode cases; see {output / 'report.json'}")


if __name__ == "__main__":
    main()
