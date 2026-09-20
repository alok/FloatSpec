#!/usr/bin/env python3
"""Cross-test source IEEE arithmetic in every rounding mode, retaining NaN payloads.

This compares compiled Lean and kernel reduction of the port's own bit
decoders/operations with pinned Rocq. Full-payload results retain exact NaN
bits; separate direct and source-mode SingleNaN results retain constructors,
signs, mantissas, and exponents. It does not claim native hardware execution
of directed rounding. Inputs and complete generated prover programs are
retained, with per-case kernel regression proofs.
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
import ieee_exact_oracle as exact_oracle


LEAN_MODES = (".RNE", ".RTZ", ".RTN", ".RTP", ".RNA")
COQ_MODES = ("mode_NE", "mode_ZR", "mode_DN", "mode_UP", "mode_NA")
OPERATIONS = ("add", "sub", "mul", "div", "sqrt_left", "fma")
COLUMNS = ("left", "right", "third") + OPERATIONS + tuple(
    f"{api}_{op}_{field}" for api in ("single", "source_single")
    for op in OPERATIONS for field in ("kind", "sign", "mantissa", "exponent"))
LEAN_HEADER = """import FloatSpec.src.IEEE754.Bits
import FloatSpec.src.IEEE754.BinarySingleNaNSourceFacade
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option exponentiation.threshold 5000
set_option pp.maxSteps 200000
set_option pp.deepTerms true
private def standard : StandardFloat → List Int
  | .S754_zero s => [0, if s then 1 else 0, 0, 0]
  | .S754_infinity s => [1, if s then 1 else 0, 0, 0]
  | .S754_nan => [2, 0, 0, 0]
  | .S754_finite s m e => [3, if s then 1 else 0, m, e]
"""
COQ_HEADER = """From Stdlib Require Import ZArith List.
From Flocq Require Import IEEE754.Bits IEEE754.Binary IEEE754.BinarySingleNaN.
Import ListNotations.
Open Scope Z_scope.
Definition standard (x : SpecFloat.spec_float) : list Z :=
  match x with
  | SpecFloat.S754_zero s => [0; if s then 1 else 0; 0; 0]
  | SpecFloat.S754_infinity s => [1; if s then 1 else 0; 0; 0]
  | SpecFloat.S754_nan => [2; 0; 0; 0]
  | SpecFloat.S754_finite s m e => [3; if s then 1 else 0; Zpos m; e]
  end.
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
                   (nan1, inf, 0), (inf, nan2, 0), (sign, one, 0),
                   (inf, inf, sign | inf), (sign | inf, sign | inf, inf),
                   (inf, sign, nan3), (sign, inf, nan3), (max_finite, two, sign | inf),
                   (sign | max_finite, two, inf), (one, sign, sign), (sign, sign, sign)]
        for mode in range(5):
            cases.extend((width, mode, *triple) for triple in triples)
            for _ in range(samples):
                cases.append((width, mode, *(rng.getrandbits(width) for _ in range(3))))
    return list(dict.fromkeys(cases))


def expression(case, language):
    case = validate_case(case)
    if language not in ("lean", "rocq"):
        raise ValueError("language must be lean or rocq")
    width, mode, left, right, third = case
    prec, emax = (24, 128) if width == 32 else (53, 1024)
    mode_name = (LEAN_MODES if language == "lean" else COQ_MODES)[mode]
    prefix, separator = ("", ", ") if language == "lean" else ("Bits.", "; ")
    let = (lambda n, v: f"let {n} := {v}; ") if language == "lean" else (lambda n, v: f"let {n} := {v} in ")
    result = "".join(let(name, f"{prefix}b{width}_of_bits {word}")
                     for name, word in zip(("x", "y", "z"), (left, right, third), strict=True))
    values = ["x", "y", "z"]
    values += [f"{prefix}b{width}_{op} {mode_name} x y" for op in ("plus", "minus", "mult", "div")]
    values += [f"{prefix}b{width}_sqrt {mode_name} x", f"{prefix}b{width}_fma {mode_name} x y z"]
    if language == "lean":
        result += (f"letI : Prec_gt_0 {prec} := ⟨by decide⟩; "
                   f"letI : Prec_lt_emax {prec} {emax} := ⟨by decide⟩; ")
    for name in ("x", "y", "z"):
        converted = (f"Binary.B2BSN {name}" if language == "lean"
                     else f"@Binary.B2BSN {prec} {emax} {name}")
        result += let(f"single_{name}", converted)
    result += "[" + separator.join(f"{prefix}bits_of_b{width} ({value})" for value in values) + "]"
    for namespace, single_mode in (("BinarySingleNaN", LEAN_MODES[mode]),
                                   ("FloatSpec.IEEE754.BinarySingleNaN.Source", f".{COQ_MODES[mode]}")):
        for op in ("Bplus", "Bminus", "Bmult", "Bdiv", "Bsqrt", "Bfma"):
            arity = 1 if op == "Bsqrt" else 3 if op == "Bfma" else 2
            operands = " ".join(f"single_{name}" for name in ("x", "y", "z")[:arity])
            if language == "lean":
                result += (f" ++ standard (binarySingleNaNFloatToStandardFloat "
                           f"({namespace}.{op} {single_mode} {operands}))")
            else:
                result += (f" ++ standard (@BinarySingleNaN.B2SF {prec} {emax} "
                           f"(@BinarySingleNaN.{op} {prec} {emax} eq_refl eq_refl "
                           f"{COQ_MODES[mode]} {operands}))")
    return result


def compiled_source(cases):
    return (LEAN_HEADER + "def main : IO Unit := IO.println ([\n" +
            ",\n".join(expression(c, "lean") for c in cases) +
            "\n] : List (List Int))\n")


def execute(cases, flocq, coqc, folder):
    lean, rocq = folder / "Modes.lean", folder / "Modes.v"
    compiled = folder / "Compiled.lean"
    lean.write_text(LEAN_HEADER + "#reduce ([\n" + ",\n".join(expression(c, "lean") for c in cases) +
                    "\n] : List (List Int))\n")
    rocq.write_text(COQ_HEADER + "Eval vm_compute in [\n" + ";\n".join(expression(c, "rocq") for c in cases) + "\n].\n")
    compiled.write_text(compiled_source(cases))
    commands = {"lean": ["lake", "env", "lean", str(lean)],
                "compiled": ["lake", "env", "lean", "--run", str(compiled)],
                "rocq": [coqc, "-q", "-R", str(flocq / "src"), "Flocq", str(rocq)]}

    def observe(name):
        output = run(commands[name], timeout=180)
        (folder / f"{name}.out").write_text(output)
        rows = parse_result(output, name, len(cases))
        if any(len(row) != len(COLUMNS) for row in rows):
            raise ValueError(f"{name}: incomplete IEEE observation columns")
        return rows

    with ThreadPoolExecutor(max_workers=3) as pool:
        futures = {name: pool.submit(observe, name) for name in commands}
        return {name: future.result() for name, future in futures.items()}


def compare(cases, results):
    if set(results) != {"lean", "compiled", "rocq"}:
        raise ValueError("all three IEEE execution paths are required")
    for name, rows in results.items():
        if len(rows) != len(cases) or any(len(row) != len(COLUMNS) for row in rows):
            raise ValueError(f"{name}: incomplete IEEE observations")
    mismatches = []
    for index, case in enumerate(cases):
        paths = [name for name in ("lean", "compiled") if results[name][index] != results["rocq"][index]]
        if paths:
            mismatches.append({"case": case, "paths": paths,
                **{name: rows[index] for name, rows in results.items()},
                "columns": [column for offset, column in enumerate(COLUMNS)
                            if any(results[name][index][offset] != results["rocq"][index][offset]
                                   for name in paths)]})
    return mismatches


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
    parser.add_argument("--coqc", help="override the compiler recorded by the reference build")
    parser.add_argument("--seed", type=int, default=923451)
    parser.add_argument("--samples", type=int, default=10, help="random triples per mode and format")
    parser.add_argument("--batch-size", type=int, default=10)
    parser.add_argument("--replay", type=Path)
    parser.add_argument("--output", type=Path)
    parser.add_argument("--skip-build", action="store_true", help="caller must have built current Bits and SingleNaN source facade")
    args = parser.parse_args()
    if args.samples < 0 or args.batch_size < 1:
        parser.error("samples must be nonnegative and batch-size positive")
    cases = ([validate_case(c) for c in json.loads(args.replay.read_text())]
             if args.replay else corpus(args.seed, args.samples))
    if not cases:
        parser.error("an empty corpus is not a pass")
    flocq = args.flocq_dir.resolve()
    pin, coqc = verify_reference(flocq), args.coqc or configured_coqc(flocq)
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
              "columns": COLUMNS,
              "method": "Compiled Lean and kernel reduction versus pinned Rocq, all 5 modes; full-payload bits plus direct/source-mode SingleNaN constructors",
              "groups": dict(Counter(f"binary{c[0]}:{LEAN_MODES[c[1]]}" for c in cases)),
              "fresh_build": not args.skip_build, "status": "running", "compared_cases": 0,
              "compiled_cases": 0, "bootstrapped_lean_cases": 0,
              "oracle_scope": exact_oracle.SCOPE, "oracle_assertions": 0,
              "oracle_mismatches": [], "mismatches": []}

    def save():
        (output / "report.json").write_text(json.dumps(report, indent=2) + "\n")
        failures = report["mismatches"] + report["oracle_mismatches"]
        if failures:
            replay = list(dict.fromkeys(tuple(row["case"]) for row in failures))
            (output / "replay.json").write_text(json.dumps(replay, indent=2) + "\n")

    save()
    print(f"Executing {len(cases)} IEEE mode cases; artifacts={output}", flush=True)
    started = time.monotonic()
    try:
        if not args.skip_build:
            (output / "lean_build.out").write_text(run(["lake", "build", "FloatSpec.src.IEEE754.Bits",
                "FloatSpec.src.IEEE754.BinarySingleNaNSourceFacade"], timeout=600))
        require_lean_source_snapshot(report["lean_source_sha256"])
        for offset in range(0, len(cases), args.batch_size):
            batch = cases[offset:offset + args.batch_size]
            folder = output / f"batch_{offset:06d}"
            folder.mkdir()
            results = execute(batch, flocq, coqc, folder)
            report["mismatches"].extend(compare(batch, results))
            oracle_failures, assertions = exact_oracle.compare_columns(
                batch, results, COLUMNS, exact_oracle.mode_columns)
            report["oracle_mismatches"].extend(oracle_failures)
            report["oracle_assertions"] += assertions
            report["compared_cases"] += len(batch)
            report["compiled_cases"] += len(batch)
            save()
            logical_oracle_failure = any(
                failure["path"] in ("lean-versus-exact-oracle", "rocq-versus-exact-oracle")
                for failure in oracle_failures)
            if results["lean"] == results["rocq"] and not logical_oracle_failure:
                bootstrap(batch, results["rocq"], folder)
                report["bootstrapped_lean_cases"] += len(batch)
            require_lean_source_snapshot(report["lean_source_sha256"])
            save()
            print(f"{report['compared_cases']}/{len(cases)}; mismatches={len(report['mismatches'])}; "
                  f"oracle_mismatches={len(report['oracle_mismatches'])}", flush=True)
        report["status"] = "mismatch" if report["mismatches"] or report["oracle_mismatches"] else "passed"
    except BaseException as error:
        report["status"], report["error"] = "error", f"{type(error).__name__}: {error}"
        raise
    finally:
        report["elapsed_seconds"] = round(time.monotonic() - started, 3)
        save()
    if report["mismatches"] or report["oracle_mismatches"]:
        raise SystemExit(f"IEEE mode or exact-oracle mismatches; see {output / 'report.json'}")
    print(f"PASS: {len(cases)} IEEE mode cases; see {output / 'report.json'}")


if __name__ == "__main__":
    main()
