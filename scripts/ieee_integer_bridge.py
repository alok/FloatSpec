#!/usr/bin/env python3
"""Cross-test IEEE nearby-integer rounding and unbounded integer truncation.

Compiled Lean, kernel reduction, and pinned Rocq agree exactly, including NaN
payloads. Native floor/ceil/round check directed and nearest-away modes. Native
unsigned conversion checks truncation only on finite inputs with |x| < 2^64;
the source integer result is unbounded and remains checked elsewhere.
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
from ieee_scale_bridge import canonical, category

MODES = (".RNE", ".RTZ", ".RTN", ".RTP", ".RNA")
COQ_MODES = ("mode_NE", "mode_ZR", "mode_DN", "mode_UP", "mode_NA")
COLUMNS = ("input", "nearby", "trunc", "single_nearby", "single_trunc")
LEAN_HEADER = """import FloatSpec.src.IEEE754.Bits
import FloatSpec.src.IEEE754.BinarySingleNaNSourceFacade
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option exponentiation.threshold 5000
set_option pp.maxSteps 200000
set_option pp.deepTerms true
private instance : Prec_gt_0 (24 : Int) := ⟨by decide⟩
private instance : Prec_lt_emax (24 : Int) (128 : Int) := ⟨by decide⟩
private instance : Prec_gt_0 (53 : Int) := ⟨by decide⟩
private instance : Prec_lt_emax (53 : Int) (1024 : Int) := ⟨by decide⟩
"""
COQ_HEADER = """From Stdlib Require Import ZArith List.
From Flocq Require Import IEEE754.Bits IEEE754.Binary IEEE754.BinarySingleNaN.
Import ListNotations.
Open Scope Z_scope.
"""


def validate_case(case):
    if not isinstance(case, (list, tuple)) or len(case) != 3 or any(type(n) is not int for n in case):
        raise ValueError("case must be [width, mode, word] integers")
    width, mode, word = case
    if width not in (32, 64) or mode not in range(5) or not 0 <= word < 1 << width:
        raise ValueError("width must be 32/64, mode 0..4, and input an unsigned word")
    return tuple(case)


def corpus(seed, samples):
    rng, cases = random.Random(seed), []
    for width, fraction, bias in ((32, 23, 127), (64, 52, 1023)):
        inf = (2 * bias + 1) << fraction
        positive = [0, 1, (1 << fraction) - 1, 1 << fraction, inf - 1, inf, inf + 1,
                    inf + (1 << (fraction - 1))]
        # Halfway integers, adjacent representable inputs, the 2^precision
        # integer-spacing transition, and both sides of the uint64 boundary.
        for exponent in (bias - 1, bias, bias + 1, bias + fraction - 1,
                         bias + fraction, bias + 63, bias + 64):
            for mantissa in (0, 1 << (fraction - 1), (1 << fraction) - 1):
                word = (exponent << fraction) + mantissa
                positive.extend((word - 1, word, word + 1))
        words = [sign | word for sign in (0, 1 << (width - 1)) for word in positive]
        for mode in range(5):
            cases.extend((width, mode, word) for word in words)
            cases.extend((width, mode, rng.getrandbits(width)) for _ in range(samples))
    return list(dict.fromkeys(cases))


def native_checked_columns(case):
    width, mode, word = validate_case(case)
    fraction, bias = (23, 127) if width == 32 else (52, 1023)
    magnitude = word & ((1 << (width - 1)) - 1)
    checked = [0]
    # C round uses ties-away, not nearest-even. Retain that observation but do
    # not claim it implements RNE. Four other modes have direct native checks.
    if mode != 0:
        checked.extend((1, 3))
    if magnitude < (bias + 64) << fraction:
        checked.extend((2, 4))
    return sorted(checked)


def expression(case, language):
    width, mode, word = validate_case(case)
    if language == "native":
        kind, uint = ("Float32", "UInt32") if width == 32 else ("Float", "UInt64")
        rounded = ("x.round", "if x < 0 then x.ceil else x.floor", "x.floor", "x.ceil", "x.round")[mode]
        negative = "true" if word >> (width - 1) else "false"
        return (f"let x := {kind}.ofBits ({word} : {uint}); let y := {rounded}; "
                f"let z : Int := if {negative} then -(x.abs.toUInt64.toNat : Int) "
                "else x.abs.toUInt64.toNat; "
                "[(x.toBits.toNat : Int), y.toBits.toNat, z, y.toBits.toNat, z]")
    if language == "lean":
        return (f"let x := b{width}_of_bits {word}; let s := Binary.B2BSN x; "
                f"let y := Binary.Bnearbyint unop_nan_pl{width} {MODES[mode]} x; "
                f"let sy := Binary.BSN2B (unop_nan_pl{width} x) (BinarySingleNaN.Bnearbyint {MODES[mode]} s); "
                f"[bits_of_b{width} x, bits_of_b{width} y, Binary.Btrunc x, "
                f"bits_of_b{width} sy, BinarySingleNaN.Btrunc s]")
    if language != "rocq":
        raise ValueError("unknown execution language")
    prec, emax = (24, 128) if width == 32 else (53, 1024)
    proof = "(ltac:(compute; reflexivity))"
    return (f"let x := b{width}_of_bits {word} in let s := Binary.B2BSN {prec} {emax} x in "
            f"let y := Binary.Bnearbyint {prec} {emax} {proof} unop_nan_pl{width} {COQ_MODES[mode]} x in "
            f"let sy := Binary.BSN2B {prec} {emax} (unop_nan_pl{width} x) "
            f"(@BinarySingleNaN.Bnearbyint {prec} {emax} {proof} {COQ_MODES[mode]} s) in "
            f"[bits_of_b{width} x; bits_of_b{width} y; Binary.Btrunc {prec} {emax} x; "
            f"bits_of_b{width} sy; @BinarySingleNaN.Btrunc {prec} {emax} s]")


def program(cases, path):
    rows = [expression(case, "lean" if path in ("lean", "compiled") else path) for case in cases]
    if path == "rocq":
        return COQ_HEADER + "Eval vm_compute in [\n" + ";\n".join(rows) + "\n].\n"
    action = "#reduce (" if path == "lean" else "def main : IO Unit := IO.println ("
    return LEAN_HEADER + action + "[\n" + ",\n".join(rows) + "\n] : List (List Int))\n"


def execute(cases, flocq, coqc, folder):
    def observe(path):
        file = folder / ("IntegerRounding.v" if path == "rocq" else f"{path.title()}.lean")
        file.write_text(program(cases, path))
        command = ([coqc, "-q", "-R", str(flocq / "src"), "Flocq", str(file)] if path == "rocq"
                   else ["lake", "env", "lean", *([] if path == "lean" else ["--run"]), str(file)])
        output = run(command)
        (folder / f"{path}.out").write_text(output)
        rows = parse_result(output, "rocq" if path == "rocq" else "lean", len(cases))
        if any(len(row) != len(COLUMNS) for row in rows):
            raise ValueError(f"{path}: incomplete integer-rounding observations")
        return rows
    with ThreadPoolExecutor(max_workers=4) as pool:
        futures = {name: pool.submit(observe, name) for name in ("lean", "compiled", "rocq", "native")}
        return {name: future.result() for name, future in futures.items()}


def compare(cases, results):
    if set(results) != {"lean", "compiled", "rocq", "native"}:
        raise ValueError("all four execution paths are required")
    if any(len(rows) != len(cases) or any(len(row) != len(COLUMNS) for row in rows)
           for rows in results.values()):
        raise ValueError("incomplete integer-rounding observations")
    mismatches, exceptions = [], []
    for index, case in enumerate(cases):
        width, _, _ = validate_case(case)
        for rows in results.values():
            if any(type(value) is not int for value in rows[index]) or any(
                    not 0 <= rows[index][column] < 1 << width for column in (0, 1, 3)):
                raise ValueError("observed bit columns must be unsigned words and other columns integers")
        record = {"case": case, **{name: rows[index] for name, rows in results.items()}}
        for path in ("lean", "compiled"):
            wrong = [name for column, name in enumerate(COLUMNS)
                     if results[path][index][column] != results["rocq"][index][column]]
            if wrong:
                mismatches.append({**record, "path": path, "columns": wrong})
        checked = native_checked_columns(case)
        def normalized(row, column):
            return canonical(width, row[column]) if column in (0, 1, 3) else row[column]
        wrong = [COLUMNS[column] for column in checked
                 if normalized(results["native"][index], column) != normalized(results["rocq"][index], column)]
        if wrong:
            mismatches.append({**record, "path": "native", "columns": wrong})
        if len(checked) != len(COLUMNS):
            exceptions.append({**record, "native_checked_columns": [COLUMNS[column] for column in checked]})
    return mismatches, exceptions


def bootstrap(cases, rows, folder):
    path = folder / "OracleRegressions.lean"
    path.write_text(LEAN_HEADER + "\n".join(
        f"example : ({expression(case, 'lean')} : List Int) = {json.dumps(row)} := by decide +kernel"
        for case, row in zip(cases, rows, strict=True)) + "\n")
    output = run(["lake", "env", "lean", str(path)])
    (folder / "oracle_regressions.out").write_text(output)
    if output.strip():
        raise ValueError(f"unexpected kernel regression diagnostics: {output[:500]}")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--flocq-dir", type=Path, required=True)
    parser.add_argument("--coqc")
    parser.add_argument("--seed", type=int, default=730519)
    parser.add_argument("--samples", type=int, default=20)
    parser.add_argument("--batch-size", type=int, default=40)
    parser.add_argument("--replay", type=Path)
    parser.add_argument("--output", type=Path)
    parser.add_argument("--skip-build", action="store_true", help="reuse an explicitly prebuilt stable snapshot")
    args = parser.parse_args()
    if args.samples < 0 or args.batch_size < 1:
        parser.error("samples must be nonnegative and batch-size positive")
    cases = ([validate_case(case) for case in json.loads(args.replay.read_text())]
             if args.replay else corpus(args.seed, args.samples))
    if not cases:
        parser.error("an empty corpus is not a pass")
    flocq = args.flocq_dir.resolve()
    pin, coqc = verify_reference(flocq), args.coqc or configured_coqc(flocq)
    output = (args.output or Path(tempfile.mkdtemp(prefix="floatspec-ieee-integer-"))).resolve()
    output.mkdir(parents=True, exist_ok=True)
    if any(output.iterdir()):
        parser.error("output directory must be empty")
    (output / "cases.json").write_text(json.dumps(cases, indent=2) + "\n")
    report = {"seed": args.seed, "reference": pin, "cases": len(cases),
              "lean_source_sha256": lean_source_fingerprint(),
              "lean_head": run(["git", "rev-parse", "HEAD"]).strip(),
              "worktree_status": run(["git", "status", "--porcelain"]).strip(),
              "lean_version": run(["lake", "env", "lean", "--version"]).strip(),
              "rocq_version": run([coqc, "--version"]).strip(), "host": run(["uname", "-sm"]).strip(),
              "fresh_build": not args.skip_build, "status": "running", "compared_cases": 0,
              "bootstrapped_lean_cases": 0, "mismatches": [], "native_scope_exceptions": [],
              "groups": dict(Counter(f"binary{c[0]}:{MODES[c[1]]}:{category(c[0], c[2])}" for c in cases)),
              "method": "Exact compiled/kernel/Rocq nearby rounding and truncation; native checks with explicit scope"}
    def save():
        (output / "report.json").write_text(json.dumps(report, indent=2) + "\n")
        if report["mismatches"]:
            replay = list(dict.fromkeys(tuple(row["case"]) for row in report["mismatches"]))
            (output / "replay.json").write_text(json.dumps(replay, indent=2) + "\n")
    started = time.monotonic()
    save()
    print(f"Executing {len(cases)} integer-rounding cases; artifacts={output}", flush=True)
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
            mismatches, exceptions = compare(batch, results)
            report["mismatches"].extend(mismatches)
            report["native_scope_exceptions"].extend(exceptions)
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
        raise SystemExit(f"Integer-rounding mismatches; see {output / 'report.json'}")
    print(f"PASS: {len(cases)} integer-rounding cases; see {output / 'report.json'}")


if __name__ == "__main__":
    main()

