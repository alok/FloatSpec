#!/usr/bin/env python3
"""Compare macOS/native Lean binary64, the Lean model, and pinned Flocq.

All inputs are raw uint64 words. NaNs are canonicalized explicitly through the
single-NaN observation model. Native frexp equality is checked only on nonzero
finite inputs; exceptional observations are still retained and reported. Every
Lean-model result is compared with Rocq, including exceptional inputs, and each
agreeing result is promoted to a kernel-checked Lean equality.
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

from flocq_bridge import ROOT, configured_coqc, parse_result, run, verify_reference


LEAN_HEADER = """import FloatSpec.Test.NativeIEEE
open FloatSpec.Test.NativeIEEE
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option pp.maxSteps 200000
set_option pp.deepTerms true
"""
COQ_HEADER = ROOT / "scripts/fixtures/NativeIEEE.v"
MASK = (1 << 64) - 1


def validate_word(word: int) -> int:
    if type(word) is not int or not 0 <= word <= MASK:
        raise ValueError("input must be an integer uint64 bit pattern")
    return word


def category(word: int) -> str:
    """Classify the public binary64 encoding, not its arithmetic result."""
    validate_word(word)
    exponent, fraction = (word >> 52) & 0x7ff, word & ((1 << 52) - 1)
    if exponent == 0x7ff:
        return "nan" if fraction else "infinity"
    if exponent == 0:
        return "subnormal" if fraction else "zero"
    return "normal"


def corpus(seed: int, samples: int) -> list[int]:
    # Both signs, both sides of exponent transitions, significand boundaries,
    # signaling/quiet NaN payloads, powers of two, and ordinary random words.
    words = []
    for sign in (0, 1 << 63):
        for exponent in (0, 1, 2, 1022, 1023, 1024, 2045, 2046, 2047):
            for fraction in (0, 1, 2, (1 << 51) - 1, 1 << 51,
                             (1 << 52) - 2, (1 << 52) - 1):
                words.append(sign | (exponent << 52) | fraction)
        for power in range(52):
            words.extend(sign | fraction for fraction in
                         ((1 << power) - 1, 1 << power, (1 << power) + 1))
    rng = random.Random(seed)
    words.extend(rng.getrandbits(64) for _ in range(samples))
    return list(dict.fromkeys(words))


def native_source(words: list[int]) -> str:
    return (LEAN_HEADER + "def main : IO Unit :=\n  IO.println ((" +
            json.dumps(words) + " : List UInt64).map nativeObservation)\n")


def execute(words: list[int], flocq: Path, coqc: str, folder: Path) -> dict[str, list[list[int]]]:
    paths = {name: folder / filename for name, filename in
             (("native", "Native.lean"), ("model", "Model.lean"), ("rocq", "NativeIEEE.v"))}
    paths["native"].write_text(native_source(words))
    paths["model"].write_text(LEAN_HEADER + "#reduce ([" +
                             ", ".join(f"modelObservation {word}" for word in words) +
                             "] : List (List Int))\n")
    paths["rocq"].write_text(COQ_HEADER.read_text() + "\nEval vm_compute in [" +
                            "; ".join(f"observation {word}" for word in words) + "].\n")
    commands = {"native": ["lake", "env", "lean", "--run", str(paths["native"])],
                "model": ["lake", "env", "lean", str(paths["model"])],
                "rocq": [coqc, "-q", "-R", str(flocq / "src"), "Flocq", str(paths["rocq"])]}

    def observe(name: str) -> list[list[int]]:
        output = run(commands[name])
        (folder / f"{name}.out").write_text(output)
        rows = parse_result(output, "rocq" if name == "rocq" else "lean", len(words))
        if any(len(row) != 5 for row in rows):
            raise ValueError(f"{name}: expected all five observation columns")
        return rows

    with ThreadPoolExecutor(max_workers=3) as pool:
        futures = {name: pool.submit(observe, name) for name in commands}
        return {name: future.result() for name, future in futures.items()}


def compare(words: list[int], observations: dict[str, list[list[int]]]) -> tuple[list, list]:
    mismatches, exceptions = [], []
    if set(observations) != {"native", "model", "rocq"}:
        raise ValueError("all three execution paths are required")
    for name, rows in observations.items():
        if len(rows) != len(words) or any(len(row) != 5 for row in rows):
            raise ValueError(f"{name}: incomplete observations")
    for index, word in enumerate(words):
        native, model, rocq = (observations[name][index] for name in ("native", "model", "rocq"))
        kind = category(word)
        record = {"word": word, "hex": f"0x{word:016x}", "category": kind,
                  "native": native, "model": model, "rocq": rocq}
        if model != rocq:
            mismatches.append({**record, "path": "model-versus-rocq"})
        # Zero/nonfinite frexp results are outside native_frExp_equiv's domain,
        # not an excuse to skip their decoding or successor/predecessor checks.
        width = 5 if kind in ("normal", "subnormal") else 3
        if native[:width] != rocq[:width]:
            mismatches.append({**record, "path": "native-versus-rocq"})
        if width == 3:
            exceptions.append({**record, "frexp_equality_asserted": False})
    return mismatches, exceptions


def bootstrap_lean(words: list[int], expected: list[list[int]], folder: Path) -> None:
    path = folder / "OracleRegressions.lean"
    statements = [f"example : modelObservation {word} = {json.dumps(row)} := by decide +kernel"
                  for word, row in zip(words, expected, strict=True)]
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
    parser.add_argument("--samples", type=int, default=200)
    parser.add_argument("--batch-size", type=int, default=25)
    parser.add_argument("--output", type=Path)
    parser.add_argument("--replay", type=Path, help="JSON array of uint64 bit patterns")
    args = parser.parse_args()
    if args.samples < 0 or args.batch_size < 1:
        parser.error("samples must be nonnegative and batch-size positive")
    flocq = args.flocq_dir.resolve()
    pin = verify_reference(flocq)
    coqc = args.coqc or configured_coqc(flocq)
    words = ([validate_word(word) for word in json.loads(args.replay.read_text())]
             if args.replay else corpus(args.seed, args.samples))
    if not words:
        parser.error("empty corpus is not a successful test")
    output = (args.output or Path(tempfile.mkdtemp(prefix="floatspec-native-ieee-"))).resolve()
    output.mkdir(parents=True, exist_ok=True)
    if any(output.iterdir()):
        parser.error("output directory must be empty; previous evidence is not overwritten")
    (output / "cases.json").write_text(json.dumps(words, indent=2) + "\n")
    report = {"seed": args.seed, "reference": pin, "cases": len(words),
              "categories": dict(Counter(map(category, words))), "status": "running",
              "lean_head": run(["git", "rev-parse", "HEAD"]).strip(),
              "worktree_status": run(["git", "status", "--porcelain"]).strip(),
              "lean_version": run(["lake", "env", "lean", "--version"]).strip(),
              "rocq_version": run([coqc, "--version"]).strip(),
              "host": run(["uname", "-sm"]).strip(),
              "method": "Native FFI execution, Lean kernel reduction, Rocq vm_compute",
              "nan_observation": "single canonical NaN; payload identity not claimed",
              "compared_cases": 0, "bootstrapped_lean_cases": 0,
              "mismatches": [], "exceptional_frexp_observations": []}
    report_path = output / "report.json"

    def save() -> None:
        report_path.write_text(json.dumps(report, indent=2) + "\n")
        if report["mismatches"]:
            (output / "replay.json").write_text(json.dumps(list(dict.fromkeys(
                row["word"] for row in report["mismatches"])), indent=2) + "\n")

    save()
    print(f"Executing {len(words)} binary64 inputs; seed={args.seed}; artifacts={output}", flush=True)
    started = time.monotonic()
    try:
        build = run(["lake", "build", "FloatSpec.Test.NativeIEEE"], timeout=600)
        (output / "lean_build.out").write_text(build)
        for offset in range(0, len(words), args.batch_size):
            batch = words[offset:offset + args.batch_size]
            folder = output / f"batch_{offset:06d}"
            folder.mkdir()
            observations = execute(batch, flocq, coqc, folder)
            mismatches, exceptions = compare(batch, observations)
            report["mismatches"].extend(mismatches)
            report["exceptional_frexp_observations"].extend(exceptions)
            report["compared_cases"] += len(batch)
            save()
            if observations["model"] == observations["rocq"]:
                bootstrap_lean(batch, observations["rocq"], folder)
                report["bootstrapped_lean_cases"] += len(batch)
                save()
            print(f"{report['compared_cases']}/{len(words)}; "
                  f"mismatches={len(report['mismatches'])}", flush=True)
        report["status"] = "mismatch" if report["mismatches"] else "passed"
    except BaseException as error:
        report["status"] = "error"
        report["error"] = f"{type(error).__name__}: {error}"
        raise
    finally:
        report["elapsed_seconds"] = round(time.monotonic() - started, 3)
        save()
    if report["mismatches"]:
        raise SystemExit(f"{len(report['mismatches'])} mismatches; see {report_path}")
    print(f"PASS: {len(words)} three-way binary64 cases; see {report_path}")


if __name__ == "__main__":
    main()
