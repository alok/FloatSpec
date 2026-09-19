#!/usr/bin/env python3
"""Replayable finite differential execution of actual Lean and pinned Rocq definitions.

Run with uv run scripts/flocq_bridge.py --flocq-dir PATH. The reference must be
built with its configured compiler. No algorithm is reimplemented in an adapter:
the adapters only construct inputs and serialize integer/location/Boolean results.
Lean uses kernel reduction, including for integer definitions marked noncomputable;
Rocq uses vm_compute. Agreement is finite testing, not a proof of equivalence.
"""

from __future__ import annotations

import argparse
import ast
from collections import Counter
from concurrent.futures import ThreadPoolExecutor
from dataclasses import asdict, dataclass
import json
import os
from pathlib import Path
import random
import re
import subprocess
import tempfile
import time


ROOT = Path(__file__).resolve().parents[1]
LEAN_LOC = [".loc_Exact", ".loc_Inexact .lt", ".loc_Inexact .eq", ".loc_Inexact .gt"]
COQ_LOC = ["loc_Exact", "loc_Inexact Lt", "loc_Inexact Eq", "loc_Inexact Gt"]
OPS = ("power", "div_eucl", "location", "round", "truncate", "div", "plus", "sqrt")
ARITIES = dict(zip(OPS, (2, 2, 3, 3, 5, 6, 6, 4), strict=True))


@dataclass(frozen=True)
class Case:
    op: str
    args: tuple[int, ...]

    def __post_init__(self) -> None:
        if self.op not in ARITIES or len(self.args) != ARITIES[self.op]:
            raise ValueError(f"unknown operation or wrong arity: {self.op}")
        if not all(type(n) is int for n in self.args):
            raise ValueError("case arguments must be integers, not source text or Booleans")
        if self.op in ("truncate", "div", "plus", "sqrt") and self.args[0] < 2:
            raise ValueError("Flocq radix requires beta >= 2")
        loc_index = {"location": 2, "round": 1, "truncate": 3}.get(self.op)
        if loc_index is not None and self.args[loc_index] not in range(4):
            raise ValueError("location encoding must be 0, 1, 2, or 3")
        if self.op == "round" and self.args[0] not in (0, 1):
            raise ValueError("rounding sign must be 0 or 1")


def corpus(seed: int, samples: int) -> list[Case]:
    """Small exhaustive boundary grids plus independent seeded samples per API."""
    cases: list[Case] = []
    for base in (-3, -2, -1, 0, 1, 2, 3, 10):
        for exponent in range(-3, 7):
            cases.append(Case("power", (base, exponent)))
    for numerator in range(-16, 17):
        for denominator in range(-8, 9):
            cases.append(Case("div_eucl", (numerator, denominator)))
    for steps in range(-2, 11):
        for index in range(-2, 13):
            for loc in range(4):
                cases.append(Case("location", (steps, index, loc)))
    for sign in range(2):
        for loc in range(4):
            for mantissa in (-2, -1, 0, 1, 2):
                cases.append(Case("round", (sign, loc, mantissa)))
    # Deliberately include zero, negative mantissas/divisors, negative shifts,
    # and exponent boundaries. These are total-function comparisons, not a
    # claim that the corresponding real-number correctness preconditions hold.
    for base in (2, 3, 10):
        for mantissa in (-9, -1, 0, 1, 2, 3, 4, 8, 9, 16, 17):
            for shift in (-2, -1, 0, 1, 2):
                cases.append(Case("sqrt", (base, mantissa, shift, 0)))
                for loc in range(4):
                    cases.append(Case("truncate", (base, mantissa, -1, loc, shift)))
            for divisor in (-3, -1, 0, 1, 2, 3):
                for exponent in (-1, 0, 1):
                    cases.append(Case("div", (base, mantissa, 0, divisor, 0, exponent)))
                    cases.append(Case("plus", (base, mantissa, 0, divisor, 0, exponent)))
    rng = random.Random(seed)
    for op in OPS:
        for _ in range(samples):
            base = rng.choice((2, 3, 10, 16))
            m1, m2 = (rng.randint(-1024, 1024) for _ in range(2))
            e1, e2, target = (rng.randint(-3, 3) for _ in range(3))
            loc = rng.randrange(4)
            if op == "power":
                args = (rng.randint(-16, 16), rng.randint(-4, 8))
            elif op == "div_eucl":
                args = (m1, m2)
            elif op == "location":
                args = (rng.randint(-16, 128), rng.randint(-16, 128), loc)
            elif op == "round":
                args = (rng.randrange(2), loc, m1)
            elif op == "truncate":
                args = (base, m1, e1, loc, target)
            elif op in ("div", "plus"):
                args = (base, m1, e1, m2, e2, target)
            else:
                args = (base, m1, e1, target)
            cases.append(Case(op, args))
    return list(dict.fromkeys(cases))


def expressions(case: Case) -> tuple[str, str]:
    """Translate inputs only; all arithmetic is performed by imported APIs."""
    a = [f"({n})" for n in case.args]
    op = case.op
    if op == "power":
        return (f"[Zaux.Zpower {a[0]} {a[1]}]", f"[Zpower {a[0]} {a[1]}]")
    if op == "div_eucl":
        return (f"pair (Zaux.Z_div_eucl {a[0]} {a[1]})",
                f"pair (Z.div_eucl {a[0]} {a[1]})")
    if op == "location":
        loc_l, loc_c = LEAN_LOC[case.args[2]], COQ_LOC[case.args[2]]
        names = ("new_location_even", "new_location_odd", "new_location")
        return ("[" + ", ".join(f"location ({n} {a[0]} {a[1]} ({loc_l}))" for n in names) + "]",
                "[" + "; ".join(f"location ({n} {a[0]} {a[1]} ({loc_c}))" for n in names) + "]")
    if op == "round":
        sign = "true" if case.args[0] else "false"
        loc_l, loc_c = LEAN_LOC[case.args[1]], COQ_LOC[case.args[1]]
        calls = ("round_UP {loc}", f"round_sign_DN {sign} {{loc}}",
                 f"round_sign_UP {sign} {{loc}}", f"round_ZR {sign} {{loc}}",
                 f"round_N {sign} {{loc}}")
        lean = [f"boolean (Round.{call.format(loc=f'({loc_l})')})" for call in calls]
        coq = [f"boolean (Round.{call.format(loc=f'({loc_c})')})" for call in calls]
        lean.append(f"Round.cond_incr {sign} {a[2]}")
        coq.append(f"Round.cond_incr {sign} {a[2]}")
        return "[" + ", ".join(lean) + "]", "[" + "; ".join(coq) + "]"
    base_l, base_c = a[0], f"(Build_radix {a[0]} eq_refl)"
    if op == "truncate":
        loc_l, loc_c = LEAN_LOC[case.args[3]], COQ_LOC[case.args[3]]
        return (f"triple (Round.truncate_aux {base_l} ({a[1]}, {a[2]}, {loc_l}) {a[4]})",
                f"triple (Round.truncate_aux {base_c} ({a[1]}, {a[2]}, {loc_c}) {a[4]})")
    name = {"div": "Div.Fdiv_core", "plus": "Plus.Fplus_core", "sqrt": "Sqrt.Fsqrt_core"}[op]
    args = " ".join(a[1:])
    return f"located ({name} {base_l} {args})", f"located ({name} {base_c} {args})"


LEAN_HEADER = """import FloatSpec.src.Calc.Plus
import FloatSpec.src.Calc.Div
import FloatSpec.src.Calc.Sqrt
open FloatSpec.Core FloatSpec.Calc FloatSpec.Calc.Bracket
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option pp.maxSteps 10000000
set_option pp.deepTerms true
namespace Bridge
private def location : Location → Int
  | .loc_Exact => 0
  | .loc_Inexact .lt => 1
  | .loc_Inexact .eq => 2
  | .loc_Inexact .gt => 3
private def boolean (b : Bool) : Int := if b then 1 else 0
private def pair (p : Int × Int) : List Int := [p.1, p.2]
private def located (p : Int × Location) : List Int := [p.1, location p.2]
private def triple (p : Int × Int × Location) : List Int := [p.1, p.2.1, location p.2.2]
"""

COQ_HEADER = """From Stdlib Require Import ZArith List.
From Flocq Require Import Core.Zaux Calc.Bracket Calc.Round Calc.Plus Calc.Div Calc.Sqrt.
Import ListNotations.
Open Scope Z_scope.
Definition location (l : SpecFloat.location) : Z :=
  match l with
  | SpecFloat.loc_Exact => 0
  | SpecFloat.loc_Inexact Lt => 1
  | SpecFloat.loc_Inexact Eq => 2
  | SpecFloat.loc_Inexact Gt => 3
  end.
Definition boolean (b : bool) : Z := if b then 1 else 0.
Definition pair (p : Z * Z) : list Z := [fst p; snd p].
Definition located (p : Z * SpecFloat.location) : list Z := [fst p; location (snd p)].
Definition triple (p : Z * Z * SpecFloat.location) : list Z :=
  let '(m, e, l) := p in [m; e; location l].
"""


def parse_result(output: str, language: str, expected_count: int) -> list[list[int]]:
    """Reject malformed/partial output; never accept an empty comparison."""
    if language == "rocq":
        match = re.fullmatch(r"\s*=\s*(.*?)\s*:\s*list\s*\(list Z\)\s*", output, re.S)
        if not match:
            raise ValueError(f"unexpected Rocq output: {output[:500]}")
        output = match[1].replace(";", ",")
    else:
        output = re.sub(r"Int\.ofNat (\d+)", r"\1", output)
        output = re.sub(r"Int\.negSucc (\d+)", lambda m: str(-int(m[1]) - 1), output)
    if not re.fullmatch(r"[\s\[\],\-0-9]+", output):
        raise ValueError(f"unexpected {language} output: {output[:500]}")
    result = ast.literal_eval(output.strip())
    if (not isinstance(result, list) or len(result) != expected_count or
            not all(isinstance(row, list) and row and
                    all(type(n) is int for n in row) for row in result)):
        raise ValueError(f"invalid {language} result shape/count")
    return result


def run(command: list[str], timeout: int = 120) -> str:
    if command[0] == "lake" and os.environ.get("LEAN_TOOLCHAIN_OVERRIDE"):
        command = ["elan", "run", os.environ["LEAN_TOOLCHAIN_OVERRIDE"], *command]
    completed = subprocess.run(command, cwd=ROOT, text=True, capture_output=True, timeout=timeout)
    if completed.returncode:
        raise RuntimeError(f"command failed ({completed.returncode}): {command}\n"
                           f"{completed.stdout}\n{completed.stderr}")
    # Warnings are retained separately by the caller's artifact files; the two
    # reduction commands should not emit any warnings with these imports.
    if completed.stderr.strip():
        raise RuntimeError(f"unexpected stderr from {command}: {completed.stderr}")
    return completed.stdout


def configured_coqc(flocq: Path) -> str:
    status = (flocq / "config.status").read_text()
    match = re.search(r'^S\["COQC"\]="([^"]+)"$', status, re.M)
    if not match or not Path(match[1]).is_file():
        raise ValueError("Build Flocq first; its configured COQC is unavailable")
    return match[1]


def execute(cases: list[Case], flocq: Path, coqc: str, folder: Path) -> tuple[list, list]:
    rows = [expressions(case) for case in cases]
    lean_path, coq_path = folder / "Bridge.lean", folder / "Bridge.v"
    radices = sorted({case.args[0] for case in cases if case.op in ("truncate", "div", "plus", "sqrt")})
    instances = "".join(f"private instance : ValidRadix {base} := ⟨by decide⟩\n"
                        for base in radices if base != 2)
    lean_path.write_text(LEAN_HEADER + instances + "#reduce ([\n" +
                         ",\n".join(row[0] for row in rows) +
                         "\n] : List (List Int))\nend Bridge\n")
    coq_path.write_text(COQ_HEADER + "Eval vm_compute in [\n" +
                        ";\n".join(row[1] for row in rows) + "\n].\n")
    with ThreadPoolExecutor(max_workers=2) as pool:
        lean = pool.submit(run, ["lake", "env", "lean", str(lean_path)])
        coq = pool.submit(run, [coqc, "-q", "-R", str(flocq / "src"), "Flocq", str(coq_path)])
        outputs = lean.result(), coq.result()
    (folder / "lean.out").write_text(outputs[0])
    (folder / "rocq.out").write_text(outputs[1])
    return (parse_result(outputs[0], "lean", len(cases)),
            parse_result(outputs[1], "rocq", len(cases)))


def bootstrap_lean(cases: list[Case], expected: list[list[int]], folder: Path) -> None:
    """Turn Rocq observations into actual kernel-checked Lean regression proofs."""
    rows = [expressions(case)[0] for case in cases]
    radices = sorted({case.args[0] for case in cases if case.op in ("truncate", "div", "plus", "sqrt")})
    instances = "".join(f"private instance : ValidRadix {base} := ⟨by decide⟩\n"
                        for base in radices if base != 2)
    path = folder / "OracleRegressions.lean"
    path.write_text(LEAN_HEADER + instances + "example : ([\n" + ",\n".join(rows) +
                    "\n] : List (List Int)) = " + json.dumps(expected) +
                    " := by decide +kernel\nend Bridge\n")
    output = run(["lake", "env", "lean", str(path)])
    (folder / "oracle_regressions.out").write_text(output)
    if output.strip():
        raise ValueError(f"unexpected Lean regression diagnostics: {output[:500]}")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--flocq-dir", type=Path, required=True)
    parser.add_argument("--coqc", help="override the compiler recorded by the reference build")
    parser.add_argument("--seed", type=int, default=20260919)
    parser.add_argument("--samples", type=int, default=100, help="random cases per API after boundary grids")
    parser.add_argument("--batch-size", type=int, default=100)
    parser.add_argument("--output", type=Path)
    parser.add_argument("--replay", type=Path, help="JSON list of {op, args} inputs")
    args = parser.parse_args()
    if args.samples < 0 or args.batch_size < 1:
        parser.error("samples must be nonnegative and batch-size positive")
    flocq = args.flocq_dir.resolve()
    pin = run(["git", "rev-parse", "HEAD:Deps/flocq"]).strip()
    if run(["git", "-C", str(flocq), "rev-parse", "HEAD"]).strip() != pin:
        parser.error("reference checkout does not match the parent repository's gitlink")
    run(["git", "-C", str(flocq), "diff", "--exit-code", "HEAD", "--", "src"])
    untracked = run(["git", "-C", str(flocq), "ls-files", "--others", "--exclude-standard", "src"])
    if any(path.endswith(".v") for path in untracked.splitlines()):
        parser.error("reference contains untracked Rocq source files")
    coqc = args.coqc or configured_coqc(flocq)
    cases = ([Case(row["op"], tuple(row["args"])) for row in json.loads(args.replay.read_text())]
             if args.replay else corpus(args.seed, args.samples))
    if not cases:
        parser.error("empty corpus is not a successful test")
    output = (args.output or Path(tempfile.mkdtemp(prefix="floatspec-bridge-"))).resolve()
    output.mkdir(parents=True, exist_ok=True)
    if any(output.iterdir()):
        parser.error("output directory must be empty; previous evidence is not overwritten")
    (output / "cases.json").write_text(json.dumps([asdict(case) for case in cases], indent=2) + "\n")
    report = {"seed": args.seed, "reference": pin, "lean_head": run(["git", "rev-parse", "HEAD"]).strip(),
              "worktree_status": run(["git", "status", "--porcelain"]).strip(),
              "lean_version": run(["lake", "env", "lean", "--version"]).strip(),
              "rocq_version": run([coqc, "--version"]).strip(), "cases": len(cases),
              "operations": dict(Counter(case.op for case in cases)), "status": "running",
              "method": "Lean kernel reduction versus Rocq vm_compute; finite tests only",
              "bootstrapped_lean_cases": 0}
    report_path = output / "report.json"
    report_path.write_text(json.dumps(report, indent=2) + "\n")
    print(f"Executing {len(cases)} cases; seed={args.seed}; artifacts={output}", flush=True)
    started = time.monotonic()
    mismatches = []
    try:
        build = run(["lake", "build", "FloatSpec.src.Calc.Plus", "FloatSpec.src.Calc.Div",
                     "FloatSpec.src.Calc.Sqrt"], timeout=600)
        (output / "lean_build.out").write_text(build)
        for offset in range(0, len(cases), args.batch_size):
            batch = cases[offset:offset + args.batch_size]
            folder = output / f"batch_{offset:06d}"
            folder.mkdir()
            lean, rocq = execute(batch, flocq, coqc, folder)
            for index, (case, left, right) in enumerate(zip(batch, lean, rocq, strict=True)):
                if left != right:
                    mismatches.append({"index": offset + index, "case": asdict(case),
                                       "lean": left, "rocq": right})
            if lean == rocq:
                bootstrap_lean(batch, rocq, folder)
                report["bootstrapped_lean_cases"] += len(batch)
            print(f"{min(offset + args.batch_size, len(cases))}/{len(cases)}; "
                  f"mismatches={len(mismatches)}", flush=True)
        report["mismatches"] = mismatches
        report["status"] = "mismatch" if mismatches else "passed"
    except Exception as error:
        report["status"] = "error"
        report["error"] = str(error)
        raise
    finally:
        report["elapsed_seconds"] = round(time.monotonic() - started, 3)
        report_path.write_text(json.dumps(report, indent=2) + "\n")
    if mismatches:
        (output / "replay.json").write_text(json.dumps([m["case"] for m in mismatches], indent=2) + "\n")
        raise SystemExit(f"{len(mismatches)} mismatches; see {report_path}")
    print(f"PASS: {len(cases)} finite differential cases; see {report_path}")


if __name__ == "__main__":
    main()
