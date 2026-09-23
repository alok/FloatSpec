#!/usr/bin/env python3
"""Exemplar lane: real Flocq client programs, trimmed and run on both sides.

Each exemplar in scripts/fixtures/exemplars/ is a pair:

- NAME.v, a trimmed Rocq program that depends only on the pinned Flocq and
  prints one ``list (list Z)`` with ``Eval vm_compute``;
- NAME.lean, which computes the same rows with FloatSpec's executable API
  and prints them with ``#eval``.

Both sides must print identical rows (differential verdict). The rows are
then checked, separately for each side, against the theorems the upstream
program proves (oracle verdict). Oracles use exact rationals and never
reuse the algorithms under test. Rows whose theorem premises are false are
counted, not judged; some exemplars include such rows on purpose as
positive controls, to show that the oracle can detect a violation.

Run with:
    uv run scripts/flocq_exemplars.py --flocq-dir PATH [--only NAME ...] [--output DIR]

Agreement is finite testing, not a proof of equivalence. Provenance and
trimming records are in scripts/fixtures/exemplars/README.md.
"""

from __future__ import annotations

import argparse
from collections.abc import Callable, Sequence
from concurrent.futures import ThreadPoolExecutor
from dataclasses import asdict, dataclass, field
from decimal import Decimal, localcontext
from fractions import Fraction
import hashlib
import json
from math import isqrt
from pathlib import Path
import shutil
import tempfile
import time

import flocq_bridge as bridge

FIXTURES = bridge.ROOT / "scripts" / "fixtures" / "exemplars"
# Upstream commits the fixtures were trimmed from (see the README).
UPSTREAM_COMMITS = {
    "flocq": "7aab8f55bceec0cfafc3b3bc0e77e0dbb5a70c5f",
}
# Fixture files that must stay byte-identical to the pinned upstream file.
UPSTREAM_VERBATIM = {"Compute.v": "examples/Compute.v"}
# Shared modules, compiled in this order and importable as Exemplars.NAME.
SHARED = ("Compute", "Choices")
# Deprecation warnings from the verbatim upstream file are its own; any
# other Rocq or Lean diagnostic fails the run.
VERBATIM_ROCQ_FLAGS = ("-w", "-deprecated")

Row = list[int]


# ---------------------------------------------------------------------------
# Exact generic-format rounding (independent of Flocq's integer algorithms)
# ---------------------------------------------------------------------------

def value(beta: int, mantissa: int, exponent: int) -> Fraction:
    return Fraction(beta) ** exponent * mantissa


def _mag(at_least: Callable[[int], bool]) -> int:
    """The e with beta^(e-1) <= |x| < beta^e, given the test |x| >= beta^k."""
    if at_least(0):
        low, high = 0, 1
        while at_least(high):
            low, high = high, high * 2
    else:
        low, high = -1, 0
        while not at_least(low):
            low, high = low * 2, low
    while high - low > 1:  # invariant: at_least(low) and not at_least(high)
        middle = (low + high) // 2
        if at_least(middle):
            low = middle
        else:
            high = middle
    return low + 1


def mag_rational(beta: int, x: Fraction) -> int:
    x = abs(x)
    if x == 0:
        raise ValueError("mag of zero")
    return _mag(lambda k: x >= Fraction(beta) ** k)


def _round_integer(mode, floor: int, exact: bool, half: int, positive: bool) -> int:
    """Round a real v with floor(v) = floor; half = sign(v - floor - 1/2)."""
    if exact:
        return floor
    if mode == "DN":
        return floor
    if mode == "UP":
        return floor + 1
    if mode == "ZR":
        return floor if positive else floor + 1
    if half < 0:
        return floor
    if half > 0:
        return floor + 1
    if mode == "NE":
        return floor if floor % 2 == 0 else floor + 1
    if mode == "NA":
        return floor + 1 if positive else floor
    if isinstance(mode, tuple) and mode[0] == "N":
        return floor + 1 if mode[1](floor) else floor
    raise ValueError(f"unknown rounding mode {mode!r}")


def round_rational(beta: int, fexp: Callable[[int], int], mode, x: Fraction) -> Fraction:
    """Flocq's round beta fexp rnd x = rnd(x * beta^-cexp x) * beta^(cexp x)."""
    if x == 0:
        return Fraction(0)
    c = fexp(mag_rational(beta, x))
    scaled = x / Fraction(beta) ** c
    floor = scaled.numerator // scaled.denominator
    frac = scaled - floor
    half = (frac > Fraction(1, 2)) - (frac < Fraction(1, 2))
    return _round_integer(mode, floor, frac == 0, half, x > 0) * Fraction(beta) ** c


def round_sqrt(beta: int, fexp: Callable[[int], int], mode, q: Fraction) -> Fraction:
    """round beta fexp rnd (sqrt q); Rocq's sqrt of a negative number is 0."""
    if q <= 0:
        return Fraction(0)
    c = fexp(_mag(lambda k: q >= Fraction(beta) ** (2 * k)))
    scaled = q / Fraction(beta) ** (2 * c)          # (sqrt q / beta^c)^2
    floor = isqrt(scaled.numerator * scaled.denominator) // scaled.denominator
    exact = floor * floor == scaled
    midpoint = (Fraction(2 * floor + 1, 2)) ** 2
    half = (scaled > midpoint) - (scaled < midpoint)
    return _round_integer(mode, floor, exact, half, True) * Fraction(beta) ** c


def in_generic_format(beta: int, fexp: Callable[[int], int], x: Fraction) -> bool:
    """Flocq's generic_format: x is an integer multiple of beta^(cexp x)."""
    return x == 0 or (x / Fraction(beta) ** fexp(mag_rational(beta, x))).denominator == 1


def flx(prec: int) -> Callable[[int], int]:
    return lambda e: e - prec


def flt(emin: int, prec: int) -> Callable[[int], int]:
    return lambda e: max(e - prec, emin)


def fix(emin: int) -> Callable[[int], int]:
    return lambda e: emin


def ftz(emin: int, prec: int) -> Callable[[int], int]:
    return lambda e: emin + prec - 1 if e - prec < emin else e - prec


# ---------------------------------------------------------------------------
# Oracles
# ---------------------------------------------------------------------------

@dataclass
class OracleReport:
    holds: int = 0
    premise_false: int = 0
    violations: list[str] = field(default_factory=list)
    # Rows outside a theorem's premises that do break its conclusion. For
    # exemplars that include such controls, at least one is required.
    control_breaks: int = 0

    def check(self, label: str, ok: bool | None) -> None:
        if ok is None:
            self.premise_false += 1
        elif ok:
            self.holds += 1
        else:
            self.violations.append(label)


COMPUTE_GRID_FEXPS = {0: flx(3), 1: flt(-3, 3), 2: fix(-1), 3: ftz(-3, 3)}
CHOICE_MODES = {0: "DN", 1: "UP", 2: "ZR", 3: "NE", 4: "NA"}


def oracle_compute_grid(rows: Sequence[Row]) -> OracleReport:
    """Compute.v plus/mult/div/sqrt_correct: each is round of the exact op."""
    report = OracleReport()
    for index, row in enumerate(rows):
        beta, fk, ck, mx, ex, my, ey, am, ae, mm, me, dm, de, rm, re_ = row
        fexp, mode = COMPUTE_GRID_FEXPS[fk], CHOICE_MODES[ck]
        x, y = value(beta, mx, ex), value(beta, my, ey)
        report.check(f"row {index} plus", value(beta, am, ae) == round_rational(beta, fexp, mode, x + y))
        report.check(f"row {index} mult", value(beta, mm, me) == round_rational(beta, fexp, mode, x * y))
        report.check(f"row {index} div", None if y == 0 else
                     value(beta, dm, de) == round_rational(beta, fexp, mode, x / y))
        report.check(f"row {index} sqrt", value(beta, rm, re_) == round_sqrt(beta, fexp, mode, x))
    return report


def decimal_value(mantissa: int, exponent: int) -> Decimal:
    """m * 2^e in the current decimal context (callers set the precision)."""
    return Decimal(mantissa) * Decimal(2) ** exponent


def oracle_cody_waite(rows: Sequence[Row]) -> OracleReport:
    """Cody_Waite.v exp_correct and argument_reduction, at 120 digits.

    Premise: x is a binary64 value (|m| < 2^53, e >= -1074) in [-746, 710].
    The decimal context's rounding error is below 10^-100 relative, far
    below the 2^-51 and 2^-71 scales of the bounds being checked.
    """
    report = OracleReport()
    with localcontext() as context:
        context.prec, context.Emax, context.Emin = 120, 10**6, -10**6
        ln2 = Decimal(2).ln()
        for index, row in enumerate(rows):
            mx, ex, km, ke, tm, te, _pm, _pe, _qm, _qe, _rm, _re, floor_k, ym, ye = row
            x = value(2, mx, ex)
            premise = abs(mx) < 2**53 and ex >= -1074 and -746 <= x <= 710
            k = value(2, km, ke)
            # k = nearbyint(...) is an integer, so Zfloor k = k (no premise needed).
            report.check(f"row {index} Zfloor k", k.denominator == 1 and k == floor_k)
            if not premise:
                report.check(f"row {index} exp_correct", None)
                report.check(f"row {index} argument_reduction", None)
                continue
            exact = decimal_value(mx, ex).exp()
            report.check(f"row {index} exp_correct",
                         abs(decimal_value(ym, ye) - exact) <= exact * Decimal(2) ** -51)
            reduced = decimal_value(mx, ex) - decimal_value(km, ke) * ln2
            report.check(f"row {index} argument_reduction",
                         abs(value(2, tm, te)) <= Fraction(355, 1024) and
                         abs(decimal_value(tm, te) - reduced) <= 65537 * Decimal(2) ** -71)
    return report


def oracle_division_u16(rows: Sequence[Row]) -> OracleReport:
    """Division_u16.v div_u16_spec, with frcpa_spec checked on the observed y0."""
    report = OracleReport()
    frcpa_format = flt(-65597, 11)
    for index, row in enumerate(rows):
        a, b, model, y0m, y0e, *_intermediate, quotient = row
        y0 = value(2, y0m, y0e)
        frcpa_spec = (1 <= b <= 65536 and in_generic_format(2, frcpa_format, y0) and
                      abs(y0 - Fraction(1, b)) <= Fraction(4433, 2**21) / b)
        ok = quotient == a // b
        if 1 <= a <= 65535 and 1 <= b <= 65535 and frcpa_spec:
            report.check(f"row {index} model {model}: div_u16 {a} {b}", ok)
        else:
            report.check(f"row {index}", None)
            report.control_breaks += not ok
    return report


TIE_PREDICATES: dict[int, Callable[[int], bool]] = {
    0: lambda floor: floor % 2 != 0,   # negb (Z.even m): ties to even
    1: lambda floor: floor >= 0,       # Zle_bool 0: ties away from zero
    2: lambda floor: True,
    3: lambda floor: False,
}


def oracle_sqrt_sqr(rows: Sequence[Row]) -> OracleReport:
    """Sqrt_sqr.v sqrt_sqr_special_case (radix 5, precision 3), step by step."""
    report = OracleReport()
    fexp = flx(3)
    for index, (k1, k2, mx, ym, ye, zm, ze, difference) in enumerate(rows):
        x, y = Fraction(mx), value(5, ym, ye)
        premise = 0 <= mx < 125
        report.check(f"row {index} y", y == round_rational(5, fexp, ("N", TIE_PREDICATES[k2]), x * x))
        report.check(f"row {index} z", value(5, zm, ze) ==
                     round_sqrt(5, fexp, ("N", TIE_PREDICATES[k1]), y))
        report.check(f"row {index} sqrt_sqr", difference == 0 if premise else None)
    return report


# family -> (outer fexp1, inner fexp2). The fixed parameters satisfy each
# family's premise: FLX prec 2 <= 3; FLT also emin' -6 <= -4; FTZ
# emin' + prec' = -2 <= emin + prec = -2.
DOUBLE_ROUNDING_FORMATS = {0: (flx(2), flx(3)), 1: (flt(-4, 2), flt(-6, 3)),
                           2: (ftz(-4, 2), ftz(-5, 3))}


def oracle_double_rounding(rows: Sequence[Row]) -> OracleReport:
    """Double_rounding_odd_radix.v round_round_eq for mult/plus/minus/sqrt/div.

    Every row's three roundings are re-derived exactly. The identity itself
    is judged only in odd radix, for inputs in the outer format, and (for
    div) nonzero y with ZnearestA on both roundings; radix-2 rows are
    positive controls.
    """
    report = OracleReport()
    for index, row in enumerate(rows):
        beta, family, op, k1, k2, mx, ex, my, ey, im, ie, om, oe, dm, de, difference = row
        fexp1, fexp2 = DOUBLE_ROUNDING_FORMATS[family]
        choice1, choice2 = ("N", TIE_PREDICATES[k1]), ("N", TIE_PREDICATES[k2])
        x, y = value(beta, mx, ex), value(beta, my, ey)

        def exact_round(fexp, mode):
            if op == 3:
                return round_sqrt(beta, fexp, mode, x)
            if op == 4:
                return round_rational(beta, fexp, mode, x / y) if y else None
            return round_rational(beta, fexp, mode, {0: x * y, 1: x + y, 2: x - y}[op])

        inner, outer, direct = value(beta, im, ie), value(beta, om, oe), value(beta, dm, de)
        for label, observed, expected in (("inner", inner, exact_round(fexp2, choice2)),
                                          ("direct", direct, exact_round(fexp1, choice1))):
            report.check(f"row {index} {label}", None if expected is None else observed == expected)
        report.check(f"row {index} outer", outer == round_rational(beta, fexp1, choice1, inner))
        premise = (beta % 2 == 1 and in_generic_format(beta, fexp1, x) and
                   (op == 3 or in_generic_format(beta, fexp1, y)) and
                   (op != 4 or (y != 0 and k1 == k2 == 1)))
        ok = difference == 0
        if premise:
            report.check(f"row {index} round_round_eq", ok)
        else:
            report.check(f"row {index} round_round_eq", None)
            report.control_breaks += not ok
    return report


def ulp_flt(emin: int, prec: int, x: Fraction) -> Fraction:
    """Flocq ulp for FLT_exp emin prec in radix 2; ulp 0 = 2^emin."""
    if x == 0:
        return Fraction(2) ** emin
    return Fraction(2) ** flt(emin, prec)(mag_rational(2, x))


def oracle_average(rows: Sequence[Row]) -> OracleReport:
    """Average.v: the correctness lemmas of the three averages and `average`."""
    report = OracleReport()
    table = {(row[0], row[1], value(2, row[2], row[3]), value(2, row[4], row[5])):
             value(2, row[12], row[13]) for row in rows}
    for index, row in enumerate(rows):
        emin, prec, mx, ex, my, ey, nm, ne, sm, se, hm, he, am, ae = row
        fexp = flt(emin, prec)
        x, y = value(2, mx, ex), value(2, my, ey)
        naive, sum_half, half_sub, average = (value(2, nm, ne), value(2, sm, se),
                                              value(2, hm, he), value(2, am, ae))
        a = (x + y) / 2
        rounded = round_rational(2, fexp, "NE", a)
        three_halves_ulp = Fraction(3, 2) * ulp_flt(emin, prec, a)
        label = f"row {index} ({x}, {y})"
        if not (in_generic_format(2, fexp, x) and in_generic_format(2, fexp, y)):
            report.check(label, None)
            continue
        report.check(f"{label} avg_naive_correct", naive == rounded)
        if abs(x) >= Fraction(2) ** (emin + 2 * prec + 1):
            report.check(f"{label} avg_sum_half_correct", sum_half == rounded)
        else:
            report.check(f"{label} avg_sum_half_correct", None)
            report.control_breaks += sum_half != rounded
        same_sign = (x >= 0 and y >= 0) or (x <= 0 and y <= 0)
        report.check(f"{label} avg_half_sub_correct",
                     abs(half_sub - a) <= three_halves_ulp if same_sign else None)
        report.check(f"{label} average_correct", abs(average - a) <= three_halves_ulp)
        report.check(f"{label} average_between", min(x, y) <= average <= max(x, y))
        report.check(f"{label} average_zero", average == 0 if a == 0 else None)
        report.check(f"{label} average_no_underflow",
                     average != 0 if abs(a) >= Fraction(2) ** emin else None)
        report.check(f"{label} average_same_sign",
                     (a < 0 or average >= 0) and (a > 0 or average <= 0))
        report.check(f"{label} average_symmetry", table.get((emin, prec, y, x)) == average)
        report.check(f"{label} average_symmetry_Ropp", table.get((emin, prec, -x, -y)) == -average)
    return report


# ---------------------------------------------------------------------------
# Exemplar registry
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class Exemplar:
    name: str
    rows: int
    width: int
    oracle: Callable[[Sequence[Row]], OracleReport]
    # True when the fixture deliberately includes premise-violating rows
    # that must break the checked identity at least once.
    needs_control_break: bool = False
    timeout: int = 600


EXEMPLARS: dict[str, Exemplar] = {e.name: e for e in (
    Exemplar("ComputeGrid", rows=960, width=15, oracle=oracle_compute_grid),
    Exemplar("CodyWaite", rows=30, width=15, oracle=oracle_cody_waite),
    Exemplar("DivisionU16", rows=152, width=12, oracle=oracle_division_u16,
             needs_control_break=True),
    Exemplar("Average", rows=578, width=14, oracle=oracle_average, needs_control_break=True),
    Exemplar("SqrtSqr", rows=2000, width=8, oracle=oracle_sqrt_sqr),
    Exemplar("DoubleRoundingOddRadix", rows=2448, width=16, oracle=oracle_double_rounding,
             needs_control_break=True),
)}


# ---------------------------------------------------------------------------
# Execution
# ---------------------------------------------------------------------------

def check_upstream_verbatim(flocq: Path) -> None:
    """Fail closed if a verbatim fixture drifted from the pinned upstream file."""
    for fixture, upstream in UPSTREAM_VERBATIM.items():
        if (FIXTURES / fixture).read_bytes() != (flocq / upstream).read_bytes():
            raise ValueError(f"{fixture} differs from pinned upstream {upstream}")


def fixture_digests() -> dict[str, str]:
    return {path.name: hashlib.sha256(path.read_bytes()).hexdigest()
            for path in sorted(FIXTURES.iterdir()) if path.suffix in {".v", ".lean"}}


class Workspace:
    """Temporary copies of the fixtures plus compiled shared modules.

    Nothing is written inside the reference checkout or the fixture directory.
    """

    def __init__(self, flocq: Path, directory: Path, coqc: str | None = None):
        self.flocq = flocq.resolve()
        self.coqc = coqc or bridge.configured_coqc(self.flocq)
        self.rocq = directory / "rocq"
        self.lean = directory / "lean"
        self.olean = directory / "olean" / "Exemplars"
        for folder in (self.rocq, self.lean / "Exemplars", self.olean):
            folder.mkdir(parents=True, exist_ok=True)
        for path in FIXTURES.iterdir():
            if path.suffix == ".v":
                shutil.copy2(path, self.rocq / path.name)
            elif path.suffix == ".lean":
                target = self.lean / ("Exemplars" if path.stem in SHARED else "") / path.name
                shutil.copy2(path, target)

    def rocq_command(self, name: str, *flags: str) -> list[str]:
        return [self.coqc, "-q", *flags, "-R", str(self.flocq / "src"), "Flocq",
                "-R", str(self.rocq), "Exemplars", str(self.rocq / f"{name}.v")]

    def lean_command(self, *arguments: str) -> list[str]:
        # Lake supplies LEAN_PATH; the compiled shared modules are appended.
        return ["lake", "env", "sh", "-c", 'LEAN_PATH="$LEAN_PATH:$0" exec lean "$@"',
                str(self.olean.parent), *arguments]

    def build_shared(self) -> None:
        for name in SHARED:
            flags = VERBATIM_ROCQ_FLAGS if f"{name}.v" in UPSTREAM_VERBATIM else ()
            output = bridge.run(self.rocq_command(name, *flags), timeout=600)
            if output.strip():
                raise RuntimeError(f"unexpected Rocq output for shared {name}: {output[:2000]}")
            output = bridge.run(self.lean_command(
                "-R", str(self.lean), "-o", str(self.olean / f"{name}.olean"),
                str(self.lean / "Exemplars" / f"{name}.lean")), timeout=600)
            if output.strip():
                raise RuntimeError(f"unexpected Lean output for shared {name}: {output[:2000]}")

    def observe(self, exemplar: Exemplar) -> dict[str, list[Row]]:
        """Run both sides (at most two provers at once) and parse strictly."""
        commands = {"rocq": self.rocq_command(exemplar.name),
                    "lean": self.lean_command(str(self.lean / f"{exemplar.name}.lean"))}

        def one(side: str) -> list[Row]:
            output = bridge.run(commands[side], timeout=exemplar.timeout)
            rows = bridge.parse_result(output, side, exemplar.rows)
            if any(len(row) != exemplar.width for row in rows):
                raise ValueError(f"{side}: rows must have exactly {exemplar.width} columns")
            return rows

        with ThreadPoolExecutor(max_workers=2) as pool:
            futures = {side: pool.submit(one, side) for side in commands}
            return {side: future.result() for side, future in futures.items()}


def differing_rows(left: Sequence[Row], right: Sequence[Row]) -> list[int]:
    if len(left) != len(right):
        raise ValueError("row counts differ")
    return [index for index, (a, b) in enumerate(zip(left, right, strict=True)) if a != b]


def judge(exemplar: Exemplar, observations: dict[str, list[Row]]) -> dict:
    """Closed verdict set: match or mismatch, plus an oracle verdict per side."""
    differences = differing_rows(observations["rocq"], observations["lean"])
    result: dict = {"exemplar": exemplar.name, "rows": exemplar.rows,
                    "verdict": "mismatch" if differences else "match",
                    "differing_rows": differences[:20]}
    for side, rows in observations.items():
        report = exemplar.oracle(rows)
        ok = not report.violations and report.holds > 0 and (
            report.control_breaks > 0 or not exemplar.needs_control_break)
        result[f"oracle_{side}"] = {"verdict": "holds" if ok else "violated", **asdict(report),
                                    "violations": report.violations[:20]}
    return result


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--flocq-dir", type=Path, required=True)
    parser.add_argument("--coqc", help="override the compiler recorded by the reference build")
    parser.add_argument("--only", action="append", choices=sorted(EXEMPLARS))
    parser.add_argument("--output", type=Path, help="keep the workspace and a JSON report here")
    args = parser.parse_args()
    flocq = args.flocq_dir.resolve()
    check_upstream_verbatim(flocq)
    names = args.only or list(EXEMPLARS)
    started = time.monotonic()
    report: dict = {"flocq": str(flocq), "fixtures_sha256": fixture_digests(),
                    "lean_source_sha256": bridge.lean_source_fingerprint(), "results": []}
    with tempfile.TemporaryDirectory(prefix="floatspec-exemplars-") as scratch:
        folder = args.output or Path(scratch)
        if args.output:
            if folder.exists() and any(folder.iterdir()):
                parser.error("output directory must be empty; do not overwrite evidence")
            folder.mkdir(parents=True, exist_ok=True)
        workspace = Workspace(flocq, folder, args.coqc)
        workspace.build_shared()
        for name in names:
            exemplar = EXEMPLARS[name]
            observations = workspace.observe(exemplar)
            result = judge(exemplar, observations)
            report["results"].append(result)
            if args.output:
                (folder / f"{name}.observations.json").write_text(json.dumps(observations) + "\n")
            print(f"{name}: {result['verdict']}, oracle rocq={result['oracle_rocq']['verdict']} "
                  f"lean={result['oracle_lean']['verdict']} "
                  f"(holds={result['oracle_rocq']['holds']}, "
                  f"premise_false={result['oracle_rocq']['premise_false']}, "
                  f"control_breaks={result['oracle_rocq']['control_breaks']})", flush=True)
        bridge.require_lean_source_snapshot(report["lean_source_sha256"])
        report["elapsed_seconds"] = round(time.monotonic() - started, 3)
        if args.output:
            (folder / "report.json").write_text(json.dumps(report, indent=2) + "\n")
    failed = [r["exemplar"] for r in report["results"]
              if r["verdict"] != "match" or r["oracle_rocq"]["verdict"] != "holds"
              or r["oracle_lean"]["verdict"] != "holds"]
    if failed:
        raise SystemExit(f"exemplar failures: {', '.join(failed)}")


if __name__ == "__main__":
    main()
