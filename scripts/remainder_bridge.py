"""Three-path finite remainder-format profile, with an independent rational oracle.

The quotient is test-input arithmetic, not a claimed executable replacement of
the real-valued Ztrunc/Znearest APIs. The source implementation under test is
binary_round at precision3/emax4. Every constructor field is observed.
"""
from contextlib import contextmanager
from dataclasses import asdict, dataclass
from fractions import Fraction
import hashlib
import random

import flocq_bridge as bridge


OPERATION = "remainder_format"
COLUMNS = ("quotient", "remainder_units", "kind", "sign", "mantissa", "exponent")
POSITIVE = (1, 2, 3) + tuple(m * 2 ** shift for shift in range(6) for m in (4, 5, 6, 7))
VALUES = tuple(-v for v in POSITIVE) + (0,) + POSITIVE
RECORDS = {0: [0, 0, 0, 0]}
for sign in (0, 1):
    for mantissa, exponent in [(m, -4) for m in (1, 2, 3)] + [
            (m, shift - 4) for shift in range(6) for m in (4, 5, 6, 7)]:
        RECORDS[(-1 if sign else 1) * mantissa * 2 ** (exponent + 4)] = [
            3, sign, mantissa, exponent]


@dataclass(frozen=True)
class Case:
    op: str
    args: tuple[int, ...]

    def __post_init__(self):
        if (self.op != OPERATION or len(self.args) != 3 or
                any(type(value) is not int for value in self.args) or
                self.args[0] not in range(4) or any(v not in VALUES for v in self.args[1:])):
            raise ValueError("remainder cases require mode0..3 and two enumerated finite units")


def corpus(seed, samples):
    if samples != 0:
        raise ValueError("this exhaustive profile uses --samples 0; there are no random duplicates")
    cases = [Case(OPERATION, (mode, x, y)) for mode in range(4) for x in VALUES for y in VALUES]
    random.Random(seed).shuffle(cases)
    return cases


def expressions(case):
    mode, x, y = case.args
    return (f"remainderObserve {mode} ({x}) ({y})",
            f"remainderObserve {mode}%nat ({x})%Z ({y})%Z")


def expected(case):
    mode, x, y = case.args
    ratio = Fraction(x, y) if y else Fraction(0)
    lower = ratio.numerator // ratio.denominator
    fraction = ratio - lower
    q = (int(ratio), lower + int(fraction > Fraction(1, 2)),
         lower + int(fraction >= Fraction(1, 2)), -((-ratio.numerator) // ratio.denominator))[mode]
    remainder = x - q * y
    nearest = min(VALUES, key=lambda value: (abs(value - remainder), RECORDS[value][2] % 2))
    premise = abs(ratio) >= Fraction(1, 2) or q == 0
    return [q, remainder, *RECORDS[nearest]], premise, nearest == remainder


def independent_checks(case, row):
    if len(row) != len(COLUMNS) or any(type(v) is not int for v in row):
        raise ValueError("remainder oracle expects six integer fields")
    want, premise, exact = expected(case)
    for column, actual, target in zip(COLUMNS, row, want, strict=True):
        if actual != target:
            raise AssertionError(f"remainder oracle {column}: {asdict(case)}: {actual} != {target}")
    if premise and not exact:
        raise AssertionError(f"remainder source premise did not preserve format: {asdict(case)}")
    return premise, (not premise and not exact)


def prefix(fixture, marker):
    source = (bridge.ROOT / "scripts/fixtures" / fixture).read_text()
    if source.count(marker) != 1:
        raise ValueError("fixture protocol boundary must be unique")
    return source.split(marker)[0]


LEAN_HEADER = prefix("RemainderGrid.lean", "private def roundedUnits").replace(
    "namespace RemainderGrid", "namespace Bridge") + """
set_option pp.maxSteps 200000
set_option pp.deepTerms true
def standard : StandardFloat → List Int
  | .S754_zero s => [0, if s then 1 else 0, 0, 0]
  | .S754_infinity s => [1, if s then 1 else 0, 0, 0]
  | .S754_nan => [2, 0, 0, 0]
  | .S754_finite s m e => [3, if s then 1 else 0, m, e]
def remainderObserve (mode : Nat) (x y : Int) : List Int :=
  let q := quotient mode x y
  let value := x - q * y
  let result := if value = 0 then StandardFloat.S754_zero false
    else binary_round (prec := 3) (emax := 4) .RNE (value < 0) value.natAbs (-4)
  [q, value] ++ standard result
"""
COQ_HEADER = prefix("RemainderGrid.v", "Definition roundedUnits") + """
Definition standard (x : SpecFloat.spec_float) : list Z :=
  match x with
  | SpecFloat.S754_zero s => [0; if s then 1 else 0; 0; 0]
  | SpecFloat.S754_infinity s => [1; if s then 1 else 0; 0; 0]
  | SpecFloat.S754_nan => [2; 0; 0; 0]
  | SpecFloat.S754_finite s m e => [3; if s then 1 else 0; Zpos m; e]
  end.
Definition remainderObserve (mode : nat) (x y : Z) : list Z :=
  let q := quotient mode x y in
  let value := x - q * y in
  let result := if Z.eqb value 0 then SpecFloat.S754_zero false else
    binary_round 3 4 mode_NE (Z.ltb value 0) (Z.to_pos (Z.abs value)) (-4) in
  [q; value] ++ standard result.
"""


@contextmanager
def profile():
    metadata = {"name": "Finite remainder-format law; quotient model plus source binary_round",
                "columns": COLUMNS, "precision": 3, "emax": 4, "unit_exponent": -4,
                "protocol_sha256": hashlib.sha256((LEAN_HEADER + COQ_HEADER).encode()).hexdigest(),
                "oracle_checked_cases": 0, "oracle_assertions": 0,
                "qualified_cases": 0, "outside_cases": 0, "inexact_outside_cases": 0,
                "zero_denominator_cases": 0}
    original_compare = bridge.compare
    def compare(cases, observations):
        mismatches = original_compare(cases, observations)
        if not mismatches:
            for case, row in zip(cases, observations["compiled"], strict=True):
                try:
                    premise, bad = independent_checks(case, row)
                except Exception:
                    metadata["oracle_failure_case"] = asdict(case)
                    raise
                metadata["oracle_checked_cases"] += 1
                metadata["oracle_assertions"] += len(COLUMNS) + int(premise)
                metadata["qualified_cases"] += int(premise)
                metadata["outside_cases"] += int(not premise)
                metadata["inexact_outside_cases"] += int(bad)
                metadata["zero_denominator_cases"] += int(case.args[2] == 0)
        return mismatches
    overrides = {"OPS": (OPERATION,), "ARITIES": {OPERATION: 3},
                 "WIDTHS": {OPERATION: len(COLUMNS)}, "RADIX_OPS": set(),
                 "BATCH_LIMITS": {OPERATION: 200}, "Case": Case,
                 "LEAN_HEADER": LEAN_HEADER, "COQ_HEADER": COQ_HEADER,
                 "expressions": expressions, "corpus": corpus, "compare": compare}
    previous = {name: getattr(bridge, name) for name in overrides}
    try:
        for name, replacement in overrides.items():
            setattr(bridge, name, replacement)
        yield metadata
    finally:
        for name, original in previous.items():
            setattr(bridge, name, original)


def main():
    with profile() as metadata:
        bridge.main(lean_build_targets=("FloatSpec.src.IEEE754.Bits",), profile_metadata=metadata)


if __name__ == "__main__":
    main()
