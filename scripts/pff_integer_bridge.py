"""Execute actual Pff positive/optional/signed integer exports in three paths.

The signed quotient is truncating, including total zero-divisor output zero.
Positive inputs must be positive before transport; reject invalid inputs rather
than letting Z.to_pos or Lean's predecessor representation silently change them.
"""
from contextlib import contextmanager
from dataclasses import asdict, dataclass
from fractions import Fraction
import hashlib
import random

import flocq_bridge as bridge

ARITIES = {"pff_quotient": 2, "pff_pdiv": 2, "pff_option": 1,
           "pff_divides": 2, "pff_maxdiv": 3}
COLUMNS = {"pff_quotient": ("quotient",),
           "pff_pdiv": tuple(f"{part}.{field}" for part in ("quotient", "remainder")
                             for field in ("tag", "payload", "oZ", "oZ1")),
           "pff_option": ("tag", "payload", "oZ", "oZ1"),
           "pff_divides": ("divides",), "pff_maxdiv": ("maxDiv",)}


@dataclass(frozen=True)
class Case:
    op: str
    args: tuple[int, ...]

    def __post_init__(self):
        if (self.op not in ARITIES or len(self.args) != ARITIES[self.op] or
                any(type(value) is not int for value in self.args)):
            raise ValueError("Pff integer protocol requires a known operation and integer arguments")
        if self.op == "pff_pdiv" and any(value <= 0 for value in self.args):
            raise ValueError("Pdiv requires positive inputs; zero is not transported as one")
        if self.op == "pff_option" and self.args[0] < 0:
            raise ValueError("option encoding uses zero for None and positive integers for Some")
        if self.op == "pff_maxdiv" and self.args[2] < 0:
            raise ValueError("maxDiv bound must be a natural number")


def corpus(seed, samples):
    signed = (-2**63, -17, -7, -3, -1, 0, 1, 3, 7, 17, 2**63)
    positive = (1, 2, 3, 7, 8, 9, 31, 32, 33, 255, 256, 257)
    cases = [Case("pff_quotient", (x, y)) for x in signed for y in signed]
    cases += [Case("pff_pdiv", (x, y)) for x in positive for y in positive]
    cases += [Case("pff_option", (x,)) for x in (0, 1, 2, 7, 8, 4096)]
    cases += [Case("pff_divides", (x, y)) for x in signed for y in signed]
    cases += [Case("pff_maxdiv", (radix, value, bound))
              for radix in (-3, -2, -1, 0, 1, 2, 3, 10)
              for value in (-81, -8, -1, 0, 1, 8, 81) for bound in (0, 1, 2, 4, 8)]
    rng = random.Random(seed)
    for _ in range(samples):
        bits = rng.choice((8, 64, 127))
        cases.append(Case("pff_quotient", tuple(rng.randint(-2**bits, 2**bits) for _ in range(2))))
        cases.append(Case("pff_pdiv", (rng.randint(1, 4096), rng.randint(1, 4096))))
        cases.append(Case("pff_option", (rng.randint(0, 4096),)))
        cases.append(Case("pff_divides", tuple(rng.randint(-2**bits, 2**bits) for _ in range(2))))
        cases.append(Case("pff_maxdiv", (rng.choice((-10, -3, -2, -1, 0, 1, 2, 3, 10)),
                                         rng.randint(-2**bits, 2**bits), rng.randint(0, 32))))
    # The runner caps homogeneous expensive families. Group random operations
    # too, avoiding one prover invocation per alternating random input.
    return sorted(cases, key=lambda case: tuple(ARITIES).index(case.op))


def expressions(case):
    name = {"pff_quotient": "quotientObserve", "pff_pdiv": "positiveDivisionObserve",
            "pff_option": "optionObserve", "pff_divides": "dividesObserve",
            "pff_maxdiv": "maxDivObserve"}[case.op]
    return (name + " " + " ".join(f"({value})" for value in case.args),
            name + " " + " ".join(f"({value}%Z)" for value in case.args))


def expected(case):
    def optional(value):
        return [int(value != 0), value, value, value]
    def divides(value, divisor):
        return value % divisor == 0 if divisor else value == 0
    if case.op == "pff_maxdiv":
        radix, value, bound = case.args
        return [max(exponent for exponent in range(bound + 1)
                    if divides(value, radix**exponent))]
    if case.op == "pff_divides":
        return [int(divides(*case.args))]
    if case.op == "pff_option":
        return optional(case.args[0])
    numerator, denominator = case.args
    if case.op == "pff_quotient":
        return [int(Fraction(numerator, denominator)) if denominator else 0]
    quotient, remainder = divmod(numerator, denominator)
    return optional(quotient) + optional(remainder)


def independent_checks(case, row):
    target = expected(case)
    if len(row) != len(target) or any(type(value) is not int for value in row):
        raise ValueError("Pff integer observation has invalid shape")
    for field, actual, want in zip(COLUMNS[case.op], row, target, strict=True):
        if actual != want:
            raise AssertionError(f"Pff integer oracle {field}: {asdict(case)}: {actual} != {want}")
    return len(target)


def prefix(language, marker):
    source = (bridge.ROOT / "scripts/fixtures" / f"PffIntegerExecution.{language}").read_text()
    if source.count(marker) != 1:
        raise ValueError("Pff integer fixture boundary must be unique")
    return source.split(marker)[0]


LEAN_HEADER = prefix("lean", "-- Standalone tests follow;")
COQ_HEADER = prefix("v", "(* Standalone tests follow;")


@contextmanager
def profile():
    metadata = {"name": "Actual Pff integer/positive/optional exports",
                "columns": COLUMNS,
                "protocol_sha256": hashlib.sha256((LEAN_HEADER + COQ_HEADER).encode()).hexdigest(),
                "oracle_checked_cases": 0, "oracle_assertions": 0,
                "zero_denominator_cases": 0}
    original_compare = bridge.compare
    def compare(cases, observations):
        mismatches = original_compare(cases, observations)
        if not mismatches:
            for case, row in zip(cases, observations["compiled"], strict=True):
                try:
                    count = independent_checks(case, row)
                except Exception:
                    metadata["oracle_failure_case"] = asdict(case)
                    raise
                metadata["oracle_checked_cases"] += 1
                metadata["oracle_assertions"] += count
                metadata["zero_denominator_cases"] += int(case.op == "pff_quotient" and case.args[1] == 0)
        return mismatches
    overrides = {"OPS": tuple(ARITIES), "ARITIES": ARITIES,
                 "WIDTHS": {op: len(cols) for op, cols in COLUMNS.items()}, "RADIX_OPS": set(),
                 "BATCH_LIMITS": {op: 100 for op in ARITIES}, "Case": Case,
                 "LEAN_HEADER": LEAN_HEADER, "COQ_HEADER": COQ_HEADER,
                 "expressions": expressions, "corpus": corpus, "compare": compare}
    previous = {name: getattr(bridge, name) for name in overrides}
    try:
        for name, value in overrides.items():
            setattr(bridge, name, value)
        yield metadata
    finally:
        for name, value in previous.items():
            setattr(bridge, name, value)


def main():
    with profile() as metadata:
        bridge.main(lean_build_targets=("FloatSpec.src.Pff.Pff",), profile_metadata=metadata)


if __name__ == "__main__":
    main()
