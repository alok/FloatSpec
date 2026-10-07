"""Execute the Digits.v functions against pinned Rocq and an exact oracle."""
from contextlib import contextmanager
from dataclasses import asdict, dataclass
import hashlib
import random

import flocq_bridge as bridge

# digit, scale: (radix, n, k); slice: (radix, n, k1, k2); sum_digit: (radix, n, count);
# digits: (radix, n); binary_length: (p) for a positive p.
ARITIES = {"digit": 3, "scale": 3, "slice": 4, "sum_digit": 3, "digits": 2,
           "binary_length": 1}
WIDTHS = {op: 1 for op in ARITIES}
RADICES = (2, 3, 10, 16)


@dataclass(frozen=True)
class Case:
    op: str
    args: tuple[int, ...]

    def __post_init__(self):
        if (self.op not in ARITIES or len(self.args) != ARITIES[self.op] or
                any(type(value) is not int for value in self.args)):
            raise ValueError("digits protocol requires a known operation and integer arguments")
        if self.op == "binary_length":
            if self.args[0] <= 0:
                raise ValueError("binary length takes a positive")
        elif self.args[0] < 2:
            raise ValueError("a radix is at least 2, never silently coerced")
        if self.op == "sum_digit" and not 0 <= self.args[2] <= 200:
            raise ValueError("the digit count is a small natural")


def positive(value):
    if value == 1:
        return "Zaux.Positive.xH"
    return f"(Zaux.Positive.{'xI' if value % 2 else 'xO'} {positive(value // 2)})"


def expressions(case):
    if case.op == "binary_length":
        (p,) = case.args
        return (f"[(Digits.digits2_Pnat {positive(p)} : Int)]",
                f"[Z.of_nat (digits2_Pnat ({p})%positive)]")
    b, *rest = case.args
    radix = f"(Build_radix {b} eq_refl)"
    lean_args = " ".join(f"({x})" for x in rest)
    if case.op == "sum_digit":
        n, count = rest
        return (f"[Digits.Zsum_digit {b} (Digits.Zdigit {b} ({n})) {count}]",
                f"[Zsum_digit {radix} (Zdigit {radix} ({n})) {count}]")
    name = {"digit": "Zdigit", "scale": "Zscale", "slice": "Zslice", "digits": "Zdigits"}[case.op]
    return f"[Digits.{name} {b} {lean_args}]", f"[{name} {radix} {lean_args}]"


def corpus(seed, samples):
    small = range(-12, 13)
    edges = (-2**64 - 1, -2**63, -1000, -1, 0, 1, 999, 1000, 2**63 - 1, 2**64)
    cases = []
    for b in RADICES:
        cases += [Case("digit", (b, n, k)) for n in (*small, *edges) for k in (-2, -1, 0, 1, 2, 3, 70)]
        cases += [Case("scale", (b, n, k)) for n in (*small, *edges) for k in (-70, -3, -1, 0, 1, 3)]
        cases += [Case("slice", (b, n, k1, k2)) for n in (-1000, -12, -1, 0, 7, 999, 2**63 - 1)
                  for k1 in (-2, 0, 1, 3) for k2 in (-1, 0, 1, 2, 5)]
        cases += [Case("sum_digit", (b, n, c)) for n in (-1000, -12, -1, 0, 7, 999, 2**64)
                  for c in (0, 1, 2, 3, 8, 70)]
        # Exact powers and their neighbours sit on the digit-count boundaries.
        powers = [b**e + d for e in (1, 2, 5, 31, 32, 63, 64) for d in (-1, 0, 1)]
        cases += [Case("digits", (b, s * n)) for n in (*range(13), *powers) for s in (1, -1)]
    cases += [Case("binary_length", (p,)) for p in
              (*range(1, 18), *(2**e + d for e in (31, 32, 52, 53, 63, 64, 100) for d in (-1, 0, 1)))]
    rng = random.Random(seed)
    for _ in range(samples):
        b = rng.choice(RADICES)
        n = rng.randint(-2**127, 2**127)
        cases.append(Case("digit", (b, n, rng.randint(-3, 130))))
        cases.append(Case("scale", (b, n, rng.randint(-130, 130))))
        cases.append(Case("slice", (b, n, rng.randint(-10, 130), rng.randint(-3, 40))))
        cases.append(Case("sum_digit", (b, n, rng.randint(0, 130))))
        cases.append(Case("digits", (b, n)))
        cases.append(Case("binary_length", (rng.randint(1, 2**127),)))
    return sorted(dict.fromkeys(cases), key=lambda c: tuple(ARITIES).index(c.op))


def quot(a, b):
    """Rocq's Z.quot: truncation toward zero, and 0 for a zero divisor."""
    if b == 0:
        return 0
    q = abs(a) // abs(b)
    return q if (a < 0) == (b < 0) else -q


def rem(a, b):
    """Rocq's Z.rem: the dividend's sign, and the dividend for a zero divisor."""
    return a - b * quot(a, b)


def zpower(b, e):
    return b**e if e >= 0 else 0


def expected(case):
    if case.op == "binary_length":
        return [case.args[0].bit_length() - 1]
    b, n, *rest = case.args
    if case.op == "digit":
        (k,) = rest
        return [rem(quot(n, zpower(b, k)), b)]
    if case.op == "scale":
        (k,) = rest
        return [n * b**k if k >= 0 else quot(n, b**-k)]
    if case.op == "slice":
        k1, k2 = rest
        scaled = n * b**-k1 if k1 <= 0 else quot(n, b**k1)
        return [rem(scaled, b**k2) if k2 >= 0 else 0]
    if case.op == "sum_digit":
        # Zsum_digit_digit: the first `count` digits reassemble the truncated remainder.
        (count,) = rest
        return [rem(n, b**count)]
    # Count base-b digits of |n| by repeated division, independently of powers.
    m, count = abs(n), 0
    while m:
        m //= b
        count += 1
    return [count]


LEAN_HEADER = """import FloatSpec.src.Core.Digits
open FloatSpec.Core
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option pp.maxSteps 200000
set_option pp.deepTerms true
namespace Bridge
"""
COQ_HEADER = """From Stdlib Require Import ZArith List.
From Flocq Require Import Core.Zaux Core.Digits.
Import ListNotations.
Open Scope Z_scope.
"""


@contextmanager
def profile():
    metadata = {"name": "Digits functions", "oracle_checked_cases": 0,
                "oracle_assertions": 0,
                "protocol_sha256": hashlib.sha256((LEAN_HEADER + COQ_HEADER).encode()).hexdigest()}
    original = bridge.compare
    def compare(cases, observations):
        mismatches = original(cases, observations)
        if not mismatches:
            for case, row in zip(cases, observations['compiled'], strict=True):
                if row != expected(case) or any(type(value) is not int for value in row):
                    metadata['oracle_failure_case'] = asdict(case)
                    raise AssertionError(f"digits independent oracle: {asdict(case)}: {row}")
                metadata['oracle_checked_cases'] += 1
                metadata['oracle_assertions'] += 1
        return mismatches
    overrides = {'OPS': tuple(ARITIES), 'ARITIES': ARITIES,
                 'WIDTHS': WIDTHS, 'RADIX_OPS': set(),
                 'BATCH_LIMITS': {op: 100 for op in ARITIES}, 'Case': Case,
                 'LEAN_HEADER': LEAN_HEADER, 'COQ_HEADER': COQ_HEADER,
                 'expressions': expressions, 'corpus': corpus, 'compare': compare}
    previous = {name: getattr(bridge, name) for name in overrides}
    try:
        for name, value in overrides.items():
            setattr(bridge, name, value)
        yield metadata
    finally:
        for name, value in previous.items():
            setattr(bridge, name, value)


if __name__ == '__main__':
    with profile() as metadata:
        bridge.main(lean_build_targets=('FloatSpec.src.Core.Digits',), profile_metadata=metadata)
