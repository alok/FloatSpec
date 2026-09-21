"""Execute the source-ordered Zaux aliases against pinned Rocq and an exact oracle."""
from contextlib import contextmanager
from dataclasses import asdict, dataclass
import hashlib
import random

import flocq_bridge as bridge

ARITIES = {"conditional_negation": 2, "positive_iteration": 4}


@dataclass(frozen=True)
class Case:
    op: str
    args: tuple[int, ...]

    def __post_init__(self):
        if (self.op not in ARITIES or len(self.args) != ARITIES[self.op] or
                any(type(value) is not int for value in self.args)):
            raise ValueError("prelude protocol requires a known operation and integer arguments")
        if self.op == "conditional_negation" and self.args[0] not in (0, 1):
            raise ValueError("sign must be zero or one")
        if self.op == "positive_iteration" and self.args[0] <= 0:
            raise ValueError("iteration count must be positive, never silently coerced from zero")


def positive(value):
    if value == 1:
        return "Positive.xH"
    return f"(Positive.{'xI' if value % 2 else 'xO'} {positive(value // 2)})"


def expressions(case):
    if case.op == "conditional_negation":
        sign, value = case.args
        return (f"[cond_Zopp {'true' if sign else 'false'} ({value})]",
                f"[cond_Zopp {'true' if sign else 'false'} ({value})]")
    count, scale, offset, initial = case.args
    return (f"[iter_pos (fun x : Int => ({scale}) * x + ({offset})) {positive(count)} ({initial})]",
            f"[iter_pos (fun x : Z => ({scale}) * x + ({offset})) ({count})%positive ({initial})]")


def corpus(seed, samples):
    cases = [Case("conditional_negation", (s, x))
             for s in (0, 1) for x in (-2**63, -7, -1, 0, 1, 7, 2**63)]
    counts = (*range(1, 10), 15, 16, 17, 31, 32, 33, 63, 64, 65, 127, 128, 129, 257)
    cases += [Case("positive_iteration", (n, a, b, x)) for n in counts
              for a in (-2, -1, 0, 1, 2) for b in (-3, 0, 3) for x in (-5, 0, 7)]
    rng = random.Random(seed)
    for _ in range(samples):
        cases.append(Case("conditional_negation", (rng.randrange(2), rng.randint(-2**127, 2**127))))
        cases.append(Case("positive_iteration", (rng.randint(1, 300), rng.randint(-3, 3),
                                                  rng.randint(-10, 10), rng.randint(-100, 100))))
    return sorted(dict.fromkeys(cases), key=lambda c: tuple(ARITIES).index(c.op))


def expected(case):
    if case.op == "conditional_negation":
        sign, value = case.args
        return [-value if sign else value]
    count, scale, offset, initial = case.args
    # Closed geometric sum, independent of the binary-recursive implementation.
    power = scale ** count
    return [initial + count * offset if scale == 1 else
            power * initial + offset * ((power - 1) // (scale - 1))]


LEAN_HEADER = """import FloatSpec.src.Core.Zaux
open FloatSpec.Core.Zaux
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option pp.maxSteps 200000
set_option pp.deepTerms true
namespace Bridge
"""
COQ_HEADER = """From Stdlib Require Import ZArith List.
From Flocq Require Import Core.Zaux.
Import ListNotations.
Open Scope Z_scope.
"""


@contextmanager
def profile():
    metadata = {"name": "Zaux prelude aliases", "oracle_checked_cases": 0,
                "oracle_assertions": 0,
                "protocol_sha256": hashlib.sha256((LEAN_HEADER + COQ_HEADER).encode()).hexdigest()}
    original = bridge.compare
    def compare(cases, observations):
        mismatches = original(cases, observations)
        if not mismatches:
            for case, row in zip(cases, observations['compiled'], strict=True):
                if row != expected(case) or any(type(value) is not int for value in row):
                    metadata['oracle_failure_case'] = asdict(case)
                    raise AssertionError(f"prelude independent oracle: {asdict(case)}: {row}")
                metadata['oracle_checked_cases'] += 1
                metadata['oracle_assertions'] += 1
        return mismatches
    overrides = {'OPS': tuple(ARITIES), 'ARITIES': ARITIES,
                 'WIDTHS': {op: 1 for op in ARITIES}, 'RADIX_OPS': set(),
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
        bridge.main(lean_build_targets=('FloatSpec.src.Core.Zaux',), profile_metadata=metadata)
