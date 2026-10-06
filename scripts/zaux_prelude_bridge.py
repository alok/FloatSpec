"""Execute the source-ordered Zaux aliases against pinned Rocq and an exact oracle."""
from contextlib import contextmanager
from dataclasses import asdict, dataclass
import hashlib
import random

import flocq_bridge as bridge

ARITIES = {"conditional_negation": 2, "positive_iteration": 4, "comparisons": 2,
           "fast_division": 2, "positive_division": 2}
# Output row lengths; comparisons observe [eq, le, lt] as 0/1 and compare as -1/0/1;
# fast_division is Zfast_div_eucl's pair; positive_division is aux1's pair, then aux's.
WIDTHS = {"conditional_negation": 1, "positive_iteration": 1, "comparisons": 4,
          "fast_division": 2, "positive_division": 4}


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
        if self.op == "positive_division" and min(self.args) <= 0:
            raise ValueError("positive division takes two positives")


def positive(value):
    if value == 1:
        return "Positive.xH"
    return f"(Positive.{'xI' if value % 2 else 'xO'} {positive(value // 2)})"


def expressions(case):
    if case.op == "conditional_negation":
        sign, value = case.args
        return (f"[cond_Zopp {'true' if sign else 'false'} ({value})]",
                f"[cond_Zopp {'true' if sign else 'false'} ({value})]")
    if case.op == "comparisons":
        # Lean's own Zeq_bool/Zle_bool/Zlt_bool and Int `compare`, against the Rocq
        # functions that Flocq's deprecated Stdlib notations expand to. (Rocq 9.1's
        # deprecation hint says Z.eqb for all three; the notations are Z.leb/Z.ltb.)
        x, y = case.args
        def tests(names):
            return [f"if {name} ({x}) ({y}) then 1 else 0" for name in names]
        lean = ", ".join(f"({test} : Int)" for test in tests(("Zeq_bool", "Zle_bool", "Zlt_bool")))
        rocq = "; ".join(tests(("Z.eqb", "Z.leb", "Z.ltb")))
        return (f"[{lean}, match compare ({x} : Int) ({y}) with | .lt => -1 | .eq => 0 | .gt => 1]",
                f"[{rocq}; match Z.compare ({x}) ({y}) with Lt => -1 | Eq => 0 | Gt => 1 end]")
    if case.op == "fast_division":
        a, b = case.args
        call = f"Zfast_div_eucl ({a}) ({b})"
        return f"[({call}).1, ({call}).2]", f"[fst ({call}); snd ({call})]"
    if case.op == "positive_division":
        a, b = case.args
        lean = [f"(Zpos_div_eucl_aux1 {positive(a)} {positive(b)})",
                f"(Zpos_div_eucl_aux {positive(a)} {positive(b)})"]
        rocq = [f"(Zpos_div_eucl_aux1 ({a})%positive ({b})%positive)",
                f"(Zpos_div_eucl_aux ({a})%positive ({b})%positive)"]
        return ("[" + ", ".join(f"{c}.1, {c}.2" for c in lean) + "]",
                "[" + "; ".join(f"fst {c}; snd {c}" for c in rocq) + "]")
    count, scale, offset, initial = case.args
    return (f"[iter_pos (fun x : Int => ({scale}) * x + ({offset})) {positive(count)} ({initial})]",
            f"[iter_pos (fun x : Z => ({scale}) * x + ({offset})) ({count})%positive ({initial})]")


def corpus(seed, samples):
    cases = [Case("conditional_negation", (s, x))
             for s in (0, 1) for x in (-2**63, -7, -1, 0, 1, 7, 2**63)]
    counts = (*range(1, 10), 15, 16, 17, 31, 32, 33, 63, 64, 65, 127, 128, 129, 257)
    cases += [Case("positive_iteration", (n, a, b, x)) for n in counts
              for a in (-2, -1, 0, 1, 2) for b in (-3, 0, 3) for x in (-5, 0, 7)]
    edges = (-2**64, -2**63 - 1, -2**63, -1, 0, 1, 2**63 - 1, 2**63, 2**64)
    cases += [Case("comparisons", (x, y)) for x in range(-3, 4) for y in range(-3, 4)]
    cases += [Case("comparisons", (x, y)) for x in edges for y in edges]
    cases += [Case("fast_division", (a, b)) for a in range(-6, 7) for b in range(-6, 7)]
    cases += [Case("fast_division", (a, b)) for a in edges for b in (-2**32 - 1, -3, 0, 3, 2**32 + 1)]
    cases += [Case("positive_division", (a, b)) for a in range(1, 13) for b in range(1, 13)]
    # Even divisors exercise the source's digit-peeling recursion before its odd fallback.
    cases += [Case("positive_division", (a, 2**k * m)) for k in (1, 5, 31, 32, 63, 64)
              for m in (1, 3) for a in (1, 2**k * m - 1, 2**k * m, 2**k * m + 1, 2**100 + 7)]
    rng = random.Random(seed)
    for _ in range(samples):
        cases.append(Case("conditional_negation", (rng.randrange(2), rng.randint(-2**127, 2**127))))
        cases.append(Case("positive_iteration", (rng.randint(1, 300), rng.randint(-3, 3),
                                                  rng.randint(-10, 10), rng.randint(-100, 100))))
        x = rng.randint(-2**127, 2**127)
        cases.append(Case("comparisons", (x, rng.choice((x, -x, x + 1, rng.randint(-2**127, 2**127))))))
        b = rng.choice((1, -1)) * rng.randint(1, 2**40) * 2**rng.randint(0, 20)
        cases.append(Case("fast_division", (rng.randint(-2**100, 2**100), rng.choice((b, 0, -b)))))
        cases.append(Case("positive_division", (rng.randint(1, 2**100),
                                                 rng.randint(1, 2**30) * 2**rng.randint(0, 40))))
    return sorted(dict.fromkeys(cases), key=lambda c: tuple(ARITIES).index(c.op))


def expected(case):
    if case.op == "conditional_negation":
        sign, value = case.args
        return [-value if sign else value]
    if case.op == "comparisons":
        x, y = case.args
        return [int(x == y), int(x <= y), int(x < y), (x > y) - (x < y)]
    if case.op == "fast_division":
        # Rocq's Z.div_eucl: floor quotient, remainder with the divisor's sign; (0, a) for b = 0.
        a, b = case.args
        return [0, a] if b == 0 else [a // b, a % b]
    if case.op == "positive_division":
        a, b = case.args
        return [a // b, a % b] * 2
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
        bridge.main(lean_build_targets=('FloatSpec.src.Core.Zaux',), profile_metadata=metadata)
