"""Executable Pff bound construction and an explicitly classified adapter.

Only make_bound, bsingle and bdouble are source exports here. PFnormalize
is a Lean indexed adapter: its signed precision is passed to the source
normalizer via abs_nat. Local compare/min/max helpers have a separate exact
rational Lean test; they are not invented Flocq declarations.
"""
from contextlib import contextmanager
from dataclasses import asdict, dataclass
from fractions import Fraction
import random

import flocq_bridge as bridge

OPERATION = "pff_bounds"
COLUMNS = ("make_bound.vNum", "make_bound.dExp", "bsingle.vNum", "bsingle.dExp",
           "bdouble.vNum", "bdouble.dExp", "PFnormalize.left.mantissa",
           "PFnormalize.left.exponent", "PFnormalize.right.mantissa",
           "PFnormalize.right.exponent")


@dataclass(frozen=True)
class Case:
    op: str
    args: tuple[int, ...]

    def __post_init__(self):
        if self.op != OPERATION or len(self.args) != 7:
            raise ValueError("Pff bound cases require pff_bounds and seven arguments")
        if any(type(value) is not int for value in self.args):
            raise ValueError("Pff bound inputs must be integers")
        if self.args[0] < 2:
            raise ValueError("make_bound exports a valid radix, not an unrestricted integer radix")


def expressions(case):
    radix, *rest = case.args
    return (
        f"pffBoundsObserve ({radix}) " + " ".join(f"({value})" for value in rest),
        f"pffBoundsObserve (Build_radix {radix} eq_refl) " +
        " ".join(f"({value}%Z)" for value in rest))


def corpus(seed, samples):
    cases = [Case(OPERATION, (radix, precision, bound_exp, mantissa, exponent,
                              -mantissa, exponent+1))
             for radix in (2, 3, 10, 16)
             for precision in (-3, -1, 0, 1, 2, 8, 24, 53)
             for bound_exp in (-1074, -149, -1, 0, 1, 149, 1074)
             for mantissa in (-17, 0, 1) for exponent in (-1075, -1, 3)]
    rng = random.Random(seed)
    for _ in range(samples):
        bits = rng.choice((4, 64, 192))
        cases.append(Case(OPERATION, (
            rng.choice((2, 3, 10, 16)), rng.choice((-256, -53, -1, 0, 1, 24, 53, 256)),
            rng.randint(-1200, 1200), rng.randint(-(1 << bits), 1 << bits),
            rng.randint(-1200, 1200), rng.randint(-(1 << bits), 1 << bits),
            rng.randint(-1200, 1200))))
    return cases


def independent_checks(case, row):
    if len(row) != len(COLUMNS) or any(type(item) is not int for item in row):
        raise ValueError("Pff bound oracle requires ten integer observations")
    radix, precision, bound_exp, mantissa, exponent, other_mantissa, other_exponent = case.args
    count = 0
    def check(condition, label):
        nonlocal count
        if not condition:
            raise AssertionError(f"Pff bound invariant {label!r} failed for {asdict(case)}")
        count += 1
    bound_num = 1 if precision < 0 else radix ** precision
    bound_abs = abs(bound_exp)
    check(row[:2] == [bound_num, bound_abs], "source positive/natural refinements")
    check(row[2:6] == [1 << 24, 149, 1 << 53, 1074], "predefined bounds")
    for offset, m, e in ((6, mantissa, exponent), (8, other_mantissa, other_exponent)):
        nm, ne = row[offset:offset+2]
        check(nm * Fraction(radix) ** ne == m * Fraction(radix) ** e, "normalization value")
        if m == 0:
            check((nm, ne) == (0, -bound_abs), "normalized zero exponent")
        if precision > 0 and abs(m) < bound_num and e >= -bound_abs:
            check(abs(nm) < bound_num and ne >= -bound_abs and
                  (bound_num <= abs(radix * nm) or
                   (ne == -bound_abs and abs(radix * nm) < bound_num)),
                  "canonical normalization under source premises")
    return count


LEAN_HEADER = """import FloatSpec.src.Pff.Pff2FlocqAux
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option pp.maxSteps 200000
set_option pp.deepTerms true
namespace Bridge
def pair {radix : Int} [ValidRadix radix] (x : PffFloat radix) : List Int :=
  [x.Fnum, x.Fexp]
def pffBoundsObserve (radix : Int) [ValidRadix radix]
    (precision boundExponent mantissa exponent otherMantissa otherExponent : Int) : List Int :=
  let bound := make_bound radix precision boundExponent ValidRadix.valid
  let x : PffFloat radix := ⟨mantissa, exponent⟩
  let y : PffFloat radix := ⟨otherMantissa, otherExponent⟩
  [bound.vNum, bound.dExp, bsingle.vNum, bsingle.dExp, bdouble.vNum, bdouble.dExp] ++
    pair (PFnormalize radix bound precision x) ++
    pair (PFnormalize radix bound precision y)
"""

COQ_HEADER = """From Stdlib Require Import ZArith List.
From Flocq Require Import Core.Zaux Pff.Pff2FlocqAux.
Import ListNotations.
Open Scope Z_scope.
Definition pair (x : Pff.float) : list Z := [Pff.Fnum x; Pff.Fexp x].
Definition pffBoundsObserve (radix : radix)
    (precision boundExponent mantissa exponent otherMantissa otherExponent : Z) : list Z :=
  let bound := make_bound radix precision boundExponent in
  let x := Pff.Float mantissa exponent in
  let y := Pff.Float otherMantissa otherExponent in
  [Zpos (Pff.vNum bound); Z.of_N (Pff.dExp bound);
   Zpos (Pff.vNum bsingle); Z.of_N (Pff.dExp bsingle);
   Zpos (Pff.vNum bdouble); Z.of_N (Pff.dExp bdouble)] ++
    pair (Pff.Fnormalize radix bound (Z.abs_nat precision) x) ++
    pair (Pff.Fnormalize radix bound (Z.abs_nat precision) y).
"""


@contextmanager
def profile():
    metadata = {"name": "Pff source bounds and signed-precision normalization adapter",
                "columns": COLUMNS, "source_exports": ["make_bound", "bsingle", "bdouble"],
                "adapter": "PFnormalize precision maps to source Z.abs_nat precision",
                "oracle_checked_cases": 0, "oracle_assertions": 0}
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
        return mismatches
    overrides = {"OPS": (OPERATION,), "ARITIES": {OPERATION: 7},
                 "WIDTHS": {OPERATION: len(COLUMNS)}, "RADIX_OPS": {OPERATION},
                 "BATCH_LIMITS": {OPERATION: 50}, "Case": Case,
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
        bridge.main(lean_build_targets=("FloatSpec.src.Pff.Pff2FlocqAux",),
                    profile_metadata=metadata)


if __name__ == "__main__":
    main()
