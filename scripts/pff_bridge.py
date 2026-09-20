"""Three-path executable Pff profile using the core bridge's strict runner.

The source facade observes its explicit integer radix. The four older
normalized compatibility APIs are separately labeled as operating at Core
type radix two, even though their ignored legacy argument receives the input
radix. Neither interface is silently substituted for the other.
"""
from contextlib import contextmanager
from dataclasses import asdict, dataclass
from fractions import Fraction
import random

import flocq_bridge as bridge

OPERATION = "pff_source"
GROUPS = (
    ("source.digit", 1), ("source.Fdigit", 1), ("source.Fshift", 2),
    ("source.Fplus", 2), ("source.Fminus", 2), ("source.Fnormalize", 2),
    ("source.Fopp", 2), ("source.Fabs", 2),
    ("integrated.Zpower_nat", 1), ("integrated.Zpower_nat_int", 1),
    ("integrated.nNormMin", 1), ("integrated.pPred", 1),
    ("integrated.firstNormalPos", 2), ("integrated.pffDigit", 1),
    ("integrated.Fdigit", 1), ("integrated.Fshift", 2),
    ("integrated.FSucc", 2), ("integrated.FPred", 2),
    ("integrated.Fnormalize", 2),
    ("integrated.FNSucc_type_radix_2", 2), ("integrated.FNPred_type_radix_2", 2),
    ("integrated.digit", 1), ("integrated.boundNat", 2),
    ("source.boundNat", 2), ("source.nNormMin", 1), ("source.firstNormalPos", 2),
    ("source.Feven", 1), ("source.Fodd", 1),
    ("source.FSucc", 2), ("source.FPred", 2),
    ("source.FNSucc", 2), ("source.FNPred", 2),
    ("source.FNeven", 1), ("source.FNodd", 1),
    ("integrated.FNeven_type_radix_2", 1), ("integrated.FNodd_type_radix_2", 1),
)
COLUMNS = tuple(name if width == 1 else name + "." + field
                for name, width in GROUPS
                for field in (("",) if width == 1 else ("mantissa", "exponent")))
OFFSETS = {}
_offset = 0
for _name, _width in GROUPS:
    OFFSETS[_name] = _offset
    _offset += _width
assert _offset == len(COLUMNS) == 56


@dataclass(frozen=True)
class Case:
    op: str
    args: tuple[int, ...]

    def __post_init__(self):
        if self.op != OPERATION or len(self.args) != 9:
            raise ValueError("Pff cases require pff_source and nine arguments")
        if any(type(value) is not int for value in self.args):
            raise ValueError("Pff inputs must be integers, not source text or Booleans")
        if any(value < 0 for value in self.args[5:]):
            raise ValueError("Pff shift, bound exponent, precision and bound predecessor are naturals")


def expressions(case: Case):
    return (
        "pffObserve " + " ".join(f"({value})" for value in case.args),
        "pffObserve " + " ".join(
            f"({value}%Z)" if index < 5 else f"(Z.to_nat ({value}%Z))"
            for index, value in enumerate(case.args)))


def valid_neighbor_corpus(seed: int, samples: int):
    """Sample the neighbor theorem domain, not just unrelated random bounds.

    Keep the Nat transport bound at most 4096: the Rocq adapter currently
    constructs its positive bound through nat. Large integer mantissas are
    exercised separately by the unrestricted corpus.
    """
    rng = random.Random(seed ^ 0x504646)
    cases = []
    for index in range(samples):
        radix = rng.choice((2, 3, 10, 16))
        maximum_precision = {2: 12, 3: 7, 10: 3, 16: 3}[radix]
        precision = rng.randint(1, maximum_precision)
        bound_num = radix ** precision
        bound_exp = rng.randint(0, 32)
        mantissa = (0 if index % 17 == 0 else
                    rng.choice((-1, 1)) * rng.randint(1, bound_num - 1))
        exponent = rng.choice((-bound_exp, -bound_exp + 1, rng.randint(-bound_exp, 32)))
        cases.append(Case(OPERATION, (
            radix, mantissa, exponent, -mantissa, exponent + 1,
            rng.randint(0, 16), bound_exp, precision, bound_num - 1)))
    return cases


def corpus(seed: int, samples: int):
    rng = random.Random(seed)
    cases = []
    for radix in (-3, -1, 0, 1, 2, 3, 10, 16):
        for mantissa in (-17, -9, -1, 0, 1, 2, 8, 9, 17):
            for exponent in (-7, -1, 0, 3):
                for precision in (0, 1, 3, 8):
                    cases.append(Case(OPERATION, (
                        radix, mantissa, exponent, 1-mantissa, exponent-1,
                        (precision+1) % 4, (precision+2) % 5, precision, precision)))
    for _ in range(samples):
        bits = rng.choice((4, 16, 64, 192))
        cases.append(Case(OPERATION, (
            rng.choice((-16, -3, -2, -1, 0, 1, 2, 3, 10, 16)),
            rng.randint(-(1 << bits), 1 << bits), rng.randint(-30, 30),
            rng.randint(-(1 << bits), 1 << bits), rng.randint(-30, 30),
            rng.randint(0, 32), rng.randint(0, 32), rng.randint(0, 256), rng.randint(0, 1024))))
    for radix in (2, 3, 10):
        for precision in (0, 1, 2, 5):
            bound_num = radix ** precision
            normal_min = radix ** max(precision-1, 0)
            for bound_exp in (0, 1, 10):
                for mantissa in sorted({
                        -bound_num, 1-bound_num, -normal_min-1, -normal_min,
                        -normal_min+1, -1, 0, 1, normal_min-1, normal_min,
                        normal_min+1, bound_num-1, bound_num}):
                    for exponent in (-bound_exp-1, -bound_exp, -bound_exp+1, 0):
                        cases.append(Case(OPERATION, (
                            radix, mantissa, exponent, -mantissa, exponent+1,
                            1, bound_exp, precision, bound_num-1)))
    return cases + valid_neighbor_corpus(seed, samples)


def pair(row, name):
    offset = OFFSETS[name]
    return row[offset:offset+2]


def scalar(row, name):
    return row[OFFSETS[name]]


def value(radix, fields):
    mantissa, exponent = fields
    if radix == 0 and exponent < 0:
        return Fraction(0)
    return mantissa * Fraction(radix) ** exponent


def independent_checks(case: Case, row: list[int]):
    """Exact finite invariants, independent of the Rocq observations."""
    if len(row) != len(COLUMNS) or any(type(item) is not int for item in row):
        raise ValueError("Pff independent oracle requires every integer observation")
    checks = 0
    def check(condition, label):
        nonlocal checks
        if not condition:
            raise AssertionError(f"Pff invariant {label!r} failed for {asdict(case)}")
        checks += 1

    radix, mantissa, exponent, other_mantissa, other_exponent, shift, bound_exp, precision, bound_pred = case.args
    x = value(radix, (mantissa, exponent))
    y = value(radix, (other_mantissa, other_exponent))
    normalized = pair(row, "source.Fnormalize")
    check(scalar(row, "source.digit") == scalar(row, "source.Fdigit"), "digit projection")
    check(pair(row, "source.Fshift") == [mantissa * radix ** shift, exponent-shift], "shift record")
    check(pair(row, "source.Fopp") == [-mantissa, exponent], "negation record")
    check(pair(row, "source.Fabs") == [abs(mantissa), exponent], "absolute-mantissa record")
    check(value(radix, pair(row, "source.Fopp")) == -x, "negation value")
    if radix != 0:
        check(value(radix, pair(row, "source.Fshift")) == x, "shift value")
        check(value(radix, pair(row, "source.Fplus")) == x+y, "addition value")
        check(value(radix, pair(row, "source.Fminus")) == x-y, "subtraction value")
        check(value(radix, normalized) == x, "normalization value")
    if radix > 0:
        check(value(radix, pair(row, "source.Fabs")) == abs(x), "absolute value")
    if radix >= 2:
        digits, remaining = 0, abs(mantissa)
        while remaining:
            remaining //= radix
            digits += 1
        check(scalar(row, "source.digit") == digits, "division-based digit count")
        check(value(radix, pair(row, "source.boundNat")) > precision, "strict natural bound")
    if mantissa == 0:
        check(normalized == [0, -bound_exp], "zero normalization exponent")
    check(scalar(row, "source.Feven") == int(mantissa % 2 == 0), "raw even predicate")
    check(scalar(row, "source.Fodd") == int(mantissa % 2 == 1), "raw odd predicate")
    check(scalar(row, "source.FNeven") == int(normalized[0] % 2 == 0), "normalized even predicate")
    check(scalar(row, "source.FNodd") == int(normalized[0] % 2 == 1), "normalized odd predicate")

    neighbor_checks = 0
    bound_num = bound_pred + 1
    if (radix >= 2 and precision > 0 and bound_num == radix ** precision
            and abs(mantissa) < bound_num and exponent >= -bound_exp):
        def canonical(fields):
            m, e = fields
            return (abs(m) < bound_num and e >= -bound_exp and
                    (bound_num <= abs(radix*m) or
                     (e == -bound_exp and abs(radix*m) < bound_num)))
        check(canonical(normalized), "normalization is canonical under source premises")
        successor = pair(row, "source.FNSucc")
        predecessor = pair(row, "source.FNPred")
        check(canonical(successor), "successor is canonical under source premises")
        check(canonical(predecessor), "predecessor is canonical under source premises")
        check(value(radix, successor) > x, "strict successor under source premises")
        check(value(radix, predecessor) < x, "strict predecessor under source premises")
        neighbor_checks = 5
    return checks, neighbor_checks


LEAN_HEADER = """import FloatSpec.src.Pff.SourceFacade
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option pp.maxSteps 200000
set_option pp.deepTerms true
namespace Bridge
def pair (x : FloatSpec.Pff.Source.float) : List Int := [x.Fnum, x.Fexp]
def pffSourceObserve (radix mantissa exponent otherMantissa otherExponent : Int)
    (shift boundExponent precision boundMantissaPred : Nat) : List Int :=
  let x : FloatSpec.Pff.Source.float := ⟨mantissa, exponent⟩
  let y : FloatSpec.Pff.Source.float := ⟨otherMantissa, otherExponent⟩
  let bound : FloatSpec.Pff.Source.Fbound :=
    ⟨boundMantissaPred + 1, boundExponent, Nat.zero_lt_succ _⟩
  [(FloatSpec.Pff.Source.digit radix mantissa : Int),
    (FloatSpec.Pff.Source.Fdigit radix x : Int)] ++
    pair (FloatSpec.Pff.Source.Fshift radix shift x) ++
    pair (FloatSpec.Pff.Source.Fplus radix x y) ++
    pair (FloatSpec.Pff.Source.Fminus radix x y) ++
    pair (FloatSpec.Pff.Source.Fnormalize radix bound precision x) ++
    pair (FloatSpec.Pff.Source.Fopp x) ++ pair (FloatSpec.Pff.Source.Fabs x)

open FloatSpec.Pff
def corePair (x : FloatSpec.Core.Defs.FlocqFloat 2) : List Int := [x.Fnum, x.Fexp]
def boolean (x : Bool) : Int := if x then 1 else 0
def pffObserve (radix mantissa exponent otherMantissa otherExponent : Int)
    (shift boundExponent precision boundMantissaPred : Nat) : List Int :=
  let x : Source.float := ⟨mantissa, exponent⟩
  let bound : Source.Fbound := ⟨boundMantissaPred + 1, boundExponent, Nat.zero_lt_succ _⟩
  let core := x.toCore 2
  let ib := bound.toIntegrated
  pffSourceObserve radix mantissa exponent otherMantissa otherExponent
    shift boundExponent precision boundMantissaPred ++
  [Zpower_nat radix shift, Zpower_nat_int radix shift,
    _root_.nNormMin radix precision, pPred ib.vNum] ++
  corePair (_root_.firstNormalPos radix ib precision) ++
  [(pffDigit radix mantissa : Int), (_root_.Fdigit radix core : Int)] ++
  corePair (_root_.Fshift radix shift core) ++
  corePair (_root_.FSucc ib radix precision core) ++
  corePair (_root_.FPred ib radix precision core) ++
  corePair (_root_.Fnormalize radix ib precision core) ++
  corePair (_root_.FNSucc ib (radix : Real) precision core) ++
  corePair (_root_.FNPred ib (radix : Real) precision core) ++
  [(_root_.digit radix mantissa : Int)] ++
  corePair (_root_.boundNat radix precision) ++
  pair (Source.boundNat radix precision) ++
  [Source.nNormMin radix precision] ++
  pair (Source.firstNormalPos radix bound precision) ++
  [boolean (@decide (Source.Feven x) (by unfold Source.Feven; infer_instance)),
    boolean (@decide (Source.Fodd x) (by unfold Source.Fodd; infer_instance))] ++
  pair (Source.FSucc bound radix precision x) ++
  pair (Source.FPred bound radix precision x) ++
  pair (Source.FNSucc bound radix precision x) ++
  pair (Source.FNPred bound radix precision x) ++
  [boolean (@decide (Source.FNeven bound radix precision x)
    (by unfold Source.FNeven Source.Feven; infer_instance)),
   boolean (@decide (Source.FNodd bound radix precision x)
    (by unfold Source.FNodd Source.Fodd; infer_instance)),
   boolean (@decide (_root_.FNeven ib (radix : Real) precision core)
    (by unfold _root_.FNeven _root_.Feven; infer_instance)),
   boolean (@decide (_root_.FNodd ib (radix : Real) precision core)
    (by unfold _root_.FNodd _root_.Fodd; infer_instance))]
"""

COQ_HEADER = """From Stdlib Require Import ZArith List.
Require Import Flocq.Pff.Pff.
Import ListNotations.
Open Scope Z_scope.
Definition pair (x : Pff.float) : list Z := [Pff.Fnum x; Pff.Fexp x].
Definition pffSourceObserve (radix mantissa exponent otherMantissa otherExponent : Z)
    (shift boundExponent precision boundMantissaPred : nat) : list Z :=
  let x := Pff.Float mantissa exponent in
  let y := Pff.Float otherMantissa otherExponent in
  let bound := Pff.Bound (Pos.of_nat (S boundMantissaPred)) (N.of_nat boundExponent) in
  [Z.of_nat (Pff.digit radix mantissa); Z.of_nat (Pff.Fdigit radix x)] ++
    pair (Pff.Fshift radix shift x) ++ pair (Pff.Fplus radix x y) ++
    pair (Pff.Fminus radix x y) ++ pair (Pff.Fnormalize radix bound precision x) ++
    pair (Pff.Fopp x) ++ pair (Pff.Fabs x).

Definition even_dec (p : Pff.float) : {Pff.Feven p} + {~ Pff.Feven p}.
Proof.
  destruct (Z.even (Pff.Fnum p)) eqn:H.
  - left. apply Z.even_spec. exact H.
  - right. intro He. apply Z.even_spec in He. congruence.
Defined.
Definition odd_dec (p : Pff.float) : {Pff.Fodd p} + {~ Pff.Fodd p}.
Proof.
  destruct (Z.odd (Pff.Fnum p)) eqn:H.
  - left. apply Z.odd_spec. exact H.
  - right. intro He. apply Z.odd_spec in He. congruence.
Defined.
Definition norm_even_dec (b : Pff.Fbound) (radix : Z) (precision : nat) (p : Pff.float)
    : {Pff.FNeven b radix precision p} + {~ Pff.FNeven b radix precision p} :=
  even_dec (Pff.Fnormalize radix b precision p).
Definition norm_odd_dec (b : Pff.Fbound) (radix : Z) (precision : nat) (p : Pff.float)
    : {Pff.FNodd b radix precision p} + {~ Pff.FNodd b radix precision p} :=
  odd_dec (Pff.Fnormalize radix b precision p).
Definition pffObserve (radix mantissa exponent otherMantissa otherExponent : Z)
    (shift boundExponent precision boundMantissaPred : nat) : list Z :=
  let x := Pff.Float mantissa exponent in
  let bound := Pff.Bound (Pos.of_nat (S boundMantissaPred)) (N.of_nat boundExponent) in
  pffSourceObserve radix mantissa exponent otherMantissa otherExponent
    shift boundExponent precision boundMantissaPred ++
  [Zpower_nat radix shift; Zpower_nat radix shift;
    Pff.nNormMin radix precision; Pff.pPred (Pff.vNum bound)] ++
  pair (Pff.firstNormalPos radix bound precision) ++
  [Z.of_nat (Pff.digit radix mantissa); Z.of_nat (Pff.Fdigit radix x)] ++
  pair (Pff.Fshift radix shift x) ++ pair (Pff.FSucc bound radix precision x) ++
  pair (Pff.FPred bound radix precision x) ++ pair (Pff.Fnormalize radix bound precision x) ++
  pair (Pff.FNSucc bound 2 precision x) ++ pair (Pff.FNPred bound 2 precision x) ++
  [Z.of_nat (Pff.digit radix mantissa)] ++
  pair (Pff.boundNat radix precision) ++ pair (Pff.boundNat radix precision) ++
  [Pff.nNormMin radix precision] ++ pair (Pff.firstNormalPos radix bound precision) ++
  [if even_dec x then 1 else 0; if odd_dec x then 1 else 0] ++
  pair (Pff.FSucc bound radix precision x) ++ pair (Pff.FPred bound radix precision x) ++
  pair (Pff.FNSucc bound radix precision x) ++ pair (Pff.FNPred bound radix precision x) ++
  [if norm_even_dec bound radix precision x then 1 else 0;
   if norm_odd_dec bound radix precision x then 1 else 0;
   if norm_even_dec bound 2 precision x then 1 else 0;
   if norm_odd_dec bound 2 precision x then 1 else 0].
"""

@contextmanager
def profile():
    """Install a standalone profile, then restore the shared module on every exit."""
    metadata = {
        "name": "Pff source and explicitly distinguished indexed compatibility APIs",
        "columns": COLUMNS,
        "legacy_normalized_radix": 2,
        "oracle_checked_cases": 0,
        "oracle_assertions": 0,
        "conditional_neighbor_assertions": 0,
    }
    original_compare = bridge.compare
    def compare(cases, observations):
        mismatches = original_compare(cases, observations)
        if not mismatches:
            for case, row in zip(cases, observations["compiled"], strict=True):
                try:
                    count, neighbors = independent_checks(case, row)
                except Exception:
                    metadata["oracle_failure_case"] = asdict(case)
                    raise
                metadata["oracle_checked_cases"] += 1
                metadata["oracle_assertions"] += count
                metadata["conditional_neighbor_assertions"] += neighbors
        return mismatches
    overrides = {
        "OPS": (OPERATION,), "ARITIES": {OPERATION: 9},
        "WIDTHS": {OPERATION: len(COLUMNS)}, "RADIX_OPS": set(),
        "BATCH_LIMITS": {OPERATION: 50}, "Case": Case,
        "LEAN_HEADER": LEAN_HEADER, "COQ_HEADER": COQ_HEADER,
        "expressions": expressions, "corpus": corpus, "compare": compare,
    }
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
        bridge.main(lean_build_targets=("FloatSpec.src.Pff.SourceFacade",),
                    profile_metadata=metadata)


if __name__ == "__main__":
    main()
