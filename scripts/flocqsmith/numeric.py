"""Tags: structural ones from the IR, numeric ones confirmed from reference values.

A case claims a tag only if the construct actually occurred (§4.5). Structural
tags (format, ops, forms, corners, spellings, modes) are read from the IR,
never from rendered text. Numeric tags (``tie``, ``inexact``,
``subnormal_range``, ``overflow_range``, ``exact_zero_sum``, ``nan_result``,
``negative_zero_result``) are computed with exact rationals from the *Rocq*
values of each arithmetic op's operands. This is a separate axis: it never
votes on port fidelity. For non-IEEE formats the same grid arithmetic applies
(FLT with ``emin = 3 - emax - p``), so these tags are exact there as well;
they are not cross-checked against ``ieee_exact_oracle.py``.
"""

from __future__ import annotations

from collections import Counter
from fractions import Fraction
from math import isqrt

from .formats import Format
from .ir import Arg, Program, iter_bindings
from .observe import Observed, values_by_id
from .table import FOLD_SHAPES, MODE_NAMES


def structural_tags(program: Program) -> Counter[str]:
    tags: Counter[str] = Counter()
    tags[f"fmt:{program.fmt.name}"] += 1
    for s in iter_bindings(program.stmts):
        if s.kind == "op":
            tags[f"op:{s.op}"] += 1
            if s.spelling == "source":
                tags["spelling:source"] += 1
            if s.op == "SF2B'" and s.args[0].kind == "sf":
                kind, _, m, e = s.args[0].value  # type: ignore[misc]
                if kind == 3 and not program.fmt.is_canonical(m, e):
                    tags["noncanonical_carrier"] += 1
        elif s.kind == "fold":
            tags[f"op:{s.op}"] += len(s.steps)
            tags[f"form:fold_{len(s.steps)}"] += 1
        else:
            tags[f"form:{s.kind}"] += 1
        if s.mode is not None:
            tags[f"mode:{MODE_NAMES[s.mode]}"] += 1
        if s.corner is not None:
            tags[f"corner:{s.corner}"] += 1
    return tags


Special = str  # "+0", "-0", "+inf", "-inf", "nan"


def bsn_value(value: tuple[int, ...]) -> Fraction | Special:
    kind, sign, m, e = value
    if kind == 0:
        return "-0" if sign else "+0"
    if kind == 1:
        return "-inf" if sign else "+inf"
    if kind == 2:
        return "nan"
    magnitude = Fraction(m) * (Fraction(2) ** e)
    return -magnitude if sign else magnitude


def _as_rational(v: Fraction | Special) -> Fraction | None:
    if isinstance(v, Fraction):
        return v
    if v in ("+0", "-0"):
        return Fraction(0)
    return None


def floor_log2(a: Fraction) -> int:
    k = a.numerator.bit_length() - a.denominator.bit_length()
    if Fraction(2) ** k > a:
        k -= 1
    return k


def round_ne(r: Fraction, fmt: Format) -> tuple[int, int] | None:
    """Round a positive rational to nearest-even on the format grid.

    Returns the canonical ``(m, e)``, or None on overflow or underflow to zero.
    Used only by the generator to *construct* operands; it never judges.
    """
    if r <= 0:
        raise ValueError("round_ne expects a positive rational")
    e = max(floor_log2(r) - fmt.p + 1, fmt.emin)
    q = r / (Fraction(2) ** e)
    n = q.numerator // q.denominator
    rest = q - n
    if rest > Fraction(1, 2) or (rest == Fraction(1, 2) and n % 2 == 1):
        n += 1
    if n == 0:
        return None
    return fmt.canonical(n, e)


def classify(r: Fraction, fmt: Format) -> set[str]:
    """Where the exact result sits relative to the format grid."""
    if r == 0:
        return {"exact"}
    a = abs(r)
    e = max(floor_log2(a) - fmt.p + 1, fmt.emin)
    q = a / (Fraction(2) ** e)
    tags = set()
    if q.denominator == 1:
        tags.add("exact")
    elif (2 * q).denominator == 1:
        tags.add("tie")
    else:
        tags.add("inexact")
    if a > Fraction((1 << fmt.p) - 1) * Fraction(2) ** (fmt.emax - fmt.p):
        tags.add("overflow_range")
    if a < Fraction(2) ** (fmt.emin + fmt.p - 1):
        tags.add("subnormal_range")
    return tags


def exact_result(op: str, args: list[Fraction | Special]) -> Fraction | None:
    """The exact rational result for finite operands, else None."""
    xs = [_as_rational(a) for a in args]
    if any(x is None for x in xs):
        return None
    vals = [x for x in xs if x is not None]
    if op == "Bplus":
        return vals[0] + vals[1]
    if op == "Bminus":
        return vals[0] - vals[1]
    if op == "Bmult":
        return vals[0] * vals[1]
    if op == "Bdiv":
        return vals[0] / vals[1] if vals[1] != 0 else None
    if op == "Bfma":
        return vals[0] * vals[1] + vals[2]
    return None


def _sqrt_exact(x: Fraction) -> bool:
    n, d = x.numerator, x.denominator
    return isqrt(n) ** 2 == n and isqrt(d) ** 2 == d


ARITH = ("Bplus", "Bminus", "Bmult", "Bdiv", "Bfma", "Bsqrt")


def numeric_tags(program: Program, reference: tuple[Observed, ...]) -> Counter[str]:
    """Numeric tags of the arithmetic ops whose operands the reference observed."""
    values = values_by_id(reference)
    tags: Counter[str] = Counter()

    def operand(arg: Arg) -> Fraction | Special | None:
        if arg.kind != "ref" or str(arg.value) not in values:
            return None
        observed = values[str(arg.value)]
        return bsn_value(observed.value) if observed.type == "BSN" else None

    def visit(op: str, mode: int | None, args: list[Arg], result_id: str) -> None:
        if op not in ARITH or result_id not in values:
            return
        operands = [operand(a) for a in args]
        if any(o is None for o in operands):
            return
        result = values[result_id].value
        if result[0] == 2:
            tags["nan_result"] += 1
        if result[0] == 0 and result[1] == 1:
            tags["negative_zero_result"] += 1
        mode_name = MODE_NAMES[mode] if mode is not None else "NE"
        if op == "Bsqrt":
            x = _as_rational(operands[0])  # type: ignore[arg-type]
            if x is not None and x > 0:
                tags["exact" if _sqrt_exact(x) else "inexact"] += 1
            return
        exact = exact_result(op, operands)  # type: ignore[arg-type]
        if exact is None:
            return
        if exact == 0 and op in ("Bplus", "Bminus", "Bfma") and all(
                _as_rational(o) != 0 for o in operands):  # type: ignore[arg-type]
            tags["exact_zero_sum"] += 1
            tags[f"exact_zero_sum:{mode_name}"] += 1
        for tag in classify(exact, program.fmt):
            tags[tag] += 1
            if tag == "tie":
                tags[f"tie:{mode_name}"] += 1

    for s in iter_bindings(program.stmts):
        if s.kind == "op" and s.op is not None:
            visit(s.op, s.mode, list(s.args), s.id)
        elif s.kind == "fold" and s.op is not None:
            acc_position, _ = FOLD_SHAPES[s.op]
            acc = s.args[0]
            for name, step in zip(s.fold_ids(), s.steps):
                args = list(step)
                args.insert(acc_position, acc)
                visit(s.op, s.mode, args, name)
                acc = Arg.ref(name)
    return tags

