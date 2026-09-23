"""Emission-time cost model and cost-based batching (FLOCQSMITH.md §13).

A timeout is not a comparable outcome, so every op is priced when it is
emitted and an arm the remaining budget cannot afford is masked. Costs are
predicted ``lean-kernel`` milliseconds (the slowest judged path), calibrated
from the design probe: ordinary binary64 operations cost 1-41 ms and
far-apart plus/fma operands cost about 0.5-0.65 ms per bit of exponent gap.
Every BSN value carries a static interval for the exponent field of its finite
values, so the gap of a later plus is bounded at emission. Shifts in
``binary_normalize``/``Bldexp``/``Btrunc`` are linear in the shift distance
(``SpecFloat.shr`` is ``iter_pos``), so they are charged per shifted bit.
"""

from __future__ import annotations

from dataclasses import dataclass

from .formats import Format
from .table import OP_BY_NAME

GAP_MS_PER_BIT = 0.65
SHIFT_MS_PER_BIT = 0.4


@dataclass(frozen=True)
class Info:
    """Static knowledge of a binding.

    For a BSN binding, ``lo``/``hi`` bound the exponent field of any finite
    value it can take; ``finite`` is False when it can only be a zero, an
    infinity or NaN. ``exact`` is the literal ``(sign, m, e)`` when known.
    """

    type: str
    lo: int = 0
    hi: int = 0
    exact: tuple[int, int, int] | None = None
    finite: bool = True

    @staticmethod
    def full(fmt: Format) -> "Info":
        return Info("BSN", fmt.emin, fmt.emax_field)

    @staticmethod
    def point(fmt: Format, sign: int, m: int, e: int) -> "Info":
        canonical = fmt.canonical(m, e)
        if canonical is None:
            raise ValueError("point info needs a representable value")
        return Info("BSN", canonical[1], canonical[1], (sign, canonical[0], canonical[1]))

    def union(self, other: "Info") -> "Info":
        if not self.finite:
            return Info(other.type, other.lo, other.hi, None, other.finite)
        if not other.finite:
            return Info(self.type, self.lo, self.hi, None, self.finite)
        return Info(self.type, min(self.lo, other.lo), max(self.hi, other.hi))


def _clamp(fmt: Format, lo: int, hi: int) -> Info:
    lo, hi = max(fmt.emin, lo), min(fmt.emax_field, hi)
    if lo > hi:
        lo = hi = fmt.emin
    return Info("BSN", lo, hi)


def result_info(op: str, fmt: Format, args: list[Info]) -> Info:
    """Conservative exponent bounds of an op's BSN result."""
    row = OP_BY_NAME[op]
    if row.result != "BSN":
        return Info(row.result)
    bsn = [a for a in args if a.type == "BSN"]
    finite = [a for a in bsn if a.finite]
    if op in ("Bopp", "Babs", "erase") and bsn:
        return bsn[0]
    if len(finite) != len(bsn):
        return Info.full(fmt)
    if op == "Bmult" and len(bsn) == 2:
        return _clamp(fmt, bsn[0].lo + bsn[1].lo - fmt.p, bsn[0].hi + bsn[1].hi + fmt.p)
    if op == "Bdiv" and len(bsn) == 2:
        return _clamp(fmt, bsn[0].lo - bsn[1].hi - 2 * fmt.p, bsn[0].hi - bsn[1].lo + 2 * fmt.p)
    if op in ("Bplus", "Bminus") and len(bsn) == 2:
        return _clamp(fmt, min(bsn[0].lo, bsn[1].lo), max(bsn[0].hi, bsn[1].hi) + 1)
    if op == "Bsqrt" and bsn:
        return _clamp(fmt, (bsn[0].lo - fmt.p) // 2 - 1, (bsn[0].hi + fmt.p) // 2 + 1)
    if op in ("Bsucc", "Bpred", "Bsucc'", "Bpred_pos'", "Bnearbyint") and bsn:
        return _clamp(fmt, bsn[0].lo - 1, bsn[0].hi + 1)
    return Info.full(fmt)


def base_cost(fmt: Format) -> float:
    return 1.0 + fmt.p / 8


def op_cost(op: str, fmt: Format, args: list[Info], exponents: list[int | None]) -> float:
    """Predicted kernel milliseconds for one application of ``op``.

    ``exponents`` lists the E-typed arguments in order: the literal value, or
    None for a reference (charged at the static bound ``2*emax + 2*p``).
    """
    row = OP_BY_NAME[op]
    base = base_cost(fmt)
    bound = 2 * fmt.emax + 2 * fmt.p
    literal = [abs(e) if e is not None else bound for e in exponents]
    finite = [a for a in args if a.type == "BSN" and a.finite]
    if row.cost in ("mint", "unary"):
        return base
    if row.cost == "arith":
        return 2 * base
    if row.cost == "div":
        return 3 * base + fmt.p / 2
    if row.cost == "gap":
        spans = [(a.lo, a.hi) for a in finite]
        if op == "Bfma" and len(args) == 3:
            x, y, z = args
            spans = []
            if x.finite and y.finite:
                spans.append((x.lo + y.lo, x.hi + y.hi + fmt.p))
            if z.finite:
                spans.append((z.lo, z.hi))
        gap = max(hi for _, hi in spans) - min(lo for lo, _ in spans) if spans else 0
        return 2 * base + GAP_MS_PER_BIT * max(gap, 0)
    if row.cost == "ldexp":
        if op == "Bldexp":
            shift = (literal[0] if literal else bound) + max((a.hi - a.lo for a in finite), default=0)
        else:
            shift = max((max(0, -a.lo) for a in finite), default=0)
        return 2 * base + SHIFT_MS_PER_BIT * shift
    if row.cost == "normalize":
        low = -literal[0] if exponents and exponents[0] is not None and exponents[0] < 0 else (
            -bound if exponents and exponents[0] is None else 0)
        shift = fmt.p + max(0, fmt.emin - low)
        return 2 * base + SHIFT_MS_PER_BIT * shift
    raise ValueError(f"unknown cost class {row.cost}")


def pack(costs: list[float], capacity_ms: float, max_items: int) -> list[list[int]]:
    """Consecutive batches filled up to predicted cost (§13.2); order preserved."""
    batches: list[list[int]] = []
    current: list[int] = []
    load = 0.0
    for index, cost in enumerate(costs):
        if current and (load + cost > capacity_ms or len(current) >= max_items):
            batches.append(current)
            current, load = [], 0.0
        current.append(index)
        load += cost
    if current:
        batches.append(current)
    return batches
