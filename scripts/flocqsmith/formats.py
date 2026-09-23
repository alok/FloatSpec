"""Formats and exact finite values (FLOCQSMITH.md §3.1, §4.1).

A BinarySingleNaN format is ``(p, emax)`` with ``0 < p < emax`` at radix 2,
``emin = 3 - emax - p``. A finite value is ``(-1)^s * m * 2^e``. Canonical
carriers satisfy ``1 <= m < 2^p``, ``emin <= e <= emax - p`` and either
``m >= 2^(p-1)`` or ``e == emin`` (Flocq ``bounded``).
"""

from __future__ import annotations

from dataclasses import dataclass


@dataclass(frozen=True)
class Format:
    name: str
    p: int
    emax: int
    ieee: bool

    def __post_init__(self) -> None:
        if not 0 < self.p < self.emax:
            raise ValueError(f"{self.name}: need 0 < p < emax")

    @property
    def emin(self) -> int:
        return 3 - self.emax - self.p

    @property
    def emax_field(self) -> int:
        """Largest exponent field of a canonical finite value."""
        return self.emax - self.p

    @property
    def exponent_span(self) -> int:
        """Bits between the smallest and largest canonical exponent fields."""
        return self.emax_field - self.emin

    def canonical(self, m: int, e: int) -> tuple[int, int] | None:
        """Canonical ``(m, e)`` for the exact value ``m * 2^e`` (m > 0), or None.

        None means the value is not representable in this format (needs more
        than ``p`` digits, is below the subnormal grid, or overflows).
        """
        if m <= 0:
            raise ValueError("canonical expects a positive mantissa")
        while m % 2 == 0:
            m //= 2
            e += 1
        if m.bit_length() > self.p or e < self.emin:
            return None
        shift = min(self.p - m.bit_length(), e - self.emin)
        m <<= shift
        e -= shift
        if e > self.emax_field:
            return None
        return m, e

    def is_canonical(self, m: int, e: int) -> bool:
        return (1 <= m < (1 << self.p) and self.emin <= e <= self.emax_field
                and (m >= (1 << (self.p - 1)) or e == self.emin))

    def to_json(self) -> dict[str, object]:
        return {"name": self.name, "p": self.p, "emax": self.emax}


# Name, (p, emax), IEEE-shaped. Only these formats are generated; tiny
# non-IEEE formats include precision 1 and an emax that is not a power of two.
FORMATS: dict[str, Format] = {f.name: f for f in (
    Format("t1_2", 1, 2, False),
    Format("t2_3", 2, 3, False),
    Format("t3_4", 3, 4, True),
    Format("t4_8", 4, 8, True),
    Format("t5_7", 5, 7, False),
    Format("t8_16", 8, 16, True),
    Format("b16", 11, 16, True),
    Format("bf16", 8, 128, True),
    Format("b32", 24, 128, True),
    Format("b64", 53, 1024, True),
)}

# Default campaign weights: cheap, exhaustible formats dominate; wide formats
# still appear so exponent-gap costs are exercised under the budget.
DEFAULT_FORMAT_WEIGHTS: dict[str, int] = {
    "t1_2": 1, "t2_3": 2, "t3_4": 4, "t4_8": 4, "t5_7": 2, "t8_16": 3,
    "b16": 5, "bf16": 2, "b32": 2, "b64": 2,
}


def format_by_params(p: int, emax: int) -> Format:
    for fmt in FORMATS.values():
        if (fmt.p, fmt.emax) == (p, emax):
            return fmt
    raise KeyError(f"no generated format with p={p}, emax={emax}")
