"""The one choice primitive and its replayable draw tape (FLOCQSMITH.md §3.4, §8.1).

Every random decision the generator makes goes through :class:`Chooser`.
A draw is recorded as ``(site, bound, value)`` with ``0 <= value < bound``.
Generation draws from a seeded PRNG; replay reads the same triples back from a
tape and checks each one. There are no rejection loops: an empty legal arm set
is a generator bug and raises :class:`GeneratorBug`, never a silent retry.
"""

from __future__ import annotations

from dataclasses import dataclass
import random
from typing import Sequence, TypeVar

T = TypeVar("T")


class GeneratorBug(RuntimeError):
    """The generator asked for an impossible draw (empty legal set, bound < 1)."""


class ReplayError(ValueError):
    """A tape does not decode under the current generator.

    ``kind`` is one of a closed set so tests and reports never match text:
    ``exhausted`` (tape ran out), ``site`` (site name differs), ``bound``
    (bound differs), ``range`` (value outside ``[0, bound)``), ``illegal``
    (value names a masked arm), ``leftover`` (values left after generation),
    ``rendering`` (regenerated renderings do not hash to the recorded ones).
    """

    KINDS = frozenset({"exhausted", "site", "bound", "range", "illegal", "leftover", "rendering"})

    def __init__(self, kind: str, message: str) -> None:
        if kind not in self.KINDS:
            raise ValueError(f"unknown ReplayError kind {kind!r}")
        super().__init__(f"{kind}: {message}")
        self.kind = kind


@dataclass(frozen=True)
class Draw:
    site: str
    bound: int
    value: int

    def to_json(self) -> list[object]:
        return [self.site, self.bound, self.value]

    @staticmethod
    def from_json(row: object) -> "Draw":
        if (not isinstance(row, list) or len(row) != 3 or not isinstance(row[0], str)
                or type(row[1]) is not int or type(row[2]) is not int):
            raise ReplayError("range", f"malformed draw {row!r}")
        return Draw(row[0], row[1], row[2])


class Chooser:
    """Seeded generation (``seed``) or checked replay (``tape``); never both."""

    def __init__(self, *, seed: str | None = None, tape: Sequence[Draw] | None = None) -> None:
        if (seed is None) == (tape is None):
            raise ValueError("give exactly one of seed or tape")
        self._rng = random.Random(seed) if seed is not None else None
        self._tape = list(tape) if tape is not None else None
        self._cursor = 0
        self.draws: list[Draw] = []

    @property
    def replaying(self) -> bool:
        return self._tape is not None

    def _draw(self, site: str, bound: int, weights: Sequence[int] | None = None) -> int:
        if bound < 1:
            raise GeneratorBug(f"nonpositive bound {bound} at {site}")
        if self._tape is not None:
            if self._cursor >= len(self._tape):
                raise ReplayError("exhausted", f"tape ended before draw {len(self.draws)} at {site}")
            draw = self._tape[self._cursor]
            self._cursor += 1
            if draw.site != site:
                raise ReplayError("site", f"draw {len(self.draws)}: tape {draw.site!r}, generator {site!r}")
            if draw.bound != bound:
                raise ReplayError("bound", f"draw {len(self.draws)} at {site}: tape {draw.bound}, generator {bound}")
            if not 0 <= draw.value < bound:
                raise ReplayError("range", f"draw {len(self.draws)} at {site}: {draw.value} not in [0, {bound})")
            if weights is not None and weights[draw.value] <= 0:
                raise ReplayError("illegal", f"draw {len(self.draws)} at {site}: arm {draw.value} is masked")
            value = draw.value
        else:
            assert self._rng is not None
            if weights is None:
                value = self._rng.randrange(bound)
            else:
                total = sum(weights)
                ticket = self._rng.randrange(total)
                value = 0
                while ticket >= weights[value]:
                    ticket -= weights[value]
                    value += 1
        self.draws.append(Draw(site, bound, value))
        return value

    def below(self, site: str, bound: int) -> int:
        """Uniform integer in ``[0, bound)``."""
        return self._draw(site, bound)

    def randint(self, site: str, low: int, high: int) -> int:
        """Uniform integer in ``[low, high]``."""
        return low + self._draw(site, high - low + 1)

    def coin(self, site: str, numerator: int, denominator: int) -> bool:
        """True with probability ``numerator / denominator``."""
        if not 0 <= numerator <= denominator or denominator < 1:
            raise GeneratorBug(f"bad probability {numerator}/{denominator} at {site}")
        return self.choose(site, [(True, numerator), (False, denominator - numerator)])

    def choose(self, site: str, arms: Sequence[tuple[T, int]]) -> T:
        """Weight x legality mask, renormalize, one draw.

        An arm with weight 0 is masked. The draw records the arm index among
        all arms, so replay checks the mask as well as the index.
        """
        if not arms:
            raise GeneratorBug(f"no arms at {site}")
        weights = [weight for _, weight in arms]
        if any(type(weight) is not int or weight < 0 for weight in weights):
            raise GeneratorBug(f"weights must be nonnegative integers at {site}: {weights}")
        if sum(weights) == 0:
            raise GeneratorBug(f"empty legal set at {site}")
        return arms[self._draw(site, len(arms), weights)][0]

    def finish(self) -> None:
        """Reject leftover tape values (replay only)."""
        if self._tape is not None and self._cursor != len(self._tape):
            raise ReplayError("leftover", f"{len(self._tape) - self._cursor} unused draws")
