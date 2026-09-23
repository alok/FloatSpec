"""Typed decoding and validation of observation documents (FLOCQSMITH.md §5.2).

The wire format is one flat integer list per case. Its meaning comes from the
observation signature. Structure is checked before meaning: an invalid
document (wrong arity, out-of-range tag or sign, a mantissa that no carrier of
the format can hold, an unknown branch tag) raises :class:`DecodeError` and is
never compared.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Sequence

Value = tuple[int, ...]


class DecodeError(ValueError):
    """The document does not fit its observation signature."""


@dataclass(frozen=True)
class Observed:
    """One decoded binding; ``arm`` is set for branch tags (0 or 1)."""

    id: str
    type: str
    op: str
    value: Value
    arm: tuple["Observed", ...] | None = None


WIDTHS = {"BSN": 4, "SF": 4, "Z": 1, "E": 1, "N": 1, "Bool": 1, "Cmp": 1}


def _check(type_: str, value: Value, p: int, emax: int) -> None:
    if type_ in ("BSN", "SF"):
        kind, sign, m, e = value
        if kind not in range(4) or sign not in (0, 1):
            raise DecodeError(f"constructor {kind} or sign {sign} out of range")
        if kind in (0, 1) and (m, e) != (0, 0):
            raise DecodeError("zero/infinity carries a mantissa")
        if kind == 2 and (sign, m, e) != (0, 0, 0):
            raise DecodeError("single NaN carries data")
        if kind == 3:
            if m < 1:
                raise DecodeError(f"finite mantissa {m} is not positive")
            if type_ == "BSN":
                emin = 3 - emax - p
                if not (m < (1 << p) and emin <= e <= emax - p and (m >= (1 << (p - 1)) or e == emin)):
                    raise DecodeError(f"({m}, {e}) is not a bounded carrier of ({p}, {emax})")
    elif type_ == "Bool":
        if value[0] not in (0, 1):
            raise DecodeError(f"boolean {value[0]}")
    elif type_ == "Cmp":
        if value[0] not in (-1, 0, 1, 2):
            raise DecodeError(f"comparison code {value[0]}")
    elif type_ == "N":
        if value[0] < 0:
            raise DecodeError(f"natural {value[0]}")
    elif type_ not in ("Z", "E"):
        raise DecodeError(f"unknown type {type_}")


def decode(signature: dict[str, object], document: Sequence[int]) -> tuple[Observed, ...]:
    if not all(type(n) is int for n in document):
        raise DecodeError("document contains a non-integer")
    p, emax = int(signature["p"]), int(signature["emax"])  # type: ignore[call-overload]
    values, cursor = _decode_block(signature["bindings"], document, 0, p, emax)  # type: ignore[arg-type]
    if cursor != len(document):
        raise DecodeError(f"{len(document) - cursor} trailing integers")
    return values


def _decode_block(rows: list[dict[str, object]], document: Sequence[int], cursor: int,
                  p: int, emax: int) -> tuple[tuple[Observed, ...], int]:
    out: list[Observed] = []
    for row in rows:
        type_, name, op = str(row["type"]), str(row["id"]), str(row["op"])
        if type_ == "branch":
            if cursor >= len(document):
                raise DecodeError(f"{name}: truncated before branch tag")
            tag = document[cursor]
            if tag not in (0, 1):
                raise DecodeError(f"{name}: branch tag {tag}")
            arms = row["arms"]
            inner, cursor = _decode_block(arms[tag], document, cursor + 1, p, emax)  # type: ignore[index]
            out.append(Observed(name, type_, op, (tag,), inner))
            continue
        width = WIDTHS.get(type_)
        if width is None:
            raise DecodeError(f"{name}: unknown type {type_}")
        if cursor + width > len(document):
            raise DecodeError(f"{name}: truncated")
        value = tuple(document[cursor:cursor + width])
        _check(type_, value, p, emax)
        out.append(Observed(name, type_, op, value))
        cursor += width
    return tuple(out), cursor


def flatten(values: Sequence[Observed]) -> list[Observed]:
    """Program-order bindings, with a branch followed by its taken arm's bindings."""
    out: list[Observed] = []
    for v in values:
        out.append(v)
        if v.arm is not None:
            out.extend(flatten(v.arm))
    return out


def first_divergence(reference: Sequence[Observed], clone: Sequence[Observed]) -> Observed | None:
    """The first binding (program order) whose value differs; branch tags first."""
    ref_flat, clone_flat = flatten(reference), flatten(clone)
    for r, c in zip(ref_flat, clone_flat):
        if r.id != c.id:
            # A branch took a different arm: the divergence is the branch tag,
            # which precedes this point in program order.
            raise AssertionError("tags agreed but binding ids differ")
        if r.value != c.value:
            return r
    if len(ref_flat) != len(clone_flat):
        raise AssertionError("equal tags but different arity")
    return None


def values_by_id(values: Sequence[Observed]) -> dict[str, Observed]:
    return {v.id: v for v in flatten(values)}
