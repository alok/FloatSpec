"""Typed SSA programs, their JSON form, type checking and observation signatures.

A program is one format plus a straight-line block of statements (§3.2):

- ``op``: ``let v := op(args)`` for a signature-table row;
- ``select``: ``let v := if c then a else b``;
- ``case4``: ``let v := match Bcompare x y with lt | eq | gt | none``;
- ``fold``: ``fold_k(op, acc, steps)``, rendered unrolled; its internal
  bindings are ``v_0 .. v_{k-2}`` and the final one is ``v`` itself;
- ``branch``: ``if c then block0 else block1`` whose observation is the tag
  (0 for the then-arm) followed by the taken arm's observations.

Arguments are references to earlier bindings or literals. Every binding is
observed, in program order (§5.1). Only glue (let, if, match, list append and
the observation encoders) is not a Flocq export.
"""

from __future__ import annotations

from dataclasses import dataclass, replace
import hashlib
import json
from typing import Iterator

from . import SCHEMA_IR
from .formats import Format, format_by_params
from .table import FOLD_SHAPES, OP_BY_NAME, VALUE_TYPES


class IRError(ValueError):
    """A program that is not well typed or not well formed."""


ARG_KINDS = ("ref", "int", "bool", "pos", "sf")


@dataclass(frozen=True)
class Arg:
    kind: str
    value: object

    @staticmethod
    def ref(name: str) -> "Arg":
        return Arg("ref", name)

    @staticmethod
    def int_(n: int) -> "Arg":
        return Arg("int", n)

    @staticmethod
    def bool_(b: bool) -> "Arg":
        return Arg("bool", b)

    @staticmethod
    def pos(n: int) -> "Arg":
        return Arg("pos", n)

    @staticmethod
    def sf(kind: int, sign: int, m: int, e: int) -> "Arg":
        return Arg("sf", (kind, sign, m, e))

    def to_json(self) -> dict[str, object]:
        return {self.kind: list(self.value) if self.kind == "sf" else self.value}  # type: ignore[arg-type]

    @staticmethod
    def from_json(row: object) -> "Arg":
        if not isinstance(row, dict) or len(row) != 1:
            raise IRError(f"malformed argument {row!r}")
        (kind, value), = row.items()
        if kind == "ref" and isinstance(value, str):
            return Arg.ref(value)
        if kind in ("int", "pos") and type(value) is int:
            return Arg(kind, value)
        if kind == "bool" and type(value) is bool:
            return Arg.bool_(value)
        if kind == "sf" and isinstance(value, list) and len(value) == 4 and all(type(v) is int for v in value):
            return Arg.sf(*value)
        raise IRError(f"malformed argument {row!r}")


@dataclass(frozen=True)
class Stmt:
    id: str
    kind: str
    type: str
    op: str | None = None
    mode: int | None = None
    spelling: str = "core"
    args: tuple[Arg, ...] = ()
    steps: tuple[tuple[Arg, ...], ...] = ()
    arms: tuple[tuple["Stmt", ...], ...] = ()
    corner: str | None = None

    def fold_ids(self) -> list[str]:
        """Binding ids of an unrolled fold: internal ones, then the statement id."""
        k = len(self.steps)
        return [f"{self.id}_{i}" for i in range(k - 1)] + [self.id]

    def to_json(self) -> dict[str, object]:
        row: dict[str, object] = {"id": self.id, "kind": self.kind, "type": self.type}
        if self.op is not None:
            row["op"] = self.op
        if self.mode is not None:
            row["mode"] = self.mode
        if self.spelling != "core":
            row["spelling"] = self.spelling
        if self.args:
            row["args"] = [a.to_json() for a in self.args]
        if self.kind == "fold":
            row["steps"] = [[a.to_json() for a in step] for step in self.steps]
        if self.kind == "branch":
            row["arms"] = [[s.to_json() for s in arm] for arm in self.arms]
        if self.corner is not None:
            row["corner"] = self.corner
        return row

    @staticmethod
    def from_json(row: object) -> "Stmt":
        if not isinstance(row, dict):
            raise IRError(f"malformed statement {row!r}")
        allowed = {"id", "kind", "type", "op", "mode", "spelling", "args", "steps", "arms", "corner"}
        if set(row) - allowed:
            raise IRError(f"unknown statement fields {sorted(set(row) - allowed)}")
        try:
            return Stmt(
                id=_str(row["id"]), kind=_str(row["kind"]), type=_str(row["type"]),
                op=_opt_str(row.get("op")), mode=_opt_int(row.get("mode")),
                spelling=_str(row.get("spelling", "core")),
                args=tuple(Arg.from_json(a) for a in _list(row.get("args", []))),
                steps=tuple(tuple(Arg.from_json(a) for a in _list(step)) for step in _list(row.get("steps", []))),
                arms=tuple(tuple(Stmt.from_json(s) for s in _list(arm)) for arm in _list(row.get("arms", []))),
                corner=_opt_str(row.get("corner")))
        except KeyError as missing:
            raise IRError(f"statement missing {missing}") from None


def _str(value: object) -> str:
    if not isinstance(value, str):
        raise IRError(f"expected string, got {value!r}")
    return value


def _opt_str(value: object) -> str | None:
    return None if value is None else _str(value)


def _opt_int(value: object) -> int | None:
    if value is None:
        return None
    if type(value) is not int:
        raise IRError(f"expected integer, got {value!r}")
    return value


def _list(value: object) -> list[object]:
    if not isinstance(value, list):
        raise IRError(f"expected list, got {value!r}")
    return value


@dataclass(frozen=True)
class Program:
    fmt: Format
    stmts: tuple[Stmt, ...]

    def to_json(self) -> dict[str, object]:
        return {"schema": SCHEMA_IR, "format": self.fmt.to_json(),
                "stmts": [s.to_json() for s in self.stmts]}

    @staticmethod
    def from_json(row: object) -> "Program":
        if not isinstance(row, dict) or row.get("schema") != SCHEMA_IR:
            raise IRError("not a flocqsmith IR document")
        fmt_row = row.get("format")
        if not isinstance(fmt_row, dict) or type(fmt_row.get("p")) is not int or type(fmt_row.get("emax")) is not int:
            raise IRError("malformed format")
        try:
            fmt = format_by_params(fmt_row["p"], fmt_row["emax"])
        except KeyError as error:
            raise IRError(str(error)) from None
        program = Program(fmt, tuple(Stmt.from_json(s) for s in _list(row.get("stmts"))))
        check_program(program)
        return program

    def canonical_json(self) -> str:
        return json.dumps(self.to_json(), sort_keys=True, separators=(",", ":"))

    def sha256(self) -> str:
        return hashlib.sha256(self.canonical_json().encode()).hexdigest()

    def with_stmts(self, stmts: tuple[Stmt, ...] | list[Stmt]) -> "Program":
        return replace(self, stmts=tuple(stmts))


def e_bound(fmt: Format) -> int:
    """Static bound on integers in exponent positions (§4.4)."""
    return 2 * fmt.emax + 2 * fmt.p


def arg_type_ok(arg: Arg, expected: str, scope: dict[str, str], fmt: Format) -> None:
    if arg.kind == "ref":
        actual = scope.get(str(arg.value))
        if actual is None:
            raise IRError(f"reference to unbound {arg.value}")
        if actual != expected:
            raise IRError(f"{arg.value} has type {actual}, expected {expected}")
        return
    if expected in ("Z", "E") and arg.kind == "int":
        if expected == "E" and abs(int(arg.value)) > e_bound(fmt):  # type: ignore[call-overload]
            raise IRError(f"exponent literal {arg.value} exceeds the static bound {e_bound(fmt)}")
        return
    if expected == "Bool" and arg.kind == "bool":
        return
    if expected == "Pos" and arg.kind == "pos":
        if int(arg.value) < 1:  # type: ignore[call-overload]
            raise IRError("positive literal must be at least 1")
        return
    if expected == "SF" and arg.kind == "sf":
        kind, sign, m, _ = arg.value  # type: ignore[misc]
        if kind not in range(4) or sign not in (0, 1) or m < 1:
            raise IRError(f"malformed spec_float literal {arg.value}")
        return
    raise IRError(f"{arg.kind} literal cannot have type {expected}")


def check_program(program: Program) -> None:
    """Type and shape check: every emitted program must pass (legality part 1)."""
    if not program.stmts:
        raise IRError("empty program")
    seen: set[str] = set()
    _check_block(program.stmts, {}, program.fmt, seen, top=True)


def _bind(name: str, seen: set[str]) -> None:
    if not name or name in seen:
        raise IRError(f"duplicate or empty binding id {name!r}")
    seen.add(name)


def _check_block(stmts: tuple[Stmt, ...], scope: dict[str, str], fmt: Format, seen: set[str], top: bool) -> None:
    for s in stmts:
        if s.kind == "op":
            row = OP_BY_NAME.get(s.op or "")
            if row is None:
                raise IRError(f"unknown op {s.op}")
            if row.has_mode != (s.mode is not None) or (s.mode is not None and s.mode not in range(5)):
                raise IRError(f"{s.id}: bad mode for {s.op}")
            if s.spelling not in ("core", "source") or (s.spelling == "source" and row.lean_source is None):
                raise IRError(f"{s.id}: bad spelling {s.spelling} for {s.op}")
            if len(s.args) != len(row.args):
                raise IRError(f"{s.id}: {s.op} takes {len(row.args)} arguments")
            for arg, expected in zip(s.args, row.args):
                arg_type_ok(arg, expected, scope, fmt)
            if s.type != row.result:
                raise IRError(f"{s.id}: declared {s.type}, {s.op} returns {row.result}")
            _bind(s.id, seen)
            scope[s.id] = s.type
        elif s.kind == "select":
            if len(s.args) != 3 or s.type not in VALUE_TYPES or s.op is not None or s.mode is not None:
                raise IRError(f"{s.id}: malformed select")
            arg_type_ok(s.args[0], "Bool", scope, fmt)
            arg_type_ok(s.args[1], s.type, scope, fmt)
            arg_type_ok(s.args[2], s.type, scope, fmt)
            _bind(s.id, seen)
            scope[s.id] = s.type
        elif s.kind == "case4":
            if len(s.args) != 6 or s.type not in VALUE_TYPES or s.op is not None or s.mode is not None:
                raise IRError(f"{s.id}: malformed case4")
            arg_type_ok(s.args[0], "BSN", scope, fmt)
            arg_type_ok(s.args[1], "BSN", scope, fmt)
            for arm in s.args[2:]:
                arg_type_ok(arm, s.type, scope, fmt)
            _bind(s.id, seen)
            scope[s.id] = s.type
        elif s.kind == "fold":
            shape = FOLD_SHAPES.get(s.op or "")
            if shape is None or s.type != "BSN" or len(s.args) != 1 or not 1 <= len(s.steps) <= 8:
                raise IRError(f"{s.id}: malformed fold")
            row = OP_BY_NAME[s.op or ""]
            if row.has_mode != (s.mode is not None) or (s.mode is not None and s.mode not in range(5)):
                raise IRError(f"{s.id}: bad fold mode")
            arg_type_ok(s.args[0], "BSN", scope, fmt)
            for step in s.steps:
                if len(step) != len(shape[1]):
                    raise IRError(f"{s.id}: fold step arity")
                for arg, expected in zip(step, shape[1]):
                    arg_type_ok(arg, expected, scope, fmt)
            for name in s.fold_ids():
                _bind(name, seen)
            scope[s.id] = "BSN"
        elif s.kind == "branch":
            if s.type != "branch" or len(s.args) != 1 or len(s.arms) != 2 or not all(s.arms):
                raise IRError(f"{s.id}: malformed branch")
            if not top:
                raise IRError(f"{s.id}: nested branches are not generated")
            arg_type_ok(s.args[0], "Bool", scope, fmt)
            _bind(s.id, seen)
            for arm in s.arms:
                _check_block(arm, dict(scope), fmt, seen, top=False)
        else:
            raise IRError(f"{s.id}: unknown statement kind {s.kind}")


# -- observation signature ---------------------------------------------------

def signature(program: Program) -> dict[str, object]:
    """The observation signature (§5.2): how the flat integer list decodes."""
    return {"p": program.fmt.p, "emax": program.fmt.emax, "bindings": _sig_block(program.stmts)}


def _sig_block(stmts: tuple[Stmt, ...]) -> list[dict[str, object]]:
    rows: list[dict[str, object]] = []
    for s in stmts:
        if s.kind == "fold":
            rows.extend({"id": name, "type": "BSN", "op": s.op} for name in s.fold_ids())
        elif s.kind == "branch":
            rows.append({"id": s.id, "type": "branch", "op": "branch",
                         "arms": [_sig_block(arm) for arm in s.arms]})
        else:
            rows.append({"id": s.id, "type": s.type, "op": s.op if s.kind == "op" else s.kind})
    return rows


def iter_bindings(stmts: tuple[Stmt, ...]) -> Iterator[Stmt]:
    """Top-level and arm statements in program order."""
    for s in stmts:
        yield s
        for arm in s.arms:
            yield from iter_bindings(arm)


def references(s: Stmt) -> set[str]:
    refs = {str(a.value) for a in s.args if a.kind == "ref"}
    for step in s.steps:
        refs |= {str(a.value) for a in step if a.kind == "ref"}
    for arm in s.arms:
        for inner in arm:
            refs |= references(inner)
    return refs


def ops_used(program: Program) -> dict[str, int]:
    counts: dict[str, int] = {}
    for s in iter_bindings(program.stmts):
        if s.kind == "op" and s.op:
            counts[s.op] = counts.get(s.op, 0) + 1
        elif s.kind == "fold" and s.op:
            counts[s.op] = counts.get(s.op, 0) + len(s.steps)
    return counts


def size(program: Program) -> int:
    """Number of observed bindings, counting fold steps and arm statements."""
    return sum(len(s.steps) if s.kind == "fold" else (0 if s.kind == "branch" else 1)
               for s in iter_bindings(program.stmts))
